%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.n37KwFobUK

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:12 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 136 expanded)
%              Number of leaves         :   18 (  46 expanded)
%              Depth                    :   12
%              Number of atoms          :  593 (1387 expanded)
%              Number of equality atoms :   22 (  40 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t31_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ C )
          <=> ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( ( r1_tarski @ B @ C )
            <=> ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t31_subset_1])).

thf('0',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ~ ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ~ ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r1_tarski @ sk_B @ sk_C_1 )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['2'])).

thf(t34_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k4_xboole_0 @ C @ B ) @ ( k4_xboole_0 @ C @ A ) ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ X1 ) @ ( k4_xboole_0 @ X2 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[t34_xboole_1])).

thf('5',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k4_xboole_0 @ X0 @ sk_C_1 ) @ ( k4_xboole_0 @ X0 @ sk_B ) )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_subset_1 @ X13 @ X14 )
        = ( k4_xboole_0 @ X13 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('8',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_subset_1 @ X13 @ X14 )
        = ( k4_xboole_0 @ X13 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('11',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('13',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k4_xboole_0 @ sk_A @ sk_B ) )
   <= ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ~ ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) @ ( k4_xboole_0 @ sk_A @ sk_B ) )
   <= ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf('15',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ~ ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['5','14'])).

thf('16',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['2'])).

thf('17',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('18',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_subset_1 @ X17 @ ( k3_subset_1 @ X17 @ X16 ) )
        = X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('19',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('21',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('22',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ( r2_hidden @ X5 @ X7 )
      | ( X7
       != ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('23',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r2_hidden @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('25',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ( m1_subset_1 @ X10 @ X11 )
      | ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('27',plain,(
    ! [X15: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_subset_1 @ X13 @ X14 )
        = ( k4_xboole_0 @ X13 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['19','20','30'])).

thf('32',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ X1 ) @ ( k4_xboole_0 @ X2 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[t34_xboole_1])).

thf('34',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k4_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_B ) ) @ ( k4_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r2_hidden @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('36',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ ( k4_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('38',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('39',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) ) ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,
    ( ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) ) ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['31','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_subset_1 @ X17 @ ( k3_subset_1 @ X17 @ X16 ) )
        = X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('43',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
    = sk_C_1 ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('46',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) )
    = sk_C_1 ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,
    ( ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_C_1 ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['40','46'])).

thf('48',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r1_tarski @ X8 @ X6 )
      | ( X7
       != ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('49',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r1_tarski @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,
    ( ( r1_tarski @ sk_B @ sk_C_1 )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['47','49'])).

thf('51',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C_1 )
   <= ~ ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('52',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','15','16','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.n37KwFobUK
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:10:03 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.36/0.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.58  % Solved by: fo/fo7.sh
% 0.36/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.58  % done 248 iterations in 0.131s
% 0.36/0.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.58  % SZS output start Refutation
% 0.36/0.58  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.36/0.58  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.36/0.58  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.36/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.58  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.36/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.58  thf(t31_subset_1, conjecture,
% 0.36/0.58    (![A:$i,B:$i]:
% 0.36/0.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.36/0.58       ( ![C:$i]:
% 0.36/0.58         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.36/0.58           ( ( r1_tarski @ B @ C ) <=>
% 0.36/0.58             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 0.36/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.58    (~( ![A:$i,B:$i]:
% 0.36/0.58        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.36/0.58          ( ![C:$i]:
% 0.36/0.58            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.36/0.58              ( ( r1_tarski @ B @ C ) <=>
% 0.36/0.58                ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) )),
% 0.36/0.58    inference('cnf.neg', [status(esa)], [t31_subset_1])).
% 0.36/0.58  thf('0', plain,
% 0.36/0.58      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.36/0.58           (k3_subset_1 @ sk_A @ sk_B))
% 0.36/0.58        | ~ (r1_tarski @ sk_B @ sk_C_1))),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('1', plain,
% 0.36/0.58      (~
% 0.36/0.58       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.36/0.58         (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.36/0.58       ~ ((r1_tarski @ sk_B @ sk_C_1))),
% 0.36/0.58      inference('split', [status(esa)], ['0'])).
% 0.36/0.58  thf('2', plain,
% 0.36/0.58      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.36/0.58         (k3_subset_1 @ sk_A @ sk_B))
% 0.36/0.58        | (r1_tarski @ sk_B @ sk_C_1))),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('3', plain,
% 0.36/0.58      (((r1_tarski @ sk_B @ sk_C_1)) <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 0.36/0.58      inference('split', [status(esa)], ['2'])).
% 0.36/0.58  thf(t34_xboole_1, axiom,
% 0.36/0.58    (![A:$i,B:$i,C:$i]:
% 0.36/0.58     ( ( r1_tarski @ A @ B ) =>
% 0.36/0.58       ( r1_tarski @ ( k4_xboole_0 @ C @ B ) @ ( k4_xboole_0 @ C @ A ) ) ))).
% 0.36/0.58  thf('4', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.58         (~ (r1_tarski @ X0 @ X1)
% 0.36/0.58          | (r1_tarski @ (k4_xboole_0 @ X2 @ X1) @ (k4_xboole_0 @ X2 @ X0)))),
% 0.36/0.58      inference('cnf', [status(esa)], [t34_xboole_1])).
% 0.36/0.58  thf('5', plain,
% 0.36/0.58      ((![X0 : $i]:
% 0.36/0.58          (r1_tarski @ (k4_xboole_0 @ X0 @ sk_C_1) @ (k4_xboole_0 @ X0 @ sk_B)))
% 0.36/0.58         <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 0.36/0.58      inference('sup-', [status(thm)], ['3', '4'])).
% 0.36/0.58  thf('6', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf(d5_subset_1, axiom,
% 0.36/0.58    (![A:$i,B:$i]:
% 0.36/0.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.36/0.58       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.36/0.58  thf('7', plain,
% 0.36/0.58      (![X13 : $i, X14 : $i]:
% 0.36/0.58         (((k3_subset_1 @ X13 @ X14) = (k4_xboole_0 @ X13 @ X14))
% 0.36/0.58          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X13)))),
% 0.36/0.58      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.36/0.58  thf('8', plain,
% 0.36/0.58      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.36/0.58      inference('sup-', [status(thm)], ['6', '7'])).
% 0.36/0.58  thf('9', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('10', plain,
% 0.36/0.58      (![X13 : $i, X14 : $i]:
% 0.36/0.58         (((k3_subset_1 @ X13 @ X14) = (k4_xboole_0 @ X13 @ X14))
% 0.36/0.58          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X13)))),
% 0.36/0.58      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.36/0.58  thf('11', plain,
% 0.36/0.58      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.36/0.58      inference('sup-', [status(thm)], ['9', '10'])).
% 0.36/0.58  thf('12', plain,
% 0.36/0.58      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.36/0.58           (k3_subset_1 @ sk_A @ sk_B)))
% 0.36/0.58         <= (~
% 0.36/0.58             ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.36/0.58               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.36/0.58      inference('split', [status(esa)], ['0'])).
% 0.36/0.58  thf('13', plain,
% 0.36/0.58      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.36/0.58           (k4_xboole_0 @ sk_A @ sk_B)))
% 0.36/0.58         <= (~
% 0.36/0.58             ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.36/0.58               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.36/0.58      inference('sup-', [status(thm)], ['11', '12'])).
% 0.36/0.58  thf('14', plain,
% 0.36/0.58      ((~ (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_C_1) @ 
% 0.36/0.58           (k4_xboole_0 @ sk_A @ sk_B)))
% 0.36/0.58         <= (~
% 0.36/0.58             ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.36/0.58               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.36/0.58      inference('sup-', [status(thm)], ['8', '13'])).
% 0.36/0.58  thf('15', plain,
% 0.36/0.58      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.36/0.58         (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.36/0.58       ~ ((r1_tarski @ sk_B @ sk_C_1))),
% 0.36/0.58      inference('sup-', [status(thm)], ['5', '14'])).
% 0.36/0.58  thf('16', plain,
% 0.36/0.58      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.36/0.58         (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.36/0.58       ((r1_tarski @ sk_B @ sk_C_1))),
% 0.36/0.58      inference('split', [status(esa)], ['2'])).
% 0.36/0.58  thf('17', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf(involutiveness_k3_subset_1, axiom,
% 0.36/0.58    (![A:$i,B:$i]:
% 0.36/0.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.36/0.58       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.36/0.58  thf('18', plain,
% 0.36/0.58      (![X16 : $i, X17 : $i]:
% 0.36/0.58         (((k3_subset_1 @ X17 @ (k3_subset_1 @ X17 @ X16)) = (X16))
% 0.36/0.58          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 0.36/0.58      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.36/0.58  thf('19', plain,
% 0.36/0.58      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.36/0.58      inference('sup-', [status(thm)], ['17', '18'])).
% 0.36/0.58  thf('20', plain,
% 0.36/0.58      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.36/0.58      inference('sup-', [status(thm)], ['9', '10'])).
% 0.36/0.58  thf(t36_xboole_1, axiom,
% 0.36/0.58    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.36/0.58  thf('21', plain,
% 0.36/0.58      (![X3 : $i, X4 : $i]: (r1_tarski @ (k4_xboole_0 @ X3 @ X4) @ X3)),
% 0.36/0.58      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.36/0.58  thf(d1_zfmisc_1, axiom,
% 0.36/0.58    (![A:$i,B:$i]:
% 0.36/0.58     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.36/0.58       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.36/0.58  thf('22', plain,
% 0.36/0.58      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.36/0.58         (~ (r1_tarski @ X5 @ X6)
% 0.36/0.58          | (r2_hidden @ X5 @ X7)
% 0.36/0.58          | ((X7) != (k1_zfmisc_1 @ X6)))),
% 0.36/0.58      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.36/0.58  thf('23', plain,
% 0.36/0.58      (![X5 : $i, X6 : $i]:
% 0.36/0.58         ((r2_hidden @ X5 @ (k1_zfmisc_1 @ X6)) | ~ (r1_tarski @ X5 @ X6))),
% 0.36/0.58      inference('simplify', [status(thm)], ['22'])).
% 0.36/0.58  thf('24', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i]:
% 0.36/0.58         (r2_hidden @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.36/0.58      inference('sup-', [status(thm)], ['21', '23'])).
% 0.36/0.58  thf(d2_subset_1, axiom,
% 0.36/0.58    (![A:$i,B:$i]:
% 0.36/0.58     ( ( ( v1_xboole_0 @ A ) =>
% 0.36/0.58         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.36/0.58       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.36/0.58         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.36/0.58  thf('25', plain,
% 0.36/0.58      (![X10 : $i, X11 : $i]:
% 0.36/0.58         (~ (r2_hidden @ X10 @ X11)
% 0.36/0.58          | (m1_subset_1 @ X10 @ X11)
% 0.36/0.58          | (v1_xboole_0 @ X11))),
% 0.36/0.58      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.36/0.58  thf('26', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i]:
% 0.36/0.58         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 0.36/0.58          | (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0)))),
% 0.36/0.58      inference('sup-', [status(thm)], ['24', '25'])).
% 0.36/0.58  thf(fc1_subset_1, axiom,
% 0.36/0.58    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.36/0.58  thf('27', plain, (![X15 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X15))),
% 0.36/0.58      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.36/0.58  thf('28', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i]:
% 0.36/0.58         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.36/0.58      inference('clc', [status(thm)], ['26', '27'])).
% 0.36/0.58  thf('29', plain,
% 0.36/0.58      (![X13 : $i, X14 : $i]:
% 0.36/0.58         (((k3_subset_1 @ X13 @ X14) = (k4_xboole_0 @ X13 @ X14))
% 0.36/0.58          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X13)))),
% 0.36/0.58      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.36/0.58  thf('30', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i]:
% 0.36/0.58         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.36/0.58           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.36/0.58      inference('sup-', [status(thm)], ['28', '29'])).
% 0.36/0.58  thf('31', plain,
% 0.36/0.58      (((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B)) = (sk_B))),
% 0.36/0.58      inference('demod', [status(thm)], ['19', '20', '30'])).
% 0.36/0.58  thf('32', plain,
% 0.36/0.58      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.36/0.58         (k3_subset_1 @ sk_A @ sk_B)))
% 0.36/0.58         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.36/0.58               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.36/0.58      inference('split', [status(esa)], ['2'])).
% 0.36/0.58  thf('33', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.58         (~ (r1_tarski @ X0 @ X1)
% 0.36/0.58          | (r1_tarski @ (k4_xboole_0 @ X2 @ X1) @ (k4_xboole_0 @ X2 @ X0)))),
% 0.36/0.58      inference('cnf', [status(esa)], [t34_xboole_1])).
% 0.36/0.58  thf('34', plain,
% 0.36/0.58      ((![X0 : $i]:
% 0.36/0.58          (r1_tarski @ (k4_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_B)) @ 
% 0.36/0.58           (k4_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_C_1))))
% 0.36/0.58         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.36/0.58               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.36/0.58      inference('sup-', [status(thm)], ['32', '33'])).
% 0.36/0.58  thf('35', plain,
% 0.36/0.58      (![X5 : $i, X6 : $i]:
% 0.36/0.58         ((r2_hidden @ X5 @ (k1_zfmisc_1 @ X6)) | ~ (r1_tarski @ X5 @ X6))),
% 0.36/0.58      inference('simplify', [status(thm)], ['22'])).
% 0.36/0.58  thf('36', plain,
% 0.36/0.58      ((![X0 : $i]:
% 0.36/0.58          (r2_hidden @ (k4_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_B)) @ 
% 0.36/0.58           (k1_zfmisc_1 @ (k4_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_C_1)))))
% 0.36/0.58         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.36/0.58               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.36/0.58      inference('sup-', [status(thm)], ['34', '35'])).
% 0.36/0.58  thf('37', plain,
% 0.36/0.58      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.36/0.58      inference('sup-', [status(thm)], ['9', '10'])).
% 0.36/0.58  thf('38', plain,
% 0.36/0.58      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.36/0.58      inference('sup-', [status(thm)], ['6', '7'])).
% 0.36/0.58  thf('39', plain,
% 0.36/0.58      ((![X0 : $i]:
% 0.36/0.58          (r2_hidden @ (k4_xboole_0 @ X0 @ (k4_xboole_0 @ sk_A @ sk_B)) @ 
% 0.36/0.58           (k1_zfmisc_1 @ (k4_xboole_0 @ X0 @ (k4_xboole_0 @ sk_A @ sk_C_1)))))
% 0.36/0.58         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.36/0.58               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.36/0.58      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.36/0.58  thf('40', plain,
% 0.36/0.58      (((r2_hidden @ sk_B @ 
% 0.36/0.58         (k1_zfmisc_1 @ (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_C_1)))))
% 0.36/0.58         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.36/0.58               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.36/0.58      inference('sup+', [status(thm)], ['31', '39'])).
% 0.36/0.58  thf('41', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('42', plain,
% 0.36/0.58      (![X16 : $i, X17 : $i]:
% 0.36/0.58         (((k3_subset_1 @ X17 @ (k3_subset_1 @ X17 @ X16)) = (X16))
% 0.36/0.58          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 0.36/0.58      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.36/0.58  thf('43', plain,
% 0.36/0.58      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C_1)) = (sk_C_1))),
% 0.36/0.58      inference('sup-', [status(thm)], ['41', '42'])).
% 0.36/0.58  thf('44', plain,
% 0.36/0.58      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.36/0.58      inference('sup-', [status(thm)], ['6', '7'])).
% 0.36/0.58  thf('45', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i]:
% 0.36/0.58         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.36/0.58           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.36/0.58      inference('sup-', [status(thm)], ['28', '29'])).
% 0.36/0.58  thf('46', plain,
% 0.36/0.58      (((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_C_1)) = (sk_C_1))),
% 0.36/0.58      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.36/0.58  thf('47', plain,
% 0.36/0.58      (((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_C_1)))
% 0.36/0.58         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.36/0.58               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.36/0.58      inference('demod', [status(thm)], ['40', '46'])).
% 0.36/0.58  thf('48', plain,
% 0.36/0.58      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.36/0.58         (~ (r2_hidden @ X8 @ X7)
% 0.36/0.58          | (r1_tarski @ X8 @ X6)
% 0.36/0.58          | ((X7) != (k1_zfmisc_1 @ X6)))),
% 0.36/0.58      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.36/0.58  thf('49', plain,
% 0.36/0.58      (![X6 : $i, X8 : $i]:
% 0.36/0.58         ((r1_tarski @ X8 @ X6) | ~ (r2_hidden @ X8 @ (k1_zfmisc_1 @ X6)))),
% 0.36/0.58      inference('simplify', [status(thm)], ['48'])).
% 0.36/0.58  thf('50', plain,
% 0.36/0.58      (((r1_tarski @ sk_B @ sk_C_1))
% 0.36/0.58         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.36/0.58               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.36/0.58      inference('sup-', [status(thm)], ['47', '49'])).
% 0.36/0.58  thf('51', plain,
% 0.36/0.58      ((~ (r1_tarski @ sk_B @ sk_C_1)) <= (~ ((r1_tarski @ sk_B @ sk_C_1)))),
% 0.36/0.58      inference('split', [status(esa)], ['0'])).
% 0.36/0.58  thf('52', plain,
% 0.36/0.58      (~
% 0.36/0.58       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.36/0.58         (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.36/0.58       ((r1_tarski @ sk_B @ sk_C_1))),
% 0.36/0.58      inference('sup-', [status(thm)], ['50', '51'])).
% 0.36/0.58  thf('53', plain, ($false),
% 0.36/0.58      inference('sat_resolution*', [status(thm)], ['1', '15', '16', '52'])).
% 0.36/0.58  
% 0.36/0.58  % SZS output end Refutation
% 0.36/0.58  
% 0.36/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
