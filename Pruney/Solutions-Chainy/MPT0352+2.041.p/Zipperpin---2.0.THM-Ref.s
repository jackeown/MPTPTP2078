%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uWfjHlAe5N

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:13 EST 2020

% Result     : Theorem 0.72s
% Output     : Refutation 0.72s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 114 expanded)
%              Number of leaves         :   25 (  41 expanded)
%              Depth                    :   12
%              Number of atoms          :  572 (1058 expanded)
%              Number of equality atoms :   14 (  20 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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

thf('2',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k3_subset_1 @ X33 @ X34 )
        = ( k4_xboole_0 @ X33 @ X34 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('4',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( r1_tarski @ sk_B @ sk_C_1 )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['5'])).

thf(t34_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k4_xboole_0 @ C @ B ) @ ( k4_xboole_0 @ C @ A ) ) ) )).

thf('7',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X12 @ X13 )
      | ( r1_tarski @ ( k4_xboole_0 @ X14 @ X13 ) @ ( k4_xboole_0 @ X14 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t34_xboole_1])).

thf('8',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k4_xboole_0 @ X0 @ sk_C_1 ) @ ( k4_xboole_0 @ X0 @ sk_B ) )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k4_xboole_0 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['4','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k3_subset_1 @ X33 @ X34 )
        = ( k4_xboole_0 @ X33 @ X34 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('12',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['9','12'])).

thf('14',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('15',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ~ ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['5'])).

thf('17',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['5'])).

thf('18',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('19',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( r1_tarski @ X19 @ ( k2_xboole_0 @ X20 @ X21 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X19 @ X20 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ X0 )
      | ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ ( k3_subset_1 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('23',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ X31 )
      | ( r2_hidden @ X30 @ X31 )
      | ( v1_xboole_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('24',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('25',plain,(
    ! [X35: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('26',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['24','25'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('27',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ X28 @ X27 )
      | ( r1_tarski @ X28 @ X26 )
      | ( X27
       != ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('28',plain,(
    ! [X26: $i,X28: $i] :
      ( ( r1_tarski @ X28 @ X26 )
      | ~ ( r2_hidden @ X28 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['26','28'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('30',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_xboole_0 @ X11 @ X10 )
        = X10 )
      | ~ ( r1_tarski @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('31',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['29','30'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('32',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X7 @ X9 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_A @ X0 )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( r1_tarski @ sk_B @ ( k2_xboole_0 @ sk_C_1 @ ( k3_subset_1 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['21','33'])).

thf(t73_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf('35',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( r1_tarski @ X22 @ X23 )
      | ~ ( r1_tarski @ X22 @ ( k2_xboole_0 @ X23 @ X24 ) )
      | ~ ( r1_xboole_0 @ X22 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t73_xboole_1])).

thf('36',plain,
    ( ( ~ ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
      | ( r1_tarski @ sk_B @ sk_C_1 ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('38',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X15 @ X16 ) @ X15 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('39',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_xboole_0 @ X11 @ X10 )
        = X10 )
      | ~ ( r1_tarski @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X15 @ X16 ) @ X15 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('42',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( r1_tarski @ X19 @ ( k2_xboole_0 @ X20 @ X21 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X19 @ X20 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['40','43'])).

thf(t106_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('45',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X4 @ X6 )
      | ~ ( r1_tarski @ X4 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    r1_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ),
    inference('sup+',[status(thm)],['37','46'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('49',plain,(
    r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( r1_tarski @ sk_B @ sk_C_1 )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['36','49'])).

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
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uWfjHlAe5N
% 0.17/0.37  % Computer   : n001.cluster.edu
% 0.17/0.37  % Model      : x86_64 x86_64
% 0.17/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.37  % Memory     : 8042.1875MB
% 0.17/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.37  % CPULimit   : 60
% 0.17/0.37  % DateTime   : Tue Dec  1 20:29:15 EST 2020
% 0.17/0.37  % CPUTime    : 
% 0.17/0.37  % Running portfolio for 600 s
% 0.17/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.37  % Number of cores: 8
% 0.17/0.38  % Python version: Python 3.6.8
% 0.17/0.38  % Running in FO mode
% 0.72/0.92  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.72/0.92  % Solved by: fo/fo7.sh
% 0.72/0.92  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.72/0.92  % done 1483 iterations in 0.433s
% 0.72/0.92  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.72/0.92  % SZS output start Refutation
% 0.72/0.92  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.72/0.92  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.72/0.92  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.72/0.92  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.72/0.92  thf(sk_B_type, type, sk_B: $i).
% 0.72/0.92  thf(sk_A_type, type, sk_A: $i).
% 0.72/0.92  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.72/0.92  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.72/0.92  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.72/0.92  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.72/0.92  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.72/0.92  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.72/0.92  thf(t31_subset_1, conjecture,
% 0.72/0.92    (![A:$i,B:$i]:
% 0.72/0.92     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.72/0.92       ( ![C:$i]:
% 0.72/0.92         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.72/0.92           ( ( r1_tarski @ B @ C ) <=>
% 0.72/0.92             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 0.72/0.92  thf(zf_stmt_0, negated_conjecture,
% 0.72/0.92    (~( ![A:$i,B:$i]:
% 0.72/0.92        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.72/0.92          ( ![C:$i]:
% 0.72/0.92            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.72/0.92              ( ( r1_tarski @ B @ C ) <=>
% 0.72/0.92                ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) )),
% 0.72/0.92    inference('cnf.neg', [status(esa)], [t31_subset_1])).
% 0.72/0.92  thf('0', plain,
% 0.72/0.92      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.72/0.92           (k3_subset_1 @ sk_A @ sk_B))
% 0.72/0.92        | ~ (r1_tarski @ sk_B @ sk_C_1))),
% 0.72/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.92  thf('1', plain,
% 0.72/0.92      (~
% 0.72/0.92       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.72/0.92         (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.72/0.92       ~ ((r1_tarski @ sk_B @ sk_C_1))),
% 0.72/0.92      inference('split', [status(esa)], ['0'])).
% 0.72/0.92  thf('2', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.72/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.92  thf(d5_subset_1, axiom,
% 0.72/0.92    (![A:$i,B:$i]:
% 0.72/0.92     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.72/0.92       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.72/0.92  thf('3', plain,
% 0.72/0.92      (![X33 : $i, X34 : $i]:
% 0.72/0.92         (((k3_subset_1 @ X33 @ X34) = (k4_xboole_0 @ X33 @ X34))
% 0.72/0.92          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X33)))),
% 0.72/0.92      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.72/0.92  thf('4', plain,
% 0.72/0.92      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.72/0.92      inference('sup-', [status(thm)], ['2', '3'])).
% 0.72/0.92  thf('5', plain,
% 0.72/0.92      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.72/0.92         (k3_subset_1 @ sk_A @ sk_B))
% 0.72/0.92        | (r1_tarski @ sk_B @ sk_C_1))),
% 0.72/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.92  thf('6', plain,
% 0.72/0.92      (((r1_tarski @ sk_B @ sk_C_1)) <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 0.72/0.92      inference('split', [status(esa)], ['5'])).
% 0.72/0.92  thf(t34_xboole_1, axiom,
% 0.72/0.92    (![A:$i,B:$i,C:$i]:
% 0.72/0.92     ( ( r1_tarski @ A @ B ) =>
% 0.72/0.92       ( r1_tarski @ ( k4_xboole_0 @ C @ B ) @ ( k4_xboole_0 @ C @ A ) ) ))).
% 0.72/0.92  thf('7', plain,
% 0.72/0.92      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.72/0.92         (~ (r1_tarski @ X12 @ X13)
% 0.72/0.92          | (r1_tarski @ (k4_xboole_0 @ X14 @ X13) @ (k4_xboole_0 @ X14 @ X12)))),
% 0.72/0.92      inference('cnf', [status(esa)], [t34_xboole_1])).
% 0.72/0.92  thf('8', plain,
% 0.72/0.92      ((![X0 : $i]:
% 0.72/0.92          (r1_tarski @ (k4_xboole_0 @ X0 @ sk_C_1) @ (k4_xboole_0 @ X0 @ sk_B)))
% 0.72/0.92         <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 0.72/0.92      inference('sup-', [status(thm)], ['6', '7'])).
% 0.72/0.92  thf('9', plain,
% 0.72/0.92      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.72/0.92         (k4_xboole_0 @ sk_A @ sk_B))) <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 0.72/0.92      inference('sup+', [status(thm)], ['4', '8'])).
% 0.72/0.92  thf('10', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.72/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.92  thf('11', plain,
% 0.72/0.92      (![X33 : $i, X34 : $i]:
% 0.72/0.92         (((k3_subset_1 @ X33 @ X34) = (k4_xboole_0 @ X33 @ X34))
% 0.72/0.92          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X33)))),
% 0.72/0.92      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.72/0.92  thf('12', plain,
% 0.72/0.92      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.72/0.92      inference('sup-', [status(thm)], ['10', '11'])).
% 0.72/0.92  thf('13', plain,
% 0.72/0.92      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.72/0.92         (k3_subset_1 @ sk_A @ sk_B))) <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 0.72/0.92      inference('demod', [status(thm)], ['9', '12'])).
% 0.72/0.92  thf('14', plain,
% 0.72/0.92      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.72/0.92           (k3_subset_1 @ sk_A @ sk_B)))
% 0.72/0.92         <= (~
% 0.72/0.92             ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.72/0.92               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.72/0.92      inference('split', [status(esa)], ['0'])).
% 0.72/0.92  thf('15', plain,
% 0.72/0.92      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.72/0.92         (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.72/0.92       ~ ((r1_tarski @ sk_B @ sk_C_1))),
% 0.72/0.92      inference('sup-', [status(thm)], ['13', '14'])).
% 0.72/0.92  thf('16', plain,
% 0.72/0.92      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.72/0.92         (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.72/0.92       ((r1_tarski @ sk_B @ sk_C_1))),
% 0.72/0.92      inference('split', [status(esa)], ['5'])).
% 0.72/0.92  thf('17', plain,
% 0.72/0.92      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.72/0.92         (k3_subset_1 @ sk_A @ sk_B)))
% 0.72/0.92         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.72/0.92               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.72/0.92      inference('split', [status(esa)], ['5'])).
% 0.72/0.92  thf('18', plain,
% 0.72/0.92      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.72/0.92      inference('sup-', [status(thm)], ['2', '3'])).
% 0.72/0.92  thf(t44_xboole_1, axiom,
% 0.72/0.92    (![A:$i,B:$i,C:$i]:
% 0.72/0.92     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 0.72/0.92       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.72/0.92  thf('19', plain,
% 0.72/0.92      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.72/0.92         ((r1_tarski @ X19 @ (k2_xboole_0 @ X20 @ X21))
% 0.72/0.92          | ~ (r1_tarski @ (k4_xboole_0 @ X19 @ X20) @ X21))),
% 0.72/0.92      inference('cnf', [status(esa)], [t44_xboole_1])).
% 0.72/0.92  thf('20', plain,
% 0.72/0.92      (![X0 : $i]:
% 0.72/0.92         (~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ X0)
% 0.72/0.92          | (r1_tarski @ sk_A @ (k2_xboole_0 @ sk_C_1 @ X0)))),
% 0.72/0.92      inference('sup-', [status(thm)], ['18', '19'])).
% 0.72/0.92  thf('21', plain,
% 0.72/0.92      (((r1_tarski @ sk_A @ 
% 0.72/0.92         (k2_xboole_0 @ sk_C_1 @ (k3_subset_1 @ sk_A @ sk_B))))
% 0.72/0.92         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.72/0.92               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.72/0.92      inference('sup-', [status(thm)], ['17', '20'])).
% 0.72/0.92  thf('22', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.72/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.92  thf(d2_subset_1, axiom,
% 0.72/0.92    (![A:$i,B:$i]:
% 0.72/0.92     ( ( ( v1_xboole_0 @ A ) =>
% 0.72/0.92         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.72/0.92       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.72/0.92         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.72/0.92  thf('23', plain,
% 0.72/0.92      (![X30 : $i, X31 : $i]:
% 0.72/0.92         (~ (m1_subset_1 @ X30 @ X31)
% 0.72/0.92          | (r2_hidden @ X30 @ X31)
% 0.72/0.92          | (v1_xboole_0 @ X31))),
% 0.72/0.92      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.72/0.92  thf('24', plain,
% 0.72/0.92      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.72/0.92        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.72/0.92      inference('sup-', [status(thm)], ['22', '23'])).
% 0.72/0.92  thf(fc1_subset_1, axiom,
% 0.72/0.92    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.72/0.92  thf('25', plain, (![X35 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X35))),
% 0.72/0.92      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.72/0.92  thf('26', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.72/0.92      inference('clc', [status(thm)], ['24', '25'])).
% 0.72/0.92  thf(d1_zfmisc_1, axiom,
% 0.72/0.92    (![A:$i,B:$i]:
% 0.72/0.92     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.72/0.92       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.72/0.92  thf('27', plain,
% 0.72/0.92      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.72/0.92         (~ (r2_hidden @ X28 @ X27)
% 0.72/0.92          | (r1_tarski @ X28 @ X26)
% 0.72/0.92          | ((X27) != (k1_zfmisc_1 @ X26)))),
% 0.72/0.92      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.72/0.92  thf('28', plain,
% 0.72/0.92      (![X26 : $i, X28 : $i]:
% 0.72/0.92         ((r1_tarski @ X28 @ X26) | ~ (r2_hidden @ X28 @ (k1_zfmisc_1 @ X26)))),
% 0.72/0.92      inference('simplify', [status(thm)], ['27'])).
% 0.72/0.92  thf('29', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.72/0.92      inference('sup-', [status(thm)], ['26', '28'])).
% 0.72/0.92  thf(t12_xboole_1, axiom,
% 0.72/0.92    (![A:$i,B:$i]:
% 0.72/0.92     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.72/0.92  thf('30', plain,
% 0.72/0.92      (![X10 : $i, X11 : $i]:
% 0.72/0.92         (((k2_xboole_0 @ X11 @ X10) = (X10)) | ~ (r1_tarski @ X11 @ X10))),
% 0.72/0.92      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.72/0.92  thf('31', plain, (((k2_xboole_0 @ sk_B @ sk_A) = (sk_A))),
% 0.72/0.92      inference('sup-', [status(thm)], ['29', '30'])).
% 0.72/0.92  thf(t11_xboole_1, axiom,
% 0.72/0.92    (![A:$i,B:$i,C:$i]:
% 0.72/0.92     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.72/0.92  thf('32', plain,
% 0.72/0.92      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.72/0.92         ((r1_tarski @ X7 @ X8) | ~ (r1_tarski @ (k2_xboole_0 @ X7 @ X9) @ X8))),
% 0.72/0.92      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.72/0.92  thf('33', plain,
% 0.72/0.92      (![X0 : $i]: (~ (r1_tarski @ sk_A @ X0) | (r1_tarski @ sk_B @ X0))),
% 0.72/0.92      inference('sup-', [status(thm)], ['31', '32'])).
% 0.72/0.92  thf('34', plain,
% 0.72/0.92      (((r1_tarski @ sk_B @ 
% 0.72/0.92         (k2_xboole_0 @ sk_C_1 @ (k3_subset_1 @ sk_A @ sk_B))))
% 0.72/0.92         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.72/0.92               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.72/0.92      inference('sup-', [status(thm)], ['21', '33'])).
% 0.72/0.92  thf(t73_xboole_1, axiom,
% 0.72/0.92    (![A:$i,B:$i,C:$i]:
% 0.72/0.92     ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & ( r1_xboole_0 @ A @ C ) ) =>
% 0.72/0.92       ( r1_tarski @ A @ B ) ))).
% 0.72/0.92  thf('35', plain,
% 0.72/0.92      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.72/0.92         ((r1_tarski @ X22 @ X23)
% 0.72/0.92          | ~ (r1_tarski @ X22 @ (k2_xboole_0 @ X23 @ X24))
% 0.72/0.92          | ~ (r1_xboole_0 @ X22 @ X24))),
% 0.72/0.92      inference('cnf', [status(esa)], [t73_xboole_1])).
% 0.72/0.92  thf('36', plain,
% 0.72/0.92      (((~ (r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.72/0.92         | (r1_tarski @ sk_B @ sk_C_1)))
% 0.72/0.92         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.72/0.92               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.72/0.92      inference('sup-', [status(thm)], ['34', '35'])).
% 0.72/0.92  thf('37', plain,
% 0.72/0.92      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.72/0.92      inference('sup-', [status(thm)], ['10', '11'])).
% 0.72/0.92  thf(t36_xboole_1, axiom,
% 0.72/0.92    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.72/0.92  thf('38', plain,
% 0.72/0.92      (![X15 : $i, X16 : $i]: (r1_tarski @ (k4_xboole_0 @ X15 @ X16) @ X15)),
% 0.72/0.92      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.72/0.92  thf('39', plain,
% 0.72/0.92      (![X10 : $i, X11 : $i]:
% 0.72/0.92         (((k2_xboole_0 @ X11 @ X10) = (X10)) | ~ (r1_tarski @ X11 @ X10))),
% 0.72/0.92      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.72/0.92  thf('40', plain,
% 0.72/0.92      (![X0 : $i, X1 : $i]:
% 0.72/0.92         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 0.72/0.92      inference('sup-', [status(thm)], ['38', '39'])).
% 0.72/0.92  thf('41', plain,
% 0.72/0.92      (![X15 : $i, X16 : $i]: (r1_tarski @ (k4_xboole_0 @ X15 @ X16) @ X15)),
% 0.72/0.92      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.72/0.92  thf('42', plain,
% 0.72/0.92      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.72/0.92         ((r1_tarski @ X19 @ (k2_xboole_0 @ X20 @ X21))
% 0.72/0.92          | ~ (r1_tarski @ (k4_xboole_0 @ X19 @ X20) @ X21))),
% 0.72/0.92      inference('cnf', [status(esa)], [t44_xboole_1])).
% 0.72/0.92  thf('43', plain,
% 0.72/0.92      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.72/0.92      inference('sup-', [status(thm)], ['41', '42'])).
% 0.72/0.92  thf('44', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.72/0.92      inference('sup+', [status(thm)], ['40', '43'])).
% 0.72/0.92  thf(t106_xboole_1, axiom,
% 0.72/0.92    (![A:$i,B:$i,C:$i]:
% 0.72/0.92     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.72/0.92       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 0.72/0.92  thf('45', plain,
% 0.72/0.92      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.72/0.92         ((r1_xboole_0 @ X4 @ X6)
% 0.72/0.92          | ~ (r1_tarski @ X4 @ (k4_xboole_0 @ X5 @ X6)))),
% 0.72/0.92      inference('cnf', [status(esa)], [t106_xboole_1])).
% 0.72/0.92  thf('46', plain,
% 0.72/0.92      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)),
% 0.72/0.92      inference('sup-', [status(thm)], ['44', '45'])).
% 0.72/0.92  thf('47', plain, ((r1_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)),
% 0.72/0.92      inference('sup+', [status(thm)], ['37', '46'])).
% 0.72/0.92  thf(symmetry_r1_xboole_0, axiom,
% 0.72/0.92    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.72/0.92  thf('48', plain,
% 0.72/0.92      (![X0 : $i, X1 : $i]:
% 0.72/0.92         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.72/0.92      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.72/0.92  thf('49', plain, ((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))),
% 0.72/0.92      inference('sup-', [status(thm)], ['47', '48'])).
% 0.72/0.92  thf('50', plain,
% 0.72/0.92      (((r1_tarski @ sk_B @ sk_C_1))
% 0.72/0.92         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.72/0.92               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.72/0.92      inference('demod', [status(thm)], ['36', '49'])).
% 0.72/0.92  thf('51', plain,
% 0.72/0.92      ((~ (r1_tarski @ sk_B @ sk_C_1)) <= (~ ((r1_tarski @ sk_B @ sk_C_1)))),
% 0.72/0.92      inference('split', [status(esa)], ['0'])).
% 0.72/0.92  thf('52', plain,
% 0.72/0.92      (~
% 0.72/0.92       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.72/0.92         (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.72/0.92       ((r1_tarski @ sk_B @ sk_C_1))),
% 0.72/0.92      inference('sup-', [status(thm)], ['50', '51'])).
% 0.72/0.92  thf('53', plain, ($false),
% 0.72/0.92      inference('sat_resolution*', [status(thm)], ['1', '15', '16', '52'])).
% 0.72/0.92  
% 0.72/0.92  % SZS output end Refutation
% 0.72/0.92  
% 0.78/0.93  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
