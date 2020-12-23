%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pJa9YrgU8a

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:24 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 180 expanded)
%              Number of leaves         :   26 (  59 expanded)
%              Depth                    :   16
%              Number of atoms          :  565 (1375 expanded)
%              Number of equality atoms :   47 ( 112 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('0',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('1',plain,(
    ! [X14: $i] :
      ( ( k5_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('2',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r2_hidden @ X6 @ X8 )
      | ~ ( r2_hidden @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('7',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t38_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) )
      <=> ( B
          = ( k1_subset_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) )
        <=> ( B
            = ( k1_subset_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t38_subset_1])).

thf('12',plain,(
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

thf('13',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ X21 )
      | ( r2_hidden @ X20 @ X21 )
      | ( v1_xboole_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('14',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('15',plain,(
    ! [X26: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('16',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['14','15'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('17',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X18 @ X17 )
      | ( r1_tarski @ X18 @ X16 )
      | ( X17
       != ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('18',plain,(
    ! [X16: $i,X18: $i] :
      ( ( r1_tarski @ X18 @ X16 )
      | ~ ( r2_hidden @ X18 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('21',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('23',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['21','22'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('24',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('25',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r2_hidden @ X6 @ X8 )
      | ~ ( r2_hidden @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( sk_B
      = ( k1_subset_1 @ sk_A ) )
    | ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['28'])).

thf('30',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('31',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ ( k3_subset_1 @ sk_A @ sk_B ) )
        | ~ ( r2_hidden @ X0 @ sk_B ) )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( sk_B
     != ( k1_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( sk_B
     != ( k1_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('35',plain,(
    ! [X23: $i] :
      ( ( k1_subset_1 @ X23 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('36',plain,
    ( ( sk_B
      = ( k1_subset_1 @ sk_A ) )
   <= ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['28'])).

thf('37',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['32'])).

thf('39',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ k1_xboole_0 ) )
   <= ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
      & ( sk_B
        = ( k1_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('41',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k3_subset_1 @ sk_A @ k1_xboole_0 ) )
   <= ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
      & ( sk_B
        = ( k1_subset_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( sk_B
     != ( k1_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','41'])).

thf('43',plain,
    ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['28'])).

thf('44',plain,(
    r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['33','42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k3_subset_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['31','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('47',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k3_subset_1 @ X24 @ X25 )
        = ( k4_xboole_0 @ X24 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('48',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k4_xboole_0 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['45','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['27','49'])).

thf('51',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['16','18'])).

thf('52',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_B ) ),
    inference(clc,[status(thm)],['50','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_B @ X0 ) ),
    inference('sup-',[status(thm)],['11','54'])).

thf('56',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ X0 )
      = sk_B ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    k1_xboole_0 = sk_B ),
    inference('sup+',[status(thm)],['10','57'])).

thf('59',plain,
    ( ( sk_B
     != ( k1_subset_1 @ sk_A ) )
   <= ( sk_B
     != ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['32'])).

thf('60',plain,(
    ! [X23: $i] :
      ( ( k1_subset_1 @ X23 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('61',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B
     != ( k1_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    sk_B
 != ( k1_subset_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['33','42'])).

thf('63',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['61','62'])).

thf('64',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['58','63'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pJa9YrgU8a
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:23:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.52  % Solved by: fo/fo7.sh
% 0.20/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.52  % done 192 iterations in 0.063s
% 0.20/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.52  % SZS output start Refutation
% 0.20/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.52  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.20/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.52  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.20/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.52  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.20/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.52  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.52  thf(d3_tarski, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.52       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.52  thf('0', plain,
% 0.20/0.52      (![X3 : $i, X5 : $i]:
% 0.20/0.52         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.20/0.52      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.52  thf(t5_boole, axiom,
% 0.20/0.52    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.52  thf('1', plain, (![X14 : $i]: ((k5_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.20/0.52      inference('cnf', [status(esa)], [t5_boole])).
% 0.20/0.52  thf(t1_xboole_0, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.20/0.52       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 0.20/0.52  thf('2', plain,
% 0.20/0.52      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X6 @ X7)
% 0.20/0.52          | ~ (r2_hidden @ X6 @ X8)
% 0.20/0.52          | ~ (r2_hidden @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.20/0.52  thf('3', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X1 @ X0)
% 0.20/0.52          | ~ (r2_hidden @ X1 @ k1_xboole_0)
% 0.20/0.52          | ~ (r2_hidden @ X1 @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.52  thf('4', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r2_hidden @ X1 @ X0))),
% 0.20/0.52      inference('simplify', [status(thm)], ['3'])).
% 0.20/0.52  thf('5', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.20/0.52      inference('condensation', [status(thm)], ['4'])).
% 0.20/0.52  thf('6', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.20/0.52      inference('sup-', [status(thm)], ['0', '5'])).
% 0.20/0.52  thf(t28_xboole_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.52  thf('7', plain,
% 0.20/0.52      (![X12 : $i, X13 : $i]:
% 0.20/0.52         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 0.20/0.52      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.52  thf('8', plain,
% 0.20/0.52      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.52  thf(commutativity_k3_xboole_0, axiom,
% 0.20/0.52    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.20/0.52  thf('9', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.52      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.52  thf('10', plain,
% 0.20/0.52      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.52      inference('sup+', [status(thm)], ['8', '9'])).
% 0.20/0.52  thf('11', plain,
% 0.20/0.52      (![X3 : $i, X5 : $i]:
% 0.20/0.52         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.20/0.52      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.52  thf(t38_subset_1, conjecture,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.52       ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 0.20/0.52         ( ( B ) = ( k1_subset_1 @ A ) ) ) ))).
% 0.20/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.52    (~( ![A:$i,B:$i]:
% 0.20/0.52        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.52          ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 0.20/0.52            ( ( B ) = ( k1_subset_1 @ A ) ) ) ) )),
% 0.20/0.52    inference('cnf.neg', [status(esa)], [t38_subset_1])).
% 0.20/0.52  thf('12', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(d2_subset_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ( v1_xboole_0 @ A ) =>
% 0.20/0.52         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.20/0.52       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.52         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.52  thf('13', plain,
% 0.20/0.52      (![X20 : $i, X21 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X20 @ X21)
% 0.20/0.52          | (r2_hidden @ X20 @ X21)
% 0.20/0.52          | (v1_xboole_0 @ X21))),
% 0.20/0.52      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.20/0.52  thf('14', plain,
% 0.20/0.52      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.20/0.52        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.52  thf(fc1_subset_1, axiom,
% 0.20/0.52    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.52  thf('15', plain, (![X26 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X26))),
% 0.20/0.52      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.20/0.52  thf('16', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.52      inference('clc', [status(thm)], ['14', '15'])).
% 0.20/0.52  thf(d1_zfmisc_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.20/0.52       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.20/0.52  thf('17', plain,
% 0.20/0.52      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X18 @ X17)
% 0.20/0.52          | (r1_tarski @ X18 @ X16)
% 0.20/0.52          | ((X17) != (k1_zfmisc_1 @ X16)))),
% 0.20/0.52      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.20/0.52  thf('18', plain,
% 0.20/0.52      (![X16 : $i, X18 : $i]:
% 0.20/0.52         ((r1_tarski @ X18 @ X16) | ~ (r2_hidden @ X18 @ (k1_zfmisc_1 @ X16)))),
% 0.20/0.52      inference('simplify', [status(thm)], ['17'])).
% 0.20/0.52  thf('19', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.20/0.52      inference('sup-', [status(thm)], ['16', '18'])).
% 0.20/0.52  thf('20', plain,
% 0.20/0.52      (![X12 : $i, X13 : $i]:
% 0.20/0.52         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 0.20/0.52      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.52  thf('21', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.20/0.52      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.52  thf('22', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.52      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.52  thf('23', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 0.20/0.52      inference('demod', [status(thm)], ['21', '22'])).
% 0.20/0.52  thf(t100_xboole_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.52  thf('24', plain,
% 0.20/0.52      (![X10 : $i, X11 : $i]:
% 0.20/0.52         ((k4_xboole_0 @ X10 @ X11)
% 0.20/0.52           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.52  thf('25', plain,
% 0.20/0.52      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.52      inference('sup+', [status(thm)], ['23', '24'])).
% 0.20/0.52  thf('26', plain,
% 0.20/0.52      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X6 @ X7)
% 0.20/0.52          | ~ (r2_hidden @ X6 @ X8)
% 0.20/0.52          | ~ (r2_hidden @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.20/0.52  thf('27', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X0 @ (k4_xboole_0 @ sk_A @ sk_B))
% 0.20/0.52          | ~ (r2_hidden @ X0 @ sk_B)
% 0.20/0.52          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.52  thf('28', plain,
% 0.20/0.52      ((((sk_B) = (k1_subset_1 @ sk_A))
% 0.20/0.52        | (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('29', plain,
% 0.20/0.52      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))
% 0.20/0.52         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))))),
% 0.20/0.52      inference('split', [status(esa)], ['28'])).
% 0.20/0.52  thf('30', plain,
% 0.20/0.52      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X2 @ X3)
% 0.20/0.52          | (r2_hidden @ X2 @ X4)
% 0.20/0.52          | ~ (r1_tarski @ X3 @ X4))),
% 0.20/0.52      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.52  thf('31', plain,
% 0.20/0.52      ((![X0 : $i]:
% 0.20/0.52          ((r2_hidden @ X0 @ (k3_subset_1 @ sk_A @ sk_B))
% 0.20/0.52           | ~ (r2_hidden @ X0 @ sk_B)))
% 0.20/0.52         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.52  thf('32', plain,
% 0.20/0.52      ((((sk_B) != (k1_subset_1 @ sk_A))
% 0.20/0.52        | ~ (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('33', plain,
% 0.20/0.52      (~ (((sk_B) = (k1_subset_1 @ sk_A))) | 
% 0.20/0.52       ~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.20/0.52      inference('split', [status(esa)], ['32'])).
% 0.20/0.52  thf('34', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.20/0.52      inference('sup-', [status(thm)], ['0', '5'])).
% 0.20/0.52  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.20/0.52  thf('35', plain, (![X23 : $i]: ((k1_subset_1 @ X23) = (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.20/0.52  thf('36', plain,
% 0.20/0.52      ((((sk_B) = (k1_subset_1 @ sk_A))) <= ((((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.20/0.52      inference('split', [status(esa)], ['28'])).
% 0.20/0.52  thf('37', plain,
% 0.20/0.52      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.20/0.52      inference('sup+', [status(thm)], ['35', '36'])).
% 0.20/0.52  thf('38', plain,
% 0.20/0.52      ((~ (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))
% 0.20/0.52         <= (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))))),
% 0.20/0.52      inference('split', [status(esa)], ['32'])).
% 0.20/0.52  thf('39', plain,
% 0.20/0.52      ((~ (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ k1_xboole_0)))
% 0.20/0.52         <= (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) & 
% 0.20/0.52             (((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['37', '38'])).
% 0.20/0.52  thf('40', plain,
% 0.20/0.52      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.20/0.52      inference('sup+', [status(thm)], ['35', '36'])).
% 0.20/0.52  thf('41', plain,
% 0.20/0.52      ((~ (r1_tarski @ k1_xboole_0 @ (k3_subset_1 @ sk_A @ k1_xboole_0)))
% 0.20/0.52         <= (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) & 
% 0.20/0.52             (((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.20/0.52      inference('demod', [status(thm)], ['39', '40'])).
% 0.20/0.52  thf('42', plain,
% 0.20/0.52      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.20/0.52       ~ (((sk_B) = (k1_subset_1 @ sk_A)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['34', '41'])).
% 0.20/0.52  thf('43', plain,
% 0.20/0.52      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.20/0.52       (((sk_B) = (k1_subset_1 @ sk_A)))),
% 0.20/0.52      inference('split', [status(esa)], ['28'])).
% 0.20/0.52  thf('44', plain, (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.20/0.52      inference('sat_resolution*', [status(thm)], ['33', '42', '43'])).
% 0.20/0.52  thf('45', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((r2_hidden @ X0 @ (k3_subset_1 @ sk_A @ sk_B))
% 0.20/0.52          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.20/0.52      inference('simpl_trail', [status(thm)], ['31', '44'])).
% 0.20/0.52  thf('46', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(d5_subset_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.52       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.20/0.52  thf('47', plain,
% 0.20/0.52      (![X24 : $i, X25 : $i]:
% 0.20/0.52         (((k3_subset_1 @ X24 @ X25) = (k4_xboole_0 @ X24 @ X25))
% 0.20/0.52          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X24)))),
% 0.20/0.52      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.20/0.52  thf('48', plain,
% 0.20/0.52      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.52      inference('sup-', [status(thm)], ['46', '47'])).
% 0.20/0.52  thf('49', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((r2_hidden @ X0 @ (k4_xboole_0 @ sk_A @ sk_B))
% 0.20/0.52          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.20/0.52      inference('demod', [status(thm)], ['45', '48'])).
% 0.20/0.52  thf('50', plain,
% 0.20/0.52      (![X0 : $i]: (~ (r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.20/0.52      inference('clc', [status(thm)], ['27', '49'])).
% 0.20/0.52  thf('51', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.20/0.52      inference('sup-', [status(thm)], ['16', '18'])).
% 0.20/0.52  thf('52', plain,
% 0.20/0.52      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X2 @ X3)
% 0.20/0.52          | (r2_hidden @ X2 @ X4)
% 0.20/0.52          | ~ (r1_tarski @ X3 @ X4))),
% 0.20/0.52      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.52  thf('53', plain,
% 0.20/0.52      (![X0 : $i]: ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.20/0.52      inference('sup-', [status(thm)], ['51', '52'])).
% 0.20/0.52  thf('54', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_B)),
% 0.20/0.52      inference('clc', [status(thm)], ['50', '53'])).
% 0.20/0.52  thf('55', plain, (![X0 : $i]: (r1_tarski @ sk_B @ X0)),
% 0.20/0.52      inference('sup-', [status(thm)], ['11', '54'])).
% 0.20/0.52  thf('56', plain,
% 0.20/0.52      (![X12 : $i, X13 : $i]:
% 0.20/0.52         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 0.20/0.52      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.52  thf('57', plain, (![X0 : $i]: ((k3_xboole_0 @ sk_B @ X0) = (sk_B))),
% 0.20/0.52      inference('sup-', [status(thm)], ['55', '56'])).
% 0.20/0.52  thf('58', plain, (((k1_xboole_0) = (sk_B))),
% 0.20/0.52      inference('sup+', [status(thm)], ['10', '57'])).
% 0.20/0.52  thf('59', plain,
% 0.20/0.52      ((((sk_B) != (k1_subset_1 @ sk_A)))
% 0.20/0.52         <= (~ (((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.20/0.52      inference('split', [status(esa)], ['32'])).
% 0.20/0.52  thf('60', plain, (![X23 : $i]: ((k1_subset_1 @ X23) = (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.20/0.52  thf('61', plain,
% 0.20/0.52      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.20/0.52      inference('demod', [status(thm)], ['59', '60'])).
% 0.20/0.52  thf('62', plain, (~ (((sk_B) = (k1_subset_1 @ sk_A)))),
% 0.20/0.52      inference('sat_resolution*', [status(thm)], ['33', '42'])).
% 0.20/0.52  thf('63', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.52      inference('simpl_trail', [status(thm)], ['61', '62'])).
% 0.20/0.52  thf('64', plain, ($false),
% 0.20/0.52      inference('simplify_reflect-', [status(thm)], ['58', '63'])).
% 0.20/0.52  
% 0.20/0.52  % SZS output end Refutation
% 0.20/0.52  
% 0.20/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
