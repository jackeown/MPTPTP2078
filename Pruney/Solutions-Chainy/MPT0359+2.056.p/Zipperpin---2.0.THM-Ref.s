%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6L2TktxZG5

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:39 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 279 expanded)
%              Number of leaves         :   21 (  90 expanded)
%              Depth                    :   16
%              Number of atoms          :  605 (2220 expanded)
%              Number of equality atoms :   49 ( 156 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(t39_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B )
      <=> ( B
          = ( k2_subset_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B )
        <=> ( B
            = ( k2_subset_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t39_subset_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('1',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_subset_1 @ X12 @ ( k3_subset_1 @ X12 @ X11 ) )
        = X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('2',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t38_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) )
      <=> ( B
          = ( k1_subset_1 @ A ) ) ) ) )).

thf('4',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ X21 @ ( k3_subset_1 @ X20 @ X21 ) )
      | ( X21
        = ( k1_subset_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t38_subset_1])).

thf('5',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
    | ~ ( m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( ( k3_subset_1 @ sk_A @ sk_B )
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('7',plain,(
    ! [X9: $i,X10: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X9 @ X10 ) @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('8',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
    | ( ( k3_subset_1 @ sk_A @ sk_B )
      = ( k1_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','8'])).

thf('10',plain,
    ( ( sk_B
      = ( k2_subset_1 @ sk_A ) )
    | ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['10'])).

thf('12',plain,
    ( ( sk_B
     != ( k2_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( sk_B
     != ( k2_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['12'])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('14',plain,(
    ! [X7: $i] :
      ( ( k2_subset_1 @ X7 )
      = X7 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('15',plain,
    ( ( sk_B
      = ( k2_subset_1 @ sk_A ) )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['10'])).

thf('16',plain,
    ( ( sk_B = sk_A )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('18',plain,(
    ! [X22: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('19',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_subset_1 @ X12 @ ( k3_subset_1 @ X12 @ X11 ) )
        = X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(t31_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ C )
          <=> ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf('21',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ~ ( r1_tarski @ ( k3_subset_1 @ X18 @ X17 ) @ ( k3_subset_1 @ X18 @ X19 ) )
      | ( r1_tarski @ X19 @ X17 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t31_subset_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k3_subset_1 @ X1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( r1_tarski @ X0 @ ( k3_subset_1 @ X1 @ k1_xboole_0 ) )
      | ~ ( m1_subset_1 @ ( k3_subset_1 @ X1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('23',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('24',plain,(
    ! [X22: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('25',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ( r2_hidden @ X13 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X22: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('32',plain,(
    ! [X9: $i,X10: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X9 @ X10 ) @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( r1_tarski @ X0 @ ( k3_subset_1 @ X1 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['22','30','33'])).

thf('35',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_A @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['29'])).

thf('37',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ X21 @ ( k3_subset_1 @ X20 @ X21 ) )
      | ( X21
        = ( k1_subset_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t38_subset_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( k1_xboole_0
        = ( k1_subset_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X22: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k1_subset_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf(t22_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ) )).

thf('41',plain,(
    ! [X16: $i] :
      ( ( k2_subset_1 @ X16 )
      = ( k3_subset_1 @ X16 @ ( k1_subset_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t22_subset_1])).

thf('42',plain,(
    ! [X7: $i] :
      ( ( k2_subset_1 @ X7 )
      = X7 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('43',plain,(
    ! [X16: $i] :
      ( X16
      = ( k3_subset_1 @ X16 @ ( k1_subset_1 @ X16 ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['40','43'])).

thf('45',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['35','44'])).

thf('46',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_A ) @ sk_A )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['16','45'])).

thf('47',plain,
    ( ( sk_B = sk_A )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('48',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
   <= ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['12'])).

thf('49',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_A )
   <= ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
      & ( sk_B
        = ( k2_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( sk_B = sk_A )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('51',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_A ) @ sk_A )
   <= ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
      & ( sk_B
        = ( k2_subset_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
    | ( sk_B
     != ( k2_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['46','51'])).

thf('53',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
    | ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['10'])).

thf('54',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ),
    inference('sat_resolution*',[status(thm)],['13','52','53'])).

thf('55',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(simpl_trail,[status(thm)],['11','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k1_subset_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('57',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['9','55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['40','43'])).

thf('59',plain,(
    sk_A = sk_B ),
    inference(demod,[status(thm)],['2','57','58'])).

thf('60',plain,
    ( ( sk_B
     != ( k2_subset_1 @ sk_A ) )
   <= ( sk_B
     != ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['12'])).

thf('61',plain,(
    ! [X7: $i] :
      ( ( k2_subset_1 @ X7 )
      = X7 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('62',plain,
    ( ( sk_B != sk_A )
   <= ( sk_B
     != ( k2_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    sk_B
 != ( k2_subset_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['13','52'])).

thf('64',plain,(
    sk_B != sk_A ),
    inference(simpl_trail,[status(thm)],['62','63'])).

thf('65',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['59','64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6L2TktxZG5
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:36:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.55  % Solved by: fo/fo7.sh
% 0.20/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.55  % done 212 iterations in 0.080s
% 0.20/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.55  % SZS output start Refutation
% 0.20/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.55  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.55  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.20/0.55  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.20/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.55  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.20/0.55  thf(t39_subset_1, conjecture,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.55       ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B ) <=>
% 0.20/0.55         ( ( B ) = ( k2_subset_1 @ A ) ) ) ))).
% 0.20/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.55    (~( ![A:$i,B:$i]:
% 0.20/0.55        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.55          ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B ) <=>
% 0.20/0.55            ( ( B ) = ( k2_subset_1 @ A ) ) ) ) )),
% 0.20/0.55    inference('cnf.neg', [status(esa)], [t39_subset_1])).
% 0.20/0.55  thf('0', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(involutiveness_k3_subset_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.55       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.20/0.55  thf('1', plain,
% 0.20/0.55      (![X11 : $i, X12 : $i]:
% 0.20/0.55         (((k3_subset_1 @ X12 @ (k3_subset_1 @ X12 @ X11)) = (X11))
% 0.20/0.55          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.20/0.55      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.20/0.55  thf('2', plain,
% 0.20/0.55      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.20/0.55      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.55  thf('3', plain,
% 0.20/0.55      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.20/0.55      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.55  thf(t38_subset_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.55       ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 0.20/0.55         ( ( B ) = ( k1_subset_1 @ A ) ) ) ))).
% 0.20/0.55  thf('4', plain,
% 0.20/0.55      (![X20 : $i, X21 : $i]:
% 0.20/0.55         (~ (r1_tarski @ X21 @ (k3_subset_1 @ X20 @ X21))
% 0.20/0.55          | ((X21) = (k1_subset_1 @ X20))
% 0.20/0.55          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X20)))),
% 0.20/0.55      inference('cnf', [status(esa)], [t38_subset_1])).
% 0.20/0.55  thf('5', plain,
% 0.20/0.55      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)
% 0.20/0.55        | ~ (m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))
% 0.20/0.55        | ((k3_subset_1 @ sk_A @ sk_B) = (k1_subset_1 @ sk_A)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.55  thf('6', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(dt_k3_subset_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.55       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.55  thf('7', plain,
% 0.20/0.55      (![X9 : $i, X10 : $i]:
% 0.20/0.55         ((m1_subset_1 @ (k3_subset_1 @ X9 @ X10) @ (k1_zfmisc_1 @ X9))
% 0.20/0.55          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X9)))),
% 0.20/0.55      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.20/0.55  thf('8', plain,
% 0.20/0.55      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.55      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.55  thf('9', plain,
% 0.20/0.55      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)
% 0.20/0.55        | ((k3_subset_1 @ sk_A @ sk_B) = (k1_subset_1 @ sk_A)))),
% 0.20/0.55      inference('demod', [status(thm)], ['5', '8'])).
% 0.20/0.55  thf('10', plain,
% 0.20/0.55      ((((sk_B) = (k2_subset_1 @ sk_A))
% 0.20/0.55        | (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('11', plain,
% 0.20/0.55      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))
% 0.20/0.55         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.20/0.55      inference('split', [status(esa)], ['10'])).
% 0.20/0.55  thf('12', plain,
% 0.20/0.55      ((((sk_B) != (k2_subset_1 @ sk_A))
% 0.20/0.55        | ~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('13', plain,
% 0.20/0.55      (~ (((sk_B) = (k2_subset_1 @ sk_A))) | 
% 0.20/0.55       ~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.20/0.55      inference('split', [status(esa)], ['12'])).
% 0.20/0.55  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.20/0.55  thf('14', plain, (![X7 : $i]: ((k2_subset_1 @ X7) = (X7))),
% 0.20/0.55      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.20/0.55  thf('15', plain,
% 0.20/0.55      ((((sk_B) = (k2_subset_1 @ sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.55      inference('split', [status(esa)], ['10'])).
% 0.20/0.55  thf('16', plain,
% 0.20/0.55      ((((sk_B) = (sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.55      inference('sup+', [status(thm)], ['14', '15'])).
% 0.20/0.55  thf('17', plain,
% 0.20/0.55      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.55      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.55  thf(t4_subset_1, axiom,
% 0.20/0.55    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.20/0.55  thf('18', plain,
% 0.20/0.55      (![X22 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X22))),
% 0.20/0.55      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.20/0.55  thf('19', plain,
% 0.20/0.55      (![X11 : $i, X12 : $i]:
% 0.20/0.55         (((k3_subset_1 @ X12 @ (k3_subset_1 @ X12 @ X11)) = (X11))
% 0.20/0.55          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.20/0.55      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.20/0.55  thf('20', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.55  thf(t31_subset_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.55       ( ![C:$i]:
% 0.20/0.55         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.55           ( ( r1_tarski @ B @ C ) <=>
% 0.20/0.55             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 0.20/0.55  thf('21', plain,
% 0.20/0.55      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.20/0.55         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18))
% 0.20/0.55          | ~ (r1_tarski @ (k3_subset_1 @ X18 @ X17) @ 
% 0.20/0.55               (k3_subset_1 @ X18 @ X19))
% 0.20/0.55          | (r1_tarski @ X19 @ X17)
% 0.20/0.55          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X18)))),
% 0.20/0.55      inference('cnf', [status(esa)], [t31_subset_1])).
% 0.20/0.55  thf('22', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         (~ (r1_tarski @ k1_xboole_0 @ (k3_subset_1 @ X1 @ X0))
% 0.20/0.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.20/0.55          | (r1_tarski @ X0 @ (k3_subset_1 @ X1 @ k1_xboole_0))
% 0.20/0.55          | ~ (m1_subset_1 @ (k3_subset_1 @ X1 @ k1_xboole_0) @ 
% 0.20/0.55               (k1_zfmisc_1 @ X1)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.55  thf(d3_tarski, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.55       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.55  thf('23', plain,
% 0.20/0.55      (![X1 : $i, X3 : $i]:
% 0.20/0.55         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.20/0.55      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.55  thf('24', plain,
% 0.20/0.55      (![X22 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X22))),
% 0.20/0.55      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.20/0.55  thf(l3_subset_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.55       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.20/0.55  thf('25', plain,
% 0.20/0.55      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.55         (~ (r2_hidden @ X13 @ X14)
% 0.20/0.55          | (r2_hidden @ X13 @ X15)
% 0.20/0.55          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 0.20/0.55      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.20/0.55  thf('26', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.55  thf('27', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         ((r1_tarski @ k1_xboole_0 @ X0)
% 0.20/0.55          | (r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X1))),
% 0.20/0.55      inference('sup-', [status(thm)], ['23', '26'])).
% 0.20/0.55  thf('28', plain,
% 0.20/0.55      (![X1 : $i, X3 : $i]:
% 0.20/0.55         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.20/0.55      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.55  thf('29', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         ((r1_tarski @ k1_xboole_0 @ X0) | (r1_tarski @ k1_xboole_0 @ X0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.55  thf('30', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.20/0.55      inference('simplify', [status(thm)], ['29'])).
% 0.20/0.55  thf('31', plain,
% 0.20/0.55      (![X22 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X22))),
% 0.20/0.55      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.20/0.55  thf('32', plain,
% 0.20/0.55      (![X9 : $i, X10 : $i]:
% 0.20/0.55         ((m1_subset_1 @ (k3_subset_1 @ X9 @ X10) @ (k1_zfmisc_1 @ X9))
% 0.20/0.55          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X9)))),
% 0.20/0.55      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.20/0.55  thf('33', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (m1_subset_1 @ (k3_subset_1 @ X0 @ k1_xboole_0) @ (k1_zfmisc_1 @ X0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.55  thf('34', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.20/0.55          | (r1_tarski @ X0 @ (k3_subset_1 @ X1 @ k1_xboole_0)))),
% 0.20/0.55      inference('demod', [status(thm)], ['22', '30', '33'])).
% 0.20/0.55  thf('35', plain,
% 0.20/0.55      ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ 
% 0.20/0.55        (k3_subset_1 @ sk_A @ k1_xboole_0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['17', '34'])).
% 0.20/0.55  thf('36', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.20/0.55      inference('simplify', [status(thm)], ['29'])).
% 0.20/0.55  thf('37', plain,
% 0.20/0.55      (![X20 : $i, X21 : $i]:
% 0.20/0.55         (~ (r1_tarski @ X21 @ (k3_subset_1 @ X20 @ X21))
% 0.20/0.55          | ((X21) = (k1_subset_1 @ X20))
% 0.20/0.55          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X20)))),
% 0.20/0.55      inference('cnf', [status(esa)], [t38_subset_1])).
% 0.20/0.55  thf('38', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 0.20/0.55          | ((k1_xboole_0) = (k1_subset_1 @ X0)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['36', '37'])).
% 0.20/0.55  thf('39', plain,
% 0.20/0.55      (![X22 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X22))),
% 0.20/0.55      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.20/0.55  thf('40', plain, (![X0 : $i]: ((k1_xboole_0) = (k1_subset_1 @ X0))),
% 0.20/0.55      inference('demod', [status(thm)], ['38', '39'])).
% 0.20/0.55  thf(t22_subset_1, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( k2_subset_1 @ A ) = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ))).
% 0.20/0.55  thf('41', plain,
% 0.20/0.55      (![X16 : $i]:
% 0.20/0.55         ((k2_subset_1 @ X16) = (k3_subset_1 @ X16 @ (k1_subset_1 @ X16)))),
% 0.20/0.55      inference('cnf', [status(esa)], [t22_subset_1])).
% 0.20/0.55  thf('42', plain, (![X7 : $i]: ((k2_subset_1 @ X7) = (X7))),
% 0.20/0.55      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.20/0.55  thf('43', plain,
% 0.20/0.55      (![X16 : $i]: ((X16) = (k3_subset_1 @ X16 @ (k1_subset_1 @ X16)))),
% 0.20/0.55      inference('demod', [status(thm)], ['41', '42'])).
% 0.20/0.55  thf('44', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 0.20/0.55      inference('sup+', [status(thm)], ['40', '43'])).
% 0.20/0.55  thf('45', plain, ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_A)),
% 0.20/0.55      inference('demod', [status(thm)], ['35', '44'])).
% 0.20/0.55  thf('46', plain,
% 0.20/0.55      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_A) @ sk_A))
% 0.20/0.55         <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.55      inference('sup+', [status(thm)], ['16', '45'])).
% 0.20/0.55  thf('47', plain,
% 0.20/0.55      ((((sk_B) = (sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.55      inference('sup+', [status(thm)], ['14', '15'])).
% 0.20/0.55  thf('48', plain,
% 0.20/0.55      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))
% 0.20/0.55         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.20/0.55      inference('split', [status(esa)], ['12'])).
% 0.20/0.55  thf('49', plain,
% 0.20/0.55      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_A))
% 0.20/0.55         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) & 
% 0.20/0.55             (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['47', '48'])).
% 0.20/0.55  thf('50', plain,
% 0.20/0.55      ((((sk_B) = (sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.55      inference('sup+', [status(thm)], ['14', '15'])).
% 0.20/0.55  thf('51', plain,
% 0.20/0.55      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_A) @ sk_A))
% 0.20/0.55         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) & 
% 0.20/0.55             (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.55      inference('demod', [status(thm)], ['49', '50'])).
% 0.20/0.55  thf('52', plain,
% 0.20/0.55      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) | 
% 0.20/0.55       ~ (((sk_B) = (k2_subset_1 @ sk_A)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['46', '51'])).
% 0.20/0.55  thf('53', plain,
% 0.20/0.55      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) | 
% 0.20/0.55       (((sk_B) = (k2_subset_1 @ sk_A)))),
% 0.20/0.55      inference('split', [status(esa)], ['10'])).
% 0.20/0.55  thf('54', plain, (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.20/0.55      inference('sat_resolution*', [status(thm)], ['13', '52', '53'])).
% 0.20/0.55  thf('55', plain, ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)),
% 0.20/0.55      inference('simpl_trail', [status(thm)], ['11', '54'])).
% 0.20/0.55  thf('56', plain, (![X0 : $i]: ((k1_xboole_0) = (k1_subset_1 @ X0))),
% 0.20/0.55      inference('demod', [status(thm)], ['38', '39'])).
% 0.20/0.55  thf('57', plain, (((k3_subset_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.20/0.55      inference('demod', [status(thm)], ['9', '55', '56'])).
% 0.20/0.55  thf('58', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 0.20/0.55      inference('sup+', [status(thm)], ['40', '43'])).
% 0.20/0.55  thf('59', plain, (((sk_A) = (sk_B))),
% 0.20/0.55      inference('demod', [status(thm)], ['2', '57', '58'])).
% 0.20/0.55  thf('60', plain,
% 0.20/0.55      ((((sk_B) != (k2_subset_1 @ sk_A)))
% 0.20/0.55         <= (~ (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.55      inference('split', [status(esa)], ['12'])).
% 0.20/0.55  thf('61', plain, (![X7 : $i]: ((k2_subset_1 @ X7) = (X7))),
% 0.20/0.55      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.20/0.55  thf('62', plain,
% 0.20/0.55      ((((sk_B) != (sk_A))) <= (~ (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.55      inference('demod', [status(thm)], ['60', '61'])).
% 0.20/0.55  thf('63', plain, (~ (((sk_B) = (k2_subset_1 @ sk_A)))),
% 0.20/0.55      inference('sat_resolution*', [status(thm)], ['13', '52'])).
% 0.20/0.55  thf('64', plain, (((sk_B) != (sk_A))),
% 0.20/0.55      inference('simpl_trail', [status(thm)], ['62', '63'])).
% 0.20/0.55  thf('65', plain, ($false),
% 0.20/0.55      inference('simplify_reflect-', [status(thm)], ['59', '64'])).
% 0.20/0.55  
% 0.20/0.55  % SZS output end Refutation
% 0.20/0.55  
% 0.20/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
