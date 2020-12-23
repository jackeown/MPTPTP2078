%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DKvNZdyhID

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:38 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 205 expanded)
%              Number of leaves         :   24 (  65 expanded)
%              Depth                    :   13
%              Number of atoms          :  580 (1714 expanded)
%              Number of equality atoms :   58 ( 169 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

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
    ! [X17: $i,X18: $i] :
      ( ( ( k3_subset_1 @ X18 @ ( k3_subset_1 @ X18 @ X17 ) )
        = X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('2',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_subset_1 @ X13 @ X14 )
        = ( k4_xboole_0 @ X13 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('5',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( k3_subset_1 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['2','5'])).

thf('7',plain,
    ( ( k3_subset_1 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['2','5'])).

thf(t38_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) )
      <=> ( B
          = ( k1_subset_1 @ A ) ) ) ) )).

thf('8',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ X21 @ ( k3_subset_1 @ X20 @ X21 ) )
      | ( X21
        = ( k1_subset_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t38_subset_1])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('9',plain,(
    ! [X11: $i] :
      ( ( k1_subset_1 @ X11 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('10',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ X21 @ ( k3_subset_1 @ X20 @ X21 ) )
      | ( X21 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,
    ( ~ ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_B )
    | ~ ( m1_subset_1 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( ( k4_xboole_0 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,
    ( ( sk_B
      = ( k2_subset_1 @ sk_A ) )
    | ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['12'])).

thf('14',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('15',plain,
    ( ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_B )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ( sk_B
     != ( k2_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( sk_B
     != ( k2_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['16'])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('18',plain,(
    ! [X12: $i] :
      ( ( k2_subset_1 @ X12 )
      = X12 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('19',plain,
    ( ( sk_B
      = ( k2_subset_1 @ sk_A ) )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['12'])).

thf('20',plain,
    ( ( sk_B = sk_A )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ sk_A ) )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_subset_1 @ X13 @ X14 )
        = ( k4_xboole_0 @ X13 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('24',plain,
    ( ( ( k3_subset_1 @ sk_A @ sk_A )
      = ( k4_xboole_0 @ sk_A @ sk_A ) )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( sk_B = sk_A )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('26',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
   <= ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['16'])).

thf('27',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_A )
   <= ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
      & ( sk_B
        = ( k2_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( sk_B = sk_A )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('29',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_A ) @ sk_A )
   <= ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
      & ( sk_B
        = ( k2_subset_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ~ ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_A ) @ sk_A )
   <= ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
      & ( sk_B
        = ( k2_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['24','29'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('32',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['31'])).

thf(t108_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ B ) ) )).

thf('33',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ( r1_tarski @ ( k3_xboole_0 @ X5 @ X7 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t108_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['31'])).

thf(t110_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k5_xboole_0 @ A @ C ) @ B ) ) )).

thf('36',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X10 @ X9 )
      | ( r1_tarski @ ( k5_xboole_0 @ X8 @ X10 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t110_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k5_xboole_0 @ X0 @ X1 ) @ X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('39',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
    | ( sk_B
     != ( k2_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['30','40'])).

thf('42',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
    | ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['12'])).

thf('43',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ),
    inference('sat_resolution*',[status(thm)],['17','41','42'])).

thf('44',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_B ),
    inference(simpl_trail,[status(thm)],['15','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('46',plain,(
    ! [X15: $i,X16: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X15 @ X16 ) @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('47',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('49',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['11','44','49'])).

thf(t22_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ) )).

thf('51',plain,(
    ! [X19: $i] :
      ( ( k2_subset_1 @ X19 )
      = ( k3_subset_1 @ X19 @ ( k1_subset_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t22_subset_1])).

thf('52',plain,(
    ! [X12: $i] :
      ( ( k2_subset_1 @ X12 )
      = X12 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('53',plain,(
    ! [X11: $i] :
      ( ( k1_subset_1 @ X11 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('54',plain,(
    ! [X19: $i] :
      ( X19
      = ( k3_subset_1 @ X19 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,(
    sk_A = sk_B ),
    inference(demod,[status(thm)],['6','50','54'])).

thf('56',plain,
    ( ( sk_B
     != ( k2_subset_1 @ sk_A ) )
   <= ( sk_B
     != ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['16'])).

thf('57',plain,(
    ! [X12: $i] :
      ( ( k2_subset_1 @ X12 )
      = X12 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('58',plain,
    ( ( sk_B != sk_A )
   <= ( sk_B
     != ( k2_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    sk_B
 != ( k2_subset_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['17','41'])).

thf('60',plain,(
    sk_B != sk_A ),
    inference(simpl_trail,[status(thm)],['58','59'])).

thf('61',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['55','60'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DKvNZdyhID
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:05:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.35/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.35/0.55  % Solved by: fo/fo7.sh
% 0.35/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.55  % done 133 iterations in 0.068s
% 0.35/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.35/0.55  % SZS output start Refutation
% 0.35/0.55  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.35/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.35/0.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.35/0.55  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.35/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.35/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.35/0.55  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.35/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.35/0.55  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.35/0.55  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.35/0.55  thf(t39_subset_1, conjecture,
% 0.35/0.55    (![A:$i,B:$i]:
% 0.35/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.35/0.55       ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B ) <=>
% 0.35/0.55         ( ( B ) = ( k2_subset_1 @ A ) ) ) ))).
% 0.35/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.55    (~( ![A:$i,B:$i]:
% 0.35/0.55        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.35/0.55          ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B ) <=>
% 0.35/0.55            ( ( B ) = ( k2_subset_1 @ A ) ) ) ) )),
% 0.35/0.55    inference('cnf.neg', [status(esa)], [t39_subset_1])).
% 0.35/0.55  thf('0', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf(involutiveness_k3_subset_1, axiom,
% 0.35/0.55    (![A:$i,B:$i]:
% 0.35/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.35/0.55       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.35/0.55  thf('1', plain,
% 0.35/0.55      (![X17 : $i, X18 : $i]:
% 0.35/0.55         (((k3_subset_1 @ X18 @ (k3_subset_1 @ X18 @ X17)) = (X17))
% 0.35/0.55          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18)))),
% 0.35/0.55      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.35/0.55  thf('2', plain,
% 0.35/0.55      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.35/0.55      inference('sup-', [status(thm)], ['0', '1'])).
% 0.35/0.55  thf('3', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf(d5_subset_1, axiom,
% 0.35/0.55    (![A:$i,B:$i]:
% 0.35/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.35/0.55       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.35/0.55  thf('4', plain,
% 0.35/0.55      (![X13 : $i, X14 : $i]:
% 0.35/0.55         (((k3_subset_1 @ X13 @ X14) = (k4_xboole_0 @ X13 @ X14))
% 0.35/0.55          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X13)))),
% 0.35/0.55      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.35/0.55  thf('5', plain,
% 0.35/0.55      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.35/0.55      inference('sup-', [status(thm)], ['3', '4'])).
% 0.35/0.55  thf('6', plain,
% 0.35/0.55      (((k3_subset_1 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B)) = (sk_B))),
% 0.35/0.55      inference('demod', [status(thm)], ['2', '5'])).
% 0.35/0.55  thf('7', plain,
% 0.35/0.55      (((k3_subset_1 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B)) = (sk_B))),
% 0.35/0.55      inference('demod', [status(thm)], ['2', '5'])).
% 0.35/0.55  thf(t38_subset_1, axiom,
% 0.35/0.55    (![A:$i,B:$i]:
% 0.35/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.35/0.55       ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 0.35/0.55         ( ( B ) = ( k1_subset_1 @ A ) ) ) ))).
% 0.35/0.55  thf('8', plain,
% 0.35/0.55      (![X20 : $i, X21 : $i]:
% 0.35/0.55         (~ (r1_tarski @ X21 @ (k3_subset_1 @ X20 @ X21))
% 0.35/0.55          | ((X21) = (k1_subset_1 @ X20))
% 0.35/0.55          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X20)))),
% 0.35/0.55      inference('cnf', [status(esa)], [t38_subset_1])).
% 0.35/0.55  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.35/0.55  thf('9', plain, (![X11 : $i]: ((k1_subset_1 @ X11) = (k1_xboole_0))),
% 0.35/0.55      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.35/0.55  thf('10', plain,
% 0.35/0.55      (![X20 : $i, X21 : $i]:
% 0.35/0.55         (~ (r1_tarski @ X21 @ (k3_subset_1 @ X20 @ X21))
% 0.35/0.55          | ((X21) = (k1_xboole_0))
% 0.35/0.55          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X20)))),
% 0.35/0.55      inference('demod', [status(thm)], ['8', '9'])).
% 0.35/0.55  thf('11', plain,
% 0.35/0.55      ((~ (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_B)
% 0.35/0.55        | ~ (m1_subset_1 @ (k4_xboole_0 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))
% 0.35/0.55        | ((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['7', '10'])).
% 0.35/0.55  thf('12', plain,
% 0.35/0.55      ((((sk_B) = (k2_subset_1 @ sk_A))
% 0.35/0.55        | (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('13', plain,
% 0.35/0.55      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))
% 0.35/0.55         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.35/0.55      inference('split', [status(esa)], ['12'])).
% 0.35/0.55  thf('14', plain,
% 0.35/0.55      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.35/0.55      inference('sup-', [status(thm)], ['3', '4'])).
% 0.35/0.55  thf('15', plain,
% 0.35/0.55      (((r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_B))
% 0.35/0.55         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.35/0.55      inference('demod', [status(thm)], ['13', '14'])).
% 0.35/0.55  thf('16', plain,
% 0.35/0.55      ((((sk_B) != (k2_subset_1 @ sk_A))
% 0.35/0.55        | ~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('17', plain,
% 0.35/0.55      (~ (((sk_B) = (k2_subset_1 @ sk_A))) | 
% 0.35/0.55       ~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.35/0.55      inference('split', [status(esa)], ['16'])).
% 0.35/0.55  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.35/0.55  thf('18', plain, (![X12 : $i]: ((k2_subset_1 @ X12) = (X12))),
% 0.35/0.55      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.35/0.55  thf('19', plain,
% 0.35/0.55      ((((sk_B) = (k2_subset_1 @ sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.35/0.55      inference('split', [status(esa)], ['12'])).
% 0.35/0.55  thf('20', plain,
% 0.35/0.55      ((((sk_B) = (sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.35/0.55      inference('sup+', [status(thm)], ['18', '19'])).
% 0.35/0.55  thf('21', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('22', plain,
% 0.35/0.55      (((m1_subset_1 @ sk_A @ (k1_zfmisc_1 @ sk_A)))
% 0.35/0.55         <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.35/0.55      inference('sup+', [status(thm)], ['20', '21'])).
% 0.35/0.55  thf('23', plain,
% 0.35/0.55      (![X13 : $i, X14 : $i]:
% 0.35/0.55         (((k3_subset_1 @ X13 @ X14) = (k4_xboole_0 @ X13 @ X14))
% 0.35/0.55          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X13)))),
% 0.35/0.55      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.35/0.55  thf('24', plain,
% 0.35/0.55      ((((k3_subset_1 @ sk_A @ sk_A) = (k4_xboole_0 @ sk_A @ sk_A)))
% 0.35/0.55         <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.35/0.55      inference('sup-', [status(thm)], ['22', '23'])).
% 0.35/0.55  thf('25', plain,
% 0.35/0.55      ((((sk_B) = (sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.35/0.55      inference('sup+', [status(thm)], ['18', '19'])).
% 0.35/0.55  thf('26', plain,
% 0.35/0.55      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))
% 0.35/0.55         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.35/0.55      inference('split', [status(esa)], ['16'])).
% 0.35/0.55  thf('27', plain,
% 0.35/0.55      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_A))
% 0.35/0.55         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) & 
% 0.35/0.55             (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.35/0.55      inference('sup-', [status(thm)], ['25', '26'])).
% 0.35/0.55  thf('28', plain,
% 0.35/0.55      ((((sk_B) = (sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.35/0.55      inference('sup+', [status(thm)], ['18', '19'])).
% 0.35/0.55  thf('29', plain,
% 0.35/0.55      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_A) @ sk_A))
% 0.35/0.55         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) & 
% 0.35/0.55             (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.35/0.55      inference('demod', [status(thm)], ['27', '28'])).
% 0.35/0.55  thf('30', plain,
% 0.35/0.55      ((~ (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_A) @ sk_A))
% 0.35/0.55         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) & 
% 0.35/0.55             (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.35/0.55      inference('sup-', [status(thm)], ['24', '29'])).
% 0.35/0.55  thf(d10_xboole_0, axiom,
% 0.35/0.55    (![A:$i,B:$i]:
% 0.35/0.55     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.35/0.55  thf('31', plain,
% 0.35/0.55      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.35/0.55      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.35/0.55  thf('32', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.35/0.55      inference('simplify', [status(thm)], ['31'])).
% 0.35/0.55  thf(t108_xboole_1, axiom,
% 0.35/0.55    (![A:$i,B:$i,C:$i]:
% 0.35/0.55     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ B ) ))).
% 0.35/0.55  thf('33', plain,
% 0.35/0.55      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.35/0.55         (~ (r1_tarski @ X5 @ X6) | (r1_tarski @ (k3_xboole_0 @ X5 @ X7) @ X6))),
% 0.35/0.55      inference('cnf', [status(esa)], [t108_xboole_1])).
% 0.35/0.55  thf('34', plain,
% 0.35/0.55      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.35/0.55      inference('sup-', [status(thm)], ['32', '33'])).
% 0.35/0.55  thf('35', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.35/0.55      inference('simplify', [status(thm)], ['31'])).
% 0.35/0.55  thf(t110_xboole_1, axiom,
% 0.35/0.55    (![A:$i,B:$i,C:$i]:
% 0.35/0.55     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 0.35/0.55       ( r1_tarski @ ( k5_xboole_0 @ A @ C ) @ B ) ))).
% 0.35/0.55  thf('36', plain,
% 0.35/0.55      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.35/0.55         (~ (r1_tarski @ X8 @ X9)
% 0.35/0.55          | ~ (r1_tarski @ X10 @ X9)
% 0.35/0.55          | (r1_tarski @ (k5_xboole_0 @ X8 @ X10) @ X9))),
% 0.35/0.55      inference('cnf', [status(esa)], [t110_xboole_1])).
% 0.35/0.55  thf('37', plain,
% 0.35/0.55      (![X0 : $i, X1 : $i]:
% 0.35/0.55         ((r1_tarski @ (k5_xboole_0 @ X0 @ X1) @ X0) | ~ (r1_tarski @ X1 @ X0))),
% 0.35/0.55      inference('sup-', [status(thm)], ['35', '36'])).
% 0.35/0.55  thf('38', plain,
% 0.35/0.55      (![X0 : $i, X1 : $i]:
% 0.35/0.55         (r1_tarski @ (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)) @ X0)),
% 0.35/0.55      inference('sup-', [status(thm)], ['34', '37'])).
% 0.35/0.55  thf(t100_xboole_1, axiom,
% 0.35/0.55    (![A:$i,B:$i]:
% 0.35/0.55     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.35/0.55  thf('39', plain,
% 0.35/0.55      (![X3 : $i, X4 : $i]:
% 0.35/0.55         ((k4_xboole_0 @ X3 @ X4)
% 0.35/0.55           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.35/0.55      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.35/0.55  thf('40', plain,
% 0.35/0.55      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 0.35/0.55      inference('demod', [status(thm)], ['38', '39'])).
% 0.35/0.55  thf('41', plain,
% 0.35/0.55      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) | 
% 0.35/0.55       ~ (((sk_B) = (k2_subset_1 @ sk_A)))),
% 0.35/0.55      inference('demod', [status(thm)], ['30', '40'])).
% 0.35/0.55  thf('42', plain,
% 0.35/0.55      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) | 
% 0.35/0.55       (((sk_B) = (k2_subset_1 @ sk_A)))),
% 0.35/0.55      inference('split', [status(esa)], ['12'])).
% 0.35/0.55  thf('43', plain, (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.35/0.55      inference('sat_resolution*', [status(thm)], ['17', '41', '42'])).
% 0.35/0.55  thf('44', plain, ((r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_B)),
% 0.35/0.55      inference('simpl_trail', [status(thm)], ['15', '43'])).
% 0.35/0.55  thf('45', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf(dt_k3_subset_1, axiom,
% 0.35/0.55    (![A:$i,B:$i]:
% 0.35/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.35/0.55       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.35/0.55  thf('46', plain,
% 0.35/0.55      (![X15 : $i, X16 : $i]:
% 0.35/0.55         ((m1_subset_1 @ (k3_subset_1 @ X15 @ X16) @ (k1_zfmisc_1 @ X15))
% 0.35/0.55          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X15)))),
% 0.35/0.55      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.35/0.55  thf('47', plain,
% 0.35/0.55      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.35/0.55      inference('sup-', [status(thm)], ['45', '46'])).
% 0.35/0.55  thf('48', plain,
% 0.35/0.55      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.35/0.55      inference('sup-', [status(thm)], ['3', '4'])).
% 0.35/0.55  thf('49', plain,
% 0.35/0.55      ((m1_subset_1 @ (k4_xboole_0 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.35/0.55      inference('demod', [status(thm)], ['47', '48'])).
% 0.35/0.55  thf('50', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.35/0.55      inference('demod', [status(thm)], ['11', '44', '49'])).
% 0.35/0.55  thf(t22_subset_1, axiom,
% 0.35/0.55    (![A:$i]:
% 0.35/0.55     ( ( k2_subset_1 @ A ) = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ))).
% 0.35/0.55  thf('51', plain,
% 0.35/0.55      (![X19 : $i]:
% 0.35/0.55         ((k2_subset_1 @ X19) = (k3_subset_1 @ X19 @ (k1_subset_1 @ X19)))),
% 0.35/0.55      inference('cnf', [status(esa)], [t22_subset_1])).
% 0.35/0.55  thf('52', plain, (![X12 : $i]: ((k2_subset_1 @ X12) = (X12))),
% 0.35/0.55      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.35/0.55  thf('53', plain, (![X11 : $i]: ((k1_subset_1 @ X11) = (k1_xboole_0))),
% 0.35/0.55      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.35/0.55  thf('54', plain, (![X19 : $i]: ((X19) = (k3_subset_1 @ X19 @ k1_xboole_0))),
% 0.35/0.55      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.35/0.55  thf('55', plain, (((sk_A) = (sk_B))),
% 0.35/0.55      inference('demod', [status(thm)], ['6', '50', '54'])).
% 0.35/0.55  thf('56', plain,
% 0.35/0.55      ((((sk_B) != (k2_subset_1 @ sk_A)))
% 0.35/0.55         <= (~ (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.35/0.55      inference('split', [status(esa)], ['16'])).
% 0.35/0.55  thf('57', plain, (![X12 : $i]: ((k2_subset_1 @ X12) = (X12))),
% 0.35/0.55      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.35/0.55  thf('58', plain,
% 0.35/0.55      ((((sk_B) != (sk_A))) <= (~ (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.35/0.55      inference('demod', [status(thm)], ['56', '57'])).
% 0.35/0.55  thf('59', plain, (~ (((sk_B) = (k2_subset_1 @ sk_A)))),
% 0.35/0.55      inference('sat_resolution*', [status(thm)], ['17', '41'])).
% 0.35/0.55  thf('60', plain, (((sk_B) != (sk_A))),
% 0.35/0.55      inference('simpl_trail', [status(thm)], ['58', '59'])).
% 0.35/0.55  thf('61', plain, ($false),
% 0.35/0.55      inference('simplify_reflect-', [status(thm)], ['55', '60'])).
% 0.35/0.55  
% 0.35/0.55  % SZS output end Refutation
% 0.35/0.55  
% 0.39/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
