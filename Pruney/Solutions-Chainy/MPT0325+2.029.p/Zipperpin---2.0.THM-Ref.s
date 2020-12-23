%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.v9y1VP1WO3

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:44 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 106 expanded)
%              Number of leaves         :   19 (  36 expanded)
%              Depth                    :   17
%              Number of atoms          :  534 ( 891 expanded)
%              Number of equality atoms :   56 (  86 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t138_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
     => ( ( ( k2_zfmisc_1 @ A @ B )
          = k1_xboole_0 )
        | ( ( r1_tarski @ A @ C )
          & ( r1_tarski @ B @ D ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
       => ( ( ( k2_zfmisc_1 @ A @ B )
            = k1_xboole_0 )
          | ( ( r1_tarski @ A @ C )
            & ( r1_tarski @ B @ D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t138_zfmisc_1])).

thf('0',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t37_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X6: $i,X8: $i] :
      ( ( ( k4_xboole_0 @ X6 @ X8 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t37_xboole_1])).

thf('3',plain,
    ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t126_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k4_xboole_0 @ A @ C ) @ B ) @ ( k2_zfmisc_1 @ A @ ( k4_xboole_0 @ B @ D ) ) ) ) )).

thf('4',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ X20 @ X22 ) @ ( k2_zfmisc_1 @ X21 @ X23 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k4_xboole_0 @ X20 @ X21 ) @ X22 ) @ ( k2_zfmisc_1 @ X20 @ ( k4_xboole_0 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[t126_zfmisc_1])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('5',plain,(
    ! [X5: $i] :
      ( r1_tarski @ k1_xboole_0 @ X5 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t9_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('6',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X11 @ X12 )
      | ( r1_tarski @ ( k2_xboole_0 @ X11 @ X13 ) @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t9_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ k1_xboole_0 @ X1 ) @ ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X5: $i] :
      ( r1_tarski @ k1_xboole_0 @ X5 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('9',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ X4 @ X3 )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ X3 @ ( k4_xboole_0 @ X2 @ X0 ) ) @ ( k4_xboole_0 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','11'])).

thf('13',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_D ) ) @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['3','12'])).

thf('14',plain,(
    ! [X5: $i] :
      ( r1_tarski @ k1_xboole_0 @ X5 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('15',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( k2_zfmisc_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_D ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['13','16'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('18',plain,(
    ! [X14: $i,X15: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X15 @ X14 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('19',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_B @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( ( k4_xboole_0 @ sk_B @ sk_D )
      = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ( ( k4_xboole_0 @ X6 @ X7 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t37_xboole_1])).

thf('22',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( r1_tarski @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( r1_tarski @ sk_B @ sk_D )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_C )
    | ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_D )
   <= ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['24'])).

thf('26',plain,
    ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf('27',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ X20 @ X22 ) @ ( k2_zfmisc_1 @ X21 @ X23 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k4_xboole_0 @ X20 @ X21 ) @ X22 ) @ ( k2_zfmisc_1 @ X20 @ ( k4_xboole_0 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[t126_zfmisc_1])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('28',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ X9 @ ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ ( k4_xboole_0 @ X3 @ X1 ) @ X2 ) @ ( k4_xboole_0 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ ( k4_xboole_0 @ sk_A @ sk_C ) @ sk_B ) @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k2_zfmisc_1 @ X15 @ X16 )
        = k1_xboole_0 )
      | ( X16 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('32',plain,(
    ! [X15: $i] :
      ( ( k2_zfmisc_1 @ X15 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['31'])).

thf(t117_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ C @ A ) )
          | ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ A @ C ) ) )
        & ~ ( r1_tarski @ B @ C ) ) )).

thf('33',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( X17 = k1_xboole_0 )
      | ( r1_tarski @ X18 @ X19 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X17 @ X18 ) @ ( k2_zfmisc_1 @ X17 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ X1 ) @ k1_xboole_0 )
      | ( r1_tarski @ X1 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_C )
      = k1_xboole_0 )
    | ( r1_tarski @ sk_B @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('37',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_C )
      = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ( ( k4_xboole_0 @ X6 @ X7 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t37_xboole_1])).

thf('39',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( r1_tarski @ sk_A @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_C )
   <= ~ ( r1_tarski @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['24'])).

thf('42',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X15: $i] :
      ( ( k2_zfmisc_1 @ X15 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['31'])).

thf('46',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    r1_tarski @ sk_A @ sk_C ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_D )
    | ~ ( r1_tarski @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['24'])).

thf('49',plain,(
    ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference('sat_resolution*',[status(thm)],['47','48'])).

thf('50',plain,(
    ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['25','49'])).

thf('51',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['23','50'])).

thf('52',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k2_zfmisc_1 @ X15 @ X16 )
        = k1_xboole_0 )
      | ( X15 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('53',plain,(
    ! [X16: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X16 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','51','53'])).

thf('55',plain,(
    $false ),
    inference(simplify,[status(thm)],['54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.v9y1VP1WO3
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:22:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.44/0.63  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.44/0.63  % Solved by: fo/fo7.sh
% 0.44/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.63  % done 214 iterations in 0.181s
% 0.44/0.63  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.44/0.63  % SZS output start Refutation
% 0.44/0.63  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.44/0.63  thf(sk_D_type, type, sk_D: $i).
% 0.44/0.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.44/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.44/0.63  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.44/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.63  thf(sk_C_type, type, sk_C: $i).
% 0.44/0.63  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.44/0.63  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.44/0.63  thf(t138_zfmisc_1, conjecture,
% 0.44/0.63    (![A:$i,B:$i,C:$i,D:$i]:
% 0.44/0.63     ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =>
% 0.44/0.63       ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) | 
% 0.44/0.63         ( ( r1_tarski @ A @ C ) & ( r1_tarski @ B @ D ) ) ) ))).
% 0.44/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.63    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.44/0.63        ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =>
% 0.44/0.63          ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) | 
% 0.44/0.63            ( ( r1_tarski @ A @ C ) & ( r1_tarski @ B @ D ) ) ) ) )),
% 0.44/0.63    inference('cnf.neg', [status(esa)], [t138_zfmisc_1])).
% 0.44/0.63  thf('0', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0))),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('1', plain,
% 0.44/0.63      ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ (k2_zfmisc_1 @ sk_C @ sk_D))),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf(t37_xboole_1, axiom,
% 0.44/0.63    (![A:$i,B:$i]:
% 0.44/0.63     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.44/0.63  thf('2', plain,
% 0.44/0.63      (![X6 : $i, X8 : $i]:
% 0.44/0.63         (((k4_xboole_0 @ X6 @ X8) = (k1_xboole_0)) | ~ (r1_tarski @ X6 @ X8))),
% 0.44/0.63      inference('cnf', [status(esa)], [t37_xboole_1])).
% 0.44/0.63  thf('3', plain,
% 0.44/0.63      (((k4_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 0.44/0.63         (k2_zfmisc_1 @ sk_C @ sk_D)) = (k1_xboole_0))),
% 0.44/0.63      inference('sup-', [status(thm)], ['1', '2'])).
% 0.44/0.63  thf(t126_zfmisc_1, axiom,
% 0.44/0.63    (![A:$i,B:$i,C:$i,D:$i]:
% 0.44/0.63     ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =
% 0.44/0.63       ( k2_xboole_0 @
% 0.44/0.63         ( k2_zfmisc_1 @ ( k4_xboole_0 @ A @ C ) @ B ) @ 
% 0.44/0.63         ( k2_zfmisc_1 @ A @ ( k4_xboole_0 @ B @ D ) ) ) ))).
% 0.44/0.63  thf('4', plain,
% 0.44/0.63      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.44/0.63         ((k4_xboole_0 @ (k2_zfmisc_1 @ X20 @ X22) @ (k2_zfmisc_1 @ X21 @ X23))
% 0.44/0.63           = (k2_xboole_0 @ (k2_zfmisc_1 @ (k4_xboole_0 @ X20 @ X21) @ X22) @ 
% 0.44/0.63              (k2_zfmisc_1 @ X20 @ (k4_xboole_0 @ X22 @ X23))))),
% 0.44/0.63      inference('cnf', [status(esa)], [t126_zfmisc_1])).
% 0.44/0.63  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.44/0.63  thf('5', plain, (![X5 : $i]: (r1_tarski @ k1_xboole_0 @ X5)),
% 0.44/0.63      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.44/0.63  thf(t9_xboole_1, axiom,
% 0.44/0.63    (![A:$i,B:$i,C:$i]:
% 0.44/0.63     ( ( r1_tarski @ A @ B ) =>
% 0.44/0.63       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.44/0.63  thf('6', plain,
% 0.44/0.63      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.44/0.63         (~ (r1_tarski @ X11 @ X12)
% 0.44/0.63          | (r1_tarski @ (k2_xboole_0 @ X11 @ X13) @ (k2_xboole_0 @ X12 @ X13)))),
% 0.44/0.63      inference('cnf', [status(esa)], [t9_xboole_1])).
% 0.44/0.63  thf('7', plain,
% 0.44/0.63      (![X0 : $i, X1 : $i]:
% 0.44/0.63         (r1_tarski @ (k2_xboole_0 @ k1_xboole_0 @ X1) @ 
% 0.44/0.63          (k2_xboole_0 @ X0 @ X1))),
% 0.44/0.63      inference('sup-', [status(thm)], ['5', '6'])).
% 0.44/0.63  thf('8', plain, (![X5 : $i]: (r1_tarski @ k1_xboole_0 @ X5)),
% 0.44/0.63      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.44/0.63  thf(t12_xboole_1, axiom,
% 0.44/0.63    (![A:$i,B:$i]:
% 0.44/0.63     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.44/0.63  thf('9', plain,
% 0.44/0.63      (![X3 : $i, X4 : $i]:
% 0.44/0.63         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 0.44/0.63      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.44/0.63  thf('10', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.44/0.63      inference('sup-', [status(thm)], ['8', '9'])).
% 0.44/0.63  thf('11', plain,
% 0.44/0.63      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X0 @ X1))),
% 0.44/0.63      inference('demod', [status(thm)], ['7', '10'])).
% 0.44/0.63  thf('12', plain,
% 0.44/0.63      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.44/0.63         (r1_tarski @ (k2_zfmisc_1 @ X3 @ (k4_xboole_0 @ X2 @ X0)) @ 
% 0.44/0.63          (k4_xboole_0 @ (k2_zfmisc_1 @ X3 @ X2) @ (k2_zfmisc_1 @ X1 @ X0)))),
% 0.44/0.63      inference('sup+', [status(thm)], ['4', '11'])).
% 0.44/0.63  thf('13', plain,
% 0.44/0.63      ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_D)) @ 
% 0.44/0.63        k1_xboole_0)),
% 0.44/0.63      inference('sup+', [status(thm)], ['3', '12'])).
% 0.44/0.63  thf('14', plain, (![X5 : $i]: (r1_tarski @ k1_xboole_0 @ X5)),
% 0.44/0.63      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.44/0.63  thf(d10_xboole_0, axiom,
% 0.44/0.63    (![A:$i,B:$i]:
% 0.44/0.63     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.44/0.63  thf('15', plain,
% 0.44/0.63      (![X0 : $i, X2 : $i]:
% 0.44/0.63         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.44/0.63      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.44/0.63  thf('16', plain,
% 0.44/0.63      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.44/0.63      inference('sup-', [status(thm)], ['14', '15'])).
% 0.44/0.63  thf('17', plain,
% 0.44/0.63      (((k2_zfmisc_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_D)) = (k1_xboole_0))),
% 0.44/0.63      inference('sup-', [status(thm)], ['13', '16'])).
% 0.44/0.63  thf(t113_zfmisc_1, axiom,
% 0.44/0.63    (![A:$i,B:$i]:
% 0.44/0.63     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.44/0.63       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.44/0.63  thf('18', plain,
% 0.44/0.63      (![X14 : $i, X15 : $i]:
% 0.44/0.63         (((X14) = (k1_xboole_0))
% 0.44/0.63          | ((X15) = (k1_xboole_0))
% 0.44/0.63          | ((k2_zfmisc_1 @ X15 @ X14) != (k1_xboole_0)))),
% 0.44/0.63      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.44/0.63  thf('19', plain,
% 0.44/0.63      ((((k1_xboole_0) != (k1_xboole_0))
% 0.44/0.63        | ((sk_A) = (k1_xboole_0))
% 0.44/0.63        | ((k4_xboole_0 @ sk_B @ sk_D) = (k1_xboole_0)))),
% 0.44/0.63      inference('sup-', [status(thm)], ['17', '18'])).
% 0.44/0.63  thf('20', plain,
% 0.44/0.63      ((((k4_xboole_0 @ sk_B @ sk_D) = (k1_xboole_0))
% 0.44/0.63        | ((sk_A) = (k1_xboole_0)))),
% 0.44/0.63      inference('simplify', [status(thm)], ['19'])).
% 0.44/0.63  thf('21', plain,
% 0.44/0.63      (![X6 : $i, X7 : $i]:
% 0.44/0.63         ((r1_tarski @ X6 @ X7) | ((k4_xboole_0 @ X6 @ X7) != (k1_xboole_0)))),
% 0.44/0.63      inference('cnf', [status(esa)], [t37_xboole_1])).
% 0.44/0.63  thf('22', plain,
% 0.44/0.63      ((((k1_xboole_0) != (k1_xboole_0))
% 0.44/0.63        | ((sk_A) = (k1_xboole_0))
% 0.44/0.63        | (r1_tarski @ sk_B @ sk_D))),
% 0.44/0.63      inference('sup-', [status(thm)], ['20', '21'])).
% 0.44/0.63  thf('23', plain, (((r1_tarski @ sk_B @ sk_D) | ((sk_A) = (k1_xboole_0)))),
% 0.44/0.63      inference('simplify', [status(thm)], ['22'])).
% 0.44/0.63  thf('24', plain,
% 0.44/0.63      ((~ (r1_tarski @ sk_A @ sk_C) | ~ (r1_tarski @ sk_B @ sk_D))),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('25', plain,
% 0.44/0.63      ((~ (r1_tarski @ sk_B @ sk_D)) <= (~ ((r1_tarski @ sk_B @ sk_D)))),
% 0.44/0.63      inference('split', [status(esa)], ['24'])).
% 0.44/0.63  thf('26', plain,
% 0.44/0.63      (((k4_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 0.44/0.63         (k2_zfmisc_1 @ sk_C @ sk_D)) = (k1_xboole_0))),
% 0.44/0.63      inference('sup-', [status(thm)], ['1', '2'])).
% 0.44/0.63  thf('27', plain,
% 0.44/0.63      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.44/0.63         ((k4_xboole_0 @ (k2_zfmisc_1 @ X20 @ X22) @ (k2_zfmisc_1 @ X21 @ X23))
% 0.44/0.63           = (k2_xboole_0 @ (k2_zfmisc_1 @ (k4_xboole_0 @ X20 @ X21) @ X22) @ 
% 0.44/0.63              (k2_zfmisc_1 @ X20 @ (k4_xboole_0 @ X22 @ X23))))),
% 0.44/0.63      inference('cnf', [status(esa)], [t126_zfmisc_1])).
% 0.44/0.63  thf(t7_xboole_1, axiom,
% 0.44/0.63    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.44/0.63  thf('28', plain,
% 0.44/0.63      (![X9 : $i, X10 : $i]: (r1_tarski @ X9 @ (k2_xboole_0 @ X9 @ X10))),
% 0.44/0.63      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.44/0.63  thf('29', plain,
% 0.44/0.63      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.44/0.63         (r1_tarski @ (k2_zfmisc_1 @ (k4_xboole_0 @ X3 @ X1) @ X2) @ 
% 0.44/0.63          (k4_xboole_0 @ (k2_zfmisc_1 @ X3 @ X2) @ (k2_zfmisc_1 @ X1 @ X0)))),
% 0.44/0.63      inference('sup+', [status(thm)], ['27', '28'])).
% 0.44/0.63  thf('30', plain,
% 0.44/0.63      ((r1_tarski @ (k2_zfmisc_1 @ (k4_xboole_0 @ sk_A @ sk_C) @ sk_B) @ 
% 0.44/0.63        k1_xboole_0)),
% 0.44/0.63      inference('sup+', [status(thm)], ['26', '29'])).
% 0.44/0.63  thf('31', plain,
% 0.44/0.63      (![X15 : $i, X16 : $i]:
% 0.44/0.63         (((k2_zfmisc_1 @ X15 @ X16) = (k1_xboole_0))
% 0.44/0.63          | ((X16) != (k1_xboole_0)))),
% 0.44/0.63      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.44/0.63  thf('32', plain,
% 0.44/0.63      (![X15 : $i]: ((k2_zfmisc_1 @ X15 @ k1_xboole_0) = (k1_xboole_0))),
% 0.44/0.63      inference('simplify', [status(thm)], ['31'])).
% 0.44/0.63  thf(t117_zfmisc_1, axiom,
% 0.44/0.63    (![A:$i,B:$i,C:$i]:
% 0.44/0.63     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.44/0.63          ( ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ C @ A ) ) | 
% 0.44/0.63            ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ A @ C ) ) ) & 
% 0.44/0.63          ( ~( r1_tarski @ B @ C ) ) ) ))).
% 0.44/0.63  thf('33', plain,
% 0.44/0.63      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.44/0.63         (((X17) = (k1_xboole_0))
% 0.44/0.63          | (r1_tarski @ X18 @ X19)
% 0.44/0.63          | ~ (r1_tarski @ (k2_zfmisc_1 @ X17 @ X18) @ 
% 0.44/0.63               (k2_zfmisc_1 @ X17 @ X19)))),
% 0.44/0.63      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 0.44/0.63  thf('34', plain,
% 0.44/0.63      (![X0 : $i, X1 : $i]:
% 0.44/0.63         (~ (r1_tarski @ (k2_zfmisc_1 @ X0 @ X1) @ k1_xboole_0)
% 0.44/0.63          | (r1_tarski @ X1 @ k1_xboole_0)
% 0.44/0.63          | ((X0) = (k1_xboole_0)))),
% 0.44/0.63      inference('sup-', [status(thm)], ['32', '33'])).
% 0.44/0.63  thf('35', plain,
% 0.44/0.63      ((((k4_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0))
% 0.44/0.63        | (r1_tarski @ sk_B @ k1_xboole_0))),
% 0.44/0.63      inference('sup-', [status(thm)], ['30', '34'])).
% 0.44/0.63  thf('36', plain,
% 0.44/0.63      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.44/0.63      inference('sup-', [status(thm)], ['14', '15'])).
% 0.44/0.63  thf('37', plain,
% 0.44/0.63      ((((k4_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0))
% 0.44/0.63        | ((sk_B) = (k1_xboole_0)))),
% 0.44/0.63      inference('sup-', [status(thm)], ['35', '36'])).
% 0.44/0.63  thf('38', plain,
% 0.44/0.63      (![X6 : $i, X7 : $i]:
% 0.44/0.63         ((r1_tarski @ X6 @ X7) | ((k4_xboole_0 @ X6 @ X7) != (k1_xboole_0)))),
% 0.44/0.63      inference('cnf', [status(esa)], [t37_xboole_1])).
% 0.44/0.63  thf('39', plain,
% 0.44/0.63      ((((k1_xboole_0) != (k1_xboole_0))
% 0.44/0.63        | ((sk_B) = (k1_xboole_0))
% 0.44/0.63        | (r1_tarski @ sk_A @ sk_C))),
% 0.44/0.63      inference('sup-', [status(thm)], ['37', '38'])).
% 0.44/0.63  thf('40', plain, (((r1_tarski @ sk_A @ sk_C) | ((sk_B) = (k1_xboole_0)))),
% 0.44/0.63      inference('simplify', [status(thm)], ['39'])).
% 0.44/0.63  thf('41', plain,
% 0.44/0.63      ((~ (r1_tarski @ sk_A @ sk_C)) <= (~ ((r1_tarski @ sk_A @ sk_C)))),
% 0.44/0.63      inference('split', [status(esa)], ['24'])).
% 0.44/0.63  thf('42', plain,
% 0.44/0.63      ((((sk_B) = (k1_xboole_0))) <= (~ ((r1_tarski @ sk_A @ sk_C)))),
% 0.44/0.63      inference('sup-', [status(thm)], ['40', '41'])).
% 0.44/0.63  thf('43', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0))),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('44', plain,
% 0.44/0.63      ((((k2_zfmisc_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 0.44/0.63         <= (~ ((r1_tarski @ sk_A @ sk_C)))),
% 0.44/0.63      inference('sup-', [status(thm)], ['42', '43'])).
% 0.44/0.63  thf('45', plain,
% 0.44/0.63      (![X15 : $i]: ((k2_zfmisc_1 @ X15 @ k1_xboole_0) = (k1_xboole_0))),
% 0.44/0.63      inference('simplify', [status(thm)], ['31'])).
% 0.44/0.63  thf('46', plain,
% 0.44/0.63      ((((k1_xboole_0) != (k1_xboole_0))) <= (~ ((r1_tarski @ sk_A @ sk_C)))),
% 0.44/0.63      inference('demod', [status(thm)], ['44', '45'])).
% 0.44/0.63  thf('47', plain, (((r1_tarski @ sk_A @ sk_C))),
% 0.44/0.63      inference('simplify', [status(thm)], ['46'])).
% 0.44/0.63  thf('48', plain,
% 0.44/0.63      (~ ((r1_tarski @ sk_B @ sk_D)) | ~ ((r1_tarski @ sk_A @ sk_C))),
% 0.44/0.63      inference('split', [status(esa)], ['24'])).
% 0.44/0.63  thf('49', plain, (~ ((r1_tarski @ sk_B @ sk_D))),
% 0.44/0.63      inference('sat_resolution*', [status(thm)], ['47', '48'])).
% 0.44/0.63  thf('50', plain, (~ (r1_tarski @ sk_B @ sk_D)),
% 0.44/0.63      inference('simpl_trail', [status(thm)], ['25', '49'])).
% 0.44/0.63  thf('51', plain, (((sk_A) = (k1_xboole_0))),
% 0.44/0.63      inference('clc', [status(thm)], ['23', '50'])).
% 0.44/0.63  thf('52', plain,
% 0.44/0.63      (![X15 : $i, X16 : $i]:
% 0.44/0.63         (((k2_zfmisc_1 @ X15 @ X16) = (k1_xboole_0))
% 0.44/0.63          | ((X15) != (k1_xboole_0)))),
% 0.44/0.63      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.44/0.63  thf('53', plain,
% 0.44/0.63      (![X16 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X16) = (k1_xboole_0))),
% 0.44/0.63      inference('simplify', [status(thm)], ['52'])).
% 0.44/0.63  thf('54', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.44/0.63      inference('demod', [status(thm)], ['0', '51', '53'])).
% 0.44/0.63  thf('55', plain, ($false), inference('simplify', [status(thm)], ['54'])).
% 0.44/0.63  
% 0.44/0.63  % SZS output end Refutation
% 0.44/0.63  
% 0.44/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
