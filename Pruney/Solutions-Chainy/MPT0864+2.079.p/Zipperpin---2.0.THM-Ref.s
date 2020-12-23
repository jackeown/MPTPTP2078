%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SwY6Pax8DI

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:10 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 143 expanded)
%              Number of leaves         :   29 (  54 expanded)
%              Depth                    :   16
%              Number of atoms          :  535 (1062 expanded)
%              Number of equality atoms :   80 ( 167 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t20_mcart_1,conjecture,(
    ! [A: $i] :
      ( ? [B: $i,C: $i] :
          ( A
          = ( k4_tarski @ B @ C ) )
     => ( ( A
         != ( k1_mcart_1 @ A ) )
        & ( A
         != ( k2_mcart_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ? [B: $i,C: $i] :
            ( A
            = ( k4_tarski @ B @ C ) )
       => ( ( A
           != ( k1_mcart_1 @ A ) )
          & ( A
           != ( k2_mcart_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t20_mcart_1])).

thf('0',plain,
    ( sk_A
    = ( k4_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('1',plain,(
    ! [X53: $i,X55: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X53 @ X55 ) )
      = X55 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('2',plain,
    ( ( k2_mcart_1 @ sk_A )
    = sk_C ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( sk_A
      = ( k2_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,
    ( ( sk_A = sk_C )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['2','4'])).

thf('6',plain,
    ( sk_A
    = ( k4_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_B @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t34_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ ( k1_tarski @ D ) ) )
    <=> ( ( A = C )
        & ( B = D ) ) ) )).

thf('8',plain,(
    ! [X46: $i,X47: $i,X48: $i,X50: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X47 @ X48 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X46 ) @ ( k1_tarski @ X50 ) ) )
      | ( X48 != X50 )
      | ( X47 != X46 ) ) ),
    inference(cnf,[status(esa)],[t34_zfmisc_1])).

thf('9',plain,(
    ! [X46: $i,X50: $i] :
      ( r2_hidden @ ( k4_tarski @ X46 @ X50 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X46 ) @ ( k1_tarski @ X50 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,
    ( ( r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['7','9'])).

thf('11',plain,
    ( sk_A
    = ( k4_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X53: $i,X54: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X53 @ X54 ) )
      = X53 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('13',plain,
    ( ( k1_mcart_1 @ sk_A )
    = sk_B ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('15',plain,
    ( ( sk_A = sk_B )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,
    ( sk_A
    = ( k4_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_A @ sk_C ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X46: $i,X50: $i] :
      ( r2_hidden @ ( k4_tarski @ X46 @ X50 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X46 ) @ ( k1_tarski @ X50 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('19',plain,
    ( ( r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_C ) ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('20',plain,(
    ! [X34: $i,X36: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X34 ) @ X36 )
      | ~ ( r2_hidden @ X34 @ X36 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('21',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_C ) ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(t135_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ A @ B ) )
        | ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ A ) ) )
     => ( A = k1_xboole_0 ) ) )).

thf('22',plain,(
    ! [X39: $i,X40: $i] :
      ( ( X39 = k1_xboole_0 )
      | ~ ( r1_tarski @ X39 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[t135_zfmisc_1])).

thf('23',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('24',plain,(
    ! [X43: $i,X44: $i] :
      ( ( X44 != X43 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X44 ) @ ( k1_tarski @ X43 ) )
       != ( k1_tarski @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('25',plain,(
    ! [X43: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X43 ) @ ( k1_tarski @ X43 ) )
     != ( k1_tarski @ X43 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('26',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t19_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) )
      = ( k1_tarski @ A ) ) )).

thf('27',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X41 ) @ ( k2_tarski @ X41 @ X42 ) )
      = ( k1_tarski @ X41 ) ) ),
    inference(cnf,[status(esa)],[t19_zfmisc_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('30',plain,(
    ! [X51: $i,X52: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X51 @ X52 ) )
      = ( k3_xboole_0 @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ ( k1_tarski @ X0 ) ) )
      = ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['32','35'])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('37',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k2_xboole_0 @ X2 @ X3 ) )
      = X2 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('40',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ ( k2_xboole_0 @ X4 @ X5 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['36','41'])).

thf('43',plain,(
    ! [X43: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X43 ) ) ),
    inference(demod,[status(thm)],['25','42'])).

thf('44',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','43'])).

thf('45',plain,(
    sk_A
 != ( k1_mcart_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,
    ( ( sk_A
      = ( k2_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('47',plain,
    ( sk_A
    = ( k2_mcart_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['45','46'])).

thf('48',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['10','47'])).

thf('49',plain,(
    ! [X34: $i,X36: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X34 ) @ X36 )
      | ~ ( r2_hidden @ X34 @ X36 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('50',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X39: $i,X40: $i] :
      ( ( X39 = k1_xboole_0 )
      | ~ ( r1_tarski @ X39 @ ( k2_zfmisc_1 @ X40 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[t135_zfmisc_1])).

thf('52',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X43: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X43 ) ) ),
    inference(demod,[status(thm)],['25','42'])).

thf('54',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    $false ),
    inference(simplify,[status(thm)],['54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SwY6Pax8DI
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:48:25 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.37/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.58  % Solved by: fo/fo7.sh
% 0.37/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.58  % done 349 iterations in 0.131s
% 0.37/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.58  % SZS output start Refutation
% 0.37/0.58  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.37/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.58  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.37/0.58  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.37/0.58  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.37/0.58  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.37/0.58  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.37/0.58  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.37/0.58  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.37/0.58  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.37/0.58  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.37/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.58  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.37/0.58  thf(sk_C_type, type, sk_C: $i).
% 0.37/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.58  thf(t20_mcart_1, conjecture,
% 0.37/0.58    (![A:$i]:
% 0.37/0.58     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.37/0.58       ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ))).
% 0.37/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.58    (~( ![A:$i]:
% 0.37/0.58        ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.37/0.58          ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ) )),
% 0.37/0.58    inference('cnf.neg', [status(esa)], [t20_mcart_1])).
% 0.37/0.58  thf('0', plain, (((sk_A) = (k4_tarski @ sk_B @ sk_C))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf(t7_mcart_1, axiom,
% 0.37/0.58    (![A:$i,B:$i]:
% 0.37/0.58     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.37/0.58       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.37/0.58  thf('1', plain,
% 0.37/0.58      (![X53 : $i, X55 : $i]: ((k2_mcart_1 @ (k4_tarski @ X53 @ X55)) = (X55))),
% 0.37/0.58      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.37/0.58  thf('2', plain, (((k2_mcart_1 @ sk_A) = (sk_C))),
% 0.37/0.58      inference('sup+', [status(thm)], ['0', '1'])).
% 0.37/0.58  thf('3', plain,
% 0.37/0.58      ((((sk_A) = (k1_mcart_1 @ sk_A)) | ((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('4', plain,
% 0.37/0.58      ((((sk_A) = (k2_mcart_1 @ sk_A))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.37/0.58      inference('split', [status(esa)], ['3'])).
% 0.37/0.58  thf('5', plain, ((((sk_A) = (sk_C))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.37/0.58      inference('sup+', [status(thm)], ['2', '4'])).
% 0.37/0.58  thf('6', plain, (((sk_A) = (k4_tarski @ sk_B @ sk_C))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('7', plain,
% 0.37/0.58      ((((sk_A) = (k4_tarski @ sk_B @ sk_A)))
% 0.37/0.58         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.37/0.58      inference('sup+', [status(thm)], ['5', '6'])).
% 0.37/0.58  thf(t34_zfmisc_1, axiom,
% 0.37/0.58    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.58     ( ( r2_hidden @
% 0.37/0.58         ( k4_tarski @ A @ B ) @ 
% 0.37/0.58         ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ ( k1_tarski @ D ) ) ) <=>
% 0.37/0.58       ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ))).
% 0.37/0.58  thf('8', plain,
% 0.37/0.58      (![X46 : $i, X47 : $i, X48 : $i, X50 : $i]:
% 0.37/0.58         ((r2_hidden @ (k4_tarski @ X47 @ X48) @ 
% 0.37/0.58           (k2_zfmisc_1 @ (k1_tarski @ X46) @ (k1_tarski @ X50)))
% 0.37/0.58          | ((X48) != (X50))
% 0.37/0.58          | ((X47) != (X46)))),
% 0.37/0.58      inference('cnf', [status(esa)], [t34_zfmisc_1])).
% 0.37/0.58  thf('9', plain,
% 0.37/0.58      (![X46 : $i, X50 : $i]:
% 0.37/0.58         (r2_hidden @ (k4_tarski @ X46 @ X50) @ 
% 0.37/0.58          (k2_zfmisc_1 @ (k1_tarski @ X46) @ (k1_tarski @ X50)))),
% 0.37/0.58      inference('simplify', [status(thm)], ['8'])).
% 0.37/0.58  thf('10', plain,
% 0.37/0.58      (((r2_hidden @ sk_A @ 
% 0.37/0.58         (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))))
% 0.37/0.58         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.37/0.58      inference('sup+', [status(thm)], ['7', '9'])).
% 0.37/0.58  thf('11', plain, (((sk_A) = (k4_tarski @ sk_B @ sk_C))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('12', plain,
% 0.37/0.58      (![X53 : $i, X54 : $i]: ((k1_mcart_1 @ (k4_tarski @ X53 @ X54)) = (X53))),
% 0.37/0.58      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.37/0.58  thf('13', plain, (((k1_mcart_1 @ sk_A) = (sk_B))),
% 0.37/0.58      inference('sup+', [status(thm)], ['11', '12'])).
% 0.37/0.58  thf('14', plain,
% 0.37/0.58      ((((sk_A) = (k1_mcart_1 @ sk_A))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.37/0.58      inference('split', [status(esa)], ['3'])).
% 0.37/0.58  thf('15', plain, ((((sk_A) = (sk_B))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.37/0.58      inference('sup+', [status(thm)], ['13', '14'])).
% 0.37/0.58  thf('16', plain, (((sk_A) = (k4_tarski @ sk_B @ sk_C))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('17', plain,
% 0.37/0.58      ((((sk_A) = (k4_tarski @ sk_A @ sk_C)))
% 0.37/0.58         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.37/0.58      inference('sup+', [status(thm)], ['15', '16'])).
% 0.37/0.58  thf('18', plain,
% 0.37/0.58      (![X46 : $i, X50 : $i]:
% 0.37/0.58         (r2_hidden @ (k4_tarski @ X46 @ X50) @ 
% 0.37/0.58          (k2_zfmisc_1 @ (k1_tarski @ X46) @ (k1_tarski @ X50)))),
% 0.37/0.58      inference('simplify', [status(thm)], ['8'])).
% 0.37/0.58  thf('19', plain,
% 0.37/0.58      (((r2_hidden @ sk_A @ 
% 0.37/0.58         (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_C))))
% 0.37/0.58         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.37/0.58      inference('sup+', [status(thm)], ['17', '18'])).
% 0.37/0.58  thf(l1_zfmisc_1, axiom,
% 0.37/0.58    (![A:$i,B:$i]:
% 0.37/0.58     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.37/0.58  thf('20', plain,
% 0.37/0.58      (![X34 : $i, X36 : $i]:
% 0.37/0.58         ((r1_tarski @ (k1_tarski @ X34) @ X36) | ~ (r2_hidden @ X34 @ X36))),
% 0.37/0.58      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.37/0.58  thf('21', plain,
% 0.37/0.58      (((r1_tarski @ (k1_tarski @ sk_A) @ 
% 0.37/0.58         (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_C))))
% 0.37/0.58         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.37/0.58      inference('sup-', [status(thm)], ['19', '20'])).
% 0.37/0.58  thf(t135_zfmisc_1, axiom,
% 0.37/0.58    (![A:$i,B:$i]:
% 0.37/0.58     ( ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ A @ B ) ) | 
% 0.37/0.58         ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.37/0.58       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.37/0.58  thf('22', plain,
% 0.37/0.58      (![X39 : $i, X40 : $i]:
% 0.37/0.58         (((X39) = (k1_xboole_0))
% 0.37/0.58          | ~ (r1_tarski @ X39 @ (k2_zfmisc_1 @ X39 @ X40)))),
% 0.37/0.58      inference('cnf', [status(esa)], [t135_zfmisc_1])).
% 0.37/0.58  thf('23', plain,
% 0.37/0.58      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 0.37/0.58         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.37/0.58      inference('sup-', [status(thm)], ['21', '22'])).
% 0.37/0.58  thf(t20_zfmisc_1, axiom,
% 0.37/0.58    (![A:$i,B:$i]:
% 0.37/0.58     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.37/0.58         ( k1_tarski @ A ) ) <=>
% 0.37/0.58       ( ( A ) != ( B ) ) ))).
% 0.37/0.58  thf('24', plain,
% 0.37/0.58      (![X43 : $i, X44 : $i]:
% 0.37/0.58         (((X44) != (X43))
% 0.37/0.58          | ((k4_xboole_0 @ (k1_tarski @ X44) @ (k1_tarski @ X43))
% 0.37/0.58              != (k1_tarski @ X44)))),
% 0.37/0.58      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.37/0.58  thf('25', plain,
% 0.37/0.58      (![X43 : $i]:
% 0.37/0.58         ((k4_xboole_0 @ (k1_tarski @ X43) @ (k1_tarski @ X43))
% 0.37/0.58           != (k1_tarski @ X43))),
% 0.37/0.58      inference('simplify', [status(thm)], ['24'])).
% 0.37/0.58  thf(t69_enumset1, axiom,
% 0.37/0.58    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.37/0.58  thf('26', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.37/0.58      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.37/0.58  thf(t19_zfmisc_1, axiom,
% 0.37/0.58    (![A:$i,B:$i]:
% 0.37/0.58     ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 0.37/0.58       ( k1_tarski @ A ) ))).
% 0.37/0.58  thf('27', plain,
% 0.37/0.58      (![X41 : $i, X42 : $i]:
% 0.37/0.58         ((k3_xboole_0 @ (k1_tarski @ X41) @ (k2_tarski @ X41 @ X42))
% 0.37/0.58           = (k1_tarski @ X41))),
% 0.37/0.58      inference('cnf', [status(esa)], [t19_zfmisc_1])).
% 0.37/0.58  thf('28', plain,
% 0.37/0.58      (![X0 : $i]:
% 0.37/0.58         ((k3_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))
% 0.37/0.58           = (k1_tarski @ X0))),
% 0.37/0.58      inference('sup+', [status(thm)], ['26', '27'])).
% 0.37/0.58  thf('29', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.37/0.58      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.37/0.58  thf(t12_setfam_1, axiom,
% 0.37/0.58    (![A:$i,B:$i]:
% 0.37/0.58     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.37/0.58  thf('30', plain,
% 0.37/0.58      (![X51 : $i, X52 : $i]:
% 0.37/0.58         ((k1_setfam_1 @ (k2_tarski @ X51 @ X52)) = (k3_xboole_0 @ X51 @ X52))),
% 0.37/0.58      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.37/0.58  thf('31', plain,
% 0.37/0.58      (![X0 : $i]: ((k1_setfam_1 @ (k1_tarski @ X0)) = (k3_xboole_0 @ X0 @ X0))),
% 0.37/0.58      inference('sup+', [status(thm)], ['29', '30'])).
% 0.37/0.58  thf('32', plain,
% 0.37/0.58      (![X0 : $i]:
% 0.37/0.58         ((k1_setfam_1 @ (k1_tarski @ (k1_tarski @ X0))) = (k1_tarski @ X0))),
% 0.37/0.58      inference('demod', [status(thm)], ['28', '31'])).
% 0.37/0.58  thf('33', plain,
% 0.37/0.58      (![X0 : $i]: ((k1_setfam_1 @ (k1_tarski @ X0)) = (k3_xboole_0 @ X0 @ X0))),
% 0.37/0.58      inference('sup+', [status(thm)], ['29', '30'])).
% 0.37/0.58  thf(t100_xboole_1, axiom,
% 0.37/0.58    (![A:$i,B:$i]:
% 0.37/0.58     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.37/0.58  thf('34', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]:
% 0.37/0.58         ((k4_xboole_0 @ X0 @ X1)
% 0.37/0.58           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.37/0.58      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.58  thf('35', plain,
% 0.37/0.58      (![X0 : $i]:
% 0.37/0.58         ((k4_xboole_0 @ X0 @ X0)
% 0.37/0.58           = (k5_xboole_0 @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0))))),
% 0.37/0.58      inference('sup+', [status(thm)], ['33', '34'])).
% 0.37/0.58  thf('36', plain,
% 0.37/0.58      (![X0 : $i]:
% 0.37/0.58         ((k4_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))
% 0.37/0.58           = (k5_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)))),
% 0.37/0.58      inference('sup+', [status(thm)], ['32', '35'])).
% 0.37/0.58  thf(t21_xboole_1, axiom,
% 0.37/0.58    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.37/0.58  thf('37', plain,
% 0.37/0.58      (![X2 : $i, X3 : $i]:
% 0.37/0.58         ((k3_xboole_0 @ X2 @ (k2_xboole_0 @ X2 @ X3)) = (X2))),
% 0.37/0.58      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.37/0.58  thf('38', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]:
% 0.37/0.58         ((k4_xboole_0 @ X0 @ X1)
% 0.37/0.58           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.37/0.58      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.58  thf('39', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]:
% 0.37/0.58         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 0.37/0.58           = (k5_xboole_0 @ X0 @ X0))),
% 0.37/0.58      inference('sup+', [status(thm)], ['37', '38'])).
% 0.37/0.58  thf(t46_xboole_1, axiom,
% 0.37/0.58    (![A:$i,B:$i]:
% 0.37/0.58     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.37/0.58  thf('40', plain,
% 0.37/0.58      (![X4 : $i, X5 : $i]:
% 0.37/0.58         ((k4_xboole_0 @ X4 @ (k2_xboole_0 @ X4 @ X5)) = (k1_xboole_0))),
% 0.37/0.58      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.37/0.58  thf('41', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.37/0.58      inference('sup+', [status(thm)], ['39', '40'])).
% 0.37/0.58  thf('42', plain,
% 0.37/0.58      (![X0 : $i]:
% 0.37/0.58         ((k4_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)) = (k1_xboole_0))),
% 0.37/0.58      inference('demod', [status(thm)], ['36', '41'])).
% 0.37/0.58  thf('43', plain, (![X43 : $i]: ((k1_xboole_0) != (k1_tarski @ X43))),
% 0.37/0.58      inference('demod', [status(thm)], ['25', '42'])).
% 0.37/0.58  thf('44', plain,
% 0.37/0.58      ((((k1_xboole_0) != (k1_xboole_0))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.37/0.58      inference('sup-', [status(thm)], ['23', '43'])).
% 0.37/0.58  thf('45', plain, (~ (((sk_A) = (k1_mcart_1 @ sk_A)))),
% 0.37/0.58      inference('simplify', [status(thm)], ['44'])).
% 0.37/0.58  thf('46', plain,
% 0.37/0.58      ((((sk_A) = (k2_mcart_1 @ sk_A))) | (((sk_A) = (k1_mcart_1 @ sk_A)))),
% 0.37/0.58      inference('split', [status(esa)], ['3'])).
% 0.37/0.58  thf('47', plain, ((((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.37/0.58      inference('sat_resolution*', [status(thm)], ['45', '46'])).
% 0.37/0.58  thf('48', plain,
% 0.37/0.58      ((r2_hidden @ sk_A @ 
% 0.37/0.58        (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)))),
% 0.37/0.58      inference('simpl_trail', [status(thm)], ['10', '47'])).
% 0.37/0.58  thf('49', plain,
% 0.37/0.58      (![X34 : $i, X36 : $i]:
% 0.37/0.58         ((r1_tarski @ (k1_tarski @ X34) @ X36) | ~ (r2_hidden @ X34 @ X36))),
% 0.37/0.58      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.37/0.58  thf('50', plain,
% 0.37/0.58      ((r1_tarski @ (k1_tarski @ sk_A) @ 
% 0.37/0.58        (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['48', '49'])).
% 0.37/0.58  thf('51', plain,
% 0.37/0.58      (![X39 : $i, X40 : $i]:
% 0.37/0.58         (((X39) = (k1_xboole_0))
% 0.37/0.58          | ~ (r1_tarski @ X39 @ (k2_zfmisc_1 @ X40 @ X39)))),
% 0.37/0.58      inference('cnf', [status(esa)], [t135_zfmisc_1])).
% 0.37/0.58  thf('52', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.37/0.58      inference('sup-', [status(thm)], ['50', '51'])).
% 0.37/0.58  thf('53', plain, (![X43 : $i]: ((k1_xboole_0) != (k1_tarski @ X43))),
% 0.37/0.58      inference('demod', [status(thm)], ['25', '42'])).
% 0.37/0.58  thf('54', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.37/0.58      inference('sup-', [status(thm)], ['52', '53'])).
% 0.37/0.58  thf('55', plain, ($false), inference('simplify', [status(thm)], ['54'])).
% 0.37/0.58  
% 0.37/0.58  % SZS output end Refutation
% 0.37/0.58  
% 0.37/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
