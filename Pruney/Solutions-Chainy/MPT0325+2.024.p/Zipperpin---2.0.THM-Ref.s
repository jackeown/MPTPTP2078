%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Fuuq3DxCnW

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:43 EST 2020

% Result     : Theorem 0.55s
% Output     : Refutation 0.55s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 118 expanded)
%              Number of leaves         :   21 (  41 expanded)
%              Depth                    :   18
%              Number of atoms          :  551 (1042 expanded)
%              Number of equality atoms :   75 ( 116 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X2: $i,X4: $i] :
      ( ( ( k4_xboole_0 @ X2 @ X4 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('3',plain,
    ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t126_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k4_xboole_0 @ A @ C ) @ B ) @ ( k2_zfmisc_1 @ A @ ( k4_xboole_0 @ B @ D ) ) ) ) )).

thf('5',plain,(
    ! [X51: $i,X52: $i,X53: $i,X54: $i] :
      ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ X51 @ X53 ) @ ( k2_zfmisc_1 @ X52 @ X54 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k4_xboole_0 @ X51 @ X52 ) @ X53 ) @ ( k2_zfmisc_1 @ X51 @ ( k4_xboole_0 @ X53 @ X54 ) ) ) ) ),
    inference(cnf,[status(esa)],[t126_zfmisc_1])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('6',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k3_xboole_0 @ X7 @ ( k2_xboole_0 @ X7 @ X8 ) )
      = X7 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ ( k4_xboole_0 @ X3 @ X1 ) @ X2 ) @ ( k4_xboole_0 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      = ( k2_zfmisc_1 @ ( k4_xboole_0 @ X3 @ X1 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ ( k4_xboole_0 @ sk_A @ sk_C ) @ sk_B ) @ k1_xboole_0 )
    = ( k2_zfmisc_1 @ ( k4_xboole_0 @ sk_A @ sk_C ) @ sk_B ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('9',plain,(
    ! [X11: $i] :
      ( ( k3_xboole_0 @ X11 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('10',plain,
    ( k1_xboole_0
    = ( k2_zfmisc_1 @ ( k4_xboole_0 @ sk_A @ sk_C ) @ sk_B ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X51: $i,X52: $i,X53: $i,X54: $i] :
      ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ X51 @ X53 ) @ ( k2_zfmisc_1 @ X52 @ X54 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k4_xboole_0 @ X51 @ X52 ) @ X53 ) @ ( k2_zfmisc_1 @ X51 @ ( k4_xboole_0 @ X53 @ X54 ) ) ) ) ),
    inference(cnf,[status(esa)],[t126_zfmisc_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ X0 ) )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('13',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('15',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X11: $i] :
      ( ( k3_xboole_0 @ X11 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('19',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['17','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ X0 ) )
      = ( k2_zfmisc_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['12','23'])).

thf('25',plain,
    ( ( k2_zfmisc_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_D ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['3','24'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('26',plain,(
    ! [X48: $i,X49: $i] :
      ( ( X48 = k1_xboole_0 )
      | ( X49 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X49 @ X48 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('27',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_B @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( ( k4_xboole_0 @ sk_B @ sk_D )
      = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( ( k4_xboole_0 @ X2 @ X3 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('30',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( r1_tarski @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( r1_tarski @ sk_B @ sk_D )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_C )
    | ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_D )
   <= ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['32'])).

thf('34',plain,
    ( k1_xboole_0
    = ( k2_zfmisc_1 @ ( k4_xboole_0 @ sk_A @ sk_C ) @ sk_B ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('35',plain,(
    ! [X48: $i,X49: $i] :
      ( ( X48 = k1_xboole_0 )
      | ( X49 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X49 @ X48 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('36',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_A @ sk_C )
      = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_A @ sk_C )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( ( k4_xboole_0 @ X2 @ X3 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

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
    inference(split,[status(esa)],['32'])).

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
    ! [X49: $i,X50: $i] :
      ( ( ( k2_zfmisc_1 @ X49 @ X50 )
        = k1_xboole_0 )
      | ( X50 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('46',plain,(
    ! [X49: $i] :
      ( ( k2_zfmisc_1 @ X49 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['44','46'])).

thf('48',plain,(
    r1_tarski @ sk_A @ sk_C ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_D )
    | ~ ( r1_tarski @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['32'])).

thf('50',plain,(
    ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference('sat_resolution*',[status(thm)],['48','49'])).

thf('51',plain,(
    ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['33','50'])).

thf('52',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['31','51'])).

thf('53',plain,(
    ! [X49: $i,X50: $i] :
      ( ( ( k2_zfmisc_1 @ X49 @ X50 )
        = k1_xboole_0 )
      | ( X49 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('54',plain,(
    ! [X50: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X50 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','52','54'])).

thf('56',plain,(
    $false ),
    inference(simplify,[status(thm)],['55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Fuuq3DxCnW
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:19:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 0.55/0.74  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.55/0.74  % Solved by: fo/fo7.sh
% 0.55/0.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.55/0.74  % done 684 iterations in 0.307s
% 0.55/0.74  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.55/0.74  % SZS output start Refutation
% 0.55/0.74  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.55/0.74  thf(sk_A_type, type, sk_A: $i).
% 0.55/0.74  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.55/0.74  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.55/0.74  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.55/0.74  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.55/0.74  thf(sk_C_type, type, sk_C: $i).
% 0.55/0.74  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.55/0.74  thf(sk_D_type, type, sk_D: $i).
% 0.55/0.74  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.55/0.74  thf(sk_B_type, type, sk_B: $i).
% 0.55/0.74  thf(t138_zfmisc_1, conjecture,
% 0.55/0.74    (![A:$i,B:$i,C:$i,D:$i]:
% 0.55/0.74     ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =>
% 0.55/0.74       ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) | 
% 0.55/0.74         ( ( r1_tarski @ A @ C ) & ( r1_tarski @ B @ D ) ) ) ))).
% 0.55/0.74  thf(zf_stmt_0, negated_conjecture,
% 0.55/0.74    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.55/0.74        ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =>
% 0.55/0.74          ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) | 
% 0.55/0.74            ( ( r1_tarski @ A @ C ) & ( r1_tarski @ B @ D ) ) ) ) )),
% 0.55/0.74    inference('cnf.neg', [status(esa)], [t138_zfmisc_1])).
% 0.55/0.74  thf('0', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('1', plain,
% 0.55/0.74      ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ (k2_zfmisc_1 @ sk_C @ sk_D))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf(l32_xboole_1, axiom,
% 0.55/0.74    (![A:$i,B:$i]:
% 0.55/0.74     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.55/0.74  thf('2', plain,
% 0.55/0.74      (![X2 : $i, X4 : $i]:
% 0.55/0.74         (((k4_xboole_0 @ X2 @ X4) = (k1_xboole_0)) | ~ (r1_tarski @ X2 @ X4))),
% 0.55/0.74      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.55/0.74  thf('3', plain,
% 0.55/0.74      (((k4_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 0.55/0.74         (k2_zfmisc_1 @ sk_C @ sk_D)) = (k1_xboole_0))),
% 0.55/0.74      inference('sup-', [status(thm)], ['1', '2'])).
% 0.55/0.74  thf('4', plain,
% 0.55/0.74      (((k4_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 0.55/0.74         (k2_zfmisc_1 @ sk_C @ sk_D)) = (k1_xboole_0))),
% 0.55/0.74      inference('sup-', [status(thm)], ['1', '2'])).
% 0.55/0.74  thf(t126_zfmisc_1, axiom,
% 0.55/0.74    (![A:$i,B:$i,C:$i,D:$i]:
% 0.55/0.74     ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =
% 0.55/0.74       ( k2_xboole_0 @
% 0.55/0.74         ( k2_zfmisc_1 @ ( k4_xboole_0 @ A @ C ) @ B ) @ 
% 0.55/0.74         ( k2_zfmisc_1 @ A @ ( k4_xboole_0 @ B @ D ) ) ) ))).
% 0.55/0.74  thf('5', plain,
% 0.55/0.74      (![X51 : $i, X52 : $i, X53 : $i, X54 : $i]:
% 0.55/0.74         ((k4_xboole_0 @ (k2_zfmisc_1 @ X51 @ X53) @ (k2_zfmisc_1 @ X52 @ X54))
% 0.55/0.74           = (k2_xboole_0 @ (k2_zfmisc_1 @ (k4_xboole_0 @ X51 @ X52) @ X53) @ 
% 0.55/0.74              (k2_zfmisc_1 @ X51 @ (k4_xboole_0 @ X53 @ X54))))),
% 0.55/0.74      inference('cnf', [status(esa)], [t126_zfmisc_1])).
% 0.55/0.74  thf(t21_xboole_1, axiom,
% 0.55/0.74    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.55/0.74  thf('6', plain,
% 0.55/0.74      (![X7 : $i, X8 : $i]:
% 0.55/0.74         ((k3_xboole_0 @ X7 @ (k2_xboole_0 @ X7 @ X8)) = (X7))),
% 0.55/0.74      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.55/0.74  thf('7', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.55/0.74         ((k3_xboole_0 @ (k2_zfmisc_1 @ (k4_xboole_0 @ X3 @ X1) @ X2) @ 
% 0.55/0.74           (k4_xboole_0 @ (k2_zfmisc_1 @ X3 @ X2) @ (k2_zfmisc_1 @ X1 @ X0)))
% 0.55/0.74           = (k2_zfmisc_1 @ (k4_xboole_0 @ X3 @ X1) @ X2))),
% 0.55/0.74      inference('sup+', [status(thm)], ['5', '6'])).
% 0.55/0.74  thf('8', plain,
% 0.55/0.74      (((k3_xboole_0 @ (k2_zfmisc_1 @ (k4_xboole_0 @ sk_A @ sk_C) @ sk_B) @ 
% 0.55/0.74         k1_xboole_0) = (k2_zfmisc_1 @ (k4_xboole_0 @ sk_A @ sk_C) @ sk_B))),
% 0.55/0.74      inference('sup+', [status(thm)], ['4', '7'])).
% 0.55/0.74  thf(t2_boole, axiom,
% 0.55/0.74    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.55/0.74  thf('9', plain,
% 0.55/0.74      (![X11 : $i]: ((k3_xboole_0 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 0.55/0.74      inference('cnf', [status(esa)], [t2_boole])).
% 0.55/0.74  thf('10', plain,
% 0.55/0.74      (((k1_xboole_0) = (k2_zfmisc_1 @ (k4_xboole_0 @ sk_A @ sk_C) @ sk_B))),
% 0.55/0.74      inference('demod', [status(thm)], ['8', '9'])).
% 0.55/0.74  thf('11', plain,
% 0.55/0.74      (![X51 : $i, X52 : $i, X53 : $i, X54 : $i]:
% 0.55/0.74         ((k4_xboole_0 @ (k2_zfmisc_1 @ X51 @ X53) @ (k2_zfmisc_1 @ X52 @ X54))
% 0.55/0.74           = (k2_xboole_0 @ (k2_zfmisc_1 @ (k4_xboole_0 @ X51 @ X52) @ X53) @ 
% 0.55/0.74              (k2_zfmisc_1 @ X51 @ (k4_xboole_0 @ X53 @ X54))))),
% 0.55/0.74      inference('cnf', [status(esa)], [t126_zfmisc_1])).
% 0.55/0.74  thf('12', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         ((k4_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 0.55/0.74           (k2_zfmisc_1 @ sk_C @ X0))
% 0.55/0.74           = (k2_xboole_0 @ k1_xboole_0 @ 
% 0.55/0.74              (k2_zfmisc_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0))))),
% 0.55/0.74      inference('sup+', [status(thm)], ['10', '11'])).
% 0.55/0.74  thf(t98_xboole_1, axiom,
% 0.55/0.74    (![A:$i,B:$i]:
% 0.55/0.74     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.55/0.74  thf('13', plain,
% 0.55/0.74      (![X17 : $i, X18 : $i]:
% 0.55/0.74         ((k2_xboole_0 @ X17 @ X18)
% 0.55/0.74           = (k5_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X17)))),
% 0.55/0.74      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.55/0.74  thf(commutativity_k5_xboole_0, axiom,
% 0.55/0.74    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.55/0.74  thf('14', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.55/0.74      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.55/0.74  thf(t5_boole, axiom,
% 0.55/0.74    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.55/0.74  thf('15', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.55/0.74      inference('cnf', [status(esa)], [t5_boole])).
% 0.55/0.74  thf('16', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.55/0.74      inference('sup+', [status(thm)], ['14', '15'])).
% 0.55/0.74  thf('17', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.55/0.74      inference('sup+', [status(thm)], ['13', '16'])).
% 0.55/0.74  thf('18', plain,
% 0.55/0.74      (![X11 : $i]: ((k3_xboole_0 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 0.55/0.74      inference('cnf', [status(esa)], [t2_boole])).
% 0.55/0.74  thf(t100_xboole_1, axiom,
% 0.55/0.74    (![A:$i,B:$i]:
% 0.55/0.74     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.55/0.74  thf('19', plain,
% 0.55/0.74      (![X5 : $i, X6 : $i]:
% 0.55/0.74         ((k4_xboole_0 @ X5 @ X6)
% 0.55/0.74           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.55/0.74      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.55/0.74  thf('20', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.55/0.74      inference('sup+', [status(thm)], ['18', '19'])).
% 0.55/0.74  thf('21', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.55/0.74      inference('cnf', [status(esa)], [t5_boole])).
% 0.55/0.74  thf('22', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.55/0.74      inference('sup+', [status(thm)], ['20', '21'])).
% 0.55/0.74  thf('23', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.55/0.74      inference('sup+', [status(thm)], ['17', '22'])).
% 0.55/0.74  thf('24', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         ((k4_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 0.55/0.74           (k2_zfmisc_1 @ sk_C @ X0))
% 0.55/0.74           = (k2_zfmisc_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)))),
% 0.55/0.74      inference('demod', [status(thm)], ['12', '23'])).
% 0.55/0.74  thf('25', plain,
% 0.55/0.74      (((k2_zfmisc_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_D)) = (k1_xboole_0))),
% 0.55/0.74      inference('demod', [status(thm)], ['3', '24'])).
% 0.55/0.74  thf(t113_zfmisc_1, axiom,
% 0.55/0.74    (![A:$i,B:$i]:
% 0.55/0.74     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.55/0.74       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.55/0.74  thf('26', plain,
% 0.55/0.74      (![X48 : $i, X49 : $i]:
% 0.55/0.74         (((X48) = (k1_xboole_0))
% 0.55/0.74          | ((X49) = (k1_xboole_0))
% 0.55/0.74          | ((k2_zfmisc_1 @ X49 @ X48) != (k1_xboole_0)))),
% 0.55/0.74      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.55/0.74  thf('27', plain,
% 0.55/0.74      ((((k1_xboole_0) != (k1_xboole_0))
% 0.55/0.74        | ((sk_A) = (k1_xboole_0))
% 0.55/0.74        | ((k4_xboole_0 @ sk_B @ sk_D) = (k1_xboole_0)))),
% 0.55/0.74      inference('sup-', [status(thm)], ['25', '26'])).
% 0.55/0.74  thf('28', plain,
% 0.55/0.74      ((((k4_xboole_0 @ sk_B @ sk_D) = (k1_xboole_0))
% 0.55/0.74        | ((sk_A) = (k1_xboole_0)))),
% 0.55/0.74      inference('simplify', [status(thm)], ['27'])).
% 0.55/0.74  thf('29', plain,
% 0.55/0.74      (![X2 : $i, X3 : $i]:
% 0.55/0.74         ((r1_tarski @ X2 @ X3) | ((k4_xboole_0 @ X2 @ X3) != (k1_xboole_0)))),
% 0.55/0.74      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.55/0.74  thf('30', plain,
% 0.55/0.74      ((((k1_xboole_0) != (k1_xboole_0))
% 0.55/0.74        | ((sk_A) = (k1_xboole_0))
% 0.55/0.74        | (r1_tarski @ sk_B @ sk_D))),
% 0.55/0.74      inference('sup-', [status(thm)], ['28', '29'])).
% 0.55/0.74  thf('31', plain, (((r1_tarski @ sk_B @ sk_D) | ((sk_A) = (k1_xboole_0)))),
% 0.55/0.74      inference('simplify', [status(thm)], ['30'])).
% 0.55/0.74  thf('32', plain,
% 0.55/0.74      ((~ (r1_tarski @ sk_A @ sk_C) | ~ (r1_tarski @ sk_B @ sk_D))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('33', plain,
% 0.55/0.74      ((~ (r1_tarski @ sk_B @ sk_D)) <= (~ ((r1_tarski @ sk_B @ sk_D)))),
% 0.55/0.74      inference('split', [status(esa)], ['32'])).
% 0.55/0.74  thf('34', plain,
% 0.55/0.74      (((k1_xboole_0) = (k2_zfmisc_1 @ (k4_xboole_0 @ sk_A @ sk_C) @ sk_B))),
% 0.55/0.74      inference('demod', [status(thm)], ['8', '9'])).
% 0.55/0.74  thf('35', plain,
% 0.55/0.74      (![X48 : $i, X49 : $i]:
% 0.55/0.74         (((X48) = (k1_xboole_0))
% 0.55/0.74          | ((X49) = (k1_xboole_0))
% 0.55/0.74          | ((k2_zfmisc_1 @ X49 @ X48) != (k1_xboole_0)))),
% 0.55/0.74      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.55/0.74  thf('36', plain,
% 0.55/0.74      ((((k1_xboole_0) != (k1_xboole_0))
% 0.55/0.74        | ((k4_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0))
% 0.55/0.74        | ((sk_B) = (k1_xboole_0)))),
% 0.55/0.74      inference('sup-', [status(thm)], ['34', '35'])).
% 0.55/0.75  thf('37', plain,
% 0.55/0.75      ((((sk_B) = (k1_xboole_0))
% 0.55/0.75        | ((k4_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0)))),
% 0.55/0.75      inference('simplify', [status(thm)], ['36'])).
% 0.55/0.75  thf('38', plain,
% 0.55/0.75      (![X2 : $i, X3 : $i]:
% 0.55/0.75         ((r1_tarski @ X2 @ X3) | ((k4_xboole_0 @ X2 @ X3) != (k1_xboole_0)))),
% 0.55/0.75      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.55/0.75  thf('39', plain,
% 0.55/0.75      ((((k1_xboole_0) != (k1_xboole_0))
% 0.55/0.75        | ((sk_B) = (k1_xboole_0))
% 0.55/0.75        | (r1_tarski @ sk_A @ sk_C))),
% 0.55/0.75      inference('sup-', [status(thm)], ['37', '38'])).
% 0.55/0.75  thf('40', plain, (((r1_tarski @ sk_A @ sk_C) | ((sk_B) = (k1_xboole_0)))),
% 0.55/0.75      inference('simplify', [status(thm)], ['39'])).
% 0.55/0.75  thf('41', plain,
% 0.55/0.75      ((~ (r1_tarski @ sk_A @ sk_C)) <= (~ ((r1_tarski @ sk_A @ sk_C)))),
% 0.55/0.75      inference('split', [status(esa)], ['32'])).
% 0.55/0.75  thf('42', plain,
% 0.55/0.75      ((((sk_B) = (k1_xboole_0))) <= (~ ((r1_tarski @ sk_A @ sk_C)))),
% 0.55/0.75      inference('sup-', [status(thm)], ['40', '41'])).
% 0.55/0.75  thf('43', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0))),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('44', plain,
% 0.55/0.75      ((((k2_zfmisc_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 0.55/0.75         <= (~ ((r1_tarski @ sk_A @ sk_C)))),
% 0.55/0.75      inference('sup-', [status(thm)], ['42', '43'])).
% 0.55/0.75  thf('45', plain,
% 0.55/0.75      (![X49 : $i, X50 : $i]:
% 0.55/0.75         (((k2_zfmisc_1 @ X49 @ X50) = (k1_xboole_0))
% 0.55/0.75          | ((X50) != (k1_xboole_0)))),
% 0.55/0.75      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.55/0.75  thf('46', plain,
% 0.55/0.75      (![X49 : $i]: ((k2_zfmisc_1 @ X49 @ k1_xboole_0) = (k1_xboole_0))),
% 0.55/0.75      inference('simplify', [status(thm)], ['45'])).
% 0.55/0.75  thf('47', plain,
% 0.55/0.75      ((((k1_xboole_0) != (k1_xboole_0))) <= (~ ((r1_tarski @ sk_A @ sk_C)))),
% 0.55/0.75      inference('demod', [status(thm)], ['44', '46'])).
% 0.55/0.75  thf('48', plain, (((r1_tarski @ sk_A @ sk_C))),
% 0.55/0.75      inference('simplify', [status(thm)], ['47'])).
% 0.55/0.75  thf('49', plain,
% 0.55/0.75      (~ ((r1_tarski @ sk_B @ sk_D)) | ~ ((r1_tarski @ sk_A @ sk_C))),
% 0.55/0.75      inference('split', [status(esa)], ['32'])).
% 0.55/0.75  thf('50', plain, (~ ((r1_tarski @ sk_B @ sk_D))),
% 0.55/0.75      inference('sat_resolution*', [status(thm)], ['48', '49'])).
% 0.55/0.75  thf('51', plain, (~ (r1_tarski @ sk_B @ sk_D)),
% 0.55/0.75      inference('simpl_trail', [status(thm)], ['33', '50'])).
% 0.55/0.75  thf('52', plain, (((sk_A) = (k1_xboole_0))),
% 0.55/0.75      inference('clc', [status(thm)], ['31', '51'])).
% 0.55/0.75  thf('53', plain,
% 0.55/0.75      (![X49 : $i, X50 : $i]:
% 0.55/0.75         (((k2_zfmisc_1 @ X49 @ X50) = (k1_xboole_0))
% 0.55/0.75          | ((X49) != (k1_xboole_0)))),
% 0.55/0.75      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.55/0.75  thf('54', plain,
% 0.55/0.75      (![X50 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X50) = (k1_xboole_0))),
% 0.55/0.75      inference('simplify', [status(thm)], ['53'])).
% 0.55/0.75  thf('55', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.55/0.75      inference('demod', [status(thm)], ['0', '52', '54'])).
% 0.55/0.75  thf('56', plain, ($false), inference('simplify', [status(thm)], ['55'])).
% 0.55/0.75  
% 0.55/0.75  % SZS output end Refutation
% 0.55/0.75  
% 0.55/0.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
