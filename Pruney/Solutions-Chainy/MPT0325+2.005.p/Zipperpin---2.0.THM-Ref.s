%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wJxjmIF3r8

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:40 EST 2020

% Result     : Theorem 4.13s
% Output     : Refutation 4.19s
% Verified   : 
% Statistics : Number of formulae       :  174 ( 294 expanded)
%              Number of leaves         :   29 ( 100 expanded)
%              Depth                    :   37
%              Number of atoms          : 1625 (3092 expanded)
%              Number of equality atoms :  170 ( 307 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

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

thf(t120_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ C @ ( k2_xboole_0 @ A @ B ) )
        = ( k2_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) )
      & ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) @ C )
        = ( k2_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )).

thf('1',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ X49 @ X51 ) @ X50 )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X49 @ X50 ) @ ( k2_zfmisc_1 @ X51 @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf('2',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('3',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('4',plain,
    ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t123_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('5',plain,(
    ! [X53: $i,X54: $i,X55: $i,X56: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X53 @ X55 ) @ ( k3_xboole_0 @ X54 @ X56 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X53 @ X54 ) @ ( k2_zfmisc_1 @ X55 @ X56 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('6',plain,
    ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ sk_C ) @ ( k3_xboole_0 @ sk_B @ sk_D ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X49: $i,X51: $i,X52: $i] :
      ( ( k2_zfmisc_1 @ X52 @ ( k2_xboole_0 @ X49 @ X51 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X52 @ X49 ) @ ( k2_zfmisc_1 @ X52 @ X51 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ sk_C ) @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_D ) @ X0 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ sk_C ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ sk_C ) @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_D ) @ sk_B ) )
    = ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_A @ sk_C ) ) @ sk_B ) ),
    inference('sup+',[status(thm)],['1','8'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('10',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_tarski @ X16 @ X15 )
      = ( k2_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('11',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X44 @ X45 ) )
      = ( k2_xboole_0 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X44 @ X45 ) )
      = ( k2_xboole_0 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('15',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('16',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('17',plain,
    ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ sk_C ) @ sk_B )
    = ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['9','14','15','16'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('19',plain,(
    ! [X53: $i,X54: $i,X55: $i,X56: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X53 @ X55 ) @ ( k3_xboole_0 @ X54 @ X56 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X53 @ X54 ) @ ( k2_zfmisc_1 @ X55 @ X56 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('20',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ X3 @ X1 ) @ ( k2_zfmisc_1 @ X2 @ X0 ) )
      = ( k5_xboole_0 @ ( k2_zfmisc_1 @ X3 @ X1 ) @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X3 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X0 ) @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','21'])).

thf(t125_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ C @ ( k4_xboole_0 @ A @ B ) )
        = ( k4_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) )
      & ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ A @ B ) @ C )
        = ( k4_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )).

thf('23',plain,(
    ! [X57: $i,X58: $i,X59: $i] :
      ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ X57 @ X59 ) @ X58 )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ X57 @ X58 ) @ ( k2_zfmisc_1 @ X59 @ X58 ) ) ) ),
    inference(cnf,[status(esa)],[t125_zfmisc_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k5_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X0 ) @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ sk_A @ sk_C ) @ sk_B )
    = ( k5_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['17','24'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('26',plain,(
    ! [X14: $i] :
      ( ( k5_xboole_0 @ X14 @ X14 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('27',plain,
    ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ sk_A @ sk_C ) @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['25','26'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('28',plain,(
    ! [X46: $i,X47: $i] :
      ( ( X46 = k1_xboole_0 )
      | ( X47 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X47 @ X46 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('29',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_A @ sk_C )
      = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_A @ sk_C )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['29'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('31',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( ( k4_xboole_0 @ X1 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('32',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( r1_tarski @ sk_A @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_C )
    | ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_C )
   <= ~ ( r1_tarski @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['34'])).

thf('36',plain,(
    ! [X49: $i,X51: $i,X52: $i] :
      ( ( k2_zfmisc_1 @ X52 @ ( k2_xboole_0 @ X49 @ X51 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X52 @ X49 ) @ ( k2_zfmisc_1 @ X52 @ X51 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf('37',plain,
    ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ sk_C ) @ ( k3_xboole_0 @ sk_B @ sk_D ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('38',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ X49 @ X51 ) @ X50 )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X49 @ X50 ) @ ( k2_zfmisc_1 @ X51 @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_C ) @ X0 ) @ ( k3_xboole_0 @ sk_B @ sk_D ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ X0 @ ( k3_xboole_0 @ sk_B @ sk_D ) ) ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_C ) @ sk_A ) @ ( k3_xboole_0 @ sk_B @ sk_D ) )
    = ( k2_zfmisc_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_B @ sk_D ) ) ) ),
    inference('sup+',[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('42',plain,
    ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_C ) @ sk_A ) @ ( k3_xboole_0 @ sk_B @ sk_D ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('44',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('45',plain,
    ( ( k2_zfmisc_1 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_D ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,(
    ! [X57: $i,X59: $i,X60: $i] :
      ( ( k2_zfmisc_1 @ X60 @ ( k4_xboole_0 @ X57 @ X59 ) )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ X60 @ X57 ) @ ( k2_zfmisc_1 @ X60 @ X59 ) ) ) ),
    inference(cnf,[status(esa)],[t125_zfmisc_1])).

thf('47',plain,
    ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ sk_C ) @ ( k3_xboole_0 @ sk_B @ sk_D ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('48',plain,(
    ! [X57: $i,X58: $i,X59: $i] :
      ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ X57 @ X59 ) @ X58 )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ X57 @ X58 ) @ ( k2_zfmisc_1 @ X59 @ X58 ) ) ) ),
    inference(cnf,[status(esa)],[t125_zfmisc_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_C ) @ X0 ) @ ( k3_xboole_0 @ sk_B @ sk_D ) )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ X0 @ ( k3_xboole_0 @ sk_B @ sk_D ) ) ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_C ) @ sk_A ) @ ( k3_xboole_0 @ sk_B @ sk_D ) )
    = ( k2_zfmisc_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_B @ sk_D ) ) ) ),
    inference('sup+',[status(thm)],['46','49'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('51',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('52',plain,(
    ! [X1: $i,X3: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X47: $i,X48: $i] :
      ( ( ( k2_zfmisc_1 @ X47 @ X48 )
        = k1_xboole_0 )
      | ( X47 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('55',plain,(
    ! [X48: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X48 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,
    ( k1_xboole_0
    = ( k2_zfmisc_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_B @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['50','53','55'])).

thf('57',plain,(
    ! [X57: $i,X58: $i,X59: $i] :
      ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ X57 @ X59 ) @ X58 )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ X57 @ X58 ) @ ( k2_zfmisc_1 @ X59 @ X58 ) ) ) ),
    inference(cnf,[status(esa)],[t125_zfmisc_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ sk_A @ X0 ) @ ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_B @ sk_D ) ) )
      = ( k4_xboole_0 @ k1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_B @ sk_D ) ) ) ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('60',plain,(
    ! [X12: $i] :
      ( ( X12 = k1_xboole_0 )
      | ~ ( r1_tarski @ X12 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('64',plain,(
    ! [X13: $i] :
      ( ( k5_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ sk_A @ X0 ) @ ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_B @ sk_D ) ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['58','65'])).

thf('67',plain,(
    ! [X46: $i,X47: $i] :
      ( ( X46 = k1_xboole_0 )
      | ( X47 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X47 @ X46 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k4_xboole_0 @ sk_A @ X0 )
        = k1_xboole_0 )
      | ( ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_B @ sk_D ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_B @ sk_D ) )
        = k1_xboole_0 )
      | ( ( k4_xboole_0 @ sk_A @ X0 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( ( k4_xboole_0 @ X1 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k4_xboole_0 @ sk_A @ X0 )
        = k1_xboole_0 )
      | ( r1_tarski @ sk_B @ ( k3_xboole_0 @ sk_B @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ ( k3_xboole_0 @ sk_B @ sk_D ) )
      | ( ( k4_xboole_0 @ sk_A @ X0 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ! [X14: $i] :
      ( ( k5_xboole_0 @ X14 @ X14 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('74',plain,(
    ! [X48: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X48 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['54'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X57: $i,X58: $i,X59: $i] :
      ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ X57 @ X59 ) @ X58 )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ X57 @ X58 ) @ ( k2_zfmisc_1 @ X59 @ X58 ) ) ) ),
    inference(cnf,[status(esa)],[t125_zfmisc_1])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X1 ) ) @ X0 )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( ( k4_xboole_0 @ X1 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X1 ) ) @ X0 )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k2_zfmisc_1 @ X2 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
       != k1_xboole_0 )
      | ( r1_tarski @ sk_B @ ( k3_xboole_0 @ sk_B @ sk_D ) )
      | ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['72','79'])).

thf('81',plain,(
    ! [X48: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X48 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['54'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ sk_B @ ( k3_xboole_0 @ sk_B @ sk_D ) )
      | ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ X0 ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ X0 ) @ k1_xboole_0 )
      | ( r1_tarski @ sk_B @ ( k3_xboole_0 @ sk_B @ sk_D ) ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,(
    ! [X12: $i] :
      ( ( X12 = k1_xboole_0 )
      | ~ ( r1_tarski @ X12 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ ( k3_xboole_0 @ sk_B @ sk_D ) )
      | ( ( k2_zfmisc_1 @ sk_A @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( r1_tarski @ sk_B @ ( k3_xboole_0 @ sk_B @ sk_D ) ) ),
    inference('sup+',[status(thm)],['45','85'])).

thf('87',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    r1_tarski @ sk_B @ ( k3_xboole_0 @ sk_B @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('90',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_B @ sk_D ) )
    = sk_B ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ sk_C ) @ ( k3_xboole_0 @ sk_B @ sk_D ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('92',plain,(
    ! [X53: $i,X54: $i,X55: $i,X56: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X53 @ X55 ) @ ( k3_xboole_0 @ X54 @ X56 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X53 @ X54 ) @ ( k2_zfmisc_1 @ X55 @ X56 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ sk_A @ sk_C ) ) @ ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ sk_B @ sk_D ) ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X53: $i,X54: $i,X55: $i,X56: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X53 @ X55 ) @ ( k3_xboole_0 @ X54 @ X56 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X53 @ X54 ) @ ( k2_zfmisc_1 @ X55 @ X56 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ sk_A @ sk_C ) ) @ ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ sk_B @ sk_D ) ) )
      = ( k2_zfmisc_1 @ ( k3_xboole_0 @ X1 @ sk_A ) @ ( k3_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ sk_A @ sk_C ) ) @ sk_B )
      = ( k2_zfmisc_1 @ ( k3_xboole_0 @ X0 @ sk_A ) @ ( k3_xboole_0 @ sk_B @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['90','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ sk_A @ sk_C ) ) @ sk_B )
      = ( k2_zfmisc_1 @ ( k3_xboole_0 @ X0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('100',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,
    ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_C ) @ sk_A ) @ ( k3_xboole_0 @ sk_B @ sk_D ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('103',plain,(
    ! [X53: $i,X54: $i,X55: $i,X56: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X53 @ X55 ) @ ( k3_xboole_0 @ X54 @ X56 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X53 @ X54 ) @ ( k2_zfmisc_1 @ X55 @ X56 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_C ) @ sk_A ) @ X1 ) @ ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_D ) @ X0 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X53: $i,X54: $i,X55: $i,X56: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X53 @ X55 ) @ ( k3_xboole_0 @ X54 @ X56 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X53 @ X54 ) @ ( k2_zfmisc_1 @ X55 @ X56 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_C ) @ sk_A ) @ X1 ) @ ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_D ) @ X0 ) )
      = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ X1 ) @ ( k3_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('108',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ X1 ) @ ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_D ) @ X0 ) )
      = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ X1 ) @ ( k3_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['106','107','108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ X0 ) @ ( k3_xboole_0 @ sk_B @ sk_D ) )
      = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ X0 ) @ ( k3_xboole_0 @ sk_B @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['101','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ X0 ) @ ( k3_xboole_0 @ sk_B @ sk_D ) )
      = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('114',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ X3 @ X1 ) @ ( k2_zfmisc_1 @ X2 @ X0 ) )
      = ( k5_xboole_0 @ ( k2_zfmisc_1 @ X3 @ X1 ) @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X3 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('115',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ X3 ) @ ( k2_zfmisc_1 @ X1 @ X2 ) )
      = ( k5_xboole_0 @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ X3 ) @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X3 @ X2 ) ) ) ) ),
    inference('sup+',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_B ) @ ( k2_zfmisc_1 @ sk_A @ sk_D ) )
      = ( k5_xboole_0 @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_B ) @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['112','115'])).

thf('117',plain,(
    ! [X14: $i] :
      ( ( k5_xboole_0 @ X14 @ X14 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_B ) @ ( k2_zfmisc_1 @ sk_A @ sk_D ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,
    ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ sk_A ) @ sk_B ) @ ( k2_zfmisc_1 @ sk_A @ sk_D ) )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['98','118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('121',plain,(
    ! [X57: $i,X59: $i,X60: $i] :
      ( ( k2_zfmisc_1 @ X60 @ ( k4_xboole_0 @ X57 @ X59 ) )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ X60 @ X57 ) @ ( k2_zfmisc_1 @ X60 @ X59 ) ) ) ),
    inference(cnf,[status(esa)],[t125_zfmisc_1])).

thf('122',plain,
    ( ( k2_zfmisc_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_D ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['119','120','121'])).

thf('123',plain,(
    ! [X46: $i,X47: $i] :
      ( ( X46 = k1_xboole_0 )
      | ( X47 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X47 @ X46 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('124',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_B @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,
    ( ( ( k4_xboole_0 @ sk_B @ sk_D )
      = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['124'])).

thf('126',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( ( k4_xboole_0 @ X1 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('127',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( r1_tarski @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,
    ( ( r1_tarski @ sk_B @ sk_D )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['127'])).

thf('129',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_D )
   <= ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['34'])).

thf('130',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,
    ( ( ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B )
     != k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X48: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X48 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['54'])).

thf('134',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,(
    r1_tarski @ sk_B @ sk_D ),
    inference(simplify,[status(thm)],['134'])).

thf('136',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_C )
    | ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['34'])).

thf('137',plain,(
    ~ ( r1_tarski @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['135','136'])).

thf('138',plain,(
    ~ ( r1_tarski @ sk_A @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['35','137'])).

thf('139',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['33','138'])).

thf('140',plain,(
    ! [X47: $i,X48: $i] :
      ( ( ( k2_zfmisc_1 @ X47 @ X48 )
        = k1_xboole_0 )
      | ( X48 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('141',plain,(
    ! [X47: $i] :
      ( ( k2_zfmisc_1 @ X47 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['140'])).

thf('142',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','139','141'])).

thf('143',plain,(
    $false ),
    inference(simplify,[status(thm)],['142'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wJxjmIF3r8
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:31:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 4.13/4.38  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 4.13/4.38  % Solved by: fo/fo7.sh
% 4.13/4.38  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.13/4.38  % done 5133 iterations in 3.921s
% 4.13/4.38  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 4.13/4.38  % SZS output start Refutation
% 4.13/4.38  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 4.13/4.38  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 4.13/4.38  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 4.13/4.38  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.13/4.38  thf(sk_D_type, type, sk_D: $i).
% 4.13/4.38  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 4.13/4.38  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 4.13/4.38  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 4.13/4.38  thf(sk_C_type, type, sk_C: $i).
% 4.13/4.38  thf(sk_B_type, type, sk_B: $i).
% 4.13/4.38  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 4.13/4.38  thf(sk_A_type, type, sk_A: $i).
% 4.13/4.38  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 4.13/4.38  thf(t138_zfmisc_1, conjecture,
% 4.13/4.38    (![A:$i,B:$i,C:$i,D:$i]:
% 4.13/4.38     ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =>
% 4.13/4.38       ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) | 
% 4.13/4.38         ( ( r1_tarski @ A @ C ) & ( r1_tarski @ B @ D ) ) ) ))).
% 4.13/4.38  thf(zf_stmt_0, negated_conjecture,
% 4.13/4.38    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 4.13/4.38        ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =>
% 4.13/4.38          ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) | 
% 4.13/4.38            ( ( r1_tarski @ A @ C ) & ( r1_tarski @ B @ D ) ) ) ) )),
% 4.13/4.38    inference('cnf.neg', [status(esa)], [t138_zfmisc_1])).
% 4.13/4.38  thf('0', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0))),
% 4.13/4.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.13/4.38  thf(t120_zfmisc_1, axiom,
% 4.13/4.38    (![A:$i,B:$i,C:$i]:
% 4.13/4.38     ( ( ( k2_zfmisc_1 @ C @ ( k2_xboole_0 @ A @ B ) ) =
% 4.13/4.38         ( k2_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 4.13/4.38       ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 4.13/4.38         ( k2_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 4.13/4.38  thf('1', plain,
% 4.13/4.38      (![X49 : $i, X50 : $i, X51 : $i]:
% 4.13/4.38         ((k2_zfmisc_1 @ (k2_xboole_0 @ X49 @ X51) @ X50)
% 4.13/4.38           = (k2_xboole_0 @ (k2_zfmisc_1 @ X49 @ X50) @ 
% 4.13/4.38              (k2_zfmisc_1 @ X51 @ X50)))),
% 4.13/4.38      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 4.13/4.38  thf('2', plain,
% 4.13/4.38      ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ (k2_zfmisc_1 @ sk_C @ sk_D))),
% 4.13/4.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.13/4.38  thf(t28_xboole_1, axiom,
% 4.13/4.38    (![A:$i,B:$i]:
% 4.13/4.38     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 4.13/4.38  thf('3', plain,
% 4.13/4.38      (![X10 : $i, X11 : $i]:
% 4.13/4.38         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 4.13/4.38      inference('cnf', [status(esa)], [t28_xboole_1])).
% 4.13/4.38  thf('4', plain,
% 4.13/4.38      (((k3_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 4.13/4.38         (k2_zfmisc_1 @ sk_C @ sk_D)) = (k2_zfmisc_1 @ sk_A @ sk_B))),
% 4.13/4.38      inference('sup-', [status(thm)], ['2', '3'])).
% 4.13/4.38  thf(t123_zfmisc_1, axiom,
% 4.13/4.38    (![A:$i,B:$i,C:$i,D:$i]:
% 4.13/4.38     ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) ) =
% 4.13/4.38       ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 4.13/4.38  thf('5', plain,
% 4.13/4.38      (![X53 : $i, X54 : $i, X55 : $i, X56 : $i]:
% 4.19/4.38         ((k2_zfmisc_1 @ (k3_xboole_0 @ X53 @ X55) @ (k3_xboole_0 @ X54 @ X56))
% 4.19/4.38           = (k3_xboole_0 @ (k2_zfmisc_1 @ X53 @ X54) @ 
% 4.19/4.38              (k2_zfmisc_1 @ X55 @ X56)))),
% 4.19/4.38      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 4.19/4.38  thf('6', plain,
% 4.19/4.38      (((k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ sk_C) @ 
% 4.19/4.38         (k3_xboole_0 @ sk_B @ sk_D)) = (k2_zfmisc_1 @ sk_A @ sk_B))),
% 4.19/4.38      inference('demod', [status(thm)], ['4', '5'])).
% 4.19/4.38  thf('7', plain,
% 4.19/4.38      (![X49 : $i, X51 : $i, X52 : $i]:
% 4.19/4.38         ((k2_zfmisc_1 @ X52 @ (k2_xboole_0 @ X49 @ X51))
% 4.19/4.38           = (k2_xboole_0 @ (k2_zfmisc_1 @ X52 @ X49) @ 
% 4.19/4.38              (k2_zfmisc_1 @ X52 @ X51)))),
% 4.19/4.38      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 4.19/4.38  thf('8', plain,
% 4.19/4.38      (![X0 : $i]:
% 4.19/4.38         ((k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ sk_C) @ 
% 4.19/4.38           (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_D) @ X0))
% 4.19/4.38           = (k2_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 4.19/4.38              (k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ sk_C) @ X0)))),
% 4.19/4.38      inference('sup+', [status(thm)], ['6', '7'])).
% 4.19/4.38  thf('9', plain,
% 4.19/4.38      (((k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ sk_C) @ 
% 4.19/4.38         (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_D) @ sk_B))
% 4.19/4.38         = (k2_zfmisc_1 @ (k2_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ sk_C)) @ 
% 4.19/4.38            sk_B))),
% 4.19/4.38      inference('sup+', [status(thm)], ['1', '8'])).
% 4.19/4.38  thf(commutativity_k2_tarski, axiom,
% 4.19/4.38    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 4.19/4.38  thf('10', plain,
% 4.19/4.38      (![X15 : $i, X16 : $i]:
% 4.19/4.38         ((k2_tarski @ X16 @ X15) = (k2_tarski @ X15 @ X16))),
% 4.19/4.38      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 4.19/4.38  thf(l51_zfmisc_1, axiom,
% 4.19/4.38    (![A:$i,B:$i]:
% 4.19/4.38     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 4.19/4.38  thf('11', plain,
% 4.19/4.38      (![X44 : $i, X45 : $i]:
% 4.19/4.38         ((k3_tarski @ (k2_tarski @ X44 @ X45)) = (k2_xboole_0 @ X44 @ X45))),
% 4.19/4.38      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 4.19/4.38  thf('12', plain,
% 4.19/4.38      (![X0 : $i, X1 : $i]:
% 4.19/4.38         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 4.19/4.38      inference('sup+', [status(thm)], ['10', '11'])).
% 4.19/4.38  thf('13', plain,
% 4.19/4.38      (![X44 : $i, X45 : $i]:
% 4.19/4.38         ((k3_tarski @ (k2_tarski @ X44 @ X45)) = (k2_xboole_0 @ X44 @ X45))),
% 4.19/4.38      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 4.19/4.38  thf('14', plain,
% 4.19/4.38      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 4.19/4.38      inference('sup+', [status(thm)], ['12', '13'])).
% 4.19/4.38  thf(t22_xboole_1, axiom,
% 4.19/4.38    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 4.19/4.38  thf('15', plain,
% 4.19/4.38      (![X8 : $i, X9 : $i]:
% 4.19/4.38         ((k2_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)) = (X8))),
% 4.19/4.38      inference('cnf', [status(esa)], [t22_xboole_1])).
% 4.19/4.38  thf('16', plain,
% 4.19/4.38      (![X8 : $i, X9 : $i]:
% 4.19/4.38         ((k2_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)) = (X8))),
% 4.19/4.38      inference('cnf', [status(esa)], [t22_xboole_1])).
% 4.19/4.38  thf('17', plain,
% 4.19/4.38      (((k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ sk_C) @ sk_B)
% 4.19/4.38         = (k2_zfmisc_1 @ sk_A @ sk_B))),
% 4.19/4.38      inference('demod', [status(thm)], ['9', '14', '15', '16'])).
% 4.19/4.38  thf(idempotence_k3_xboole_0, axiom,
% 4.19/4.38    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 4.19/4.38  thf('18', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 4.19/4.38      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 4.19/4.38  thf('19', plain,
% 4.19/4.38      (![X53 : $i, X54 : $i, X55 : $i, X56 : $i]:
% 4.19/4.38         ((k2_zfmisc_1 @ (k3_xboole_0 @ X53 @ X55) @ (k3_xboole_0 @ X54 @ X56))
% 4.19/4.38           = (k3_xboole_0 @ (k2_zfmisc_1 @ X53 @ X54) @ 
% 4.19/4.38              (k2_zfmisc_1 @ X55 @ X56)))),
% 4.19/4.38      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 4.19/4.38  thf(t100_xboole_1, axiom,
% 4.19/4.38    (![A:$i,B:$i]:
% 4.19/4.38     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 4.19/4.38  thf('20', plain,
% 4.19/4.38      (![X4 : $i, X5 : $i]:
% 4.19/4.38         ((k4_xboole_0 @ X4 @ X5)
% 4.19/4.38           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 4.19/4.38      inference('cnf', [status(esa)], [t100_xboole_1])).
% 4.19/4.38  thf('21', plain,
% 4.19/4.38      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.19/4.38         ((k4_xboole_0 @ (k2_zfmisc_1 @ X3 @ X1) @ (k2_zfmisc_1 @ X2 @ X0))
% 4.19/4.38           = (k5_xboole_0 @ (k2_zfmisc_1 @ X3 @ X1) @ 
% 4.19/4.38              (k2_zfmisc_1 @ (k3_xboole_0 @ X3 @ X2) @ (k3_xboole_0 @ X1 @ X0))))),
% 4.19/4.38      inference('sup+', [status(thm)], ['19', '20'])).
% 4.19/4.38  thf('22', plain,
% 4.19/4.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.19/4.38         ((k4_xboole_0 @ (k2_zfmisc_1 @ X2 @ X0) @ (k2_zfmisc_1 @ X1 @ X0))
% 4.19/4.38           = (k5_xboole_0 @ (k2_zfmisc_1 @ X2 @ X0) @ 
% 4.19/4.38              (k2_zfmisc_1 @ (k3_xboole_0 @ X2 @ X1) @ X0)))),
% 4.19/4.38      inference('sup+', [status(thm)], ['18', '21'])).
% 4.19/4.38  thf(t125_zfmisc_1, axiom,
% 4.19/4.38    (![A:$i,B:$i,C:$i]:
% 4.19/4.38     ( ( ( k2_zfmisc_1 @ C @ ( k4_xboole_0 @ A @ B ) ) =
% 4.19/4.38         ( k4_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 4.19/4.38       ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 4.19/4.38         ( k4_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 4.19/4.38  thf('23', plain,
% 4.19/4.38      (![X57 : $i, X58 : $i, X59 : $i]:
% 4.19/4.38         ((k2_zfmisc_1 @ (k4_xboole_0 @ X57 @ X59) @ X58)
% 4.19/4.38           = (k4_xboole_0 @ (k2_zfmisc_1 @ X57 @ X58) @ 
% 4.19/4.38              (k2_zfmisc_1 @ X59 @ X58)))),
% 4.19/4.38      inference('cnf', [status(esa)], [t125_zfmisc_1])).
% 4.19/4.38  thf('24', plain,
% 4.19/4.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.19/4.38         ((k2_zfmisc_1 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 4.19/4.38           = (k5_xboole_0 @ (k2_zfmisc_1 @ X2 @ X0) @ 
% 4.19/4.38              (k2_zfmisc_1 @ (k3_xboole_0 @ X2 @ X1) @ X0)))),
% 4.19/4.38      inference('demod', [status(thm)], ['22', '23'])).
% 4.19/4.38  thf('25', plain,
% 4.19/4.38      (((k2_zfmisc_1 @ (k4_xboole_0 @ sk_A @ sk_C) @ sk_B)
% 4.19/4.38         = (k5_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 4.19/4.38            (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.19/4.38      inference('sup+', [status(thm)], ['17', '24'])).
% 4.19/4.38  thf(t92_xboole_1, axiom,
% 4.19/4.38    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 4.19/4.38  thf('26', plain, (![X14 : $i]: ((k5_xboole_0 @ X14 @ X14) = (k1_xboole_0))),
% 4.19/4.38      inference('cnf', [status(esa)], [t92_xboole_1])).
% 4.19/4.38  thf('27', plain,
% 4.19/4.38      (((k2_zfmisc_1 @ (k4_xboole_0 @ sk_A @ sk_C) @ sk_B) = (k1_xboole_0))),
% 4.19/4.38      inference('demod', [status(thm)], ['25', '26'])).
% 4.19/4.38  thf(t113_zfmisc_1, axiom,
% 4.19/4.38    (![A:$i,B:$i]:
% 4.19/4.38     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 4.19/4.38       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 4.19/4.38  thf('28', plain,
% 4.19/4.38      (![X46 : $i, X47 : $i]:
% 4.19/4.38         (((X46) = (k1_xboole_0))
% 4.19/4.38          | ((X47) = (k1_xboole_0))
% 4.19/4.38          | ((k2_zfmisc_1 @ X47 @ X46) != (k1_xboole_0)))),
% 4.19/4.38      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 4.19/4.38  thf('29', plain,
% 4.19/4.38      ((((k1_xboole_0) != (k1_xboole_0))
% 4.19/4.38        | ((k4_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0))
% 4.19/4.38        | ((sk_B) = (k1_xboole_0)))),
% 4.19/4.38      inference('sup-', [status(thm)], ['27', '28'])).
% 4.19/4.38  thf('30', plain,
% 4.19/4.38      ((((sk_B) = (k1_xboole_0))
% 4.19/4.38        | ((k4_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0)))),
% 4.19/4.38      inference('simplify', [status(thm)], ['29'])).
% 4.19/4.38  thf(l32_xboole_1, axiom,
% 4.19/4.38    (![A:$i,B:$i]:
% 4.19/4.38     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 4.19/4.38  thf('31', plain,
% 4.19/4.38      (![X1 : $i, X2 : $i]:
% 4.19/4.38         ((r1_tarski @ X1 @ X2) | ((k4_xboole_0 @ X1 @ X2) != (k1_xboole_0)))),
% 4.19/4.38      inference('cnf', [status(esa)], [l32_xboole_1])).
% 4.19/4.38  thf('32', plain,
% 4.19/4.38      ((((k1_xboole_0) != (k1_xboole_0))
% 4.19/4.38        | ((sk_B) = (k1_xboole_0))
% 4.19/4.38        | (r1_tarski @ sk_A @ sk_C))),
% 4.19/4.38      inference('sup-', [status(thm)], ['30', '31'])).
% 4.19/4.38  thf('33', plain, (((r1_tarski @ sk_A @ sk_C) | ((sk_B) = (k1_xboole_0)))),
% 4.19/4.38      inference('simplify', [status(thm)], ['32'])).
% 4.19/4.38  thf('34', plain,
% 4.19/4.38      ((~ (r1_tarski @ sk_A @ sk_C) | ~ (r1_tarski @ sk_B @ sk_D))),
% 4.19/4.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.19/4.38  thf('35', plain,
% 4.19/4.38      ((~ (r1_tarski @ sk_A @ sk_C)) <= (~ ((r1_tarski @ sk_A @ sk_C)))),
% 4.19/4.38      inference('split', [status(esa)], ['34'])).
% 4.19/4.38  thf('36', plain,
% 4.19/4.38      (![X49 : $i, X51 : $i, X52 : $i]:
% 4.19/4.38         ((k2_zfmisc_1 @ X52 @ (k2_xboole_0 @ X49 @ X51))
% 4.19/4.38           = (k2_xboole_0 @ (k2_zfmisc_1 @ X52 @ X49) @ 
% 4.19/4.38              (k2_zfmisc_1 @ X52 @ X51)))),
% 4.19/4.38      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 4.19/4.38  thf('37', plain,
% 4.19/4.38      (((k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ sk_C) @ 
% 4.19/4.38         (k3_xboole_0 @ sk_B @ sk_D)) = (k2_zfmisc_1 @ sk_A @ sk_B))),
% 4.19/4.38      inference('demod', [status(thm)], ['4', '5'])).
% 4.19/4.38  thf('38', plain,
% 4.19/4.38      (![X49 : $i, X50 : $i, X51 : $i]:
% 4.19/4.38         ((k2_zfmisc_1 @ (k2_xboole_0 @ X49 @ X51) @ X50)
% 4.19/4.38           = (k2_xboole_0 @ (k2_zfmisc_1 @ X49 @ X50) @ 
% 4.19/4.38              (k2_zfmisc_1 @ X51 @ X50)))),
% 4.19/4.38      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 4.19/4.38  thf('39', plain,
% 4.19/4.38      (![X0 : $i]:
% 4.19/4.38         ((k2_zfmisc_1 @ (k2_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_C) @ X0) @ 
% 4.19/4.38           (k3_xboole_0 @ sk_B @ sk_D))
% 4.19/4.38           = (k2_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 4.19/4.38              (k2_zfmisc_1 @ X0 @ (k3_xboole_0 @ sk_B @ sk_D))))),
% 4.19/4.38      inference('sup+', [status(thm)], ['37', '38'])).
% 4.19/4.38  thf('40', plain,
% 4.19/4.38      (((k2_zfmisc_1 @ (k2_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_C) @ sk_A) @ 
% 4.19/4.38         (k3_xboole_0 @ sk_B @ sk_D))
% 4.19/4.38         = (k2_zfmisc_1 @ sk_A @ 
% 4.19/4.38            (k2_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_B @ sk_D))))),
% 4.19/4.38      inference('sup+', [status(thm)], ['36', '39'])).
% 4.19/4.38  thf('41', plain,
% 4.19/4.38      (![X8 : $i, X9 : $i]:
% 4.19/4.38         ((k2_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)) = (X8))),
% 4.19/4.38      inference('cnf', [status(esa)], [t22_xboole_1])).
% 4.19/4.38  thf('42', plain,
% 4.19/4.38      (((k2_zfmisc_1 @ (k2_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_C) @ sk_A) @ 
% 4.19/4.38         (k3_xboole_0 @ sk_B @ sk_D)) = (k2_zfmisc_1 @ sk_A @ sk_B))),
% 4.19/4.38      inference('demod', [status(thm)], ['40', '41'])).
% 4.19/4.38  thf('43', plain,
% 4.19/4.38      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 4.19/4.38      inference('sup+', [status(thm)], ['12', '13'])).
% 4.19/4.38  thf('44', plain,
% 4.19/4.38      (![X8 : $i, X9 : $i]:
% 4.19/4.38         ((k2_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)) = (X8))),
% 4.19/4.38      inference('cnf', [status(esa)], [t22_xboole_1])).
% 4.19/4.38  thf('45', plain,
% 4.19/4.38      (((k2_zfmisc_1 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_D))
% 4.19/4.38         = (k2_zfmisc_1 @ sk_A @ sk_B))),
% 4.19/4.38      inference('demod', [status(thm)], ['42', '43', '44'])).
% 4.19/4.38  thf('46', plain,
% 4.19/4.38      (![X57 : $i, X59 : $i, X60 : $i]:
% 4.19/4.38         ((k2_zfmisc_1 @ X60 @ (k4_xboole_0 @ X57 @ X59))
% 4.19/4.38           = (k4_xboole_0 @ (k2_zfmisc_1 @ X60 @ X57) @ 
% 4.19/4.38              (k2_zfmisc_1 @ X60 @ X59)))),
% 4.19/4.38      inference('cnf', [status(esa)], [t125_zfmisc_1])).
% 4.19/4.38  thf('47', plain,
% 4.19/4.38      (((k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ sk_C) @ 
% 4.19/4.38         (k3_xboole_0 @ sk_B @ sk_D)) = (k2_zfmisc_1 @ sk_A @ sk_B))),
% 4.19/4.38      inference('demod', [status(thm)], ['4', '5'])).
% 4.19/4.38  thf('48', plain,
% 4.19/4.38      (![X57 : $i, X58 : $i, X59 : $i]:
% 4.19/4.38         ((k2_zfmisc_1 @ (k4_xboole_0 @ X57 @ X59) @ X58)
% 4.19/4.38           = (k4_xboole_0 @ (k2_zfmisc_1 @ X57 @ X58) @ 
% 4.19/4.38              (k2_zfmisc_1 @ X59 @ X58)))),
% 4.19/4.38      inference('cnf', [status(esa)], [t125_zfmisc_1])).
% 4.19/4.38  thf('49', plain,
% 4.19/4.38      (![X0 : $i]:
% 4.19/4.38         ((k2_zfmisc_1 @ (k4_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_C) @ X0) @ 
% 4.19/4.38           (k3_xboole_0 @ sk_B @ sk_D))
% 4.19/4.38           = (k4_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 4.19/4.38              (k2_zfmisc_1 @ X0 @ (k3_xboole_0 @ sk_B @ sk_D))))),
% 4.19/4.38      inference('sup+', [status(thm)], ['47', '48'])).
% 4.19/4.38  thf('50', plain,
% 4.19/4.38      (((k2_zfmisc_1 @ (k4_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_C) @ sk_A) @ 
% 4.19/4.38         (k3_xboole_0 @ sk_B @ sk_D))
% 4.19/4.38         = (k2_zfmisc_1 @ sk_A @ 
% 4.19/4.38            (k4_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_B @ sk_D))))),
% 4.19/4.38      inference('sup+', [status(thm)], ['46', '49'])).
% 4.19/4.38  thf(t17_xboole_1, axiom,
% 4.19/4.38    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 4.19/4.38  thf('51', plain,
% 4.19/4.38      (![X6 : $i, X7 : $i]: (r1_tarski @ (k3_xboole_0 @ X6 @ X7) @ X6)),
% 4.19/4.38      inference('cnf', [status(esa)], [t17_xboole_1])).
% 4.19/4.38  thf('52', plain,
% 4.19/4.38      (![X1 : $i, X3 : $i]:
% 4.19/4.38         (((k4_xboole_0 @ X1 @ X3) = (k1_xboole_0)) | ~ (r1_tarski @ X1 @ X3))),
% 4.19/4.38      inference('cnf', [status(esa)], [l32_xboole_1])).
% 4.19/4.38  thf('53', plain,
% 4.19/4.38      (![X0 : $i, X1 : $i]:
% 4.19/4.38         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 4.19/4.38      inference('sup-', [status(thm)], ['51', '52'])).
% 4.19/4.38  thf('54', plain,
% 4.19/4.38      (![X47 : $i, X48 : $i]:
% 4.19/4.38         (((k2_zfmisc_1 @ X47 @ X48) = (k1_xboole_0))
% 4.19/4.38          | ((X47) != (k1_xboole_0)))),
% 4.19/4.38      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 4.19/4.38  thf('55', plain,
% 4.19/4.38      (![X48 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X48) = (k1_xboole_0))),
% 4.19/4.38      inference('simplify', [status(thm)], ['54'])).
% 4.19/4.38  thf('56', plain,
% 4.19/4.38      (((k1_xboole_0)
% 4.19/4.38         = (k2_zfmisc_1 @ sk_A @ 
% 4.19/4.38            (k4_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_B @ sk_D))))),
% 4.19/4.38      inference('demod', [status(thm)], ['50', '53', '55'])).
% 4.19/4.38  thf('57', plain,
% 4.19/4.38      (![X57 : $i, X58 : $i, X59 : $i]:
% 4.19/4.38         ((k2_zfmisc_1 @ (k4_xboole_0 @ X57 @ X59) @ X58)
% 4.19/4.38           = (k4_xboole_0 @ (k2_zfmisc_1 @ X57 @ X58) @ 
% 4.19/4.38              (k2_zfmisc_1 @ X59 @ X58)))),
% 4.19/4.38      inference('cnf', [status(esa)], [t125_zfmisc_1])).
% 4.19/4.38  thf('58', plain,
% 4.19/4.38      (![X0 : $i]:
% 4.19/4.38         ((k2_zfmisc_1 @ (k4_xboole_0 @ sk_A @ X0) @ 
% 4.19/4.38           (k4_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_B @ sk_D)))
% 4.19/4.38           = (k4_xboole_0 @ k1_xboole_0 @ 
% 4.19/4.38              (k2_zfmisc_1 @ X0 @ 
% 4.19/4.38               (k4_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_B @ sk_D)))))),
% 4.19/4.38      inference('sup+', [status(thm)], ['56', '57'])).
% 4.19/4.38  thf('59', plain,
% 4.19/4.38      (![X6 : $i, X7 : $i]: (r1_tarski @ (k3_xboole_0 @ X6 @ X7) @ X6)),
% 4.19/4.38      inference('cnf', [status(esa)], [t17_xboole_1])).
% 4.19/4.38  thf(t3_xboole_1, axiom,
% 4.19/4.38    (![A:$i]:
% 4.19/4.38     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 4.19/4.38  thf('60', plain,
% 4.19/4.38      (![X12 : $i]:
% 4.19/4.38         (((X12) = (k1_xboole_0)) | ~ (r1_tarski @ X12 @ k1_xboole_0))),
% 4.19/4.38      inference('cnf', [status(esa)], [t3_xboole_1])).
% 4.19/4.38  thf('61', plain,
% 4.19/4.38      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 4.19/4.38      inference('sup-', [status(thm)], ['59', '60'])).
% 4.19/4.38  thf('62', plain,
% 4.19/4.38      (![X4 : $i, X5 : $i]:
% 4.19/4.38         ((k4_xboole_0 @ X4 @ X5)
% 4.19/4.38           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 4.19/4.38      inference('cnf', [status(esa)], [t100_xboole_1])).
% 4.19/4.38  thf('63', plain,
% 4.19/4.38      (![X0 : $i]:
% 4.19/4.38         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 4.19/4.38           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 4.19/4.38      inference('sup+', [status(thm)], ['61', '62'])).
% 4.19/4.38  thf(t5_boole, axiom,
% 4.19/4.38    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 4.19/4.38  thf('64', plain, (![X13 : $i]: ((k5_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 4.19/4.38      inference('cnf', [status(esa)], [t5_boole])).
% 4.19/4.38  thf('65', plain,
% 4.19/4.38      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 4.19/4.38      inference('demod', [status(thm)], ['63', '64'])).
% 4.19/4.38  thf('66', plain,
% 4.19/4.38      (![X0 : $i]:
% 4.19/4.38         ((k2_zfmisc_1 @ (k4_xboole_0 @ sk_A @ X0) @ 
% 4.19/4.38           (k4_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_B @ sk_D))) = (k1_xboole_0))),
% 4.19/4.38      inference('demod', [status(thm)], ['58', '65'])).
% 4.19/4.38  thf('67', plain,
% 4.19/4.38      (![X46 : $i, X47 : $i]:
% 4.19/4.38         (((X46) = (k1_xboole_0))
% 4.19/4.38          | ((X47) = (k1_xboole_0))
% 4.19/4.38          | ((k2_zfmisc_1 @ X47 @ X46) != (k1_xboole_0)))),
% 4.19/4.38      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 4.19/4.38  thf('68', plain,
% 4.19/4.38      (![X0 : $i]:
% 4.19/4.38         (((k1_xboole_0) != (k1_xboole_0))
% 4.19/4.38          | ((k4_xboole_0 @ sk_A @ X0) = (k1_xboole_0))
% 4.19/4.38          | ((k4_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_B @ sk_D)) = (k1_xboole_0)))),
% 4.19/4.38      inference('sup-', [status(thm)], ['66', '67'])).
% 4.19/4.38  thf('69', plain,
% 4.19/4.38      (![X0 : $i]:
% 4.19/4.38         (((k4_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_B @ sk_D)) = (k1_xboole_0))
% 4.19/4.38          | ((k4_xboole_0 @ sk_A @ X0) = (k1_xboole_0)))),
% 4.19/4.38      inference('simplify', [status(thm)], ['68'])).
% 4.19/4.38  thf('70', plain,
% 4.19/4.38      (![X1 : $i, X2 : $i]:
% 4.19/4.38         ((r1_tarski @ X1 @ X2) | ((k4_xboole_0 @ X1 @ X2) != (k1_xboole_0)))),
% 4.19/4.38      inference('cnf', [status(esa)], [l32_xboole_1])).
% 4.19/4.38  thf('71', plain,
% 4.19/4.38      (![X0 : $i]:
% 4.19/4.38         (((k1_xboole_0) != (k1_xboole_0))
% 4.19/4.38          | ((k4_xboole_0 @ sk_A @ X0) = (k1_xboole_0))
% 4.19/4.38          | (r1_tarski @ sk_B @ (k3_xboole_0 @ sk_B @ sk_D)))),
% 4.19/4.38      inference('sup-', [status(thm)], ['69', '70'])).
% 4.19/4.38  thf('72', plain,
% 4.19/4.38      (![X0 : $i]:
% 4.19/4.38         ((r1_tarski @ sk_B @ (k3_xboole_0 @ sk_B @ sk_D))
% 4.19/4.38          | ((k4_xboole_0 @ sk_A @ X0) = (k1_xboole_0)))),
% 4.19/4.38      inference('simplify', [status(thm)], ['71'])).
% 4.19/4.38  thf('73', plain, (![X14 : $i]: ((k5_xboole_0 @ X14 @ X14) = (k1_xboole_0))),
% 4.19/4.38      inference('cnf', [status(esa)], [t92_xboole_1])).
% 4.19/4.38  thf('74', plain,
% 4.19/4.38      (![X48 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X48) = (k1_xboole_0))),
% 4.19/4.38      inference('simplify', [status(thm)], ['54'])).
% 4.19/4.38  thf('75', plain,
% 4.19/4.38      (![X0 : $i, X1 : $i]:
% 4.19/4.38         ((k2_zfmisc_1 @ (k5_xboole_0 @ X0 @ X0) @ X1) = (k1_xboole_0))),
% 4.19/4.38      inference('sup+', [status(thm)], ['73', '74'])).
% 4.19/4.38  thf('76', plain,
% 4.19/4.38      (![X57 : $i, X58 : $i, X59 : $i]:
% 4.19/4.38         ((k2_zfmisc_1 @ (k4_xboole_0 @ X57 @ X59) @ X58)
% 4.19/4.38           = (k4_xboole_0 @ (k2_zfmisc_1 @ X57 @ X58) @ 
% 4.19/4.38              (k2_zfmisc_1 @ X59 @ X58)))),
% 4.19/4.38      inference('cnf', [status(esa)], [t125_zfmisc_1])).
% 4.19/4.38  thf('77', plain,
% 4.19/4.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.19/4.38         ((k2_zfmisc_1 @ (k4_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X1)) @ X0)
% 4.19/4.38           = (k4_xboole_0 @ (k2_zfmisc_1 @ X2 @ X0) @ k1_xboole_0))),
% 4.19/4.38      inference('sup+', [status(thm)], ['75', '76'])).
% 4.19/4.38  thf('78', plain,
% 4.19/4.38      (![X1 : $i, X2 : $i]:
% 4.19/4.38         ((r1_tarski @ X1 @ X2) | ((k4_xboole_0 @ X1 @ X2) != (k1_xboole_0)))),
% 4.19/4.38      inference('cnf', [status(esa)], [l32_xboole_1])).
% 4.19/4.38  thf('79', plain,
% 4.19/4.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.19/4.38         (((k2_zfmisc_1 @ (k4_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X1)) @ X0)
% 4.19/4.38            != (k1_xboole_0))
% 4.19/4.38          | (r1_tarski @ (k2_zfmisc_1 @ X2 @ X0) @ k1_xboole_0))),
% 4.19/4.38      inference('sup-', [status(thm)], ['77', '78'])).
% 4.19/4.38  thf('80', plain,
% 4.19/4.38      (![X0 : $i]:
% 4.19/4.38         (((k2_zfmisc_1 @ k1_xboole_0 @ X0) != (k1_xboole_0))
% 4.19/4.38          | (r1_tarski @ sk_B @ (k3_xboole_0 @ sk_B @ sk_D))
% 4.19/4.38          | (r1_tarski @ (k2_zfmisc_1 @ sk_A @ X0) @ k1_xboole_0))),
% 4.19/4.38      inference('sup-', [status(thm)], ['72', '79'])).
% 4.19/4.38  thf('81', plain,
% 4.19/4.38      (![X48 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X48) = (k1_xboole_0))),
% 4.19/4.38      inference('simplify', [status(thm)], ['54'])).
% 4.19/4.38  thf('82', plain,
% 4.19/4.38      (![X0 : $i]:
% 4.19/4.38         (((k1_xboole_0) != (k1_xboole_0))
% 4.19/4.38          | (r1_tarski @ sk_B @ (k3_xboole_0 @ sk_B @ sk_D))
% 4.19/4.38          | (r1_tarski @ (k2_zfmisc_1 @ sk_A @ X0) @ k1_xboole_0))),
% 4.19/4.38      inference('demod', [status(thm)], ['80', '81'])).
% 4.19/4.38  thf('83', plain,
% 4.19/4.38      (![X0 : $i]:
% 4.19/4.38         ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ X0) @ k1_xboole_0)
% 4.19/4.38          | (r1_tarski @ sk_B @ (k3_xboole_0 @ sk_B @ sk_D)))),
% 4.19/4.38      inference('simplify', [status(thm)], ['82'])).
% 4.19/4.38  thf('84', plain,
% 4.19/4.38      (![X12 : $i]:
% 4.19/4.38         (((X12) = (k1_xboole_0)) | ~ (r1_tarski @ X12 @ k1_xboole_0))),
% 4.19/4.38      inference('cnf', [status(esa)], [t3_xboole_1])).
% 4.19/4.38  thf('85', plain,
% 4.19/4.38      (![X0 : $i]:
% 4.19/4.38         ((r1_tarski @ sk_B @ (k3_xboole_0 @ sk_B @ sk_D))
% 4.19/4.38          | ((k2_zfmisc_1 @ sk_A @ X0) = (k1_xboole_0)))),
% 4.19/4.38      inference('sup-', [status(thm)], ['83', '84'])).
% 4.19/4.38  thf('86', plain,
% 4.19/4.38      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 4.19/4.38        | (r1_tarski @ sk_B @ (k3_xboole_0 @ sk_B @ sk_D)))),
% 4.19/4.38      inference('sup+', [status(thm)], ['45', '85'])).
% 4.19/4.38  thf('87', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0))),
% 4.19/4.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.19/4.38  thf('88', plain, ((r1_tarski @ sk_B @ (k3_xboole_0 @ sk_B @ sk_D))),
% 4.19/4.38      inference('simplify_reflect-', [status(thm)], ['86', '87'])).
% 4.19/4.38  thf('89', plain,
% 4.19/4.38      (![X10 : $i, X11 : $i]:
% 4.19/4.38         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 4.19/4.38      inference('cnf', [status(esa)], [t28_xboole_1])).
% 4.19/4.38  thf('90', plain,
% 4.19/4.38      (((k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_B @ sk_D)) = (sk_B))),
% 4.19/4.38      inference('sup-', [status(thm)], ['88', '89'])).
% 4.19/4.38  thf('91', plain,
% 4.19/4.38      (((k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ sk_C) @ 
% 4.19/4.38         (k3_xboole_0 @ sk_B @ sk_D)) = (k2_zfmisc_1 @ sk_A @ sk_B))),
% 4.19/4.38      inference('demod', [status(thm)], ['4', '5'])).
% 4.19/4.38  thf('92', plain,
% 4.19/4.38      (![X53 : $i, X54 : $i, X55 : $i, X56 : $i]:
% 4.19/4.38         ((k2_zfmisc_1 @ (k3_xboole_0 @ X53 @ X55) @ (k3_xboole_0 @ X54 @ X56))
% 4.19/4.38           = (k3_xboole_0 @ (k2_zfmisc_1 @ X53 @ X54) @ 
% 4.19/4.38              (k2_zfmisc_1 @ X55 @ X56)))),
% 4.19/4.38      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 4.19/4.38  thf('93', plain,
% 4.19/4.38      (![X0 : $i, X1 : $i]:
% 4.19/4.38         ((k2_zfmisc_1 @ (k3_xboole_0 @ X1 @ (k3_xboole_0 @ sk_A @ sk_C)) @ 
% 4.19/4.38           (k3_xboole_0 @ X0 @ (k3_xboole_0 @ sk_B @ sk_D)))
% 4.19/4.38           = (k3_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0) @ 
% 4.19/4.38              (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.19/4.38      inference('sup+', [status(thm)], ['91', '92'])).
% 4.19/4.38  thf('94', plain,
% 4.19/4.38      (![X53 : $i, X54 : $i, X55 : $i, X56 : $i]:
% 4.19/4.38         ((k2_zfmisc_1 @ (k3_xboole_0 @ X53 @ X55) @ (k3_xboole_0 @ X54 @ X56))
% 4.19/4.38           = (k3_xboole_0 @ (k2_zfmisc_1 @ X53 @ X54) @ 
% 4.19/4.38              (k2_zfmisc_1 @ X55 @ X56)))),
% 4.19/4.38      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 4.19/4.38  thf('95', plain,
% 4.19/4.38      (![X0 : $i, X1 : $i]:
% 4.19/4.38         ((k2_zfmisc_1 @ (k3_xboole_0 @ X1 @ (k3_xboole_0 @ sk_A @ sk_C)) @ 
% 4.19/4.38           (k3_xboole_0 @ X0 @ (k3_xboole_0 @ sk_B @ sk_D)))
% 4.19/4.38           = (k2_zfmisc_1 @ (k3_xboole_0 @ X1 @ sk_A) @ 
% 4.19/4.38              (k3_xboole_0 @ X0 @ sk_B)))),
% 4.19/4.38      inference('demod', [status(thm)], ['93', '94'])).
% 4.19/4.38  thf('96', plain,
% 4.19/4.38      (![X0 : $i]:
% 4.19/4.38         ((k2_zfmisc_1 @ (k3_xboole_0 @ X0 @ (k3_xboole_0 @ sk_A @ sk_C)) @ 
% 4.19/4.38           sk_B)
% 4.19/4.38           = (k2_zfmisc_1 @ (k3_xboole_0 @ X0 @ sk_A) @ 
% 4.19/4.38              (k3_xboole_0 @ sk_B @ sk_B)))),
% 4.19/4.38      inference('sup+', [status(thm)], ['90', '95'])).
% 4.19/4.38  thf('97', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 4.19/4.38      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 4.19/4.38  thf('98', plain,
% 4.19/4.38      (![X0 : $i]:
% 4.19/4.38         ((k2_zfmisc_1 @ (k3_xboole_0 @ X0 @ (k3_xboole_0 @ sk_A @ sk_C)) @ 
% 4.19/4.38           sk_B) = (k2_zfmisc_1 @ (k3_xboole_0 @ X0 @ sk_A) @ sk_B))),
% 4.19/4.38      inference('demod', [status(thm)], ['96', '97'])).
% 4.19/4.38  thf('99', plain,
% 4.19/4.38      (![X6 : $i, X7 : $i]: (r1_tarski @ (k3_xboole_0 @ X6 @ X7) @ X6)),
% 4.19/4.38      inference('cnf', [status(esa)], [t17_xboole_1])).
% 4.19/4.38  thf('100', plain,
% 4.19/4.38      (![X10 : $i, X11 : $i]:
% 4.19/4.38         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 4.19/4.38      inference('cnf', [status(esa)], [t28_xboole_1])).
% 4.19/4.38  thf('101', plain,
% 4.19/4.38      (![X0 : $i, X1 : $i]:
% 4.19/4.38         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 4.19/4.38           = (k3_xboole_0 @ X0 @ X1))),
% 4.19/4.38      inference('sup-', [status(thm)], ['99', '100'])).
% 4.19/4.38  thf('102', plain,
% 4.19/4.38      (((k2_zfmisc_1 @ (k2_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_C) @ sk_A) @ 
% 4.19/4.38         (k3_xboole_0 @ sk_B @ sk_D)) = (k2_zfmisc_1 @ sk_A @ sk_B))),
% 4.19/4.38      inference('demod', [status(thm)], ['40', '41'])).
% 4.19/4.38  thf('103', plain,
% 4.19/4.38      (![X53 : $i, X54 : $i, X55 : $i, X56 : $i]:
% 4.19/4.38         ((k2_zfmisc_1 @ (k3_xboole_0 @ X53 @ X55) @ (k3_xboole_0 @ X54 @ X56))
% 4.19/4.38           = (k3_xboole_0 @ (k2_zfmisc_1 @ X53 @ X54) @ 
% 4.19/4.38              (k2_zfmisc_1 @ X55 @ X56)))),
% 4.19/4.38      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 4.19/4.38  thf('104', plain,
% 4.19/4.38      (![X0 : $i, X1 : $i]:
% 4.19/4.38         ((k2_zfmisc_1 @ 
% 4.19/4.38           (k3_xboole_0 @ (k2_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_C) @ sk_A) @ 
% 4.19/4.38            X1) @ 
% 4.19/4.38           (k3_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_D) @ X0))
% 4.19/4.38           = (k3_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 4.19/4.38              (k2_zfmisc_1 @ X1 @ X0)))),
% 4.19/4.38      inference('sup+', [status(thm)], ['102', '103'])).
% 4.19/4.38  thf('105', plain,
% 4.19/4.38      (![X53 : $i, X54 : $i, X55 : $i, X56 : $i]:
% 4.19/4.38         ((k2_zfmisc_1 @ (k3_xboole_0 @ X53 @ X55) @ (k3_xboole_0 @ X54 @ X56))
% 4.19/4.38           = (k3_xboole_0 @ (k2_zfmisc_1 @ X53 @ X54) @ 
% 4.19/4.38              (k2_zfmisc_1 @ X55 @ X56)))),
% 4.19/4.38      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 4.19/4.38  thf('106', plain,
% 4.19/4.38      (![X0 : $i, X1 : $i]:
% 4.19/4.38         ((k2_zfmisc_1 @ 
% 4.19/4.38           (k3_xboole_0 @ (k2_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_C) @ sk_A) @ 
% 4.19/4.38            X1) @ 
% 4.19/4.38           (k3_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_D) @ X0))
% 4.19/4.38           = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ X1) @ 
% 4.19/4.38              (k3_xboole_0 @ sk_B @ X0)))),
% 4.19/4.38      inference('demod', [status(thm)], ['104', '105'])).
% 4.19/4.38  thf('107', plain,
% 4.19/4.38      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 4.19/4.38      inference('sup+', [status(thm)], ['12', '13'])).
% 4.19/4.38  thf('108', plain,
% 4.19/4.38      (![X8 : $i, X9 : $i]:
% 4.19/4.38         ((k2_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)) = (X8))),
% 4.19/4.38      inference('cnf', [status(esa)], [t22_xboole_1])).
% 4.19/4.38  thf('109', plain,
% 4.19/4.38      (![X0 : $i, X1 : $i]:
% 4.19/4.38         ((k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ X1) @ 
% 4.19/4.38           (k3_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_D) @ X0))
% 4.19/4.38           = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ X1) @ 
% 4.19/4.38              (k3_xboole_0 @ sk_B @ X0)))),
% 4.19/4.38      inference('demod', [status(thm)], ['106', '107', '108'])).
% 4.19/4.38  thf('110', plain,
% 4.19/4.38      (![X0 : $i]:
% 4.19/4.38         ((k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ X0) @ 
% 4.19/4.38           (k3_xboole_0 @ sk_B @ sk_D))
% 4.19/4.38           = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ X0) @ 
% 4.19/4.38              (k3_xboole_0 @ sk_B @ sk_B)))),
% 4.19/4.38      inference('sup+', [status(thm)], ['101', '109'])).
% 4.19/4.38  thf('111', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 4.19/4.38      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 4.19/4.38  thf('112', plain,
% 4.19/4.38      (![X0 : $i]:
% 4.19/4.38         ((k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ X0) @ 
% 4.19/4.38           (k3_xboole_0 @ sk_B @ sk_D))
% 4.19/4.38           = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ X0) @ sk_B))),
% 4.19/4.38      inference('demod', [status(thm)], ['110', '111'])).
% 4.19/4.38  thf('113', plain,
% 4.19/4.38      (![X0 : $i, X1 : $i]:
% 4.19/4.38         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 4.19/4.38           = (k3_xboole_0 @ X0 @ X1))),
% 4.19/4.38      inference('sup-', [status(thm)], ['99', '100'])).
% 4.19/4.38  thf('114', plain,
% 4.19/4.38      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.19/4.38         ((k4_xboole_0 @ (k2_zfmisc_1 @ X3 @ X1) @ (k2_zfmisc_1 @ X2 @ X0))
% 4.19/4.38           = (k5_xboole_0 @ (k2_zfmisc_1 @ X3 @ X1) @ 
% 4.19/4.38              (k2_zfmisc_1 @ (k3_xboole_0 @ X3 @ X2) @ (k3_xboole_0 @ X1 @ X0))))),
% 4.19/4.38      inference('sup+', [status(thm)], ['19', '20'])).
% 4.19/4.38  thf('115', plain,
% 4.19/4.38      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.19/4.38         ((k4_xboole_0 @ (k2_zfmisc_1 @ (k3_xboole_0 @ X1 @ X0) @ X3) @ 
% 4.19/4.38           (k2_zfmisc_1 @ X1 @ X2))
% 4.19/4.38           = (k5_xboole_0 @ (k2_zfmisc_1 @ (k3_xboole_0 @ X1 @ X0) @ X3) @ 
% 4.19/4.38              (k2_zfmisc_1 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X3 @ X2))))),
% 4.19/4.38      inference('sup+', [status(thm)], ['113', '114'])).
% 4.19/4.38  thf('116', plain,
% 4.19/4.38      (![X0 : $i]:
% 4.19/4.38         ((k4_xboole_0 @ (k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ X0) @ sk_B) @ 
% 4.19/4.38           (k2_zfmisc_1 @ sk_A @ sk_D))
% 4.19/4.38           = (k5_xboole_0 @ (k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ X0) @ sk_B) @ 
% 4.19/4.38              (k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ X0) @ sk_B)))),
% 4.19/4.38      inference('sup+', [status(thm)], ['112', '115'])).
% 4.19/4.38  thf('117', plain, (![X14 : $i]: ((k5_xboole_0 @ X14 @ X14) = (k1_xboole_0))),
% 4.19/4.38      inference('cnf', [status(esa)], [t92_xboole_1])).
% 4.19/4.38  thf('118', plain,
% 4.19/4.38      (![X0 : $i]:
% 4.19/4.38         ((k4_xboole_0 @ (k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ X0) @ sk_B) @ 
% 4.19/4.38           (k2_zfmisc_1 @ sk_A @ sk_D)) = (k1_xboole_0))),
% 4.19/4.38      inference('demod', [status(thm)], ['116', '117'])).
% 4.19/4.38  thf('119', plain,
% 4.19/4.38      (((k4_xboole_0 @ (k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ sk_A) @ sk_B) @ 
% 4.19/4.38         (k2_zfmisc_1 @ sk_A @ sk_D)) = (k1_xboole_0))),
% 4.19/4.38      inference('sup+', [status(thm)], ['98', '118'])).
% 4.19/4.38  thf('120', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 4.19/4.38      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 4.19/4.38  thf('121', plain,
% 4.19/4.38      (![X57 : $i, X59 : $i, X60 : $i]:
% 4.19/4.38         ((k2_zfmisc_1 @ X60 @ (k4_xboole_0 @ X57 @ X59))
% 4.19/4.38           = (k4_xboole_0 @ (k2_zfmisc_1 @ X60 @ X57) @ 
% 4.19/4.38              (k2_zfmisc_1 @ X60 @ X59)))),
% 4.19/4.38      inference('cnf', [status(esa)], [t125_zfmisc_1])).
% 4.19/4.38  thf('122', plain,
% 4.19/4.38      (((k2_zfmisc_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_D)) = (k1_xboole_0))),
% 4.19/4.38      inference('demod', [status(thm)], ['119', '120', '121'])).
% 4.19/4.38  thf('123', plain,
% 4.19/4.38      (![X46 : $i, X47 : $i]:
% 4.19/4.38         (((X46) = (k1_xboole_0))
% 4.19/4.38          | ((X47) = (k1_xboole_0))
% 4.19/4.38          | ((k2_zfmisc_1 @ X47 @ X46) != (k1_xboole_0)))),
% 4.19/4.38      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 4.19/4.38  thf('124', plain,
% 4.19/4.38      ((((k1_xboole_0) != (k1_xboole_0))
% 4.19/4.38        | ((sk_A) = (k1_xboole_0))
% 4.19/4.38        | ((k4_xboole_0 @ sk_B @ sk_D) = (k1_xboole_0)))),
% 4.19/4.38      inference('sup-', [status(thm)], ['122', '123'])).
% 4.19/4.38  thf('125', plain,
% 4.19/4.38      ((((k4_xboole_0 @ sk_B @ sk_D) = (k1_xboole_0))
% 4.19/4.38        | ((sk_A) = (k1_xboole_0)))),
% 4.19/4.38      inference('simplify', [status(thm)], ['124'])).
% 4.19/4.38  thf('126', plain,
% 4.19/4.38      (![X1 : $i, X2 : $i]:
% 4.19/4.38         ((r1_tarski @ X1 @ X2) | ((k4_xboole_0 @ X1 @ X2) != (k1_xboole_0)))),
% 4.19/4.38      inference('cnf', [status(esa)], [l32_xboole_1])).
% 4.19/4.38  thf('127', plain,
% 4.19/4.38      ((((k1_xboole_0) != (k1_xboole_0))
% 4.19/4.38        | ((sk_A) = (k1_xboole_0))
% 4.19/4.38        | (r1_tarski @ sk_B @ sk_D))),
% 4.19/4.38      inference('sup-', [status(thm)], ['125', '126'])).
% 4.19/4.38  thf('128', plain, (((r1_tarski @ sk_B @ sk_D) | ((sk_A) = (k1_xboole_0)))),
% 4.19/4.38      inference('simplify', [status(thm)], ['127'])).
% 4.19/4.38  thf('129', plain,
% 4.19/4.38      ((~ (r1_tarski @ sk_B @ sk_D)) <= (~ ((r1_tarski @ sk_B @ sk_D)))),
% 4.19/4.38      inference('split', [status(esa)], ['34'])).
% 4.19/4.38  thf('130', plain,
% 4.19/4.38      ((((sk_A) = (k1_xboole_0))) <= (~ ((r1_tarski @ sk_B @ sk_D)))),
% 4.19/4.38      inference('sup-', [status(thm)], ['128', '129'])).
% 4.19/4.38  thf('131', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0))),
% 4.19/4.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.19/4.38  thf('132', plain,
% 4.19/4.38      ((((k2_zfmisc_1 @ k1_xboole_0 @ sk_B) != (k1_xboole_0)))
% 4.19/4.38         <= (~ ((r1_tarski @ sk_B @ sk_D)))),
% 4.19/4.38      inference('sup-', [status(thm)], ['130', '131'])).
% 4.19/4.38  thf('133', plain,
% 4.19/4.38      (![X48 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X48) = (k1_xboole_0))),
% 4.19/4.38      inference('simplify', [status(thm)], ['54'])).
% 4.19/4.38  thf('134', plain,
% 4.19/4.38      ((((k1_xboole_0) != (k1_xboole_0))) <= (~ ((r1_tarski @ sk_B @ sk_D)))),
% 4.19/4.38      inference('demod', [status(thm)], ['132', '133'])).
% 4.19/4.38  thf('135', plain, (((r1_tarski @ sk_B @ sk_D))),
% 4.19/4.38      inference('simplify', [status(thm)], ['134'])).
% 4.19/4.38  thf('136', plain,
% 4.19/4.38      (~ ((r1_tarski @ sk_A @ sk_C)) | ~ ((r1_tarski @ sk_B @ sk_D))),
% 4.19/4.38      inference('split', [status(esa)], ['34'])).
% 4.19/4.38  thf('137', plain, (~ ((r1_tarski @ sk_A @ sk_C))),
% 4.19/4.38      inference('sat_resolution*', [status(thm)], ['135', '136'])).
% 4.19/4.38  thf('138', plain, (~ (r1_tarski @ sk_A @ sk_C)),
% 4.19/4.38      inference('simpl_trail', [status(thm)], ['35', '137'])).
% 4.19/4.38  thf('139', plain, (((sk_B) = (k1_xboole_0))),
% 4.19/4.38      inference('clc', [status(thm)], ['33', '138'])).
% 4.19/4.38  thf('140', plain,
% 4.19/4.38      (![X47 : $i, X48 : $i]:
% 4.19/4.38         (((k2_zfmisc_1 @ X47 @ X48) = (k1_xboole_0))
% 4.19/4.38          | ((X48) != (k1_xboole_0)))),
% 4.19/4.38      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 4.19/4.38  thf('141', plain,
% 4.19/4.38      (![X47 : $i]: ((k2_zfmisc_1 @ X47 @ k1_xboole_0) = (k1_xboole_0))),
% 4.19/4.38      inference('simplify', [status(thm)], ['140'])).
% 4.19/4.38  thf('142', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 4.19/4.38      inference('demod', [status(thm)], ['0', '139', '141'])).
% 4.19/4.38  thf('143', plain, ($false), inference('simplify', [status(thm)], ['142'])).
% 4.19/4.38  
% 4.19/4.38  % SZS output end Refutation
% 4.19/4.38  
% 4.19/4.39  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
