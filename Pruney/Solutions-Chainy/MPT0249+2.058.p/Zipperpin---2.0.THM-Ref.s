%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KzzdLbA3nn

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:46 EST 2020

% Result     : Theorem 0.49s
% Output     : Refutation 0.49s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 493 expanded)
%              Number of leaves         :   21 ( 169 expanded)
%              Depth                    :   23
%              Number of atoms          :  746 (3740 expanded)
%              Number of equality atoms :  112 ( 563 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t44_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) )
        & ( B != C )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( ( k1_tarski @ A )
            = ( k2_xboole_0 @ B @ C ) )
          & ( B != C )
          & ( B != k1_xboole_0 )
          & ( C != k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t44_zfmisc_1])).

thf('0',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ X9 @ ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('3',plain,(
    r1_tarski @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('4',plain,(
    ! [X44: $i,X45: $i] :
      ( ( X45
        = ( k1_tarski @ X44 ) )
      | ( X45 = k1_xboole_0 )
      | ~ ( r1_tarski @ X45 @ ( k1_tarski @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('5',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( sk_B
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['5','6'])).

thf('8',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['0','7'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k4_xboole_0 @ X6 @ X7 ) )
      = ( k3_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('10',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X4 @ X5 ) @ X4 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,
    ( sk_B
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['5','6'])).

thf('13',plain,(
    ! [X44: $i,X45: $i] :
      ( ( X45
        = ( k1_tarski @ X44 ) )
      | ( X45 = k1_xboole_0 )
      | ~ ( r1_tarski @ X45 @ ( k1_tarski @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( sk_B
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['5','6'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( X0 = k1_xboole_0 )
      | ( X0 = sk_B ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_B @ X0 )
        = sk_B )
      | ( ( k3_xboole_0 @ sk_B @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('18',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ sk_B @ X0 )
        = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) )
      | ( ( k3_xboole_0 @ sk_B @ X0 )
        = sk_B ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('20',plain,(
    ! [X8: $i] :
      ( ( k5_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ sk_B @ X0 )
        = sk_B )
      | ( ( k3_xboole_0 @ sk_B @ X0 )
        = sk_B ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('22',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X14 @ X15 ) @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('23',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k5_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('24',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k5_xboole_0 @ X15 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( ( k2_xboole_0 @ sk_B @ X0 )
        = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ X0 @ sk_B ) ) )
      | ( ( k4_xboole_0 @ sk_B @ X0 )
        = sk_B ) ) ),
    inference('sup+',[status(thm)],['21','24'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('27',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k5_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('31',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('32',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X8: $i] :
      ( ( k5_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k4_xboole_0 @ X6 @ X7 ) )
      = ( k3_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['30','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ sk_B @ X0 ) ) )
      | ( ( k4_xboole_0 @ sk_B @ X0 )
        = sk_B ) ) ),
    inference('sup+',[status(thm)],['25','40'])).

thf('42',plain,
    ( ( k1_xboole_0
      = ( k5_xboole_0 @ sk_C @ sk_B ) )
    | ( ( k4_xboole_0 @ sk_B @ sk_C )
      = sk_B ) ),
    inference('sup+',[status(thm)],['8','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('44',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k5_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X1 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k5_xboole_0 @ X15 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ ( k3_xboole_0 @ X0 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('53',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('54',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k5_xboole_0 @ X15 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('57',plain,(
    ! [X8: $i] :
      ( ( k5_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['55','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['51','52','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      = X1 ) ),
    inference('sup+',[status(thm)],['48','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['45','61'])).

thf('63',plain,
    ( ( sk_B
      = ( k5_xboole_0 @ sk_C @ k1_xboole_0 ) )
    | ( ( k4_xboole_0 @ sk_B @ sk_C )
      = sk_B ) ),
    inference('sup+',[status(thm)],['42','62'])).

thf('64',plain,(
    ! [X8: $i] :
      ( ( k5_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('65',plain,
    ( ( sk_B = sk_C )
    | ( ( k4_xboole_0 @ sk_B @ sk_C )
      = sk_B ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    sk_B != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_C )
    = sk_B ),
    inference('simplify_reflect-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k4_xboole_0 @ X6 @ X7 ) )
      = ( k3_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('69',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_B )
    = ( k3_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('71',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k5_xboole_0 @ X15 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('73',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_C )
    = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_C @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['0','7'])).

thf('75',plain,(
    ! [X8: $i] :
      ( ( k5_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('76',plain,
    ( sk_B
    = ( k5_xboole_0 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['73','74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['45','61'])).

thf('78',plain,
    ( sk_C
    = ( k5_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      = X1 ) ),
    inference('sup+',[status(thm)],['48','60'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['30','39'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      = X1 ) ),
    inference('sup+',[status(thm)],['48','60'])).

thf('83',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    sk_C = k1_xboole_0 ),
    inference(demod,[status(thm)],['78','83'])).

thf('85',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['84','85'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KzzdLbA3nn
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:55:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.49/0.66  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.49/0.66  % Solved by: fo/fo7.sh
% 0.49/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.49/0.66  % done 466 iterations in 0.195s
% 0.49/0.66  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.49/0.66  % SZS output start Refutation
% 0.49/0.66  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.49/0.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.49/0.66  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.49/0.66  thf(sk_C_type, type, sk_C: $i).
% 0.49/0.66  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.49/0.66  thf(sk_B_type, type, sk_B: $i).
% 0.49/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.49/0.66  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.49/0.66  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.49/0.66  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.49/0.66  thf(t44_zfmisc_1, conjecture,
% 0.49/0.66    (![A:$i,B:$i,C:$i]:
% 0.49/0.66     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.49/0.66          ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.49/0.66          ( ( C ) != ( k1_xboole_0 ) ) ) ))).
% 0.49/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.49/0.66    (~( ![A:$i,B:$i,C:$i]:
% 0.49/0.66        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.49/0.66             ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.49/0.66             ( ( C ) != ( k1_xboole_0 ) ) ) ) )),
% 0.49/0.66    inference('cnf.neg', [status(esa)], [t44_zfmisc_1])).
% 0.49/0.66  thf('0', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.49/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.66  thf('1', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.49/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.66  thf(t7_xboole_1, axiom,
% 0.49/0.66    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.49/0.66  thf('2', plain,
% 0.49/0.66      (![X9 : $i, X10 : $i]: (r1_tarski @ X9 @ (k2_xboole_0 @ X9 @ X10))),
% 0.49/0.66      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.49/0.66  thf('3', plain, ((r1_tarski @ sk_B @ (k1_tarski @ sk_A))),
% 0.49/0.66      inference('sup+', [status(thm)], ['1', '2'])).
% 0.49/0.66  thf(l3_zfmisc_1, axiom,
% 0.49/0.66    (![A:$i,B:$i]:
% 0.49/0.66     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.49/0.66       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.49/0.66  thf('4', plain,
% 0.49/0.66      (![X44 : $i, X45 : $i]:
% 0.49/0.66         (((X45) = (k1_tarski @ X44))
% 0.49/0.66          | ((X45) = (k1_xboole_0))
% 0.49/0.66          | ~ (r1_tarski @ X45 @ (k1_tarski @ X44)))),
% 0.49/0.66      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.49/0.66  thf('5', plain, ((((sk_B) = (k1_xboole_0)) | ((sk_B) = (k1_tarski @ sk_A)))),
% 0.49/0.66      inference('sup-', [status(thm)], ['3', '4'])).
% 0.49/0.66  thf('6', plain, (((sk_B) != (k1_xboole_0))),
% 0.49/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.66  thf('7', plain, (((sk_B) = (k1_tarski @ sk_A))),
% 0.49/0.66      inference('simplify_reflect-', [status(thm)], ['5', '6'])).
% 0.49/0.66  thf('8', plain, (((sk_B) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.49/0.66      inference('demod', [status(thm)], ['0', '7'])).
% 0.49/0.66  thf(t48_xboole_1, axiom,
% 0.49/0.66    (![A:$i,B:$i]:
% 0.49/0.66     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.49/0.66  thf('9', plain,
% 0.49/0.66      (![X6 : $i, X7 : $i]:
% 0.49/0.66         ((k4_xboole_0 @ X6 @ (k4_xboole_0 @ X6 @ X7))
% 0.49/0.66           = (k3_xboole_0 @ X6 @ X7))),
% 0.49/0.66      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.49/0.66  thf(t36_xboole_1, axiom,
% 0.49/0.66    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.49/0.66  thf('10', plain,
% 0.49/0.66      (![X4 : $i, X5 : $i]: (r1_tarski @ (k4_xboole_0 @ X4 @ X5) @ X4)),
% 0.49/0.66      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.49/0.66  thf('11', plain,
% 0.49/0.66      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.49/0.66      inference('sup+', [status(thm)], ['9', '10'])).
% 0.49/0.66  thf('12', plain, (((sk_B) = (k1_tarski @ sk_A))),
% 0.49/0.66      inference('simplify_reflect-', [status(thm)], ['5', '6'])).
% 0.49/0.66  thf('13', plain,
% 0.49/0.66      (![X44 : $i, X45 : $i]:
% 0.49/0.66         (((X45) = (k1_tarski @ X44))
% 0.49/0.66          | ((X45) = (k1_xboole_0))
% 0.49/0.66          | ~ (r1_tarski @ X45 @ (k1_tarski @ X44)))),
% 0.49/0.66      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.49/0.66  thf('14', plain,
% 0.49/0.66      (![X0 : $i]:
% 0.49/0.66         (~ (r1_tarski @ X0 @ sk_B)
% 0.49/0.66          | ((X0) = (k1_xboole_0))
% 0.49/0.66          | ((X0) = (k1_tarski @ sk_A)))),
% 0.49/0.66      inference('sup-', [status(thm)], ['12', '13'])).
% 0.49/0.66  thf('15', plain, (((sk_B) = (k1_tarski @ sk_A))),
% 0.49/0.66      inference('simplify_reflect-', [status(thm)], ['5', '6'])).
% 0.49/0.66  thf('16', plain,
% 0.49/0.66      (![X0 : $i]:
% 0.49/0.66         (~ (r1_tarski @ X0 @ sk_B) | ((X0) = (k1_xboole_0)) | ((X0) = (sk_B)))),
% 0.49/0.66      inference('demod', [status(thm)], ['14', '15'])).
% 0.49/0.66  thf('17', plain,
% 0.49/0.66      (![X0 : $i]:
% 0.49/0.66         (((k3_xboole_0 @ sk_B @ X0) = (sk_B))
% 0.49/0.66          | ((k3_xboole_0 @ sk_B @ X0) = (k1_xboole_0)))),
% 0.49/0.66      inference('sup-', [status(thm)], ['11', '16'])).
% 0.49/0.66  thf(t100_xboole_1, axiom,
% 0.49/0.66    (![A:$i,B:$i]:
% 0.49/0.66     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.49/0.66  thf('18', plain,
% 0.49/0.66      (![X1 : $i, X2 : $i]:
% 0.49/0.66         ((k4_xboole_0 @ X1 @ X2)
% 0.49/0.66           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.49/0.66      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.49/0.66  thf('19', plain,
% 0.49/0.66      (![X0 : $i]:
% 0.49/0.66         (((k4_xboole_0 @ sk_B @ X0) = (k5_xboole_0 @ sk_B @ k1_xboole_0))
% 0.49/0.66          | ((k3_xboole_0 @ sk_B @ X0) = (sk_B)))),
% 0.49/0.66      inference('sup+', [status(thm)], ['17', '18'])).
% 0.49/0.66  thf(t5_boole, axiom,
% 0.49/0.66    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.49/0.66  thf('20', plain, (![X8 : $i]: ((k5_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.49/0.66      inference('cnf', [status(esa)], [t5_boole])).
% 0.49/0.66  thf('21', plain,
% 0.49/0.66      (![X0 : $i]:
% 0.49/0.66         (((k4_xboole_0 @ sk_B @ X0) = (sk_B))
% 0.49/0.66          | ((k3_xboole_0 @ sk_B @ X0) = (sk_B)))),
% 0.49/0.66      inference('demod', [status(thm)], ['19', '20'])).
% 0.49/0.66  thf(t94_xboole_1, axiom,
% 0.49/0.66    (![A:$i,B:$i]:
% 0.49/0.66     ( ( k2_xboole_0 @ A @ B ) =
% 0.49/0.66       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.49/0.66  thf('22', plain,
% 0.49/0.66      (![X14 : $i, X15 : $i]:
% 0.49/0.66         ((k2_xboole_0 @ X14 @ X15)
% 0.49/0.66           = (k5_xboole_0 @ (k5_xboole_0 @ X14 @ X15) @ 
% 0.49/0.66              (k3_xboole_0 @ X14 @ X15)))),
% 0.49/0.66      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.49/0.66  thf(t91_xboole_1, axiom,
% 0.49/0.66    (![A:$i,B:$i,C:$i]:
% 0.49/0.66     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.49/0.66       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.49/0.66  thf('23', plain,
% 0.49/0.66      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.49/0.66         ((k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ X13)
% 0.49/0.66           = (k5_xboole_0 @ X11 @ (k5_xboole_0 @ X12 @ X13)))),
% 0.49/0.66      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.49/0.66  thf('24', plain,
% 0.49/0.66      (![X14 : $i, X15 : $i]:
% 0.49/0.66         ((k2_xboole_0 @ X14 @ X15)
% 0.49/0.66           = (k5_xboole_0 @ X14 @ 
% 0.49/0.66              (k5_xboole_0 @ X15 @ (k3_xboole_0 @ X14 @ X15))))),
% 0.49/0.66      inference('demod', [status(thm)], ['22', '23'])).
% 0.49/0.66  thf('25', plain,
% 0.49/0.66      (![X0 : $i]:
% 0.49/0.66         (((k2_xboole_0 @ sk_B @ X0)
% 0.49/0.66            = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ X0 @ sk_B)))
% 0.49/0.66          | ((k4_xboole_0 @ sk_B @ X0) = (sk_B)))),
% 0.49/0.66      inference('sup+', [status(thm)], ['21', '24'])).
% 0.49/0.66  thf(idempotence_k3_xboole_0, axiom,
% 0.49/0.66    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.49/0.66  thf('26', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.49/0.66      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.49/0.66  thf('27', plain,
% 0.49/0.66      (![X1 : $i, X2 : $i]:
% 0.49/0.66         ((k4_xboole_0 @ X1 @ X2)
% 0.49/0.66           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.49/0.66      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.49/0.66  thf('28', plain,
% 0.49/0.66      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.49/0.66      inference('sup+', [status(thm)], ['26', '27'])).
% 0.49/0.66  thf('29', plain,
% 0.49/0.66      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.49/0.66         ((k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ X13)
% 0.49/0.66           = (k5_xboole_0 @ X11 @ (k5_xboole_0 @ X12 @ X13)))),
% 0.49/0.66      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.49/0.66  thf('30', plain,
% 0.49/0.66      (![X0 : $i, X1 : $i]:
% 0.49/0.66         ((k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 0.49/0.66           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))))),
% 0.49/0.66      inference('sup+', [status(thm)], ['28', '29'])).
% 0.49/0.66  thf(t2_boole, axiom,
% 0.49/0.66    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.49/0.66  thf('31', plain,
% 0.49/0.66      (![X3 : $i]: ((k3_xboole_0 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 0.49/0.66      inference('cnf', [status(esa)], [t2_boole])).
% 0.49/0.66  thf('32', plain,
% 0.49/0.66      (![X1 : $i, X2 : $i]:
% 0.49/0.66         ((k4_xboole_0 @ X1 @ X2)
% 0.49/0.66           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.49/0.66      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.49/0.66  thf('33', plain,
% 0.49/0.66      (![X0 : $i]:
% 0.49/0.66         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.49/0.66      inference('sup+', [status(thm)], ['31', '32'])).
% 0.49/0.66  thf('34', plain, (![X8 : $i]: ((k5_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.49/0.66      inference('cnf', [status(esa)], [t5_boole])).
% 0.49/0.66  thf('35', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.49/0.66      inference('sup+', [status(thm)], ['33', '34'])).
% 0.49/0.66  thf('36', plain,
% 0.49/0.66      (![X6 : $i, X7 : $i]:
% 0.49/0.66         ((k4_xboole_0 @ X6 @ (k4_xboole_0 @ X6 @ X7))
% 0.49/0.66           = (k3_xboole_0 @ X6 @ X7))),
% 0.49/0.66      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.49/0.66  thf('37', plain,
% 0.49/0.66      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.49/0.66      inference('sup+', [status(thm)], ['35', '36'])).
% 0.49/0.66  thf('38', plain,
% 0.49/0.66      (![X3 : $i]: ((k3_xboole_0 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 0.49/0.66      inference('cnf', [status(esa)], [t2_boole])).
% 0.49/0.66  thf('39', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.49/0.66      inference('demod', [status(thm)], ['37', '38'])).
% 0.49/0.66  thf('40', plain,
% 0.49/0.66      (![X0 : $i, X1 : $i]:
% 0.49/0.66         ((k1_xboole_0)
% 0.49/0.66           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))))),
% 0.49/0.66      inference('demod', [status(thm)], ['30', '39'])).
% 0.49/0.66  thf('41', plain,
% 0.49/0.66      (![X0 : $i]:
% 0.49/0.66         (((k1_xboole_0) = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ sk_B @ X0)))
% 0.49/0.66          | ((k4_xboole_0 @ sk_B @ X0) = (sk_B)))),
% 0.49/0.66      inference('sup+', [status(thm)], ['25', '40'])).
% 0.49/0.66  thf('42', plain,
% 0.49/0.66      ((((k1_xboole_0) = (k5_xboole_0 @ sk_C @ sk_B))
% 0.49/0.66        | ((k4_xboole_0 @ sk_B @ sk_C) = (sk_B)))),
% 0.49/0.66      inference('sup+', [status(thm)], ['8', '41'])).
% 0.49/0.66  thf('43', plain,
% 0.49/0.66      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.49/0.66      inference('sup+', [status(thm)], ['26', '27'])).
% 0.49/0.66  thf('44', plain,
% 0.49/0.66      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.49/0.66         ((k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ X13)
% 0.49/0.66           = (k5_xboole_0 @ X11 @ (k5_xboole_0 @ X12 @ X13)))),
% 0.49/0.66      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.49/0.66  thf('45', plain,
% 0.49/0.66      (![X0 : $i, X1 : $i]:
% 0.49/0.66         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1)
% 0.49/0.66           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 0.49/0.66      inference('sup+', [status(thm)], ['43', '44'])).
% 0.49/0.66  thf('46', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.49/0.66      inference('demod', [status(thm)], ['37', '38'])).
% 0.49/0.66  thf('47', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.49/0.66      inference('demod', [status(thm)], ['37', '38'])).
% 0.49/0.66  thf('48', plain,
% 0.49/0.66      (![X0 : $i, X1 : $i]: ((k4_xboole_0 @ X1 @ X1) = (k4_xboole_0 @ X0 @ X0))),
% 0.49/0.66      inference('sup+', [status(thm)], ['46', '47'])).
% 0.49/0.66  thf('49', plain,
% 0.49/0.66      (![X14 : $i, X15 : $i]:
% 0.49/0.66         ((k2_xboole_0 @ X14 @ X15)
% 0.49/0.66           = (k5_xboole_0 @ X14 @ 
% 0.49/0.66              (k5_xboole_0 @ X15 @ (k3_xboole_0 @ X14 @ X15))))),
% 0.49/0.66      inference('demod', [status(thm)], ['22', '23'])).
% 0.49/0.66  thf('50', plain,
% 0.49/0.66      (![X0 : $i, X1 : $i]:
% 0.49/0.66         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1)
% 0.49/0.66           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 0.49/0.66      inference('sup+', [status(thm)], ['43', '44'])).
% 0.49/0.66  thf('51', plain,
% 0.49/0.66      (![X0 : $i]:
% 0.49/0.66         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ (k3_xboole_0 @ X0 @ X0))
% 0.49/0.66           = (k2_xboole_0 @ X0 @ X0))),
% 0.49/0.66      inference('sup+', [status(thm)], ['49', '50'])).
% 0.49/0.66  thf('52', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.49/0.66      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.49/0.66  thf('53', plain,
% 0.49/0.66      (![X1 : $i, X2 : $i]:
% 0.49/0.66         ((k4_xboole_0 @ X1 @ X2)
% 0.49/0.66           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.49/0.66      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.49/0.66  thf('54', plain,
% 0.49/0.66      (![X14 : $i, X15 : $i]:
% 0.49/0.66         ((k2_xboole_0 @ X14 @ X15)
% 0.49/0.66           = (k5_xboole_0 @ X14 @ 
% 0.49/0.66              (k5_xboole_0 @ X15 @ (k3_xboole_0 @ X14 @ X15))))),
% 0.49/0.66      inference('demod', [status(thm)], ['22', '23'])).
% 0.49/0.66  thf('55', plain,
% 0.49/0.66      (![X0 : $i]:
% 0.49/0.66         ((k2_xboole_0 @ X0 @ X0)
% 0.49/0.66           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.49/0.66      inference('sup+', [status(thm)], ['53', '54'])).
% 0.49/0.66  thf('56', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.49/0.66      inference('demod', [status(thm)], ['37', '38'])).
% 0.49/0.66  thf('57', plain, (![X8 : $i]: ((k5_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.49/0.66      inference('cnf', [status(esa)], [t5_boole])).
% 0.49/0.66  thf('58', plain,
% 0.49/0.66      (![X0 : $i, X1 : $i]:
% 0.49/0.66         ((k5_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0)) = (X1))),
% 0.49/0.66      inference('sup+', [status(thm)], ['56', '57'])).
% 0.49/0.66  thf('59', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.49/0.66      inference('demod', [status(thm)], ['55', '58'])).
% 0.49/0.66  thf('60', plain,
% 0.49/0.66      (![X0 : $i]: ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X0) = (X0))),
% 0.49/0.66      inference('demod', [status(thm)], ['51', '52', '59'])).
% 0.49/0.66  thf('61', plain,
% 0.49/0.66      (![X0 : $i, X1 : $i]:
% 0.49/0.66         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1) = (X1))),
% 0.49/0.66      inference('sup+', [status(thm)], ['48', '60'])).
% 0.49/0.66  thf('62', plain,
% 0.49/0.66      (![X0 : $i, X1 : $i]:
% 0.49/0.66         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 0.49/0.66      inference('demod', [status(thm)], ['45', '61'])).
% 0.49/0.66  thf('63', plain,
% 0.49/0.66      ((((sk_B) = (k5_xboole_0 @ sk_C @ k1_xboole_0))
% 0.49/0.66        | ((k4_xboole_0 @ sk_B @ sk_C) = (sk_B)))),
% 0.49/0.66      inference('sup+', [status(thm)], ['42', '62'])).
% 0.49/0.66  thf('64', plain, (![X8 : $i]: ((k5_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.49/0.66      inference('cnf', [status(esa)], [t5_boole])).
% 0.49/0.66  thf('65', plain,
% 0.49/0.66      ((((sk_B) = (sk_C)) | ((k4_xboole_0 @ sk_B @ sk_C) = (sk_B)))),
% 0.49/0.66      inference('demod', [status(thm)], ['63', '64'])).
% 0.49/0.66  thf('66', plain, (((sk_B) != (sk_C))),
% 0.49/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.66  thf('67', plain, (((k4_xboole_0 @ sk_B @ sk_C) = (sk_B))),
% 0.49/0.66      inference('simplify_reflect-', [status(thm)], ['65', '66'])).
% 0.49/0.66  thf('68', plain,
% 0.49/0.66      (![X6 : $i, X7 : $i]:
% 0.49/0.66         ((k4_xboole_0 @ X6 @ (k4_xboole_0 @ X6 @ X7))
% 0.49/0.66           = (k3_xboole_0 @ X6 @ X7))),
% 0.49/0.66      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.49/0.66  thf('69', plain,
% 0.49/0.66      (((k4_xboole_0 @ sk_B @ sk_B) = (k3_xboole_0 @ sk_B @ sk_C))),
% 0.49/0.66      inference('sup+', [status(thm)], ['67', '68'])).
% 0.49/0.66  thf('70', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.49/0.66      inference('demod', [status(thm)], ['37', '38'])).
% 0.49/0.66  thf('71', plain, (((k1_xboole_0) = (k3_xboole_0 @ sk_B @ sk_C))),
% 0.49/0.66      inference('demod', [status(thm)], ['69', '70'])).
% 0.49/0.66  thf('72', plain,
% 0.49/0.66      (![X14 : $i, X15 : $i]:
% 0.49/0.66         ((k2_xboole_0 @ X14 @ X15)
% 0.49/0.66           = (k5_xboole_0 @ X14 @ 
% 0.49/0.66              (k5_xboole_0 @ X15 @ (k3_xboole_0 @ X14 @ X15))))),
% 0.49/0.66      inference('demod', [status(thm)], ['22', '23'])).
% 0.49/0.66  thf('73', plain,
% 0.49/0.66      (((k2_xboole_0 @ sk_B @ sk_C)
% 0.49/0.66         = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_C @ k1_xboole_0)))),
% 0.49/0.66      inference('sup+', [status(thm)], ['71', '72'])).
% 0.49/0.66  thf('74', plain, (((sk_B) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.49/0.66      inference('demod', [status(thm)], ['0', '7'])).
% 0.49/0.66  thf('75', plain, (![X8 : $i]: ((k5_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.49/0.66      inference('cnf', [status(esa)], [t5_boole])).
% 0.49/0.66  thf('76', plain, (((sk_B) = (k5_xboole_0 @ sk_B @ sk_C))),
% 0.49/0.66      inference('demod', [status(thm)], ['73', '74', '75'])).
% 0.49/0.66  thf('77', plain,
% 0.49/0.66      (![X0 : $i, X1 : $i]:
% 0.49/0.66         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 0.49/0.66      inference('demod', [status(thm)], ['45', '61'])).
% 0.49/0.66  thf('78', plain, (((sk_C) = (k5_xboole_0 @ sk_B @ sk_B))),
% 0.49/0.66      inference('sup+', [status(thm)], ['76', '77'])).
% 0.49/0.66  thf('79', plain,
% 0.49/0.66      (![X0 : $i, X1 : $i]:
% 0.49/0.66         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1) = (X1))),
% 0.49/0.66      inference('sup+', [status(thm)], ['48', '60'])).
% 0.49/0.66  thf('80', plain,
% 0.49/0.66      (![X0 : $i, X1 : $i]:
% 0.49/0.66         ((k1_xboole_0)
% 0.49/0.66           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))))),
% 0.49/0.66      inference('demod', [status(thm)], ['30', '39'])).
% 0.49/0.66  thf('81', plain,
% 0.49/0.66      (![X0 : $i, X1 : $i]:
% 0.49/0.66         ((k1_xboole_0)
% 0.49/0.66           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X1) @ X0)))),
% 0.49/0.66      inference('sup+', [status(thm)], ['79', '80'])).
% 0.49/0.66  thf('82', plain,
% 0.49/0.66      (![X0 : $i, X1 : $i]:
% 0.49/0.66         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1) = (X1))),
% 0.49/0.66      inference('sup+', [status(thm)], ['48', '60'])).
% 0.49/0.66  thf('83', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.49/0.66      inference('demod', [status(thm)], ['81', '82'])).
% 0.49/0.66  thf('84', plain, (((sk_C) = (k1_xboole_0))),
% 0.49/0.66      inference('demod', [status(thm)], ['78', '83'])).
% 0.49/0.66  thf('85', plain, (((sk_C) != (k1_xboole_0))),
% 0.49/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.66  thf('86', plain, ($false),
% 0.49/0.66      inference('simplify_reflect-', [status(thm)], ['84', '85'])).
% 0.49/0.66  
% 0.49/0.66  % SZS output end Refutation
% 0.49/0.66  
% 0.49/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
