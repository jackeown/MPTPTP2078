%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8rmSDVEUVR

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:55 EST 2020

% Result     : Theorem 1.07s
% Output     : Refutation 1.07s
% Verified   : 
% Statistics : Number of formulae       :  159 (1300 expanded)
%              Number of leaves         :   26 ( 446 expanded)
%              Depth                    :   35
%              Number of atoms          : 1299 (9607 expanded)
%              Number of equality atoms :  140 (1279 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t45_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B )
     => ( r2_hidden @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B )
       => ( r2_hidden @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t45_zfmisc_1])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('1',plain,(
    ! [X13: $i] :
      ( ( k3_xboole_0 @ X13 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('4',plain,(
    ! [X18: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X18 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X65: $i,X66: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X65 @ X66 ) )
      = ( k2_xboole_0 @ X65 @ X66 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('7',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X19 @ X20 ) )
      = ( k5_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X19 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X0 @ k1_xboole_0 ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('9',plain,(
    ! [X12: $i] :
      ( ( k2_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('10',plain,(
    ! [X65: $i,X66: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X65 @ X66 ) )
      = ( k2_xboole_0 @ X65 @ X66 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('11',plain,(
    ! [X12: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X12 @ k1_xboole_0 ) )
      = X12 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['3','12'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('14',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X13: $i] :
      ( ( k3_xboole_0 @ X13 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['3','12'])).

thf('21',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf(t112_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ A @ C ) @ B ) ) )).

thf('22',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X6 @ X8 ) @ ( k3_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X6 @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t112_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('27',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['25','28'])).

thf(t101_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('30',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X4 @ X5 ) @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t101_xboole_1])).

thf('31',plain,(
    ! [X65: $i,X66: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X65 @ X66 ) )
      = ( k2_xboole_0 @ X65 @ X66 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('32',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k4_xboole_0 @ ( k3_tarski @ ( k2_tarski @ X4 @ X5 ) ) @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('34',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k3_xboole_0 @ X9 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('41',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['39','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('45',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X65: $i,X66: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X65 @ X66 ) )
      = ( k2_xboole_0 @ X65 @ X66 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('47',plain,(
    r1_tarski @ ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ sk_A ) @ sk_B ) ) @ sk_B ),
    inference(demod,[status(thm)],['45','46'])).

thf(t45_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( B
        = ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) ) )).

thf('48',plain,(
    ! [X14: $i,X15: $i] :
      ( ( X15
        = ( k2_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) ) )
      | ~ ( r1_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t45_xboole_1])).

thf('49',plain,(
    ! [X65: $i,X66: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X65 @ X66 ) )
      = ( k2_xboole_0 @ X65 @ X66 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('50',plain,(
    ! [X14: $i,X15: $i] :
      ( ( X15
        = ( k3_tarski @ ( k2_tarski @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) ) ) )
      | ~ ( r1_tarski @ X14 @ X15 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( sk_B
    = ( k3_tarski @ ( k2_tarski @ ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ sk_A ) @ sk_B ) ) @ ( k4_xboole_0 @ sk_B @ ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ sk_A ) @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k4_xboole_0 @ ( k3_tarski @ ( k2_tarski @ X4 @ X5 ) ) @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('53',plain,
    ( ( k5_xboole_0 @ ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ sk_A ) @ sk_B ) ) @ ( k4_xboole_0 @ sk_B @ ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ sk_A ) @ sk_B ) ) ) )
    = ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ sk_A ) @ sk_B ) ) @ ( k4_xboole_0 @ sk_B @ ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ sk_A ) @ sk_B ) ) ) ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X19 @ X20 ) )
      = ( k5_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X19 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('55',plain,
    ( ( k3_tarski @ ( k2_tarski @ ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ sk_A ) @ sk_B ) ) @ sk_B ) )
    = ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ sk_A ) @ sk_B ) ) @ ( k4_xboole_0 @ sk_B @ ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ sk_A ) @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('58',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X6 @ X8 ) @ ( k3_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X6 @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t112_xboole_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['56','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X6 @ X8 ) @ ( k3_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X6 @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t112_xboole_1])).

thf('65',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('66',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['63','64','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('72',plain,(
    ! [X13: $i] :
      ( ( k3_xboole_0 @ X13 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['70','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['60','74','75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['3','12'])).

thf('79',plain,
    ( ( k3_tarski @ ( k2_tarski @ ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ sk_A ) @ sk_B ) ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['55','77','78'])).

thf('80',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k4_xboole_0 @ ( k3_tarski @ ( k2_tarski @ X4 @ X5 ) ) @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('81',plain,
    ( ( k5_xboole_0 @ ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ sk_A ) @ sk_B ) ) @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ sk_A ) @ sk_B ) ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('84',plain,
    ( ( k5_xboole_0 @ ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ sk_A ) @ sk_B ) ) @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['81','82','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['60','74','75','76'])).

thf('86',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ sk_A ) @ sk_B ) ) @ ( k5_xboole_0 @ ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ sk_A ) @ sk_B ) ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['25','28'])).

thf('88',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ sk_A ) @ sk_B ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('90',plain,
    ( ( k4_xboole_0 @ ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ sk_A ) @ sk_B ) ) @ k1_xboole_0 )
    = ( k3_xboole_0 @ ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ sk_A ) @ sk_B ) ) @ sk_B ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['3','12'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('93',plain,
    ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ sk_A ) @ sk_B ) )
    = ( k3_xboole_0 @ sk_B @ ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['90','91','92'])).

thf('94',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k3_xboole_0 @ X9 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('96',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['70','73'])).

thf('98',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ sk_A ) @ sk_B ) ) ) @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['93','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ sk_A ) @ sk_B ) ) @ X0 ) @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['44','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ sk_A ) @ sk_B ) ) @ X0 ) @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['43','100'])).

thf('102',plain,
    ( ( k4_xboole_0 @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ sk_B )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['32','101'])).

thf('103',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('104',plain,
    ( ( k4_xboole_0 @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ k1_xboole_0 )
    = ( k3_xboole_0 @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ sk_B ) ),
    inference('sup+',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['3','12'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('107',plain,
    ( ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k3_xboole_0 @ sk_B @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['104','105','106'])).

thf('108',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['107','108'])).

thf('110',plain,
    ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ sk_B )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['29','109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['60','74','75','76'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['111','118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['3','12'])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['110','121'])).

thf('123',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('124',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 )
    = ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['3','12'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('127',plain,
    ( ( k1_tarski @ sk_A )
    = ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['124','125','126'])).

thf(l29_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k3_xboole_0 @ A @ ( k1_tarski @ B ) )
        = ( k1_tarski @ B ) )
     => ( r2_hidden @ B @ A ) ) )).

thf('128',plain,(
    ! [X63: $i,X64: $i] :
      ( ( r2_hidden @ X63 @ X64 )
      | ( ( k3_xboole_0 @ X64 @ ( k1_tarski @ X63 ) )
       != ( k1_tarski @ X63 ) ) ) ),
    inference(cnf,[status(esa)],[l29_zfmisc_1])).

thf('129',plain,
    ( ( ( k1_tarski @ sk_A )
     != ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['129'])).

thf('131',plain,(
    $false ),
    inference(demod,[status(thm)],['0','130'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8rmSDVEUVR
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:16:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 1.07/1.28  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.07/1.28  % Solved by: fo/fo7.sh
% 1.07/1.28  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.07/1.28  % done 1240 iterations in 0.833s
% 1.07/1.28  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.07/1.28  % SZS output start Refutation
% 1.07/1.28  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.07/1.28  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.07/1.28  thf(sk_A_type, type, sk_A: $i).
% 1.07/1.28  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.07/1.28  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.07/1.28  thf(sk_B_type, type, sk_B: $i).
% 1.07/1.28  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.07/1.28  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.07/1.28  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 1.07/1.28  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.07/1.28  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.07/1.28  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.07/1.28  thf(t45_zfmisc_1, conjecture,
% 1.07/1.28    (![A:$i,B:$i]:
% 1.07/1.28     ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B ) =>
% 1.07/1.28       ( r2_hidden @ A @ B ) ))).
% 1.07/1.28  thf(zf_stmt_0, negated_conjecture,
% 1.07/1.28    (~( ![A:$i,B:$i]:
% 1.07/1.28        ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B ) =>
% 1.07/1.28          ( r2_hidden @ A @ B ) ) )),
% 1.07/1.28    inference('cnf.neg', [status(esa)], [t45_zfmisc_1])).
% 1.07/1.28  thf('0', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 1.07/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.28  thf(t2_boole, axiom,
% 1.07/1.28    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 1.07/1.28  thf('1', plain,
% 1.07/1.28      (![X13 : $i]: ((k3_xboole_0 @ X13 @ k1_xboole_0) = (k1_xboole_0))),
% 1.07/1.28      inference('cnf', [status(esa)], [t2_boole])).
% 1.07/1.28  thf(t100_xboole_1, axiom,
% 1.07/1.28    (![A:$i,B:$i]:
% 1.07/1.28     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.07/1.28  thf('2', plain,
% 1.07/1.28      (![X2 : $i, X3 : $i]:
% 1.07/1.28         ((k4_xboole_0 @ X2 @ X3)
% 1.07/1.28           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 1.07/1.28      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.07/1.28  thf('3', plain,
% 1.07/1.28      (![X0 : $i]:
% 1.07/1.28         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.07/1.28      inference('sup+', [status(thm)], ['1', '2'])).
% 1.07/1.28  thf(t4_boole, axiom,
% 1.07/1.28    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 1.07/1.28  thf('4', plain,
% 1.07/1.28      (![X18 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X18) = (k1_xboole_0))),
% 1.07/1.28      inference('cnf', [status(esa)], [t4_boole])).
% 1.07/1.28  thf(t98_xboole_1, axiom,
% 1.07/1.28    (![A:$i,B:$i]:
% 1.07/1.28     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 1.07/1.28  thf('5', plain,
% 1.07/1.28      (![X19 : $i, X20 : $i]:
% 1.07/1.28         ((k2_xboole_0 @ X19 @ X20)
% 1.07/1.28           = (k5_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X19)))),
% 1.07/1.28      inference('cnf', [status(esa)], [t98_xboole_1])).
% 1.07/1.28  thf(l51_zfmisc_1, axiom,
% 1.07/1.28    (![A:$i,B:$i]:
% 1.07/1.28     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.07/1.28  thf('6', plain,
% 1.07/1.28      (![X65 : $i, X66 : $i]:
% 1.07/1.28         ((k3_tarski @ (k2_tarski @ X65 @ X66)) = (k2_xboole_0 @ X65 @ X66))),
% 1.07/1.28      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.07/1.28  thf('7', plain,
% 1.07/1.28      (![X19 : $i, X20 : $i]:
% 1.07/1.28         ((k3_tarski @ (k2_tarski @ X19 @ X20))
% 1.07/1.28           = (k5_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X19)))),
% 1.07/1.28      inference('demod', [status(thm)], ['5', '6'])).
% 1.07/1.28  thf('8', plain,
% 1.07/1.28      (![X0 : $i]:
% 1.07/1.28         ((k3_tarski @ (k2_tarski @ X0 @ k1_xboole_0))
% 1.07/1.28           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.07/1.28      inference('sup+', [status(thm)], ['4', '7'])).
% 1.07/1.28  thf(t1_boole, axiom,
% 1.07/1.28    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.07/1.28  thf('9', plain, (![X12 : $i]: ((k2_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 1.07/1.28      inference('cnf', [status(esa)], [t1_boole])).
% 1.07/1.28  thf('10', plain,
% 1.07/1.28      (![X65 : $i, X66 : $i]:
% 1.07/1.28         ((k3_tarski @ (k2_tarski @ X65 @ X66)) = (k2_xboole_0 @ X65 @ X66))),
% 1.07/1.28      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.07/1.28  thf('11', plain,
% 1.07/1.28      (![X12 : $i]: ((k3_tarski @ (k2_tarski @ X12 @ k1_xboole_0)) = (X12))),
% 1.07/1.28      inference('demod', [status(thm)], ['9', '10'])).
% 1.07/1.28  thf('12', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.07/1.28      inference('sup+', [status(thm)], ['8', '11'])).
% 1.07/1.28  thf('13', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.07/1.28      inference('demod', [status(thm)], ['3', '12'])).
% 1.07/1.28  thf(t48_xboole_1, axiom,
% 1.07/1.28    (![A:$i,B:$i]:
% 1.07/1.28     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.07/1.28  thf('14', plain,
% 1.07/1.28      (![X16 : $i, X17 : $i]:
% 1.07/1.28         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 1.07/1.28           = (k3_xboole_0 @ X16 @ X17))),
% 1.07/1.28      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.07/1.28  thf('15', plain,
% 1.07/1.28      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 1.07/1.28      inference('sup+', [status(thm)], ['13', '14'])).
% 1.07/1.28  thf('16', plain,
% 1.07/1.28      (![X13 : $i]: ((k3_xboole_0 @ X13 @ k1_xboole_0) = (k1_xboole_0))),
% 1.07/1.28      inference('cnf', [status(esa)], [t2_boole])).
% 1.07/1.28  thf('17', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.07/1.28      inference('demod', [status(thm)], ['15', '16'])).
% 1.07/1.28  thf('18', plain,
% 1.07/1.28      (![X16 : $i, X17 : $i]:
% 1.07/1.28         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 1.07/1.28           = (k3_xboole_0 @ X16 @ X17))),
% 1.07/1.28      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.07/1.28  thf('19', plain,
% 1.07/1.28      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 1.07/1.28      inference('sup+', [status(thm)], ['17', '18'])).
% 1.07/1.28  thf('20', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.07/1.28      inference('demod', [status(thm)], ['3', '12'])).
% 1.07/1.28  thf('21', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 1.07/1.28      inference('demod', [status(thm)], ['19', '20'])).
% 1.07/1.28  thf(t112_xboole_1, axiom,
% 1.07/1.28    (![A:$i,B:$i,C:$i]:
% 1.07/1.28     ( ( k5_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) ) =
% 1.07/1.28       ( k3_xboole_0 @ ( k5_xboole_0 @ A @ C ) @ B ) ))).
% 1.07/1.28  thf('22', plain,
% 1.07/1.28      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.07/1.28         ((k5_xboole_0 @ (k3_xboole_0 @ X6 @ X8) @ (k3_xboole_0 @ X7 @ X8))
% 1.07/1.28           = (k3_xboole_0 @ (k5_xboole_0 @ X6 @ X7) @ X8))),
% 1.07/1.28      inference('cnf', [status(esa)], [t112_xboole_1])).
% 1.07/1.28  thf('23', plain,
% 1.07/1.28      (![X0 : $i, X1 : $i]:
% 1.07/1.28         ((k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 1.07/1.28           = (k3_xboole_0 @ (k5_xboole_0 @ X0 @ X1) @ X0))),
% 1.07/1.28      inference('sup+', [status(thm)], ['21', '22'])).
% 1.07/1.28  thf(commutativity_k3_xboole_0, axiom,
% 1.07/1.28    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.07/1.28  thf('24', plain,
% 1.07/1.28      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.07/1.28      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.07/1.28  thf('25', plain,
% 1.07/1.28      (![X0 : $i, X1 : $i]:
% 1.07/1.28         ((k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 1.07/1.28           = (k3_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 1.07/1.28      inference('demod', [status(thm)], ['23', '24'])).
% 1.07/1.28  thf('26', plain,
% 1.07/1.28      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.07/1.28      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.07/1.28  thf('27', plain,
% 1.07/1.28      (![X2 : $i, X3 : $i]:
% 1.07/1.28         ((k4_xboole_0 @ X2 @ X3)
% 1.07/1.28           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 1.07/1.28      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.07/1.28  thf('28', plain,
% 1.07/1.28      (![X0 : $i, X1 : $i]:
% 1.07/1.28         ((k4_xboole_0 @ X0 @ X1)
% 1.07/1.28           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.07/1.28      inference('sup+', [status(thm)], ['26', '27'])).
% 1.07/1.28  thf('29', plain,
% 1.07/1.28      (![X0 : $i, X1 : $i]:
% 1.07/1.28         ((k4_xboole_0 @ X1 @ X0)
% 1.07/1.28           = (k3_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.07/1.28      inference('sup+', [status(thm)], ['25', '28'])).
% 1.07/1.28  thf(t101_xboole_1, axiom,
% 1.07/1.28    (![A:$i,B:$i]:
% 1.07/1.28     ( ( k5_xboole_0 @ A @ B ) =
% 1.07/1.28       ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.07/1.28  thf('30', plain,
% 1.07/1.28      (![X4 : $i, X5 : $i]:
% 1.07/1.28         ((k5_xboole_0 @ X4 @ X5)
% 1.07/1.28           = (k4_xboole_0 @ (k2_xboole_0 @ X4 @ X5) @ (k3_xboole_0 @ X4 @ X5)))),
% 1.07/1.28      inference('cnf', [status(esa)], [t101_xboole_1])).
% 1.07/1.28  thf('31', plain,
% 1.07/1.28      (![X65 : $i, X66 : $i]:
% 1.07/1.28         ((k3_tarski @ (k2_tarski @ X65 @ X66)) = (k2_xboole_0 @ X65 @ X66))),
% 1.07/1.28      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.07/1.28  thf('32', plain,
% 1.07/1.28      (![X4 : $i, X5 : $i]:
% 1.07/1.28         ((k5_xboole_0 @ X4 @ X5)
% 1.07/1.28           = (k4_xboole_0 @ (k3_tarski @ (k2_tarski @ X4 @ X5)) @ 
% 1.07/1.28              (k3_xboole_0 @ X4 @ X5)))),
% 1.07/1.28      inference('demod', [status(thm)], ['30', '31'])).
% 1.07/1.28  thf('33', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 1.07/1.28      inference('demod', [status(thm)], ['19', '20'])).
% 1.07/1.28  thf(t16_xboole_1, axiom,
% 1.07/1.28    (![A:$i,B:$i,C:$i]:
% 1.07/1.28     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 1.07/1.28       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 1.07/1.28  thf('34', plain,
% 1.07/1.28      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.07/1.28         ((k3_xboole_0 @ (k3_xboole_0 @ X9 @ X10) @ X11)
% 1.07/1.28           = (k3_xboole_0 @ X9 @ (k3_xboole_0 @ X10 @ X11)))),
% 1.07/1.28      inference('cnf', [status(esa)], [t16_xboole_1])).
% 1.07/1.28  thf('35', plain,
% 1.07/1.28      (![X0 : $i, X1 : $i]:
% 1.07/1.28         ((k3_xboole_0 @ X0 @ X1)
% 1.07/1.28           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 1.07/1.28      inference('sup+', [status(thm)], ['33', '34'])).
% 1.07/1.28  thf('36', plain,
% 1.07/1.28      (![X2 : $i, X3 : $i]:
% 1.07/1.28         ((k4_xboole_0 @ X2 @ X3)
% 1.07/1.28           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 1.07/1.28      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.07/1.28  thf('37', plain,
% 1.07/1.28      (![X0 : $i, X1 : $i]:
% 1.07/1.28         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 1.07/1.28           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.07/1.28      inference('sup+', [status(thm)], ['35', '36'])).
% 1.07/1.28  thf('38', plain,
% 1.07/1.28      (![X2 : $i, X3 : $i]:
% 1.07/1.28         ((k4_xboole_0 @ X2 @ X3)
% 1.07/1.28           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 1.07/1.28      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.07/1.28  thf('39', plain,
% 1.07/1.28      (![X0 : $i, X1 : $i]:
% 1.07/1.28         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 1.07/1.28           = (k4_xboole_0 @ X1 @ X0))),
% 1.07/1.28      inference('demod', [status(thm)], ['37', '38'])).
% 1.07/1.28  thf('40', plain,
% 1.07/1.28      (![X16 : $i, X17 : $i]:
% 1.07/1.28         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 1.07/1.28           = (k3_xboole_0 @ X16 @ X17))),
% 1.07/1.28      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.07/1.28  thf('41', plain,
% 1.07/1.28      (![X16 : $i, X17 : $i]:
% 1.07/1.28         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 1.07/1.28           = (k3_xboole_0 @ X16 @ X17))),
% 1.07/1.28      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.07/1.28  thf('42', plain,
% 1.07/1.28      (![X0 : $i, X1 : $i]:
% 1.07/1.28         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 1.07/1.28           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.07/1.28      inference('sup+', [status(thm)], ['40', '41'])).
% 1.07/1.28  thf('43', plain,
% 1.07/1.28      (![X0 : $i, X1 : $i]:
% 1.07/1.28         ((k4_xboole_0 @ X1 @ X0)
% 1.07/1.28           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.07/1.28      inference('sup+', [status(thm)], ['39', '42'])).
% 1.07/1.28  thf('44', plain,
% 1.07/1.28      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.07/1.28      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.07/1.28  thf('45', plain,
% 1.07/1.28      ((r1_tarski @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ sk_B)),
% 1.07/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.28  thf('46', plain,
% 1.07/1.28      (![X65 : $i, X66 : $i]:
% 1.07/1.28         ((k3_tarski @ (k2_tarski @ X65 @ X66)) = (k2_xboole_0 @ X65 @ X66))),
% 1.07/1.28      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.07/1.28  thf('47', plain,
% 1.07/1.28      ((r1_tarski @ (k3_tarski @ (k2_tarski @ (k1_tarski @ sk_A) @ sk_B)) @ 
% 1.07/1.28        sk_B)),
% 1.07/1.28      inference('demod', [status(thm)], ['45', '46'])).
% 1.07/1.28  thf(t45_xboole_1, axiom,
% 1.07/1.28    (![A:$i,B:$i]:
% 1.07/1.28     ( ( r1_tarski @ A @ B ) =>
% 1.07/1.28       ( ( B ) = ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) ))).
% 1.07/1.28  thf('48', plain,
% 1.07/1.28      (![X14 : $i, X15 : $i]:
% 1.07/1.28         (((X15) = (k2_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14)))
% 1.07/1.28          | ~ (r1_tarski @ X14 @ X15))),
% 1.07/1.28      inference('cnf', [status(esa)], [t45_xboole_1])).
% 1.07/1.28  thf('49', plain,
% 1.07/1.28      (![X65 : $i, X66 : $i]:
% 1.07/1.28         ((k3_tarski @ (k2_tarski @ X65 @ X66)) = (k2_xboole_0 @ X65 @ X66))),
% 1.07/1.28      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.07/1.28  thf('50', plain,
% 1.07/1.28      (![X14 : $i, X15 : $i]:
% 1.07/1.28         (((X15) = (k3_tarski @ (k2_tarski @ X14 @ (k4_xboole_0 @ X15 @ X14))))
% 1.07/1.28          | ~ (r1_tarski @ X14 @ X15))),
% 1.07/1.28      inference('demod', [status(thm)], ['48', '49'])).
% 1.07/1.28  thf('51', plain,
% 1.07/1.28      (((sk_B)
% 1.07/1.28         = (k3_tarski @ 
% 1.07/1.28            (k2_tarski @ 
% 1.07/1.28             (k3_tarski @ (k2_tarski @ (k1_tarski @ sk_A) @ sk_B)) @ 
% 1.07/1.28             (k4_xboole_0 @ sk_B @ 
% 1.07/1.28              (k3_tarski @ (k2_tarski @ (k1_tarski @ sk_A) @ sk_B))))))),
% 1.07/1.28      inference('sup-', [status(thm)], ['47', '50'])).
% 1.07/1.28  thf('52', plain,
% 1.07/1.28      (![X4 : $i, X5 : $i]:
% 1.07/1.28         ((k5_xboole_0 @ X4 @ X5)
% 1.07/1.28           = (k4_xboole_0 @ (k3_tarski @ (k2_tarski @ X4 @ X5)) @ 
% 1.07/1.28              (k3_xboole_0 @ X4 @ X5)))),
% 1.07/1.28      inference('demod', [status(thm)], ['30', '31'])).
% 1.07/1.28  thf('53', plain,
% 1.07/1.28      (((k5_xboole_0 @ (k3_tarski @ (k2_tarski @ (k1_tarski @ sk_A) @ sk_B)) @ 
% 1.07/1.28         (k4_xboole_0 @ sk_B @ 
% 1.07/1.28          (k3_tarski @ (k2_tarski @ (k1_tarski @ sk_A) @ sk_B))))
% 1.07/1.28         = (k4_xboole_0 @ sk_B @ 
% 1.07/1.28            (k3_xboole_0 @ 
% 1.07/1.28             (k3_tarski @ (k2_tarski @ (k1_tarski @ sk_A) @ sk_B)) @ 
% 1.07/1.28             (k4_xboole_0 @ sk_B @ 
% 1.07/1.28              (k3_tarski @ (k2_tarski @ (k1_tarski @ sk_A) @ sk_B))))))),
% 1.07/1.28      inference('sup+', [status(thm)], ['51', '52'])).
% 1.07/1.28  thf('54', plain,
% 1.07/1.28      (![X19 : $i, X20 : $i]:
% 1.07/1.28         ((k3_tarski @ (k2_tarski @ X19 @ X20))
% 1.07/1.28           = (k5_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X19)))),
% 1.07/1.28      inference('demod', [status(thm)], ['5', '6'])).
% 1.07/1.28  thf('55', plain,
% 1.07/1.28      (((k3_tarski @ 
% 1.07/1.28         (k2_tarski @ (k3_tarski @ (k2_tarski @ (k1_tarski @ sk_A) @ sk_B)) @ 
% 1.07/1.28          sk_B))
% 1.07/1.28         = (k4_xboole_0 @ sk_B @ 
% 1.07/1.28            (k3_xboole_0 @ 
% 1.07/1.28             (k3_tarski @ (k2_tarski @ (k1_tarski @ sk_A) @ sk_B)) @ 
% 1.07/1.28             (k4_xboole_0 @ sk_B @ 
% 1.07/1.28              (k3_tarski @ (k2_tarski @ (k1_tarski @ sk_A) @ sk_B))))))),
% 1.07/1.28      inference('demod', [status(thm)], ['53', '54'])).
% 1.07/1.28  thf('56', plain,
% 1.07/1.28      (![X2 : $i, X3 : $i]:
% 1.07/1.28         ((k4_xboole_0 @ X2 @ X3)
% 1.07/1.28           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 1.07/1.28      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.07/1.28  thf('57', plain,
% 1.07/1.28      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.07/1.28      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.07/1.28  thf('58', plain,
% 1.07/1.28      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.07/1.28         ((k5_xboole_0 @ (k3_xboole_0 @ X6 @ X8) @ (k3_xboole_0 @ X7 @ X8))
% 1.07/1.28           = (k3_xboole_0 @ (k5_xboole_0 @ X6 @ X7) @ X8))),
% 1.07/1.28      inference('cnf', [status(esa)], [t112_xboole_1])).
% 1.07/1.28  thf('59', plain,
% 1.07/1.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.07/1.28         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X2 @ X1))
% 1.07/1.28           = (k3_xboole_0 @ (k5_xboole_0 @ X0 @ X2) @ X1))),
% 1.07/1.28      inference('sup+', [status(thm)], ['57', '58'])).
% 1.07/1.28  thf('60', plain,
% 1.07/1.28      (![X0 : $i, X1 : $i]:
% 1.07/1.28         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 1.07/1.28           = (k3_xboole_0 @ (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1)) @ X0))),
% 1.07/1.28      inference('sup+', [status(thm)], ['56', '59'])).
% 1.07/1.28  thf('61', plain,
% 1.07/1.28      (![X0 : $i, X1 : $i]:
% 1.07/1.28         ((k3_xboole_0 @ X0 @ X1)
% 1.07/1.28           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 1.07/1.28      inference('sup+', [status(thm)], ['33', '34'])).
% 1.07/1.28  thf('62', plain,
% 1.07/1.28      (![X0 : $i, X1 : $i]:
% 1.07/1.28         ((k4_xboole_0 @ X0 @ X1)
% 1.07/1.28           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.07/1.28      inference('sup+', [status(thm)], ['26', '27'])).
% 1.07/1.28  thf('63', plain,
% 1.07/1.28      (![X0 : $i, X1 : $i]:
% 1.07/1.28         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)
% 1.07/1.28           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 1.07/1.28      inference('sup+', [status(thm)], ['61', '62'])).
% 1.07/1.28  thf('64', plain,
% 1.07/1.28      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.07/1.28         ((k5_xboole_0 @ (k3_xboole_0 @ X6 @ X8) @ (k3_xboole_0 @ X7 @ X8))
% 1.07/1.28           = (k3_xboole_0 @ (k5_xboole_0 @ X6 @ X7) @ X8))),
% 1.07/1.28      inference('cnf', [status(esa)], [t112_xboole_1])).
% 1.07/1.28  thf('65', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 1.07/1.28      inference('demod', [status(thm)], ['19', '20'])).
% 1.07/1.28  thf('66', plain,
% 1.07/1.28      (![X2 : $i, X3 : $i]:
% 1.07/1.28         ((k4_xboole_0 @ X2 @ X3)
% 1.07/1.28           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 1.07/1.28      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.07/1.28  thf('67', plain,
% 1.07/1.28      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.07/1.28      inference('sup+', [status(thm)], ['65', '66'])).
% 1.07/1.28  thf('68', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.07/1.28      inference('demod', [status(thm)], ['15', '16'])).
% 1.07/1.28  thf('69', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.07/1.28      inference('sup+', [status(thm)], ['67', '68'])).
% 1.07/1.28  thf('70', plain,
% 1.07/1.28      (![X0 : $i, X1 : $i]:
% 1.07/1.28         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)
% 1.07/1.28           = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 1.07/1.28      inference('demod', [status(thm)], ['63', '64', '69'])).
% 1.07/1.28  thf('71', plain,
% 1.07/1.28      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.07/1.28      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.07/1.28  thf('72', plain,
% 1.07/1.28      (![X13 : $i]: ((k3_xboole_0 @ X13 @ k1_xboole_0) = (k1_xboole_0))),
% 1.07/1.28      inference('cnf', [status(esa)], [t2_boole])).
% 1.07/1.28  thf('73', plain,
% 1.07/1.28      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.07/1.28      inference('sup+', [status(thm)], ['71', '72'])).
% 1.07/1.28  thf('74', plain,
% 1.07/1.28      (![X0 : $i, X1 : $i]:
% 1.07/1.28         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1) = (k1_xboole_0))),
% 1.07/1.28      inference('demod', [status(thm)], ['70', '73'])).
% 1.07/1.28  thf('75', plain,
% 1.07/1.28      (![X0 : $i, X1 : $i]:
% 1.07/1.28         ((k4_xboole_0 @ X0 @ X1)
% 1.07/1.28           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.07/1.28      inference('sup+', [status(thm)], ['26', '27'])).
% 1.07/1.28  thf('76', plain,
% 1.07/1.28      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.07/1.28      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.07/1.28  thf('77', plain,
% 1.07/1.28      (![X0 : $i, X1 : $i]:
% 1.07/1.28         ((k1_xboole_0) = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.07/1.28      inference('demod', [status(thm)], ['60', '74', '75', '76'])).
% 1.07/1.28  thf('78', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.07/1.28      inference('demod', [status(thm)], ['3', '12'])).
% 1.07/1.28  thf('79', plain,
% 1.07/1.28      (((k3_tarski @ 
% 1.07/1.28         (k2_tarski @ (k3_tarski @ (k2_tarski @ (k1_tarski @ sk_A) @ sk_B)) @ 
% 1.07/1.28          sk_B))
% 1.07/1.28         = (sk_B))),
% 1.07/1.28      inference('demod', [status(thm)], ['55', '77', '78'])).
% 1.07/1.28  thf('80', plain,
% 1.07/1.28      (![X4 : $i, X5 : $i]:
% 1.07/1.28         ((k5_xboole_0 @ X4 @ X5)
% 1.07/1.28           = (k4_xboole_0 @ (k3_tarski @ (k2_tarski @ X4 @ X5)) @ 
% 1.07/1.28              (k3_xboole_0 @ X4 @ X5)))),
% 1.07/1.28      inference('demod', [status(thm)], ['30', '31'])).
% 1.07/1.28  thf('81', plain,
% 1.07/1.28      (((k5_xboole_0 @ (k3_tarski @ (k2_tarski @ (k1_tarski @ sk_A) @ sk_B)) @ 
% 1.07/1.28         sk_B)
% 1.07/1.28         = (k4_xboole_0 @ sk_B @ 
% 1.07/1.28            (k3_xboole_0 @ 
% 1.07/1.28             (k3_tarski @ (k2_tarski @ (k1_tarski @ sk_A) @ sk_B)) @ sk_B)))),
% 1.07/1.28      inference('sup+', [status(thm)], ['79', '80'])).
% 1.07/1.28  thf('82', plain,
% 1.07/1.28      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.07/1.28      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.07/1.28  thf('83', plain,
% 1.07/1.28      (![X0 : $i, X1 : $i]:
% 1.07/1.28         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 1.07/1.28           = (k4_xboole_0 @ X1 @ X0))),
% 1.07/1.28      inference('demod', [status(thm)], ['37', '38'])).
% 1.07/1.28  thf('84', plain,
% 1.07/1.28      (((k5_xboole_0 @ (k3_tarski @ (k2_tarski @ (k1_tarski @ sk_A) @ sk_B)) @ 
% 1.07/1.28         sk_B)
% 1.07/1.28         = (k4_xboole_0 @ sk_B @ 
% 1.07/1.28            (k3_tarski @ (k2_tarski @ (k1_tarski @ sk_A) @ sk_B))))),
% 1.07/1.28      inference('demod', [status(thm)], ['81', '82', '83'])).
% 1.07/1.28  thf('85', plain,
% 1.07/1.28      (![X0 : $i, X1 : $i]:
% 1.07/1.28         ((k1_xboole_0) = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.07/1.28      inference('demod', [status(thm)], ['60', '74', '75', '76'])).
% 1.07/1.28  thf('86', plain,
% 1.07/1.28      (((k1_xboole_0)
% 1.07/1.28         = (k3_xboole_0 @ 
% 1.07/1.28            (k3_tarski @ (k2_tarski @ (k1_tarski @ sk_A) @ sk_B)) @ 
% 1.07/1.28            (k5_xboole_0 @ 
% 1.07/1.28             (k3_tarski @ (k2_tarski @ (k1_tarski @ sk_A) @ sk_B)) @ sk_B)))),
% 1.07/1.28      inference('sup+', [status(thm)], ['84', '85'])).
% 1.07/1.28  thf('87', plain,
% 1.07/1.28      (![X0 : $i, X1 : $i]:
% 1.07/1.28         ((k4_xboole_0 @ X1 @ X0)
% 1.07/1.28           = (k3_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.07/1.28      inference('sup+', [status(thm)], ['25', '28'])).
% 1.07/1.28  thf('88', plain,
% 1.07/1.28      (((k1_xboole_0)
% 1.07/1.28         = (k4_xboole_0 @ 
% 1.07/1.28            (k3_tarski @ (k2_tarski @ (k1_tarski @ sk_A) @ sk_B)) @ sk_B))),
% 1.07/1.28      inference('demod', [status(thm)], ['86', '87'])).
% 1.07/1.28  thf('89', plain,
% 1.07/1.28      (![X16 : $i, X17 : $i]:
% 1.07/1.28         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 1.07/1.28           = (k3_xboole_0 @ X16 @ X17))),
% 1.07/1.28      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.07/1.28  thf('90', plain,
% 1.07/1.28      (((k4_xboole_0 @ (k3_tarski @ (k2_tarski @ (k1_tarski @ sk_A) @ sk_B)) @ 
% 1.07/1.28         k1_xboole_0)
% 1.07/1.28         = (k3_xboole_0 @ 
% 1.07/1.28            (k3_tarski @ (k2_tarski @ (k1_tarski @ sk_A) @ sk_B)) @ sk_B))),
% 1.07/1.28      inference('sup+', [status(thm)], ['88', '89'])).
% 1.07/1.28  thf('91', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.07/1.28      inference('demod', [status(thm)], ['3', '12'])).
% 1.07/1.28  thf('92', plain,
% 1.07/1.28      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.07/1.28      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.07/1.28  thf('93', plain,
% 1.07/1.28      (((k3_tarski @ (k2_tarski @ (k1_tarski @ sk_A) @ sk_B))
% 1.07/1.28         = (k3_xboole_0 @ sk_B @ 
% 1.07/1.28            (k3_tarski @ (k2_tarski @ (k1_tarski @ sk_A) @ sk_B))))),
% 1.07/1.28      inference('demod', [status(thm)], ['90', '91', '92'])).
% 1.07/1.28  thf('94', plain,
% 1.07/1.28      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.07/1.28         ((k3_xboole_0 @ (k3_xboole_0 @ X9 @ X10) @ X11)
% 1.07/1.28           = (k3_xboole_0 @ X9 @ (k3_xboole_0 @ X10 @ X11)))),
% 1.07/1.28      inference('cnf', [status(esa)], [t16_xboole_1])).
% 1.07/1.28  thf('95', plain,
% 1.07/1.28      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.07/1.28      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.07/1.28  thf('96', plain,
% 1.07/1.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.07/1.28         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1))
% 1.07/1.28           = (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.07/1.28      inference('sup+', [status(thm)], ['94', '95'])).
% 1.07/1.28  thf('97', plain,
% 1.07/1.28      (![X0 : $i, X1 : $i]:
% 1.07/1.28         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1) = (k1_xboole_0))),
% 1.07/1.28      inference('demod', [status(thm)], ['70', '73'])).
% 1.07/1.28  thf('98', plain,
% 1.07/1.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.07/1.28         ((k4_xboole_0 @ (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X1)
% 1.07/1.28           = (k1_xboole_0))),
% 1.07/1.28      inference('sup+', [status(thm)], ['96', '97'])).
% 1.07/1.28  thf('99', plain,
% 1.07/1.28      (![X0 : $i]:
% 1.07/1.28         ((k4_xboole_0 @ 
% 1.07/1.28           (k3_xboole_0 @ X0 @ 
% 1.07/1.28            (k3_tarski @ (k2_tarski @ (k1_tarski @ sk_A) @ sk_B))) @ 
% 1.07/1.28           sk_B) = (k1_xboole_0))),
% 1.07/1.28      inference('sup+', [status(thm)], ['93', '98'])).
% 1.07/1.28  thf('100', plain,
% 1.07/1.28      (![X0 : $i]:
% 1.07/1.28         ((k4_xboole_0 @ 
% 1.07/1.28           (k3_xboole_0 @ 
% 1.07/1.28            (k3_tarski @ (k2_tarski @ (k1_tarski @ sk_A) @ sk_B)) @ X0) @ 
% 1.07/1.28           sk_B) = (k1_xboole_0))),
% 1.07/1.28      inference('sup+', [status(thm)], ['44', '99'])).
% 1.07/1.28  thf('101', plain,
% 1.07/1.28      (![X0 : $i]:
% 1.07/1.28         ((k4_xboole_0 @ 
% 1.07/1.28           (k4_xboole_0 @ 
% 1.07/1.28            (k3_tarski @ (k2_tarski @ (k1_tarski @ sk_A) @ sk_B)) @ X0) @ 
% 1.07/1.28           sk_B) = (k1_xboole_0))),
% 1.07/1.28      inference('sup+', [status(thm)], ['43', '100'])).
% 1.07/1.28  thf('102', plain,
% 1.07/1.28      (((k4_xboole_0 @ (k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ sk_B)
% 1.07/1.28         = (k1_xboole_0))),
% 1.07/1.28      inference('sup+', [status(thm)], ['32', '101'])).
% 1.07/1.28  thf('103', plain,
% 1.07/1.28      (![X16 : $i, X17 : $i]:
% 1.07/1.28         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 1.07/1.28           = (k3_xboole_0 @ X16 @ X17))),
% 1.07/1.28      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.07/1.28  thf('104', plain,
% 1.07/1.28      (((k4_xboole_0 @ (k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ k1_xboole_0)
% 1.07/1.28         = (k3_xboole_0 @ (k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ sk_B))),
% 1.07/1.28      inference('sup+', [status(thm)], ['102', '103'])).
% 1.07/1.28  thf('105', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.07/1.28      inference('demod', [status(thm)], ['3', '12'])).
% 1.07/1.28  thf('106', plain,
% 1.07/1.28      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.07/1.28      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.07/1.28  thf('107', plain,
% 1.07/1.28      (((k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 1.07/1.28         = (k3_xboole_0 @ sk_B @ (k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)))),
% 1.07/1.28      inference('demod', [status(thm)], ['104', '105', '106'])).
% 1.07/1.28  thf('108', plain,
% 1.07/1.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.07/1.28         ((k4_xboole_0 @ (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X1)
% 1.07/1.28           = (k1_xboole_0))),
% 1.07/1.28      inference('sup+', [status(thm)], ['96', '97'])).
% 1.07/1.28  thf('109', plain,
% 1.07/1.28      (![X0 : $i]:
% 1.07/1.28         ((k4_xboole_0 @ 
% 1.07/1.28           (k3_xboole_0 @ X0 @ (k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)) @ 
% 1.07/1.28           sk_B) = (k1_xboole_0))),
% 1.07/1.28      inference('sup+', [status(thm)], ['107', '108'])).
% 1.07/1.28  thf('110', plain,
% 1.07/1.28      (((k4_xboole_0 @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ sk_B)
% 1.07/1.28         = (k1_xboole_0))),
% 1.07/1.28      inference('sup+', [status(thm)], ['29', '109'])).
% 1.07/1.28  thf('111', plain,
% 1.07/1.28      (![X0 : $i, X1 : $i]:
% 1.07/1.28         ((k1_xboole_0) = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.07/1.28      inference('demod', [status(thm)], ['60', '74', '75', '76'])).
% 1.07/1.28  thf('112', plain,
% 1.07/1.28      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.07/1.28      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.07/1.28  thf('113', plain,
% 1.07/1.28      (![X0 : $i, X1 : $i]:
% 1.07/1.28         ((k3_xboole_0 @ X0 @ X1)
% 1.07/1.28           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 1.07/1.28      inference('sup+', [status(thm)], ['33', '34'])).
% 1.07/1.28  thf('114', plain,
% 1.07/1.28      (![X0 : $i, X1 : $i]:
% 1.07/1.28         ((k3_xboole_0 @ X0 @ X1)
% 1.07/1.28           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.07/1.28      inference('sup+', [status(thm)], ['112', '113'])).
% 1.07/1.28  thf('115', plain,
% 1.07/1.28      (![X2 : $i, X3 : $i]:
% 1.07/1.28         ((k4_xboole_0 @ X2 @ X3)
% 1.07/1.28           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 1.07/1.28      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.07/1.28  thf('116', plain,
% 1.07/1.28      (![X0 : $i, X1 : $i]:
% 1.07/1.28         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1))
% 1.07/1.28           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.07/1.28      inference('sup+', [status(thm)], ['114', '115'])).
% 1.07/1.28  thf('117', plain,
% 1.07/1.28      (![X2 : $i, X3 : $i]:
% 1.07/1.28         ((k4_xboole_0 @ X2 @ X3)
% 1.07/1.28           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 1.07/1.28      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.07/1.28  thf('118', plain,
% 1.07/1.28      (![X0 : $i, X1 : $i]:
% 1.07/1.28         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1))
% 1.07/1.28           = (k4_xboole_0 @ X1 @ X0))),
% 1.07/1.28      inference('demod', [status(thm)], ['116', '117'])).
% 1.07/1.28  thf('119', plain,
% 1.07/1.28      (![X0 : $i, X1 : $i]:
% 1.07/1.28         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ k1_xboole_0)
% 1.07/1.28           = (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 1.07/1.28      inference('sup+', [status(thm)], ['111', '118'])).
% 1.07/1.28  thf('120', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.07/1.28      inference('demod', [status(thm)], ['3', '12'])).
% 1.07/1.28  thf('121', plain,
% 1.07/1.28      (![X0 : $i, X1 : $i]:
% 1.07/1.28         ((k4_xboole_0 @ X1 @ X0)
% 1.07/1.28           = (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 1.07/1.28      inference('demod', [status(thm)], ['119', '120'])).
% 1.07/1.28  thf('122', plain,
% 1.07/1.28      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 1.07/1.28      inference('demod', [status(thm)], ['110', '121'])).
% 1.07/1.28  thf('123', plain,
% 1.07/1.28      (![X16 : $i, X17 : $i]:
% 1.07/1.28         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 1.07/1.28           = (k3_xboole_0 @ X16 @ X17))),
% 1.07/1.28      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.07/1.28  thf('124', plain,
% 1.07/1.28      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0)
% 1.07/1.28         = (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 1.07/1.28      inference('sup+', [status(thm)], ['122', '123'])).
% 1.07/1.28  thf('125', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.07/1.28      inference('demod', [status(thm)], ['3', '12'])).
% 1.07/1.28  thf('126', plain,
% 1.07/1.28      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.07/1.28      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.07/1.28  thf('127', plain,
% 1.07/1.28      (((k1_tarski @ sk_A) = (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 1.07/1.28      inference('demod', [status(thm)], ['124', '125', '126'])).
% 1.07/1.28  thf(l29_zfmisc_1, axiom,
% 1.07/1.28    (![A:$i,B:$i]:
% 1.07/1.28     ( ( ( k3_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( k1_tarski @ B ) ) =>
% 1.07/1.28       ( r2_hidden @ B @ A ) ))).
% 1.07/1.28  thf('128', plain,
% 1.07/1.28      (![X63 : $i, X64 : $i]:
% 1.07/1.28         ((r2_hidden @ X63 @ X64)
% 1.07/1.28          | ((k3_xboole_0 @ X64 @ (k1_tarski @ X63)) != (k1_tarski @ X63)))),
% 1.07/1.28      inference('cnf', [status(esa)], [l29_zfmisc_1])).
% 1.07/1.28  thf('129', plain,
% 1.07/1.28      ((((k1_tarski @ sk_A) != (k1_tarski @ sk_A)) | (r2_hidden @ sk_A @ sk_B))),
% 1.07/1.28      inference('sup-', [status(thm)], ['127', '128'])).
% 1.07/1.28  thf('130', plain, ((r2_hidden @ sk_A @ sk_B)),
% 1.07/1.28      inference('simplify', [status(thm)], ['129'])).
% 1.07/1.28  thf('131', plain, ($false), inference('demod', [status(thm)], ['0', '130'])).
% 1.07/1.28  
% 1.07/1.28  % SZS output end Refutation
% 1.07/1.28  
% 1.07/1.29  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
