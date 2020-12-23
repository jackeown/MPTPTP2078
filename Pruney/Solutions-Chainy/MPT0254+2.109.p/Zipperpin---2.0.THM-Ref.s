%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lPVnzqeAfg

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:49 EST 2020

% Result     : Theorem 0.85s
% Output     : Refutation 0.85s
% Verified   : 
% Statistics : Number of formulae       :  160 ( 642 expanded)
%              Number of leaves         :   21 ( 223 expanded)
%              Depth                    :   23
%              Number of atoms          : 1571 (5626 expanded)
%              Number of equality atoms :  148 ( 629 expanded)
%              Maximal formula depth    :   10 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t49_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
       != k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t49_zfmisc_1])).

thf('0',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X16 @ X17 ) @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf('3',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('4',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ ( k5_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('7',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ ( k5_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','8'])).

thf('10',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['0','9'])).

thf('11',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['0','9'])).

thf('12',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ ( k5_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('13',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ ( k5_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = ( k5_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['11','16'])).

thf('18',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('19',plain,(
    ! [X11: $i] :
      ( ( k5_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('23',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('26',plain,(
    ! [X15: $i] :
      ( ( k5_xboole_0 @ X15 @ X15 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('27',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k5_xboole_0 @ X12 @ ( k5_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['25','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['24','31'])).

thf('33',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k4_xboole_0 @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['21','34'])).

thf('36',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('37',plain,
    ( ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) @ ( k4_xboole_0 @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('39',plain,
    ( ( k4_xboole_0 @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = ( k5_xboole_0 @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('41',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('42',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k5_xboole_0 @ X12 @ ( k5_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( k4_xboole_0 @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ sk_B @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['39','40','43'])).

thf('45',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k5_xboole_0 @ X12 @ ( k5_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('46',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('49',plain,
    ( ( k4_xboole_0 @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['44','47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('51',plain,
    ( ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) )
    = ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) @ ( k4_xboole_0 @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['25','30'])).

thf('54',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = ( k5_xboole_0 @ ( k4_xboole_0 @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('57',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('59',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('60',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('62',plain,
    ( ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) )
    = ( k5_xboole_0 @ sk_B @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ ( k5_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('64',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k5_xboole_0 @ X12 @ ( k5_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k5_xboole_0 @ X12 @ ( k5_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X2 ) ) ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['67','68','69','70'])).

thf('72',plain,
    ( ( k5_xboole_0 @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) ) ),
    inference('sup+',[status(thm)],['62','71'])).

thf('73',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('74',plain,
    ( ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) )
    = ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('76',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('77',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('78',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('79',plain,
    ( ( k4_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = ( k5_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) )
    = ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['72','73','74','75','76','79'])).

thf('81',plain,
    ( ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) )
    = ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['51','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['25','30'])).

thf('83',plain,
    ( ( k1_tarski @ sk_A )
    = ( k5_xboole_0 @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) @ ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('85',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('86',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('87',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['25','30'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k4_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['86','91'])).

thf('93',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('94',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) @ ( k4_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('96',plain,
    ( ( k1_tarski @ sk_A )
    = ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['83','84','85','94','95'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('97',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('98',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X15: $i] :
      ( ( k5_xboole_0 @ X15 @ X15 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ ( k5_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('107',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('109',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X16 ) ) ) ),
    inference(demod,[status(thm)],['106','107','108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['105','109'])).

thf('111',plain,(
    ! [X11: $i] :
      ( ( k5_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = sk_B ),
    inference('sup+',[status(thm)],['96','112'])).

thf('114',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['0','9'])).

thf('115',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup+',[status(thm)],['113','114'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('116',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('117',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X15: $i] :
      ( ( k5_xboole_0 @ X15 @ X15 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('122',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ ( k5_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['128','129'])).

thf('131',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['10','115','130'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('132',plain,(
    ! [X48: $i,X49: $i] :
      ( ( X49 != X48 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X49 ) @ ( k1_tarski @ X48 ) )
       != ( k1_tarski @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('133',plain,(
    ! [X48: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X48 ) @ ( k1_tarski @ X48 ) )
     != ( k1_tarski @ X48 ) ) ),
    inference(simplify,[status(thm)],['132'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['118','119'])).

thf('135',plain,(
    ! [X48: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X48 ) ) ),
    inference(demod,[status(thm)],['133','134'])).

thf('136',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['131','135'])).

thf('137',plain,(
    $false ),
    inference(simplify,[status(thm)],['136'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lPVnzqeAfg
% 0.16/0.38  % Computer   : n025.cluster.edu
% 0.16/0.38  % Model      : x86_64 x86_64
% 0.16/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.38  % Memory     : 8042.1875MB
% 0.16/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.38  % CPULimit   : 60
% 0.16/0.38  % DateTime   : Tue Dec  1 18:31:51 EST 2020
% 0.23/0.38  % CPUTime    : 
% 0.23/0.38  % Running portfolio for 600 s
% 0.23/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.23/0.38  % Number of cores: 8
% 0.23/0.38  % Python version: Python 3.6.8
% 0.23/0.38  % Running in FO mode
% 0.85/1.10  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.85/1.10  % Solved by: fo/fo7.sh
% 0.85/1.10  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.85/1.10  % done 497 iterations in 0.609s
% 0.85/1.10  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.85/1.10  % SZS output start Refutation
% 0.85/1.10  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.85/1.10  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.85/1.10  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.85/1.10  thf(sk_B_type, type, sk_B: $i).
% 0.85/1.10  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.85/1.10  thf(sk_A_type, type, sk_A: $i).
% 0.85/1.10  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.85/1.10  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.85/1.10  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.85/1.10  thf(t49_zfmisc_1, conjecture,
% 0.85/1.10    (![A:$i,B:$i]:
% 0.85/1.10     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.85/1.10  thf(zf_stmt_0, negated_conjecture,
% 0.85/1.10    (~( ![A:$i,B:$i]:
% 0.85/1.10        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ) )),
% 0.85/1.10    inference('cnf.neg', [status(esa)], [t49_zfmisc_1])).
% 0.85/1.10  thf('0', plain,
% 0.85/1.10      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.85/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.10  thf(commutativity_k5_xboole_0, axiom,
% 0.85/1.10    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.85/1.10  thf('1', plain,
% 0.85/1.10      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.85/1.10      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.85/1.10  thf(t94_xboole_1, axiom,
% 0.85/1.10    (![A:$i,B:$i]:
% 0.85/1.10     ( ( k2_xboole_0 @ A @ B ) =
% 0.85/1.10       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.85/1.10  thf('2', plain,
% 0.85/1.10      (![X16 : $i, X17 : $i]:
% 0.85/1.10         ((k2_xboole_0 @ X16 @ X17)
% 0.85/1.10           = (k5_xboole_0 @ (k5_xboole_0 @ X16 @ X17) @ 
% 0.85/1.10              (k3_xboole_0 @ X16 @ X17)))),
% 0.85/1.10      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.85/1.10  thf('3', plain,
% 0.85/1.10      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.85/1.10      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.85/1.10  thf('4', plain,
% 0.85/1.10      (![X16 : $i, X17 : $i]:
% 0.85/1.10         ((k2_xboole_0 @ X16 @ X17)
% 0.85/1.10           = (k5_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ 
% 0.85/1.10              (k5_xboole_0 @ X16 @ X17)))),
% 0.85/1.10      inference('demod', [status(thm)], ['2', '3'])).
% 0.85/1.10  thf('5', plain,
% 0.85/1.10      (![X0 : $i, X1 : $i]:
% 0.85/1.10         ((k2_xboole_0 @ X0 @ X1)
% 0.85/1.10           = (k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k5_xboole_0 @ X1 @ X0)))),
% 0.85/1.10      inference('sup+', [status(thm)], ['1', '4'])).
% 0.85/1.10  thf(commutativity_k3_xboole_0, axiom,
% 0.85/1.10    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.85/1.10  thf('6', plain,
% 0.85/1.10      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.85/1.10      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.85/1.10  thf('7', plain,
% 0.85/1.10      (![X16 : $i, X17 : $i]:
% 0.85/1.10         ((k2_xboole_0 @ X16 @ X17)
% 0.85/1.10           = (k5_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ 
% 0.85/1.10              (k5_xboole_0 @ X16 @ X17)))),
% 0.85/1.10      inference('demod', [status(thm)], ['2', '3'])).
% 0.85/1.10  thf('8', plain,
% 0.85/1.10      (![X0 : $i, X1 : $i]:
% 0.85/1.10         ((k2_xboole_0 @ X0 @ X1)
% 0.85/1.10           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X0 @ X1)))),
% 0.85/1.10      inference('sup+', [status(thm)], ['6', '7'])).
% 0.85/1.10  thf('9', plain,
% 0.85/1.10      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X0 @ X1) = (k2_xboole_0 @ X1 @ X0))),
% 0.85/1.10      inference('sup+', [status(thm)], ['5', '8'])).
% 0.85/1.10  thf('10', plain,
% 0.85/1.10      (((k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))),
% 0.85/1.10      inference('demod', [status(thm)], ['0', '9'])).
% 0.85/1.10  thf('11', plain,
% 0.85/1.10      (((k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))),
% 0.85/1.10      inference('demod', [status(thm)], ['0', '9'])).
% 0.85/1.10  thf('12', plain,
% 0.85/1.10      (![X16 : $i, X17 : $i]:
% 0.85/1.10         ((k2_xboole_0 @ X16 @ X17)
% 0.85/1.10           = (k5_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ 
% 0.85/1.10              (k5_xboole_0 @ X16 @ X17)))),
% 0.85/1.10      inference('demod', [status(thm)], ['2', '3'])).
% 0.85/1.10  thf('13', plain,
% 0.85/1.10      (![X16 : $i, X17 : $i]:
% 0.85/1.10         ((k2_xboole_0 @ X16 @ X17)
% 0.85/1.10           = (k5_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ 
% 0.85/1.10              (k5_xboole_0 @ X16 @ X17)))),
% 0.85/1.10      inference('demod', [status(thm)], ['2', '3'])).
% 0.85/1.10  thf('14', plain,
% 0.85/1.10      (![X0 : $i, X1 : $i]:
% 0.85/1.10         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 0.85/1.10           = (k5_xboole_0 @ 
% 0.85/1.10              (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0)) @ 
% 0.85/1.10              (k2_xboole_0 @ X1 @ X0)))),
% 0.85/1.10      inference('sup+', [status(thm)], ['12', '13'])).
% 0.85/1.10  thf('15', plain,
% 0.85/1.10      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.85/1.10      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.85/1.10  thf('16', plain,
% 0.85/1.10      (![X0 : $i, X1 : $i]:
% 0.85/1.10         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 0.85/1.10           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 0.85/1.10              (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))))),
% 0.85/1.10      inference('demod', [status(thm)], ['14', '15'])).
% 0.85/1.10  thf('17', plain,
% 0.85/1.10      (((k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.85/1.10         (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.85/1.10         = (k5_xboole_0 @ k1_xboole_0 @ 
% 0.85/1.10            (k3_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.85/1.10             (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))),
% 0.85/1.10      inference('sup+', [status(thm)], ['11', '16'])).
% 0.85/1.10  thf('18', plain,
% 0.85/1.10      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.85/1.10      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.85/1.10  thf(t5_boole, axiom,
% 0.85/1.10    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.85/1.10  thf('19', plain, (![X11 : $i]: ((k5_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.85/1.10      inference('cnf', [status(esa)], [t5_boole])).
% 0.85/1.10  thf('20', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.85/1.10      inference('sup+', [status(thm)], ['18', '19'])).
% 0.85/1.10  thf('21', plain,
% 0.85/1.10      (((k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.85/1.10         (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.85/1.10         = (k3_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.85/1.10            (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))),
% 0.85/1.10      inference('demod', [status(thm)], ['17', '20'])).
% 0.85/1.10  thf('22', plain,
% 0.85/1.10      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.85/1.10      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.85/1.10  thf(t100_xboole_1, axiom,
% 0.85/1.10    (![A:$i,B:$i]:
% 0.85/1.10     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.85/1.10  thf('23', plain,
% 0.85/1.10      (![X5 : $i, X6 : $i]:
% 0.85/1.10         ((k4_xboole_0 @ X5 @ X6)
% 0.85/1.10           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.85/1.10      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.85/1.10  thf('24', plain,
% 0.85/1.10      (![X0 : $i, X1 : $i]:
% 0.85/1.10         ((k4_xboole_0 @ X0 @ X1)
% 0.85/1.10           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.85/1.10      inference('sup+', [status(thm)], ['22', '23'])).
% 0.85/1.10  thf('25', plain,
% 0.85/1.10      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.85/1.10      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.85/1.10  thf(t92_xboole_1, axiom,
% 0.85/1.10    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.85/1.10  thf('26', plain, (![X15 : $i]: ((k5_xboole_0 @ X15 @ X15) = (k1_xboole_0))),
% 0.85/1.10      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.85/1.10  thf(t91_xboole_1, axiom,
% 0.85/1.10    (![A:$i,B:$i,C:$i]:
% 0.85/1.10     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.85/1.10       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.85/1.10  thf('27', plain,
% 0.85/1.10      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.85/1.10         ((k5_xboole_0 @ (k5_xboole_0 @ X12 @ X13) @ X14)
% 0.85/1.10           = (k5_xboole_0 @ X12 @ (k5_xboole_0 @ X13 @ X14)))),
% 0.85/1.10      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.85/1.10  thf('28', plain,
% 0.85/1.10      (![X0 : $i, X1 : $i]:
% 0.85/1.10         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.85/1.10           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.85/1.10      inference('sup+', [status(thm)], ['26', '27'])).
% 0.85/1.10  thf('29', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.85/1.10      inference('sup+', [status(thm)], ['18', '19'])).
% 0.85/1.10  thf('30', plain,
% 0.85/1.10      (![X0 : $i, X1 : $i]:
% 0.85/1.10         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.85/1.10      inference('demod', [status(thm)], ['28', '29'])).
% 0.85/1.10  thf('31', plain,
% 0.85/1.10      (![X0 : $i, X1 : $i]:
% 0.85/1.10         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.85/1.10      inference('sup+', [status(thm)], ['25', '30'])).
% 0.85/1.10  thf('32', plain,
% 0.85/1.10      (![X0 : $i, X1 : $i]:
% 0.85/1.10         ((X1)
% 0.85/1.10           = (k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0)))),
% 0.85/1.10      inference('sup+', [status(thm)], ['24', '31'])).
% 0.85/1.10  thf('33', plain,
% 0.85/1.10      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.85/1.10      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.85/1.10  thf('34', plain,
% 0.85/1.10      (![X0 : $i, X1 : $i]:
% 0.85/1.10         ((X1)
% 0.85/1.10           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 0.85/1.10      inference('demod', [status(thm)], ['32', '33'])).
% 0.85/1.10  thf('35', plain,
% 0.85/1.10      (((k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.85/1.10         = (k5_xboole_0 @ 
% 0.85/1.10            (k4_xboole_0 @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.85/1.10             (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A))) @ 
% 0.85/1.10            (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.85/1.10             (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))),
% 0.85/1.10      inference('sup+', [status(thm)], ['21', '34'])).
% 0.85/1.10  thf('36', plain,
% 0.85/1.10      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.85/1.10      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.85/1.10  thf('37', plain,
% 0.85/1.10      (((k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.85/1.10         = (k5_xboole_0 @ 
% 0.85/1.10            (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.85/1.10             (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))) @ 
% 0.85/1.10            (k4_xboole_0 @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.85/1.10             (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))),
% 0.85/1.10      inference('demod', [status(thm)], ['35', '36'])).
% 0.85/1.10  thf('38', plain,
% 0.85/1.10      (![X0 : $i, X1 : $i]:
% 0.85/1.10         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.85/1.10      inference('demod', [status(thm)], ['28', '29'])).
% 0.85/1.10  thf('39', plain,
% 0.85/1.10      (((k4_xboole_0 @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.85/1.10         (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.85/1.10         = (k5_xboole_0 @ 
% 0.85/1.10            (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.85/1.10             (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))) @ 
% 0.85/1.10            (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))),
% 0.85/1.10      inference('sup+', [status(thm)], ['37', '38'])).
% 0.85/1.10  thf('40', plain,
% 0.85/1.10      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.85/1.10      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.85/1.10  thf('41', plain,
% 0.85/1.10      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.85/1.10      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.85/1.10  thf('42', plain,
% 0.85/1.10      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.85/1.10         ((k5_xboole_0 @ (k5_xboole_0 @ X12 @ X13) @ X14)
% 0.85/1.10           = (k5_xboole_0 @ X12 @ (k5_xboole_0 @ X13 @ X14)))),
% 0.85/1.10      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.85/1.10  thf('43', plain,
% 0.85/1.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.85/1.10         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X2)
% 0.85/1.10           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X2)))),
% 0.85/1.10      inference('sup+', [status(thm)], ['41', '42'])).
% 0.85/1.10  thf('44', plain,
% 0.85/1.10      (((k4_xboole_0 @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.85/1.10         (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.85/1.10         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.85/1.10            (k5_xboole_0 @ sk_B @ 
% 0.85/1.10             (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.85/1.10              (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))))),
% 0.85/1.10      inference('demod', [status(thm)], ['39', '40', '43'])).
% 0.85/1.10  thf('45', plain,
% 0.85/1.10      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.85/1.10         ((k5_xboole_0 @ (k5_xboole_0 @ X12 @ X13) @ X14)
% 0.85/1.10           = (k5_xboole_0 @ X12 @ (k5_xboole_0 @ X13 @ X14)))),
% 0.85/1.10      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.85/1.10  thf('46', plain,
% 0.85/1.10      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.85/1.10      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.85/1.10  thf('47', plain,
% 0.85/1.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.85/1.10         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 0.85/1.10           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.85/1.10      inference('sup+', [status(thm)], ['45', '46'])).
% 0.85/1.10  thf('48', plain,
% 0.85/1.10      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.85/1.10      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.85/1.10  thf('49', plain,
% 0.85/1.10      (((k4_xboole_0 @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.85/1.10         (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.85/1.10         = (k5_xboole_0 @ sk_B @ 
% 0.85/1.10            (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.85/1.10             (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.85/1.10              (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))))),
% 0.85/1.10      inference('demod', [status(thm)], ['44', '47', '48'])).
% 0.85/1.10  thf('50', plain,
% 0.85/1.10      (![X0 : $i, X1 : $i]:
% 0.85/1.10         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.85/1.10      inference('demod', [status(thm)], ['28', '29'])).
% 0.85/1.10  thf('51', plain,
% 0.85/1.10      (((k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.85/1.10         (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.85/1.10          (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))
% 0.85/1.10         = (k5_xboole_0 @ sk_B @ 
% 0.85/1.10            (k4_xboole_0 @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.85/1.10             (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))),
% 0.85/1.10      inference('sup+', [status(thm)], ['49', '50'])).
% 0.85/1.10  thf('52', plain,
% 0.85/1.10      (((k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.85/1.10         = (k5_xboole_0 @ 
% 0.85/1.10            (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.85/1.10             (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))) @ 
% 0.85/1.10            (k4_xboole_0 @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.85/1.10             (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))),
% 0.85/1.10      inference('demod', [status(thm)], ['35', '36'])).
% 0.85/1.10  thf('53', plain,
% 0.85/1.10      (![X0 : $i, X1 : $i]:
% 0.85/1.10         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.85/1.10      inference('sup+', [status(thm)], ['25', '30'])).
% 0.85/1.10  thf('54', plain,
% 0.85/1.10      (((k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.85/1.10         (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.85/1.10         = (k5_xboole_0 @ 
% 0.85/1.10            (k4_xboole_0 @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.85/1.10             (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A))) @ 
% 0.85/1.10            (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))),
% 0.85/1.10      inference('sup+', [status(thm)], ['52', '53'])).
% 0.85/1.10  thf('55', plain,
% 0.85/1.10      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.85/1.10      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.85/1.10  thf('56', plain,
% 0.85/1.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.85/1.10         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X2)
% 0.85/1.10           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X2)))),
% 0.85/1.10      inference('sup+', [status(thm)], ['41', '42'])).
% 0.85/1.10  thf('57', plain,
% 0.85/1.10      (((k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.85/1.10         (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.85/1.10         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.85/1.10            (k5_xboole_0 @ sk_B @ 
% 0.85/1.10             (k4_xboole_0 @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.85/1.10              (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))))),
% 0.85/1.10      inference('demod', [status(thm)], ['54', '55', '56'])).
% 0.85/1.10  thf('58', plain,
% 0.85/1.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.85/1.10         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 0.85/1.10           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.85/1.10      inference('sup+', [status(thm)], ['45', '46'])).
% 0.85/1.10  thf('59', plain,
% 0.85/1.10      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.85/1.10      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.85/1.10  thf('60', plain,
% 0.85/1.10      (((k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.85/1.10         (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.85/1.10         = (k5_xboole_0 @ sk_B @ 
% 0.85/1.10            (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.85/1.10             (k4_xboole_0 @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.85/1.10              (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))))),
% 0.85/1.10      inference('demod', [status(thm)], ['57', '58', '59'])).
% 0.85/1.10  thf('61', plain,
% 0.85/1.10      (![X0 : $i, X1 : $i]:
% 0.85/1.10         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.85/1.10      inference('demod', [status(thm)], ['28', '29'])).
% 0.85/1.10  thf('62', plain,
% 0.85/1.10      (((k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.85/1.10         (k4_xboole_0 @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.85/1.10          (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))
% 0.85/1.10         = (k5_xboole_0 @ sk_B @ 
% 0.85/1.10            (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.85/1.10             (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))),
% 0.85/1.10      inference('sup+', [status(thm)], ['60', '61'])).
% 0.85/1.10  thf('63', plain,
% 0.85/1.10      (![X16 : $i, X17 : $i]:
% 0.85/1.10         ((k2_xboole_0 @ X16 @ X17)
% 0.85/1.10           = (k5_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ 
% 0.85/1.10              (k5_xboole_0 @ X16 @ X17)))),
% 0.85/1.10      inference('demod', [status(thm)], ['2', '3'])).
% 0.85/1.10  thf('64', plain,
% 0.85/1.10      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.85/1.10         ((k5_xboole_0 @ (k5_xboole_0 @ X12 @ X13) @ X14)
% 0.85/1.10           = (k5_xboole_0 @ X12 @ (k5_xboole_0 @ X13 @ X14)))),
% 0.85/1.10      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.85/1.10  thf('65', plain,
% 0.85/1.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.85/1.10         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2)
% 0.85/1.10           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 0.85/1.10              (k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X2)))),
% 0.85/1.10      inference('sup+', [status(thm)], ['63', '64'])).
% 0.85/1.10  thf('66', plain,
% 0.85/1.10      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.85/1.10         ((k5_xboole_0 @ (k5_xboole_0 @ X12 @ X13) @ X14)
% 0.85/1.10           = (k5_xboole_0 @ X12 @ (k5_xboole_0 @ X13 @ X14)))),
% 0.85/1.10      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.85/1.10  thf('67', plain,
% 0.85/1.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.85/1.10         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2)
% 0.85/1.10           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 0.85/1.10              (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X2))))),
% 0.85/1.10      inference('demod', [status(thm)], ['65', '66'])).
% 0.85/1.10  thf('68', plain,
% 0.85/1.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.85/1.10         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 0.85/1.10           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.85/1.10      inference('sup+', [status(thm)], ['45', '46'])).
% 0.85/1.10  thf('69', plain,
% 0.85/1.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.85/1.10         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X2)
% 0.85/1.10           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X2)))),
% 0.85/1.10      inference('sup+', [status(thm)], ['41', '42'])).
% 0.85/1.10  thf('70', plain,
% 0.85/1.10      (![X0 : $i, X1 : $i]:
% 0.85/1.10         ((k4_xboole_0 @ X0 @ X1)
% 0.85/1.10           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.85/1.10      inference('sup+', [status(thm)], ['22', '23'])).
% 0.85/1.10  thf('71', plain,
% 0.85/1.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.85/1.10         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2)
% 0.85/1.10           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ X1))))),
% 0.85/1.10      inference('demod', [status(thm)], ['67', '68', '69', '70'])).
% 0.85/1.10  thf('72', plain,
% 0.85/1.10      (((k5_xboole_0 @ 
% 0.85/1.10         (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.85/1.10          (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))) @ 
% 0.85/1.10         (k1_tarski @ sk_A))
% 0.85/1.10         = (k5_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.85/1.10            (k5_xboole_0 @ sk_B @ 
% 0.85/1.10             (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.85/1.10              (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))))),
% 0.85/1.10      inference('sup+', [status(thm)], ['62', '71'])).
% 0.85/1.10  thf('73', plain,
% 0.85/1.10      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.85/1.10      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.85/1.10  thf('74', plain,
% 0.85/1.10      (((k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.85/1.10         (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.85/1.10          (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))
% 0.85/1.10         = (k5_xboole_0 @ sk_B @ 
% 0.85/1.10            (k4_xboole_0 @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.85/1.10             (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))),
% 0.85/1.10      inference('sup+', [status(thm)], ['49', '50'])).
% 0.85/1.10  thf('75', plain,
% 0.85/1.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.85/1.10         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 0.85/1.10           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.85/1.10      inference('sup+', [status(thm)], ['45', '46'])).
% 0.85/1.10  thf('76', plain,
% 0.85/1.10      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.85/1.10      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.85/1.10  thf('77', plain,
% 0.85/1.10      (((k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.85/1.10         (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.85/1.10         = (k3_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.85/1.10            (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))),
% 0.85/1.10      inference('demod', [status(thm)], ['17', '20'])).
% 0.85/1.10  thf('78', plain,
% 0.85/1.10      (![X5 : $i, X6 : $i]:
% 0.85/1.10         ((k4_xboole_0 @ X5 @ X6)
% 0.85/1.10           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.85/1.10      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.85/1.10  thf('79', plain,
% 0.85/1.10      (((k4_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.85/1.10         (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.85/1.10         = (k5_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.85/1.10            (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.85/1.10             (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))),
% 0.85/1.10      inference('sup+', [status(thm)], ['77', '78'])).
% 0.85/1.10  thf('80', plain,
% 0.85/1.10      (((k5_xboole_0 @ sk_B @ 
% 0.85/1.10         (k4_xboole_0 @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.85/1.10          (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))
% 0.85/1.10         = (k5_xboole_0 @ sk_B @ 
% 0.85/1.10            (k4_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.85/1.10             (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))),
% 0.85/1.10      inference('demod', [status(thm)], ['72', '73', '74', '75', '76', '79'])).
% 0.85/1.10  thf('81', plain,
% 0.85/1.10      (((k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.85/1.10         (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.85/1.10          (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))
% 0.85/1.10         = (k5_xboole_0 @ sk_B @ 
% 0.85/1.10            (k4_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.85/1.10             (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))),
% 0.85/1.10      inference('demod', [status(thm)], ['51', '80'])).
% 0.85/1.10  thf('82', plain,
% 0.85/1.10      (![X0 : $i, X1 : $i]:
% 0.85/1.10         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.85/1.10      inference('sup+', [status(thm)], ['25', '30'])).
% 0.85/1.10  thf('83', plain,
% 0.85/1.10      (((k1_tarski @ sk_A)
% 0.85/1.10         = (k5_xboole_0 @ 
% 0.85/1.10            (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.85/1.10             (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))) @ 
% 0.85/1.10            (k5_xboole_0 @ sk_B @ 
% 0.85/1.10             (k4_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.85/1.10              (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))))),
% 0.85/1.10      inference('sup+', [status(thm)], ['81', '82'])).
% 0.85/1.10  thf('84', plain,
% 0.85/1.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.85/1.10         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 0.85/1.10           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.85/1.10      inference('sup+', [status(thm)], ['45', '46'])).
% 0.85/1.10  thf('85', plain,
% 0.85/1.10      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.85/1.10      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.85/1.10  thf('86', plain,
% 0.85/1.10      (((k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.85/1.10         (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.85/1.10         = (k3_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.85/1.10            (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))),
% 0.85/1.10      inference('demod', [status(thm)], ['17', '20'])).
% 0.85/1.10  thf('87', plain,
% 0.85/1.10      (![X5 : $i, X6 : $i]:
% 0.85/1.10         ((k4_xboole_0 @ X5 @ X6)
% 0.85/1.10           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.85/1.10      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.85/1.10  thf('88', plain,
% 0.85/1.10      (![X0 : $i, X1 : $i]:
% 0.85/1.10         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.85/1.10      inference('sup+', [status(thm)], ['25', '30'])).
% 0.85/1.10  thf('89', plain,
% 0.85/1.10      (![X0 : $i, X1 : $i]:
% 0.85/1.10         ((X1)
% 0.85/1.10           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0)))),
% 0.85/1.10      inference('sup+', [status(thm)], ['87', '88'])).
% 0.85/1.10  thf('90', plain,
% 0.85/1.10      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.85/1.10      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.85/1.10  thf('91', plain,
% 0.85/1.10      (![X0 : $i, X1 : $i]:
% 0.85/1.10         ((X1)
% 0.85/1.10           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 0.85/1.10      inference('demod', [status(thm)], ['89', '90'])).
% 0.85/1.10  thf('92', plain,
% 0.85/1.10      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.85/1.10         = (k5_xboole_0 @ 
% 0.85/1.10            (k4_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.85/1.10             (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))) @ 
% 0.85/1.10            (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.85/1.10             (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))),
% 0.85/1.10      inference('sup+', [status(thm)], ['86', '91'])).
% 0.85/1.10  thf('93', plain,
% 0.85/1.10      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.85/1.10      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.85/1.10  thf('94', plain,
% 0.85/1.10      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.85/1.10         = (k5_xboole_0 @ 
% 0.85/1.10            (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.85/1.10             (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))) @ 
% 0.85/1.10            (k4_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.85/1.10             (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))),
% 0.85/1.10      inference('demod', [status(thm)], ['92', '93'])).
% 0.85/1.10  thf('95', plain,
% 0.85/1.10      (![X5 : $i, X6 : $i]:
% 0.85/1.10         ((k4_xboole_0 @ X5 @ X6)
% 0.85/1.10           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.85/1.10      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.85/1.10  thf('96', plain,
% 0.85/1.10      (((k1_tarski @ sk_A) = (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.85/1.10      inference('demod', [status(thm)], ['83', '84', '85', '94', '95'])).
% 0.85/1.10  thf(t36_xboole_1, axiom,
% 0.85/1.10    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.85/1.10  thf('97', plain,
% 0.85/1.10      (![X9 : $i, X10 : $i]: (r1_tarski @ (k4_xboole_0 @ X9 @ X10) @ X9)),
% 0.85/1.10      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.85/1.10  thf(t28_xboole_1, axiom,
% 0.85/1.10    (![A:$i,B:$i]:
% 0.85/1.10     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.85/1.10  thf('98', plain,
% 0.85/1.10      (![X7 : $i, X8 : $i]:
% 0.85/1.10         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 0.85/1.10      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.85/1.10  thf('99', plain,
% 0.85/1.10      (![X0 : $i, X1 : $i]:
% 0.85/1.10         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 0.85/1.10           = (k4_xboole_0 @ X0 @ X1))),
% 0.85/1.10      inference('sup-', [status(thm)], ['97', '98'])).
% 0.85/1.10  thf('100', plain,
% 0.85/1.10      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.85/1.10      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.85/1.10  thf('101', plain,
% 0.85/1.10      (![X0 : $i, X1 : $i]:
% 0.85/1.10         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.85/1.10           = (k4_xboole_0 @ X0 @ X1))),
% 0.85/1.10      inference('demod', [status(thm)], ['99', '100'])).
% 0.85/1.10  thf('102', plain,
% 0.85/1.10      (![X0 : $i, X1 : $i]:
% 0.85/1.10         ((k4_xboole_0 @ X0 @ X1)
% 0.85/1.10           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.85/1.10      inference('sup+', [status(thm)], ['22', '23'])).
% 0.85/1.10  thf('103', plain,
% 0.85/1.10      (![X0 : $i, X1 : $i]:
% 0.85/1.10         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1)
% 0.85/1.10           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0)))),
% 0.85/1.10      inference('sup+', [status(thm)], ['101', '102'])).
% 0.85/1.10  thf('104', plain, (![X15 : $i]: ((k5_xboole_0 @ X15 @ X15) = (k1_xboole_0))),
% 0.85/1.10      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.85/1.10  thf('105', plain,
% 0.85/1.10      (![X0 : $i, X1 : $i]:
% 0.85/1.10         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1) = (k1_xboole_0))),
% 0.85/1.10      inference('demod', [status(thm)], ['103', '104'])).
% 0.85/1.10  thf('106', plain,
% 0.85/1.10      (![X16 : $i, X17 : $i]:
% 0.85/1.10         ((k2_xboole_0 @ X16 @ X17)
% 0.85/1.10           = (k5_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ 
% 0.85/1.10              (k5_xboole_0 @ X16 @ X17)))),
% 0.85/1.10      inference('demod', [status(thm)], ['2', '3'])).
% 0.85/1.10  thf('107', plain,
% 0.85/1.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.85/1.10         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 0.85/1.10           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.85/1.10      inference('sup+', [status(thm)], ['45', '46'])).
% 0.85/1.10  thf('108', plain,
% 0.85/1.10      (![X0 : $i, X1 : $i]:
% 0.85/1.10         ((k4_xboole_0 @ X0 @ X1)
% 0.85/1.10           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.85/1.10      inference('sup+', [status(thm)], ['22', '23'])).
% 0.85/1.10  thf('109', plain,
% 0.85/1.10      (![X16 : $i, X17 : $i]:
% 0.85/1.10         ((k2_xboole_0 @ X16 @ X17)
% 0.85/1.10           = (k5_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X16)))),
% 0.85/1.10      inference('demod', [status(thm)], ['106', '107', '108'])).
% 0.85/1.10  thf('110', plain,
% 0.85/1.10      (![X0 : $i, X1 : $i]:
% 0.85/1.10         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.85/1.10           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.85/1.10      inference('sup+', [status(thm)], ['105', '109'])).
% 0.85/1.10  thf('111', plain, (![X11 : $i]: ((k5_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.85/1.10      inference('cnf', [status(esa)], [t5_boole])).
% 0.85/1.10  thf('112', plain,
% 0.85/1.10      (![X0 : $i, X1 : $i]:
% 0.85/1.10         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) = (X0))),
% 0.85/1.10      inference('demod', [status(thm)], ['110', '111'])).
% 0.85/1.10  thf('113', plain, (((k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (sk_B))),
% 0.85/1.10      inference('sup+', [status(thm)], ['96', '112'])).
% 0.85/1.10  thf('114', plain,
% 0.85/1.10      (((k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))),
% 0.85/1.10      inference('demod', [status(thm)], ['0', '9'])).
% 0.85/1.10  thf('115', plain, (((sk_B) = (k1_xboole_0))),
% 0.85/1.10      inference('sup+', [status(thm)], ['113', '114'])).
% 0.85/1.10  thf(idempotence_k3_xboole_0, axiom,
% 0.85/1.10    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.85/1.10  thf('116', plain, (![X4 : $i]: ((k3_xboole_0 @ X4 @ X4) = (X4))),
% 0.85/1.10      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.85/1.10  thf('117', plain,
% 0.85/1.10      (![X5 : $i, X6 : $i]:
% 0.85/1.10         ((k4_xboole_0 @ X5 @ X6)
% 0.85/1.10           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.85/1.10      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.85/1.10  thf('118', plain,
% 0.85/1.10      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.85/1.10      inference('sup+', [status(thm)], ['116', '117'])).
% 0.85/1.10  thf('119', plain, (![X15 : $i]: ((k5_xboole_0 @ X15 @ X15) = (k1_xboole_0))),
% 0.85/1.10      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.85/1.10  thf('120', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.85/1.10      inference('sup+', [status(thm)], ['118', '119'])).
% 0.85/1.10  thf('121', plain,
% 0.85/1.10      (![X9 : $i, X10 : $i]: (r1_tarski @ (k4_xboole_0 @ X9 @ X10) @ X9)),
% 0.85/1.10      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.85/1.10  thf('122', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.85/1.10      inference('sup+', [status(thm)], ['120', '121'])).
% 0.85/1.10  thf('123', plain,
% 0.85/1.10      (![X7 : $i, X8 : $i]:
% 0.85/1.10         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 0.85/1.10      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.85/1.10  thf('124', plain,
% 0.85/1.10      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.85/1.10      inference('sup-', [status(thm)], ['122', '123'])).
% 0.85/1.10  thf('125', plain,
% 0.85/1.10      (![X16 : $i, X17 : $i]:
% 0.85/1.10         ((k2_xboole_0 @ X16 @ X17)
% 0.85/1.10           = (k5_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ 
% 0.85/1.10              (k5_xboole_0 @ X16 @ X17)))),
% 0.85/1.10      inference('demod', [status(thm)], ['2', '3'])).
% 0.85/1.10  thf('126', plain,
% 0.85/1.10      (![X0 : $i]:
% 0.85/1.10         ((k2_xboole_0 @ k1_xboole_0 @ X0)
% 0.85/1.10           = (k5_xboole_0 @ k1_xboole_0 @ (k5_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.85/1.10      inference('sup+', [status(thm)], ['124', '125'])).
% 0.85/1.10  thf('127', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.85/1.10      inference('sup+', [status(thm)], ['18', '19'])).
% 0.85/1.10  thf('128', plain,
% 0.85/1.10      (![X0 : $i]:
% 0.85/1.10         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 0.85/1.10      inference('demod', [status(thm)], ['126', '127'])).
% 0.85/1.10  thf('129', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.85/1.10      inference('sup+', [status(thm)], ['18', '19'])).
% 0.85/1.10  thf('130', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.85/1.10      inference('sup+', [status(thm)], ['128', '129'])).
% 0.85/1.10  thf('131', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.85/1.10      inference('demod', [status(thm)], ['10', '115', '130'])).
% 0.85/1.10  thf(t20_zfmisc_1, axiom,
% 0.85/1.10    (![A:$i,B:$i]:
% 0.85/1.10     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.85/1.10         ( k1_tarski @ A ) ) <=>
% 0.85/1.10       ( ( A ) != ( B ) ) ))).
% 0.85/1.10  thf('132', plain,
% 0.85/1.10      (![X48 : $i, X49 : $i]:
% 0.85/1.10         (((X49) != (X48))
% 0.85/1.10          | ((k4_xboole_0 @ (k1_tarski @ X49) @ (k1_tarski @ X48))
% 0.85/1.10              != (k1_tarski @ X49)))),
% 0.85/1.10      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.85/1.10  thf('133', plain,
% 0.85/1.10      (![X48 : $i]:
% 0.85/1.10         ((k4_xboole_0 @ (k1_tarski @ X48) @ (k1_tarski @ X48))
% 0.85/1.10           != (k1_tarski @ X48))),
% 0.85/1.10      inference('simplify', [status(thm)], ['132'])).
% 0.85/1.10  thf('134', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.85/1.10      inference('sup+', [status(thm)], ['118', '119'])).
% 0.85/1.10  thf('135', plain, (![X48 : $i]: ((k1_xboole_0) != (k1_tarski @ X48))),
% 0.85/1.10      inference('demod', [status(thm)], ['133', '134'])).
% 0.85/1.10  thf('136', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.85/1.10      inference('sup-', [status(thm)], ['131', '135'])).
% 0.85/1.10  thf('137', plain, ($false), inference('simplify', [status(thm)], ['136'])).
% 0.85/1.10  
% 0.85/1.10  % SZS output end Refutation
% 0.85/1.10  
% 0.85/1.11  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
