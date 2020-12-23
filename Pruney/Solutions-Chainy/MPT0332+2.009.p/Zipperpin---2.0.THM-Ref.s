%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hFCodO1QyQ

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:08 EST 2020

% Result     : Theorem 1.15s
% Output     : Refutation 1.15s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 591 expanded)
%              Number of leaves         :   23 ( 210 expanded)
%              Depth                    :   23
%              Number of atoms          :  913 (4741 expanded)
%              Number of equality atoms :   95 ( 573 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t145_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r2_hidden @ A @ C )
        & ~ ( r2_hidden @ B @ C )
        & ( C
         != ( k4_xboole_0 @ ( k2_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) @ ( k2_tarski @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ~ ( r2_hidden @ A @ C )
          & ~ ( r2_hidden @ B @ C )
          & ( C
           != ( k4_xboole_0 @ ( k2_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) @ ( k2_tarski @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t145_zfmisc_1])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t144_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r2_hidden @ A @ C )
        & ~ ( r2_hidden @ B @ C )
        & ( C
         != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) )).

thf('1',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( r2_hidden @ X48 @ X49 )
      | ( r2_hidden @ X50 @ X49 )
      | ( X49
        = ( k4_xboole_0 @ X49 @ ( k2_tarski @ X48 @ X50 ) ) ) ) ),
    inference(cnf,[status(esa)],[t144_zfmisc_1])).

thf('2',plain,(
    sk_C
 != ( k4_xboole_0 @ ( k2_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('6',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k3_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X15 @ X16 ) @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf('7',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('8',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k3_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X15 @ X16 ) @ ( k5_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('11',plain,(
    ! [X14: $i] :
      ( ( k5_xboole_0 @ X14 @ X14 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('12',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k5_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('15',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','18'])).

thf('20',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k5_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('21',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','17'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['13','16'])).

thf('27',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k3_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X15 @ X16 ) @ ( k5_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X1 ) ) )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['25','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','24'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','8'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('35',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k3_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X15 @ X16 ) @ ( k5_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('39',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ X8 @ ( k4_xboole_0 @ X9 @ X8 ) )
      = ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('40',plain,(
    ! [X14: $i] :
      ( ( k5_xboole_0 @ X14 @ X14 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','32','37','38','39','40'])).

thf('42',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['43','44'])).

thf(t96_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ) )).

thf('46',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X17 @ X18 ) @ ( k5_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t96_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('47',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_xboole_0 @ X7 @ X6 )
        = X6 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k3_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X15 @ X16 ) @ ( k5_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k5_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k5_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('54',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['13','16'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['56','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['13','16'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','36'])).

thf('65',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['13','16'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['52','55','62','63','68'])).

thf('70',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['45','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['56','59'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','81'])).

thf('83',plain,(
    sk_C
 != ( k4_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','82'])).

thf('84',plain,
    ( ( sk_C != sk_C )
    | ( r2_hidden @ sk_B @ sk_C )
    | ( r2_hidden @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1','83'])).

thf('85',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
    | ( r2_hidden @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    r2_hidden @ sk_B @ sk_C ),
    inference(clc,[status(thm)],['85','86'])).

thf('88',plain,(
    $false ),
    inference(demod,[status(thm)],['0','87'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hFCodO1QyQ
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:45:45 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 1.15/1.33  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.15/1.33  % Solved by: fo/fo7.sh
% 1.15/1.33  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.15/1.33  % done 1487 iterations in 0.866s
% 1.15/1.33  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.15/1.33  % SZS output start Refutation
% 1.15/1.33  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.15/1.33  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.15/1.33  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.15/1.33  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.15/1.33  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.15/1.33  thf(sk_A_type, type, sk_A: $i).
% 1.15/1.33  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.15/1.33  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.15/1.33  thf(sk_C_type, type, sk_C: $i).
% 1.15/1.33  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.15/1.33  thf(sk_B_type, type, sk_B: $i).
% 1.15/1.33  thf(t145_zfmisc_1, conjecture,
% 1.15/1.33    (![A:$i,B:$i,C:$i]:
% 1.15/1.33     ( ~( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) & 
% 1.15/1.33          ( ( C ) !=
% 1.15/1.33            ( k4_xboole_0 @
% 1.15/1.33              ( k2_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) @ 
% 1.15/1.33              ( k2_tarski @ A @ B ) ) ) ) ))).
% 1.15/1.33  thf(zf_stmt_0, negated_conjecture,
% 1.15/1.33    (~( ![A:$i,B:$i,C:$i]:
% 1.15/1.33        ( ~( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) & 
% 1.15/1.33             ( ( C ) !=
% 1.15/1.33               ( k4_xboole_0 @
% 1.15/1.33                 ( k2_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) @ 
% 1.15/1.33                 ( k2_tarski @ A @ B ) ) ) ) ) )),
% 1.15/1.33    inference('cnf.neg', [status(esa)], [t145_zfmisc_1])).
% 1.15/1.33  thf('0', plain, (~ (r2_hidden @ sk_B @ sk_C)),
% 1.15/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.33  thf(t144_zfmisc_1, axiom,
% 1.15/1.33    (![A:$i,B:$i,C:$i]:
% 1.15/1.33     ( ~( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) & 
% 1.15/1.33          ( ( C ) != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) ))).
% 1.15/1.33  thf('1', plain,
% 1.15/1.33      (![X48 : $i, X49 : $i, X50 : $i]:
% 1.15/1.33         ((r2_hidden @ X48 @ X49)
% 1.15/1.33          | (r2_hidden @ X50 @ X49)
% 1.15/1.33          | ((X49) = (k4_xboole_0 @ X49 @ (k2_tarski @ X48 @ X50))))),
% 1.15/1.33      inference('cnf', [status(esa)], [t144_zfmisc_1])).
% 1.15/1.33  thf('2', plain,
% 1.15/1.33      (((sk_C)
% 1.15/1.33         != (k4_xboole_0 @ (k2_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)) @ 
% 1.15/1.33             (k2_tarski @ sk_A @ sk_B)))),
% 1.15/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.33  thf(commutativity_k2_xboole_0, axiom,
% 1.15/1.33    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 1.15/1.33  thf('3', plain,
% 1.15/1.33      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.15/1.33      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.15/1.33  thf('4', plain,
% 1.15/1.33      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.15/1.33      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.15/1.33  thf(commutativity_k5_xboole_0, axiom,
% 1.15/1.33    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 1.15/1.33  thf('5', plain,
% 1.15/1.33      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 1.15/1.33      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.15/1.33  thf(t95_xboole_1, axiom,
% 1.15/1.33    (![A:$i,B:$i]:
% 1.15/1.33     ( ( k3_xboole_0 @ A @ B ) =
% 1.15/1.33       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 1.15/1.33  thf('6', plain,
% 1.15/1.33      (![X15 : $i, X16 : $i]:
% 1.15/1.33         ((k3_xboole_0 @ X15 @ X16)
% 1.15/1.33           = (k5_xboole_0 @ (k5_xboole_0 @ X15 @ X16) @ 
% 1.15/1.33              (k2_xboole_0 @ X15 @ X16)))),
% 1.15/1.33      inference('cnf', [status(esa)], [t95_xboole_1])).
% 1.15/1.33  thf('7', plain,
% 1.15/1.33      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 1.15/1.33      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.15/1.33  thf('8', plain,
% 1.15/1.33      (![X15 : $i, X16 : $i]:
% 1.15/1.33         ((k3_xboole_0 @ X15 @ X16)
% 1.15/1.33           = (k5_xboole_0 @ (k2_xboole_0 @ X15 @ X16) @ 
% 1.15/1.33              (k5_xboole_0 @ X15 @ X16)))),
% 1.15/1.33      inference('demod', [status(thm)], ['6', '7'])).
% 1.15/1.33  thf('9', plain,
% 1.15/1.33      (![X0 : $i, X1 : $i]:
% 1.15/1.33         ((k3_xboole_0 @ X0 @ X1)
% 1.15/1.33           = (k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k5_xboole_0 @ X1 @ X0)))),
% 1.15/1.33      inference('sup+', [status(thm)], ['5', '8'])).
% 1.15/1.33  thf('10', plain,
% 1.15/1.33      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 1.15/1.33      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.15/1.33  thf(t92_xboole_1, axiom,
% 1.15/1.33    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 1.15/1.33  thf('11', plain, (![X14 : $i]: ((k5_xboole_0 @ X14 @ X14) = (k1_xboole_0))),
% 1.15/1.33      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.15/1.33  thf(t91_xboole_1, axiom,
% 1.15/1.33    (![A:$i,B:$i,C:$i]:
% 1.15/1.33     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 1.15/1.33       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 1.15/1.33  thf('12', plain,
% 1.15/1.33      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.15/1.33         ((k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ X13)
% 1.15/1.33           = (k5_xboole_0 @ X11 @ (k5_xboole_0 @ X12 @ X13)))),
% 1.15/1.33      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.15/1.33  thf('13', plain,
% 1.15/1.33      (![X0 : $i, X1 : $i]:
% 1.15/1.33         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 1.15/1.33           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.15/1.33      inference('sup+', [status(thm)], ['11', '12'])).
% 1.15/1.33  thf('14', plain,
% 1.15/1.33      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 1.15/1.33      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.15/1.33  thf(t5_boole, axiom,
% 1.15/1.33    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.15/1.33  thf('15', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 1.15/1.33      inference('cnf', [status(esa)], [t5_boole])).
% 1.15/1.33  thf('16', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.15/1.33      inference('sup+', [status(thm)], ['14', '15'])).
% 1.15/1.33  thf('17', plain,
% 1.15/1.33      (![X0 : $i, X1 : $i]:
% 1.15/1.33         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.15/1.33      inference('demod', [status(thm)], ['13', '16'])).
% 1.15/1.33  thf('18', plain,
% 1.15/1.33      (![X0 : $i, X1 : $i]:
% 1.15/1.33         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.15/1.33      inference('sup+', [status(thm)], ['10', '17'])).
% 1.15/1.33  thf('19', plain,
% 1.15/1.33      (![X0 : $i, X1 : $i]:
% 1.15/1.33         ((k2_xboole_0 @ X1 @ X0)
% 1.15/1.33           = (k5_xboole_0 @ (k5_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X1 @ X0)))),
% 1.15/1.33      inference('sup+', [status(thm)], ['9', '18'])).
% 1.15/1.33  thf('20', plain,
% 1.15/1.33      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.15/1.33         ((k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ X13)
% 1.15/1.33           = (k5_xboole_0 @ X11 @ (k5_xboole_0 @ X12 @ X13)))),
% 1.15/1.33      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.15/1.33  thf(t100_xboole_1, axiom,
% 1.15/1.33    (![A:$i,B:$i]:
% 1.15/1.33     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.15/1.33  thf('21', plain,
% 1.15/1.33      (![X4 : $i, X5 : $i]:
% 1.15/1.33         ((k4_xboole_0 @ X4 @ X5)
% 1.15/1.33           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 1.15/1.33      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.15/1.33  thf('22', plain,
% 1.15/1.33      (![X0 : $i, X1 : $i]:
% 1.15/1.33         ((k2_xboole_0 @ X1 @ X0)
% 1.15/1.33           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.15/1.33      inference('demod', [status(thm)], ['19', '20', '21'])).
% 1.15/1.33  thf('23', plain,
% 1.15/1.33      (![X0 : $i, X1 : $i]:
% 1.15/1.33         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.15/1.33      inference('sup+', [status(thm)], ['10', '17'])).
% 1.15/1.33  thf('24', plain,
% 1.15/1.33      (![X0 : $i, X1 : $i]:
% 1.15/1.33         ((X0)
% 1.15/1.33           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0)))),
% 1.15/1.33      inference('sup+', [status(thm)], ['22', '23'])).
% 1.15/1.33  thf('25', plain,
% 1.15/1.33      (![X0 : $i, X1 : $i]:
% 1.15/1.33         ((X1)
% 1.15/1.33           = (k5_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0)))),
% 1.15/1.33      inference('sup+', [status(thm)], ['4', '24'])).
% 1.15/1.33  thf('26', plain,
% 1.15/1.33      (![X0 : $i, X1 : $i]:
% 1.15/1.33         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.15/1.33      inference('demod', [status(thm)], ['13', '16'])).
% 1.15/1.33  thf('27', plain,
% 1.15/1.33      (![X15 : $i, X16 : $i]:
% 1.15/1.33         ((k3_xboole_0 @ X15 @ X16)
% 1.15/1.33           = (k5_xboole_0 @ (k2_xboole_0 @ X15 @ X16) @ 
% 1.15/1.33              (k5_xboole_0 @ X15 @ X16)))),
% 1.15/1.33      inference('demod', [status(thm)], ['6', '7'])).
% 1.15/1.33  thf('28', plain,
% 1.15/1.33      (![X0 : $i, X1 : $i]:
% 1.15/1.33         ((k3_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0))
% 1.15/1.33           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)) @ X0))),
% 1.15/1.33      inference('sup+', [status(thm)], ['26', '27'])).
% 1.15/1.33  thf('29', plain,
% 1.15/1.33      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 1.15/1.33      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.15/1.33  thf('30', plain,
% 1.15/1.33      (![X0 : $i, X1 : $i]:
% 1.15/1.33         ((k3_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0))
% 1.15/1.33           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0))))),
% 1.15/1.33      inference('demod', [status(thm)], ['28', '29'])).
% 1.15/1.33  thf('31', plain,
% 1.15/1.33      (![X0 : $i, X1 : $i]:
% 1.15/1.33         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 1.15/1.33           (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X1)))
% 1.15/1.33           = (k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ 
% 1.15/1.33              (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)))),
% 1.15/1.33      inference('sup+', [status(thm)], ['25', '30'])).
% 1.15/1.33  thf('32', plain,
% 1.15/1.33      (![X0 : $i, X1 : $i]:
% 1.15/1.33         ((X1)
% 1.15/1.33           = (k5_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0)))),
% 1.15/1.33      inference('sup+', [status(thm)], ['4', '24'])).
% 1.15/1.33  thf('33', plain,
% 1.15/1.33      (![X0 : $i, X1 : $i]:
% 1.15/1.33         ((k3_xboole_0 @ X0 @ X1)
% 1.15/1.33           = (k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k5_xboole_0 @ X1 @ X0)))),
% 1.15/1.33      inference('sup+', [status(thm)], ['5', '8'])).
% 1.15/1.33  thf('34', plain,
% 1.15/1.33      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.15/1.33      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.15/1.33  thf('35', plain,
% 1.15/1.33      (![X15 : $i, X16 : $i]:
% 1.15/1.33         ((k3_xboole_0 @ X15 @ X16)
% 1.15/1.33           = (k5_xboole_0 @ (k2_xboole_0 @ X15 @ X16) @ 
% 1.15/1.33              (k5_xboole_0 @ X15 @ X16)))),
% 1.15/1.33      inference('demod', [status(thm)], ['6', '7'])).
% 1.15/1.33  thf('36', plain,
% 1.15/1.33      (![X0 : $i, X1 : $i]:
% 1.15/1.33         ((k3_xboole_0 @ X0 @ X1)
% 1.15/1.33           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X0 @ X1)))),
% 1.15/1.33      inference('sup+', [status(thm)], ['34', '35'])).
% 1.15/1.33  thf('37', plain,
% 1.15/1.33      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X0 @ X1) = (k3_xboole_0 @ X1 @ X0))),
% 1.15/1.33      inference('sup+', [status(thm)], ['33', '36'])).
% 1.15/1.33  thf('38', plain,
% 1.15/1.33      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.15/1.33      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.15/1.33  thf(t39_xboole_1, axiom,
% 1.15/1.33    (![A:$i,B:$i]:
% 1.15/1.33     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.15/1.33  thf('39', plain,
% 1.15/1.33      (![X8 : $i, X9 : $i]:
% 1.15/1.33         ((k2_xboole_0 @ X8 @ (k4_xboole_0 @ X9 @ X8))
% 1.15/1.33           = (k2_xboole_0 @ X8 @ X9))),
% 1.15/1.33      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.15/1.33  thf('40', plain, (![X14 : $i]: ((k5_xboole_0 @ X14 @ X14) = (k1_xboole_0))),
% 1.15/1.33      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.15/1.33  thf('41', plain,
% 1.15/1.33      (![X0 : $i, X1 : $i]:
% 1.15/1.33         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 1.15/1.33      inference('demod', [status(thm)], ['31', '32', '37', '38', '39', '40'])).
% 1.15/1.33  thf('42', plain,
% 1.15/1.33      (![X4 : $i, X5 : $i]:
% 1.15/1.33         ((k4_xboole_0 @ X4 @ X5)
% 1.15/1.33           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 1.15/1.33      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.15/1.33  thf('43', plain,
% 1.15/1.33      (![X0 : $i, X1 : $i]:
% 1.15/1.33         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 1.15/1.33           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.15/1.33      inference('sup+', [status(thm)], ['41', '42'])).
% 1.15/1.33  thf('44', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 1.15/1.33      inference('cnf', [status(esa)], [t5_boole])).
% 1.15/1.33  thf('45', plain,
% 1.15/1.33      (![X0 : $i, X1 : $i]:
% 1.15/1.33         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 1.15/1.33      inference('demod', [status(thm)], ['43', '44'])).
% 1.15/1.33  thf(t96_xboole_1, axiom,
% 1.15/1.33    (![A:$i,B:$i]:
% 1.15/1.33     ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ))).
% 1.15/1.33  thf('46', plain,
% 1.15/1.33      (![X17 : $i, X18 : $i]:
% 1.15/1.33         (r1_tarski @ (k4_xboole_0 @ X17 @ X18) @ (k5_xboole_0 @ X17 @ X18))),
% 1.15/1.33      inference('cnf', [status(esa)], [t96_xboole_1])).
% 1.15/1.33  thf(t12_xboole_1, axiom,
% 1.15/1.33    (![A:$i,B:$i]:
% 1.15/1.33     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 1.15/1.33  thf('47', plain,
% 1.15/1.33      (![X6 : $i, X7 : $i]:
% 1.15/1.33         (((k2_xboole_0 @ X7 @ X6) = (X6)) | ~ (r1_tarski @ X7 @ X6))),
% 1.15/1.33      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.15/1.33  thf('48', plain,
% 1.15/1.33      (![X0 : $i, X1 : $i]:
% 1.15/1.33         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 1.15/1.33           = (k5_xboole_0 @ X1 @ X0))),
% 1.15/1.33      inference('sup-', [status(thm)], ['46', '47'])).
% 1.15/1.33  thf('49', plain,
% 1.15/1.33      (![X15 : $i, X16 : $i]:
% 1.15/1.33         ((k3_xboole_0 @ X15 @ X16)
% 1.15/1.33           = (k5_xboole_0 @ (k2_xboole_0 @ X15 @ X16) @ 
% 1.15/1.33              (k5_xboole_0 @ X15 @ X16)))),
% 1.15/1.33      inference('demod', [status(thm)], ['6', '7'])).
% 1.15/1.33  thf('50', plain,
% 1.15/1.33      (![X0 : $i, X1 : $i]:
% 1.15/1.33         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 1.15/1.33           = (k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ 
% 1.15/1.33              (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))))),
% 1.15/1.33      inference('sup+', [status(thm)], ['48', '49'])).
% 1.15/1.33  thf('51', plain,
% 1.15/1.33      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.15/1.33         ((k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ X13)
% 1.15/1.33           = (k5_xboole_0 @ X11 @ (k5_xboole_0 @ X12 @ X13)))),
% 1.15/1.33      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.15/1.33  thf('52', plain,
% 1.15/1.33      (![X0 : $i, X1 : $i]:
% 1.15/1.33         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 1.15/1.33           = (k5_xboole_0 @ X1 @ 
% 1.15/1.33              (k5_xboole_0 @ X0 @ 
% 1.15/1.33               (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0)))))),
% 1.15/1.33      inference('demod', [status(thm)], ['50', '51'])).
% 1.15/1.33  thf('53', plain,
% 1.15/1.33      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.15/1.33         ((k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ X13)
% 1.15/1.33           = (k5_xboole_0 @ X11 @ (k5_xboole_0 @ X12 @ X13)))),
% 1.15/1.33      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.15/1.33  thf('54', plain,
% 1.15/1.33      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 1.15/1.33      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.15/1.33  thf('55', plain,
% 1.15/1.33      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.15/1.33         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 1.15/1.33           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.15/1.33      inference('sup+', [status(thm)], ['53', '54'])).
% 1.15/1.33  thf('56', plain,
% 1.15/1.33      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.15/1.33      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.15/1.33  thf('57', plain,
% 1.15/1.33      (![X0 : $i, X1 : $i]:
% 1.15/1.33         ((k2_xboole_0 @ X1 @ X0)
% 1.15/1.33           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.15/1.33      inference('demod', [status(thm)], ['19', '20', '21'])).
% 1.15/1.33  thf('58', plain,
% 1.15/1.33      (![X0 : $i, X1 : $i]:
% 1.15/1.33         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.15/1.33      inference('demod', [status(thm)], ['13', '16'])).
% 1.15/1.33  thf('59', plain,
% 1.15/1.33      (![X0 : $i, X1 : $i]:
% 1.15/1.33         ((k4_xboole_0 @ X1 @ X0)
% 1.15/1.33           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.15/1.33      inference('sup+', [status(thm)], ['57', '58'])).
% 1.15/1.33  thf('60', plain,
% 1.15/1.33      (![X0 : $i, X1 : $i]:
% 1.15/1.33         ((k4_xboole_0 @ X0 @ X1)
% 1.15/1.33           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.15/1.33      inference('sup+', [status(thm)], ['56', '59'])).
% 1.15/1.33  thf('61', plain,
% 1.15/1.33      (![X0 : $i, X1 : $i]:
% 1.15/1.33         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.15/1.33      inference('demod', [status(thm)], ['13', '16'])).
% 1.15/1.33  thf('62', plain,
% 1.15/1.33      (![X0 : $i, X1 : $i]:
% 1.15/1.33         ((k2_xboole_0 @ X0 @ X1)
% 1.15/1.33           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.15/1.33      inference('sup+', [status(thm)], ['60', '61'])).
% 1.15/1.33  thf('63', plain,
% 1.15/1.33      (![X0 : $i, X1 : $i]:
% 1.15/1.33         ((k4_xboole_0 @ X1 @ X0)
% 1.15/1.33           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.15/1.33      inference('sup+', [status(thm)], ['57', '58'])).
% 1.15/1.33  thf('64', plain,
% 1.15/1.33      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X0 @ X1) = (k3_xboole_0 @ X1 @ X0))),
% 1.15/1.33      inference('sup+', [status(thm)], ['33', '36'])).
% 1.15/1.33  thf('65', plain,
% 1.15/1.33      (![X4 : $i, X5 : $i]:
% 1.15/1.33         ((k4_xboole_0 @ X4 @ X5)
% 1.15/1.33           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 1.15/1.33      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.15/1.33  thf('66', plain,
% 1.15/1.33      (![X0 : $i, X1 : $i]:
% 1.15/1.33         ((k4_xboole_0 @ X0 @ X1)
% 1.15/1.33           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.15/1.33      inference('sup+', [status(thm)], ['64', '65'])).
% 1.15/1.33  thf('67', plain,
% 1.15/1.33      (![X0 : $i, X1 : $i]:
% 1.15/1.33         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.15/1.33      inference('demod', [status(thm)], ['13', '16'])).
% 1.15/1.33  thf('68', plain,
% 1.15/1.33      (![X0 : $i, X1 : $i]:
% 1.15/1.33         ((k3_xboole_0 @ X0 @ X1)
% 1.15/1.33           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.15/1.33      inference('sup+', [status(thm)], ['66', '67'])).
% 1.15/1.33  thf('69', plain,
% 1.15/1.33      (![X0 : $i, X1 : $i]:
% 1.15/1.33         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 1.15/1.33           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.15/1.33      inference('demod', [status(thm)], ['52', '55', '62', '63', '68'])).
% 1.15/1.33  thf('70', plain,
% 1.15/1.33      (![X4 : $i, X5 : $i]:
% 1.15/1.33         ((k4_xboole_0 @ X4 @ X5)
% 1.15/1.33           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 1.15/1.33      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.15/1.33  thf('71', plain,
% 1.15/1.33      (![X0 : $i, X1 : $i]:
% 1.15/1.33         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 1.15/1.33           = (k4_xboole_0 @ X1 @ X0))),
% 1.15/1.33      inference('demod', [status(thm)], ['69', '70'])).
% 1.15/1.33  thf('72', plain,
% 1.15/1.33      (![X0 : $i, X1 : $i]:
% 1.15/1.33         ((k3_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))
% 1.15/1.33           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.15/1.33      inference('sup+', [status(thm)], ['45', '71'])).
% 1.15/1.33  thf('73', plain,
% 1.15/1.33      (![X0 : $i, X1 : $i]:
% 1.15/1.33         ((k2_xboole_0 @ X0 @ X1)
% 1.15/1.33           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.15/1.33      inference('sup+', [status(thm)], ['60', '61'])).
% 1.15/1.33  thf('74', plain,
% 1.15/1.33      (![X0 : $i, X1 : $i]:
% 1.15/1.33         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 1.15/1.33      inference('demod', [status(thm)], ['43', '44'])).
% 1.15/1.33  thf('75', plain,
% 1.15/1.33      (![X0 : $i, X1 : $i]:
% 1.15/1.33         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)) = (X0))),
% 1.15/1.33      inference('demod', [status(thm)], ['72', '73', '74'])).
% 1.15/1.33  thf('76', plain,
% 1.15/1.33      (![X0 : $i, X1 : $i]:
% 1.15/1.33         ((k4_xboole_0 @ X0 @ X1)
% 1.15/1.33           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.15/1.33      inference('sup+', [status(thm)], ['64', '65'])).
% 1.15/1.33  thf('77', plain,
% 1.15/1.33      (![X0 : $i, X1 : $i]:
% 1.15/1.33         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0)
% 1.15/1.33           = (k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 1.15/1.33      inference('sup+', [status(thm)], ['75', '76'])).
% 1.15/1.33  thf('78', plain,
% 1.15/1.33      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 1.15/1.33      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.15/1.33  thf('79', plain,
% 1.15/1.33      (![X0 : $i, X1 : $i]:
% 1.15/1.33         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0)
% 1.15/1.33           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 1.15/1.33      inference('demod', [status(thm)], ['77', '78'])).
% 1.15/1.33  thf('80', plain,
% 1.15/1.33      (![X0 : $i, X1 : $i]:
% 1.15/1.33         ((k4_xboole_0 @ X0 @ X1)
% 1.15/1.33           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.15/1.33      inference('sup+', [status(thm)], ['56', '59'])).
% 1.15/1.33  thf('81', plain,
% 1.15/1.33      (![X0 : $i, X1 : $i]:
% 1.15/1.33         ((k4_xboole_0 @ X1 @ X0)
% 1.15/1.33           = (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 1.15/1.33      inference('sup+', [status(thm)], ['79', '80'])).
% 1.15/1.33  thf('82', plain,
% 1.15/1.33      (![X0 : $i, X1 : $i]:
% 1.15/1.33         ((k4_xboole_0 @ X1 @ X0)
% 1.15/1.33           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 1.15/1.33      inference('sup+', [status(thm)], ['3', '81'])).
% 1.15/1.33  thf('83', plain,
% 1.15/1.33      (((sk_C) != (k4_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)))),
% 1.15/1.33      inference('demod', [status(thm)], ['2', '82'])).
% 1.15/1.33  thf('84', plain,
% 1.15/1.33      ((((sk_C) != (sk_C))
% 1.15/1.33        | (r2_hidden @ sk_B @ sk_C)
% 1.15/1.33        | (r2_hidden @ sk_A @ sk_C))),
% 1.15/1.33      inference('sup-', [status(thm)], ['1', '83'])).
% 1.15/1.33  thf('85', plain, (((r2_hidden @ sk_A @ sk_C) | (r2_hidden @ sk_B @ sk_C))),
% 1.15/1.33      inference('simplify', [status(thm)], ['84'])).
% 1.15/1.33  thf('86', plain, (~ (r2_hidden @ sk_A @ sk_C)),
% 1.15/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.33  thf('87', plain, ((r2_hidden @ sk_B @ sk_C)),
% 1.15/1.33      inference('clc', [status(thm)], ['85', '86'])).
% 1.15/1.33  thf('88', plain, ($false), inference('demod', [status(thm)], ['0', '87'])).
% 1.15/1.33  
% 1.15/1.33  % SZS output end Refutation
% 1.15/1.33  
% 1.15/1.34  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
