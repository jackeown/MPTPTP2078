%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.agSmOaWc7l

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:25 EST 2020

% Result     : Theorem 0.52s
% Output     : Refutation 0.52s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 225 expanded)
%              Number of leaves         :   22 (  82 expanded)
%              Depth                    :   19
%              Number of atoms          :  680 (1532 expanded)
%              Number of equality atoms :   69 ( 169 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('0',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('1',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('2',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t54_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B )
        & ( r2_hidden @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B )
          & ( r2_hidden @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t54_zfmisc_1])).

thf('3',plain,(
    r1_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t76_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ ( k3_xboole_0 @ C @ A ) @ ( k3_xboole_0 @ C @ B ) ) ) )).

thf('4',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r1_xboole_0 @ X19 @ X20 )
      | ( r1_xboole_0 @ ( k3_xboole_0 @ X21 @ X19 ) @ ( k3_xboole_0 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t76_xboole_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) @ ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    r1_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['2','5'])).

thf('7',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r1_xboole_0 @ X19 @ X20 )
      | ( r1_xboole_0 @ ( k3_xboole_0 @ X21 @ X19 ) @ ( k3_xboole_0 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t76_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) @ ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r1_xboole_0 @ X19 @ X20 )
      | ( r1_xboole_0 @ ( k3_xboole_0 @ X21 @ X19 ) @ ( k3_xboole_0 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t76_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) ) @ ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) @ ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) @ ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup+',[status(thm)],['1','10'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('12',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('13',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('14',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('16',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['19','20'])).

thf(t54_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ C ) ) ) )).

thf('22',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k3_xboole_0 @ X14 @ X15 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ ( k4_xboole_0 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t54_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ k1_xboole_0 @ X1 ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('25',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X12 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['23','26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('32',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k3_xboole_0 @ X14 @ X15 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ ( k4_xboole_0 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t54_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('34',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) )
      = ( k4_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf(t71_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( ( k2_xboole_0 @ A @ B )
          = ( k2_xboole_0 @ C @ B ) )
        & ( r1_xboole_0 @ A @ B )
        & ( r1_xboole_0 @ C @ B ) )
     => ( A = C ) ) )).

thf('39',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r1_xboole_0 @ X16 @ X17 )
      | ( ( k2_xboole_0 @ X16 @ X17 )
       != ( k2_xboole_0 @ X18 @ X17 ) )
      | ~ ( r1_xboole_0 @ X18 @ X17 )
      | ( X16 = X18 ) ) ),
    inference(cnf,[status(esa)],[t71_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ X1 @ X0 )
       != X0 )
      | ( X1 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X12 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('42',plain,(
    ! [X22: $i,X23: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X22 @ X23 ) @ X23 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ X1 @ X0 )
       != X0 )
      | ( X1 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
       != ( k3_xboole_0 @ X0 @ X1 ) )
      | ~ ( r1_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['29','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) )
       != ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) @ ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['11','45'])).

thf('47',plain,
    ( ( ( k3_xboole_0 @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ ( k1_tarski @ sk_A ) )
     != ( k3_xboole_0 @ ( k3_xboole_0 @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ ( k1_tarski @ sk_A ) ) @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) )
    | ( ( k3_xboole_0 @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','46'])).

thf('48',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('49',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ k1_xboole_0 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('56',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('58',plain,
    ( ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    | ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['47','54','55','56','57'])).

thf('59',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) )
      = ( k4_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('61',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 )
    = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('63',plain,
    ( ( k1_tarski @ sk_A )
    = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['61','62'])).

thf(l33_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
    <=> ~ ( r2_hidden @ A @ B ) ) )).

thf('64',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( r2_hidden @ X29 @ X30 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X29 ) @ X30 )
       != ( k1_tarski @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[l33_zfmisc_1])).

thf('65',plain,
    ( ( ( k1_tarski @ sk_A )
     != ( k1_tarski @ sk_A ) )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ( k1_tarski @ sk_A )
 != ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    $false ),
    inference(simplify,[status(thm)],['67'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.agSmOaWc7l
% 0.15/0.34  % Computer   : n015.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 17:43:53 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.35  % Running in FO mode
% 0.52/0.75  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.52/0.75  % Solved by: fo/fo7.sh
% 0.52/0.75  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.52/0.75  % done 442 iterations in 0.292s
% 0.52/0.75  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.52/0.75  % SZS output start Refutation
% 0.52/0.75  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.52/0.75  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.52/0.75  thf(sk_B_type, type, sk_B: $i).
% 0.52/0.75  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.52/0.75  thf(sk_A_type, type, sk_A: $i).
% 0.52/0.75  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.52/0.75  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.52/0.75  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.52/0.75  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.52/0.75  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.52/0.75  thf(idempotence_k3_xboole_0, axiom,
% 0.52/0.75    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.52/0.75  thf('0', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 0.52/0.75      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.52/0.75  thf('1', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 0.52/0.75      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.52/0.75  thf('2', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 0.52/0.75      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.52/0.75  thf(t54_zfmisc_1, conjecture,
% 0.52/0.75    (![A:$i,B:$i]:
% 0.52/0.75     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) & ( r2_hidden @ A @ B ) ) ))).
% 0.52/0.75  thf(zf_stmt_0, negated_conjecture,
% 0.52/0.75    (~( ![A:$i,B:$i]:
% 0.52/0.75        ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) & ( r2_hidden @ A @ B ) ) ) )),
% 0.52/0.75    inference('cnf.neg', [status(esa)], [t54_zfmisc_1])).
% 0.52/0.75  thf('3', plain, ((r1_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)),
% 0.52/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.75  thf(t76_xboole_1, axiom,
% 0.52/0.75    (![A:$i,B:$i,C:$i]:
% 0.52/0.75     ( ( r1_xboole_0 @ A @ B ) =>
% 0.52/0.75       ( r1_xboole_0 @ ( k3_xboole_0 @ C @ A ) @ ( k3_xboole_0 @ C @ B ) ) ))).
% 0.52/0.75  thf('4', plain,
% 0.52/0.75      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.52/0.75         (~ (r1_xboole_0 @ X19 @ X20)
% 0.52/0.75          | (r1_xboole_0 @ (k3_xboole_0 @ X21 @ X19) @ 
% 0.52/0.75             (k3_xboole_0 @ X21 @ X20)))),
% 0.52/0.75      inference('cnf', [status(esa)], [t76_xboole_1])).
% 0.52/0.75  thf('5', plain,
% 0.52/0.75      (![X0 : $i]:
% 0.52/0.75         (r1_xboole_0 @ (k3_xboole_0 @ X0 @ (k1_tarski @ sk_A)) @ 
% 0.52/0.75          (k3_xboole_0 @ X0 @ sk_B))),
% 0.52/0.75      inference('sup-', [status(thm)], ['3', '4'])).
% 0.52/0.75  thf('6', plain,
% 0.52/0.75      ((r1_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.52/0.75        (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 0.52/0.75      inference('sup+', [status(thm)], ['2', '5'])).
% 0.52/0.75  thf('7', plain,
% 0.52/0.75      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.52/0.75         (~ (r1_xboole_0 @ X19 @ X20)
% 0.52/0.75          | (r1_xboole_0 @ (k3_xboole_0 @ X21 @ X19) @ 
% 0.52/0.75             (k3_xboole_0 @ X21 @ X20)))),
% 0.52/0.75      inference('cnf', [status(esa)], [t76_xboole_1])).
% 0.52/0.75  thf('8', plain,
% 0.52/0.75      (![X0 : $i]:
% 0.52/0.75         (r1_xboole_0 @ (k3_xboole_0 @ X0 @ (k1_tarski @ sk_A)) @ 
% 0.52/0.75          (k3_xboole_0 @ X0 @ (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.52/0.75      inference('sup-', [status(thm)], ['6', '7'])).
% 0.52/0.75  thf('9', plain,
% 0.52/0.75      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.52/0.75         (~ (r1_xboole_0 @ X19 @ X20)
% 0.52/0.75          | (r1_xboole_0 @ (k3_xboole_0 @ X21 @ X19) @ 
% 0.52/0.75             (k3_xboole_0 @ X21 @ X20)))),
% 0.52/0.75      inference('cnf', [status(esa)], [t76_xboole_1])).
% 0.52/0.75  thf('10', plain,
% 0.52/0.75      (![X0 : $i, X1 : $i]:
% 0.52/0.75         (r1_xboole_0 @ 
% 0.52/0.75          (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ (k1_tarski @ sk_A))) @ 
% 0.52/0.75          (k3_xboole_0 @ X1 @ 
% 0.52/0.75           (k3_xboole_0 @ X0 @ (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))))),
% 0.52/0.75      inference('sup-', [status(thm)], ['8', '9'])).
% 0.52/0.75  thf('11', plain,
% 0.52/0.75      (![X0 : $i]:
% 0.52/0.75         (r1_xboole_0 @ (k3_xboole_0 @ X0 @ (k1_tarski @ sk_A)) @ 
% 0.52/0.75          (k3_xboole_0 @ (k3_xboole_0 @ X0 @ (k1_tarski @ sk_A)) @ 
% 0.52/0.75           (k3_xboole_0 @ X0 @ (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))))),
% 0.52/0.75      inference('sup+', [status(thm)], ['1', '10'])).
% 0.52/0.75  thf(t48_xboole_1, axiom,
% 0.52/0.75    (![A:$i,B:$i]:
% 0.52/0.75     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.52/0.75  thf('12', plain,
% 0.52/0.75      (![X10 : $i, X11 : $i]:
% 0.52/0.75         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 0.52/0.75           = (k3_xboole_0 @ X10 @ X11))),
% 0.52/0.75      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.52/0.75  thf('13', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 0.52/0.75      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.52/0.75  thf(t17_xboole_1, axiom,
% 0.52/0.75    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.52/0.75  thf('14', plain,
% 0.52/0.75      (![X6 : $i, X7 : $i]: (r1_tarski @ (k3_xboole_0 @ X6 @ X7) @ X6)),
% 0.52/0.75      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.52/0.75  thf('15', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.52/0.75      inference('sup+', [status(thm)], ['13', '14'])).
% 0.52/0.75  thf(l32_xboole_1, axiom,
% 0.52/0.75    (![A:$i,B:$i]:
% 0.52/0.75     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.52/0.75  thf('16', plain,
% 0.52/0.75      (![X3 : $i, X5 : $i]:
% 0.52/0.75         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.52/0.75      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.52/0.75  thf('17', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.52/0.75      inference('sup-', [status(thm)], ['15', '16'])).
% 0.52/0.75  thf('18', plain,
% 0.52/0.75      (![X10 : $i, X11 : $i]:
% 0.52/0.75         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 0.52/0.75           = (k3_xboole_0 @ X10 @ X11))),
% 0.52/0.75      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.52/0.75  thf('19', plain,
% 0.52/0.75      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.52/0.75      inference('sup+', [status(thm)], ['17', '18'])).
% 0.52/0.75  thf('20', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 0.52/0.75      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.52/0.75  thf('21', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.52/0.75      inference('demod', [status(thm)], ['19', '20'])).
% 0.52/0.75  thf(t54_xboole_1, axiom,
% 0.52/0.75    (![A:$i,B:$i,C:$i]:
% 0.52/0.75     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) =
% 0.52/0.75       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ C ) ) ))).
% 0.52/0.75  thf('22', plain,
% 0.52/0.75      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.52/0.75         ((k4_xboole_0 @ X13 @ (k3_xboole_0 @ X14 @ X15))
% 0.52/0.75           = (k2_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ 
% 0.52/0.75              (k4_xboole_0 @ X13 @ X15)))),
% 0.52/0.75      inference('cnf', [status(esa)], [t54_xboole_1])).
% 0.52/0.75  thf('23', plain,
% 0.52/0.75      (![X0 : $i, X1 : $i]:
% 0.52/0.75         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ k1_xboole_0 @ X1))
% 0.52/0.75           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.52/0.75      inference('sup+', [status(thm)], ['21', '22'])).
% 0.52/0.75  thf('24', plain,
% 0.52/0.75      (![X10 : $i, X11 : $i]:
% 0.52/0.75         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 0.52/0.75           = (k3_xboole_0 @ X10 @ X11))),
% 0.52/0.75      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.52/0.75  thf(t4_boole, axiom,
% 0.52/0.75    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.52/0.75  thf('25', plain,
% 0.52/0.75      (![X12 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X12) = (k1_xboole_0))),
% 0.52/0.75      inference('cnf', [status(esa)], [t4_boole])).
% 0.52/0.75  thf('26', plain,
% 0.52/0.75      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.52/0.75      inference('sup+', [status(thm)], ['24', '25'])).
% 0.52/0.75  thf('27', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.52/0.75      inference('demod', [status(thm)], ['19', '20'])).
% 0.52/0.75  thf('28', plain,
% 0.52/0.75      (![X0 : $i, X1 : $i]:
% 0.52/0.75         ((X0) = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.52/0.75      inference('demod', [status(thm)], ['23', '26', '27'])).
% 0.52/0.75  thf('29', plain,
% 0.52/0.75      (![X0 : $i, X1 : $i]:
% 0.52/0.75         ((X1) = (k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.52/0.75      inference('sup+', [status(thm)], ['12', '28'])).
% 0.52/0.75  thf('30', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.52/0.75      inference('demod', [status(thm)], ['19', '20'])).
% 0.52/0.75  thf('31', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.52/0.75      inference('sup-', [status(thm)], ['15', '16'])).
% 0.52/0.75  thf('32', plain,
% 0.52/0.75      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.52/0.75         ((k4_xboole_0 @ X13 @ (k3_xboole_0 @ X14 @ X15))
% 0.52/0.75           = (k2_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ 
% 0.52/0.75              (k4_xboole_0 @ X13 @ X15)))),
% 0.52/0.75      inference('cnf', [status(esa)], [t54_xboole_1])).
% 0.52/0.75  thf('33', plain,
% 0.52/0.75      (![X0 : $i, X1 : $i]:
% 0.52/0.75         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.52/0.75           = (k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.52/0.75      inference('sup+', [status(thm)], ['31', '32'])).
% 0.52/0.75  thf(t47_xboole_1, axiom,
% 0.52/0.75    (![A:$i,B:$i]:
% 0.52/0.75     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.52/0.75  thf('34', plain,
% 0.52/0.75      (![X8 : $i, X9 : $i]:
% 0.52/0.75         ((k4_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9))
% 0.52/0.75           = (k4_xboole_0 @ X8 @ X9))),
% 0.52/0.75      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.52/0.75  thf('35', plain,
% 0.52/0.75      (![X0 : $i, X1 : $i]:
% 0.52/0.75         ((k4_xboole_0 @ X1 @ X0)
% 0.52/0.75           = (k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.52/0.75      inference('demod', [status(thm)], ['33', '34'])).
% 0.52/0.75  thf('36', plain,
% 0.52/0.75      (![X0 : $i]:
% 0.52/0.75         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 0.52/0.75      inference('sup+', [status(thm)], ['30', '35'])).
% 0.52/0.75  thf('37', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.52/0.75      inference('demod', [status(thm)], ['19', '20'])).
% 0.52/0.75  thf('38', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.52/0.75      inference('sup+', [status(thm)], ['36', '37'])).
% 0.52/0.75  thf(t71_xboole_1, axiom,
% 0.52/0.75    (![A:$i,B:$i,C:$i]:
% 0.52/0.75     ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ B ) ) & 
% 0.52/0.75         ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ C @ B ) ) =>
% 0.52/0.75       ( ( A ) = ( C ) ) ))).
% 0.52/0.75  thf('39', plain,
% 0.52/0.75      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.52/0.75         (~ (r1_xboole_0 @ X16 @ X17)
% 0.52/0.75          | ((k2_xboole_0 @ X16 @ X17) != (k2_xboole_0 @ X18 @ X17))
% 0.52/0.75          | ~ (r1_xboole_0 @ X18 @ X17)
% 0.52/0.75          | ((X16) = (X18)))),
% 0.52/0.75      inference('cnf', [status(esa)], [t71_xboole_1])).
% 0.52/0.75  thf('40', plain,
% 0.52/0.75      (![X0 : $i, X1 : $i]:
% 0.52/0.75         (((k2_xboole_0 @ X1 @ X0) != (X0))
% 0.52/0.75          | ((X1) = (k1_xboole_0))
% 0.52/0.75          | ~ (r1_xboole_0 @ k1_xboole_0 @ X0)
% 0.52/0.75          | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.52/0.75      inference('sup-', [status(thm)], ['38', '39'])).
% 0.52/0.75  thf('41', plain,
% 0.52/0.75      (![X12 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X12) = (k1_xboole_0))),
% 0.52/0.75      inference('cnf', [status(esa)], [t4_boole])).
% 0.52/0.75  thf(t79_xboole_1, axiom,
% 0.52/0.75    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.52/0.75  thf('42', plain,
% 0.52/0.75      (![X22 : $i, X23 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X22 @ X23) @ X23)),
% 0.52/0.75      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.52/0.75  thf('43', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.52/0.75      inference('sup+', [status(thm)], ['41', '42'])).
% 0.52/0.75  thf('44', plain,
% 0.52/0.75      (![X0 : $i, X1 : $i]:
% 0.52/0.75         (((k2_xboole_0 @ X1 @ X0) != (X0))
% 0.52/0.75          | ((X1) = (k1_xboole_0))
% 0.52/0.75          | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.52/0.75      inference('demod', [status(thm)], ['40', '43'])).
% 0.52/0.75  thf('45', plain,
% 0.52/0.75      (![X0 : $i, X1 : $i]:
% 0.52/0.75         (((X0) != (k3_xboole_0 @ X0 @ X1))
% 0.52/0.75          | ~ (r1_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 0.52/0.75          | ((X0) = (k1_xboole_0)))),
% 0.52/0.75      inference('sup-', [status(thm)], ['29', '44'])).
% 0.52/0.75  thf('46', plain,
% 0.52/0.75      (![X0 : $i]:
% 0.52/0.75         (((k3_xboole_0 @ X0 @ (k1_tarski @ sk_A)) = (k1_xboole_0))
% 0.52/0.75          | ((k3_xboole_0 @ X0 @ (k1_tarski @ sk_A))
% 0.52/0.75              != (k3_xboole_0 @ (k3_xboole_0 @ X0 @ (k1_tarski @ sk_A)) @ 
% 0.52/0.75                  (k3_xboole_0 @ X0 @ (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)))))),
% 0.52/0.75      inference('sup-', [status(thm)], ['11', '45'])).
% 0.52/0.75  thf('47', plain,
% 0.52/0.75      ((((k3_xboole_0 @ (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ 
% 0.52/0.75          (k1_tarski @ sk_A))
% 0.52/0.75          != (k3_xboole_0 @ 
% 0.52/0.75              (k3_xboole_0 @ (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ 
% 0.52/0.75               (k1_tarski @ sk_A)) @ 
% 0.52/0.75              (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)))
% 0.52/0.75        | ((k3_xboole_0 @ (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ 
% 0.52/0.75            (k1_tarski @ sk_A)) = (k1_xboole_0)))),
% 0.52/0.75      inference('sup-', [status(thm)], ['0', '46'])).
% 0.52/0.75  thf('48', plain,
% 0.52/0.75      (![X6 : $i, X7 : $i]: (r1_tarski @ (k3_xboole_0 @ X6 @ X7) @ X6)),
% 0.52/0.75      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.52/0.75  thf('49', plain,
% 0.52/0.75      (![X3 : $i, X5 : $i]:
% 0.52/0.75         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.52/0.75      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.52/0.75  thf('50', plain,
% 0.52/0.75      (![X0 : $i, X1 : $i]:
% 0.52/0.75         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.52/0.75      inference('sup-', [status(thm)], ['48', '49'])).
% 0.52/0.75  thf('51', plain,
% 0.52/0.75      (![X10 : $i, X11 : $i]:
% 0.52/0.75         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 0.52/0.75           = (k3_xboole_0 @ X10 @ X11))),
% 0.52/0.75      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.52/0.75  thf('52', plain,
% 0.52/0.75      (![X0 : $i, X1 : $i]:
% 0.52/0.75         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ k1_xboole_0)
% 0.52/0.75           = (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 0.52/0.75      inference('sup+', [status(thm)], ['50', '51'])).
% 0.52/0.75  thf('53', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.52/0.75      inference('demod', [status(thm)], ['19', '20'])).
% 0.52/0.75  thf('54', plain,
% 0.52/0.75      (![X0 : $i, X1 : $i]:
% 0.52/0.75         ((k3_xboole_0 @ X0 @ X1)
% 0.52/0.75           = (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 0.52/0.75      inference('demod', [status(thm)], ['52', '53'])).
% 0.52/0.75  thf('55', plain,
% 0.52/0.75      (![X0 : $i, X1 : $i]:
% 0.52/0.75         ((k3_xboole_0 @ X0 @ X1)
% 0.52/0.75           = (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 0.52/0.75      inference('demod', [status(thm)], ['52', '53'])).
% 0.52/0.75  thf('56', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 0.52/0.75      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.52/0.75  thf('57', plain,
% 0.52/0.75      (![X0 : $i, X1 : $i]:
% 0.52/0.75         ((k3_xboole_0 @ X0 @ X1)
% 0.52/0.75           = (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 0.52/0.75      inference('demod', [status(thm)], ['52', '53'])).
% 0.52/0.75  thf('58', plain,
% 0.52/0.75      ((((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.52/0.75          != (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))
% 0.52/0.75        | ((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))),
% 0.52/0.75      inference('demod', [status(thm)], ['47', '54', '55', '56', '57'])).
% 0.52/0.75  thf('59', plain,
% 0.52/0.75      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.52/0.75      inference('simplify', [status(thm)], ['58'])).
% 0.52/0.75  thf('60', plain,
% 0.52/0.75      (![X8 : $i, X9 : $i]:
% 0.52/0.75         ((k4_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9))
% 0.52/0.75           = (k4_xboole_0 @ X8 @ X9))),
% 0.52/0.75      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.52/0.75  thf('61', plain,
% 0.52/0.75      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0)
% 0.52/0.75         = (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 0.52/0.75      inference('sup+', [status(thm)], ['59', '60'])).
% 0.52/0.75  thf('62', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.52/0.75      inference('demod', [status(thm)], ['19', '20'])).
% 0.52/0.75  thf('63', plain,
% 0.52/0.75      (((k1_tarski @ sk_A) = (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 0.52/0.75      inference('demod', [status(thm)], ['61', '62'])).
% 0.52/0.75  thf(l33_zfmisc_1, axiom,
% 0.52/0.75    (![A:$i,B:$i]:
% 0.52/0.75     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 0.52/0.75       ( ~( r2_hidden @ A @ B ) ) ))).
% 0.52/0.75  thf('64', plain,
% 0.52/0.75      (![X29 : $i, X30 : $i]:
% 0.52/0.75         (~ (r2_hidden @ X29 @ X30)
% 0.52/0.75          | ((k4_xboole_0 @ (k1_tarski @ X29) @ X30) != (k1_tarski @ X29)))),
% 0.52/0.75      inference('cnf', [status(esa)], [l33_zfmisc_1])).
% 0.52/0.75  thf('65', plain,
% 0.52/0.75      ((((k1_tarski @ sk_A) != (k1_tarski @ sk_A))
% 0.52/0.75        | ~ (r2_hidden @ sk_A @ sk_B))),
% 0.52/0.75      inference('sup-', [status(thm)], ['63', '64'])).
% 0.52/0.75  thf('66', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.52/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.75  thf('67', plain, (((k1_tarski @ sk_A) != (k1_tarski @ sk_A))),
% 0.52/0.75      inference('demod', [status(thm)], ['65', '66'])).
% 0.52/0.75  thf('68', plain, ($false), inference('simplify', [status(thm)], ['67'])).
% 0.52/0.75  
% 0.52/0.75  % SZS output end Refutation
% 0.52/0.75  
% 0.52/0.76  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
