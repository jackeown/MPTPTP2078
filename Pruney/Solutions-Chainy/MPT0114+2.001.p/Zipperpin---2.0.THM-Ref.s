%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.61kRCz0jRx

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:41 EST 2020

% Result     : Theorem 6.85s
% Output     : Refutation 6.85s
% Verified   : 
% Statistics : Number of formulae       :  152 (1199 expanded)
%              Number of leaves         :   24 ( 407 expanded)
%              Depth                    :   18
%              Number of atoms          : 1350 (9157 expanded)
%              Number of equality atoms :  100 ( 872 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t107_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ A @ ( k5_xboole_0 @ B @ C ) )
      <=> ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t107_xboole_1])).

thf('0',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
    | ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) )
    | ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    | ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) )
   <= ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['2'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('4',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_xboole_0 @ X10 @ X9 )
        = X9 )
      | ~ ( r1_tarski @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('5',plain,
    ( ( ( k2_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) )
      = ( k5_xboole_0 @ sk_B @ sk_C ) )
   <= ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('6',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k2_xboole_0 @ X19 @ X20 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('7',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) )
      = k1_xboole_0 )
   <= ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(l98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k5_xboole_0 @ X7 @ X8 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X7 @ X8 ) @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf(t52_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('9',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k4_xboole_0 @ X24 @ X25 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X23 @ X24 ) @ ( k3_xboole_0 @ X23 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('10',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k5_xboole_0 @ X7 @ X8 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X7 @ X8 ) @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ ( k3_xboole_0 @ X2 @ X0 ) )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ ( k3_xboole_0 @ X2 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('13',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( ( k5_xboole_0 @ ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) @ ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) )
      = ( k4_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) @ ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ) ) )
   <= ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['7','14'])).

thf('16',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k5_xboole_0 @ X7 @ X8 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X7 @ X8 ) @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('17',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X14 @ X15 ) @ X14 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('18',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_xboole_0 @ X10 @ X9 )
        = X9 )
      | ~ ( r1_tarski @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k2_xboole_0 @ X19 @ X20 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('22',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) )
      = k1_xboole_0 )
   <= ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('23',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k4_xboole_0 @ X24 @ X25 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X23 @ X24 ) @ ( k3_xboole_0 @ X23 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('24',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ ( k5_xboole_0 @ sk_B @ sk_C ) @ X0 ) )
        = ( k2_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ sk_A @ X0 ) ) )
   <= ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k2_xboole_0 @ X19 @ X20 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('26',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X14 @ X15 ) @ X14 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_xboole_0 @ X10 @ X9 )
        = X9 )
      | ~ ( r1_tarski @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ ( k5_xboole_0 @ sk_B @ sk_C ) @ X0 ) )
        = ( k3_xboole_0 @ sk_A @ X0 ) )
   <= ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['24','29'])).

thf('31',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
        = ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ ( k5_xboole_0 @ sk_B @ sk_C ) @ X0 ) ) )
   <= ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['21','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('33',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k5_xboole_0 @ X7 @ X8 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X7 @ X8 ) @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('36',plain,(
    ! [X13: $i] :
      ( ( k3_xboole_0 @ X13 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['34','37'])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('39',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ X11 @ ( k2_xboole_0 @ X11 @ X12 ) )
      = X11 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('40',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('41',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X14 @ X15 ) @ X14 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['39','42'])).

thf(t37_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('44',plain,(
    ! [X16: $i,X18: $i] :
      ( ( ( k4_xboole_0 @ X16 @ X18 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t37_xboole_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['34','37'])).

thf('49',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['39','42'])).

thf('50',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_xboole_0 @ X10 @ X9 )
        = X9 )
      | ~ ( r1_tarski @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ X11 @ ( k2_xboole_0 @ X11 @ X12 ) )
      = X11 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['47','48','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['38','54'])).

thf('56',plain,
    ( ! [X0: $i] :
        ( sk_A
        = ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ ( k5_xboole_0 @ sk_B @ sk_C ) @ X0 ) ) )
   <= ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['31','55'])).

thf('57',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ sk_A @ ( k2_xboole_0 @ ( k5_xboole_0 @ sk_B @ sk_C ) @ X0 ) )
   <= ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['56','59'])).

thf('61',plain,
    ( ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
   <= ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['20','60'])).

thf('62',plain,(
    ! [X16: $i,X18: $i] :
      ( ( ( k4_xboole_0 @ X16 @ X18 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t37_xboole_1])).

thf('63',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
      = k1_xboole_0 )
   <= ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['47','48','53'])).

thf('65',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
      = k1_xboole_0 )
   <= ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('66',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('69',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k2_xboole_0 @ X19 @ X20 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
      = k1_xboole_0 )
   <= ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['15','63','64','65','66','67','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ ( k3_xboole_0 @ X2 @ X0 ) )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ ( k3_xboole_0 @ X2 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ k1_xboole_0 ) @ ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['38','54'])).

thf('76',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('78',plain,
    ( ( ( k5_xboole_0 @ ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) @ ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) )
      = ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ) ) )
   <= ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['71','77'])).

thf('79',plain,
    ( ( ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
      = k1_xboole_0 )
   <= ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['15','63','64','65','66','67','70'])).

thf('80',plain,(
    ! [X13: $i] :
      ( ( k3_xboole_0 @ X13 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('81',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['38','54'])).

thf('82',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k4_xboole_0 @ X24 @ X25 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X23 @ X24 ) @ ( k3_xboole_0 @ X23 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ k1_xboole_0 @ X1 ) )
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('85',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['38','54'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['80','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['38','54'])).

thf(t55_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('89',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X26 @ X27 ) @ ( k3_xboole_0 @ X26 @ X27 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X26 @ X27 ) @ ( k4_xboole_0 @ X27 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t55_xboole_1])).

thf('90',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k5_xboole_0 @ X7 @ X8 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X7 @ X8 ) @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf('91',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k5_xboole_0 @ X26 @ X27 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X26 @ X27 ) @ ( k4_xboole_0 @ X27 @ X26 ) ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['88','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['87','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('97',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['38','54'])).

thf('98',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
      = sk_A )
   <= ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['78','79','95','96','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('100',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k4_xboole_0 @ X24 @ X25 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X23 @ X24 ) @ ( k3_xboole_0 @ X23 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['39','42'])).

thf(t85_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ) )).

thf('105',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( r1_tarski @ X28 @ X29 )
      | ( r1_xboole_0 @ X28 @ ( k4_xboole_0 @ X30 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['103','106'])).

thf('108',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
   <= ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['98','107'])).

thf('109',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
    | ~ ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    | ~ ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
   <= ~ ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['109'])).

thf('111',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) )
    | ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['108','110'])).

thf('112',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    | ~ ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) )
    | ~ ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['109'])).

thf('113',plain,
    ( ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
   <= ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['2'])).

thf('114',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
   <= ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t86_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf('115',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( r1_tarski @ X31 @ X32 )
      | ~ ( r1_xboole_0 @ X31 @ X33 )
      | ( r1_tarski @ X31 @ ( k4_xboole_0 @ X32 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t86_xboole_1])).

thf('116',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_A @ ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ sk_B @ sk_C ) ) )
        | ~ ( r1_tarski @ sk_A @ X0 ) )
   <= ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,
    ( ( r1_tarski @ sk_A @ ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_C ) @ ( k3_xboole_0 @ sk_B @ sk_C ) ) )
   <= ( ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
      & ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['113','116'])).

thf('118',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k5_xboole_0 @ X7 @ X8 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X7 @ X8 ) @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf('119',plain,
    ( ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) )
   <= ( ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
      & ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) )
   <= ~ ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['109'])).

thf('121',plain,
    ( ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) )
    | ~ ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    | ~ ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,
    ( ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) )
    | ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['2'])).

thf('123',plain,
    ( ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
   <= ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['20','60'])).

thf('124',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
   <= ~ ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['109'])).

thf('125',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) )
    | ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','111','112','121','122','125'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.61kRCz0jRx
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:08:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 6.85/7.03  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 6.85/7.03  % Solved by: fo/fo7.sh
% 6.85/7.03  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.85/7.03  % done 6939 iterations in 6.576s
% 6.85/7.03  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 6.85/7.03  % SZS output start Refutation
% 6.85/7.03  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 6.85/7.03  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 6.85/7.03  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 6.85/7.03  thf(sk_B_type, type, sk_B: $i).
% 6.85/7.03  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 6.85/7.03  thf(sk_A_type, type, sk_A: $i).
% 6.85/7.03  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 6.85/7.03  thf(sk_C_type, type, sk_C: $i).
% 6.85/7.03  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 6.85/7.03  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 6.85/7.03  thf(t107_xboole_1, conjecture,
% 6.85/7.03    (![A:$i,B:$i,C:$i]:
% 6.85/7.03     ( ( r1_tarski @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 6.85/7.03       ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & 
% 6.85/7.03         ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ))).
% 6.85/7.03  thf(zf_stmt_0, negated_conjecture,
% 6.85/7.03    (~( ![A:$i,B:$i,C:$i]:
% 6.85/7.03        ( ( r1_tarski @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 6.85/7.03          ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & 
% 6.85/7.03            ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ) )),
% 6.85/7.03    inference('cnf.neg', [status(esa)], [t107_xboole_1])).
% 6.85/7.03  thf('0', plain,
% 6.85/7.03      (((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))
% 6.85/7.03        | (r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)))),
% 6.85/7.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.85/7.03  thf('1', plain,
% 6.85/7.03      (((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))) | 
% 6.85/7.03       ((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)))),
% 6.85/7.03      inference('split', [status(esa)], ['0'])).
% 6.85/7.03  thf('2', plain,
% 6.85/7.03      (((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))
% 6.85/7.03        | (r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)))),
% 6.85/7.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.85/7.03  thf('3', plain,
% 6.85/7.03      (((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)))
% 6.85/7.03         <= (((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))))),
% 6.85/7.03      inference('split', [status(esa)], ['2'])).
% 6.85/7.03  thf(t12_xboole_1, axiom,
% 6.85/7.03    (![A:$i,B:$i]:
% 6.85/7.03     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 6.85/7.03  thf('4', plain,
% 6.85/7.03      (![X9 : $i, X10 : $i]:
% 6.85/7.03         (((k2_xboole_0 @ X10 @ X9) = (X9)) | ~ (r1_tarski @ X10 @ X9))),
% 6.85/7.03      inference('cnf', [status(esa)], [t12_xboole_1])).
% 6.85/7.03  thf('5', plain,
% 6.85/7.03      ((((k2_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))
% 6.85/7.03          = (k5_xboole_0 @ sk_B @ sk_C)))
% 6.85/7.03         <= (((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))))),
% 6.85/7.03      inference('sup-', [status(thm)], ['3', '4'])).
% 6.85/7.03  thf(t46_xboole_1, axiom,
% 6.85/7.03    (![A:$i,B:$i]:
% 6.85/7.03     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 6.85/7.03  thf('6', plain,
% 6.85/7.03      (![X19 : $i, X20 : $i]:
% 6.85/7.03         ((k4_xboole_0 @ X19 @ (k2_xboole_0 @ X19 @ X20)) = (k1_xboole_0))),
% 6.85/7.03      inference('cnf', [status(esa)], [t46_xboole_1])).
% 6.85/7.03  thf('7', plain,
% 6.85/7.03      ((((k4_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)) = (k1_xboole_0)))
% 6.85/7.03         <= (((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))))),
% 6.85/7.03      inference('sup+', [status(thm)], ['5', '6'])).
% 6.85/7.03  thf(l98_xboole_1, axiom,
% 6.85/7.03    (![A:$i,B:$i]:
% 6.85/7.03     ( ( k5_xboole_0 @ A @ B ) =
% 6.85/7.03       ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 6.85/7.03  thf('8', plain,
% 6.85/7.03      (![X7 : $i, X8 : $i]:
% 6.85/7.03         ((k5_xboole_0 @ X7 @ X8)
% 6.85/7.03           = (k4_xboole_0 @ (k2_xboole_0 @ X7 @ X8) @ (k3_xboole_0 @ X7 @ X8)))),
% 6.85/7.03      inference('cnf', [status(esa)], [l98_xboole_1])).
% 6.85/7.03  thf(t52_xboole_1, axiom,
% 6.85/7.03    (![A:$i,B:$i,C:$i]:
% 6.85/7.03     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 6.85/7.03       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 6.85/7.03  thf('9', plain,
% 6.85/7.03      (![X23 : $i, X24 : $i, X25 : $i]:
% 6.85/7.03         ((k4_xboole_0 @ X23 @ (k4_xboole_0 @ X24 @ X25))
% 6.85/7.03           = (k2_xboole_0 @ (k4_xboole_0 @ X23 @ X24) @ 
% 6.85/7.03              (k3_xboole_0 @ X23 @ X25)))),
% 6.85/7.03      inference('cnf', [status(esa)], [t52_xboole_1])).
% 6.85/7.03  thf('10', plain,
% 6.85/7.03      (![X7 : $i, X8 : $i]:
% 6.85/7.03         ((k5_xboole_0 @ X7 @ X8)
% 6.85/7.03           = (k4_xboole_0 @ (k2_xboole_0 @ X7 @ X8) @ (k3_xboole_0 @ X7 @ X8)))),
% 6.85/7.03      inference('cnf', [status(esa)], [l98_xboole_1])).
% 6.85/7.03  thf('11', plain,
% 6.85/7.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.85/7.03         ((k5_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ (k3_xboole_0 @ X2 @ X0))
% 6.85/7.03           = (k4_xboole_0 @ (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ 
% 6.85/7.03              (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ (k3_xboole_0 @ X2 @ X0))))),
% 6.85/7.03      inference('sup+', [status(thm)], ['9', '10'])).
% 6.85/7.03  thf('12', plain,
% 6.85/7.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.85/7.03         ((k5_xboole_0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ 
% 6.85/7.03           (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 6.85/7.03           = (k4_xboole_0 @ (k4_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)) @ 
% 6.85/7.03              (k3_xboole_0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ 
% 6.85/7.03               (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))))),
% 6.85/7.03      inference('sup+', [status(thm)], ['8', '11'])).
% 6.85/7.03  thf(commutativity_k3_xboole_0, axiom,
% 6.85/7.03    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 6.85/7.03  thf('13', plain,
% 6.85/7.03      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 6.85/7.03      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 6.85/7.03  thf('14', plain,
% 6.85/7.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.85/7.03         ((k5_xboole_0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ 
% 6.85/7.03           (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 6.85/7.03           = (k4_xboole_0 @ (k4_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)) @ 
% 6.85/7.03              (k3_xboole_0 @ (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 6.85/7.03               (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))))),
% 6.85/7.03      inference('demod', [status(thm)], ['12', '13'])).
% 6.85/7.03  thf('15', plain,
% 6.85/7.03      ((((k5_xboole_0 @ (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)) @ 
% 6.85/7.03          (k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)))
% 6.85/7.03          = (k4_xboole_0 @ k1_xboole_0 @ 
% 6.85/7.03             (k3_xboole_0 @ 
% 6.85/7.03              (k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)) @ 
% 6.85/7.03              (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))))
% 6.85/7.03         <= (((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))))),
% 6.85/7.03      inference('sup+', [status(thm)], ['7', '14'])).
% 6.85/7.03  thf('16', plain,
% 6.85/7.03      (![X7 : $i, X8 : $i]:
% 6.85/7.03         ((k5_xboole_0 @ X7 @ X8)
% 6.85/7.03           = (k4_xboole_0 @ (k2_xboole_0 @ X7 @ X8) @ (k3_xboole_0 @ X7 @ X8)))),
% 6.85/7.03      inference('cnf', [status(esa)], [l98_xboole_1])).
% 6.85/7.03  thf(t36_xboole_1, axiom,
% 6.85/7.03    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 6.85/7.03  thf('17', plain,
% 6.85/7.03      (![X14 : $i, X15 : $i]: (r1_tarski @ (k4_xboole_0 @ X14 @ X15) @ X14)),
% 6.85/7.03      inference('cnf', [status(esa)], [t36_xboole_1])).
% 6.85/7.03  thf('18', plain,
% 6.85/7.03      (![X9 : $i, X10 : $i]:
% 6.85/7.03         (((k2_xboole_0 @ X10 @ X9) = (X9)) | ~ (r1_tarski @ X10 @ X9))),
% 6.85/7.03      inference('cnf', [status(esa)], [t12_xboole_1])).
% 6.85/7.03  thf('19', plain,
% 6.85/7.03      (![X0 : $i, X1 : $i]:
% 6.85/7.03         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 6.85/7.03      inference('sup-', [status(thm)], ['17', '18'])).
% 6.85/7.03  thf('20', plain,
% 6.85/7.03      (![X0 : $i, X1 : $i]:
% 6.85/7.03         ((k2_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))
% 6.85/7.03           = (k2_xboole_0 @ X1 @ X0))),
% 6.85/7.03      inference('sup+', [status(thm)], ['16', '19'])).
% 6.85/7.03  thf('21', plain,
% 6.85/7.03      (![X19 : $i, X20 : $i]:
% 6.85/7.03         ((k4_xboole_0 @ X19 @ (k2_xboole_0 @ X19 @ X20)) = (k1_xboole_0))),
% 6.85/7.03      inference('cnf', [status(esa)], [t46_xboole_1])).
% 6.85/7.03  thf('22', plain,
% 6.85/7.03      ((((k4_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)) = (k1_xboole_0)))
% 6.85/7.03         <= (((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))))),
% 6.85/7.03      inference('sup+', [status(thm)], ['5', '6'])).
% 6.85/7.03  thf('23', plain,
% 6.85/7.03      (![X23 : $i, X24 : $i, X25 : $i]:
% 6.85/7.03         ((k4_xboole_0 @ X23 @ (k4_xboole_0 @ X24 @ X25))
% 6.85/7.03           = (k2_xboole_0 @ (k4_xboole_0 @ X23 @ X24) @ 
% 6.85/7.03              (k3_xboole_0 @ X23 @ X25)))),
% 6.85/7.03      inference('cnf', [status(esa)], [t52_xboole_1])).
% 6.85/7.03  thf('24', plain,
% 6.85/7.03      ((![X0 : $i]:
% 6.85/7.03          ((k4_xboole_0 @ sk_A @ 
% 6.85/7.03            (k4_xboole_0 @ (k5_xboole_0 @ sk_B @ sk_C) @ X0))
% 6.85/7.03            = (k2_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ sk_A @ X0))))
% 6.85/7.03         <= (((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))))),
% 6.85/7.03      inference('sup+', [status(thm)], ['22', '23'])).
% 6.85/7.03  thf('25', plain,
% 6.85/7.03      (![X19 : $i, X20 : $i]:
% 6.85/7.03         ((k4_xboole_0 @ X19 @ (k2_xboole_0 @ X19 @ X20)) = (k1_xboole_0))),
% 6.85/7.03      inference('cnf', [status(esa)], [t46_xboole_1])).
% 6.85/7.03  thf('26', plain,
% 6.85/7.03      (![X14 : $i, X15 : $i]: (r1_tarski @ (k4_xboole_0 @ X14 @ X15) @ X14)),
% 6.85/7.03      inference('cnf', [status(esa)], [t36_xboole_1])).
% 6.85/7.03  thf('27', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 6.85/7.03      inference('sup+', [status(thm)], ['25', '26'])).
% 6.85/7.03  thf('28', plain,
% 6.85/7.03      (![X9 : $i, X10 : $i]:
% 6.85/7.03         (((k2_xboole_0 @ X10 @ X9) = (X9)) | ~ (r1_tarski @ X10 @ X9))),
% 6.85/7.03      inference('cnf', [status(esa)], [t12_xboole_1])).
% 6.85/7.03  thf('29', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 6.85/7.03      inference('sup-', [status(thm)], ['27', '28'])).
% 6.85/7.03  thf('30', plain,
% 6.85/7.03      ((![X0 : $i]:
% 6.85/7.03          ((k4_xboole_0 @ sk_A @ 
% 6.85/7.03            (k4_xboole_0 @ (k5_xboole_0 @ sk_B @ sk_C) @ X0))
% 6.85/7.03            = (k3_xboole_0 @ sk_A @ X0)))
% 6.85/7.03         <= (((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))))),
% 6.85/7.03      inference('demod', [status(thm)], ['24', '29'])).
% 6.85/7.03  thf('31', plain,
% 6.85/7.03      ((![X0 : $i]:
% 6.85/7.03          ((k4_xboole_0 @ sk_A @ k1_xboole_0)
% 6.85/7.03            = (k3_xboole_0 @ sk_A @ 
% 6.85/7.03               (k2_xboole_0 @ (k5_xboole_0 @ sk_B @ sk_C) @ X0))))
% 6.85/7.03         <= (((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))))),
% 6.85/7.03      inference('sup+', [status(thm)], ['21', '30'])).
% 6.85/7.03  thf('32', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 6.85/7.03      inference('sup-', [status(thm)], ['27', '28'])).
% 6.85/7.03  thf('33', plain,
% 6.85/7.03      (![X7 : $i, X8 : $i]:
% 6.85/7.03         ((k5_xboole_0 @ X7 @ X8)
% 6.85/7.03           = (k4_xboole_0 @ (k2_xboole_0 @ X7 @ X8) @ (k3_xboole_0 @ X7 @ X8)))),
% 6.85/7.03      inference('cnf', [status(esa)], [l98_xboole_1])).
% 6.85/7.03  thf('34', plain,
% 6.85/7.03      (![X0 : $i]:
% 6.85/7.03         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 6.85/7.03           = (k4_xboole_0 @ X0 @ (k3_xboole_0 @ k1_xboole_0 @ X0)))),
% 6.85/7.03      inference('sup+', [status(thm)], ['32', '33'])).
% 6.85/7.03  thf('35', plain,
% 6.85/7.03      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 6.85/7.03      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 6.85/7.03  thf(t2_boole, axiom,
% 6.85/7.03    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 6.85/7.03  thf('36', plain,
% 6.85/7.03      (![X13 : $i]: ((k3_xboole_0 @ X13 @ k1_xboole_0) = (k1_xboole_0))),
% 6.85/7.03      inference('cnf', [status(esa)], [t2_boole])).
% 6.85/7.03  thf('37', plain,
% 6.85/7.03      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 6.85/7.03      inference('sup+', [status(thm)], ['35', '36'])).
% 6.85/7.03  thf('38', plain,
% 6.85/7.03      (![X0 : $i]:
% 6.85/7.03         ((k5_xboole_0 @ k1_xboole_0 @ X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 6.85/7.03      inference('demod', [status(thm)], ['34', '37'])).
% 6.85/7.03  thf(t21_xboole_1, axiom,
% 6.85/7.03    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 6.85/7.03  thf('39', plain,
% 6.85/7.03      (![X11 : $i, X12 : $i]:
% 6.85/7.03         ((k3_xboole_0 @ X11 @ (k2_xboole_0 @ X11 @ X12)) = (X11))),
% 6.85/7.03      inference('cnf', [status(esa)], [t21_xboole_1])).
% 6.85/7.03  thf(t48_xboole_1, axiom,
% 6.85/7.03    (![A:$i,B:$i]:
% 6.85/7.03     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 6.85/7.03  thf('40', plain,
% 6.85/7.03      (![X21 : $i, X22 : $i]:
% 6.85/7.03         ((k4_xboole_0 @ X21 @ (k4_xboole_0 @ X21 @ X22))
% 6.85/7.03           = (k3_xboole_0 @ X21 @ X22))),
% 6.85/7.03      inference('cnf', [status(esa)], [t48_xboole_1])).
% 6.85/7.03  thf('41', plain,
% 6.85/7.03      (![X14 : $i, X15 : $i]: (r1_tarski @ (k4_xboole_0 @ X14 @ X15) @ X14)),
% 6.85/7.03      inference('cnf', [status(esa)], [t36_xboole_1])).
% 6.85/7.03  thf('42', plain,
% 6.85/7.03      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 6.85/7.03      inference('sup+', [status(thm)], ['40', '41'])).
% 6.85/7.03  thf('43', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 6.85/7.03      inference('sup+', [status(thm)], ['39', '42'])).
% 6.85/7.03  thf(t37_xboole_1, axiom,
% 6.85/7.03    (![A:$i,B:$i]:
% 6.85/7.03     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 6.85/7.03  thf('44', plain,
% 6.85/7.03      (![X16 : $i, X18 : $i]:
% 6.85/7.03         (((k4_xboole_0 @ X16 @ X18) = (k1_xboole_0))
% 6.85/7.03          | ~ (r1_tarski @ X16 @ X18))),
% 6.85/7.03      inference('cnf', [status(esa)], [t37_xboole_1])).
% 6.85/7.03  thf('45', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 6.85/7.03      inference('sup-', [status(thm)], ['43', '44'])).
% 6.85/7.03  thf('46', plain,
% 6.85/7.03      (![X21 : $i, X22 : $i]:
% 6.85/7.03         ((k4_xboole_0 @ X21 @ (k4_xboole_0 @ X21 @ X22))
% 6.85/7.03           = (k3_xboole_0 @ X21 @ X22))),
% 6.85/7.03      inference('cnf', [status(esa)], [t48_xboole_1])).
% 6.85/7.03  thf('47', plain,
% 6.85/7.03      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 6.85/7.03      inference('sup+', [status(thm)], ['45', '46'])).
% 6.85/7.03  thf('48', plain,
% 6.85/7.03      (![X0 : $i]:
% 6.85/7.03         ((k5_xboole_0 @ k1_xboole_0 @ X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 6.85/7.03      inference('demod', [status(thm)], ['34', '37'])).
% 6.85/7.03  thf('49', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 6.85/7.03      inference('sup+', [status(thm)], ['39', '42'])).
% 6.85/7.03  thf('50', plain,
% 6.85/7.03      (![X9 : $i, X10 : $i]:
% 6.85/7.03         (((k2_xboole_0 @ X10 @ X9) = (X9)) | ~ (r1_tarski @ X10 @ X9))),
% 6.85/7.03      inference('cnf', [status(esa)], [t12_xboole_1])).
% 6.85/7.03  thf('51', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 6.85/7.03      inference('sup-', [status(thm)], ['49', '50'])).
% 6.85/7.03  thf('52', plain,
% 6.85/7.03      (![X11 : $i, X12 : $i]:
% 6.85/7.03         ((k3_xboole_0 @ X11 @ (k2_xboole_0 @ X11 @ X12)) = (X11))),
% 6.85/7.03      inference('cnf', [status(esa)], [t21_xboole_1])).
% 6.85/7.03  thf('53', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 6.85/7.03      inference('sup+', [status(thm)], ['51', '52'])).
% 6.85/7.03  thf('54', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 6.85/7.03      inference('demod', [status(thm)], ['47', '48', '53'])).
% 6.85/7.03  thf('55', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 6.85/7.03      inference('demod', [status(thm)], ['38', '54'])).
% 6.85/7.03  thf('56', plain,
% 6.85/7.03      ((![X0 : $i]:
% 6.85/7.03          ((sk_A)
% 6.85/7.03            = (k3_xboole_0 @ sk_A @ 
% 6.85/7.03               (k2_xboole_0 @ (k5_xboole_0 @ sk_B @ sk_C) @ X0))))
% 6.85/7.03         <= (((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))))),
% 6.85/7.03      inference('demod', [status(thm)], ['31', '55'])).
% 6.85/7.03  thf('57', plain,
% 6.85/7.03      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 6.85/7.03      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 6.85/7.03  thf('58', plain,
% 6.85/7.03      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 6.85/7.03      inference('sup+', [status(thm)], ['40', '41'])).
% 6.85/7.03  thf('59', plain,
% 6.85/7.03      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 6.85/7.03      inference('sup+', [status(thm)], ['57', '58'])).
% 6.85/7.03  thf('60', plain,
% 6.85/7.03      ((![X0 : $i]:
% 6.85/7.03          (r1_tarski @ sk_A @ (k2_xboole_0 @ (k5_xboole_0 @ sk_B @ sk_C) @ X0)))
% 6.85/7.03         <= (((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))))),
% 6.85/7.03      inference('sup+', [status(thm)], ['56', '59'])).
% 6.85/7.03  thf('61', plain,
% 6.85/7.03      (((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))
% 6.85/7.03         <= (((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))))),
% 6.85/7.03      inference('sup+', [status(thm)], ['20', '60'])).
% 6.85/7.03  thf('62', plain,
% 6.85/7.03      (![X16 : $i, X18 : $i]:
% 6.85/7.03         (((k4_xboole_0 @ X16 @ X18) = (k1_xboole_0))
% 6.85/7.03          | ~ (r1_tarski @ X16 @ X18))),
% 6.85/7.03      inference('cnf', [status(esa)], [t37_xboole_1])).
% 6.85/7.03  thf('63', plain,
% 6.85/7.03      ((((k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)) = (k1_xboole_0)))
% 6.85/7.03         <= (((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))))),
% 6.85/7.03      inference('sup-', [status(thm)], ['61', '62'])).
% 6.85/7.03  thf('64', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 6.85/7.03      inference('demod', [status(thm)], ['47', '48', '53'])).
% 6.85/7.03  thf('65', plain,
% 6.85/7.03      ((((k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)) = (k1_xboole_0)))
% 6.85/7.03         <= (((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))))),
% 6.85/7.03      inference('sup-', [status(thm)], ['61', '62'])).
% 6.85/7.03  thf('66', plain,
% 6.85/7.03      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 6.85/7.03      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 6.85/7.03  thf('67', plain,
% 6.85/7.03      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 6.85/7.03      inference('sup+', [status(thm)], ['35', '36'])).
% 6.85/7.03  thf('68', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 6.85/7.03      inference('sup-', [status(thm)], ['27', '28'])).
% 6.85/7.03  thf('69', plain,
% 6.85/7.03      (![X19 : $i, X20 : $i]:
% 6.85/7.03         ((k4_xboole_0 @ X19 @ (k2_xboole_0 @ X19 @ X20)) = (k1_xboole_0))),
% 6.85/7.03      inference('cnf', [status(esa)], [t46_xboole_1])).
% 6.85/7.03  thf('70', plain,
% 6.85/7.03      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 6.85/7.03      inference('sup+', [status(thm)], ['68', '69'])).
% 6.85/7.03  thf('71', plain,
% 6.85/7.03      ((((k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)) = (k1_xboole_0)))
% 6.85/7.03         <= (((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))))),
% 6.85/7.03      inference('demod', [status(thm)],
% 6.85/7.03                ['15', '63', '64', '65', '66', '67', '70'])).
% 6.85/7.03  thf('72', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 6.85/7.03      inference('sup-', [status(thm)], ['43', '44'])).
% 6.85/7.03  thf('73', plain,
% 6.85/7.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.85/7.03         ((k5_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ (k3_xboole_0 @ X2 @ X0))
% 6.85/7.03           = (k4_xboole_0 @ (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ 
% 6.85/7.03              (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ (k3_xboole_0 @ X2 @ X0))))),
% 6.85/7.03      inference('sup+', [status(thm)], ['9', '10'])).
% 6.85/7.03  thf('74', plain,
% 6.85/7.03      (![X0 : $i, X1 : $i]:
% 6.85/7.03         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 6.85/7.03           = (k4_xboole_0 @ (k4_xboole_0 @ X1 @ k1_xboole_0) @ 
% 6.85/7.03              (k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))))),
% 6.85/7.03      inference('sup+', [status(thm)], ['72', '73'])).
% 6.85/7.03  thf('75', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 6.85/7.03      inference('demod', [status(thm)], ['38', '54'])).
% 6.85/7.03  thf('76', plain,
% 6.85/7.03      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 6.85/7.03      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 6.85/7.03  thf('77', plain,
% 6.85/7.03      (![X0 : $i, X1 : $i]:
% 6.85/7.03         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 6.85/7.03           = (k4_xboole_0 @ X1 @ 
% 6.85/7.03              (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))))),
% 6.85/7.03      inference('demod', [status(thm)], ['74', '75', '76'])).
% 6.85/7.03  thf('78', plain,
% 6.85/7.03      ((((k5_xboole_0 @ (k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)) @ 
% 6.85/7.03          (k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)))
% 6.85/7.03          = (k4_xboole_0 @ sk_A @ 
% 6.85/7.03             (k3_xboole_0 @ k1_xboole_0 @ 
% 6.85/7.03              (k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))))))
% 6.85/7.03         <= (((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))))),
% 6.85/7.03      inference('sup+', [status(thm)], ['71', '77'])).
% 6.85/7.03  thf('79', plain,
% 6.85/7.03      ((((k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)) = (k1_xboole_0)))
% 6.85/7.03         <= (((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))))),
% 6.85/7.03      inference('demod', [status(thm)],
% 6.85/7.03                ['15', '63', '64', '65', '66', '67', '70'])).
% 6.85/7.03  thf('80', plain,
% 6.85/7.03      (![X13 : $i]: ((k3_xboole_0 @ X13 @ k1_xboole_0) = (k1_xboole_0))),
% 6.85/7.03      inference('cnf', [status(esa)], [t2_boole])).
% 6.85/7.03  thf('81', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 6.85/7.03      inference('demod', [status(thm)], ['38', '54'])).
% 6.85/7.03  thf('82', plain,
% 6.85/7.03      (![X23 : $i, X24 : $i, X25 : $i]:
% 6.85/7.03         ((k4_xboole_0 @ X23 @ (k4_xboole_0 @ X24 @ X25))
% 6.85/7.03           = (k2_xboole_0 @ (k4_xboole_0 @ X23 @ X24) @ 
% 6.85/7.03              (k3_xboole_0 @ X23 @ X25)))),
% 6.85/7.03      inference('cnf', [status(esa)], [t52_xboole_1])).
% 6.85/7.03  thf('83', plain,
% 6.85/7.03      (![X0 : $i, X1 : $i]:
% 6.85/7.03         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ k1_xboole_0 @ X1))
% 6.85/7.03           = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 6.85/7.03      inference('sup+', [status(thm)], ['81', '82'])).
% 6.85/7.03  thf('84', plain,
% 6.85/7.03      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 6.85/7.03      inference('sup+', [status(thm)], ['68', '69'])).
% 6.85/7.03  thf('85', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 6.85/7.03      inference('demod', [status(thm)], ['38', '54'])).
% 6.85/7.03  thf('86', plain,
% 6.85/7.03      (![X0 : $i, X1 : $i]:
% 6.85/7.03         ((X0) = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 6.85/7.03      inference('demod', [status(thm)], ['83', '84', '85'])).
% 6.85/7.03  thf('87', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 6.85/7.03      inference('sup+', [status(thm)], ['80', '86'])).
% 6.85/7.03  thf('88', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 6.85/7.03      inference('demod', [status(thm)], ['38', '54'])).
% 6.85/7.03  thf(t55_xboole_1, axiom,
% 6.85/7.03    (![A:$i,B:$i]:
% 6.85/7.03     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) =
% 6.85/7.03       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 6.85/7.03  thf('89', plain,
% 6.85/7.03      (![X26 : $i, X27 : $i]:
% 6.85/7.03         ((k4_xboole_0 @ (k2_xboole_0 @ X26 @ X27) @ (k3_xboole_0 @ X26 @ X27))
% 6.85/7.03           = (k2_xboole_0 @ (k4_xboole_0 @ X26 @ X27) @ 
% 6.85/7.03              (k4_xboole_0 @ X27 @ X26)))),
% 6.85/7.03      inference('cnf', [status(esa)], [t55_xboole_1])).
% 6.85/7.03  thf('90', plain,
% 6.85/7.03      (![X7 : $i, X8 : $i]:
% 6.85/7.03         ((k5_xboole_0 @ X7 @ X8)
% 6.85/7.03           = (k4_xboole_0 @ (k2_xboole_0 @ X7 @ X8) @ (k3_xboole_0 @ X7 @ X8)))),
% 6.85/7.03      inference('cnf', [status(esa)], [l98_xboole_1])).
% 6.85/7.03  thf('91', plain,
% 6.85/7.03      (![X26 : $i, X27 : $i]:
% 6.85/7.03         ((k5_xboole_0 @ X26 @ X27)
% 6.85/7.03           = (k2_xboole_0 @ (k4_xboole_0 @ X26 @ X27) @ 
% 6.85/7.03              (k4_xboole_0 @ X27 @ X26)))),
% 6.85/7.03      inference('demod', [status(thm)], ['89', '90'])).
% 6.85/7.03  thf('92', plain,
% 6.85/7.03      (![X0 : $i]:
% 6.85/7.03         ((k5_xboole_0 @ X0 @ k1_xboole_0)
% 6.85/7.03           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 6.85/7.03      inference('sup+', [status(thm)], ['88', '91'])).
% 6.85/7.03  thf('93', plain,
% 6.85/7.03      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 6.85/7.03      inference('sup+', [status(thm)], ['68', '69'])).
% 6.85/7.03  thf('94', plain,
% 6.85/7.03      (![X0 : $i]:
% 6.85/7.03         ((k5_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 6.85/7.03      inference('demod', [status(thm)], ['92', '93'])).
% 6.85/7.03  thf('95', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 6.85/7.03      inference('sup+', [status(thm)], ['87', '94'])).
% 6.85/7.03  thf('96', plain,
% 6.85/7.03      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 6.85/7.03      inference('sup+', [status(thm)], ['35', '36'])).
% 6.85/7.03  thf('97', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 6.85/7.03      inference('demod', [status(thm)], ['38', '54'])).
% 6.85/7.03  thf('98', plain,
% 6.85/7.03      ((((k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)) = (sk_A)))
% 6.85/7.03         <= (((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))))),
% 6.85/7.03      inference('demod', [status(thm)], ['78', '79', '95', '96', '97'])).
% 6.85/7.03  thf('99', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 6.85/7.03      inference('sup+', [status(thm)], ['51', '52'])).
% 6.85/7.03  thf('100', plain,
% 6.85/7.03      (![X23 : $i, X24 : $i, X25 : $i]:
% 6.85/7.03         ((k4_xboole_0 @ X23 @ (k4_xboole_0 @ X24 @ X25))
% 6.85/7.03           = (k2_xboole_0 @ (k4_xboole_0 @ X23 @ X24) @ 
% 6.85/7.03              (k3_xboole_0 @ X23 @ X25)))),
% 6.85/7.03      inference('cnf', [status(esa)], [t52_xboole_1])).
% 6.85/7.03  thf('101', plain,
% 6.85/7.03      (![X0 : $i, X1 : $i]:
% 6.85/7.03         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 6.85/7.03           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 6.85/7.03      inference('sup+', [status(thm)], ['99', '100'])).
% 6.85/7.03  thf('102', plain,
% 6.85/7.03      (![X0 : $i, X1 : $i]:
% 6.85/7.03         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 6.85/7.03      inference('sup-', [status(thm)], ['17', '18'])).
% 6.85/7.03  thf('103', plain,
% 6.85/7.03      (![X0 : $i, X1 : $i]:
% 6.85/7.03         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 6.85/7.03      inference('demod', [status(thm)], ['101', '102'])).
% 6.85/7.03  thf('104', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 6.85/7.03      inference('sup+', [status(thm)], ['39', '42'])).
% 6.85/7.03  thf(t85_xboole_1, axiom,
% 6.85/7.03    (![A:$i,B:$i,C:$i]:
% 6.85/7.03     ( ( r1_tarski @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ))).
% 6.85/7.03  thf('105', plain,
% 6.85/7.03      (![X28 : $i, X29 : $i, X30 : $i]:
% 6.85/7.03         (~ (r1_tarski @ X28 @ X29)
% 6.85/7.03          | (r1_xboole_0 @ X28 @ (k4_xboole_0 @ X30 @ X29)))),
% 6.85/7.03      inference('cnf', [status(esa)], [t85_xboole_1])).
% 6.85/7.03  thf('106', plain,
% 6.85/7.03      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 6.85/7.03      inference('sup-', [status(thm)], ['104', '105'])).
% 6.85/7.03  thf('107', plain,
% 6.85/7.03      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)),
% 6.85/7.03      inference('sup+', [status(thm)], ['103', '106'])).
% 6.85/7.03  thf('108', plain,
% 6.85/7.03      (((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)))
% 6.85/7.03         <= (((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))))),
% 6.85/7.03      inference('sup+', [status(thm)], ['98', '107'])).
% 6.85/7.03  thf('109', plain,
% 6.85/7.03      ((~ (r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))
% 6.85/7.03        | ~ (r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))
% 6.85/7.03        | ~ (r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)))),
% 6.85/7.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.85/7.03  thf('110', plain,
% 6.85/7.03      ((~ (r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)))
% 6.85/7.03         <= (~ ((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))))),
% 6.85/7.03      inference('split', [status(esa)], ['109'])).
% 6.85/7.03  thf('111', plain,
% 6.85/7.03      (~ ((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))) | 
% 6.85/7.03       ((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)))),
% 6.85/7.03      inference('sup-', [status(thm)], ['108', '110'])).
% 6.85/7.03  thf('112', plain,
% 6.85/7.03      (~ ((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))) | 
% 6.85/7.03       ~ ((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))) | 
% 6.85/7.03       ~ ((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)))),
% 6.85/7.03      inference('split', [status(esa)], ['109'])).
% 6.85/7.03  thf('113', plain,
% 6.85/7.03      (((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))
% 6.85/7.03         <= (((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 6.85/7.03      inference('split', [status(esa)], ['2'])).
% 6.85/7.03  thf('114', plain,
% 6.85/7.03      (((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)))
% 6.85/7.03         <= (((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))))),
% 6.85/7.03      inference('split', [status(esa)], ['0'])).
% 6.85/7.03  thf(t86_xboole_1, axiom,
% 6.85/7.03    (![A:$i,B:$i,C:$i]:
% 6.85/7.03     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) =>
% 6.85/7.03       ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ))).
% 6.85/7.03  thf('115', plain,
% 6.85/7.03      (![X31 : $i, X32 : $i, X33 : $i]:
% 6.85/7.03         (~ (r1_tarski @ X31 @ X32)
% 6.85/7.03          | ~ (r1_xboole_0 @ X31 @ X33)
% 6.85/7.03          | (r1_tarski @ X31 @ (k4_xboole_0 @ X32 @ X33)))),
% 6.85/7.03      inference('cnf', [status(esa)], [t86_xboole_1])).
% 6.85/7.03  thf('116', plain,
% 6.85/7.03      ((![X0 : $i]:
% 6.85/7.03          ((r1_tarski @ sk_A @ (k4_xboole_0 @ X0 @ (k3_xboole_0 @ sk_B @ sk_C)))
% 6.85/7.03           | ~ (r1_tarski @ sk_A @ X0)))
% 6.85/7.03         <= (((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))))),
% 6.85/7.03      inference('sup-', [status(thm)], ['114', '115'])).
% 6.85/7.03  thf('117', plain,
% 6.85/7.03      (((r1_tarski @ sk_A @ 
% 6.85/7.03         (k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_C) @ 
% 6.85/7.03          (k3_xboole_0 @ sk_B @ sk_C))))
% 6.85/7.03         <= (((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))) & 
% 6.85/7.03             ((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))))),
% 6.85/7.03      inference('sup-', [status(thm)], ['113', '116'])).
% 6.85/7.03  thf('118', plain,
% 6.85/7.03      (![X7 : $i, X8 : $i]:
% 6.85/7.03         ((k5_xboole_0 @ X7 @ X8)
% 6.85/7.03           = (k4_xboole_0 @ (k2_xboole_0 @ X7 @ X8) @ (k3_xboole_0 @ X7 @ X8)))),
% 6.85/7.03      inference('cnf', [status(esa)], [l98_xboole_1])).
% 6.85/7.03  thf('119', plain,
% 6.85/7.03      (((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)))
% 6.85/7.03         <= (((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))) & 
% 6.85/7.03             ((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))))),
% 6.85/7.03      inference('demod', [status(thm)], ['117', '118'])).
% 6.85/7.03  thf('120', plain,
% 6.85/7.03      ((~ (r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)))
% 6.85/7.03         <= (~ ((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))))),
% 6.85/7.03      inference('split', [status(esa)], ['109'])).
% 6.85/7.03  thf('121', plain,
% 6.85/7.03      (((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))) | 
% 6.85/7.03       ~ ((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))) | 
% 6.85/7.03       ~ ((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)))),
% 6.85/7.03      inference('sup-', [status(thm)], ['119', '120'])).
% 6.85/7.03  thf('122', plain,
% 6.85/7.03      (((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))) | 
% 6.85/7.03       ((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 6.85/7.03      inference('split', [status(esa)], ['2'])).
% 6.85/7.03  thf('123', plain,
% 6.85/7.03      (((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))
% 6.85/7.03         <= (((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))))),
% 6.85/7.03      inference('sup+', [status(thm)], ['20', '60'])).
% 6.85/7.03  thf('124', plain,
% 6.85/7.03      ((~ (r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))
% 6.85/7.03         <= (~ ((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 6.85/7.03      inference('split', [status(esa)], ['109'])).
% 6.85/7.03  thf('125', plain,
% 6.85/7.03      (~ ((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))) | 
% 6.85/7.03       ((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 6.85/7.03      inference('sup-', [status(thm)], ['123', '124'])).
% 6.85/7.03  thf('126', plain, ($false),
% 6.85/7.03      inference('sat_resolution*', [status(thm)],
% 6.85/7.03                ['1', '111', '112', '121', '122', '125'])).
% 6.85/7.03  
% 6.85/7.03  % SZS output end Refutation
% 6.85/7.03  
% 6.85/7.04  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
