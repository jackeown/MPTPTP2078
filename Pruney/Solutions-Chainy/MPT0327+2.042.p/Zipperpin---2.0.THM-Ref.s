%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.eY6ZA1ILP1

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:55 EST 2020

% Result     : Theorem 1.56s
% Output     : Refutation 1.56s
% Verified   : 
% Statistics : Number of formulae       :  117 (1034 expanded)
%              Number of leaves         :   23 ( 332 expanded)
%              Depth                    :   19
%              Number of atoms          :  853 (7738 expanded)
%              Number of equality atoms :   98 ( 926 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t140_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k4_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) )
        = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r2_hidden @ A @ B )
       => ( ( k2_xboole_0 @ ( k4_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) )
          = B ) ) ),
    inference('cnf.neg',[status(esa)],[t140_zfmisc_1])).

thf('0',plain,(
    ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('1',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X19 @ X20 ) @ X21 )
      = ( k5_xboole_0 @ X19 @ ( k5_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('3',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['2'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('4',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('6',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['2'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('9',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['1','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['7','10'])).

thf('14',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X19 @ X20 ) @ X21 )
      = ( k5_xboole_0 @ X19 @ ( k5_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('16',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('17',plain,(
    ! [X12: $i] :
      ( r1_tarski @ k1_xboole_0 @ X12 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('18',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['16','19'])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('21',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X22 @ X23 ) @ ( k3_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf('22',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X19 @ X20 ) @ X21 )
      = ( k5_xboole_0 @ X19 @ ( k5_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('23',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ X22 @ ( k5_xboole_0 @ X23 @ ( k3_xboole_0 @ X22 @ X23 ) ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['20','23'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('25',plain,(
    ! [X18: $i] :
      ( ( k5_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['15','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['7','10'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['15','26'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X18: $i] :
      ( ( k5_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['27','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['12','33'])).

thf('35',plain,(
    ! [X18: $i] :
      ( ( k5_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ X22 @ ( k5_xboole_0 @ X23 @ ( k3_xboole_0 @ X22 @ X23 ) ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('38',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X19 @ X20 ) @ X21 )
      = ( k5_xboole_0 @ X19 @ ( k5_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X19 @ X20 ) @ X21 )
      = ( k5_xboole_0 @ X19 @ ( k5_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['36','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['27','32'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['42','45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['27','32'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('51',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ X22 @ ( k5_xboole_0 @ X23 @ ( k3_xboole_0 @ X22 @ X23 ) ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['49','54'])).

thf('56',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
 != sk_B ),
    inference(demod,[status(thm)],['0','55'])).

thf('57',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('59',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k3_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X15 @ X16 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('62',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['60','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['7','10'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['57','66'])).

thf('68',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k3_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X15 @ X16 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X18: $i] :
      ( ( k5_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['49','54'])).

thf('79',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('80',plain,(
    ! [X34: $i,X36: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X34 ) @ X36 )
      | ~ ( r2_hidden @ X34 @ X36 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('81',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('83',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('85',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ X22 @ ( k5_xboole_0 @ X23 @ ( k3_xboole_0 @ X22 @ X23 ) ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('87',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['7','10'])).

thf('89',plain,(
    ! [X18: $i] :
      ( ( k5_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('90',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = sk_B ),
    inference(demod,[status(thm)],['87','88','89'])).

thf('91',plain,(
    sk_B != sk_B ),
    inference(demod,[status(thm)],['56','77','78','90'])).

thf('92',plain,(
    $false ),
    inference(simplify,[status(thm)],['91'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.eY6ZA1ILP1
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:02:26 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.21/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 1.56/1.75  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.56/1.75  % Solved by: fo/fo7.sh
% 1.56/1.75  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.56/1.75  % done 2459 iterations in 1.260s
% 1.56/1.75  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.56/1.75  % SZS output start Refutation
% 1.56/1.75  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.56/1.75  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.56/1.75  thf(sk_A_type, type, sk_A: $i).
% 1.56/1.75  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.56/1.75  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.56/1.75  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.56/1.75  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.56/1.75  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.56/1.75  thf(sk_B_type, type, sk_B: $i).
% 1.56/1.75  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.56/1.75  thf(t140_zfmisc_1, conjecture,
% 1.56/1.75    (![A:$i,B:$i]:
% 1.56/1.75     ( ( r2_hidden @ A @ B ) =>
% 1.56/1.75       ( ( k2_xboole_0 @
% 1.56/1.75           ( k4_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) ) =
% 1.56/1.75         ( B ) ) ))).
% 1.56/1.75  thf(zf_stmt_0, negated_conjecture,
% 1.56/1.75    (~( ![A:$i,B:$i]:
% 1.56/1.75        ( ( r2_hidden @ A @ B ) =>
% 1.56/1.75          ( ( k2_xboole_0 @
% 1.56/1.75              ( k4_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) ) =
% 1.56/1.75            ( B ) ) ) )),
% 1.56/1.75    inference('cnf.neg', [status(esa)], [t140_zfmisc_1])).
% 1.56/1.75  thf('0', plain,
% 1.56/1.75      (((k2_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 1.56/1.75         (k1_tarski @ sk_A)) != (sk_B))),
% 1.56/1.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.56/1.75  thf(t91_xboole_1, axiom,
% 1.56/1.75    (![A:$i,B:$i,C:$i]:
% 1.56/1.75     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 1.56/1.75       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 1.56/1.75  thf('1', plain,
% 1.56/1.75      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.56/1.75         ((k5_xboole_0 @ (k5_xboole_0 @ X19 @ X20) @ X21)
% 1.56/1.75           = (k5_xboole_0 @ X19 @ (k5_xboole_0 @ X20 @ X21)))),
% 1.56/1.75      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.56/1.75  thf(d10_xboole_0, axiom,
% 1.56/1.75    (![A:$i,B:$i]:
% 1.56/1.75     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.56/1.75  thf('2', plain,
% 1.56/1.75      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 1.56/1.75      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.56/1.75  thf('3', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 1.56/1.75      inference('simplify', [status(thm)], ['2'])).
% 1.56/1.75  thf(t28_xboole_1, axiom,
% 1.56/1.75    (![A:$i,B:$i]:
% 1.56/1.75     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.56/1.75  thf('4', plain,
% 1.56/1.75      (![X10 : $i, X11 : $i]:
% 1.56/1.75         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 1.56/1.75      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.56/1.75  thf('5', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 1.56/1.75      inference('sup-', [status(thm)], ['3', '4'])).
% 1.56/1.75  thf(t100_xboole_1, axiom,
% 1.56/1.75    (![A:$i,B:$i]:
% 1.56/1.75     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.56/1.75  thf('6', plain,
% 1.56/1.75      (![X8 : $i, X9 : $i]:
% 1.56/1.75         ((k4_xboole_0 @ X8 @ X9)
% 1.56/1.75           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 1.56/1.75      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.56/1.75  thf('7', plain,
% 1.56/1.75      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.56/1.75      inference('sup+', [status(thm)], ['5', '6'])).
% 1.56/1.75  thf('8', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 1.56/1.75      inference('simplify', [status(thm)], ['2'])).
% 1.56/1.75  thf(l32_xboole_1, axiom,
% 1.56/1.75    (![A:$i,B:$i]:
% 1.56/1.75     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.56/1.75  thf('9', plain,
% 1.56/1.75      (![X5 : $i, X7 : $i]:
% 1.56/1.75         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 1.56/1.75      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.56/1.75  thf('10', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.56/1.75      inference('sup-', [status(thm)], ['8', '9'])).
% 1.56/1.75  thf('11', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 1.56/1.75      inference('demod', [status(thm)], ['7', '10'])).
% 1.56/1.75  thf('12', plain,
% 1.56/1.75      (![X0 : $i, X1 : $i]:
% 1.56/1.75         ((k1_xboole_0)
% 1.56/1.75           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))))),
% 1.56/1.75      inference('sup+', [status(thm)], ['1', '11'])).
% 1.56/1.75  thf('13', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 1.56/1.75      inference('demod', [status(thm)], ['7', '10'])).
% 1.56/1.75  thf('14', plain,
% 1.56/1.75      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.56/1.75         ((k5_xboole_0 @ (k5_xboole_0 @ X19 @ X20) @ X21)
% 1.56/1.75           = (k5_xboole_0 @ X19 @ (k5_xboole_0 @ X20 @ X21)))),
% 1.56/1.75      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.56/1.75  thf('15', plain,
% 1.56/1.75      (![X0 : $i, X1 : $i]:
% 1.56/1.75         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 1.56/1.75           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.56/1.75      inference('sup+', [status(thm)], ['13', '14'])).
% 1.56/1.75  thf(t48_xboole_1, axiom,
% 1.56/1.75    (![A:$i,B:$i]:
% 1.56/1.75     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.56/1.75  thf('16', plain,
% 1.56/1.75      (![X13 : $i, X14 : $i]:
% 1.56/1.75         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 1.56/1.75           = (k3_xboole_0 @ X13 @ X14))),
% 1.56/1.75      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.56/1.75  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 1.56/1.75  thf('17', plain, (![X12 : $i]: (r1_tarski @ k1_xboole_0 @ X12)),
% 1.56/1.75      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.56/1.75  thf('18', plain,
% 1.56/1.75      (![X5 : $i, X7 : $i]:
% 1.56/1.75         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 1.56/1.75      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.56/1.75  thf('19', plain,
% 1.56/1.75      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.56/1.75      inference('sup-', [status(thm)], ['17', '18'])).
% 1.56/1.75  thf('20', plain,
% 1.56/1.75      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.56/1.75      inference('sup+', [status(thm)], ['16', '19'])).
% 1.56/1.75  thf(t94_xboole_1, axiom,
% 1.56/1.75    (![A:$i,B:$i]:
% 1.56/1.75     ( ( k2_xboole_0 @ A @ B ) =
% 1.56/1.75       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.56/1.75  thf('21', plain,
% 1.56/1.75      (![X22 : $i, X23 : $i]:
% 1.56/1.75         ((k2_xboole_0 @ X22 @ X23)
% 1.56/1.75           = (k5_xboole_0 @ (k5_xboole_0 @ X22 @ X23) @ 
% 1.56/1.75              (k3_xboole_0 @ X22 @ X23)))),
% 1.56/1.75      inference('cnf', [status(esa)], [t94_xboole_1])).
% 1.56/1.75  thf('22', plain,
% 1.56/1.75      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.56/1.75         ((k5_xboole_0 @ (k5_xboole_0 @ X19 @ X20) @ X21)
% 1.56/1.75           = (k5_xboole_0 @ X19 @ (k5_xboole_0 @ X20 @ X21)))),
% 1.56/1.75      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.56/1.75  thf('23', plain,
% 1.56/1.75      (![X22 : $i, X23 : $i]:
% 1.56/1.75         ((k2_xboole_0 @ X22 @ X23)
% 1.56/1.75           = (k5_xboole_0 @ X22 @ 
% 1.56/1.75              (k5_xboole_0 @ X23 @ (k3_xboole_0 @ X22 @ X23))))),
% 1.56/1.75      inference('demod', [status(thm)], ['21', '22'])).
% 1.56/1.75  thf('24', plain,
% 1.56/1.75      (![X0 : $i]:
% 1.56/1.75         ((k2_xboole_0 @ k1_xboole_0 @ X0)
% 1.56/1.75           = (k5_xboole_0 @ k1_xboole_0 @ (k5_xboole_0 @ X0 @ k1_xboole_0)))),
% 1.56/1.75      inference('sup+', [status(thm)], ['20', '23'])).
% 1.56/1.75  thf(t5_boole, axiom,
% 1.56/1.75    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.56/1.75  thf('25', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 1.56/1.75      inference('cnf', [status(esa)], [t5_boole])).
% 1.56/1.75  thf('26', plain,
% 1.56/1.75      (![X0 : $i]:
% 1.56/1.75         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 1.56/1.75      inference('demod', [status(thm)], ['24', '25'])).
% 1.56/1.75  thf('27', plain,
% 1.56/1.75      (![X0 : $i, X1 : $i]:
% 1.56/1.75         ((k2_xboole_0 @ k1_xboole_0 @ X0)
% 1.56/1.75           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.56/1.75      inference('demod', [status(thm)], ['15', '26'])).
% 1.56/1.75  thf('28', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 1.56/1.75      inference('demod', [status(thm)], ['7', '10'])).
% 1.56/1.75  thf('29', plain,
% 1.56/1.75      (![X0 : $i, X1 : $i]:
% 1.56/1.75         ((k2_xboole_0 @ k1_xboole_0 @ X0)
% 1.56/1.75           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.56/1.75      inference('demod', [status(thm)], ['15', '26'])).
% 1.56/1.75  thf('30', plain,
% 1.56/1.75      (![X0 : $i]:
% 1.56/1.75         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.56/1.75      inference('sup+', [status(thm)], ['28', '29'])).
% 1.56/1.75  thf('31', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 1.56/1.75      inference('cnf', [status(esa)], [t5_boole])).
% 1.56/1.75  thf('32', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.56/1.75      inference('sup+', [status(thm)], ['30', '31'])).
% 1.56/1.75  thf('33', plain,
% 1.56/1.75      (![X0 : $i, X1 : $i]:
% 1.56/1.75         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.56/1.75      inference('demod', [status(thm)], ['27', '32'])).
% 1.56/1.75  thf('34', plain,
% 1.56/1.75      (![X0 : $i, X1 : $i]:
% 1.56/1.75         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))
% 1.56/1.75           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 1.56/1.75      inference('sup+', [status(thm)], ['12', '33'])).
% 1.56/1.75  thf('35', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 1.56/1.75      inference('cnf', [status(esa)], [t5_boole])).
% 1.56/1.75  thf('36', plain,
% 1.56/1.75      (![X0 : $i, X1 : $i]:
% 1.56/1.75         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 1.56/1.75      inference('demod', [status(thm)], ['34', '35'])).
% 1.56/1.75  thf('37', plain,
% 1.56/1.75      (![X22 : $i, X23 : $i]:
% 1.56/1.75         ((k2_xboole_0 @ X22 @ X23)
% 1.56/1.75           = (k5_xboole_0 @ X22 @ 
% 1.56/1.75              (k5_xboole_0 @ X23 @ (k3_xboole_0 @ X22 @ X23))))),
% 1.56/1.75      inference('demod', [status(thm)], ['21', '22'])).
% 1.56/1.75  thf('38', plain,
% 1.56/1.75      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.56/1.75         ((k5_xboole_0 @ (k5_xboole_0 @ X19 @ X20) @ X21)
% 1.56/1.75           = (k5_xboole_0 @ X19 @ (k5_xboole_0 @ X20 @ X21)))),
% 1.56/1.75      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.56/1.75  thf('39', plain,
% 1.56/1.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.56/1.75         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2)
% 1.56/1.75           = (k5_xboole_0 @ X1 @ 
% 1.56/1.75              (k5_xboole_0 @ (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) @ X2)))),
% 1.56/1.75      inference('sup+', [status(thm)], ['37', '38'])).
% 1.56/1.75  thf('40', plain,
% 1.56/1.75      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.56/1.75         ((k5_xboole_0 @ (k5_xboole_0 @ X19 @ X20) @ X21)
% 1.56/1.75           = (k5_xboole_0 @ X19 @ (k5_xboole_0 @ X20 @ X21)))),
% 1.56/1.75      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.56/1.75  thf('41', plain,
% 1.56/1.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.56/1.75         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2)
% 1.56/1.75           = (k5_xboole_0 @ X1 @ 
% 1.56/1.75              (k5_xboole_0 @ X0 @ (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))))),
% 1.56/1.75      inference('demod', [status(thm)], ['39', '40'])).
% 1.56/1.75  thf('42', plain,
% 1.56/1.75      (![X0 : $i, X1 : $i]:
% 1.56/1.75         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 1.56/1.75           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.56/1.75      inference('sup+', [status(thm)], ['36', '41'])).
% 1.56/1.75  thf('43', plain,
% 1.56/1.75      (![X0 : $i, X1 : $i]:
% 1.56/1.75         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 1.56/1.75      inference('demod', [status(thm)], ['34', '35'])).
% 1.56/1.75  thf('44', plain,
% 1.56/1.75      (![X0 : $i, X1 : $i]:
% 1.56/1.75         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.56/1.75      inference('demod', [status(thm)], ['27', '32'])).
% 1.56/1.75  thf('45', plain,
% 1.56/1.75      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 1.56/1.75      inference('sup+', [status(thm)], ['43', '44'])).
% 1.56/1.75  thf('46', plain,
% 1.56/1.75      (![X8 : $i, X9 : $i]:
% 1.56/1.75         ((k4_xboole_0 @ X8 @ X9)
% 1.56/1.75           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 1.56/1.75      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.56/1.75  thf('47', plain,
% 1.56/1.75      (![X0 : $i, X1 : $i]:
% 1.56/1.75         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 1.56/1.75           = (k4_xboole_0 @ X1 @ X0))),
% 1.56/1.75      inference('demod', [status(thm)], ['42', '45', '46'])).
% 1.56/1.75  thf('48', plain,
% 1.56/1.75      (![X0 : $i, X1 : $i]:
% 1.56/1.75         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.56/1.75      inference('demod', [status(thm)], ['27', '32'])).
% 1.56/1.75  thf('49', plain,
% 1.56/1.75      (![X0 : $i, X1 : $i]:
% 1.56/1.75         ((k2_xboole_0 @ X1 @ X0)
% 1.56/1.75           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.56/1.75      inference('sup+', [status(thm)], ['47', '48'])).
% 1.56/1.75  thf(commutativity_k3_xboole_0, axiom,
% 1.56/1.75    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.56/1.75  thf('50', plain,
% 1.56/1.75      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.56/1.75      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.56/1.75  thf('51', plain,
% 1.56/1.75      (![X22 : $i, X23 : $i]:
% 1.56/1.75         ((k2_xboole_0 @ X22 @ X23)
% 1.56/1.75           = (k5_xboole_0 @ X22 @ 
% 1.56/1.75              (k5_xboole_0 @ X23 @ (k3_xboole_0 @ X22 @ X23))))),
% 1.56/1.75      inference('demod', [status(thm)], ['21', '22'])).
% 1.56/1.75  thf('52', plain,
% 1.56/1.75      (![X0 : $i, X1 : $i]:
% 1.56/1.75         ((k2_xboole_0 @ X0 @ X1)
% 1.56/1.75           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))))),
% 1.56/1.75      inference('sup+', [status(thm)], ['50', '51'])).
% 1.56/1.75  thf('53', plain,
% 1.56/1.75      (![X8 : $i, X9 : $i]:
% 1.56/1.75         ((k4_xboole_0 @ X8 @ X9)
% 1.56/1.75           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 1.56/1.75      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.56/1.75  thf('54', plain,
% 1.56/1.75      (![X0 : $i, X1 : $i]:
% 1.56/1.75         ((k2_xboole_0 @ X0 @ X1)
% 1.56/1.75           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.56/1.75      inference('demod', [status(thm)], ['52', '53'])).
% 1.56/1.75  thf('55', plain,
% 1.56/1.75      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X0 @ X1) = (k2_xboole_0 @ X1 @ X0))),
% 1.56/1.75      inference('sup+', [status(thm)], ['49', '54'])).
% 1.56/1.75  thf('56', plain,
% 1.56/1.75      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ 
% 1.56/1.75         (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))) != (sk_B))),
% 1.56/1.75      inference('demod', [status(thm)], ['0', '55'])).
% 1.56/1.75  thf('57', plain,
% 1.56/1.75      (![X13 : $i, X14 : $i]:
% 1.56/1.75         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 1.56/1.75           = (k3_xboole_0 @ X13 @ X14))),
% 1.56/1.75      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.56/1.75  thf('58', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 1.56/1.75      inference('sup-', [status(thm)], ['3', '4'])).
% 1.56/1.75  thf(t49_xboole_1, axiom,
% 1.56/1.75    (![A:$i,B:$i,C:$i]:
% 1.56/1.75     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 1.56/1.75       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 1.56/1.75  thf('59', plain,
% 1.56/1.75      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.56/1.75         ((k3_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X17))
% 1.56/1.75           = (k4_xboole_0 @ (k3_xboole_0 @ X15 @ X16) @ X17))),
% 1.56/1.75      inference('cnf', [status(esa)], [t49_xboole_1])).
% 1.56/1.75  thf('60', plain,
% 1.56/1.75      (![X0 : $i, X1 : $i]:
% 1.56/1.75         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 1.56/1.75           = (k4_xboole_0 @ X0 @ X1))),
% 1.56/1.75      inference('sup+', [status(thm)], ['58', '59'])).
% 1.56/1.75  thf('61', plain,
% 1.56/1.75      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.56/1.75      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.56/1.75  thf('62', plain,
% 1.56/1.75      (![X8 : $i, X9 : $i]:
% 1.56/1.75         ((k4_xboole_0 @ X8 @ X9)
% 1.56/1.75           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 1.56/1.75      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.56/1.75  thf('63', plain,
% 1.56/1.75      (![X0 : $i, X1 : $i]:
% 1.56/1.75         ((k4_xboole_0 @ X0 @ X1)
% 1.56/1.75           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.56/1.75      inference('sup+', [status(thm)], ['61', '62'])).
% 1.56/1.75  thf('64', plain,
% 1.56/1.75      (![X0 : $i, X1 : $i]:
% 1.56/1.75         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1)
% 1.56/1.75           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0)))),
% 1.56/1.75      inference('sup+', [status(thm)], ['60', '63'])).
% 1.56/1.75  thf('65', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 1.56/1.75      inference('demod', [status(thm)], ['7', '10'])).
% 1.56/1.75  thf('66', plain,
% 1.56/1.75      (![X0 : $i, X1 : $i]:
% 1.56/1.75         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1) = (k1_xboole_0))),
% 1.56/1.75      inference('demod', [status(thm)], ['64', '65'])).
% 1.56/1.75  thf('67', plain,
% 1.56/1.75      (![X0 : $i, X1 : $i]:
% 1.56/1.75         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1) = (k1_xboole_0))),
% 1.56/1.75      inference('sup+', [status(thm)], ['57', '66'])).
% 1.56/1.75  thf('68', plain,
% 1.56/1.75      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.56/1.75         ((k3_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X17))
% 1.56/1.75           = (k4_xboole_0 @ (k3_xboole_0 @ X15 @ X16) @ X17))),
% 1.56/1.75      inference('cnf', [status(esa)], [t49_xboole_1])).
% 1.56/1.75  thf('69', plain,
% 1.56/1.75      (![X0 : $i, X1 : $i]:
% 1.56/1.75         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 1.56/1.75      inference('demod', [status(thm)], ['67', '68'])).
% 1.56/1.75  thf('70', plain,
% 1.56/1.75      (![X0 : $i, X1 : $i]:
% 1.56/1.75         ((k4_xboole_0 @ X0 @ X1)
% 1.56/1.75           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.56/1.75      inference('sup+', [status(thm)], ['61', '62'])).
% 1.56/1.75  thf('71', plain,
% 1.56/1.75      (![X0 : $i, X1 : $i]:
% 1.56/1.75         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 1.56/1.75           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ k1_xboole_0))),
% 1.56/1.75      inference('sup+', [status(thm)], ['69', '70'])).
% 1.56/1.75  thf('72', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 1.56/1.75      inference('cnf', [status(esa)], [t5_boole])).
% 1.56/1.75  thf('73', plain,
% 1.56/1.75      (![X0 : $i, X1 : $i]:
% 1.56/1.75         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 1.56/1.75           = (k4_xboole_0 @ X1 @ X0))),
% 1.56/1.75      inference('demod', [status(thm)], ['71', '72'])).
% 1.56/1.75  thf('74', plain,
% 1.56/1.75      (![X0 : $i, X1 : $i]:
% 1.56/1.75         ((k2_xboole_0 @ X0 @ X1)
% 1.56/1.75           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.56/1.75      inference('demod', [status(thm)], ['52', '53'])).
% 1.56/1.75  thf('75', plain,
% 1.56/1.75      (![X0 : $i, X1 : $i]:
% 1.56/1.75         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 1.56/1.75           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.56/1.75      inference('sup+', [status(thm)], ['73', '74'])).
% 1.56/1.75  thf('76', plain,
% 1.56/1.75      (![X0 : $i, X1 : $i]:
% 1.56/1.75         ((k2_xboole_0 @ X0 @ X1)
% 1.56/1.75           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.56/1.75      inference('demod', [status(thm)], ['52', '53'])).
% 1.56/1.75  thf('77', plain,
% 1.56/1.75      (![X0 : $i, X1 : $i]:
% 1.56/1.75         ((k2_xboole_0 @ X0 @ X1)
% 1.56/1.75           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.56/1.75      inference('sup+', [status(thm)], ['75', '76'])).
% 1.56/1.75  thf('78', plain,
% 1.56/1.75      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X0 @ X1) = (k2_xboole_0 @ X1 @ X0))),
% 1.56/1.75      inference('sup+', [status(thm)], ['49', '54'])).
% 1.56/1.75  thf('79', plain, ((r2_hidden @ sk_A @ sk_B)),
% 1.56/1.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.56/1.75  thf(l1_zfmisc_1, axiom,
% 1.56/1.75    (![A:$i,B:$i]:
% 1.56/1.75     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 1.56/1.75  thf('80', plain,
% 1.56/1.75      (![X34 : $i, X36 : $i]:
% 1.56/1.75         ((r1_tarski @ (k1_tarski @ X34) @ X36) | ~ (r2_hidden @ X34 @ X36))),
% 1.56/1.75      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 1.56/1.75  thf('81', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B)),
% 1.56/1.75      inference('sup-', [status(thm)], ['79', '80'])).
% 1.56/1.75  thf('82', plain,
% 1.56/1.75      (![X10 : $i, X11 : $i]:
% 1.56/1.75         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 1.56/1.75      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.56/1.75  thf('83', plain,
% 1.56/1.75      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))),
% 1.56/1.75      inference('sup-', [status(thm)], ['81', '82'])).
% 1.56/1.75  thf('84', plain,
% 1.56/1.75      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.56/1.75      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.56/1.75  thf('85', plain,
% 1.56/1.75      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 1.56/1.75      inference('demod', [status(thm)], ['83', '84'])).
% 1.56/1.75  thf('86', plain,
% 1.56/1.75      (![X22 : $i, X23 : $i]:
% 1.56/1.75         ((k2_xboole_0 @ X22 @ X23)
% 1.56/1.75           = (k5_xboole_0 @ X22 @ 
% 1.56/1.75              (k5_xboole_0 @ X23 @ (k3_xboole_0 @ X22 @ X23))))),
% 1.56/1.75      inference('demod', [status(thm)], ['21', '22'])).
% 1.56/1.75  thf('87', plain,
% 1.56/1.75      (((k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 1.56/1.75         = (k5_xboole_0 @ sk_B @ 
% 1.56/1.75            (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))))),
% 1.56/1.75      inference('sup+', [status(thm)], ['85', '86'])).
% 1.56/1.75  thf('88', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 1.56/1.75      inference('demod', [status(thm)], ['7', '10'])).
% 1.56/1.75  thf('89', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 1.56/1.75      inference('cnf', [status(esa)], [t5_boole])).
% 1.56/1.75  thf('90', plain, (((k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (sk_B))),
% 1.56/1.75      inference('demod', [status(thm)], ['87', '88', '89'])).
% 1.56/1.75  thf('91', plain, (((sk_B) != (sk_B))),
% 1.56/1.75      inference('demod', [status(thm)], ['56', '77', '78', '90'])).
% 1.56/1.75  thf('92', plain, ($false), inference('simplify', [status(thm)], ['91'])).
% 1.56/1.75  
% 1.56/1.75  % SZS output end Refutation
% 1.56/1.75  
% 1.56/1.76  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
