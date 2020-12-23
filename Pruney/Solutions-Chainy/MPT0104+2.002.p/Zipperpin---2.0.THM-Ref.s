%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QQsosuKZVI

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:03 EST 2020

% Result     : Theorem 1.81s
% Output     : Refutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 242 expanded)
%              Number of leaves         :   27 (  90 expanded)
%              Depth                    :   16
%              Number of atoms          : 1021 (1851 expanded)
%              Number of equality atoms :   99 ( 181 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t97_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
        & ( r1_tarski @ ( k4_xboole_0 @ B @ A ) @ C ) )
     => ( r1_tarski @ ( k5_xboole_0 @ A @ B ) @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
          & ( r1_tarski @ ( k4_xboole_0 @ B @ A ) @ C ) )
       => ( r1_tarski @ ( k5_xboole_0 @ A @ B ) @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t97_xboole_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t96_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X37: $i,X38: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X37 @ X38 ) @ ( k5_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t96_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X7: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ X7 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(d6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('4',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('7',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X31 @ X32 ) @ X33 )
      = ( k5_xboole_0 @ X31 @ ( k5_xboole_0 @ X32 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('8',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('9',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('12',plain,(
    ! [X25: $i] :
      ( ( k5_xboole_0 @ X25 @ k1_xboole_0 )
      = X25 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('16',plain,(
    ! [X37: $i,X38: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X37 @ X38 ) @ ( k5_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t96_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('18',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r1_tarski @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X15 @ X16 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('20',plain,(
    ! [X6: $i] :
      ( ( k2_xboole_0 @ X6 @ X6 )
      = X6 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X7: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ X7 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['14','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['5','6','7','24'])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('26',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k2_xboole_0 @ X35 @ X36 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X35 @ X36 ) @ ( k3_xboole_0 @ X35 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf('27',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X31 @ X32 ) @ X33 )
      = ( k5_xboole_0 @ X31 @ ( k5_xboole_0 @ X32 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('28',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k2_xboole_0 @ X35 @ X36 )
      = ( k5_xboole_0 @ X35 @ ( k5_xboole_0 @ X36 @ ( k3_xboole_0 @ X35 @ X36 ) ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('30',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k3_xboole_0 @ X18 @ X19 ) )
      = ( k4_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('34',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k3_xboole_0 @ X22 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X22 @ X23 ) @ X24 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('35',plain,(
    ! [X6: $i] :
      ( ( k2_xboole_0 @ X6 @ X6 )
      = X6 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('36',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('38',plain,(
    ! [X34: $i] :
      ( ( k5_xboole_0 @ X34 @ X34 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('40',plain,(
    ! [X10: $i] :
      ( ( k3_xboole_0 @ X10 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('41',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('42',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X25: $i] :
      ( ( k5_xboole_0 @ X25 @ k1_xboole_0 )
      = X25 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('45',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('47',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['33','34','39','40','47'])).

thf('49',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k2_xboole_0 @ X35 @ X36 )
      = ( k5_xboole_0 @ X35 @ ( k4_xboole_0 @ X36 @ X35 ) ) ) ),
    inference(demod,[status(thm)],['28','48'])).

thf('50',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('51',plain,(
    ! [X34: $i] :
      ( ( k5_xboole_0 @ X34 @ X34 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('52',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X31 @ X32 ) @ X33 )
      = ( k5_xboole_0 @ X31 @ ( k5_xboole_0 @ X32 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['50','55'])).

thf('57',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k2_xboole_0 @ X35 @ X36 )
      = ( k5_xboole_0 @ X35 @ ( k5_xboole_0 @ X36 @ ( k3_xboole_0 @ X35 @ X36 ) ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('58',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X31 @ X32 ) @ X33 )
      = ( k5_xboole_0 @ X31 @ ( k5_xboole_0 @ X32 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X31 @ X32 ) @ X33 )
      = ( k5_xboole_0 @ X31 @ ( k5_xboole_0 @ X32 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['56','61'])).

thf('63',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('64',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k3_xboole_0 @ X18 @ X19 ) )
      = ( k4_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('65',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k3_xboole_0 @ X22 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X22 @ X23 ) @ X24 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('68',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('69',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['19','20'])).

thf(t34_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k4_xboole_0 @ C @ B ) @ ( k4_xboole_0 @ C @ A ) ) ) )).

thf('70',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X11 @ X12 )
      | ( r1_tarski @ ( k4_xboole_0 @ X13 @ X12 ) @ ( k4_xboole_0 @ X13 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t34_xboole_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X7: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ X7 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['68','75'])).

thf('77',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k3_xboole_0 @ X22 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X22 @ X23 ) @ X24 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['66','67','78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['62','63','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['25','49','81'])).

thf('83',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X11 @ X12 )
      | ( r1_tarski @ ( k4_xboole_0 @ X13 @ X12 ) @ ( k4_xboole_0 @ X13 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t34_xboole_1])).

thf('85',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ sk_C ) @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r1_tarski @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X15 @ X16 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('87',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_C @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_B ) @ ( k2_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['82','87'])).

thf('89',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_B @ sk_A ) @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X7: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ X7 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('91',plain,
    ( ( k4_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_A ) @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('93',plain,
    ( ( k4_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_A ) @ k1_xboole_0 )
    = ( k3_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_A ) @ sk_C ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('96',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = ( k3_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['93','94','95'])).

thf('97',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k2_xboole_0 @ X35 @ X36 )
      = ( k5_xboole_0 @ X35 @ ( k5_xboole_0 @ X36 @ ( k3_xboole_0 @ X35 @ X36 ) ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('98',plain,
    ( ( k2_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_B @ sk_A ) )
    = ( k5_xboole_0 @ sk_C @ ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_A ) @ ( k4_xboole_0 @ sk_B @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X34: $i] :
      ( ( k5_xboole_0 @ X34 @ X34 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('100',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('102',plain,
    ( ( k2_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_B @ sk_A ) )
    = sk_C ),
    inference(demod,[status(thm)],['98','99','100','101'])).

thf('103',plain,(
    r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_B ) @ sk_C ),
    inference(demod,[status(thm)],['88','102'])).

thf('104',plain,(
    $false ),
    inference(demod,[status(thm)],['0','103'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QQsosuKZVI
% 0.15/0.35  % Computer   : n005.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 10:00:48 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.36  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 1.81/2.05  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.81/2.05  % Solved by: fo/fo7.sh
% 1.81/2.05  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.81/2.05  % done 3698 iterations in 1.589s
% 1.81/2.05  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.81/2.05  % SZS output start Refutation
% 1.81/2.05  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.81/2.05  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.81/2.05  thf(sk_A_type, type, sk_A: $i).
% 1.81/2.05  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.81/2.05  thf(sk_B_type, type, sk_B: $i).
% 1.81/2.05  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.81/2.05  thf(sk_C_type, type, sk_C: $i).
% 1.81/2.05  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.81/2.05  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.81/2.05  thf(t97_xboole_1, conjecture,
% 1.81/2.05    (![A:$i,B:$i,C:$i]:
% 1.81/2.05     ( ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) & 
% 1.81/2.05         ( r1_tarski @ ( k4_xboole_0 @ B @ A ) @ C ) ) =>
% 1.81/2.05       ( r1_tarski @ ( k5_xboole_0 @ A @ B ) @ C ) ))).
% 1.81/2.05  thf(zf_stmt_0, negated_conjecture,
% 1.81/2.05    (~( ![A:$i,B:$i,C:$i]:
% 1.81/2.05        ( ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) & 
% 1.81/2.05            ( r1_tarski @ ( k4_xboole_0 @ B @ A ) @ C ) ) =>
% 1.81/2.05          ( r1_tarski @ ( k5_xboole_0 @ A @ B ) @ C ) ) )),
% 1.81/2.05    inference('cnf.neg', [status(esa)], [t97_xboole_1])).
% 1.81/2.05  thf('0', plain, (~ (r1_tarski @ (k5_xboole_0 @ sk_A @ sk_B) @ sk_C)),
% 1.81/2.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.05  thf(t96_xboole_1, axiom,
% 1.81/2.05    (![A:$i,B:$i]:
% 1.81/2.05     ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ))).
% 1.81/2.05  thf('1', plain,
% 1.81/2.05      (![X37 : $i, X38 : $i]:
% 1.81/2.05         (r1_tarski @ (k4_xboole_0 @ X37 @ X38) @ (k5_xboole_0 @ X37 @ X38))),
% 1.81/2.05      inference('cnf', [status(esa)], [t96_xboole_1])).
% 1.81/2.05  thf(l32_xboole_1, axiom,
% 1.81/2.05    (![A:$i,B:$i]:
% 1.81/2.05     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.81/2.05  thf('2', plain,
% 1.81/2.05      (![X7 : $i, X9 : $i]:
% 1.81/2.05         (((k4_xboole_0 @ X7 @ X9) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ X9))),
% 1.81/2.05      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.81/2.05  thf('3', plain,
% 1.81/2.05      (![X0 : $i, X1 : $i]:
% 1.81/2.05         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 1.81/2.05           = (k1_xboole_0))),
% 1.81/2.05      inference('sup-', [status(thm)], ['1', '2'])).
% 1.81/2.05  thf(d6_xboole_0, axiom,
% 1.81/2.05    (![A:$i,B:$i]:
% 1.81/2.05     ( ( k5_xboole_0 @ A @ B ) =
% 1.81/2.05       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 1.81/2.05  thf('4', plain,
% 1.81/2.05      (![X4 : $i, X5 : $i]:
% 1.81/2.05         ((k5_xboole_0 @ X4 @ X5)
% 1.81/2.05           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 1.81/2.05      inference('cnf', [status(esa)], [d6_xboole_0])).
% 1.81/2.05  thf('5', plain,
% 1.81/2.05      (![X0 : $i, X1 : $i]:
% 1.81/2.05         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 1.81/2.05           = (k2_xboole_0 @ k1_xboole_0 @ 
% 1.81/2.05              (k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))))),
% 1.81/2.05      inference('sup+', [status(thm)], ['3', '4'])).
% 1.81/2.05  thf(commutativity_k5_xboole_0, axiom,
% 1.81/2.05    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 1.81/2.05  thf('6', plain,
% 1.81/2.05      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 1.81/2.05      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.81/2.05  thf(t91_xboole_1, axiom,
% 1.81/2.05    (![A:$i,B:$i,C:$i]:
% 1.81/2.05     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 1.81/2.05       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 1.81/2.05  thf('7', plain,
% 1.81/2.05      (![X31 : $i, X32 : $i, X33 : $i]:
% 1.81/2.05         ((k5_xboole_0 @ (k5_xboole_0 @ X31 @ X32) @ X33)
% 1.81/2.05           = (k5_xboole_0 @ X31 @ (k5_xboole_0 @ X32 @ X33)))),
% 1.81/2.05      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.81/2.05  thf(t3_boole, axiom,
% 1.81/2.05    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.81/2.05  thf('8', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 1.81/2.05      inference('cnf', [status(esa)], [t3_boole])).
% 1.81/2.05  thf('9', plain,
% 1.81/2.05      (![X4 : $i, X5 : $i]:
% 1.81/2.05         ((k5_xboole_0 @ X4 @ X5)
% 1.81/2.05           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 1.81/2.05      inference('cnf', [status(esa)], [d6_xboole_0])).
% 1.81/2.05  thf('10', plain,
% 1.81/2.05      (![X0 : $i]:
% 1.81/2.05         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 1.81/2.05           = (k2_xboole_0 @ (k4_xboole_0 @ k1_xboole_0 @ X0) @ X0))),
% 1.81/2.05      inference('sup+', [status(thm)], ['8', '9'])).
% 1.81/2.05  thf('11', plain,
% 1.81/2.05      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 1.81/2.05      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.81/2.05  thf(t5_boole, axiom,
% 1.81/2.05    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.81/2.05  thf('12', plain, (![X25 : $i]: ((k5_xboole_0 @ X25 @ k1_xboole_0) = (X25))),
% 1.81/2.05      inference('cnf', [status(esa)], [t5_boole])).
% 1.81/2.05  thf('13', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.81/2.05      inference('sup+', [status(thm)], ['11', '12'])).
% 1.81/2.05  thf('14', plain,
% 1.81/2.05      (![X0 : $i]:
% 1.81/2.05         ((X0) = (k2_xboole_0 @ (k4_xboole_0 @ k1_xboole_0 @ X0) @ X0))),
% 1.81/2.05      inference('demod', [status(thm)], ['10', '13'])).
% 1.81/2.05  thf('15', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.81/2.05      inference('sup+', [status(thm)], ['11', '12'])).
% 1.81/2.05  thf('16', plain,
% 1.81/2.05      (![X37 : $i, X38 : $i]:
% 1.81/2.05         (r1_tarski @ (k4_xboole_0 @ X37 @ X38) @ (k5_xboole_0 @ X37 @ X38))),
% 1.81/2.05      inference('cnf', [status(esa)], [t96_xboole_1])).
% 1.81/2.05  thf('17', plain,
% 1.81/2.05      (![X0 : $i]: (r1_tarski @ (k4_xboole_0 @ k1_xboole_0 @ X0) @ X0)),
% 1.81/2.05      inference('sup+', [status(thm)], ['15', '16'])).
% 1.81/2.05  thf(t44_xboole_1, axiom,
% 1.81/2.05    (![A:$i,B:$i,C:$i]:
% 1.81/2.05     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 1.81/2.05       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 1.81/2.05  thf('18', plain,
% 1.81/2.05      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.81/2.05         ((r1_tarski @ X15 @ (k2_xboole_0 @ X16 @ X17))
% 1.81/2.05          | ~ (r1_tarski @ (k4_xboole_0 @ X15 @ X16) @ X17))),
% 1.81/2.05      inference('cnf', [status(esa)], [t44_xboole_1])).
% 1.81/2.05  thf('19', plain,
% 1.81/2.05      (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ (k2_xboole_0 @ X0 @ X0))),
% 1.81/2.05      inference('sup-', [status(thm)], ['17', '18'])).
% 1.81/2.05  thf(idempotence_k2_xboole_0, axiom,
% 1.81/2.05    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 1.81/2.05  thf('20', plain, (![X6 : $i]: ((k2_xboole_0 @ X6 @ X6) = (X6))),
% 1.81/2.05      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 1.81/2.05  thf('21', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.81/2.05      inference('demod', [status(thm)], ['19', '20'])).
% 1.81/2.05  thf('22', plain,
% 1.81/2.05      (![X7 : $i, X9 : $i]:
% 1.81/2.05         (((k4_xboole_0 @ X7 @ X9) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ X9))),
% 1.81/2.05      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.81/2.05  thf('23', plain,
% 1.81/2.05      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.81/2.05      inference('sup-', [status(thm)], ['21', '22'])).
% 1.81/2.05  thf('24', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 1.81/2.05      inference('demod', [status(thm)], ['14', '23'])).
% 1.81/2.05  thf('25', plain,
% 1.81/2.05      (![X0 : $i, X1 : $i]:
% 1.81/2.05         ((k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))
% 1.81/2.05           = (k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0)))),
% 1.81/2.05      inference('demod', [status(thm)], ['5', '6', '7', '24'])).
% 1.81/2.05  thf(t94_xboole_1, axiom,
% 1.81/2.05    (![A:$i,B:$i]:
% 1.81/2.05     ( ( k2_xboole_0 @ A @ B ) =
% 1.81/2.05       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.81/2.05  thf('26', plain,
% 1.81/2.05      (![X35 : $i, X36 : $i]:
% 1.81/2.05         ((k2_xboole_0 @ X35 @ X36)
% 1.81/2.05           = (k5_xboole_0 @ (k5_xboole_0 @ X35 @ X36) @ 
% 1.81/2.05              (k3_xboole_0 @ X35 @ X36)))),
% 1.81/2.05      inference('cnf', [status(esa)], [t94_xboole_1])).
% 1.81/2.05  thf('27', plain,
% 1.81/2.05      (![X31 : $i, X32 : $i, X33 : $i]:
% 1.81/2.05         ((k5_xboole_0 @ (k5_xboole_0 @ X31 @ X32) @ X33)
% 1.81/2.05           = (k5_xboole_0 @ X31 @ (k5_xboole_0 @ X32 @ X33)))),
% 1.81/2.05      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.81/2.05  thf('28', plain,
% 1.81/2.05      (![X35 : $i, X36 : $i]:
% 1.81/2.05         ((k2_xboole_0 @ X35 @ X36)
% 1.81/2.05           = (k5_xboole_0 @ X35 @ 
% 1.81/2.05              (k5_xboole_0 @ X36 @ (k3_xboole_0 @ X35 @ X36))))),
% 1.81/2.05      inference('demod', [status(thm)], ['26', '27'])).
% 1.81/2.05  thf(commutativity_k3_xboole_0, axiom,
% 1.81/2.05    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.81/2.05  thf('29', plain,
% 1.81/2.05      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.81/2.05      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.81/2.05  thf(t47_xboole_1, axiom,
% 1.81/2.05    (![A:$i,B:$i]:
% 1.81/2.05     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 1.81/2.05  thf('30', plain,
% 1.81/2.05      (![X18 : $i, X19 : $i]:
% 1.81/2.05         ((k4_xboole_0 @ X18 @ (k3_xboole_0 @ X18 @ X19))
% 1.81/2.05           = (k4_xboole_0 @ X18 @ X19))),
% 1.81/2.05      inference('cnf', [status(esa)], [t47_xboole_1])).
% 1.81/2.05  thf('31', plain,
% 1.81/2.05      (![X0 : $i, X1 : $i]:
% 1.81/2.05         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 1.81/2.05           = (k4_xboole_0 @ X0 @ X1))),
% 1.81/2.05      inference('sup+', [status(thm)], ['29', '30'])).
% 1.81/2.05  thf('32', plain,
% 1.81/2.05      (![X4 : $i, X5 : $i]:
% 1.81/2.05         ((k5_xboole_0 @ X4 @ X5)
% 1.81/2.05           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 1.81/2.05      inference('cnf', [status(esa)], [d6_xboole_0])).
% 1.81/2.05  thf('33', plain,
% 1.81/2.05      (![X0 : $i, X1 : $i]:
% 1.81/2.05         ((k5_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1))
% 1.81/2.05           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 1.81/2.05              (k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X1)))),
% 1.81/2.05      inference('sup+', [status(thm)], ['31', '32'])).
% 1.81/2.05  thf(t49_xboole_1, axiom,
% 1.81/2.05    (![A:$i,B:$i,C:$i]:
% 1.81/2.05     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 1.81/2.05       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 1.81/2.05  thf('34', plain,
% 1.81/2.05      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.81/2.05         ((k3_xboole_0 @ X22 @ (k4_xboole_0 @ X23 @ X24))
% 1.81/2.05           = (k4_xboole_0 @ (k3_xboole_0 @ X22 @ X23) @ X24))),
% 1.81/2.05      inference('cnf', [status(esa)], [t49_xboole_1])).
% 1.81/2.05  thf('35', plain, (![X6 : $i]: ((k2_xboole_0 @ X6 @ X6) = (X6))),
% 1.81/2.05      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 1.81/2.05  thf('36', plain,
% 1.81/2.05      (![X4 : $i, X5 : $i]:
% 1.81/2.05         ((k5_xboole_0 @ X4 @ X5)
% 1.81/2.05           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 1.81/2.05      inference('cnf', [status(esa)], [d6_xboole_0])).
% 1.81/2.05  thf('37', plain,
% 1.81/2.05      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 1.81/2.05      inference('sup+', [status(thm)], ['35', '36'])).
% 1.81/2.05  thf(t92_xboole_1, axiom,
% 1.81/2.05    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 1.81/2.05  thf('38', plain, (![X34 : $i]: ((k5_xboole_0 @ X34 @ X34) = (k1_xboole_0))),
% 1.81/2.05      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.81/2.05  thf('39', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 1.81/2.05      inference('demod', [status(thm)], ['37', '38'])).
% 1.81/2.05  thf(t2_boole, axiom,
% 1.81/2.05    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 1.81/2.05  thf('40', plain,
% 1.81/2.05      (![X10 : $i]: ((k3_xboole_0 @ X10 @ k1_xboole_0) = (k1_xboole_0))),
% 1.81/2.05      inference('cnf', [status(esa)], [t2_boole])).
% 1.81/2.05  thf('41', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 1.81/2.05      inference('cnf', [status(esa)], [t3_boole])).
% 1.81/2.05  thf('42', plain,
% 1.81/2.05      (![X4 : $i, X5 : $i]:
% 1.81/2.05         ((k5_xboole_0 @ X4 @ X5)
% 1.81/2.05           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 1.81/2.05      inference('cnf', [status(esa)], [d6_xboole_0])).
% 1.81/2.05  thf('43', plain,
% 1.81/2.05      (![X0 : $i]:
% 1.81/2.05         ((k5_xboole_0 @ X0 @ k1_xboole_0)
% 1.81/2.05           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 1.81/2.05      inference('sup+', [status(thm)], ['41', '42'])).
% 1.81/2.05  thf('44', plain, (![X25 : $i]: ((k5_xboole_0 @ X25 @ k1_xboole_0) = (X25))),
% 1.81/2.05      inference('cnf', [status(esa)], [t5_boole])).
% 1.81/2.05  thf('45', plain,
% 1.81/2.05      (![X0 : $i]:
% 1.81/2.05         ((X0) = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 1.81/2.05      inference('demod', [status(thm)], ['43', '44'])).
% 1.81/2.05  thf('46', plain,
% 1.81/2.05      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.81/2.05      inference('sup-', [status(thm)], ['21', '22'])).
% 1.81/2.05  thf('47', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 1.81/2.05      inference('demod', [status(thm)], ['45', '46'])).
% 1.81/2.05  thf('48', plain,
% 1.81/2.05      (![X0 : $i, X1 : $i]:
% 1.81/2.05         ((k5_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1))
% 1.81/2.05           = (k4_xboole_0 @ X1 @ X0))),
% 1.81/2.05      inference('demod', [status(thm)], ['33', '34', '39', '40', '47'])).
% 1.81/2.05  thf('49', plain,
% 1.81/2.05      (![X35 : $i, X36 : $i]:
% 1.81/2.05         ((k2_xboole_0 @ X35 @ X36)
% 1.81/2.05           = (k5_xboole_0 @ X35 @ (k4_xboole_0 @ X36 @ X35)))),
% 1.81/2.05      inference('demod', [status(thm)], ['28', '48'])).
% 1.81/2.05  thf('50', plain,
% 1.81/2.05      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 1.81/2.05      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.81/2.05  thf('51', plain, (![X34 : $i]: ((k5_xboole_0 @ X34 @ X34) = (k1_xboole_0))),
% 1.81/2.05      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.81/2.05  thf('52', plain,
% 1.81/2.05      (![X31 : $i, X32 : $i, X33 : $i]:
% 1.81/2.05         ((k5_xboole_0 @ (k5_xboole_0 @ X31 @ X32) @ X33)
% 1.81/2.05           = (k5_xboole_0 @ X31 @ (k5_xboole_0 @ X32 @ X33)))),
% 1.81/2.05      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.81/2.05  thf('53', plain,
% 1.81/2.05      (![X0 : $i, X1 : $i]:
% 1.81/2.05         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 1.81/2.05           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.81/2.05      inference('sup+', [status(thm)], ['51', '52'])).
% 1.81/2.05  thf('54', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.81/2.05      inference('sup+', [status(thm)], ['11', '12'])).
% 1.81/2.05  thf('55', plain,
% 1.81/2.05      (![X0 : $i, X1 : $i]:
% 1.81/2.05         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.81/2.05      inference('demod', [status(thm)], ['53', '54'])).
% 1.81/2.05  thf('56', plain,
% 1.81/2.05      (![X0 : $i, X1 : $i]:
% 1.81/2.05         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.81/2.05      inference('sup+', [status(thm)], ['50', '55'])).
% 1.81/2.05  thf('57', plain,
% 1.81/2.05      (![X35 : $i, X36 : $i]:
% 1.81/2.05         ((k2_xboole_0 @ X35 @ X36)
% 1.81/2.05           = (k5_xboole_0 @ X35 @ 
% 1.81/2.05              (k5_xboole_0 @ X36 @ (k3_xboole_0 @ X35 @ X36))))),
% 1.81/2.05      inference('demod', [status(thm)], ['26', '27'])).
% 1.81/2.05  thf('58', plain,
% 1.81/2.05      (![X31 : $i, X32 : $i, X33 : $i]:
% 1.81/2.05         ((k5_xboole_0 @ (k5_xboole_0 @ X31 @ X32) @ X33)
% 1.81/2.05           = (k5_xboole_0 @ X31 @ (k5_xboole_0 @ X32 @ X33)))),
% 1.81/2.05      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.81/2.05  thf('59', plain,
% 1.81/2.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.81/2.05         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2)
% 1.81/2.05           = (k5_xboole_0 @ X1 @ 
% 1.81/2.05              (k5_xboole_0 @ (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) @ X2)))),
% 1.81/2.05      inference('sup+', [status(thm)], ['57', '58'])).
% 1.81/2.05  thf('60', plain,
% 1.81/2.05      (![X31 : $i, X32 : $i, X33 : $i]:
% 1.81/2.05         ((k5_xboole_0 @ (k5_xboole_0 @ X31 @ X32) @ X33)
% 1.81/2.05           = (k5_xboole_0 @ X31 @ (k5_xboole_0 @ X32 @ X33)))),
% 1.81/2.05      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.81/2.05  thf('61', plain,
% 1.81/2.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.81/2.05         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2)
% 1.81/2.05           = (k5_xboole_0 @ X1 @ 
% 1.81/2.05              (k5_xboole_0 @ X0 @ (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))))),
% 1.81/2.05      inference('demod', [status(thm)], ['59', '60'])).
% 1.81/2.05  thf('62', plain,
% 1.81/2.05      (![X0 : $i, X1 : $i]:
% 1.81/2.05         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 1.81/2.05           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.81/2.05      inference('sup+', [status(thm)], ['56', '61'])).
% 1.81/2.05  thf('63', plain,
% 1.81/2.05      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 1.81/2.05      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.81/2.05  thf('64', plain,
% 1.81/2.05      (![X18 : $i, X19 : $i]:
% 1.81/2.05         ((k4_xboole_0 @ X18 @ (k3_xboole_0 @ X18 @ X19))
% 1.81/2.05           = (k4_xboole_0 @ X18 @ X19))),
% 1.81/2.05      inference('cnf', [status(esa)], [t47_xboole_1])).
% 1.81/2.05  thf('65', plain,
% 1.81/2.05      (![X4 : $i, X5 : $i]:
% 1.81/2.05         ((k5_xboole_0 @ X4 @ X5)
% 1.81/2.05           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 1.81/2.05      inference('cnf', [status(esa)], [d6_xboole_0])).
% 1.81/2.05  thf('66', plain,
% 1.81/2.05      (![X0 : $i, X1 : $i]:
% 1.81/2.05         ((k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 1.81/2.05           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 1.81/2.05              (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)))),
% 1.81/2.05      inference('sup+', [status(thm)], ['64', '65'])).
% 1.81/2.05  thf('67', plain,
% 1.81/2.05      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.81/2.05         ((k3_xboole_0 @ X22 @ (k4_xboole_0 @ X23 @ X24))
% 1.81/2.05           = (k4_xboole_0 @ (k3_xboole_0 @ X22 @ X23) @ X24))),
% 1.81/2.05      inference('cnf', [status(esa)], [t49_xboole_1])).
% 1.81/2.05  thf(t48_xboole_1, axiom,
% 1.81/2.05    (![A:$i,B:$i]:
% 1.81/2.05     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.81/2.05  thf('68', plain,
% 1.81/2.05      (![X20 : $i, X21 : $i]:
% 1.81/2.05         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X20 @ X21))
% 1.81/2.05           = (k3_xboole_0 @ X20 @ X21))),
% 1.81/2.05      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.81/2.05  thf('69', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.81/2.05      inference('demod', [status(thm)], ['19', '20'])).
% 1.81/2.05  thf(t34_xboole_1, axiom,
% 1.81/2.05    (![A:$i,B:$i,C:$i]:
% 1.81/2.05     ( ( r1_tarski @ A @ B ) =>
% 1.81/2.05       ( r1_tarski @ ( k4_xboole_0 @ C @ B ) @ ( k4_xboole_0 @ C @ A ) ) ))).
% 1.81/2.05  thf('70', plain,
% 1.81/2.05      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.81/2.05         (~ (r1_tarski @ X11 @ X12)
% 1.81/2.05          | (r1_tarski @ (k4_xboole_0 @ X13 @ X12) @ (k4_xboole_0 @ X13 @ X11)))),
% 1.81/2.05      inference('cnf', [status(esa)], [t34_xboole_1])).
% 1.81/2.05  thf('71', plain,
% 1.81/2.05      (![X0 : $i, X1 : $i]:
% 1.81/2.05         (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ 
% 1.81/2.05          (k4_xboole_0 @ X1 @ k1_xboole_0))),
% 1.81/2.05      inference('sup-', [status(thm)], ['69', '70'])).
% 1.81/2.05  thf('72', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 1.81/2.05      inference('cnf', [status(esa)], [t3_boole])).
% 1.81/2.05  thf('73', plain,
% 1.81/2.05      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X1)),
% 1.81/2.05      inference('demod', [status(thm)], ['71', '72'])).
% 1.81/2.05  thf('74', plain,
% 1.81/2.05      (![X7 : $i, X9 : $i]:
% 1.81/2.05         (((k4_xboole_0 @ X7 @ X9) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ X9))),
% 1.81/2.05      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.81/2.05  thf('75', plain,
% 1.81/2.05      (![X0 : $i, X1 : $i]:
% 1.81/2.05         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 1.81/2.05      inference('sup-', [status(thm)], ['73', '74'])).
% 1.81/2.05  thf('76', plain,
% 1.81/2.05      (![X0 : $i, X1 : $i]:
% 1.81/2.05         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1) = (k1_xboole_0))),
% 1.81/2.05      inference('sup+', [status(thm)], ['68', '75'])).
% 1.81/2.05  thf('77', plain,
% 1.81/2.05      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.81/2.05         ((k3_xboole_0 @ X22 @ (k4_xboole_0 @ X23 @ X24))
% 1.81/2.05           = (k4_xboole_0 @ (k3_xboole_0 @ X22 @ X23) @ X24))),
% 1.81/2.05      inference('cnf', [status(esa)], [t49_xboole_1])).
% 1.81/2.05  thf('78', plain,
% 1.81/2.05      (![X0 : $i, X1 : $i]:
% 1.81/2.05         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 1.81/2.05      inference('demod', [status(thm)], ['76', '77'])).
% 1.81/2.05  thf('79', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 1.81/2.05      inference('demod', [status(thm)], ['45', '46'])).
% 1.81/2.05  thf('80', plain,
% 1.81/2.05      (![X0 : $i, X1 : $i]:
% 1.81/2.05         ((k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 1.81/2.05           = (k4_xboole_0 @ X1 @ X0))),
% 1.81/2.05      inference('demod', [status(thm)], ['66', '67', '78', '79'])).
% 1.81/2.05  thf('81', plain,
% 1.81/2.05      (![X0 : $i, X1 : $i]:
% 1.81/2.05         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 1.81/2.05           = (k4_xboole_0 @ X1 @ X0))),
% 1.81/2.05      inference('demod', [status(thm)], ['62', '63', '80'])).
% 1.81/2.05  thf('82', plain,
% 1.81/2.05      (![X0 : $i, X1 : $i]:
% 1.81/2.05         ((k4_xboole_0 @ X0 @ X1)
% 1.81/2.05           = (k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0)))),
% 1.81/2.05      inference('demod', [status(thm)], ['25', '49', '81'])).
% 1.81/2.05  thf('83', plain, ((r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_C)),
% 1.81/2.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.05  thf('84', plain,
% 1.81/2.05      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.81/2.05         (~ (r1_tarski @ X11 @ X12)
% 1.81/2.05          | (r1_tarski @ (k4_xboole_0 @ X13 @ X12) @ (k4_xboole_0 @ X13 @ X11)))),
% 1.81/2.05      inference('cnf', [status(esa)], [t34_xboole_1])).
% 1.81/2.05  thf('85', plain,
% 1.81/2.05      (![X0 : $i]:
% 1.81/2.05         (r1_tarski @ (k4_xboole_0 @ X0 @ sk_C) @ 
% 1.81/2.05          (k4_xboole_0 @ X0 @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 1.81/2.05      inference('sup-', [status(thm)], ['83', '84'])).
% 1.81/2.05  thf('86', plain,
% 1.81/2.05      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.81/2.05         ((r1_tarski @ X15 @ (k2_xboole_0 @ X16 @ X17))
% 1.81/2.05          | ~ (r1_tarski @ (k4_xboole_0 @ X15 @ X16) @ X17))),
% 1.81/2.05      inference('cnf', [status(esa)], [t44_xboole_1])).
% 1.81/2.05  thf('87', plain,
% 1.81/2.05      (![X0 : $i]:
% 1.81/2.05         (r1_tarski @ X0 @ 
% 1.81/2.05          (k2_xboole_0 @ sk_C @ 
% 1.81/2.05           (k4_xboole_0 @ X0 @ (k4_xboole_0 @ sk_A @ sk_B))))),
% 1.81/2.05      inference('sup-', [status(thm)], ['85', '86'])).
% 1.81/2.05  thf('88', plain,
% 1.81/2.05      ((r1_tarski @ (k5_xboole_0 @ sk_A @ sk_B) @ 
% 1.81/2.05        (k2_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_B @ sk_A)))),
% 1.81/2.05      inference('sup+', [status(thm)], ['82', '87'])).
% 1.81/2.05  thf('89', plain, ((r1_tarski @ (k4_xboole_0 @ sk_B @ sk_A) @ sk_C)),
% 1.81/2.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.05  thf('90', plain,
% 1.81/2.05      (![X7 : $i, X9 : $i]:
% 1.81/2.05         (((k4_xboole_0 @ X7 @ X9) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ X9))),
% 1.81/2.05      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.81/2.05  thf('91', plain,
% 1.81/2.05      (((k4_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_A) @ sk_C) = (k1_xboole_0))),
% 1.81/2.05      inference('sup-', [status(thm)], ['89', '90'])).
% 1.81/2.05  thf('92', plain,
% 1.81/2.05      (![X20 : $i, X21 : $i]:
% 1.81/2.05         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X20 @ X21))
% 1.81/2.05           = (k3_xboole_0 @ X20 @ X21))),
% 1.81/2.05      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.81/2.05  thf('93', plain,
% 1.81/2.05      (((k4_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_A) @ k1_xboole_0)
% 1.81/2.05         = (k3_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_A) @ sk_C))),
% 1.81/2.05      inference('sup+', [status(thm)], ['91', '92'])).
% 1.81/2.05  thf('94', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 1.81/2.05      inference('cnf', [status(esa)], [t3_boole])).
% 1.81/2.05  thf('95', plain,
% 1.81/2.05      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.81/2.05      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.81/2.05  thf('96', plain,
% 1.81/2.05      (((k4_xboole_0 @ sk_B @ sk_A)
% 1.81/2.05         = (k3_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_B @ sk_A)))),
% 1.81/2.05      inference('demod', [status(thm)], ['93', '94', '95'])).
% 1.81/2.05  thf('97', plain,
% 1.81/2.05      (![X35 : $i, X36 : $i]:
% 1.81/2.05         ((k2_xboole_0 @ X35 @ X36)
% 1.81/2.05           = (k5_xboole_0 @ X35 @ 
% 1.81/2.05              (k5_xboole_0 @ X36 @ (k3_xboole_0 @ X35 @ X36))))),
% 1.81/2.05      inference('demod', [status(thm)], ['26', '27'])).
% 1.81/2.05  thf('98', plain,
% 1.81/2.05      (((k2_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_B @ sk_A))
% 1.81/2.05         = (k5_xboole_0 @ sk_C @ 
% 1.81/2.05            (k5_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_A) @ 
% 1.81/2.05             (k4_xboole_0 @ sk_B @ sk_A))))),
% 1.81/2.05      inference('sup+', [status(thm)], ['96', '97'])).
% 1.81/2.05  thf('99', plain, (![X34 : $i]: ((k5_xboole_0 @ X34 @ X34) = (k1_xboole_0))),
% 1.81/2.05      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.81/2.05  thf('100', plain,
% 1.81/2.05      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 1.81/2.05      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.81/2.05  thf('101', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.81/2.05      inference('sup+', [status(thm)], ['11', '12'])).
% 1.81/2.05  thf('102', plain,
% 1.81/2.05      (((k2_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_B @ sk_A)) = (sk_C))),
% 1.81/2.05      inference('demod', [status(thm)], ['98', '99', '100', '101'])).
% 1.81/2.05  thf('103', plain, ((r1_tarski @ (k5_xboole_0 @ sk_A @ sk_B) @ sk_C)),
% 1.81/2.05      inference('demod', [status(thm)], ['88', '102'])).
% 1.81/2.05  thf('104', plain, ($false), inference('demod', [status(thm)], ['0', '103'])).
% 1.81/2.05  
% 1.81/2.05  % SZS output end Refutation
% 1.81/2.05  
% 1.90/2.06  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
