%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.h1Rnj8zt1C

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:58 EST 2020

% Result     : Theorem 1.94s
% Output     : Refutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :  150 (1131 expanded)
%              Number of leaves         :   26 ( 394 expanded)
%              Depth                    :   27
%              Number of atoms          : 1305 (8844 expanded)
%              Number of equality atoms :  149 (1141 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t141_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( ( k4_xboole_0 @ ( k2_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) )
        = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ~ ( r2_hidden @ A @ B )
       => ( ( k4_xboole_0 @ ( k2_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) )
          = B ) ) ),
    inference('cnf.neg',[status(esa)],[t141_zfmisc_1])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('1',plain,(
    ! [X21: $i,X25: $i] :
      ( ( X25
        = ( k1_tarski @ X21 ) )
      | ( ( sk_C @ X25 @ X21 )
        = X21 )
      | ( r2_hidden @ ( sk_C @ X25 @ X21 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ X8 @ X5 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('3',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
        = X2 )
      | ( ( k4_xboole_0 @ X1 @ X0 )
        = ( k1_tarski @ X2 ) )
      | ( r2_hidden @ ( sk_C @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X21: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X24 @ X23 )
      | ( X24 = X21 )
      | ( X23
       != ( k1_tarski @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('6',plain,(
    ! [X21: $i,X24: $i] :
      ( ( X24 = X21 )
      | ~ ( r2_hidden @ X24 @ ( k1_tarski @ X21 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X2 )
        = ( k1_tarski @ X1 ) )
      | ( ( sk_C @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) @ X1 )
        = X1 )
      | ( ( sk_C @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 != X2 )
      | ( ( sk_C @ ( k4_xboole_0 @ ( k1_tarski @ X2 ) @ X1 ) @ X0 )
        = X2 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X2 ) @ X1 )
        = ( k1_tarski @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['7'])).

thf('9',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X2 ) @ X1 )
        = ( k1_tarski @ X2 ) )
      | ( ( sk_C @ ( k4_xboole_0 @ ( k1_tarski @ X2 ) @ X1 ) @ X2 )
        = X2 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( X22 != X21 )
      | ( r2_hidden @ X22 @ X23 )
      | ( X23
       != ( k1_tarski @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('11',plain,(
    ! [X21: $i] :
      ( r2_hidden @ X21 @ ( k1_tarski @ X21 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ( r2_hidden @ X4 @ X6 )
      | ( r2_hidden @ X4 @ X7 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('13',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X4 @ ( k4_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ X4 @ X6 )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X2 ) @ X1 )
        = ( k1_tarski @ X2 ) )
      | ( ( sk_C @ ( k4_xboole_0 @ ( k1_tarski @ X2 ) @ X1 ) @ X2 )
        = X2 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('16',plain,(
    ! [X21: $i,X25: $i] :
      ( ( X25
        = ( k1_tarski @ X21 ) )
      | ( ( sk_C @ X25 @ X21 )
       != X21 )
      | ~ ( r2_hidden @ ( sk_C @ X25 @ X21 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) @ X0 )
       != X0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) @ X0 )
       != X0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = ( k1_tarski @ X1 ) )
      | ( ( sk_C @ ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) @ X1 )
       != X1 ) ) ),
    inference('sup-',[status(thm)],['14','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != X0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k1_tarski @ X0 ) )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('24',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k3_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X19 @ X20 ) @ ( k2_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('25',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('26',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k3_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X19 @ X20 ) @ ( k5_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('29',plain,(
    ! [X18: $i] :
      ( ( k5_xboole_0 @ X18 @ X18 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('30',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k5_xboole_0 @ X15 @ ( k5_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('32',plain,(
    ! [X26: $i] :
      ( ( k2_tarski @ X26 @ X26 )
      = ( k1_tarski @ X26 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t31_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_tarski @ A ) )
      = A ) )).

thf('33',plain,(
    ! [X56: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X56 ) )
      = X56 ) ),
    inference(cnf,[status(esa)],[t31_zfmisc_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('35',plain,(
    ! [X54: $i,X55: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X54 @ X55 ) )
      = ( k2_xboole_0 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k3_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X19 @ X20 ) @ ( k5_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('39',plain,(
    ! [X10: $i] :
      ( ( k3_xboole_0 @ X10 @ X10 )
      = X10 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('40',plain,(
    ! [X18: $i] :
      ( ( k5_xboole_0 @ X18 @ X18 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['31','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['28','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['27','45'])).

thf('47',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('48',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k5_xboole_0 @ X15 @ ( k5_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('50',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['46','49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['28','44'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k5_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['21','56'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('58',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X13 @ X14 ) @ X14 )
      = ( k4_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['46','49','50'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['46','49','50'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['46','49','50'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['31','43'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['67','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['66','71'])).

thf('73',plain,(
    ! [X18: $i] :
      ( ( k5_xboole_0 @ X18 @ X18 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['63','74'])).

thf('76',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['31','43'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['75','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['62','81'])).

thf('83',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('84',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k3_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X19 @ X20 ) @ ( k5_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['23','26'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['28','44'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['87','90'])).

thf('92',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k3_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X19 @ X20 ) @ ( k5_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('93',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k5_xboole_0 @ X15 @ ( k5_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('94',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k5_xboole_0 @ X15 @ ( k5_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('96',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X2 ) ) ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k5_xboole_0 @ X15 @ ( k5_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('98',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('99',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['67','70'])).

thf('102',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['96','99','100','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['91','102'])).

thf('104',plain,(
    ! [X18: $i] :
      ( ( k5_xboole_0 @ X18 @ X18 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['82','105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['62','81'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k5_xboole_0 @ X15 @ ( k5_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['28','44'])).

thf('111',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X2 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X2 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X2 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['108','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('114',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X2 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['67','70'])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['57','114','115'])).

thf('117',plain,(
    ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X13 @ X14 ) @ X14 )
      = ( k4_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('119',plain,(
    ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
 != sk_B ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,
    ( ( sk_B != sk_B )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['116','119'])).

thf('121',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['120'])).

thf('122',plain,(
    $false ),
    inference(demod,[status(thm)],['0','121'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.h1Rnj8zt1C
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:26:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.94/2.20  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.94/2.20  % Solved by: fo/fo7.sh
% 1.94/2.20  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.94/2.20  % done 2425 iterations in 1.721s
% 1.94/2.20  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.94/2.20  % SZS output start Refutation
% 1.94/2.20  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.94/2.20  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.94/2.20  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.94/2.20  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.94/2.20  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 1.94/2.20  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.94/2.20  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.94/2.20  thf(sk_A_type, type, sk_A: $i).
% 1.94/2.20  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.94/2.20  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.94/2.20  thf(sk_B_type, type, sk_B: $i).
% 1.94/2.20  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.94/2.20  thf(t141_zfmisc_1, conjecture,
% 1.94/2.20    (![A:$i,B:$i]:
% 1.94/2.20     ( ( ~( r2_hidden @ A @ B ) ) =>
% 1.94/2.20       ( ( k4_xboole_0 @
% 1.94/2.20           ( k2_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) ) =
% 1.94/2.20         ( B ) ) ))).
% 1.94/2.20  thf(zf_stmt_0, negated_conjecture,
% 1.94/2.20    (~( ![A:$i,B:$i]:
% 1.94/2.20        ( ( ~( r2_hidden @ A @ B ) ) =>
% 1.94/2.20          ( ( k4_xboole_0 @
% 1.94/2.20              ( k2_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) ) =
% 1.94/2.20            ( B ) ) ) )),
% 1.94/2.20    inference('cnf.neg', [status(esa)], [t141_zfmisc_1])).
% 1.94/2.20  thf('0', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 1.94/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.20  thf(d1_tarski, axiom,
% 1.94/2.20    (![A:$i,B:$i]:
% 1.94/2.20     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 1.94/2.20       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 1.94/2.20  thf('1', plain,
% 1.94/2.20      (![X21 : $i, X25 : $i]:
% 1.94/2.20         (((X25) = (k1_tarski @ X21))
% 1.94/2.20          | ((sk_C @ X25 @ X21) = (X21))
% 1.94/2.20          | (r2_hidden @ (sk_C @ X25 @ X21) @ X25))),
% 1.94/2.20      inference('cnf', [status(esa)], [d1_tarski])).
% 1.94/2.20  thf(d5_xboole_0, axiom,
% 1.94/2.20    (![A:$i,B:$i,C:$i]:
% 1.94/2.20     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 1.94/2.20       ( ![D:$i]:
% 1.94/2.20         ( ( r2_hidden @ D @ C ) <=>
% 1.94/2.20           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 1.94/2.20  thf('2', plain,
% 1.94/2.20      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 1.94/2.20         (~ (r2_hidden @ X8 @ X7)
% 1.94/2.20          | (r2_hidden @ X8 @ X5)
% 1.94/2.20          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 1.94/2.20      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.94/2.20  thf('3', plain,
% 1.94/2.20      (![X5 : $i, X6 : $i, X8 : $i]:
% 1.94/2.20         ((r2_hidden @ X8 @ X5) | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 1.94/2.20      inference('simplify', [status(thm)], ['2'])).
% 1.94/2.20  thf('4', plain,
% 1.94/2.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.94/2.20         (((sk_C @ (k4_xboole_0 @ X1 @ X0) @ X2) = (X2))
% 1.94/2.20          | ((k4_xboole_0 @ X1 @ X0) = (k1_tarski @ X2))
% 1.94/2.20          | (r2_hidden @ (sk_C @ (k4_xboole_0 @ X1 @ X0) @ X2) @ X1))),
% 1.94/2.20      inference('sup-', [status(thm)], ['1', '3'])).
% 1.94/2.20  thf('5', plain,
% 1.94/2.20      (![X21 : $i, X23 : $i, X24 : $i]:
% 1.94/2.20         (~ (r2_hidden @ X24 @ X23)
% 1.94/2.20          | ((X24) = (X21))
% 1.94/2.20          | ((X23) != (k1_tarski @ X21)))),
% 1.94/2.20      inference('cnf', [status(esa)], [d1_tarski])).
% 1.94/2.20  thf('6', plain,
% 1.94/2.20      (![X21 : $i, X24 : $i]:
% 1.94/2.20         (((X24) = (X21)) | ~ (r2_hidden @ X24 @ (k1_tarski @ X21)))),
% 1.94/2.20      inference('simplify', [status(thm)], ['5'])).
% 1.94/2.20  thf('7', plain,
% 1.94/2.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.94/2.20         (((k4_xboole_0 @ (k1_tarski @ X0) @ X2) = (k1_tarski @ X1))
% 1.94/2.20          | ((sk_C @ (k4_xboole_0 @ (k1_tarski @ X0) @ X2) @ X1) = (X1))
% 1.94/2.20          | ((sk_C @ (k4_xboole_0 @ (k1_tarski @ X0) @ X2) @ X1) = (X0)))),
% 1.94/2.20      inference('sup-', [status(thm)], ['4', '6'])).
% 1.94/2.20  thf('8', plain,
% 1.94/2.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.94/2.20         (((X0) != (X2))
% 1.94/2.20          | ((sk_C @ (k4_xboole_0 @ (k1_tarski @ X2) @ X1) @ X0) = (X2))
% 1.94/2.20          | ((k4_xboole_0 @ (k1_tarski @ X2) @ X1) = (k1_tarski @ X0)))),
% 1.94/2.20      inference('eq_fact', [status(thm)], ['7'])).
% 1.94/2.20  thf('9', plain,
% 1.94/2.20      (![X1 : $i, X2 : $i]:
% 1.94/2.20         (((k4_xboole_0 @ (k1_tarski @ X2) @ X1) = (k1_tarski @ X2))
% 1.94/2.20          | ((sk_C @ (k4_xboole_0 @ (k1_tarski @ X2) @ X1) @ X2) = (X2)))),
% 1.94/2.20      inference('simplify', [status(thm)], ['8'])).
% 1.94/2.20  thf('10', plain,
% 1.94/2.20      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.94/2.20         (((X22) != (X21))
% 1.94/2.20          | (r2_hidden @ X22 @ X23)
% 1.94/2.20          | ((X23) != (k1_tarski @ X21)))),
% 1.94/2.20      inference('cnf', [status(esa)], [d1_tarski])).
% 1.94/2.20  thf('11', plain, (![X21 : $i]: (r2_hidden @ X21 @ (k1_tarski @ X21))),
% 1.94/2.20      inference('simplify', [status(thm)], ['10'])).
% 1.94/2.20  thf('12', plain,
% 1.94/2.20      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 1.94/2.20         (~ (r2_hidden @ X4 @ X5)
% 1.94/2.20          | (r2_hidden @ X4 @ X6)
% 1.94/2.20          | (r2_hidden @ X4 @ X7)
% 1.94/2.20          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 1.94/2.20      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.94/2.20  thf('13', plain,
% 1.94/2.20      (![X4 : $i, X5 : $i, X6 : $i]:
% 1.94/2.20         ((r2_hidden @ X4 @ (k4_xboole_0 @ X5 @ X6))
% 1.94/2.20          | (r2_hidden @ X4 @ X6)
% 1.94/2.20          | ~ (r2_hidden @ X4 @ X5))),
% 1.94/2.20      inference('simplify', [status(thm)], ['12'])).
% 1.94/2.20  thf('14', plain,
% 1.94/2.20      (![X0 : $i, X1 : $i]:
% 1.94/2.20         ((r2_hidden @ X0 @ X1)
% 1.94/2.20          | (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 1.94/2.20      inference('sup-', [status(thm)], ['11', '13'])).
% 1.94/2.20  thf('15', plain,
% 1.94/2.20      (![X1 : $i, X2 : $i]:
% 1.94/2.20         (((k4_xboole_0 @ (k1_tarski @ X2) @ X1) = (k1_tarski @ X2))
% 1.94/2.20          | ((sk_C @ (k4_xboole_0 @ (k1_tarski @ X2) @ X1) @ X2) = (X2)))),
% 1.94/2.20      inference('simplify', [status(thm)], ['8'])).
% 1.94/2.20  thf('16', plain,
% 1.94/2.20      (![X21 : $i, X25 : $i]:
% 1.94/2.20         (((X25) = (k1_tarski @ X21))
% 1.94/2.20          | ((sk_C @ X25 @ X21) != (X21))
% 1.94/2.20          | ~ (r2_hidden @ (sk_C @ X25 @ X21) @ X25))),
% 1.94/2.20      inference('cnf', [status(esa)], [d1_tarski])).
% 1.94/2.20  thf('17', plain,
% 1.94/2.20      (![X0 : $i, X1 : $i]:
% 1.94/2.20         (~ (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_tarski @ X0) @ X1))
% 1.94/2.20          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_tarski @ X0))
% 1.94/2.20          | ((sk_C @ (k4_xboole_0 @ (k1_tarski @ X0) @ X1) @ X0) != (X0))
% 1.94/2.20          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_tarski @ X0)))),
% 1.94/2.20      inference('sup-', [status(thm)], ['15', '16'])).
% 1.94/2.20  thf('18', plain,
% 1.94/2.20      (![X0 : $i, X1 : $i]:
% 1.94/2.20         (((sk_C @ (k4_xboole_0 @ (k1_tarski @ X0) @ X1) @ X0) != (X0))
% 1.94/2.20          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_tarski @ X0))
% 1.94/2.20          | ~ (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 1.94/2.20      inference('simplify', [status(thm)], ['17'])).
% 1.94/2.20  thf('19', plain,
% 1.94/2.20      (![X0 : $i, X1 : $i]:
% 1.94/2.20         ((r2_hidden @ X1 @ X0)
% 1.94/2.20          | ((k4_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_tarski @ X1))
% 1.94/2.20          | ((sk_C @ (k4_xboole_0 @ (k1_tarski @ X1) @ X0) @ X1) != (X1)))),
% 1.94/2.20      inference('sup-', [status(thm)], ['14', '18'])).
% 1.94/2.20  thf('20', plain,
% 1.94/2.20      (![X0 : $i, X1 : $i]:
% 1.94/2.20         (((X0) != (X0))
% 1.94/2.20          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_tarski @ X0))
% 1.94/2.20          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_tarski @ X0))
% 1.94/2.20          | (r2_hidden @ X0 @ X1))),
% 1.94/2.20      inference('sup-', [status(thm)], ['9', '19'])).
% 1.94/2.20  thf('21', plain,
% 1.94/2.20      (![X0 : $i, X1 : $i]:
% 1.94/2.20         ((r2_hidden @ X0 @ X1)
% 1.94/2.20          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_tarski @ X0)))),
% 1.94/2.20      inference('simplify', [status(thm)], ['20'])).
% 1.94/2.20  thf(commutativity_k2_xboole_0, axiom,
% 1.94/2.20    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 1.94/2.20  thf('22', plain,
% 1.94/2.20      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.94/2.20      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.94/2.20  thf('23', plain,
% 1.94/2.20      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.94/2.20      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.94/2.20  thf(t95_xboole_1, axiom,
% 1.94/2.20    (![A:$i,B:$i]:
% 1.94/2.20     ( ( k3_xboole_0 @ A @ B ) =
% 1.94/2.20       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 1.94/2.20  thf('24', plain,
% 1.94/2.20      (![X19 : $i, X20 : $i]:
% 1.94/2.20         ((k3_xboole_0 @ X19 @ X20)
% 1.94/2.20           = (k5_xboole_0 @ (k5_xboole_0 @ X19 @ X20) @ 
% 1.94/2.20              (k2_xboole_0 @ X19 @ X20)))),
% 1.94/2.20      inference('cnf', [status(esa)], [t95_xboole_1])).
% 1.94/2.20  thf(commutativity_k5_xboole_0, axiom,
% 1.94/2.20    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 1.94/2.20  thf('25', plain,
% 1.94/2.20      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 1.94/2.20      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.94/2.20  thf('26', plain,
% 1.94/2.20      (![X19 : $i, X20 : $i]:
% 1.94/2.20         ((k3_xboole_0 @ X19 @ X20)
% 1.94/2.20           = (k5_xboole_0 @ (k2_xboole_0 @ X19 @ X20) @ 
% 1.94/2.20              (k5_xboole_0 @ X19 @ X20)))),
% 1.94/2.20      inference('demod', [status(thm)], ['24', '25'])).
% 1.94/2.20  thf('27', plain,
% 1.94/2.20      (![X0 : $i, X1 : $i]:
% 1.94/2.20         ((k3_xboole_0 @ X0 @ X1)
% 1.94/2.20           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X0 @ X1)))),
% 1.94/2.20      inference('sup+', [status(thm)], ['23', '26'])).
% 1.94/2.20  thf('28', plain,
% 1.94/2.20      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 1.94/2.20      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.94/2.20  thf(t92_xboole_1, axiom,
% 1.94/2.20    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 1.94/2.20  thf('29', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ X18) = (k1_xboole_0))),
% 1.94/2.20      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.94/2.20  thf(t91_xboole_1, axiom,
% 1.94/2.20    (![A:$i,B:$i,C:$i]:
% 1.94/2.20     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 1.94/2.20       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 1.94/2.20  thf('30', plain,
% 1.94/2.20      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.94/2.20         ((k5_xboole_0 @ (k5_xboole_0 @ X15 @ X16) @ X17)
% 1.94/2.20           = (k5_xboole_0 @ X15 @ (k5_xboole_0 @ X16 @ X17)))),
% 1.94/2.20      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.94/2.20  thf('31', plain,
% 1.94/2.20      (![X0 : $i, X1 : $i]:
% 1.94/2.20         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 1.94/2.20           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.94/2.20      inference('sup+', [status(thm)], ['29', '30'])).
% 1.94/2.20  thf(t69_enumset1, axiom,
% 1.94/2.20    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.94/2.20  thf('32', plain,
% 1.94/2.20      (![X26 : $i]: ((k2_tarski @ X26 @ X26) = (k1_tarski @ X26))),
% 1.94/2.20      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.94/2.20  thf(t31_zfmisc_1, axiom,
% 1.94/2.20    (![A:$i]: ( ( k3_tarski @ ( k1_tarski @ A ) ) = ( A ) ))).
% 1.94/2.20  thf('33', plain, (![X56 : $i]: ((k3_tarski @ (k1_tarski @ X56)) = (X56))),
% 1.94/2.20      inference('cnf', [status(esa)], [t31_zfmisc_1])).
% 1.94/2.20  thf('34', plain, (![X0 : $i]: ((k3_tarski @ (k2_tarski @ X0 @ X0)) = (X0))),
% 1.94/2.20      inference('sup+', [status(thm)], ['32', '33'])).
% 1.94/2.20  thf(l51_zfmisc_1, axiom,
% 1.94/2.20    (![A:$i,B:$i]:
% 1.94/2.20     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.94/2.20  thf('35', plain,
% 1.94/2.20      (![X54 : $i, X55 : $i]:
% 1.94/2.20         ((k3_tarski @ (k2_tarski @ X54 @ X55)) = (k2_xboole_0 @ X54 @ X55))),
% 1.94/2.20      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.94/2.20  thf('36', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 1.94/2.20      inference('demod', [status(thm)], ['34', '35'])).
% 1.94/2.20  thf('37', plain,
% 1.94/2.20      (![X19 : $i, X20 : $i]:
% 1.94/2.20         ((k3_xboole_0 @ X19 @ X20)
% 1.94/2.20           = (k5_xboole_0 @ (k2_xboole_0 @ X19 @ X20) @ 
% 1.94/2.20              (k5_xboole_0 @ X19 @ X20)))),
% 1.94/2.20      inference('demod', [status(thm)], ['24', '25'])).
% 1.94/2.20  thf('38', plain,
% 1.94/2.20      (![X0 : $i]:
% 1.94/2.20         ((k3_xboole_0 @ X0 @ X0)
% 1.94/2.20           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 1.94/2.20      inference('sup+', [status(thm)], ['36', '37'])).
% 1.94/2.20  thf(idempotence_k3_xboole_0, axiom,
% 1.94/2.20    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 1.94/2.20  thf('39', plain, (![X10 : $i]: ((k3_xboole_0 @ X10 @ X10) = (X10))),
% 1.94/2.20      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 1.94/2.20  thf('40', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ X18) = (k1_xboole_0))),
% 1.94/2.20      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.94/2.20  thf('41', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.94/2.20      inference('demod', [status(thm)], ['38', '39', '40'])).
% 1.94/2.20  thf('42', plain,
% 1.94/2.20      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 1.94/2.20      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.94/2.20  thf('43', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.94/2.20      inference('sup+', [status(thm)], ['41', '42'])).
% 1.94/2.20  thf('44', plain,
% 1.94/2.20      (![X0 : $i, X1 : $i]:
% 1.94/2.20         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.94/2.20      inference('demod', [status(thm)], ['31', '43'])).
% 1.94/2.20  thf('45', plain,
% 1.94/2.20      (![X0 : $i, X1 : $i]:
% 1.94/2.20         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.94/2.20      inference('sup+', [status(thm)], ['28', '44'])).
% 1.94/2.20  thf('46', plain,
% 1.94/2.20      (![X0 : $i, X1 : $i]:
% 1.94/2.20         ((k2_xboole_0 @ X0 @ X1)
% 1.94/2.20           = (k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 1.94/2.20      inference('sup+', [status(thm)], ['27', '45'])).
% 1.94/2.20  thf('47', plain,
% 1.94/2.20      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 1.94/2.20      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.94/2.20  thf('48', plain,
% 1.94/2.20      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.94/2.20         ((k5_xboole_0 @ (k5_xboole_0 @ X15 @ X16) @ X17)
% 1.94/2.20           = (k5_xboole_0 @ X15 @ (k5_xboole_0 @ X16 @ X17)))),
% 1.94/2.20      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.94/2.20  thf('49', plain,
% 1.94/2.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.94/2.20         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X2)
% 1.94/2.20           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X2)))),
% 1.94/2.20      inference('sup+', [status(thm)], ['47', '48'])).
% 1.94/2.20  thf(t100_xboole_1, axiom,
% 1.94/2.20    (![A:$i,B:$i]:
% 1.94/2.20     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.94/2.20  thf('50', plain,
% 1.94/2.20      (![X11 : $i, X12 : $i]:
% 1.94/2.20         ((k4_xboole_0 @ X11 @ X12)
% 1.94/2.20           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 1.94/2.20      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.94/2.20  thf('51', plain,
% 1.94/2.20      (![X0 : $i, X1 : $i]:
% 1.94/2.20         ((k2_xboole_0 @ X0 @ X1)
% 1.94/2.20           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.94/2.20      inference('demod', [status(thm)], ['46', '49', '50'])).
% 1.94/2.20  thf('52', plain,
% 1.94/2.20      (![X0 : $i, X1 : $i]:
% 1.94/2.20         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.94/2.20      inference('sup+', [status(thm)], ['28', '44'])).
% 1.94/2.20  thf('53', plain,
% 1.94/2.20      (![X0 : $i, X1 : $i]:
% 1.94/2.20         ((X1)
% 1.94/2.20           = (k5_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0)))),
% 1.94/2.20      inference('sup+', [status(thm)], ['51', '52'])).
% 1.94/2.20  thf('54', plain,
% 1.94/2.20      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 1.94/2.20      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.94/2.20  thf('55', plain,
% 1.94/2.20      (![X0 : $i, X1 : $i]:
% 1.94/2.20         ((X1)
% 1.94/2.20           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1)))),
% 1.94/2.20      inference('demod', [status(thm)], ['53', '54'])).
% 1.94/2.20  thf('56', plain,
% 1.94/2.20      (![X0 : $i, X1 : $i]:
% 1.94/2.20         ((X0)
% 1.94/2.20           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0)))),
% 1.94/2.20      inference('sup+', [status(thm)], ['22', '55'])).
% 1.94/2.20  thf('57', plain,
% 1.94/2.20      (![X0 : $i, X1 : $i]:
% 1.94/2.20         (((X1)
% 1.94/2.20            = (k5_xboole_0 @ (k2_xboole_0 @ (k1_tarski @ X0) @ X1) @ 
% 1.94/2.20               (k1_tarski @ X0)))
% 1.94/2.20          | (r2_hidden @ X0 @ X1))),
% 1.94/2.20      inference('sup+', [status(thm)], ['21', '56'])).
% 1.94/2.20  thf(t40_xboole_1, axiom,
% 1.94/2.20    (![A:$i,B:$i]:
% 1.94/2.20     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 1.94/2.20  thf('58', plain,
% 1.94/2.20      (![X13 : $i, X14 : $i]:
% 1.94/2.20         ((k4_xboole_0 @ (k2_xboole_0 @ X13 @ X14) @ X14)
% 1.94/2.20           = (k4_xboole_0 @ X13 @ X14))),
% 1.94/2.20      inference('cnf', [status(esa)], [t40_xboole_1])).
% 1.94/2.20  thf('59', plain,
% 1.94/2.20      (![X0 : $i, X1 : $i]:
% 1.94/2.20         ((k2_xboole_0 @ X0 @ X1)
% 1.94/2.20           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.94/2.20      inference('demod', [status(thm)], ['46', '49', '50'])).
% 1.94/2.20  thf('60', plain,
% 1.94/2.20      (![X0 : $i, X1 : $i]:
% 1.94/2.20         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 1.94/2.20           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.94/2.20      inference('sup+', [status(thm)], ['58', '59'])).
% 1.94/2.20  thf('61', plain,
% 1.94/2.20      (![X0 : $i, X1 : $i]:
% 1.94/2.20         ((k2_xboole_0 @ X0 @ X1)
% 1.94/2.20           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.94/2.20      inference('demod', [status(thm)], ['46', '49', '50'])).
% 1.94/2.20  thf('62', plain,
% 1.94/2.20      (![X0 : $i, X1 : $i]:
% 1.94/2.20         ((k2_xboole_0 @ X0 @ X1)
% 1.94/2.20           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.94/2.20      inference('sup+', [status(thm)], ['60', '61'])).
% 1.94/2.20  thf('63', plain,
% 1.94/2.20      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.94/2.20      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.94/2.20  thf('64', plain,
% 1.94/2.20      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.94/2.20      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.94/2.20  thf('65', plain,
% 1.94/2.20      (![X0 : $i, X1 : $i]:
% 1.94/2.20         ((k2_xboole_0 @ X0 @ X1)
% 1.94/2.20           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.94/2.20      inference('sup+', [status(thm)], ['60', '61'])).
% 1.94/2.20  thf('66', plain,
% 1.94/2.20      (![X0 : $i, X1 : $i]:
% 1.94/2.20         ((k2_xboole_0 @ X1 @ X0)
% 1.94/2.20           = (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.94/2.20      inference('sup+', [status(thm)], ['64', '65'])).
% 1.94/2.20  thf('67', plain,
% 1.94/2.20      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.94/2.20      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.94/2.20  thf('68', plain,
% 1.94/2.20      (![X0 : $i, X1 : $i]:
% 1.94/2.20         ((k2_xboole_0 @ X0 @ X1)
% 1.94/2.20           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.94/2.20      inference('demod', [status(thm)], ['46', '49', '50'])).
% 1.94/2.20  thf('69', plain,
% 1.94/2.20      (![X0 : $i, X1 : $i]:
% 1.94/2.20         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.94/2.20      inference('demod', [status(thm)], ['31', '43'])).
% 1.94/2.20  thf('70', plain,
% 1.94/2.20      (![X0 : $i, X1 : $i]:
% 1.94/2.20         ((k4_xboole_0 @ X0 @ X1)
% 1.94/2.20           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.94/2.20      inference('sup+', [status(thm)], ['68', '69'])).
% 1.94/2.20  thf('71', plain,
% 1.94/2.20      (![X0 : $i, X1 : $i]:
% 1.94/2.20         ((k4_xboole_0 @ X1 @ X0)
% 1.94/2.20           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.94/2.20      inference('sup+', [status(thm)], ['67', '70'])).
% 1.94/2.20  thf('72', plain,
% 1.94/2.20      (![X0 : $i, X1 : $i]:
% 1.94/2.20         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 1.94/2.20           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0)))),
% 1.94/2.20      inference('sup+', [status(thm)], ['66', '71'])).
% 1.94/2.20  thf('73', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ X18) = (k1_xboole_0))),
% 1.94/2.20      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.94/2.20  thf('74', plain,
% 1.94/2.20      (![X0 : $i, X1 : $i]:
% 1.94/2.20         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 1.94/2.20      inference('demod', [status(thm)], ['72', '73'])).
% 1.94/2.20  thf('75', plain,
% 1.94/2.20      (![X0 : $i, X1 : $i]:
% 1.94/2.20         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 1.94/2.20      inference('sup+', [status(thm)], ['63', '74'])).
% 1.94/2.20  thf('76', plain,
% 1.94/2.20      (![X11 : $i, X12 : $i]:
% 1.94/2.20         ((k4_xboole_0 @ X11 @ X12)
% 1.94/2.20           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 1.94/2.20      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.94/2.20  thf('77', plain,
% 1.94/2.20      (![X0 : $i, X1 : $i]:
% 1.94/2.20         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.94/2.20      inference('demod', [status(thm)], ['31', '43'])).
% 1.94/2.20  thf('78', plain,
% 1.94/2.20      (![X0 : $i, X1 : $i]:
% 1.94/2.20         ((k3_xboole_0 @ X1 @ X0)
% 1.94/2.20           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.94/2.20      inference('sup+', [status(thm)], ['76', '77'])).
% 1.94/2.20  thf('79', plain,
% 1.94/2.20      (![X0 : $i, X1 : $i]:
% 1.94/2.20         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 1.94/2.20           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.94/2.20      inference('sup+', [status(thm)], ['75', '78'])).
% 1.94/2.20  thf('80', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.94/2.20      inference('demod', [status(thm)], ['38', '39', '40'])).
% 1.94/2.20  thf('81', plain,
% 1.94/2.20      (![X0 : $i, X1 : $i]:
% 1.94/2.20         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (X0))),
% 1.94/2.20      inference('demod', [status(thm)], ['79', '80'])).
% 1.94/2.20  thf('82', plain,
% 1.94/2.20      (![X0 : $i, X1 : $i]:
% 1.94/2.20         ((k3_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0))
% 1.94/2.20           = (k2_xboole_0 @ X0 @ X1))),
% 1.94/2.20      inference('sup+', [status(thm)], ['62', '81'])).
% 1.94/2.20  thf('83', plain,
% 1.94/2.20      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 1.94/2.20      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.94/2.20  thf('84', plain,
% 1.94/2.20      (![X19 : $i, X20 : $i]:
% 1.94/2.20         ((k3_xboole_0 @ X19 @ X20)
% 1.94/2.20           = (k5_xboole_0 @ (k2_xboole_0 @ X19 @ X20) @ 
% 1.94/2.20              (k5_xboole_0 @ X19 @ X20)))),
% 1.94/2.20      inference('demod', [status(thm)], ['24', '25'])).
% 1.94/2.20  thf('85', plain,
% 1.94/2.20      (![X0 : $i, X1 : $i]:
% 1.94/2.20         ((k3_xboole_0 @ X0 @ X1)
% 1.94/2.20           = (k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k5_xboole_0 @ X1 @ X0)))),
% 1.94/2.20      inference('sup+', [status(thm)], ['83', '84'])).
% 1.94/2.20  thf('86', plain,
% 1.94/2.20      (![X0 : $i, X1 : $i]:
% 1.94/2.20         ((k3_xboole_0 @ X0 @ X1)
% 1.94/2.20           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X0 @ X1)))),
% 1.94/2.20      inference('sup+', [status(thm)], ['23', '26'])).
% 1.94/2.20  thf('87', plain,
% 1.94/2.20      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X0 @ X1) = (k3_xboole_0 @ X1 @ X0))),
% 1.94/2.20      inference('sup+', [status(thm)], ['85', '86'])).
% 1.94/2.20  thf('88', plain,
% 1.94/2.20      (![X11 : $i, X12 : $i]:
% 1.94/2.20         ((k4_xboole_0 @ X11 @ X12)
% 1.94/2.20           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 1.94/2.20      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.94/2.20  thf('89', plain,
% 1.94/2.20      (![X0 : $i, X1 : $i]:
% 1.94/2.20         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.94/2.20      inference('sup+', [status(thm)], ['28', '44'])).
% 1.94/2.20  thf('90', plain,
% 1.94/2.20      (![X0 : $i, X1 : $i]:
% 1.94/2.20         ((X1)
% 1.94/2.20           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0)))),
% 1.94/2.20      inference('sup+', [status(thm)], ['88', '89'])).
% 1.94/2.20  thf('91', plain,
% 1.94/2.20      (![X0 : $i, X1 : $i]:
% 1.94/2.20         ((X0)
% 1.94/2.20           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1)))),
% 1.94/2.20      inference('sup+', [status(thm)], ['87', '90'])).
% 1.94/2.20  thf('92', plain,
% 1.94/2.20      (![X19 : $i, X20 : $i]:
% 1.94/2.20         ((k3_xboole_0 @ X19 @ X20)
% 1.94/2.20           = (k5_xboole_0 @ (k2_xboole_0 @ X19 @ X20) @ 
% 1.94/2.20              (k5_xboole_0 @ X19 @ X20)))),
% 1.94/2.20      inference('demod', [status(thm)], ['24', '25'])).
% 1.94/2.20  thf('93', plain,
% 1.94/2.20      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.94/2.20         ((k5_xboole_0 @ (k5_xboole_0 @ X15 @ X16) @ X17)
% 1.94/2.20           = (k5_xboole_0 @ X15 @ (k5_xboole_0 @ X16 @ X17)))),
% 1.94/2.20      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.94/2.20  thf('94', plain,
% 1.94/2.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.94/2.20         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 1.94/2.20           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 1.94/2.20              (k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X2)))),
% 1.94/2.20      inference('sup+', [status(thm)], ['92', '93'])).
% 1.94/2.20  thf('95', plain,
% 1.94/2.20      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.94/2.20         ((k5_xboole_0 @ (k5_xboole_0 @ X15 @ X16) @ X17)
% 1.94/2.20           = (k5_xboole_0 @ X15 @ (k5_xboole_0 @ X16 @ X17)))),
% 1.94/2.20      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.94/2.20  thf('96', plain,
% 1.94/2.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.94/2.20         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 1.94/2.20           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 1.94/2.20              (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X2))))),
% 1.94/2.20      inference('demod', [status(thm)], ['94', '95'])).
% 1.94/2.20  thf('97', plain,
% 1.94/2.20      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.94/2.20         ((k5_xboole_0 @ (k5_xboole_0 @ X15 @ X16) @ X17)
% 1.94/2.20           = (k5_xboole_0 @ X15 @ (k5_xboole_0 @ X16 @ X17)))),
% 1.94/2.20      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.94/2.20  thf('98', plain,
% 1.94/2.20      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 1.94/2.20      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.94/2.20  thf('99', plain,
% 1.94/2.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.94/2.20         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 1.94/2.20           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.94/2.20      inference('sup+', [status(thm)], ['97', '98'])).
% 1.94/2.20  thf('100', plain,
% 1.94/2.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.94/2.20         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X2)
% 1.94/2.20           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X2)))),
% 1.94/2.20      inference('sup+', [status(thm)], ['47', '48'])).
% 1.94/2.20  thf('101', plain,
% 1.94/2.20      (![X0 : $i, X1 : $i]:
% 1.94/2.20         ((k4_xboole_0 @ X1 @ X0)
% 1.94/2.20           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.94/2.20      inference('sup+', [status(thm)], ['67', '70'])).
% 1.94/2.20  thf('102', plain,
% 1.94/2.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.94/2.20         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 1.94/2.20           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))))),
% 1.94/2.20      inference('demod', [status(thm)], ['96', '99', '100', '101'])).
% 1.94/2.20  thf('103', plain,
% 1.94/2.20      (![X0 : $i, X1 : $i]:
% 1.94/2.20         ((k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X1 @ X0))
% 1.94/2.20           = (k5_xboole_0 @ X0 @ X0))),
% 1.94/2.20      inference('sup+', [status(thm)], ['91', '102'])).
% 1.94/2.20  thf('104', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ X18) = (k1_xboole_0))),
% 1.94/2.20      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.94/2.20  thf('105', plain,
% 1.94/2.20      (![X0 : $i, X1 : $i]:
% 1.94/2.20         ((k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X1 @ X0))
% 1.94/2.20           = (k1_xboole_0))),
% 1.94/2.20      inference('demod', [status(thm)], ['103', '104'])).
% 1.94/2.20  thf('106', plain,
% 1.94/2.20      (![X0 : $i, X1 : $i]:
% 1.94/2.20         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 1.94/2.20           (k3_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0)))
% 1.94/2.20           = (k1_xboole_0))),
% 1.94/2.20      inference('sup+', [status(thm)], ['82', '105'])).
% 1.94/2.20  thf('107', plain,
% 1.94/2.20      (![X0 : $i, X1 : $i]:
% 1.94/2.20         ((k3_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0))
% 1.94/2.20           = (k2_xboole_0 @ X0 @ X1))),
% 1.94/2.20      inference('sup+', [status(thm)], ['62', '81'])).
% 1.94/2.20  thf('108', plain,
% 1.94/2.20      (![X0 : $i, X1 : $i]:
% 1.94/2.20         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X1))
% 1.94/2.20           = (k1_xboole_0))),
% 1.94/2.20      inference('demod', [status(thm)], ['106', '107'])).
% 1.94/2.20  thf('109', plain,
% 1.94/2.20      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.94/2.20         ((k5_xboole_0 @ (k5_xboole_0 @ X15 @ X16) @ X17)
% 1.94/2.20           = (k5_xboole_0 @ X15 @ (k5_xboole_0 @ X16 @ X17)))),
% 1.94/2.20      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.94/2.20  thf('110', plain,
% 1.94/2.20      (![X0 : $i, X1 : $i]:
% 1.94/2.20         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.94/2.20      inference('sup+', [status(thm)], ['28', '44'])).
% 1.94/2.20  thf('111', plain,
% 1.94/2.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.94/2.20         ((k5_xboole_0 @ X2 @ X1)
% 1.94/2.20           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0))))),
% 1.94/2.20      inference('sup+', [status(thm)], ['109', '110'])).
% 1.94/2.20  thf('112', plain,
% 1.94/2.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.94/2.20         ((k5_xboole_0 @ X2 @ (k2_xboole_0 @ X0 @ X1))
% 1.94/2.20           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 1.94/2.20              (k5_xboole_0 @ X2 @ k1_xboole_0)))),
% 1.94/2.20      inference('sup+', [status(thm)], ['108', '111'])).
% 1.94/2.20  thf('113', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.94/2.20      inference('demod', [status(thm)], ['38', '39', '40'])).
% 1.94/2.20  thf('114', plain,
% 1.94/2.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.94/2.20         ((k5_xboole_0 @ X2 @ (k2_xboole_0 @ X0 @ X1))
% 1.94/2.20           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 1.94/2.20      inference('demod', [status(thm)], ['112', '113'])).
% 1.94/2.20  thf('115', plain,
% 1.94/2.20      (![X0 : $i, X1 : $i]:
% 1.94/2.20         ((k4_xboole_0 @ X1 @ X0)
% 1.94/2.20           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.94/2.20      inference('sup+', [status(thm)], ['67', '70'])).
% 1.94/2.20  thf('116', plain,
% 1.94/2.20      (![X0 : $i, X1 : $i]:
% 1.94/2.20         (((X1) = (k4_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 1.94/2.20          | (r2_hidden @ X0 @ X1))),
% 1.94/2.20      inference('demod', [status(thm)], ['57', '114', '115'])).
% 1.94/2.20  thf('117', plain,
% 1.94/2.20      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 1.94/2.20         (k1_tarski @ sk_A)) != (sk_B))),
% 1.94/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.20  thf('118', plain,
% 1.94/2.20      (![X13 : $i, X14 : $i]:
% 1.94/2.20         ((k4_xboole_0 @ (k2_xboole_0 @ X13 @ X14) @ X14)
% 1.94/2.20           = (k4_xboole_0 @ X13 @ X14))),
% 1.94/2.20      inference('cnf', [status(esa)], [t40_xboole_1])).
% 1.94/2.20  thf('119', plain, (((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) != (sk_B))),
% 1.94/2.20      inference('demod', [status(thm)], ['117', '118'])).
% 1.94/2.20  thf('120', plain, ((((sk_B) != (sk_B)) | (r2_hidden @ sk_A @ sk_B))),
% 1.94/2.20      inference('sup-', [status(thm)], ['116', '119'])).
% 1.94/2.20  thf('121', plain, ((r2_hidden @ sk_A @ sk_B)),
% 1.94/2.20      inference('simplify', [status(thm)], ['120'])).
% 1.94/2.20  thf('122', plain, ($false), inference('demod', [status(thm)], ['0', '121'])).
% 1.94/2.20  
% 1.94/2.20  % SZS output end Refutation
% 1.94/2.20  
% 1.94/2.21  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
