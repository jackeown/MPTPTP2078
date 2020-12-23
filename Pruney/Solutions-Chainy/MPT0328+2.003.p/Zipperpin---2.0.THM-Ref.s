%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.msrvxg5jRZ

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:58 EST 2020

% Result     : Theorem 1.21s
% Output     : Refutation 1.21s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 229 expanded)
%              Number of leaves         :   26 (  83 expanded)
%              Depth                    :   16
%              Number of atoms          :  888 (1975 expanded)
%              Number of equality atoms :  103 ( 239 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X3 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('3',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
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
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ( r2_hidden @ X2 @ X5 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('13',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X2 @ ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
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

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('22',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ X16 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('23',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('25',plain,(
    ! [X26: $i] :
      ( ( k2_tarski @ X26 @ X26 )
      = ( k1_tarski @ X26 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t31_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_tarski @ A ) )
      = A ) )).

thf('26',plain,(
    ! [X56: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X56 ) )
      = X56 ) ),
    inference(cnf,[status(esa)],[t31_zfmisc_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('28',plain,(
    ! [X54: $i,X55: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X54 @ X55 ) )
      = ( k2_xboole_0 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('30',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X17 @ X18 ) @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('32',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X17 @ X18 ) @ ( k5_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['29','32'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('34',plain,(
    ! [X8: $i] :
      ( ( k3_xboole_0 @ X8 @ X8 )
      = X8 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('35',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ X16 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['24','38'])).

thf('40',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X17 @ X18 ) @ ( k5_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('41',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X2 ) ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X0 @ X2 ) @ X1 )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['44','47','50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['39','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('55',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['24','38'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['56','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k5_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['21','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('63',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_tarski @ X20 @ X19 )
      = ( k2_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('64',plain,(
    ! [X54: $i,X55: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X54 @ X55 ) )
      = ( k2_xboole_0 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X54: $i,X55: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X54 @ X55 ) )
      = ( k2_xboole_0 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['61','62','69'])).

thf('71',plain,(
    ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('72',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X11 @ X12 ) @ X12 )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('73',plain,(
    ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
 != sk_B ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,
    ( ( sk_B != sk_B )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['70','73'])).

thf('75',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    $false ),
    inference(demod,[status(thm)],['0','75'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.msrvxg5jRZ
% 0.14/0.33  % Computer   : n022.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 19:37:26 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.33  % Running portfolio for 600 s
% 0.14/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 1.21/1.43  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.21/1.43  % Solved by: fo/fo7.sh
% 1.21/1.43  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.21/1.43  % done 1805 iterations in 0.991s
% 1.21/1.43  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.21/1.43  % SZS output start Refutation
% 1.21/1.43  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.21/1.43  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.21/1.43  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.21/1.43  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.21/1.43  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.21/1.43  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.21/1.43  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 1.21/1.43  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.21/1.43  thf(sk_A_type, type, sk_A: $i).
% 1.21/1.43  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.21/1.43  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.21/1.43  thf(sk_B_type, type, sk_B: $i).
% 1.21/1.43  thf(t141_zfmisc_1, conjecture,
% 1.21/1.43    (![A:$i,B:$i]:
% 1.21/1.43     ( ( ~( r2_hidden @ A @ B ) ) =>
% 1.21/1.43       ( ( k4_xboole_0 @
% 1.21/1.43           ( k2_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) ) =
% 1.21/1.43         ( B ) ) ))).
% 1.21/1.43  thf(zf_stmt_0, negated_conjecture,
% 1.21/1.43    (~( ![A:$i,B:$i]:
% 1.21/1.43        ( ( ~( r2_hidden @ A @ B ) ) =>
% 1.21/1.43          ( ( k4_xboole_0 @
% 1.21/1.43              ( k2_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) ) =
% 1.21/1.43            ( B ) ) ) )),
% 1.21/1.43    inference('cnf.neg', [status(esa)], [t141_zfmisc_1])).
% 1.21/1.43  thf('0', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 1.21/1.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.43  thf(d1_tarski, axiom,
% 1.21/1.43    (![A:$i,B:$i]:
% 1.21/1.43     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 1.21/1.43       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 1.21/1.43  thf('1', plain,
% 1.21/1.43      (![X21 : $i, X25 : $i]:
% 1.21/1.43         (((X25) = (k1_tarski @ X21))
% 1.21/1.43          | ((sk_C @ X25 @ X21) = (X21))
% 1.21/1.43          | (r2_hidden @ (sk_C @ X25 @ X21) @ X25))),
% 1.21/1.43      inference('cnf', [status(esa)], [d1_tarski])).
% 1.21/1.43  thf(d5_xboole_0, axiom,
% 1.21/1.43    (![A:$i,B:$i,C:$i]:
% 1.21/1.43     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 1.21/1.43       ( ![D:$i]:
% 1.21/1.43         ( ( r2_hidden @ D @ C ) <=>
% 1.21/1.43           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 1.21/1.43  thf('2', plain,
% 1.21/1.43      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.21/1.43         (~ (r2_hidden @ X6 @ X5)
% 1.21/1.43          | (r2_hidden @ X6 @ X3)
% 1.21/1.43          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 1.21/1.43      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.21/1.43  thf('3', plain,
% 1.21/1.43      (![X3 : $i, X4 : $i, X6 : $i]:
% 1.21/1.43         ((r2_hidden @ X6 @ X3) | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 1.21/1.43      inference('simplify', [status(thm)], ['2'])).
% 1.21/1.43  thf('4', plain,
% 1.21/1.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.21/1.43         (((sk_C @ (k4_xboole_0 @ X1 @ X0) @ X2) = (X2))
% 1.21/1.43          | ((k4_xboole_0 @ X1 @ X0) = (k1_tarski @ X2))
% 1.21/1.43          | (r2_hidden @ (sk_C @ (k4_xboole_0 @ X1 @ X0) @ X2) @ X1))),
% 1.21/1.43      inference('sup-', [status(thm)], ['1', '3'])).
% 1.21/1.43  thf('5', plain,
% 1.21/1.43      (![X21 : $i, X23 : $i, X24 : $i]:
% 1.21/1.43         (~ (r2_hidden @ X24 @ X23)
% 1.21/1.43          | ((X24) = (X21))
% 1.21/1.43          | ((X23) != (k1_tarski @ X21)))),
% 1.21/1.43      inference('cnf', [status(esa)], [d1_tarski])).
% 1.21/1.43  thf('6', plain,
% 1.21/1.43      (![X21 : $i, X24 : $i]:
% 1.21/1.43         (((X24) = (X21)) | ~ (r2_hidden @ X24 @ (k1_tarski @ X21)))),
% 1.21/1.43      inference('simplify', [status(thm)], ['5'])).
% 1.21/1.43  thf('7', plain,
% 1.21/1.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.21/1.43         (((k4_xboole_0 @ (k1_tarski @ X0) @ X2) = (k1_tarski @ X1))
% 1.21/1.43          | ((sk_C @ (k4_xboole_0 @ (k1_tarski @ X0) @ X2) @ X1) = (X1))
% 1.21/1.43          | ((sk_C @ (k4_xboole_0 @ (k1_tarski @ X0) @ X2) @ X1) = (X0)))),
% 1.21/1.43      inference('sup-', [status(thm)], ['4', '6'])).
% 1.21/1.43  thf('8', plain,
% 1.21/1.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.21/1.43         (((X0) != (X2))
% 1.21/1.43          | ((sk_C @ (k4_xboole_0 @ (k1_tarski @ X2) @ X1) @ X0) = (X2))
% 1.21/1.43          | ((k4_xboole_0 @ (k1_tarski @ X2) @ X1) = (k1_tarski @ X0)))),
% 1.21/1.43      inference('eq_fact', [status(thm)], ['7'])).
% 1.21/1.43  thf('9', plain,
% 1.21/1.43      (![X1 : $i, X2 : $i]:
% 1.21/1.43         (((k4_xboole_0 @ (k1_tarski @ X2) @ X1) = (k1_tarski @ X2))
% 1.21/1.43          | ((sk_C @ (k4_xboole_0 @ (k1_tarski @ X2) @ X1) @ X2) = (X2)))),
% 1.21/1.43      inference('simplify', [status(thm)], ['8'])).
% 1.21/1.43  thf('10', plain,
% 1.21/1.43      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.21/1.43         (((X22) != (X21))
% 1.21/1.43          | (r2_hidden @ X22 @ X23)
% 1.21/1.43          | ((X23) != (k1_tarski @ X21)))),
% 1.21/1.43      inference('cnf', [status(esa)], [d1_tarski])).
% 1.21/1.43  thf('11', plain, (![X21 : $i]: (r2_hidden @ X21 @ (k1_tarski @ X21))),
% 1.21/1.43      inference('simplify', [status(thm)], ['10'])).
% 1.21/1.43  thf('12', plain,
% 1.21/1.43      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 1.21/1.43         (~ (r2_hidden @ X2 @ X3)
% 1.21/1.43          | (r2_hidden @ X2 @ X4)
% 1.21/1.43          | (r2_hidden @ X2 @ X5)
% 1.21/1.43          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 1.21/1.43      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.21/1.43  thf('13', plain,
% 1.21/1.43      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.21/1.43         ((r2_hidden @ X2 @ (k4_xboole_0 @ X3 @ X4))
% 1.21/1.43          | (r2_hidden @ X2 @ X4)
% 1.21/1.43          | ~ (r2_hidden @ X2 @ X3))),
% 1.21/1.43      inference('simplify', [status(thm)], ['12'])).
% 1.21/1.43  thf('14', plain,
% 1.21/1.43      (![X0 : $i, X1 : $i]:
% 1.21/1.43         ((r2_hidden @ X0 @ X1)
% 1.21/1.43          | (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 1.21/1.43      inference('sup-', [status(thm)], ['11', '13'])).
% 1.21/1.43  thf('15', plain,
% 1.21/1.43      (![X1 : $i, X2 : $i]:
% 1.21/1.43         (((k4_xboole_0 @ (k1_tarski @ X2) @ X1) = (k1_tarski @ X2))
% 1.21/1.43          | ((sk_C @ (k4_xboole_0 @ (k1_tarski @ X2) @ X1) @ X2) = (X2)))),
% 1.21/1.43      inference('simplify', [status(thm)], ['8'])).
% 1.21/1.43  thf('16', plain,
% 1.21/1.43      (![X21 : $i, X25 : $i]:
% 1.21/1.43         (((X25) = (k1_tarski @ X21))
% 1.21/1.43          | ((sk_C @ X25 @ X21) != (X21))
% 1.21/1.43          | ~ (r2_hidden @ (sk_C @ X25 @ X21) @ X25))),
% 1.21/1.43      inference('cnf', [status(esa)], [d1_tarski])).
% 1.21/1.43  thf('17', plain,
% 1.21/1.43      (![X0 : $i, X1 : $i]:
% 1.21/1.43         (~ (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_tarski @ X0) @ X1))
% 1.21/1.43          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_tarski @ X0))
% 1.21/1.43          | ((sk_C @ (k4_xboole_0 @ (k1_tarski @ X0) @ X1) @ X0) != (X0))
% 1.21/1.43          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_tarski @ X0)))),
% 1.21/1.43      inference('sup-', [status(thm)], ['15', '16'])).
% 1.21/1.43  thf('18', plain,
% 1.21/1.43      (![X0 : $i, X1 : $i]:
% 1.21/1.43         (((sk_C @ (k4_xboole_0 @ (k1_tarski @ X0) @ X1) @ X0) != (X0))
% 1.21/1.43          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_tarski @ X0))
% 1.21/1.43          | ~ (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 1.21/1.43      inference('simplify', [status(thm)], ['17'])).
% 1.21/1.43  thf('19', plain,
% 1.21/1.43      (![X0 : $i, X1 : $i]:
% 1.21/1.43         ((r2_hidden @ X1 @ X0)
% 1.21/1.43          | ((k4_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_tarski @ X1))
% 1.21/1.43          | ((sk_C @ (k4_xboole_0 @ (k1_tarski @ X1) @ X0) @ X1) != (X1)))),
% 1.21/1.43      inference('sup-', [status(thm)], ['14', '18'])).
% 1.21/1.43  thf('20', plain,
% 1.21/1.43      (![X0 : $i, X1 : $i]:
% 1.21/1.43         (((X0) != (X0))
% 1.21/1.43          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_tarski @ X0))
% 1.21/1.43          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_tarski @ X0))
% 1.21/1.43          | (r2_hidden @ X0 @ X1))),
% 1.21/1.43      inference('sup-', [status(thm)], ['9', '19'])).
% 1.21/1.43  thf('21', plain,
% 1.21/1.43      (![X0 : $i, X1 : $i]:
% 1.21/1.43         ((r2_hidden @ X0 @ X1)
% 1.21/1.43          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_tarski @ X0)))),
% 1.21/1.43      inference('simplify', [status(thm)], ['20'])).
% 1.21/1.43  thf(t92_xboole_1, axiom,
% 1.21/1.43    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 1.21/1.43  thf('22', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ X16) = (k1_xboole_0))),
% 1.21/1.43      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.21/1.43  thf(t91_xboole_1, axiom,
% 1.21/1.43    (![A:$i,B:$i,C:$i]:
% 1.21/1.43     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 1.21/1.43       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 1.21/1.43  thf('23', plain,
% 1.21/1.43      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.21/1.43         ((k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15)
% 1.21/1.43           = (k5_xboole_0 @ X13 @ (k5_xboole_0 @ X14 @ X15)))),
% 1.21/1.43      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.21/1.43  thf('24', plain,
% 1.21/1.43      (![X0 : $i, X1 : $i]:
% 1.21/1.43         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 1.21/1.43           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.21/1.43      inference('sup+', [status(thm)], ['22', '23'])).
% 1.21/1.43  thf(t69_enumset1, axiom,
% 1.21/1.43    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.21/1.43  thf('25', plain,
% 1.21/1.43      (![X26 : $i]: ((k2_tarski @ X26 @ X26) = (k1_tarski @ X26))),
% 1.21/1.43      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.21/1.43  thf(t31_zfmisc_1, axiom,
% 1.21/1.43    (![A:$i]: ( ( k3_tarski @ ( k1_tarski @ A ) ) = ( A ) ))).
% 1.21/1.43  thf('26', plain, (![X56 : $i]: ((k3_tarski @ (k1_tarski @ X56)) = (X56))),
% 1.21/1.43      inference('cnf', [status(esa)], [t31_zfmisc_1])).
% 1.21/1.43  thf('27', plain, (![X0 : $i]: ((k3_tarski @ (k2_tarski @ X0 @ X0)) = (X0))),
% 1.21/1.43      inference('sup+', [status(thm)], ['25', '26'])).
% 1.21/1.43  thf(l51_zfmisc_1, axiom,
% 1.21/1.43    (![A:$i,B:$i]:
% 1.21/1.43     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.21/1.43  thf('28', plain,
% 1.21/1.43      (![X54 : $i, X55 : $i]:
% 1.21/1.43         ((k3_tarski @ (k2_tarski @ X54 @ X55)) = (k2_xboole_0 @ X54 @ X55))),
% 1.21/1.43      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.21/1.43  thf('29', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 1.21/1.43      inference('demod', [status(thm)], ['27', '28'])).
% 1.21/1.43  thf(t95_xboole_1, axiom,
% 1.21/1.43    (![A:$i,B:$i]:
% 1.21/1.43     ( ( k3_xboole_0 @ A @ B ) =
% 1.21/1.43       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 1.21/1.43  thf('30', plain,
% 1.21/1.43      (![X17 : $i, X18 : $i]:
% 1.21/1.43         ((k3_xboole_0 @ X17 @ X18)
% 1.21/1.43           = (k5_xboole_0 @ (k5_xboole_0 @ X17 @ X18) @ 
% 1.21/1.43              (k2_xboole_0 @ X17 @ X18)))),
% 1.21/1.43      inference('cnf', [status(esa)], [t95_xboole_1])).
% 1.21/1.43  thf(commutativity_k5_xboole_0, axiom,
% 1.21/1.43    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 1.21/1.43  thf('31', plain,
% 1.21/1.43      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 1.21/1.43      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.21/1.43  thf('32', plain,
% 1.21/1.43      (![X17 : $i, X18 : $i]:
% 1.21/1.43         ((k3_xboole_0 @ X17 @ X18)
% 1.21/1.43           = (k5_xboole_0 @ (k2_xboole_0 @ X17 @ X18) @ 
% 1.21/1.43              (k5_xboole_0 @ X17 @ X18)))),
% 1.21/1.43      inference('demod', [status(thm)], ['30', '31'])).
% 1.21/1.43  thf('33', plain,
% 1.21/1.43      (![X0 : $i]:
% 1.21/1.43         ((k3_xboole_0 @ X0 @ X0)
% 1.21/1.43           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 1.21/1.43      inference('sup+', [status(thm)], ['29', '32'])).
% 1.21/1.43  thf(idempotence_k3_xboole_0, axiom,
% 1.21/1.43    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 1.21/1.43  thf('34', plain, (![X8 : $i]: ((k3_xboole_0 @ X8 @ X8) = (X8))),
% 1.21/1.43      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 1.21/1.43  thf('35', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ X16) = (k1_xboole_0))),
% 1.21/1.43      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.21/1.43  thf('36', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.21/1.43      inference('demod', [status(thm)], ['33', '34', '35'])).
% 1.21/1.43  thf('37', plain,
% 1.21/1.43      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 1.21/1.43      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.21/1.43  thf('38', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.21/1.43      inference('sup+', [status(thm)], ['36', '37'])).
% 1.21/1.43  thf('39', plain,
% 1.21/1.43      (![X0 : $i, X1 : $i]:
% 1.21/1.43         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.21/1.43      inference('demod', [status(thm)], ['24', '38'])).
% 1.21/1.43  thf('40', plain,
% 1.21/1.43      (![X17 : $i, X18 : $i]:
% 1.21/1.43         ((k3_xboole_0 @ X17 @ X18)
% 1.21/1.43           = (k5_xboole_0 @ (k2_xboole_0 @ X17 @ X18) @ 
% 1.21/1.43              (k5_xboole_0 @ X17 @ X18)))),
% 1.21/1.43      inference('demod', [status(thm)], ['30', '31'])).
% 1.21/1.43  thf('41', plain,
% 1.21/1.43      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.21/1.43         ((k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15)
% 1.21/1.43           = (k5_xboole_0 @ X13 @ (k5_xboole_0 @ X14 @ X15)))),
% 1.21/1.43      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.21/1.43  thf('42', plain,
% 1.21/1.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.21/1.43         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 1.21/1.43           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 1.21/1.43              (k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X2)))),
% 1.21/1.43      inference('sup+', [status(thm)], ['40', '41'])).
% 1.21/1.43  thf('43', plain,
% 1.21/1.43      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.21/1.43         ((k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15)
% 1.21/1.43           = (k5_xboole_0 @ X13 @ (k5_xboole_0 @ X14 @ X15)))),
% 1.21/1.43      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.21/1.43  thf('44', plain,
% 1.21/1.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.21/1.43         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 1.21/1.43           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 1.21/1.43              (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X2))))),
% 1.21/1.43      inference('demod', [status(thm)], ['42', '43'])).
% 1.21/1.43  thf('45', plain,
% 1.21/1.43      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.21/1.43         ((k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15)
% 1.21/1.43           = (k5_xboole_0 @ X13 @ (k5_xboole_0 @ X14 @ X15)))),
% 1.21/1.43      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.21/1.43  thf('46', plain,
% 1.21/1.43      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 1.21/1.43      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.21/1.43  thf('47', plain,
% 1.21/1.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.21/1.43         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 1.21/1.43           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.21/1.43      inference('sup+', [status(thm)], ['45', '46'])).
% 1.21/1.43  thf('48', plain,
% 1.21/1.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.21/1.43         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 1.21/1.43           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.21/1.43      inference('sup+', [status(thm)], ['45', '46'])).
% 1.21/1.43  thf('49', plain,
% 1.21/1.43      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 1.21/1.43      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.21/1.43  thf('50', plain,
% 1.21/1.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.21/1.43         ((k5_xboole_0 @ (k5_xboole_0 @ X0 @ X2) @ X1)
% 1.21/1.43           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.21/1.43      inference('sup+', [status(thm)], ['48', '49'])).
% 1.21/1.43  thf('51', plain,
% 1.21/1.43      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 1.21/1.43      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.21/1.43  thf('52', plain,
% 1.21/1.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.21/1.43         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 1.21/1.43           = (k5_xboole_0 @ X1 @ 
% 1.21/1.43              (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))))),
% 1.21/1.43      inference('demod', [status(thm)], ['44', '47', '50', '51'])).
% 1.21/1.43  thf('53', plain,
% 1.21/1.43      (![X0 : $i, X1 : $i]:
% 1.21/1.43         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)
% 1.21/1.43           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.21/1.43      inference('sup+', [status(thm)], ['39', '52'])).
% 1.21/1.43  thf('54', plain,
% 1.21/1.43      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 1.21/1.43      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.21/1.43  thf(t100_xboole_1, axiom,
% 1.21/1.43    (![A:$i,B:$i]:
% 1.21/1.43     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.21/1.43  thf('55', plain,
% 1.21/1.43      (![X9 : $i, X10 : $i]:
% 1.21/1.43         ((k4_xboole_0 @ X9 @ X10)
% 1.21/1.43           = (k5_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)))),
% 1.21/1.43      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.21/1.43  thf('56', plain,
% 1.21/1.43      (![X0 : $i, X1 : $i]:
% 1.21/1.43         ((k4_xboole_0 @ X1 @ X0)
% 1.21/1.43           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.21/1.43      inference('demod', [status(thm)], ['53', '54', '55'])).
% 1.21/1.43  thf('57', plain,
% 1.21/1.43      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 1.21/1.43      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.21/1.43  thf('58', plain,
% 1.21/1.43      (![X0 : $i, X1 : $i]:
% 1.21/1.43         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.21/1.43      inference('demod', [status(thm)], ['24', '38'])).
% 1.21/1.43  thf('59', plain,
% 1.21/1.43      (![X0 : $i, X1 : $i]:
% 1.21/1.43         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.21/1.43      inference('sup+', [status(thm)], ['57', '58'])).
% 1.21/1.43  thf('60', plain,
% 1.21/1.43      (![X0 : $i, X1 : $i]:
% 1.21/1.43         ((X0)
% 1.21/1.43           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0)))),
% 1.21/1.43      inference('sup+', [status(thm)], ['56', '59'])).
% 1.21/1.43  thf('61', plain,
% 1.21/1.43      (![X0 : $i, X1 : $i]:
% 1.21/1.43         (((X1)
% 1.21/1.43            = (k5_xboole_0 @ (k2_xboole_0 @ (k1_tarski @ X0) @ X1) @ 
% 1.21/1.43               (k1_tarski @ X0)))
% 1.21/1.43          | (r2_hidden @ X0 @ X1))),
% 1.21/1.43      inference('sup+', [status(thm)], ['21', '60'])).
% 1.21/1.43  thf('62', plain,
% 1.21/1.43      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 1.21/1.43      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.21/1.43  thf(commutativity_k2_tarski, axiom,
% 1.21/1.43    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 1.21/1.43  thf('63', plain,
% 1.21/1.43      (![X19 : $i, X20 : $i]:
% 1.21/1.43         ((k2_tarski @ X20 @ X19) = (k2_tarski @ X19 @ X20))),
% 1.21/1.43      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.21/1.43  thf('64', plain,
% 1.21/1.43      (![X54 : $i, X55 : $i]:
% 1.21/1.43         ((k3_tarski @ (k2_tarski @ X54 @ X55)) = (k2_xboole_0 @ X54 @ X55))),
% 1.21/1.43      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.21/1.43  thf('65', plain,
% 1.21/1.43      (![X0 : $i, X1 : $i]:
% 1.21/1.43         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 1.21/1.43      inference('sup+', [status(thm)], ['63', '64'])).
% 1.21/1.43  thf('66', plain,
% 1.21/1.43      (![X54 : $i, X55 : $i]:
% 1.21/1.43         ((k3_tarski @ (k2_tarski @ X54 @ X55)) = (k2_xboole_0 @ X54 @ X55))),
% 1.21/1.43      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.21/1.43  thf('67', plain,
% 1.21/1.43      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.21/1.43      inference('sup+', [status(thm)], ['65', '66'])).
% 1.21/1.43  thf('68', plain,
% 1.21/1.43      (![X0 : $i, X1 : $i]:
% 1.21/1.43         ((k4_xboole_0 @ X1 @ X0)
% 1.21/1.43           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.21/1.43      inference('demod', [status(thm)], ['53', '54', '55'])).
% 1.21/1.43  thf('69', plain,
% 1.21/1.43      (![X0 : $i, X1 : $i]:
% 1.21/1.43         ((k4_xboole_0 @ X0 @ X1)
% 1.21/1.43           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.21/1.43      inference('sup+', [status(thm)], ['67', '68'])).
% 1.21/1.43  thf('70', plain,
% 1.21/1.43      (![X0 : $i, X1 : $i]:
% 1.21/1.43         (((X1) = (k4_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 1.21/1.43          | (r2_hidden @ X0 @ X1))),
% 1.21/1.43      inference('demod', [status(thm)], ['61', '62', '69'])).
% 1.21/1.43  thf('71', plain,
% 1.21/1.43      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 1.21/1.43         (k1_tarski @ sk_A)) != (sk_B))),
% 1.21/1.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.43  thf(t40_xboole_1, axiom,
% 1.21/1.43    (![A:$i,B:$i]:
% 1.21/1.43     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 1.21/1.43  thf('72', plain,
% 1.21/1.43      (![X11 : $i, X12 : $i]:
% 1.21/1.43         ((k4_xboole_0 @ (k2_xboole_0 @ X11 @ X12) @ X12)
% 1.21/1.43           = (k4_xboole_0 @ X11 @ X12))),
% 1.21/1.43      inference('cnf', [status(esa)], [t40_xboole_1])).
% 1.21/1.43  thf('73', plain, (((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) != (sk_B))),
% 1.21/1.43      inference('demod', [status(thm)], ['71', '72'])).
% 1.21/1.43  thf('74', plain, ((((sk_B) != (sk_B)) | (r2_hidden @ sk_A @ sk_B))),
% 1.21/1.43      inference('sup-', [status(thm)], ['70', '73'])).
% 1.21/1.43  thf('75', plain, ((r2_hidden @ sk_A @ sk_B)),
% 1.21/1.43      inference('simplify', [status(thm)], ['74'])).
% 1.21/1.43  thf('76', plain, ($false), inference('demod', [status(thm)], ['0', '75'])).
% 1.21/1.43  
% 1.21/1.43  % SZS output end Refutation
% 1.21/1.43  
% 1.21/1.43  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
