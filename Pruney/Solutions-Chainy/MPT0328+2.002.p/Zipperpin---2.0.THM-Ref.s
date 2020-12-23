%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cBFUY9NOMw

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:58 EST 2020

% Result     : Theorem 1.19s
% Output     : Refutation 1.19s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 211 expanded)
%              Number of leaves         :   25 (  77 expanded)
%              Depth                    :   16
%              Number of atoms          :  857 (1858 expanded)
%              Number of equality atoms :   98 ( 221 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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
    ! [X22: $i,X26: $i] :
      ( ( X26
        = ( k1_tarski @ X22 ) )
      | ( ( sk_C @ X26 @ X22 )
        = X22 )
      | ( r2_hidden @ ( sk_C @ X26 @ X22 ) @ X26 ) ) ),
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
    ! [X22: $i,X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X25 @ X24 )
      | ( X25 = X22 )
      | ( X24
       != ( k1_tarski @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('6',plain,(
    ! [X22: $i,X25: $i] :
      ( ( X25 = X22 )
      | ~ ( r2_hidden @ X25 @ ( k1_tarski @ X22 ) ) ) ),
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
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( X23 != X22 )
      | ( r2_hidden @ X23 @ X24 )
      | ( X24
       != ( k1_tarski @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('11',plain,(
    ! [X22: $i] :
      ( r2_hidden @ X22 @ ( k1_tarski @ X22 ) ) ),
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
    ! [X22: $i,X26: $i] :
      ( ( X26
        = ( k1_tarski @ X22 ) )
      | ( ( sk_C @ X26 @ X22 )
       != X22 )
      | ~ ( r2_hidden @ ( sk_C @ X26 @ X22 ) @ X26 ) ) ),
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
    ! [X17: $i] :
      ( ( k5_xboole_0 @ X17 @ X17 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('23',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k5_xboole_0 @ X14 @ ( k5_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('25',plain,(
    ! [X8: $i] :
      ( ( k2_xboole_0 @ X8 @ X8 )
      = X8 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('26',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k3_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X18 @ X19 ) @ ( k2_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('28',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k3_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X18 @ X19 ) @ ( k5_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['25','28'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('30',plain,(
    ! [X9: $i] :
      ( ( k3_xboole_0 @ X9 @ X9 )
      = X9 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('31',plain,(
    ! [X17: $i] :
      ( ( k5_xboole_0 @ X17 @ X17 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['24','34'])).

thf('36',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k3_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X18 @ X19 ) @ ( k5_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('37',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k5_xboole_0 @ X14 @ ( k5_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k5_xboole_0 @ X14 @ ( k5_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X2 ) ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k5_xboole_0 @ X14 @ ( k5_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X0 @ X2 ) @ X1 )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['40','43','46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['35','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('51',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['24','34'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['52','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k5_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['21','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('59',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_tarski @ X21 @ X20 )
      = ( k2_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('60',plain,(
    ! [X55: $i,X56: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X55 @ X56 ) )
      = ( k2_xboole_0 @ X55 @ X56 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X55: $i,X56: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X55 @ X56 ) )
      = ( k2_xboole_0 @ X55 @ X56 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['57','58','65'])).

thf('67',plain,(
    ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('68',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X12 @ X13 ) @ X13 )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('69',plain,(
    ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
 != sk_B ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( sk_B != sk_B )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['66','69'])).

thf('71',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    $false ),
    inference(demod,[status(thm)],['0','71'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cBFUY9NOMw
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:50:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.19/1.41  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.19/1.41  % Solved by: fo/fo7.sh
% 1.19/1.41  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.19/1.41  % done 1691 iterations in 0.953s
% 1.19/1.41  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.19/1.41  % SZS output start Refutation
% 1.19/1.41  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.19/1.41  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.19/1.41  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.19/1.41  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 1.19/1.41  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.19/1.41  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.19/1.41  thf(sk_B_type, type, sk_B: $i).
% 1.19/1.41  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.19/1.41  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.19/1.41  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.19/1.41  thf(sk_A_type, type, sk_A: $i).
% 1.19/1.41  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.19/1.41  thf(t141_zfmisc_1, conjecture,
% 1.19/1.41    (![A:$i,B:$i]:
% 1.19/1.41     ( ( ~( r2_hidden @ A @ B ) ) =>
% 1.19/1.41       ( ( k4_xboole_0 @
% 1.19/1.41           ( k2_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) ) =
% 1.19/1.41         ( B ) ) ))).
% 1.19/1.41  thf(zf_stmt_0, negated_conjecture,
% 1.19/1.41    (~( ![A:$i,B:$i]:
% 1.19/1.41        ( ( ~( r2_hidden @ A @ B ) ) =>
% 1.19/1.41          ( ( k4_xboole_0 @
% 1.19/1.41              ( k2_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) ) =
% 1.19/1.41            ( B ) ) ) )),
% 1.19/1.41    inference('cnf.neg', [status(esa)], [t141_zfmisc_1])).
% 1.19/1.41  thf('0', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 1.19/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.41  thf(d1_tarski, axiom,
% 1.19/1.41    (![A:$i,B:$i]:
% 1.19/1.41     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 1.19/1.41       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 1.19/1.41  thf('1', plain,
% 1.19/1.41      (![X22 : $i, X26 : $i]:
% 1.19/1.41         (((X26) = (k1_tarski @ X22))
% 1.19/1.41          | ((sk_C @ X26 @ X22) = (X22))
% 1.19/1.41          | (r2_hidden @ (sk_C @ X26 @ X22) @ X26))),
% 1.19/1.41      inference('cnf', [status(esa)], [d1_tarski])).
% 1.19/1.41  thf(d5_xboole_0, axiom,
% 1.19/1.41    (![A:$i,B:$i,C:$i]:
% 1.19/1.41     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 1.19/1.41       ( ![D:$i]:
% 1.19/1.41         ( ( r2_hidden @ D @ C ) <=>
% 1.19/1.41           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 1.19/1.41  thf('2', plain,
% 1.19/1.42      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.19/1.42         (~ (r2_hidden @ X6 @ X5)
% 1.19/1.42          | (r2_hidden @ X6 @ X3)
% 1.19/1.42          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 1.19/1.42      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.19/1.42  thf('3', plain,
% 1.19/1.42      (![X3 : $i, X4 : $i, X6 : $i]:
% 1.19/1.42         ((r2_hidden @ X6 @ X3) | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 1.19/1.42      inference('simplify', [status(thm)], ['2'])).
% 1.19/1.42  thf('4', plain,
% 1.19/1.42      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.19/1.42         (((sk_C @ (k4_xboole_0 @ X1 @ X0) @ X2) = (X2))
% 1.19/1.42          | ((k4_xboole_0 @ X1 @ X0) = (k1_tarski @ X2))
% 1.19/1.42          | (r2_hidden @ (sk_C @ (k4_xboole_0 @ X1 @ X0) @ X2) @ X1))),
% 1.19/1.42      inference('sup-', [status(thm)], ['1', '3'])).
% 1.19/1.42  thf('5', plain,
% 1.19/1.42      (![X22 : $i, X24 : $i, X25 : $i]:
% 1.19/1.42         (~ (r2_hidden @ X25 @ X24)
% 1.19/1.42          | ((X25) = (X22))
% 1.19/1.42          | ((X24) != (k1_tarski @ X22)))),
% 1.19/1.42      inference('cnf', [status(esa)], [d1_tarski])).
% 1.19/1.42  thf('6', plain,
% 1.19/1.42      (![X22 : $i, X25 : $i]:
% 1.19/1.42         (((X25) = (X22)) | ~ (r2_hidden @ X25 @ (k1_tarski @ X22)))),
% 1.19/1.42      inference('simplify', [status(thm)], ['5'])).
% 1.19/1.42  thf('7', plain,
% 1.19/1.42      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.19/1.42         (((k4_xboole_0 @ (k1_tarski @ X0) @ X2) = (k1_tarski @ X1))
% 1.19/1.42          | ((sk_C @ (k4_xboole_0 @ (k1_tarski @ X0) @ X2) @ X1) = (X1))
% 1.19/1.42          | ((sk_C @ (k4_xboole_0 @ (k1_tarski @ X0) @ X2) @ X1) = (X0)))),
% 1.19/1.42      inference('sup-', [status(thm)], ['4', '6'])).
% 1.19/1.42  thf('8', plain,
% 1.19/1.42      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.19/1.42         (((X0) != (X2))
% 1.19/1.42          | ((sk_C @ (k4_xboole_0 @ (k1_tarski @ X2) @ X1) @ X0) = (X2))
% 1.19/1.42          | ((k4_xboole_0 @ (k1_tarski @ X2) @ X1) = (k1_tarski @ X0)))),
% 1.19/1.42      inference('eq_fact', [status(thm)], ['7'])).
% 1.19/1.42  thf('9', plain,
% 1.19/1.42      (![X1 : $i, X2 : $i]:
% 1.19/1.42         (((k4_xboole_0 @ (k1_tarski @ X2) @ X1) = (k1_tarski @ X2))
% 1.19/1.42          | ((sk_C @ (k4_xboole_0 @ (k1_tarski @ X2) @ X1) @ X2) = (X2)))),
% 1.19/1.42      inference('simplify', [status(thm)], ['8'])).
% 1.19/1.42  thf('10', plain,
% 1.19/1.42      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.19/1.42         (((X23) != (X22))
% 1.19/1.42          | (r2_hidden @ X23 @ X24)
% 1.19/1.42          | ((X24) != (k1_tarski @ X22)))),
% 1.19/1.42      inference('cnf', [status(esa)], [d1_tarski])).
% 1.19/1.42  thf('11', plain, (![X22 : $i]: (r2_hidden @ X22 @ (k1_tarski @ X22))),
% 1.19/1.42      inference('simplify', [status(thm)], ['10'])).
% 1.19/1.42  thf('12', plain,
% 1.19/1.42      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 1.19/1.42         (~ (r2_hidden @ X2 @ X3)
% 1.19/1.42          | (r2_hidden @ X2 @ X4)
% 1.19/1.42          | (r2_hidden @ X2 @ X5)
% 1.19/1.42          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 1.19/1.42      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.19/1.42  thf('13', plain,
% 1.19/1.42      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.19/1.42         ((r2_hidden @ X2 @ (k4_xboole_0 @ X3 @ X4))
% 1.19/1.42          | (r2_hidden @ X2 @ X4)
% 1.19/1.42          | ~ (r2_hidden @ X2 @ X3))),
% 1.19/1.42      inference('simplify', [status(thm)], ['12'])).
% 1.19/1.42  thf('14', plain,
% 1.19/1.42      (![X0 : $i, X1 : $i]:
% 1.19/1.42         ((r2_hidden @ X0 @ X1)
% 1.19/1.42          | (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 1.19/1.42      inference('sup-', [status(thm)], ['11', '13'])).
% 1.19/1.42  thf('15', plain,
% 1.19/1.42      (![X1 : $i, X2 : $i]:
% 1.19/1.42         (((k4_xboole_0 @ (k1_tarski @ X2) @ X1) = (k1_tarski @ X2))
% 1.19/1.42          | ((sk_C @ (k4_xboole_0 @ (k1_tarski @ X2) @ X1) @ X2) = (X2)))),
% 1.19/1.42      inference('simplify', [status(thm)], ['8'])).
% 1.19/1.42  thf('16', plain,
% 1.19/1.42      (![X22 : $i, X26 : $i]:
% 1.19/1.42         (((X26) = (k1_tarski @ X22))
% 1.19/1.42          | ((sk_C @ X26 @ X22) != (X22))
% 1.19/1.42          | ~ (r2_hidden @ (sk_C @ X26 @ X22) @ X26))),
% 1.19/1.42      inference('cnf', [status(esa)], [d1_tarski])).
% 1.19/1.42  thf('17', plain,
% 1.19/1.42      (![X0 : $i, X1 : $i]:
% 1.19/1.42         (~ (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_tarski @ X0) @ X1))
% 1.19/1.42          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_tarski @ X0))
% 1.19/1.42          | ((sk_C @ (k4_xboole_0 @ (k1_tarski @ X0) @ X1) @ X0) != (X0))
% 1.19/1.42          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_tarski @ X0)))),
% 1.19/1.42      inference('sup-', [status(thm)], ['15', '16'])).
% 1.19/1.42  thf('18', plain,
% 1.19/1.42      (![X0 : $i, X1 : $i]:
% 1.19/1.42         (((sk_C @ (k4_xboole_0 @ (k1_tarski @ X0) @ X1) @ X0) != (X0))
% 1.19/1.42          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_tarski @ X0))
% 1.19/1.42          | ~ (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 1.19/1.42      inference('simplify', [status(thm)], ['17'])).
% 1.19/1.42  thf('19', plain,
% 1.19/1.42      (![X0 : $i, X1 : $i]:
% 1.19/1.42         ((r2_hidden @ X1 @ X0)
% 1.19/1.42          | ((k4_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_tarski @ X1))
% 1.19/1.42          | ((sk_C @ (k4_xboole_0 @ (k1_tarski @ X1) @ X0) @ X1) != (X1)))),
% 1.19/1.42      inference('sup-', [status(thm)], ['14', '18'])).
% 1.19/1.42  thf('20', plain,
% 1.19/1.42      (![X0 : $i, X1 : $i]:
% 1.19/1.42         (((X0) != (X0))
% 1.19/1.42          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_tarski @ X0))
% 1.19/1.42          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_tarski @ X0))
% 1.19/1.42          | (r2_hidden @ X0 @ X1))),
% 1.19/1.42      inference('sup-', [status(thm)], ['9', '19'])).
% 1.19/1.42  thf('21', plain,
% 1.19/1.42      (![X0 : $i, X1 : $i]:
% 1.19/1.42         ((r2_hidden @ X0 @ X1)
% 1.19/1.42          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_tarski @ X0)))),
% 1.19/1.42      inference('simplify', [status(thm)], ['20'])).
% 1.19/1.42  thf(t92_xboole_1, axiom,
% 1.19/1.42    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 1.19/1.42  thf('22', plain, (![X17 : $i]: ((k5_xboole_0 @ X17 @ X17) = (k1_xboole_0))),
% 1.19/1.42      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.19/1.42  thf(t91_xboole_1, axiom,
% 1.19/1.42    (![A:$i,B:$i,C:$i]:
% 1.19/1.42     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 1.19/1.42       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 1.19/1.42  thf('23', plain,
% 1.19/1.42      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.19/1.42         ((k5_xboole_0 @ (k5_xboole_0 @ X14 @ X15) @ X16)
% 1.19/1.42           = (k5_xboole_0 @ X14 @ (k5_xboole_0 @ X15 @ X16)))),
% 1.19/1.42      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.19/1.42  thf('24', plain,
% 1.19/1.42      (![X0 : $i, X1 : $i]:
% 1.19/1.42         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 1.19/1.42           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.19/1.42      inference('sup+', [status(thm)], ['22', '23'])).
% 1.19/1.42  thf(idempotence_k2_xboole_0, axiom,
% 1.19/1.42    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 1.19/1.42  thf('25', plain, (![X8 : $i]: ((k2_xboole_0 @ X8 @ X8) = (X8))),
% 1.19/1.42      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 1.19/1.42  thf(t95_xboole_1, axiom,
% 1.19/1.42    (![A:$i,B:$i]:
% 1.19/1.42     ( ( k3_xboole_0 @ A @ B ) =
% 1.19/1.42       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 1.19/1.42  thf('26', plain,
% 1.19/1.42      (![X18 : $i, X19 : $i]:
% 1.19/1.42         ((k3_xboole_0 @ X18 @ X19)
% 1.19/1.42           = (k5_xboole_0 @ (k5_xboole_0 @ X18 @ X19) @ 
% 1.19/1.42              (k2_xboole_0 @ X18 @ X19)))),
% 1.19/1.42      inference('cnf', [status(esa)], [t95_xboole_1])).
% 1.19/1.42  thf(commutativity_k5_xboole_0, axiom,
% 1.19/1.42    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 1.19/1.42  thf('27', plain,
% 1.19/1.42      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 1.19/1.42      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.19/1.42  thf('28', plain,
% 1.19/1.42      (![X18 : $i, X19 : $i]:
% 1.19/1.42         ((k3_xboole_0 @ X18 @ X19)
% 1.19/1.42           = (k5_xboole_0 @ (k2_xboole_0 @ X18 @ X19) @ 
% 1.19/1.42              (k5_xboole_0 @ X18 @ X19)))),
% 1.19/1.42      inference('demod', [status(thm)], ['26', '27'])).
% 1.19/1.42  thf('29', plain,
% 1.19/1.42      (![X0 : $i]:
% 1.19/1.42         ((k3_xboole_0 @ X0 @ X0)
% 1.19/1.42           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 1.19/1.42      inference('sup+', [status(thm)], ['25', '28'])).
% 1.19/1.42  thf(idempotence_k3_xboole_0, axiom,
% 1.19/1.42    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 1.19/1.42  thf('30', plain, (![X9 : $i]: ((k3_xboole_0 @ X9 @ X9) = (X9))),
% 1.19/1.42      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 1.19/1.42  thf('31', plain, (![X17 : $i]: ((k5_xboole_0 @ X17 @ X17) = (k1_xboole_0))),
% 1.19/1.42      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.19/1.42  thf('32', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.19/1.42      inference('demod', [status(thm)], ['29', '30', '31'])).
% 1.19/1.42  thf('33', plain,
% 1.19/1.42      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 1.19/1.42      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.19/1.42  thf('34', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.19/1.42      inference('sup+', [status(thm)], ['32', '33'])).
% 1.19/1.42  thf('35', plain,
% 1.19/1.42      (![X0 : $i, X1 : $i]:
% 1.19/1.42         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.19/1.42      inference('demod', [status(thm)], ['24', '34'])).
% 1.19/1.42  thf('36', plain,
% 1.19/1.42      (![X18 : $i, X19 : $i]:
% 1.19/1.42         ((k3_xboole_0 @ X18 @ X19)
% 1.19/1.42           = (k5_xboole_0 @ (k2_xboole_0 @ X18 @ X19) @ 
% 1.19/1.42              (k5_xboole_0 @ X18 @ X19)))),
% 1.19/1.42      inference('demod', [status(thm)], ['26', '27'])).
% 1.19/1.42  thf('37', plain,
% 1.19/1.42      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.19/1.42         ((k5_xboole_0 @ (k5_xboole_0 @ X14 @ X15) @ X16)
% 1.19/1.42           = (k5_xboole_0 @ X14 @ (k5_xboole_0 @ X15 @ X16)))),
% 1.19/1.42      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.19/1.42  thf('38', plain,
% 1.19/1.42      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.19/1.42         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 1.19/1.42           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 1.19/1.42              (k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X2)))),
% 1.19/1.42      inference('sup+', [status(thm)], ['36', '37'])).
% 1.19/1.42  thf('39', plain,
% 1.19/1.42      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.19/1.42         ((k5_xboole_0 @ (k5_xboole_0 @ X14 @ X15) @ X16)
% 1.19/1.42           = (k5_xboole_0 @ X14 @ (k5_xboole_0 @ X15 @ X16)))),
% 1.19/1.42      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.19/1.42  thf('40', plain,
% 1.19/1.42      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.19/1.42         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 1.19/1.42           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 1.19/1.42              (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X2))))),
% 1.19/1.42      inference('demod', [status(thm)], ['38', '39'])).
% 1.19/1.42  thf('41', plain,
% 1.19/1.42      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.19/1.42         ((k5_xboole_0 @ (k5_xboole_0 @ X14 @ X15) @ X16)
% 1.19/1.42           = (k5_xboole_0 @ X14 @ (k5_xboole_0 @ X15 @ X16)))),
% 1.19/1.42      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.19/1.42  thf('42', plain,
% 1.19/1.42      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 1.19/1.42      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.19/1.42  thf('43', plain,
% 1.19/1.42      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.19/1.42         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 1.19/1.42           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.19/1.42      inference('sup+', [status(thm)], ['41', '42'])).
% 1.19/1.42  thf('44', plain,
% 1.19/1.42      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.19/1.42         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 1.19/1.42           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.19/1.42      inference('sup+', [status(thm)], ['41', '42'])).
% 1.19/1.42  thf('45', plain,
% 1.19/1.42      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 1.19/1.42      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.19/1.42  thf('46', plain,
% 1.19/1.42      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.19/1.42         ((k5_xboole_0 @ (k5_xboole_0 @ X0 @ X2) @ X1)
% 1.19/1.42           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.19/1.42      inference('sup+', [status(thm)], ['44', '45'])).
% 1.19/1.42  thf('47', plain,
% 1.19/1.42      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 1.19/1.42      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.19/1.42  thf('48', plain,
% 1.19/1.42      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.19/1.42         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 1.19/1.42           = (k5_xboole_0 @ X1 @ 
% 1.19/1.42              (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))))),
% 1.19/1.42      inference('demod', [status(thm)], ['40', '43', '46', '47'])).
% 1.19/1.42  thf('49', plain,
% 1.19/1.42      (![X0 : $i, X1 : $i]:
% 1.19/1.42         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)
% 1.19/1.42           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.19/1.42      inference('sup+', [status(thm)], ['35', '48'])).
% 1.19/1.42  thf('50', plain,
% 1.19/1.42      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 1.19/1.42      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.19/1.42  thf(t100_xboole_1, axiom,
% 1.19/1.42    (![A:$i,B:$i]:
% 1.19/1.42     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.19/1.42  thf('51', plain,
% 1.19/1.42      (![X10 : $i, X11 : $i]:
% 1.19/1.42         ((k4_xboole_0 @ X10 @ X11)
% 1.19/1.42           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 1.19/1.42      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.19/1.42  thf('52', plain,
% 1.19/1.42      (![X0 : $i, X1 : $i]:
% 1.19/1.42         ((k4_xboole_0 @ X1 @ X0)
% 1.19/1.42           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.19/1.42      inference('demod', [status(thm)], ['49', '50', '51'])).
% 1.19/1.42  thf('53', plain,
% 1.19/1.42      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 1.19/1.42      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.19/1.42  thf('54', plain,
% 1.19/1.42      (![X0 : $i, X1 : $i]:
% 1.19/1.42         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.19/1.42      inference('demod', [status(thm)], ['24', '34'])).
% 1.19/1.42  thf('55', plain,
% 1.19/1.42      (![X0 : $i, X1 : $i]:
% 1.19/1.42         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.19/1.42      inference('sup+', [status(thm)], ['53', '54'])).
% 1.19/1.42  thf('56', plain,
% 1.19/1.42      (![X0 : $i, X1 : $i]:
% 1.19/1.42         ((X0)
% 1.19/1.42           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0)))),
% 1.19/1.42      inference('sup+', [status(thm)], ['52', '55'])).
% 1.19/1.42  thf('57', plain,
% 1.19/1.42      (![X0 : $i, X1 : $i]:
% 1.19/1.42         (((X1)
% 1.19/1.42            = (k5_xboole_0 @ (k2_xboole_0 @ (k1_tarski @ X0) @ X1) @ 
% 1.19/1.42               (k1_tarski @ X0)))
% 1.19/1.42          | (r2_hidden @ X0 @ X1))),
% 1.19/1.42      inference('sup+', [status(thm)], ['21', '56'])).
% 1.19/1.42  thf('58', plain,
% 1.19/1.42      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 1.19/1.42      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.19/1.42  thf(commutativity_k2_tarski, axiom,
% 1.19/1.42    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 1.19/1.42  thf('59', plain,
% 1.19/1.42      (![X20 : $i, X21 : $i]:
% 1.19/1.42         ((k2_tarski @ X21 @ X20) = (k2_tarski @ X20 @ X21))),
% 1.19/1.42      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.19/1.42  thf(l51_zfmisc_1, axiom,
% 1.19/1.42    (![A:$i,B:$i]:
% 1.19/1.42     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.19/1.42  thf('60', plain,
% 1.19/1.42      (![X55 : $i, X56 : $i]:
% 1.19/1.42         ((k3_tarski @ (k2_tarski @ X55 @ X56)) = (k2_xboole_0 @ X55 @ X56))),
% 1.19/1.42      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.19/1.42  thf('61', plain,
% 1.19/1.42      (![X0 : $i, X1 : $i]:
% 1.19/1.42         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 1.19/1.42      inference('sup+', [status(thm)], ['59', '60'])).
% 1.19/1.42  thf('62', plain,
% 1.19/1.42      (![X55 : $i, X56 : $i]:
% 1.19/1.42         ((k3_tarski @ (k2_tarski @ X55 @ X56)) = (k2_xboole_0 @ X55 @ X56))),
% 1.19/1.42      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.19/1.42  thf('63', plain,
% 1.19/1.42      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.19/1.42      inference('sup+', [status(thm)], ['61', '62'])).
% 1.19/1.42  thf('64', plain,
% 1.19/1.42      (![X0 : $i, X1 : $i]:
% 1.19/1.42         ((k4_xboole_0 @ X1 @ X0)
% 1.19/1.42           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.19/1.42      inference('demod', [status(thm)], ['49', '50', '51'])).
% 1.19/1.42  thf('65', plain,
% 1.19/1.42      (![X0 : $i, X1 : $i]:
% 1.19/1.42         ((k4_xboole_0 @ X0 @ X1)
% 1.19/1.42           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.19/1.42      inference('sup+', [status(thm)], ['63', '64'])).
% 1.19/1.42  thf('66', plain,
% 1.19/1.42      (![X0 : $i, X1 : $i]:
% 1.19/1.42         (((X1) = (k4_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 1.19/1.42          | (r2_hidden @ X0 @ X1))),
% 1.19/1.42      inference('demod', [status(thm)], ['57', '58', '65'])).
% 1.19/1.42  thf('67', plain,
% 1.19/1.42      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 1.19/1.42         (k1_tarski @ sk_A)) != (sk_B))),
% 1.19/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.42  thf(t40_xboole_1, axiom,
% 1.19/1.42    (![A:$i,B:$i]:
% 1.19/1.42     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 1.19/1.42  thf('68', plain,
% 1.19/1.42      (![X12 : $i, X13 : $i]:
% 1.19/1.42         ((k4_xboole_0 @ (k2_xboole_0 @ X12 @ X13) @ X13)
% 1.19/1.42           = (k4_xboole_0 @ X12 @ X13))),
% 1.19/1.42      inference('cnf', [status(esa)], [t40_xboole_1])).
% 1.19/1.42  thf('69', plain, (((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) != (sk_B))),
% 1.19/1.42      inference('demod', [status(thm)], ['67', '68'])).
% 1.19/1.42  thf('70', plain, ((((sk_B) != (sk_B)) | (r2_hidden @ sk_A @ sk_B))),
% 1.19/1.42      inference('sup-', [status(thm)], ['66', '69'])).
% 1.19/1.42  thf('71', plain, ((r2_hidden @ sk_A @ sk_B)),
% 1.19/1.42      inference('simplify', [status(thm)], ['70'])).
% 1.19/1.42  thf('72', plain, ($false), inference('demod', [status(thm)], ['0', '71'])).
% 1.19/1.42  
% 1.19/1.42  % SZS output end Refutation
% 1.19/1.42  
% 1.19/1.42  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
