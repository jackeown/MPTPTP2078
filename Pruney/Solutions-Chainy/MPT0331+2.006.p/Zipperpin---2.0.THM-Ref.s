%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.EKW2DXlJdz

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:04 EST 2020

% Result     : Theorem 7.56s
% Output     : Refutation 7.56s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 286 expanded)
%              Number of leaves         :   24 (  95 expanded)
%              Depth                    :   24
%              Number of atoms          :  805 (2249 expanded)
%              Number of equality atoms :   92 ( 252 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t144_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r2_hidden @ A @ C )
        & ~ ( r2_hidden @ B @ C )
        & ( C
         != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ~ ( r2_hidden @ A @ C )
          & ~ ( r2_hidden @ B @ C )
          & ( C
           != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t144_zfmisc_1])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k1_enumset1 @ X27 @ X27 @ X28 )
      = ( k2_tarski @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t72_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = ( k2_tarski @ A @ B ) )
    <=> ( ~ ( r2_hidden @ A @ C )
        & ~ ( r2_hidden @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X32: $i,X34: $i,X35: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X32 @ X34 ) @ X35 )
        = ( k2_tarski @ X32 @ X34 ) )
      | ( r2_hidden @ X34 @ X35 )
      | ( r2_hidden @ X32 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t72_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) @ X2 )
        = ( k2_tarski @ X1 @ X0 ) )
      | ( r2_hidden @ X1 @ X2 )
      | ( r2_hidden @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('4',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ( X12 != X13 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('5',plain,(
    ! [X13: $i] :
      ( r1_tarski @ X13 @ X13 ) ),
    inference(simplify,[status(thm)],['4'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('6',plain,(
    ! [X15: $i,X17: $i] :
      ( ( ( k4_xboole_0 @ X15 @ X17 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('8',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( k3_xboole_0 @ X24 @ ( k4_xboole_0 @ X25 @ X26 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X24 @ X25 ) @ X26 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('11',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k3_xboole_0 @ X22 @ X23 ) )
      = ( k4_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['9','12'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('14',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k3_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['9','12'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['9','12'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('24',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( k3_xboole_0 @ X24 @ ( k4_xboole_0 @ X25 @ X26 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X24 @ X25 ) @ X26 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf(t32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = ( k4_xboole_0 @ B @ A ) )
     => ( A = B ) ) )).

thf('26',plain,(
    ! [X20: $i,X21: $i] :
      ( ( X21 = X20 )
      | ( ( k4_xboole_0 @ X21 @ X20 )
       != ( k4_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t32_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) )
       != ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ( X0
        = ( k3_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
       != ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('30',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k3_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
       != ( k3_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
       != ( k3_xboole_0 @ ( k5_xboole_0 @ X1 @ k1_xboole_0 ) @ X0 ) )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['17','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('39',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k3_xboole_0 @ X22 @ X23 ) )
      = ( k4_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('40',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ X15 @ X16 )
      | ( ( k4_xboole_0 @ X15 @ X16 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_tarski @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ X0 @ ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X12: $i,X14: $i] :
      ( ( X12 = X14 )
      | ~ ( r1_tarski @ X14 @ X12 )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ X0 @ X0 ) @ X0 )
      | ( ( k3_xboole_0 @ X0 @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('46',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('47',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ( r2_hidden @ X10 @ X8 )
      | ( X9
       != ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('48',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','48'])).

thf('50',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['45','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('55',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( k3_xboole_0 @ X24 @ ( k4_xboole_0 @ X25 @ X26 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X24 @ X25 ) @ X26 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['53','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['37','57'])).

thf('59',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k3_xboole_0 @ X22 @ X23 ) )
      = ( k4_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) )
       != ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ( X0
        = ( k3_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
       != ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      | ( X1
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['9','12'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( X1
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ) ),
    inference('sup-',[status(thm)],['58','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['53','56'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( X0
        = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['64','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['15','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X2 @ ( k2_tarski @ X1 @ X0 ) )
        = X2 )
      | ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['3','72'])).

thf('74',plain,(
    sk_C_1
 != ( k4_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( sk_C_1 != sk_C_1 )
    | ( r2_hidden @ sk_A @ sk_C_1 )
    | ( r2_hidden @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( r2_hidden @ sk_B @ sk_C_1 )
    | ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ~ ( r2_hidden @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    r2_hidden @ sk_A @ sk_C_1 ),
    inference(clc,[status(thm)],['76','77'])).

thf('79',plain,(
    $false ),
    inference(demod,[status(thm)],['0','78'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.EKW2DXlJdz
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:07:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 7.56/7.74  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 7.56/7.74  % Solved by: fo/fo7.sh
% 7.56/7.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 7.56/7.74  % done 6964 iterations in 7.273s
% 7.56/7.74  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 7.56/7.74  % SZS output start Refutation
% 7.56/7.74  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 7.56/7.74  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 7.56/7.74  thf(sk_A_type, type, sk_A: $i).
% 7.56/7.74  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 7.56/7.74  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 7.56/7.74  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 7.56/7.74  thf(sk_C_1_type, type, sk_C_1: $i).
% 7.56/7.74  thf(sk_B_type, type, sk_B: $i).
% 7.56/7.74  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 7.56/7.74  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 7.56/7.74  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 7.56/7.74  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 7.56/7.74  thf(t144_zfmisc_1, conjecture,
% 7.56/7.74    (![A:$i,B:$i,C:$i]:
% 7.56/7.74     ( ~( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) & 
% 7.56/7.74          ( ( C ) != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) ))).
% 7.56/7.74  thf(zf_stmt_0, negated_conjecture,
% 7.56/7.74    (~( ![A:$i,B:$i,C:$i]:
% 7.56/7.74        ( ~( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) & 
% 7.56/7.74             ( ( C ) != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) ) )),
% 7.56/7.74    inference('cnf.neg', [status(esa)], [t144_zfmisc_1])).
% 7.56/7.74  thf('0', plain, (~ (r2_hidden @ sk_A @ sk_C_1)),
% 7.56/7.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.56/7.74  thf(t70_enumset1, axiom,
% 7.56/7.74    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 7.56/7.74  thf('1', plain,
% 7.56/7.74      (![X27 : $i, X28 : $i]:
% 7.56/7.74         ((k1_enumset1 @ X27 @ X27 @ X28) = (k2_tarski @ X27 @ X28))),
% 7.56/7.74      inference('cnf', [status(esa)], [t70_enumset1])).
% 7.56/7.74  thf(t72_zfmisc_1, axiom,
% 7.56/7.74    (![A:$i,B:$i,C:$i]:
% 7.56/7.74     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) <=>
% 7.56/7.74       ( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) ) ))).
% 7.56/7.74  thf('2', plain,
% 7.56/7.74      (![X32 : $i, X34 : $i, X35 : $i]:
% 7.56/7.74         (((k4_xboole_0 @ (k2_tarski @ X32 @ X34) @ X35)
% 7.56/7.74            = (k2_tarski @ X32 @ X34))
% 7.56/7.74          | (r2_hidden @ X34 @ X35)
% 7.56/7.74          | (r2_hidden @ X32 @ X35))),
% 7.56/7.74      inference('cnf', [status(esa)], [t72_zfmisc_1])).
% 7.56/7.74  thf('3', plain,
% 7.56/7.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.56/7.74         (((k4_xboole_0 @ (k1_enumset1 @ X1 @ X1 @ X0) @ X2)
% 7.56/7.74            = (k2_tarski @ X1 @ X0))
% 7.56/7.74          | (r2_hidden @ X1 @ X2)
% 7.56/7.74          | (r2_hidden @ X0 @ X2))),
% 7.56/7.74      inference('sup+', [status(thm)], ['1', '2'])).
% 7.56/7.74  thf(d10_xboole_0, axiom,
% 7.56/7.74    (![A:$i,B:$i]:
% 7.56/7.74     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 7.56/7.74  thf('4', plain,
% 7.56/7.74      (![X12 : $i, X13 : $i]: ((r1_tarski @ X12 @ X13) | ((X12) != (X13)))),
% 7.56/7.74      inference('cnf', [status(esa)], [d10_xboole_0])).
% 7.56/7.74  thf('5', plain, (![X13 : $i]: (r1_tarski @ X13 @ X13)),
% 7.56/7.74      inference('simplify', [status(thm)], ['4'])).
% 7.56/7.74  thf(l32_xboole_1, axiom,
% 7.56/7.74    (![A:$i,B:$i]:
% 7.56/7.74     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 7.56/7.74  thf('6', plain,
% 7.56/7.74      (![X15 : $i, X17 : $i]:
% 7.56/7.74         (((k4_xboole_0 @ X15 @ X17) = (k1_xboole_0))
% 7.56/7.74          | ~ (r1_tarski @ X15 @ X17))),
% 7.56/7.74      inference('cnf', [status(esa)], [l32_xboole_1])).
% 7.56/7.74  thf('7', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 7.56/7.74      inference('sup-', [status(thm)], ['5', '6'])).
% 7.56/7.74  thf(t49_xboole_1, axiom,
% 7.56/7.74    (![A:$i,B:$i,C:$i]:
% 7.56/7.74     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 7.56/7.74       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 7.56/7.74  thf('8', plain,
% 7.56/7.74      (![X24 : $i, X25 : $i, X26 : $i]:
% 7.56/7.74         ((k3_xboole_0 @ X24 @ (k4_xboole_0 @ X25 @ X26))
% 7.56/7.74           = (k4_xboole_0 @ (k3_xboole_0 @ X24 @ X25) @ X26))),
% 7.56/7.74      inference('cnf', [status(esa)], [t49_xboole_1])).
% 7.56/7.74  thf('9', plain,
% 7.56/7.74      (![X0 : $i, X1 : $i]:
% 7.56/7.74         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))
% 7.56/7.74           = (k1_xboole_0))),
% 7.56/7.74      inference('sup+', [status(thm)], ['7', '8'])).
% 7.56/7.74  thf(commutativity_k3_xboole_0, axiom,
% 7.56/7.74    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 7.56/7.74  thf('10', plain,
% 7.56/7.74      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 7.56/7.74      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 7.56/7.74  thf(t47_xboole_1, axiom,
% 7.56/7.74    (![A:$i,B:$i]:
% 7.56/7.74     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 7.56/7.74  thf('11', plain,
% 7.56/7.74      (![X22 : $i, X23 : $i]:
% 7.56/7.74         ((k4_xboole_0 @ X22 @ (k3_xboole_0 @ X22 @ X23))
% 7.56/7.74           = (k4_xboole_0 @ X22 @ X23))),
% 7.56/7.74      inference('cnf', [status(esa)], [t47_xboole_1])).
% 7.56/7.74  thf('12', plain,
% 7.56/7.74      (![X0 : $i, X1 : $i]:
% 7.56/7.74         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 7.56/7.74           = (k4_xboole_0 @ X0 @ X1))),
% 7.56/7.74      inference('sup+', [status(thm)], ['10', '11'])).
% 7.56/7.74  thf('13', plain,
% 7.56/7.74      (![X0 : $i, X1 : $i]:
% 7.56/7.74         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 7.56/7.74      inference('demod', [status(thm)], ['9', '12'])).
% 7.56/7.74  thf(t100_xboole_1, axiom,
% 7.56/7.74    (![A:$i,B:$i]:
% 7.56/7.74     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 7.56/7.74  thf('14', plain,
% 7.56/7.74      (![X18 : $i, X19 : $i]:
% 7.56/7.74         ((k4_xboole_0 @ X18 @ X19)
% 7.56/7.74           = (k5_xboole_0 @ X18 @ (k3_xboole_0 @ X18 @ X19)))),
% 7.56/7.74      inference('cnf', [status(esa)], [t100_xboole_1])).
% 7.56/7.74  thf('15', plain,
% 7.56/7.74      (![X0 : $i, X1 : $i]:
% 7.56/7.74         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 7.56/7.74           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 7.56/7.74      inference('sup+', [status(thm)], ['13', '14'])).
% 7.56/7.74  thf('16', plain,
% 7.56/7.74      (![X0 : $i, X1 : $i]:
% 7.56/7.74         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 7.56/7.74      inference('demod', [status(thm)], ['9', '12'])).
% 7.56/7.74  thf('17', plain,
% 7.56/7.74      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 7.56/7.74      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 7.56/7.74  thf('18', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 7.56/7.74      inference('sup-', [status(thm)], ['5', '6'])).
% 7.56/7.74  thf('19', plain,
% 7.56/7.74      (![X0 : $i, X1 : $i]:
% 7.56/7.74         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 7.56/7.74      inference('demod', [status(thm)], ['9', '12'])).
% 7.56/7.74  thf('20', plain,
% 7.56/7.74      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 7.56/7.74      inference('sup+', [status(thm)], ['18', '19'])).
% 7.56/7.74  thf('21', plain,
% 7.56/7.74      (![X0 : $i, X1 : $i]:
% 7.56/7.74         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 7.56/7.74           = (k4_xboole_0 @ X0 @ X1))),
% 7.56/7.74      inference('sup+', [status(thm)], ['10', '11'])).
% 7.56/7.74  thf('22', plain,
% 7.56/7.74      (![X0 : $i]:
% 7.56/7.74         ((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 7.56/7.74           = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 7.56/7.74      inference('sup+', [status(thm)], ['20', '21'])).
% 7.56/7.74  thf('23', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 7.56/7.74      inference('sup-', [status(thm)], ['5', '6'])).
% 7.56/7.74  thf('24', plain,
% 7.56/7.74      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 7.56/7.74      inference('demod', [status(thm)], ['22', '23'])).
% 7.56/7.74  thf('25', plain,
% 7.56/7.74      (![X24 : $i, X25 : $i, X26 : $i]:
% 7.56/7.74         ((k3_xboole_0 @ X24 @ (k4_xboole_0 @ X25 @ X26))
% 7.56/7.74           = (k4_xboole_0 @ (k3_xboole_0 @ X24 @ X25) @ X26))),
% 7.56/7.74      inference('cnf', [status(esa)], [t49_xboole_1])).
% 7.56/7.74  thf(t32_xboole_1, axiom,
% 7.56/7.74    (![A:$i,B:$i]:
% 7.56/7.74     ( ( ( k4_xboole_0 @ A @ B ) = ( k4_xboole_0 @ B @ A ) ) =>
% 7.56/7.74       ( ( A ) = ( B ) ) ))).
% 7.56/7.74  thf('26', plain,
% 7.56/7.74      (![X20 : $i, X21 : $i]:
% 7.56/7.74         (((X21) = (X20))
% 7.56/7.74          | ((k4_xboole_0 @ X21 @ X20) != (k4_xboole_0 @ X20 @ X21)))),
% 7.56/7.74      inference('cnf', [status(esa)], [t32_xboole_1])).
% 7.56/7.74  thf('27', plain,
% 7.56/7.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.56/7.74         (((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1))
% 7.56/7.74            != (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))
% 7.56/7.74          | ((X0) = (k3_xboole_0 @ X2 @ X1)))),
% 7.56/7.74      inference('sup-', [status(thm)], ['25', '26'])).
% 7.56/7.74  thf('28', plain,
% 7.56/7.74      (![X0 : $i, X1 : $i]:
% 7.56/7.74         (((k1_xboole_0)
% 7.56/7.74            != (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ k1_xboole_0)))
% 7.56/7.74          | ((k1_xboole_0) = (k3_xboole_0 @ X1 @ X0)))),
% 7.56/7.74      inference('sup-', [status(thm)], ['24', '27'])).
% 7.56/7.74  thf('29', plain,
% 7.56/7.74      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 7.56/7.74      inference('sup+', [status(thm)], ['18', '19'])).
% 7.56/7.74  thf('30', plain,
% 7.56/7.74      (![X18 : $i, X19 : $i]:
% 7.56/7.74         ((k4_xboole_0 @ X18 @ X19)
% 7.56/7.74           = (k5_xboole_0 @ X18 @ (k3_xboole_0 @ X18 @ X19)))),
% 7.56/7.74      inference('cnf', [status(esa)], [t100_xboole_1])).
% 7.56/7.74  thf('31', plain,
% 7.56/7.74      (![X0 : $i]:
% 7.56/7.74         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 7.56/7.74      inference('sup+', [status(thm)], ['29', '30'])).
% 7.56/7.74  thf('32', plain,
% 7.56/7.74      (![X0 : $i, X1 : $i]:
% 7.56/7.74         (((k1_xboole_0)
% 7.56/7.74            != (k3_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ k1_xboole_0)))
% 7.56/7.74          | ((k1_xboole_0) = (k3_xboole_0 @ X1 @ X0)))),
% 7.56/7.74      inference('demod', [status(thm)], ['28', '31'])).
% 7.56/7.74  thf('33', plain,
% 7.56/7.74      (![X0 : $i, X1 : $i]:
% 7.56/7.74         (((k1_xboole_0)
% 7.56/7.74            != (k3_xboole_0 @ (k5_xboole_0 @ X1 @ k1_xboole_0) @ X0))
% 7.56/7.74          | ((k1_xboole_0) = (k3_xboole_0 @ X0 @ X1)))),
% 7.56/7.74      inference('sup-', [status(thm)], ['17', '32'])).
% 7.56/7.74  thf('34', plain,
% 7.56/7.74      (![X0 : $i, X1 : $i]:
% 7.56/7.74         (((k1_xboole_0) != (k1_xboole_0))
% 7.56/7.74          | ((k1_xboole_0)
% 7.56/7.74              = (k3_xboole_0 @ 
% 7.56/7.74                 (k4_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ k1_xboole_0)) @ X0)))),
% 7.56/7.74      inference('sup-', [status(thm)], ['16', '33'])).
% 7.56/7.74  thf('35', plain,
% 7.56/7.74      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 7.56/7.74      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 7.56/7.74  thf('36', plain,
% 7.56/7.74      (![X0 : $i, X1 : $i]:
% 7.56/7.74         (((k1_xboole_0) != (k1_xboole_0))
% 7.56/7.74          | ((k1_xboole_0)
% 7.56/7.74              = (k3_xboole_0 @ X0 @ 
% 7.56/7.74                 (k4_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ k1_xboole_0)))))),
% 7.56/7.74      inference('demod', [status(thm)], ['34', '35'])).
% 7.56/7.74  thf('37', plain,
% 7.56/7.74      (![X0 : $i, X1 : $i]:
% 7.56/7.74         ((k1_xboole_0)
% 7.56/7.74           = (k3_xboole_0 @ X0 @ 
% 7.56/7.74              (k4_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ k1_xboole_0))))),
% 7.56/7.74      inference('simplify', [status(thm)], ['36'])).
% 7.56/7.74  thf('38', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 7.56/7.74      inference('sup-', [status(thm)], ['5', '6'])).
% 7.56/7.74  thf('39', plain,
% 7.56/7.74      (![X22 : $i, X23 : $i]:
% 7.56/7.74         ((k4_xboole_0 @ X22 @ (k3_xboole_0 @ X22 @ X23))
% 7.56/7.74           = (k4_xboole_0 @ X22 @ X23))),
% 7.56/7.74      inference('cnf', [status(esa)], [t47_xboole_1])).
% 7.56/7.74  thf('40', plain,
% 7.56/7.74      (![X15 : $i, X16 : $i]:
% 7.56/7.74         ((r1_tarski @ X15 @ X16)
% 7.56/7.74          | ((k4_xboole_0 @ X15 @ X16) != (k1_xboole_0)))),
% 7.56/7.74      inference('cnf', [status(esa)], [l32_xboole_1])).
% 7.56/7.74  thf('41', plain,
% 7.56/7.74      (![X0 : $i, X1 : $i]:
% 7.56/7.74         (((k4_xboole_0 @ X1 @ X0) != (k1_xboole_0))
% 7.56/7.74          | (r1_tarski @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 7.56/7.74      inference('sup-', [status(thm)], ['39', '40'])).
% 7.56/7.74  thf('42', plain,
% 7.56/7.74      (![X0 : $i]:
% 7.56/7.74         (((k1_xboole_0) != (k1_xboole_0))
% 7.56/7.74          | (r1_tarski @ X0 @ (k3_xboole_0 @ X0 @ X0)))),
% 7.56/7.74      inference('sup-', [status(thm)], ['38', '41'])).
% 7.56/7.74  thf('43', plain, (![X0 : $i]: (r1_tarski @ X0 @ (k3_xboole_0 @ X0 @ X0))),
% 7.56/7.74      inference('simplify', [status(thm)], ['42'])).
% 7.56/7.74  thf('44', plain,
% 7.56/7.74      (![X12 : $i, X14 : $i]:
% 7.56/7.74         (((X12) = (X14))
% 7.56/7.74          | ~ (r1_tarski @ X14 @ X12)
% 7.56/7.74          | ~ (r1_tarski @ X12 @ X14))),
% 7.56/7.74      inference('cnf', [status(esa)], [d10_xboole_0])).
% 7.56/7.74  thf('45', plain,
% 7.56/7.74      (![X0 : $i]:
% 7.56/7.74         (~ (r1_tarski @ (k3_xboole_0 @ X0 @ X0) @ X0)
% 7.56/7.74          | ((k3_xboole_0 @ X0 @ X0) = (X0)))),
% 7.56/7.74      inference('sup-', [status(thm)], ['43', '44'])).
% 7.56/7.74  thf(d3_tarski, axiom,
% 7.56/7.74    (![A:$i,B:$i]:
% 7.56/7.74     ( ( r1_tarski @ A @ B ) <=>
% 7.56/7.74       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 7.56/7.74  thf('46', plain,
% 7.56/7.74      (![X3 : $i, X5 : $i]:
% 7.56/7.74         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 7.56/7.74      inference('cnf', [status(esa)], [d3_tarski])).
% 7.56/7.74  thf(d4_xboole_0, axiom,
% 7.56/7.74    (![A:$i,B:$i,C:$i]:
% 7.56/7.74     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 7.56/7.74       ( ![D:$i]:
% 7.56/7.74         ( ( r2_hidden @ D @ C ) <=>
% 7.56/7.74           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 7.56/7.74  thf('47', plain,
% 7.56/7.74      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 7.56/7.74         (~ (r2_hidden @ X10 @ X9)
% 7.56/7.74          | (r2_hidden @ X10 @ X8)
% 7.56/7.74          | ((X9) != (k3_xboole_0 @ X7 @ X8)))),
% 7.56/7.74      inference('cnf', [status(esa)], [d4_xboole_0])).
% 7.56/7.74  thf('48', plain,
% 7.56/7.74      (![X7 : $i, X8 : $i, X10 : $i]:
% 7.56/7.74         ((r2_hidden @ X10 @ X8)
% 7.56/7.74          | ~ (r2_hidden @ X10 @ (k3_xboole_0 @ X7 @ X8)))),
% 7.56/7.74      inference('simplify', [status(thm)], ['47'])).
% 7.56/7.74  thf('49', plain,
% 7.56/7.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.56/7.74         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 7.56/7.74          | (r2_hidden @ (sk_C @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X0))),
% 7.56/7.74      inference('sup-', [status(thm)], ['46', '48'])).
% 7.56/7.74  thf('50', plain,
% 7.56/7.74      (![X3 : $i, X5 : $i]:
% 7.56/7.74         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 7.56/7.74      inference('cnf', [status(esa)], [d3_tarski])).
% 7.56/7.74  thf('51', plain,
% 7.56/7.74      (![X0 : $i, X1 : $i]:
% 7.56/7.74         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 7.56/7.74          | (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 7.56/7.74      inference('sup-', [status(thm)], ['49', '50'])).
% 7.56/7.74  thf('52', plain,
% 7.56/7.74      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 7.56/7.74      inference('simplify', [status(thm)], ['51'])).
% 7.56/7.74  thf('53', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 7.56/7.74      inference('demod', [status(thm)], ['45', '52'])).
% 7.56/7.74  thf('54', plain,
% 7.56/7.74      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 7.56/7.74      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 7.56/7.74  thf('55', plain,
% 7.56/7.74      (![X24 : $i, X25 : $i, X26 : $i]:
% 7.56/7.74         ((k3_xboole_0 @ X24 @ (k4_xboole_0 @ X25 @ X26))
% 7.56/7.74           = (k4_xboole_0 @ (k3_xboole_0 @ X24 @ X25) @ X26))),
% 7.56/7.74      inference('cnf', [status(esa)], [t49_xboole_1])).
% 7.56/7.74  thf('56', plain,
% 7.56/7.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.56/7.74         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 7.56/7.74           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 7.56/7.74      inference('sup+', [status(thm)], ['54', '55'])).
% 7.56/7.74  thf('57', plain,
% 7.56/7.74      (![X0 : $i, X1 : $i]:
% 7.56/7.74         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 7.56/7.74           = (k4_xboole_0 @ X0 @ X1))),
% 7.56/7.74      inference('sup+', [status(thm)], ['53', '56'])).
% 7.56/7.74  thf('58', plain,
% 7.56/7.74      (![X0 : $i]:
% 7.56/7.74         ((k1_xboole_0) = (k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ k1_xboole_0)))),
% 7.56/7.74      inference('sup+', [status(thm)], ['37', '57'])).
% 7.56/7.74  thf('59', plain,
% 7.56/7.74      (![X22 : $i, X23 : $i]:
% 7.56/7.74         ((k4_xboole_0 @ X22 @ (k3_xboole_0 @ X22 @ X23))
% 7.56/7.74           = (k4_xboole_0 @ X22 @ X23))),
% 7.56/7.74      inference('cnf', [status(esa)], [t47_xboole_1])).
% 7.56/7.74  thf('60', plain,
% 7.56/7.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.56/7.74         (((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1))
% 7.56/7.74            != (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))
% 7.56/7.74          | ((X0) = (k3_xboole_0 @ X2 @ X1)))),
% 7.56/7.74      inference('sup-', [status(thm)], ['25', '26'])).
% 7.56/7.74  thf('61', plain,
% 7.56/7.74      (![X0 : $i, X1 : $i]:
% 7.56/7.74         (((k4_xboole_0 @ X1 @ X0)
% 7.56/7.74            != (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)))
% 7.56/7.74          | ((X1) = (k3_xboole_0 @ X1 @ X0)))),
% 7.56/7.74      inference('sup-', [status(thm)], ['59', '60'])).
% 7.56/7.74  thf('62', plain,
% 7.56/7.74      (![X0 : $i, X1 : $i]:
% 7.56/7.74         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 7.56/7.74      inference('demod', [status(thm)], ['9', '12'])).
% 7.56/7.74  thf('63', plain,
% 7.56/7.74      (![X0 : $i, X1 : $i]:
% 7.56/7.74         (((k4_xboole_0 @ X1 @ X0) != (k1_xboole_0))
% 7.56/7.74          | ((X1) = (k3_xboole_0 @ X1 @ X0)))),
% 7.56/7.74      inference('demod', [status(thm)], ['61', '62'])).
% 7.56/7.74  thf('64', plain,
% 7.56/7.74      (![X0 : $i]:
% 7.56/7.74         (((k1_xboole_0) != (k1_xboole_0))
% 7.56/7.74          | ((X0) = (k3_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ k1_xboole_0))))),
% 7.56/7.74      inference('sup-', [status(thm)], ['58', '63'])).
% 7.56/7.74  thf('65', plain,
% 7.56/7.74      (![X0 : $i]:
% 7.56/7.74         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 7.56/7.74      inference('sup+', [status(thm)], ['29', '30'])).
% 7.56/7.74  thf('66', plain,
% 7.56/7.74      (![X0 : $i, X1 : $i]:
% 7.56/7.74         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 7.56/7.74           = (k4_xboole_0 @ X0 @ X1))),
% 7.56/7.74      inference('sup+', [status(thm)], ['53', '56'])).
% 7.56/7.74  thf('67', plain,
% 7.56/7.74      (![X0 : $i]:
% 7.56/7.74         ((k3_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ k1_xboole_0))
% 7.56/7.74           = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 7.56/7.74      inference('sup+', [status(thm)], ['65', '66'])).
% 7.56/7.74  thf('68', plain,
% 7.56/7.74      (![X0 : $i]:
% 7.56/7.74         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 7.56/7.74      inference('sup+', [status(thm)], ['29', '30'])).
% 7.56/7.74  thf('69', plain,
% 7.56/7.74      (![X0 : $i]:
% 7.56/7.74         ((k3_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ k1_xboole_0))
% 7.56/7.74           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 7.56/7.74      inference('demod', [status(thm)], ['67', '68'])).
% 7.56/7.74  thf('70', plain,
% 7.56/7.74      (![X0 : $i]:
% 7.56/7.74         (((k1_xboole_0) != (k1_xboole_0))
% 7.56/7.74          | ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0)))),
% 7.56/7.74      inference('demod', [status(thm)], ['64', '69'])).
% 7.56/7.74  thf('71', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 7.56/7.74      inference('simplify', [status(thm)], ['70'])).
% 7.56/7.74  thf('72', plain,
% 7.56/7.74      (![X0 : $i, X1 : $i]:
% 7.56/7.74         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 7.56/7.74      inference('demod', [status(thm)], ['15', '71'])).
% 7.56/7.74  thf('73', plain,
% 7.56/7.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.56/7.74         (((k4_xboole_0 @ X2 @ (k2_tarski @ X1 @ X0)) = (X2))
% 7.56/7.74          | (r2_hidden @ X0 @ X2)
% 7.56/7.74          | (r2_hidden @ X1 @ X2))),
% 7.56/7.74      inference('sup+', [status(thm)], ['3', '72'])).
% 7.56/7.74  thf('74', plain,
% 7.56/7.74      (((sk_C_1) != (k4_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_A @ sk_B)))),
% 7.56/7.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.56/7.74  thf('75', plain,
% 7.56/7.74      ((((sk_C_1) != (sk_C_1))
% 7.56/7.74        | (r2_hidden @ sk_A @ sk_C_1)
% 7.56/7.74        | (r2_hidden @ sk_B @ sk_C_1))),
% 7.56/7.74      inference('sup-', [status(thm)], ['73', '74'])).
% 7.56/7.74  thf('76', plain,
% 7.56/7.74      (((r2_hidden @ sk_B @ sk_C_1) | (r2_hidden @ sk_A @ sk_C_1))),
% 7.56/7.74      inference('simplify', [status(thm)], ['75'])).
% 7.56/7.74  thf('77', plain, (~ (r2_hidden @ sk_B @ sk_C_1)),
% 7.56/7.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.56/7.74  thf('78', plain, ((r2_hidden @ sk_A @ sk_C_1)),
% 7.56/7.74      inference('clc', [status(thm)], ['76', '77'])).
% 7.56/7.74  thf('79', plain, ($false), inference('demod', [status(thm)], ['0', '78'])).
% 7.56/7.74  
% 7.56/7.74  % SZS output end Refutation
% 7.56/7.74  
% 7.56/7.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
