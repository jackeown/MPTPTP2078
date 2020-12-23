%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MS5NimZTk3

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:09 EST 2020

% Result     : Theorem 1.44s
% Output     : Refutation 1.44s
% Verified   : 
% Statistics : Number of formulae       :  127 (1278 expanded)
%              Number of leaves         :   31 ( 454 expanded)
%              Depth                    :   26
%              Number of atoms          :  979 (10561 expanded)
%              Number of equality atoms :  109 (1260 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

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
    ! [X85: $i,X86: $i,X87: $i] :
      ( ( r2_hidden @ X85 @ X86 )
      | ( r2_hidden @ X87 @ X86 )
      | ( X86
        = ( k4_xboole_0 @ X86 @ ( k2_tarski @ X85 @ X87 ) ) ) ) ),
    inference(cnf,[status(esa)],[t144_zfmisc_1])).

thf('2',plain,(
    sk_C
 != ( k4_xboole_0 @ ( k2_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t98_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ A @ C @ B ) ) )).

thf('3',plain,(
    ! [X80: $i,X81: $i,X82: $i] :
      ( ( k1_enumset1 @ X80 @ X82 @ X81 )
      = ( k1_enumset1 @ X80 @ X81 @ X82 ) ) ),
    inference(cnf,[status(esa)],[t98_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X53: $i,X54: $i] :
      ( ( k1_enumset1 @ X53 @ X53 @ X54 )
      = ( k2_tarski @ X53 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t137_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('6',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X24 @ X23 ) @ ( k2_tarski @ X25 @ X23 ) )
      = ( k1_enumset1 @ X23 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t137_enumset1])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('7',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k2_tarski @ X26 @ X27 )
      = ( k2_xboole_0 @ ( k1_tarski @ X26 ) @ ( k1_tarski @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('8',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k2_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t6_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('10',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X12 @ ( k2_xboole_0 @ X12 @ X13 ) )
      = ( k2_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_1])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('11',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k3_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X18 @ X19 ) @ ( k2_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('12',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k5_xboole_0 @ X14 @ ( k5_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('13',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k3_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k5_xboole_0 @ X19 @ ( k2_xboole_0 @ X18 @ X19 ) ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('15',plain,(
    ! [X17: $i] :
      ( ( k5_xboole_0 @ X17 @ X17 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('17',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('18',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k3_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k5_xboole_0 @ X19 @ ( k2_xboole_0 @ X18 @ X19 ) ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('20',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('21',plain,(
    ! [X17: $i] :
      ( ( k5_xboole_0 @ X17 @ X17 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['16','22'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('24',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X17: $i] :
      ( ( k5_xboole_0 @ X17 @ X17 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['9','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['6','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['5','29'])).

thf('31',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k3_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k5_xboole_0 @ X19 @ ( k2_xboole_0 @ X18 @ X19 ) ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('32',plain,(
    ! [X17: $i] :
      ( ( k5_xboole_0 @ X17 @ X17 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('33',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k5_xboole_0 @ X14 @ ( k5_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['31','38'])).

thf('40',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['34','37'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['41','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['30','47'])).

thf('49',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k2_tarski @ X26 @ X27 )
      = ( k2_xboole_0 @ ( k1_tarski @ X26 ) @ ( k1_tarski @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('51',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ ( k4_xboole_0 @ X8 @ X7 ) )
      = ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ k1_xboole_0 )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k2_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('54',plain,(
    ! [X6: $i] :
      ( ( k2_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('55',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k2_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['52','53','54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['49','56'])).

thf('58',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k2_tarski @ X26 @ X27 )
      = ( k2_xboole_0 @ ( k1_tarski @ X26 ) @ ( k1_tarski @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['48','59','60'])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('62',plain,(
    ! [X83: $i,X84: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X83 @ X84 ) )
      = ( k2_xboole_0 @ X83 @ X84 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X83: $i,X84: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X83 @ X84 ) )
      = ( k2_xboole_0 @ X83 @ X84 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['52','53','54','55'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['66','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['34','37'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['70','73'])).

thf('75',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k2_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('76',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X12 @ ( k2_xboole_0 @ X12 @ X13 ) )
      = ( k2_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_1])).

thf('77',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['74','75','76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['65','78'])).

thf('80',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X12 @ ( k2_xboole_0 @ X12 @ X13 ) )
      = ( k2_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_1])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['80','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['79','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['65','78'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['85','86','87'])).

thf('89',plain,(
    sk_C
 != ( k4_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','88'])).

thf('90',plain,
    ( ( sk_C != sk_C )
    | ( r2_hidden @ sk_B @ sk_C )
    | ( r2_hidden @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1','89'])).

thf('91',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
    | ( r2_hidden @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    r2_hidden @ sk_B @ sk_C ),
    inference(clc,[status(thm)],['91','92'])).

thf('94',plain,(
    $false ),
    inference(demod,[status(thm)],['0','93'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MS5NimZTk3
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:12:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.44/1.69  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.44/1.69  % Solved by: fo/fo7.sh
% 1.44/1.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.44/1.69  % done 1659 iterations in 1.229s
% 1.44/1.69  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.44/1.69  % SZS output start Refutation
% 1.44/1.69  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.44/1.69  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.44/1.69  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.44/1.69  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 1.44/1.69  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.44/1.69  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.44/1.69  thf(sk_B_type, type, sk_B: $i).
% 1.44/1.69  thf(sk_A_type, type, sk_A: $i).
% 1.44/1.69  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.44/1.69  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 1.44/1.69  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.44/1.69  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.44/1.69  thf(sk_C_type, type, sk_C: $i).
% 1.44/1.69  thf(t145_zfmisc_1, conjecture,
% 1.44/1.69    (![A:$i,B:$i,C:$i]:
% 1.44/1.69     ( ~( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) & 
% 1.44/1.69          ( ( C ) !=
% 1.44/1.69            ( k4_xboole_0 @
% 1.44/1.69              ( k2_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) @ 
% 1.44/1.69              ( k2_tarski @ A @ B ) ) ) ) ))).
% 1.44/1.69  thf(zf_stmt_0, negated_conjecture,
% 1.44/1.69    (~( ![A:$i,B:$i,C:$i]:
% 1.44/1.69        ( ~( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) & 
% 1.44/1.69             ( ( C ) !=
% 1.44/1.69               ( k4_xboole_0 @
% 1.44/1.69                 ( k2_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) @ 
% 1.44/1.69                 ( k2_tarski @ A @ B ) ) ) ) ) )),
% 1.44/1.69    inference('cnf.neg', [status(esa)], [t145_zfmisc_1])).
% 1.44/1.69  thf('0', plain, (~ (r2_hidden @ sk_B @ sk_C)),
% 1.44/1.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.69  thf(t144_zfmisc_1, axiom,
% 1.44/1.69    (![A:$i,B:$i,C:$i]:
% 1.44/1.69     ( ~( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) & 
% 1.44/1.69          ( ( C ) != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) ))).
% 1.44/1.69  thf('1', plain,
% 1.44/1.69      (![X85 : $i, X86 : $i, X87 : $i]:
% 1.44/1.69         ((r2_hidden @ X85 @ X86)
% 1.44/1.69          | (r2_hidden @ X87 @ X86)
% 1.44/1.69          | ((X86) = (k4_xboole_0 @ X86 @ (k2_tarski @ X85 @ X87))))),
% 1.44/1.69      inference('cnf', [status(esa)], [t144_zfmisc_1])).
% 1.44/1.69  thf('2', plain,
% 1.44/1.69      (((sk_C)
% 1.44/1.69         != (k4_xboole_0 @ (k2_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)) @ 
% 1.44/1.69             (k2_tarski @ sk_A @ sk_B)))),
% 1.44/1.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.69  thf(t98_enumset1, axiom,
% 1.44/1.69    (![A:$i,B:$i,C:$i]:
% 1.44/1.69     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ A @ C @ B ) ))).
% 1.44/1.69  thf('3', plain,
% 1.44/1.69      (![X80 : $i, X81 : $i, X82 : $i]:
% 1.44/1.69         ((k1_enumset1 @ X80 @ X82 @ X81) = (k1_enumset1 @ X80 @ X81 @ X82))),
% 1.44/1.69      inference('cnf', [status(esa)], [t98_enumset1])).
% 1.44/1.69  thf(t70_enumset1, axiom,
% 1.44/1.69    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 1.44/1.69  thf('4', plain,
% 1.44/1.69      (![X53 : $i, X54 : $i]:
% 1.44/1.69         ((k1_enumset1 @ X53 @ X53 @ X54) = (k2_tarski @ X53 @ X54))),
% 1.44/1.69      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.44/1.69  thf('5', plain,
% 1.44/1.69      (![X0 : $i, X1 : $i]:
% 1.44/1.69         ((k1_enumset1 @ X0 @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 1.44/1.69      inference('sup+', [status(thm)], ['3', '4'])).
% 1.44/1.69  thf(t137_enumset1, axiom,
% 1.44/1.69    (![A:$i,B:$i,C:$i]:
% 1.44/1.69     ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) ) =
% 1.44/1.69       ( k1_enumset1 @ A @ B @ C ) ))).
% 1.44/1.69  thf('6', plain,
% 1.44/1.69      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.44/1.69         ((k2_xboole_0 @ (k2_tarski @ X24 @ X23) @ (k2_tarski @ X25 @ X23))
% 1.44/1.69           = (k1_enumset1 @ X23 @ X24 @ X25))),
% 1.44/1.69      inference('cnf', [status(esa)], [t137_enumset1])).
% 1.44/1.69  thf(t41_enumset1, axiom,
% 1.44/1.69    (![A:$i,B:$i]:
% 1.44/1.69     ( ( k2_tarski @ A @ B ) =
% 1.44/1.69       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 1.44/1.69  thf('7', plain,
% 1.44/1.69      (![X26 : $i, X27 : $i]:
% 1.44/1.69         ((k2_tarski @ X26 @ X27)
% 1.44/1.69           = (k2_xboole_0 @ (k1_tarski @ X26) @ (k1_tarski @ X27)))),
% 1.44/1.69      inference('cnf', [status(esa)], [t41_enumset1])).
% 1.44/1.69  thf(t4_xboole_1, axiom,
% 1.44/1.69    (![A:$i,B:$i,C:$i]:
% 1.44/1.69     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 1.44/1.69       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 1.44/1.69  thf('8', plain,
% 1.44/1.69      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.44/1.69         ((k2_xboole_0 @ (k2_xboole_0 @ X9 @ X10) @ X11)
% 1.44/1.69           = (k2_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 1.44/1.69      inference('cnf', [status(esa)], [t4_xboole_1])).
% 1.44/1.69  thf('9', plain,
% 1.44/1.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.44/1.69         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 1.44/1.69           = (k2_xboole_0 @ (k1_tarski @ X1) @ 
% 1.44/1.69              (k2_xboole_0 @ (k1_tarski @ X0) @ X2)))),
% 1.44/1.69      inference('sup+', [status(thm)], ['7', '8'])).
% 1.44/1.69  thf(t6_xboole_1, axiom,
% 1.44/1.69    (![A:$i,B:$i]:
% 1.44/1.69     ( ( k2_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.44/1.69  thf('10', plain,
% 1.44/1.69      (![X12 : $i, X13 : $i]:
% 1.44/1.69         ((k2_xboole_0 @ X12 @ (k2_xboole_0 @ X12 @ X13))
% 1.44/1.69           = (k2_xboole_0 @ X12 @ X13))),
% 1.44/1.69      inference('cnf', [status(esa)], [t6_xboole_1])).
% 1.44/1.69  thf(t95_xboole_1, axiom,
% 1.44/1.69    (![A:$i,B:$i]:
% 1.44/1.69     ( ( k3_xboole_0 @ A @ B ) =
% 1.44/1.69       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 1.44/1.69  thf('11', plain,
% 1.44/1.69      (![X18 : $i, X19 : $i]:
% 1.44/1.69         ((k3_xboole_0 @ X18 @ X19)
% 1.44/1.69           = (k5_xboole_0 @ (k5_xboole_0 @ X18 @ X19) @ 
% 1.44/1.69              (k2_xboole_0 @ X18 @ X19)))),
% 1.44/1.69      inference('cnf', [status(esa)], [t95_xboole_1])).
% 1.44/1.69  thf(t91_xboole_1, axiom,
% 1.44/1.69    (![A:$i,B:$i,C:$i]:
% 1.44/1.69     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 1.44/1.69       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 1.44/1.69  thf('12', plain,
% 1.44/1.69      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.44/1.69         ((k5_xboole_0 @ (k5_xboole_0 @ X14 @ X15) @ X16)
% 1.44/1.69           = (k5_xboole_0 @ X14 @ (k5_xboole_0 @ X15 @ X16)))),
% 1.44/1.69      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.44/1.69  thf('13', plain,
% 1.44/1.69      (![X18 : $i, X19 : $i]:
% 1.44/1.69         ((k3_xboole_0 @ X18 @ X19)
% 1.44/1.69           = (k5_xboole_0 @ X18 @ 
% 1.44/1.69              (k5_xboole_0 @ X19 @ (k2_xboole_0 @ X18 @ X19))))),
% 1.44/1.69      inference('demod', [status(thm)], ['11', '12'])).
% 1.44/1.69  thf('14', plain,
% 1.44/1.69      (![X0 : $i, X1 : $i]:
% 1.44/1.69         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 1.44/1.69           = (k5_xboole_0 @ X1 @ 
% 1.44/1.69              (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))))),
% 1.44/1.69      inference('sup+', [status(thm)], ['10', '13'])).
% 1.44/1.69  thf(t92_xboole_1, axiom,
% 1.44/1.69    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 1.44/1.69  thf('15', plain, (![X17 : $i]: ((k5_xboole_0 @ X17 @ X17) = (k1_xboole_0))),
% 1.44/1.69      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.44/1.69  thf('16', plain,
% 1.44/1.69      (![X0 : $i, X1 : $i]:
% 1.44/1.69         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 1.44/1.69           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 1.44/1.69      inference('demod', [status(thm)], ['14', '15'])).
% 1.44/1.69  thf(idempotence_k2_xboole_0, axiom,
% 1.44/1.69    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 1.44/1.69  thf('17', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ X2) = (X2))),
% 1.44/1.69      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 1.44/1.69  thf('18', plain,
% 1.44/1.69      (![X18 : $i, X19 : $i]:
% 1.44/1.69         ((k3_xboole_0 @ X18 @ X19)
% 1.44/1.69           = (k5_xboole_0 @ X18 @ 
% 1.44/1.69              (k5_xboole_0 @ X19 @ (k2_xboole_0 @ X18 @ X19))))),
% 1.44/1.69      inference('demod', [status(thm)], ['11', '12'])).
% 1.44/1.69  thf('19', plain,
% 1.44/1.69      (![X0 : $i]:
% 1.44/1.69         ((k3_xboole_0 @ X0 @ X0)
% 1.44/1.69           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 1.44/1.69      inference('sup+', [status(thm)], ['17', '18'])).
% 1.44/1.69  thf(idempotence_k3_xboole_0, axiom,
% 1.44/1.69    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 1.44/1.69  thf('20', plain, (![X3 : $i]: ((k3_xboole_0 @ X3 @ X3) = (X3))),
% 1.44/1.69      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 1.44/1.69  thf('21', plain, (![X17 : $i]: ((k5_xboole_0 @ X17 @ X17) = (k1_xboole_0))),
% 1.44/1.69      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.44/1.69  thf('22', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.44/1.69      inference('demod', [status(thm)], ['19', '20', '21'])).
% 1.44/1.69  thf('23', plain,
% 1.44/1.69      (![X0 : $i, X1 : $i]:
% 1.44/1.69         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (X1))),
% 1.44/1.69      inference('demod', [status(thm)], ['16', '22'])).
% 1.44/1.69  thf(t100_xboole_1, axiom,
% 1.44/1.69    (![A:$i,B:$i]:
% 1.44/1.69     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.44/1.69  thf('24', plain,
% 1.44/1.69      (![X4 : $i, X5 : $i]:
% 1.44/1.69         ((k4_xboole_0 @ X4 @ X5)
% 1.44/1.69           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 1.44/1.69      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.44/1.69  thf('25', plain,
% 1.44/1.69      (![X0 : $i, X1 : $i]:
% 1.44/1.69         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 1.44/1.69           = (k5_xboole_0 @ X0 @ X0))),
% 1.44/1.69      inference('sup+', [status(thm)], ['23', '24'])).
% 1.44/1.69  thf('26', plain, (![X17 : $i]: ((k5_xboole_0 @ X17 @ X17) = (k1_xboole_0))),
% 1.44/1.69      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.44/1.69  thf('27', plain,
% 1.44/1.69      (![X0 : $i, X1 : $i]:
% 1.44/1.69         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 1.44/1.69      inference('demod', [status(thm)], ['25', '26'])).
% 1.44/1.69  thf('28', plain,
% 1.44/1.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.44/1.69         ((k4_xboole_0 @ (k1_tarski @ X2) @ 
% 1.44/1.69           (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ X0)) = (k1_xboole_0))),
% 1.44/1.69      inference('sup+', [status(thm)], ['9', '27'])).
% 1.44/1.69  thf('29', plain,
% 1.44/1.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.44/1.69         ((k4_xboole_0 @ (k1_tarski @ X1) @ (k1_enumset1 @ X2 @ X1 @ X0))
% 1.44/1.69           = (k1_xboole_0))),
% 1.44/1.69      inference('sup+', [status(thm)], ['6', '28'])).
% 1.44/1.69  thf('30', plain,
% 1.44/1.69      (![X0 : $i, X1 : $i]:
% 1.44/1.69         ((k4_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X1 @ X0))
% 1.44/1.69           = (k1_xboole_0))),
% 1.44/1.69      inference('sup+', [status(thm)], ['5', '29'])).
% 1.44/1.69  thf('31', plain,
% 1.44/1.69      (![X18 : $i, X19 : $i]:
% 1.44/1.69         ((k3_xboole_0 @ X18 @ X19)
% 1.44/1.69           = (k5_xboole_0 @ X18 @ 
% 1.44/1.69              (k5_xboole_0 @ X19 @ (k2_xboole_0 @ X18 @ X19))))),
% 1.44/1.69      inference('demod', [status(thm)], ['11', '12'])).
% 1.44/1.69  thf('32', plain, (![X17 : $i]: ((k5_xboole_0 @ X17 @ X17) = (k1_xboole_0))),
% 1.44/1.69      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.44/1.69  thf('33', plain,
% 1.44/1.69      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.44/1.69         ((k5_xboole_0 @ (k5_xboole_0 @ X14 @ X15) @ X16)
% 1.44/1.69           = (k5_xboole_0 @ X14 @ (k5_xboole_0 @ X15 @ X16)))),
% 1.44/1.69      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.44/1.69  thf('34', plain,
% 1.44/1.69      (![X0 : $i, X1 : $i]:
% 1.44/1.69         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 1.44/1.69           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.44/1.69      inference('sup+', [status(thm)], ['32', '33'])).
% 1.44/1.69  thf('35', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.44/1.69      inference('demod', [status(thm)], ['19', '20', '21'])).
% 1.44/1.69  thf(commutativity_k5_xboole_0, axiom,
% 1.44/1.69    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 1.44/1.69  thf('36', plain,
% 1.44/1.69      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 1.44/1.69      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.44/1.69  thf('37', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.44/1.69      inference('sup+', [status(thm)], ['35', '36'])).
% 1.44/1.69  thf('38', plain,
% 1.44/1.69      (![X0 : $i, X1 : $i]:
% 1.44/1.69         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.44/1.69      inference('demod', [status(thm)], ['34', '37'])).
% 1.44/1.69  thf('39', plain,
% 1.44/1.69      (![X0 : $i, X1 : $i]:
% 1.44/1.69         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 1.44/1.69           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.44/1.69      inference('sup+', [status(thm)], ['31', '38'])).
% 1.44/1.69  thf('40', plain,
% 1.44/1.69      (![X4 : $i, X5 : $i]:
% 1.44/1.69         ((k4_xboole_0 @ X4 @ X5)
% 1.44/1.69           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 1.44/1.69      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.44/1.69  thf('41', plain,
% 1.44/1.69      (![X0 : $i, X1 : $i]:
% 1.44/1.69         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 1.44/1.69           = (k4_xboole_0 @ X1 @ X0))),
% 1.44/1.69      inference('demod', [status(thm)], ['39', '40'])).
% 1.44/1.69  thf('42', plain,
% 1.44/1.69      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 1.44/1.69      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.44/1.69  thf('43', plain,
% 1.44/1.69      (![X0 : $i, X1 : $i]:
% 1.44/1.69         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.44/1.69      inference('demod', [status(thm)], ['34', '37'])).
% 1.44/1.69  thf('44', plain,
% 1.44/1.69      (![X0 : $i, X1 : $i]:
% 1.44/1.69         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.44/1.69      inference('sup+', [status(thm)], ['42', '43'])).
% 1.44/1.69  thf('45', plain,
% 1.44/1.69      (![X0 : $i, X1 : $i]:
% 1.44/1.69         ((X0)
% 1.44/1.69           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0)))),
% 1.44/1.69      inference('sup+', [status(thm)], ['41', '44'])).
% 1.44/1.69  thf('46', plain,
% 1.44/1.69      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 1.44/1.69      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.44/1.69  thf('47', plain,
% 1.44/1.69      (![X0 : $i, X1 : $i]:
% 1.44/1.69         ((X0)
% 1.44/1.69           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0)))),
% 1.44/1.69      inference('demod', [status(thm)], ['45', '46'])).
% 1.44/1.69  thf('48', plain,
% 1.44/1.69      (![X0 : $i, X1 : $i]:
% 1.44/1.69         ((k2_tarski @ X1 @ X0)
% 1.44/1.69           = (k5_xboole_0 @ k1_xboole_0 @ 
% 1.44/1.69              (k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X1 @ X0))))),
% 1.44/1.69      inference('sup+', [status(thm)], ['30', '47'])).
% 1.44/1.69  thf('49', plain,
% 1.44/1.69      (![X26 : $i, X27 : $i]:
% 1.44/1.69         ((k2_tarski @ X26 @ X27)
% 1.44/1.69           = (k2_xboole_0 @ (k1_tarski @ X26) @ (k1_tarski @ X27)))),
% 1.44/1.69      inference('cnf', [status(esa)], [t41_enumset1])).
% 1.44/1.69  thf('50', plain,
% 1.44/1.69      (![X0 : $i, X1 : $i]:
% 1.44/1.69         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 1.44/1.69      inference('demod', [status(thm)], ['25', '26'])).
% 1.44/1.69  thf(t39_xboole_1, axiom,
% 1.44/1.69    (![A:$i,B:$i]:
% 1.44/1.69     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.44/1.69  thf('51', plain,
% 1.44/1.69      (![X7 : $i, X8 : $i]:
% 1.44/1.69         ((k2_xboole_0 @ X7 @ (k4_xboole_0 @ X8 @ X7))
% 1.44/1.69           = (k2_xboole_0 @ X7 @ X8))),
% 1.44/1.69      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.44/1.69  thf('52', plain,
% 1.44/1.69      (![X0 : $i, X1 : $i]:
% 1.44/1.69         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ k1_xboole_0)
% 1.44/1.69           = (k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 1.44/1.69      inference('sup+', [status(thm)], ['50', '51'])).
% 1.44/1.69  thf('53', plain,
% 1.44/1.69      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.44/1.69         ((k2_xboole_0 @ (k2_xboole_0 @ X9 @ X10) @ X11)
% 1.44/1.69           = (k2_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 1.44/1.69      inference('cnf', [status(esa)], [t4_xboole_1])).
% 1.44/1.69  thf(t1_boole, axiom,
% 1.44/1.69    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.44/1.69  thf('54', plain, (![X6 : $i]: ((k2_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 1.44/1.69      inference('cnf', [status(esa)], [t1_boole])).
% 1.44/1.69  thf('55', plain,
% 1.44/1.69      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.44/1.69         ((k2_xboole_0 @ (k2_xboole_0 @ X9 @ X10) @ X11)
% 1.44/1.69           = (k2_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 1.44/1.69      inference('cnf', [status(esa)], [t4_xboole_1])).
% 1.44/1.69  thf('56', plain,
% 1.44/1.69      (![X0 : $i, X1 : $i]:
% 1.44/1.69         ((k2_xboole_0 @ X0 @ X1)
% 1.44/1.69           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.44/1.69      inference('demod', [status(thm)], ['52', '53', '54', '55'])).
% 1.44/1.69  thf('57', plain,
% 1.44/1.69      (![X0 : $i, X1 : $i]:
% 1.44/1.69         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1))
% 1.44/1.69           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X1 @ X0)))),
% 1.44/1.69      inference('sup+', [status(thm)], ['49', '56'])).
% 1.44/1.69  thf('58', plain,
% 1.44/1.69      (![X26 : $i, X27 : $i]:
% 1.44/1.69         ((k2_tarski @ X26 @ X27)
% 1.44/1.69           = (k2_xboole_0 @ (k1_tarski @ X26) @ (k1_tarski @ X27)))),
% 1.44/1.69      inference('cnf', [status(esa)], [t41_enumset1])).
% 1.44/1.69  thf('59', plain,
% 1.44/1.69      (![X0 : $i, X1 : $i]:
% 1.44/1.69         ((k2_tarski @ X0 @ X1)
% 1.44/1.69           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X1 @ X0)))),
% 1.44/1.69      inference('demod', [status(thm)], ['57', '58'])).
% 1.44/1.69  thf('60', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.44/1.69      inference('sup+', [status(thm)], ['35', '36'])).
% 1.44/1.69  thf('61', plain,
% 1.44/1.69      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 1.44/1.69      inference('demod', [status(thm)], ['48', '59', '60'])).
% 1.44/1.69  thf(l51_zfmisc_1, axiom,
% 1.44/1.69    (![A:$i,B:$i]:
% 1.44/1.69     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.44/1.69  thf('62', plain,
% 1.44/1.69      (![X83 : $i, X84 : $i]:
% 1.44/1.69         ((k3_tarski @ (k2_tarski @ X83 @ X84)) = (k2_xboole_0 @ X83 @ X84))),
% 1.44/1.69      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.44/1.69  thf('63', plain,
% 1.44/1.69      (![X0 : $i, X1 : $i]:
% 1.44/1.69         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 1.44/1.69      inference('sup+', [status(thm)], ['61', '62'])).
% 1.44/1.69  thf('64', plain,
% 1.44/1.69      (![X83 : $i, X84 : $i]:
% 1.44/1.69         ((k3_tarski @ (k2_tarski @ X83 @ X84)) = (k2_xboole_0 @ X83 @ X84))),
% 1.44/1.69      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.44/1.69  thf('65', plain,
% 1.44/1.69      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.44/1.69      inference('sup+', [status(thm)], ['63', '64'])).
% 1.44/1.69  thf('66', plain,
% 1.44/1.69      (![X0 : $i, X1 : $i]:
% 1.44/1.69         ((k2_xboole_0 @ X0 @ X1)
% 1.44/1.69           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.44/1.69      inference('demod', [status(thm)], ['52', '53', '54', '55'])).
% 1.44/1.69  thf('67', plain,
% 1.44/1.69      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.44/1.69      inference('sup+', [status(thm)], ['63', '64'])).
% 1.44/1.69  thf('68', plain,
% 1.44/1.69      (![X0 : $i, X1 : $i]:
% 1.44/1.69         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 1.44/1.69      inference('demod', [status(thm)], ['25', '26'])).
% 1.44/1.69  thf('69', plain,
% 1.44/1.69      (![X0 : $i, X1 : $i]:
% 1.44/1.69         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 1.44/1.69      inference('sup+', [status(thm)], ['67', '68'])).
% 1.44/1.69  thf('70', plain,
% 1.44/1.69      (![X0 : $i, X1 : $i]:
% 1.44/1.69         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0))
% 1.44/1.69           = (k1_xboole_0))),
% 1.44/1.69      inference('sup+', [status(thm)], ['66', '69'])).
% 1.44/1.69  thf('71', plain,
% 1.44/1.69      (![X0 : $i, X1 : $i]:
% 1.44/1.69         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 1.44/1.69           = (k4_xboole_0 @ X1 @ X0))),
% 1.44/1.69      inference('demod', [status(thm)], ['39', '40'])).
% 1.44/1.69  thf('72', plain,
% 1.44/1.69      (![X0 : $i, X1 : $i]:
% 1.44/1.69         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.44/1.69      inference('demod', [status(thm)], ['34', '37'])).
% 1.44/1.69  thf('73', plain,
% 1.44/1.69      (![X0 : $i, X1 : $i]:
% 1.44/1.69         ((k2_xboole_0 @ X1 @ X0)
% 1.44/1.69           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.44/1.69      inference('sup+', [status(thm)], ['71', '72'])).
% 1.44/1.69  thf('74', plain,
% 1.44/1.69      (![X0 : $i, X1 : $i]:
% 1.44/1.69         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0))
% 1.44/1.69           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ k1_xboole_0))),
% 1.44/1.69      inference('sup+', [status(thm)], ['70', '73'])).
% 1.44/1.69  thf('75', plain,
% 1.44/1.69      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.44/1.69         ((k2_xboole_0 @ (k2_xboole_0 @ X9 @ X10) @ X11)
% 1.44/1.69           = (k2_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 1.44/1.69      inference('cnf', [status(esa)], [t4_xboole_1])).
% 1.44/1.69  thf('76', plain,
% 1.44/1.69      (![X12 : $i, X13 : $i]:
% 1.44/1.69         ((k2_xboole_0 @ X12 @ (k2_xboole_0 @ X12 @ X13))
% 1.44/1.69           = (k2_xboole_0 @ X12 @ X13))),
% 1.44/1.69      inference('cnf', [status(esa)], [t6_xboole_1])).
% 1.44/1.69  thf('77', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.44/1.69      inference('demod', [status(thm)], ['19', '20', '21'])).
% 1.44/1.69  thf('78', plain,
% 1.44/1.69      (![X0 : $i, X1 : $i]:
% 1.44/1.69         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 1.44/1.69           = (k2_xboole_0 @ X1 @ X0))),
% 1.44/1.69      inference('demod', [status(thm)], ['74', '75', '76', '77'])).
% 1.44/1.69  thf('79', plain,
% 1.44/1.69      (![X0 : $i, X1 : $i]:
% 1.44/1.69         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 1.44/1.69           = (k2_xboole_0 @ X0 @ X1))),
% 1.44/1.69      inference('sup+', [status(thm)], ['65', '78'])).
% 1.44/1.69  thf('80', plain,
% 1.44/1.69      (![X12 : $i, X13 : $i]:
% 1.44/1.69         ((k2_xboole_0 @ X12 @ (k2_xboole_0 @ X12 @ X13))
% 1.44/1.69           = (k2_xboole_0 @ X12 @ X13))),
% 1.44/1.69      inference('cnf', [status(esa)], [t6_xboole_1])).
% 1.44/1.69  thf('81', plain,
% 1.44/1.69      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.44/1.69      inference('sup+', [status(thm)], ['63', '64'])).
% 1.44/1.69  thf('82', plain,
% 1.44/1.69      (![X0 : $i, X1 : $i]:
% 1.44/1.69         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 1.44/1.69           = (k4_xboole_0 @ X1 @ X0))),
% 1.44/1.69      inference('demod', [status(thm)], ['39', '40'])).
% 1.44/1.69  thf('83', plain,
% 1.44/1.69      (![X0 : $i, X1 : $i]:
% 1.44/1.69         ((k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 1.44/1.69           = (k4_xboole_0 @ X0 @ X1))),
% 1.44/1.69      inference('sup+', [status(thm)], ['81', '82'])).
% 1.44/1.69  thf('84', plain,
% 1.44/1.69      (![X0 : $i, X1 : $i]:
% 1.44/1.69         ((k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 1.44/1.69           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1))),
% 1.44/1.69      inference('sup+', [status(thm)], ['80', '83'])).
% 1.44/1.69  thf('85', plain,
% 1.44/1.69      (![X0 : $i, X1 : $i]:
% 1.44/1.69         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 1.44/1.69           = (k4_xboole_0 @ (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)) @ X0))),
% 1.44/1.69      inference('sup+', [status(thm)], ['79', '84'])).
% 1.44/1.69  thf('86', plain,
% 1.44/1.69      (![X0 : $i, X1 : $i]:
% 1.44/1.69         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 1.44/1.69           = (k4_xboole_0 @ X1 @ X0))),
% 1.44/1.69      inference('demod', [status(thm)], ['39', '40'])).
% 1.44/1.69  thf('87', plain,
% 1.44/1.69      (![X0 : $i, X1 : $i]:
% 1.44/1.69         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 1.44/1.69           = (k2_xboole_0 @ X0 @ X1))),
% 1.44/1.69      inference('sup+', [status(thm)], ['65', '78'])).
% 1.44/1.69  thf('88', plain,
% 1.44/1.69      (![X0 : $i, X1 : $i]:
% 1.44/1.69         ((k4_xboole_0 @ X1 @ X0)
% 1.44/1.69           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 1.44/1.69      inference('demod', [status(thm)], ['85', '86', '87'])).
% 1.44/1.69  thf('89', plain,
% 1.44/1.69      (((sk_C) != (k4_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)))),
% 1.44/1.69      inference('demod', [status(thm)], ['2', '88'])).
% 1.44/1.69  thf('90', plain,
% 1.44/1.69      ((((sk_C) != (sk_C))
% 1.44/1.69        | (r2_hidden @ sk_B @ sk_C)
% 1.44/1.69        | (r2_hidden @ sk_A @ sk_C))),
% 1.44/1.69      inference('sup-', [status(thm)], ['1', '89'])).
% 1.44/1.69  thf('91', plain, (((r2_hidden @ sk_A @ sk_C) | (r2_hidden @ sk_B @ sk_C))),
% 1.44/1.69      inference('simplify', [status(thm)], ['90'])).
% 1.44/1.69  thf('92', plain, (~ (r2_hidden @ sk_A @ sk_C)),
% 1.44/1.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.69  thf('93', plain, ((r2_hidden @ sk_B @ sk_C)),
% 1.44/1.69      inference('clc', [status(thm)], ['91', '92'])).
% 1.44/1.69  thf('94', plain, ($false), inference('demod', [status(thm)], ['0', '93'])).
% 1.44/1.69  
% 1.44/1.69  % SZS output end Refutation
% 1.44/1.69  
% 1.54/1.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
