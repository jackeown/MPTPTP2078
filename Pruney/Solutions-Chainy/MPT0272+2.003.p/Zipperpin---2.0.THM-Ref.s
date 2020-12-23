%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Ptx4SlFzzC

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:26 EST 2020

% Result     : Theorem 0.57s
% Output     : Refutation 0.57s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 301 expanded)
%              Number of leaves         :   28 ( 111 expanded)
%              Depth                    :   17
%              Number of atoms          :  837 (2317 expanded)
%              Number of equality atoms :   93 ( 286 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('0',plain,(
    ! [X48: $i,X49: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X48 ) @ X49 )
      | ( r2_hidden @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t88_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
        = A ) ) )).

thf('3',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k4_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ X11 )
        = X10 )
      | ~ ( r1_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t88_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('6',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k3_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X16 @ X17 ) @ ( k2_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('8',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k3_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X16 @ X17 ) @ ( k5_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) @ ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) @ ( k1_tarski @ X1 ) ) )
        = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) @ ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) @ ( k1_tarski @ X1 ) ) ) ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','11'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('13',plain,(
    ! [X20: $i] :
      ( ( k2_tarski @ X20 @ X20 )
      = ( k1_tarski @ X20 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t31_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_tarski @ A ) )
      = A ) )).

thf('14',plain,(
    ! [X52: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X52 ) )
      = X52 ) ),
    inference(cnf,[status(esa)],[t31_zfmisc_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('16',plain,(
    ! [X50: $i,X51: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X50 @ X51 ) )
      = ( k2_xboole_0 @ X50 @ X51 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('18',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k2_xboole_0 @ X6 @ ( k2_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('19',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k3_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X16 @ X17 ) @ ( k5_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ ( k5_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('24',plain,(
    ! [X15: $i] :
      ( ( k5_xboole_0 @ X15 @ X15 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('25',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k5_xboole_0 @ X12 @ ( k5_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('28',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['21','22','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['21','22','31'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['21','22','31'])).

thf('35',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k2_xboole_0 @ X6 @ ( k2_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('37',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_tarski @ X19 @ X18 )
      = ( k2_tarski @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('38',plain,(
    ! [X50: $i,X51: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X50 @ X51 ) )
      = ( k2_xboole_0 @ X50 @ X51 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X50: $i,X51: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X50 @ X51 ) )
      = ( k2_xboole_0 @ X50 @ X51 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('43',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k3_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X16 @ X17 ) @ ( k5_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','30'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k5_xboole_0 @ X12 @ ( k5_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('48',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['26','29'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['41','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X1 )
        = ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['12','32','33','34','35','36','52'])).

thf(t69_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
      | ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
          = ( k1_tarski @ A ) )
        | ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
          = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t69_zfmisc_1])).

thf('54',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( ( k1_tarski @ sk_A )
     != ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['55'])).

thf(t52_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) )
        = ( k1_tarski @ A ) ) ) )).

thf('57',plain,(
    ! [X53: $i,X54: $i] :
      ( ( ( k3_xboole_0 @ X54 @ ( k1_tarski @ X53 ) )
        = ( k1_tarski @ X53 ) )
      | ~ ( r2_hidden @ X53 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t52_zfmisc_1])).

thf('58',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('60',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','30'])).

thf('62',plain,
    ( sk_B
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('64',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('67',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k2_xboole_0 @ X6 @ ( k2_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k3_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X16 @ X17 ) @ ( k5_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','30'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X15: $i] :
      ( ( k5_xboole_0 @ X15 @ X15 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['65','76'])).

thf('78',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['64','77'])).

thf('79',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['78','79'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Ptx4SlFzzC
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:00:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.57/0.77  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.57/0.77  % Solved by: fo/fo7.sh
% 0.57/0.77  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.57/0.77  % done 612 iterations in 0.310s
% 0.57/0.77  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.57/0.77  % SZS output start Refutation
% 0.57/0.77  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.57/0.77  thf(sk_B_type, type, sk_B: $i).
% 0.57/0.77  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.57/0.77  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.57/0.77  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.57/0.77  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.57/0.77  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.57/0.77  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.57/0.77  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.57/0.77  thf(sk_A_type, type, sk_A: $i).
% 0.57/0.77  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.57/0.77  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.57/0.77  thf(l27_zfmisc_1, axiom,
% 0.57/0.77    (![A:$i,B:$i]:
% 0.57/0.77     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.57/0.77  thf('0', plain,
% 0.57/0.77      (![X48 : $i, X49 : $i]:
% 0.57/0.77         ((r1_xboole_0 @ (k1_tarski @ X48) @ X49) | (r2_hidden @ X48 @ X49))),
% 0.57/0.77      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.57/0.77  thf(symmetry_r1_xboole_0, axiom,
% 0.57/0.77    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.57/0.77  thf('1', plain,
% 0.57/0.77      (![X2 : $i, X3 : $i]:
% 0.57/0.77         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 0.57/0.77      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.57/0.77  thf('2', plain,
% 0.57/0.77      (![X0 : $i, X1 : $i]:
% 0.57/0.77         ((r2_hidden @ X1 @ X0) | (r1_xboole_0 @ X0 @ (k1_tarski @ X1)))),
% 0.57/0.77      inference('sup-', [status(thm)], ['0', '1'])).
% 0.57/0.77  thf(t88_xboole_1, axiom,
% 0.57/0.77    (![A:$i,B:$i]:
% 0.57/0.77     ( ( r1_xboole_0 @ A @ B ) =>
% 0.57/0.77       ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( A ) ) ))).
% 0.57/0.77  thf('3', plain,
% 0.57/0.77      (![X10 : $i, X11 : $i]:
% 0.57/0.77         (((k4_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ X11) = (X10))
% 0.57/0.77          | ~ (r1_xboole_0 @ X10 @ X11))),
% 0.57/0.77      inference('cnf', [status(esa)], [t88_xboole_1])).
% 0.57/0.77  thf('4', plain,
% 0.57/0.77      (![X0 : $i, X1 : $i]:
% 0.57/0.77         ((r2_hidden @ X0 @ X1)
% 0.57/0.77          | ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0)) @ 
% 0.57/0.77              (k1_tarski @ X0)) = (X1)))),
% 0.57/0.77      inference('sup-', [status(thm)], ['2', '3'])).
% 0.57/0.77  thf(t100_xboole_1, axiom,
% 0.57/0.77    (![A:$i,B:$i]:
% 0.57/0.77     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.57/0.77  thf('5', plain,
% 0.57/0.77      (![X4 : $i, X5 : $i]:
% 0.57/0.77         ((k4_xboole_0 @ X4 @ X5)
% 0.57/0.77           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.57/0.77      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.57/0.77  thf(t95_xboole_1, axiom,
% 0.57/0.77    (![A:$i,B:$i]:
% 0.57/0.77     ( ( k3_xboole_0 @ A @ B ) =
% 0.57/0.77       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.57/0.77  thf('6', plain,
% 0.57/0.77      (![X16 : $i, X17 : $i]:
% 0.57/0.77         ((k3_xboole_0 @ X16 @ X17)
% 0.57/0.77           = (k5_xboole_0 @ (k5_xboole_0 @ X16 @ X17) @ 
% 0.57/0.77              (k2_xboole_0 @ X16 @ X17)))),
% 0.57/0.77      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.57/0.77  thf(commutativity_k5_xboole_0, axiom,
% 0.57/0.77    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.57/0.77  thf('7', plain,
% 0.57/0.77      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.57/0.77      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.57/0.77  thf('8', plain,
% 0.57/0.77      (![X16 : $i, X17 : $i]:
% 0.57/0.77         ((k3_xboole_0 @ X16 @ X17)
% 0.57/0.77           = (k5_xboole_0 @ (k2_xboole_0 @ X16 @ X17) @ 
% 0.57/0.77              (k5_xboole_0 @ X16 @ X17)))),
% 0.57/0.77      inference('demod', [status(thm)], ['6', '7'])).
% 0.57/0.77  thf('9', plain,
% 0.57/0.77      (![X0 : $i, X1 : $i]:
% 0.57/0.77         ((k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.57/0.77           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.57/0.77              (k4_xboole_0 @ X1 @ X0)))),
% 0.57/0.77      inference('sup+', [status(thm)], ['5', '8'])).
% 0.57/0.77  thf('10', plain,
% 0.57/0.77      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.57/0.77      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.57/0.77  thf('11', plain,
% 0.57/0.77      (![X0 : $i, X1 : $i]:
% 0.57/0.77         ((k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.57/0.77           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 0.57/0.77              (k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.57/0.77      inference('demod', [status(thm)], ['9', '10'])).
% 0.57/0.77  thf('12', plain,
% 0.57/0.77      (![X0 : $i, X1 : $i]:
% 0.57/0.77         (((k3_xboole_0 @ (k2_xboole_0 @ X0 @ (k1_tarski @ X1)) @ 
% 0.57/0.77            (k3_xboole_0 @ (k2_xboole_0 @ X0 @ (k1_tarski @ X1)) @ 
% 0.57/0.77             (k1_tarski @ X1)))
% 0.57/0.77            = (k5_xboole_0 @ X0 @ 
% 0.57/0.77               (k2_xboole_0 @ (k2_xboole_0 @ X0 @ (k1_tarski @ X1)) @ 
% 0.57/0.77                (k3_xboole_0 @ (k2_xboole_0 @ X0 @ (k1_tarski @ X1)) @ 
% 0.57/0.77                 (k1_tarski @ X1)))))
% 0.57/0.77          | (r2_hidden @ X1 @ X0))),
% 0.57/0.77      inference('sup+', [status(thm)], ['4', '11'])).
% 0.57/0.77  thf(t69_enumset1, axiom,
% 0.57/0.77    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.57/0.77  thf('13', plain,
% 0.57/0.77      (![X20 : $i]: ((k2_tarski @ X20 @ X20) = (k1_tarski @ X20))),
% 0.57/0.77      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.57/0.77  thf(t31_zfmisc_1, axiom,
% 0.57/0.77    (![A:$i]: ( ( k3_tarski @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.57/0.77  thf('14', plain, (![X52 : $i]: ((k3_tarski @ (k1_tarski @ X52)) = (X52))),
% 0.57/0.77      inference('cnf', [status(esa)], [t31_zfmisc_1])).
% 0.57/0.77  thf('15', plain, (![X0 : $i]: ((k3_tarski @ (k2_tarski @ X0 @ X0)) = (X0))),
% 0.57/0.77      inference('sup+', [status(thm)], ['13', '14'])).
% 0.57/0.77  thf(l51_zfmisc_1, axiom,
% 0.57/0.77    (![A:$i,B:$i]:
% 0.57/0.77     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.57/0.77  thf('16', plain,
% 0.57/0.77      (![X50 : $i, X51 : $i]:
% 0.57/0.77         ((k3_tarski @ (k2_tarski @ X50 @ X51)) = (k2_xboole_0 @ X50 @ X51))),
% 0.57/0.77      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.57/0.77  thf('17', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.57/0.77      inference('demod', [status(thm)], ['15', '16'])).
% 0.57/0.77  thf(t4_xboole_1, axiom,
% 0.57/0.77    (![A:$i,B:$i,C:$i]:
% 0.57/0.77     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 0.57/0.77       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.57/0.77  thf('18', plain,
% 0.57/0.77      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.57/0.77         ((k2_xboole_0 @ (k2_xboole_0 @ X6 @ X7) @ X8)
% 0.57/0.77           = (k2_xboole_0 @ X6 @ (k2_xboole_0 @ X7 @ X8)))),
% 0.57/0.77      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.57/0.77  thf('19', plain,
% 0.57/0.77      (![X16 : $i, X17 : $i]:
% 0.57/0.77         ((k3_xboole_0 @ X16 @ X17)
% 0.57/0.77           = (k5_xboole_0 @ (k2_xboole_0 @ X16 @ X17) @ 
% 0.57/0.77              (k5_xboole_0 @ X16 @ X17)))),
% 0.57/0.77      inference('demod', [status(thm)], ['6', '7'])).
% 0.57/0.77  thf('20', plain,
% 0.57/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.57/0.77         ((k3_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0)
% 0.57/0.77           = (k5_xboole_0 @ (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ 
% 0.57/0.77              (k5_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0)))),
% 0.57/0.77      inference('sup+', [status(thm)], ['18', '19'])).
% 0.57/0.77  thf('21', plain,
% 0.57/0.77      (![X0 : $i, X1 : $i]:
% 0.57/0.77         ((k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 0.57/0.77           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 0.57/0.77              (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)))),
% 0.57/0.77      inference('sup+', [status(thm)], ['17', '20'])).
% 0.57/0.77  thf('22', plain,
% 0.57/0.77      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.57/0.77      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.57/0.77  thf('23', plain,
% 0.57/0.77      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.57/0.77      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.57/0.77  thf(t92_xboole_1, axiom,
% 0.57/0.77    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.57/0.77  thf('24', plain, (![X15 : $i]: ((k5_xboole_0 @ X15 @ X15) = (k1_xboole_0))),
% 0.57/0.77      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.57/0.77  thf(t91_xboole_1, axiom,
% 0.57/0.77    (![A:$i,B:$i,C:$i]:
% 0.57/0.77     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.57/0.77       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.57/0.77  thf('25', plain,
% 0.57/0.77      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.57/0.77         ((k5_xboole_0 @ (k5_xboole_0 @ X12 @ X13) @ X14)
% 0.57/0.77           = (k5_xboole_0 @ X12 @ (k5_xboole_0 @ X13 @ X14)))),
% 0.57/0.77      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.57/0.77  thf('26', plain,
% 0.57/0.77      (![X0 : $i, X1 : $i]:
% 0.57/0.77         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.57/0.77           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.57/0.77      inference('sup+', [status(thm)], ['24', '25'])).
% 0.57/0.77  thf('27', plain,
% 0.57/0.77      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.57/0.77      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.57/0.77  thf(t5_boole, axiom,
% 0.57/0.77    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.57/0.77  thf('28', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.57/0.77      inference('cnf', [status(esa)], [t5_boole])).
% 0.57/0.77  thf('29', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.57/0.77      inference('sup+', [status(thm)], ['27', '28'])).
% 0.57/0.77  thf('30', plain,
% 0.57/0.77      (![X0 : $i, X1 : $i]:
% 0.57/0.77         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.57/0.77      inference('demod', [status(thm)], ['26', '29'])).
% 0.57/0.77  thf('31', plain,
% 0.57/0.77      (![X0 : $i, X1 : $i]:
% 0.57/0.77         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.57/0.77      inference('sup+', [status(thm)], ['23', '30'])).
% 0.57/0.77  thf('32', plain,
% 0.57/0.77      (![X0 : $i, X1 : $i]:
% 0.57/0.77         ((k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0) = (X0))),
% 0.57/0.77      inference('demod', [status(thm)], ['21', '22', '31'])).
% 0.57/0.77  thf('33', plain,
% 0.57/0.77      (![X0 : $i, X1 : $i]:
% 0.57/0.77         ((k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0) = (X0))),
% 0.57/0.77      inference('demod', [status(thm)], ['21', '22', '31'])).
% 0.57/0.77  thf('34', plain,
% 0.57/0.77      (![X0 : $i, X1 : $i]:
% 0.57/0.77         ((k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0) = (X0))),
% 0.57/0.77      inference('demod', [status(thm)], ['21', '22', '31'])).
% 0.57/0.77  thf('35', plain,
% 0.57/0.77      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.57/0.77         ((k2_xboole_0 @ (k2_xboole_0 @ X6 @ X7) @ X8)
% 0.57/0.77           = (k2_xboole_0 @ X6 @ (k2_xboole_0 @ X7 @ X8)))),
% 0.57/0.77      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.57/0.77  thf('36', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.57/0.77      inference('demod', [status(thm)], ['15', '16'])).
% 0.57/0.77  thf(commutativity_k2_tarski, axiom,
% 0.57/0.77    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.57/0.77  thf('37', plain,
% 0.57/0.77      (![X18 : $i, X19 : $i]:
% 0.57/0.77         ((k2_tarski @ X19 @ X18) = (k2_tarski @ X18 @ X19))),
% 0.57/0.77      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.57/0.77  thf('38', plain,
% 0.57/0.77      (![X50 : $i, X51 : $i]:
% 0.57/0.77         ((k3_tarski @ (k2_tarski @ X50 @ X51)) = (k2_xboole_0 @ X50 @ X51))),
% 0.57/0.77      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.57/0.77  thf('39', plain,
% 0.57/0.77      (![X0 : $i, X1 : $i]:
% 0.57/0.77         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.57/0.77      inference('sup+', [status(thm)], ['37', '38'])).
% 0.57/0.77  thf('40', plain,
% 0.57/0.77      (![X50 : $i, X51 : $i]:
% 0.57/0.77         ((k3_tarski @ (k2_tarski @ X50 @ X51)) = (k2_xboole_0 @ X50 @ X51))),
% 0.57/0.77      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.57/0.77  thf('41', plain,
% 0.57/0.77      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.57/0.77      inference('sup+', [status(thm)], ['39', '40'])).
% 0.57/0.77  thf('42', plain,
% 0.57/0.77      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.57/0.77      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.57/0.77  thf('43', plain,
% 0.57/0.77      (![X16 : $i, X17 : $i]:
% 0.57/0.77         ((k3_xboole_0 @ X16 @ X17)
% 0.57/0.77           = (k5_xboole_0 @ (k2_xboole_0 @ X16 @ X17) @ 
% 0.57/0.77              (k5_xboole_0 @ X16 @ X17)))),
% 0.57/0.77      inference('demod', [status(thm)], ['6', '7'])).
% 0.57/0.77  thf('44', plain,
% 0.57/0.77      (![X0 : $i, X1 : $i]:
% 0.57/0.77         ((k3_xboole_0 @ X0 @ X1)
% 0.57/0.77           = (k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k5_xboole_0 @ X1 @ X0)))),
% 0.57/0.77      inference('sup+', [status(thm)], ['42', '43'])).
% 0.57/0.77  thf('45', plain,
% 0.57/0.77      (![X0 : $i, X1 : $i]:
% 0.57/0.77         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.57/0.77      inference('sup+', [status(thm)], ['23', '30'])).
% 0.57/0.77  thf('46', plain,
% 0.57/0.77      (![X0 : $i, X1 : $i]:
% 0.57/0.77         ((k2_xboole_0 @ X1 @ X0)
% 0.57/0.77           = (k5_xboole_0 @ (k5_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X1 @ X0)))),
% 0.57/0.77      inference('sup+', [status(thm)], ['44', '45'])).
% 0.57/0.77  thf('47', plain,
% 0.57/0.77      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.57/0.77         ((k5_xboole_0 @ (k5_xboole_0 @ X12 @ X13) @ X14)
% 0.57/0.77           = (k5_xboole_0 @ X12 @ (k5_xboole_0 @ X13 @ X14)))),
% 0.57/0.77      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.57/0.77  thf('48', plain,
% 0.57/0.77      (![X4 : $i, X5 : $i]:
% 0.57/0.77         ((k4_xboole_0 @ X4 @ X5)
% 0.57/0.77           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.57/0.77      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.57/0.77  thf('49', plain,
% 0.57/0.77      (![X0 : $i, X1 : $i]:
% 0.57/0.77         ((k2_xboole_0 @ X1 @ X0)
% 0.57/0.77           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.57/0.77      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.57/0.77  thf('50', plain,
% 0.57/0.77      (![X0 : $i, X1 : $i]:
% 0.57/0.77         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.57/0.77      inference('demod', [status(thm)], ['26', '29'])).
% 0.57/0.77  thf('51', plain,
% 0.57/0.77      (![X0 : $i, X1 : $i]:
% 0.57/0.77         ((k4_xboole_0 @ X1 @ X0)
% 0.57/0.77           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.57/0.77      inference('sup+', [status(thm)], ['49', '50'])).
% 0.57/0.77  thf('52', plain,
% 0.57/0.77      (![X0 : $i, X1 : $i]:
% 0.57/0.77         ((k4_xboole_0 @ X0 @ X1)
% 0.57/0.77           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.57/0.77      inference('sup+', [status(thm)], ['41', '51'])).
% 0.57/0.77  thf('53', plain,
% 0.57/0.77      (![X0 : $i, X1 : $i]:
% 0.57/0.77         (((k1_tarski @ X1) = (k4_xboole_0 @ (k1_tarski @ X1) @ X0))
% 0.57/0.77          | (r2_hidden @ X1 @ X0))),
% 0.57/0.77      inference('demod', [status(thm)],
% 0.57/0.77                ['12', '32', '33', '34', '35', '36', '52'])).
% 0.57/0.77  thf(t69_zfmisc_1, conjecture,
% 0.57/0.77    (![A:$i,B:$i]:
% 0.57/0.77     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) | 
% 0.57/0.77       ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) ))).
% 0.57/0.77  thf(zf_stmt_0, negated_conjecture,
% 0.57/0.77    (~( ![A:$i,B:$i]:
% 0.57/0.77        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) | 
% 0.57/0.77          ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) ) )),
% 0.57/0.77    inference('cnf.neg', [status(esa)], [t69_zfmisc_1])).
% 0.57/0.77  thf('54', plain,
% 0.57/0.77      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A))),
% 0.57/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.77  thf('55', plain,
% 0.57/0.77      ((((k1_tarski @ sk_A) != (k1_tarski @ sk_A)) | (r2_hidden @ sk_A @ sk_B))),
% 0.57/0.77      inference('sup-', [status(thm)], ['53', '54'])).
% 0.57/0.77  thf('56', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.57/0.77      inference('simplify', [status(thm)], ['55'])).
% 0.57/0.77  thf(t52_zfmisc_1, axiom,
% 0.57/0.77    (![A:$i,B:$i]:
% 0.57/0.77     ( ( r2_hidden @ A @ B ) =>
% 0.57/0.77       ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) ) = ( k1_tarski @ A ) ) ))).
% 0.57/0.77  thf('57', plain,
% 0.57/0.77      (![X53 : $i, X54 : $i]:
% 0.57/0.77         (((k3_xboole_0 @ X54 @ (k1_tarski @ X53)) = (k1_tarski @ X53))
% 0.57/0.77          | ~ (r2_hidden @ X53 @ X54))),
% 0.57/0.77      inference('cnf', [status(esa)], [t52_zfmisc_1])).
% 0.57/0.77  thf('58', plain,
% 0.57/0.77      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 0.57/0.77      inference('sup-', [status(thm)], ['56', '57'])).
% 0.57/0.77  thf('59', plain,
% 0.57/0.77      (![X4 : $i, X5 : $i]:
% 0.57/0.77         ((k4_xboole_0 @ X4 @ X5)
% 0.57/0.77           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.57/0.77      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.57/0.77  thf('60', plain,
% 0.57/0.77      (((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.57/0.77         = (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.57/0.77      inference('sup+', [status(thm)], ['58', '59'])).
% 0.57/0.77  thf('61', plain,
% 0.57/0.77      (![X0 : $i, X1 : $i]:
% 0.57/0.77         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.57/0.77      inference('sup+', [status(thm)], ['23', '30'])).
% 0.57/0.77  thf('62', plain,
% 0.57/0.77      (((sk_B)
% 0.57/0.77         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.57/0.77            (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))),
% 0.57/0.77      inference('sup+', [status(thm)], ['60', '61'])).
% 0.57/0.77  thf('63', plain,
% 0.57/0.77      (![X0 : $i, X1 : $i]:
% 0.57/0.77         ((k2_xboole_0 @ X1 @ X0)
% 0.57/0.77           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.57/0.77      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.57/0.77  thf('64', plain, (((sk_B) = (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.57/0.77      inference('demod', [status(thm)], ['62', '63'])).
% 0.57/0.77  thf('65', plain,
% 0.57/0.77      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.57/0.77      inference('sup+', [status(thm)], ['39', '40'])).
% 0.57/0.77  thf('66', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.57/0.77      inference('demod', [status(thm)], ['15', '16'])).
% 0.57/0.77  thf('67', plain,
% 0.57/0.77      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.57/0.77         ((k2_xboole_0 @ (k2_xboole_0 @ X6 @ X7) @ X8)
% 0.57/0.77           = (k2_xboole_0 @ X6 @ (k2_xboole_0 @ X7 @ X8)))),
% 0.57/0.77      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.57/0.77  thf('68', plain,
% 0.57/0.77      (![X0 : $i, X1 : $i]:
% 0.57/0.77         ((k2_xboole_0 @ X0 @ X1)
% 0.57/0.77           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 0.57/0.77      inference('sup+', [status(thm)], ['66', '67'])).
% 0.57/0.77  thf('69', plain,
% 0.57/0.77      (![X16 : $i, X17 : $i]:
% 0.57/0.77         ((k3_xboole_0 @ X16 @ X17)
% 0.57/0.77           = (k5_xboole_0 @ (k2_xboole_0 @ X16 @ X17) @ 
% 0.57/0.77              (k5_xboole_0 @ X16 @ X17)))),
% 0.57/0.77      inference('demod', [status(thm)], ['6', '7'])).
% 0.57/0.77  thf('70', plain,
% 0.57/0.77      (![X0 : $i, X1 : $i]:
% 0.57/0.77         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 0.57/0.77           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 0.57/0.77              (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))))),
% 0.57/0.77      inference('sup+', [status(thm)], ['68', '69'])).
% 0.57/0.77  thf('71', plain,
% 0.57/0.77      (![X0 : $i, X1 : $i]:
% 0.57/0.77         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.57/0.77      inference('sup+', [status(thm)], ['23', '30'])).
% 0.57/0.77  thf('72', plain,
% 0.57/0.77      (![X0 : $i, X1 : $i]:
% 0.57/0.77         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (X1))),
% 0.57/0.77      inference('demod', [status(thm)], ['70', '71'])).
% 0.57/0.77  thf('73', plain,
% 0.57/0.77      (![X4 : $i, X5 : $i]:
% 0.57/0.77         ((k4_xboole_0 @ X4 @ X5)
% 0.57/0.77           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.57/0.77      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.57/0.77  thf('74', plain,
% 0.57/0.77      (![X0 : $i, X1 : $i]:
% 0.57/0.77         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 0.57/0.77           = (k5_xboole_0 @ X0 @ X0))),
% 0.57/0.77      inference('sup+', [status(thm)], ['72', '73'])).
% 0.57/0.77  thf('75', plain, (![X15 : $i]: ((k5_xboole_0 @ X15 @ X15) = (k1_xboole_0))),
% 0.57/0.77      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.57/0.77  thf('76', plain,
% 0.57/0.77      (![X0 : $i, X1 : $i]:
% 0.57/0.77         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 0.57/0.77      inference('demod', [status(thm)], ['74', '75'])).
% 0.57/0.77  thf('77', plain,
% 0.57/0.77      (![X0 : $i, X1 : $i]:
% 0.57/0.77         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.57/0.77      inference('sup+', [status(thm)], ['65', '76'])).
% 0.57/0.77  thf('78', plain,
% 0.57/0.77      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.57/0.77      inference('sup+', [status(thm)], ['64', '77'])).
% 0.57/0.77  thf('79', plain,
% 0.57/0.77      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_xboole_0))),
% 0.57/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.77  thf('80', plain, ($false),
% 0.57/0.77      inference('simplify_reflect-', [status(thm)], ['78', '79'])).
% 0.57/0.77  
% 0.57/0.77  % SZS output end Refutation
% 0.57/0.77  
% 0.57/0.78  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
