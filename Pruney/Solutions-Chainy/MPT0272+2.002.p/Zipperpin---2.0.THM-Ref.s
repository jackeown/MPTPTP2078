%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1p1YifhmfH

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:26 EST 2020

% Result     : Theorem 0.53s
% Output     : Refutation 0.53s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 337 expanded)
%              Number of leaves         :   26 ( 123 expanded)
%              Depth                    :   21
%              Number of atoms          :  709 (2619 expanded)
%              Number of equality atoms :   82 ( 325 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('0',plain,(
    ! [X49: $i,X50: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X49 ) @ X50 )
      | ( r2_hidden @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(t88_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
        = A ) ) )).

thf('1',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k4_xboole_0 @ ( k2_xboole_0 @ X11 @ X12 ) @ X12 )
        = X11 )
      | ~ ( r1_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t88_xboole_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) @ X0 )
        = ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X17 @ X18 ) @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('6',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X17 @ X18 ) @ ( k5_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','6'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('8',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('11',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_tarski @ X20 @ X19 )
      = ( k2_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('12',plain,(
    ! [X53: $i,X54: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X53 @ X54 ) )
      = ( k2_xboole_0 @ X53 @ X54 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X53: $i,X54: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X53 @ X54 ) )
      = ( k2_xboole_0 @ X53 @ X54 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','6'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('18',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ X16 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('19',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('22',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','25'])).

thf('27',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('28',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['20','23'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','10','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
        = ( k5_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('36',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('37',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X7 @ X8 ) @ X9 )
      = ( k2_xboole_0 @ X7 @ ( k2_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X17 @ X18 ) @ ( k5_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','24'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['35','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','31'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['34','43','44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','10','32'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = ( k5_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ X16 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = ( k5_xboole_0 @ ( k1_tarski @ X1 ) @ k1_xboole_0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = ( k1_tarski @ X1 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['52','53','54'])).

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

thf('56',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( ( k1_tarski @ sk_A )
     != ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['57'])).

thf(l31_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) )
        = ( k1_tarski @ A ) ) ) )).

thf('59',plain,(
    ! [X51: $i,X52: $i] :
      ( ( ( k3_xboole_0 @ X52 @ ( k1_tarski @ X51 ) )
        = ( k1_tarski @ X51 ) )
      | ~ ( r2_hidden @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[l31_zfmisc_1])).

thf('60',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','10','32'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['20','23'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['60','63'])).

thf('65',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ X16 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('66',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['66','67'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1p1YifhmfH
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:32:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.53/0.76  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.53/0.76  % Solved by: fo/fo7.sh
% 0.53/0.76  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.53/0.76  % done 496 iterations in 0.303s
% 0.53/0.76  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.53/0.76  % SZS output start Refutation
% 0.53/0.76  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.53/0.76  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.53/0.76  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.53/0.76  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.53/0.76  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.53/0.76  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.53/0.76  thf(sk_A_type, type, sk_A: $i).
% 0.53/0.76  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.53/0.76  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.53/0.76  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.53/0.76  thf(sk_B_type, type, sk_B: $i).
% 0.53/0.76  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.53/0.76  thf(l27_zfmisc_1, axiom,
% 0.53/0.76    (![A:$i,B:$i]:
% 0.53/0.76     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.53/0.76  thf('0', plain,
% 0.53/0.76      (![X49 : $i, X50 : $i]:
% 0.53/0.76         ((r1_xboole_0 @ (k1_tarski @ X49) @ X50) | (r2_hidden @ X49 @ X50))),
% 0.53/0.76      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.53/0.76  thf(t88_xboole_1, axiom,
% 0.53/0.76    (![A:$i,B:$i]:
% 0.53/0.76     ( ( r1_xboole_0 @ A @ B ) =>
% 0.53/0.76       ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( A ) ) ))).
% 0.53/0.76  thf('1', plain,
% 0.53/0.76      (![X11 : $i, X12 : $i]:
% 0.53/0.76         (((k4_xboole_0 @ (k2_xboole_0 @ X11 @ X12) @ X12) = (X11))
% 0.53/0.76          | ~ (r1_xboole_0 @ X11 @ X12))),
% 0.53/0.76      inference('cnf', [status(esa)], [t88_xboole_1])).
% 0.53/0.76  thf('2', plain,
% 0.53/0.76      (![X0 : $i, X1 : $i]:
% 0.53/0.76         ((r2_hidden @ X1 @ X0)
% 0.53/0.76          | ((k4_xboole_0 @ (k2_xboole_0 @ (k1_tarski @ X1) @ X0) @ X0)
% 0.53/0.76              = (k1_tarski @ X1)))),
% 0.53/0.76      inference('sup-', [status(thm)], ['0', '1'])).
% 0.53/0.76  thf(commutativity_k5_xboole_0, axiom,
% 0.53/0.76    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.53/0.76  thf('3', plain,
% 0.53/0.76      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.53/0.76      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.53/0.76  thf(t95_xboole_1, axiom,
% 0.53/0.76    (![A:$i,B:$i]:
% 0.53/0.76     ( ( k3_xboole_0 @ A @ B ) =
% 0.53/0.76       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.53/0.76  thf('4', plain,
% 0.53/0.76      (![X17 : $i, X18 : $i]:
% 0.53/0.76         ((k3_xboole_0 @ X17 @ X18)
% 0.53/0.76           = (k5_xboole_0 @ (k5_xboole_0 @ X17 @ X18) @ 
% 0.53/0.76              (k2_xboole_0 @ X17 @ X18)))),
% 0.53/0.76      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.53/0.76  thf('5', plain,
% 0.53/0.76      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.53/0.76      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.53/0.76  thf('6', plain,
% 0.53/0.76      (![X17 : $i, X18 : $i]:
% 0.53/0.76         ((k3_xboole_0 @ X17 @ X18)
% 0.53/0.76           = (k5_xboole_0 @ (k2_xboole_0 @ X17 @ X18) @ 
% 0.53/0.76              (k5_xboole_0 @ X17 @ X18)))),
% 0.53/0.76      inference('demod', [status(thm)], ['4', '5'])).
% 0.53/0.76  thf('7', plain,
% 0.53/0.76      (![X0 : $i, X1 : $i]:
% 0.53/0.76         ((k3_xboole_0 @ X0 @ X1)
% 0.53/0.76           = (k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k5_xboole_0 @ X1 @ X0)))),
% 0.53/0.76      inference('sup+', [status(thm)], ['3', '6'])).
% 0.53/0.76  thf(t91_xboole_1, axiom,
% 0.53/0.76    (![A:$i,B:$i,C:$i]:
% 0.53/0.76     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.53/0.76       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.53/0.76  thf('8', plain,
% 0.53/0.76      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.53/0.76         ((k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15)
% 0.53/0.76           = (k5_xboole_0 @ X13 @ (k5_xboole_0 @ X14 @ X15)))),
% 0.53/0.76      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.53/0.76  thf('9', plain,
% 0.53/0.76      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.53/0.76      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.53/0.76  thf('10', plain,
% 0.53/0.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.76         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 0.53/0.76           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.53/0.76      inference('sup+', [status(thm)], ['8', '9'])).
% 0.53/0.76  thf(commutativity_k2_tarski, axiom,
% 0.53/0.76    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.53/0.76  thf('11', plain,
% 0.53/0.76      (![X19 : $i, X20 : $i]:
% 0.53/0.76         ((k2_tarski @ X20 @ X19) = (k2_tarski @ X19 @ X20))),
% 0.53/0.76      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.53/0.76  thf(l51_zfmisc_1, axiom,
% 0.53/0.76    (![A:$i,B:$i]:
% 0.53/0.76     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.53/0.76  thf('12', plain,
% 0.53/0.76      (![X53 : $i, X54 : $i]:
% 0.53/0.76         ((k3_tarski @ (k2_tarski @ X53 @ X54)) = (k2_xboole_0 @ X53 @ X54))),
% 0.53/0.76      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.53/0.76  thf('13', plain,
% 0.53/0.76      (![X0 : $i, X1 : $i]:
% 0.53/0.76         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.53/0.76      inference('sup+', [status(thm)], ['11', '12'])).
% 0.53/0.76  thf('14', plain,
% 0.53/0.76      (![X53 : $i, X54 : $i]:
% 0.53/0.76         ((k3_tarski @ (k2_tarski @ X53 @ X54)) = (k2_xboole_0 @ X53 @ X54))),
% 0.53/0.76      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.53/0.76  thf('15', plain,
% 0.53/0.76      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.53/0.76      inference('sup+', [status(thm)], ['13', '14'])).
% 0.53/0.76  thf('16', plain,
% 0.53/0.76      (![X0 : $i, X1 : $i]:
% 0.53/0.76         ((k3_xboole_0 @ X0 @ X1)
% 0.53/0.76           = (k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k5_xboole_0 @ X1 @ X0)))),
% 0.53/0.76      inference('sup+', [status(thm)], ['3', '6'])).
% 0.53/0.76  thf('17', plain,
% 0.53/0.76      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.53/0.76      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.53/0.76  thf(t92_xboole_1, axiom,
% 0.53/0.76    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.53/0.76  thf('18', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ X16) = (k1_xboole_0))),
% 0.53/0.76      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.53/0.76  thf('19', plain,
% 0.53/0.76      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.53/0.76         ((k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15)
% 0.53/0.76           = (k5_xboole_0 @ X13 @ (k5_xboole_0 @ X14 @ X15)))),
% 0.53/0.76      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.53/0.76  thf('20', plain,
% 0.53/0.76      (![X0 : $i, X1 : $i]:
% 0.53/0.76         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.53/0.76           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.53/0.76      inference('sup+', [status(thm)], ['18', '19'])).
% 0.53/0.76  thf('21', plain,
% 0.53/0.76      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.53/0.76      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.53/0.76  thf(t5_boole, axiom,
% 0.53/0.76    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.53/0.76  thf('22', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.53/0.76      inference('cnf', [status(esa)], [t5_boole])).
% 0.53/0.76  thf('23', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.53/0.76      inference('sup+', [status(thm)], ['21', '22'])).
% 0.53/0.76  thf('24', plain,
% 0.53/0.76      (![X0 : $i, X1 : $i]:
% 0.53/0.76         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.53/0.76      inference('demod', [status(thm)], ['20', '23'])).
% 0.53/0.76  thf('25', plain,
% 0.53/0.76      (![X0 : $i, X1 : $i]:
% 0.53/0.76         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.53/0.76      inference('sup+', [status(thm)], ['17', '24'])).
% 0.53/0.76  thf('26', plain,
% 0.53/0.76      (![X0 : $i, X1 : $i]:
% 0.53/0.76         ((k2_xboole_0 @ X1 @ X0)
% 0.53/0.76           = (k5_xboole_0 @ (k5_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X1 @ X0)))),
% 0.53/0.76      inference('sup+', [status(thm)], ['16', '25'])).
% 0.53/0.76  thf('27', plain,
% 0.53/0.76      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.53/0.76         ((k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15)
% 0.53/0.76           = (k5_xboole_0 @ X13 @ (k5_xboole_0 @ X14 @ X15)))),
% 0.53/0.76      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.53/0.76  thf(t100_xboole_1, axiom,
% 0.53/0.76    (![A:$i,B:$i]:
% 0.53/0.76     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.53/0.76  thf('28', plain,
% 0.53/0.76      (![X5 : $i, X6 : $i]:
% 0.53/0.76         ((k4_xboole_0 @ X5 @ X6)
% 0.53/0.76           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.53/0.76      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.53/0.76  thf('29', plain,
% 0.53/0.76      (![X0 : $i, X1 : $i]:
% 0.53/0.76         ((k2_xboole_0 @ X1 @ X0)
% 0.53/0.76           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.53/0.76      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.53/0.76  thf('30', plain,
% 0.53/0.76      (![X0 : $i, X1 : $i]:
% 0.53/0.76         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.53/0.76      inference('demod', [status(thm)], ['20', '23'])).
% 0.53/0.76  thf('31', plain,
% 0.53/0.76      (![X0 : $i, X1 : $i]:
% 0.53/0.76         ((k4_xboole_0 @ X1 @ X0)
% 0.53/0.76           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.53/0.76      inference('sup+', [status(thm)], ['29', '30'])).
% 0.53/0.76  thf('32', plain,
% 0.53/0.76      (![X0 : $i, X1 : $i]:
% 0.53/0.76         ((k4_xboole_0 @ X0 @ X1)
% 0.53/0.76           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.53/0.76      inference('sup+', [status(thm)], ['15', '31'])).
% 0.53/0.76  thf('33', plain,
% 0.53/0.76      (![X0 : $i, X1 : $i]:
% 0.53/0.76         ((k3_xboole_0 @ X0 @ X1)
% 0.53/0.76           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.53/0.76      inference('demod', [status(thm)], ['7', '10', '32'])).
% 0.53/0.76  thf('34', plain,
% 0.53/0.76      (![X0 : $i, X1 : $i]:
% 0.53/0.76         (((k3_xboole_0 @ X1 @ (k2_xboole_0 @ (k1_tarski @ X0) @ X1))
% 0.53/0.76            = (k5_xboole_0 @ (k2_xboole_0 @ (k1_tarski @ X0) @ X1) @ 
% 0.53/0.76               (k1_tarski @ X0)))
% 0.53/0.76          | (r2_hidden @ X0 @ X1))),
% 0.53/0.76      inference('sup+', [status(thm)], ['2', '33'])).
% 0.53/0.76  thf('35', plain,
% 0.53/0.76      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.53/0.76      inference('sup+', [status(thm)], ['13', '14'])).
% 0.53/0.76  thf(idempotence_k2_xboole_0, axiom,
% 0.53/0.76    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.53/0.76  thf('36', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ X2) = (X2))),
% 0.53/0.76      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.53/0.76  thf(t4_xboole_1, axiom,
% 0.53/0.76    (![A:$i,B:$i,C:$i]:
% 0.53/0.76     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 0.53/0.76       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.53/0.76  thf('37', plain,
% 0.53/0.76      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.53/0.76         ((k2_xboole_0 @ (k2_xboole_0 @ X7 @ X8) @ X9)
% 0.53/0.76           = (k2_xboole_0 @ X7 @ (k2_xboole_0 @ X8 @ X9)))),
% 0.53/0.76      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.53/0.76  thf('38', plain,
% 0.53/0.76      (![X0 : $i, X1 : $i]:
% 0.53/0.76         ((k2_xboole_0 @ X0 @ X1)
% 0.53/0.76           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 0.53/0.76      inference('sup+', [status(thm)], ['36', '37'])).
% 0.53/0.76  thf('39', plain,
% 0.53/0.76      (![X17 : $i, X18 : $i]:
% 0.53/0.76         ((k3_xboole_0 @ X17 @ X18)
% 0.53/0.76           = (k5_xboole_0 @ (k2_xboole_0 @ X17 @ X18) @ 
% 0.53/0.76              (k5_xboole_0 @ X17 @ X18)))),
% 0.53/0.76      inference('demod', [status(thm)], ['4', '5'])).
% 0.53/0.76  thf('40', plain,
% 0.53/0.76      (![X0 : $i, X1 : $i]:
% 0.53/0.76         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 0.53/0.76           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 0.53/0.76              (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))))),
% 0.53/0.76      inference('sup+', [status(thm)], ['38', '39'])).
% 0.53/0.76  thf('41', plain,
% 0.53/0.76      (![X0 : $i, X1 : $i]:
% 0.53/0.76         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.53/0.76      inference('sup+', [status(thm)], ['17', '24'])).
% 0.53/0.76  thf('42', plain,
% 0.53/0.76      (![X0 : $i, X1 : $i]:
% 0.53/0.76         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (X1))),
% 0.53/0.76      inference('demod', [status(thm)], ['40', '41'])).
% 0.53/0.76  thf('43', plain,
% 0.53/0.76      (![X0 : $i, X1 : $i]:
% 0.53/0.76         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (X0))),
% 0.53/0.76      inference('sup+', [status(thm)], ['35', '42'])).
% 0.53/0.76  thf('44', plain,
% 0.53/0.76      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.53/0.76      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.53/0.76  thf('45', plain,
% 0.53/0.76      (![X0 : $i, X1 : $i]:
% 0.53/0.76         ((k4_xboole_0 @ X0 @ X1)
% 0.53/0.76           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.53/0.76      inference('sup+', [status(thm)], ['15', '31'])).
% 0.53/0.76  thf('46', plain,
% 0.53/0.76      (![X0 : $i, X1 : $i]:
% 0.53/0.76         (((X1) = (k4_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 0.53/0.76          | (r2_hidden @ X0 @ X1))),
% 0.53/0.76      inference('demod', [status(thm)], ['34', '43', '44', '45'])).
% 0.53/0.76  thf('47', plain,
% 0.53/0.76      (![X0 : $i, X1 : $i]:
% 0.53/0.76         ((k3_xboole_0 @ X0 @ X1)
% 0.53/0.76           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.53/0.76      inference('demod', [status(thm)], ['7', '10', '32'])).
% 0.53/0.76  thf('48', plain,
% 0.53/0.76      (![X0 : $i, X1 : $i]:
% 0.53/0.76         (((k3_xboole_0 @ (k1_tarski @ X1) @ X0) = (k5_xboole_0 @ X0 @ X0))
% 0.53/0.76          | (r2_hidden @ X1 @ X0))),
% 0.53/0.76      inference('sup+', [status(thm)], ['46', '47'])).
% 0.53/0.76  thf('49', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ X16) = (k1_xboole_0))),
% 0.53/0.76      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.53/0.76  thf('50', plain,
% 0.53/0.76      (![X0 : $i, X1 : $i]:
% 0.53/0.76         (((k3_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_xboole_0))
% 0.53/0.76          | (r2_hidden @ X1 @ X0))),
% 0.53/0.76      inference('demod', [status(thm)], ['48', '49'])).
% 0.53/0.76  thf('51', plain,
% 0.53/0.76      (![X5 : $i, X6 : $i]:
% 0.53/0.76         ((k4_xboole_0 @ X5 @ X6)
% 0.53/0.76           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.53/0.76      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.53/0.76  thf('52', plain,
% 0.53/0.76      (![X0 : $i, X1 : $i]:
% 0.53/0.76         (((k4_xboole_0 @ (k1_tarski @ X1) @ X0)
% 0.53/0.76            = (k5_xboole_0 @ (k1_tarski @ X1) @ k1_xboole_0))
% 0.53/0.76          | (r2_hidden @ X1 @ X0))),
% 0.53/0.76      inference('sup+', [status(thm)], ['50', '51'])).
% 0.53/0.76  thf('53', plain,
% 0.53/0.76      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.53/0.76      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.53/0.76  thf('54', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.53/0.76      inference('sup+', [status(thm)], ['21', '22'])).
% 0.53/0.76  thf('55', plain,
% 0.53/0.76      (![X0 : $i, X1 : $i]:
% 0.53/0.76         (((k4_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_tarski @ X1))
% 0.53/0.76          | (r2_hidden @ X1 @ X0))),
% 0.53/0.76      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.53/0.76  thf(t69_zfmisc_1, conjecture,
% 0.53/0.76    (![A:$i,B:$i]:
% 0.53/0.76     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) | 
% 0.53/0.76       ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) ))).
% 0.53/0.76  thf(zf_stmt_0, negated_conjecture,
% 0.53/0.76    (~( ![A:$i,B:$i]:
% 0.53/0.76        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) | 
% 0.53/0.76          ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) ) )),
% 0.53/0.76    inference('cnf.neg', [status(esa)], [t69_zfmisc_1])).
% 0.53/0.76  thf('56', plain,
% 0.53/0.76      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A))),
% 0.53/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.76  thf('57', plain,
% 0.53/0.76      ((((k1_tarski @ sk_A) != (k1_tarski @ sk_A)) | (r2_hidden @ sk_A @ sk_B))),
% 0.53/0.76      inference('sup-', [status(thm)], ['55', '56'])).
% 0.53/0.76  thf('58', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.53/0.76      inference('simplify', [status(thm)], ['57'])).
% 0.53/0.76  thf(l31_zfmisc_1, axiom,
% 0.53/0.76    (![A:$i,B:$i]:
% 0.53/0.76     ( ( r2_hidden @ A @ B ) =>
% 0.53/0.76       ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) ) = ( k1_tarski @ A ) ) ))).
% 0.53/0.76  thf('59', plain,
% 0.53/0.76      (![X51 : $i, X52 : $i]:
% 0.53/0.76         (((k3_xboole_0 @ X52 @ (k1_tarski @ X51)) = (k1_tarski @ X51))
% 0.53/0.76          | ~ (r2_hidden @ X51 @ X52))),
% 0.53/0.76      inference('cnf', [status(esa)], [l31_zfmisc_1])).
% 0.53/0.76  thf('60', plain,
% 0.53/0.76      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 0.53/0.76      inference('sup-', [status(thm)], ['58', '59'])).
% 0.53/0.76  thf('61', plain,
% 0.53/0.76      (![X0 : $i, X1 : $i]:
% 0.53/0.76         ((k3_xboole_0 @ X0 @ X1)
% 0.53/0.76           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.53/0.76      inference('demod', [status(thm)], ['7', '10', '32'])).
% 0.53/0.76  thf('62', plain,
% 0.53/0.76      (![X0 : $i, X1 : $i]:
% 0.53/0.76         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.53/0.76      inference('demod', [status(thm)], ['20', '23'])).
% 0.53/0.76  thf('63', plain,
% 0.53/0.76      (![X0 : $i, X1 : $i]:
% 0.53/0.76         ((k4_xboole_0 @ X0 @ X1)
% 0.53/0.76           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.53/0.76      inference('sup+', [status(thm)], ['61', '62'])).
% 0.53/0.76  thf('64', plain,
% 0.53/0.76      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.53/0.76         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.53/0.76      inference('sup+', [status(thm)], ['60', '63'])).
% 0.53/0.76  thf('65', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ X16) = (k1_xboole_0))),
% 0.53/0.76      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.53/0.76  thf('66', plain,
% 0.53/0.76      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.53/0.76      inference('demod', [status(thm)], ['64', '65'])).
% 0.53/0.76  thf('67', plain,
% 0.53/0.76      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_xboole_0))),
% 0.53/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.76  thf('68', plain, ($false),
% 0.53/0.76      inference('simplify_reflect-', [status(thm)], ['66', '67'])).
% 0.53/0.76  
% 0.53/0.76  % SZS output end Refutation
% 0.53/0.76  
% 0.53/0.77  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
