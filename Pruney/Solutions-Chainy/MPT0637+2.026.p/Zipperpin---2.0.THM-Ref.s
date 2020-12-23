%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.oTUBqf6xey

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:59 EST 2020

% Result     : Theorem 0.85s
% Output     : Refutation 0.85s
% Verified   : 
% Statistics : Number of formulae       :  167 ( 662 expanded)
%              Number of leaves         :   26 ( 229 expanded)
%              Depth                    :   20
%              Number of atoms          : 1550 (5575 expanded)
%              Number of equality atoms :  101 ( 437 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('0',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k7_relat_1 @ X31 @ X30 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X30 ) @ X31 ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t43_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
        = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t43_funct_1])).

thf('1',plain,(
    ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k6_relat_1 @ sk_A ) )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
     != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('3',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('4',plain,(
    ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('5',plain,(
    ! [X22: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X22 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t98_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = A ) ) )).

thf('6',plain,(
    ! [X32: $i] :
      ( ( ( k7_relat_1 @ X32 @ ( k1_relat_1 @ X32 ) )
        = X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t98_relat_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(t100_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('10',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X14 @ X15 ) @ X16 )
        = ( k7_relat_1 @ X14 @ ( k3_xboole_0 @ X15 @ X16 ) ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('11',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k7_relat_1 @ X31 @ X30 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X30 ) @ X31 ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t76_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B )
        & ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ) )).

thf('12',plain,(
    ! [X24: $i,X25: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ X25 ) @ X24 ) @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t76_relat_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k7_relat_1 @ X1 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k3_xboole_0 @ ( k7_relat_1 @ X0 @ X1 ) @ X0 )
        = ( k7_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('17',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_tarski @ X3 @ X2 )
      = ( k2_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('18',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k3_xboole_0 @ X0 @ ( k7_relat_1 @ X0 @ X1 ) )
        = ( k7_relat_1 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['16','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ ( k7_relat_1 @ X2 @ X1 ) @ ( k7_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
        = ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['10','22'])).

thf('24',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k7_relat_1 @ X31 @ X30 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X30 ) @ X31 ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('25',plain,(
    ! [X24: $i,X25: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ X25 ) @ X24 ) @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t76_relat_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k3_xboole_0 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X0 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k3_xboole_0 @ X0 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf(fc1_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('30',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[fc1_relat_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['24','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k3_xboole_0 @ ( k7_relat_1 @ X2 @ X1 ) @ ( k7_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
        = ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference(clc,[status(thm)],['23','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k7_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X1 ) @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
        = ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['9','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('39',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X14 @ X15 ) @ X16 )
        = ( k7_relat_1 @ X14 @ ( k3_xboole_0 @ X15 @ X16 ) ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k3_xboole_0 @ X0 @ ( k7_relat_1 @ X0 @ X1 ) )
        = ( k7_relat_1 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['16','21'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k6_relat_1 @ X1 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
        = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('46',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k6_relat_1 @ X1 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('49',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X14 @ X15 ) @ X16 )
        = ( k7_relat_1 @ X14 @ ( k3_xboole_0 @ X15 @ X16 ) ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('50',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X14 @ X15 ) @ X16 )
        = ( k7_relat_1 @ X14 @ ( k3_xboole_0 @ X15 @ X16 ) ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X3 )
        = ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ ( k3_xboole_0 @ X0 @ X3 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X3 )
        = ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ ( k3_xboole_0 @ X0 @ X3 ) ) ) ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X2 )
        = ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X1 ) @ ( k3_xboole_0 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['48','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('56',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X2 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k3_xboole_0 @ X0 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('59',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X1 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['36','37','47','57','58','59'])).

thf('61',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k7_relat_1 @ X31 @ X30 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X30 ) @ X31 ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('62',plain,(
    ! [X24: $i,X25: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X24 @ ( k6_relat_1 @ X25 ) ) @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t76_relat_1])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('63',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ( r1_tarski @ ( k2_relat_1 @ X18 ) @ ( k2_relat_1 @ X17 ) )
      | ~ ( r1_tarski @ X18 @ X17 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ! [X24: $i,X25: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X24 @ ( k6_relat_1 @ X25 ) ) @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t76_relat_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k3_xboole_0 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) @ X0 )
        = ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k3_xboole_0 @ X0 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
        = ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[fc1_relat_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['65','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['61','74'])).

thf('76',plain,(
    ! [X23: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('77',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('78',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['75','76','77','78'])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('80',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X28 ) @ X29 )
      | ( ( k5_relat_1 @ X28 @ ( k6_relat_1 @ X29 ) )
        = X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k6_relat_1 @ X0 ) )
        = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k7_relat_1 @ X31 @ X30 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X30 ) @ X31 ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('86',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['84','85','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['81','87'])).

thf('89',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k7_relat_1 @ X31 @ X30 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X30 ) @ X31 ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k3_xboole_0 @ X0 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k3_xboole_0 @ X1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k6_relat_1 @ X1 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
        = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k7_relat_1 @ X31 @ X30 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X30 ) @ X31 ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('98',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X20 @ X19 ) @ X21 )
        = ( k5_relat_1 @ X20 @ ( k5_relat_1 @ X19 @ X21 ) ) )
      | ~ ( v1_relat_1 @ X21 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('99',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('101',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ ( k6_relat_1 @ X1 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['96','102'])).

thf('104',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('105',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('106',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ ( k6_relat_1 @ X1 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['103','104','105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k7_relat_1 @ X1 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k6_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ( r1_tarski @ ( k2_relat_1 @ X18 ) @ ( k2_relat_1 @ X17 ) )
      | ~ ( r1_tarski @ X18 @ X17 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['84','85','86'])).

thf('115',plain,(
    ! [X23: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('116',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['113','114','115','116'])).

thf('118',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X28 ) @ X29 )
      | ( ( k5_relat_1 @ X28 @ ( k6_relat_1 @ X29 ) )
        = X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ ( k6_relat_1 @ X0 ) )
        = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['84','85','86'])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ ( k6_relat_1 @ X0 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['101'])).

thf('123',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X2 ) @ ( k6_relat_1 @ X1 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X2 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k3_xboole_0 @ X0 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ ( k6_relat_1 @ X0 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['84','85','86'])).

thf('127',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('128',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k3_xboole_0 @ X0 @ X2 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['123','124','125','126','127'])).

thf('129',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ ( k6_relat_1 @ X1 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k3_xboole_0 @ X0 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['106','128'])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['88','129'])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['130','133'])).

thf('135',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['60','134'])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['135','136'])).

thf('138',plain,(
    ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','137'])).

thf('139',plain,(
    $false ),
    inference(simplify,[status(thm)],['138'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.oTUBqf6xey
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:27:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.85/1.03  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.85/1.03  % Solved by: fo/fo7.sh
% 0.85/1.03  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.85/1.03  % done 732 iterations in 0.577s
% 0.85/1.03  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.85/1.03  % SZS output start Refutation
% 0.85/1.03  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.85/1.03  thf(sk_B_type, type, sk_B: $i).
% 0.85/1.03  thf(sk_A_type, type, sk_A: $i).
% 0.85/1.03  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.85/1.03  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.85/1.03  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.85/1.03  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.85/1.03  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.85/1.03  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.85/1.03  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.85/1.03  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.85/1.03  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.85/1.03  thf(t94_relat_1, axiom,
% 0.85/1.03    (![A:$i,B:$i]:
% 0.85/1.03     ( ( v1_relat_1 @ B ) =>
% 0.85/1.03       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.85/1.03  thf('0', plain,
% 0.85/1.03      (![X30 : $i, X31 : $i]:
% 0.85/1.03         (((k7_relat_1 @ X31 @ X30) = (k5_relat_1 @ (k6_relat_1 @ X30) @ X31))
% 0.85/1.03          | ~ (v1_relat_1 @ X31))),
% 0.85/1.03      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.85/1.03  thf(t43_funct_1, conjecture,
% 0.85/1.03    (![A:$i,B:$i]:
% 0.85/1.03     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.85/1.03       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.85/1.03  thf(zf_stmt_0, negated_conjecture,
% 0.85/1.03    (~( ![A:$i,B:$i]:
% 0.85/1.03        ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.85/1.03          ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 0.85/1.03    inference('cnf.neg', [status(esa)], [t43_funct_1])).
% 0.85/1.03  thf('1', plain,
% 0.85/1.03      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A))
% 0.85/1.03         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.85/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.03  thf('2', plain,
% 0.85/1.03      ((((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 0.85/1.03          != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))
% 0.85/1.03        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A)))),
% 0.85/1.03      inference('sup-', [status(thm)], ['0', '1'])).
% 0.85/1.03  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.85/1.03  thf('3', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.85/1.03      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.85/1.03  thf('4', plain,
% 0.85/1.03      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 0.85/1.03         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.85/1.03      inference('demod', [status(thm)], ['2', '3'])).
% 0.85/1.03  thf(t71_relat_1, axiom,
% 0.85/1.03    (![A:$i]:
% 0.85/1.03     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.85/1.03       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.85/1.03  thf('5', plain, (![X22 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X22)) = (X22))),
% 0.85/1.03      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.85/1.03  thf(t98_relat_1, axiom,
% 0.85/1.03    (![A:$i]:
% 0.85/1.03     ( ( v1_relat_1 @ A ) =>
% 0.85/1.03       ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( A ) ) ))).
% 0.85/1.03  thf('6', plain,
% 0.85/1.03      (![X32 : $i]:
% 0.85/1.03         (((k7_relat_1 @ X32 @ (k1_relat_1 @ X32)) = (X32))
% 0.85/1.03          | ~ (v1_relat_1 @ X32))),
% 0.85/1.03      inference('cnf', [status(esa)], [t98_relat_1])).
% 0.85/1.03  thf('7', plain,
% 0.85/1.03      (![X0 : $i]:
% 0.85/1.03         (((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))
% 0.85/1.03          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.85/1.03      inference('sup+', [status(thm)], ['5', '6'])).
% 0.85/1.03  thf('8', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.85/1.03      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.85/1.03  thf('9', plain,
% 0.85/1.03      (![X0 : $i]: ((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 0.85/1.03      inference('demod', [status(thm)], ['7', '8'])).
% 0.85/1.03  thf(t100_relat_1, axiom,
% 0.85/1.03    (![A:$i,B:$i,C:$i]:
% 0.85/1.03     ( ( v1_relat_1 @ C ) =>
% 0.85/1.03       ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.85/1.03         ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 0.85/1.03  thf('10', plain,
% 0.85/1.03      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.85/1.03         (((k7_relat_1 @ (k7_relat_1 @ X14 @ X15) @ X16)
% 0.85/1.03            = (k7_relat_1 @ X14 @ (k3_xboole_0 @ X15 @ X16)))
% 0.85/1.03          | ~ (v1_relat_1 @ X14))),
% 0.85/1.03      inference('cnf', [status(esa)], [t100_relat_1])).
% 0.85/1.03  thf('11', plain,
% 0.85/1.03      (![X30 : $i, X31 : $i]:
% 0.85/1.03         (((k7_relat_1 @ X31 @ X30) = (k5_relat_1 @ (k6_relat_1 @ X30) @ X31))
% 0.85/1.03          | ~ (v1_relat_1 @ X31))),
% 0.85/1.03      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.85/1.03  thf(t76_relat_1, axiom,
% 0.85/1.03    (![A:$i,B:$i]:
% 0.85/1.03     ( ( v1_relat_1 @ B ) =>
% 0.85/1.03       ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B ) & 
% 0.85/1.03         ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ))).
% 0.85/1.03  thf('12', plain,
% 0.85/1.03      (![X24 : $i, X25 : $i]:
% 0.85/1.03         ((r1_tarski @ (k5_relat_1 @ (k6_relat_1 @ X25) @ X24) @ X24)
% 0.85/1.03          | ~ (v1_relat_1 @ X24))),
% 0.85/1.03      inference('cnf', [status(esa)], [t76_relat_1])).
% 0.85/1.03  thf('13', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         ((r1_tarski @ (k7_relat_1 @ X1 @ X0) @ X1)
% 0.85/1.03          | ~ (v1_relat_1 @ X1)
% 0.85/1.03          | ~ (v1_relat_1 @ X1))),
% 0.85/1.03      inference('sup+', [status(thm)], ['11', '12'])).
% 0.85/1.03  thf('14', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         (~ (v1_relat_1 @ X1) | (r1_tarski @ (k7_relat_1 @ X1 @ X0) @ X1))),
% 0.85/1.03      inference('simplify', [status(thm)], ['13'])).
% 0.85/1.03  thf(t28_xboole_1, axiom,
% 0.85/1.03    (![A:$i,B:$i]:
% 0.85/1.03     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.85/1.03  thf('15', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         (((k3_xboole_0 @ X0 @ X1) = (X0)) | ~ (r1_tarski @ X0 @ X1))),
% 0.85/1.03      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.85/1.03  thf('16', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         (~ (v1_relat_1 @ X0)
% 0.85/1.03          | ((k3_xboole_0 @ (k7_relat_1 @ X0 @ X1) @ X0)
% 0.85/1.03              = (k7_relat_1 @ X0 @ X1)))),
% 0.85/1.03      inference('sup-', [status(thm)], ['14', '15'])).
% 0.85/1.03  thf(commutativity_k2_tarski, axiom,
% 0.85/1.03    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.85/1.03  thf('17', plain,
% 0.85/1.03      (![X2 : $i, X3 : $i]: ((k2_tarski @ X3 @ X2) = (k2_tarski @ X2 @ X3))),
% 0.85/1.03      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.85/1.03  thf(t12_setfam_1, axiom,
% 0.85/1.03    (![A:$i,B:$i]:
% 0.85/1.03     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.85/1.03  thf('18', plain,
% 0.85/1.03      (![X9 : $i, X10 : $i]:
% 0.85/1.03         ((k1_setfam_1 @ (k2_tarski @ X9 @ X10)) = (k3_xboole_0 @ X9 @ X10))),
% 0.85/1.03      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.85/1.03  thf('19', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.85/1.03      inference('sup+', [status(thm)], ['17', '18'])).
% 0.85/1.03  thf('20', plain,
% 0.85/1.03      (![X9 : $i, X10 : $i]:
% 0.85/1.03         ((k1_setfam_1 @ (k2_tarski @ X9 @ X10)) = (k3_xboole_0 @ X9 @ X10))),
% 0.85/1.03      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.85/1.03  thf('21', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.85/1.03      inference('sup+', [status(thm)], ['19', '20'])).
% 0.85/1.03  thf('22', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         (~ (v1_relat_1 @ X0)
% 0.85/1.03          | ((k3_xboole_0 @ X0 @ (k7_relat_1 @ X0 @ X1))
% 0.85/1.03              = (k7_relat_1 @ X0 @ X1)))),
% 0.85/1.03      inference('demod', [status(thm)], ['16', '21'])).
% 0.85/1.03  thf('23', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.85/1.03         (((k3_xboole_0 @ (k7_relat_1 @ X2 @ X1) @ 
% 0.85/1.03            (k7_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 0.85/1.03            = (k7_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0))
% 0.85/1.03          | ~ (v1_relat_1 @ X2)
% 0.85/1.03          | ~ (v1_relat_1 @ (k7_relat_1 @ X2 @ X1)))),
% 0.85/1.03      inference('sup+', [status(thm)], ['10', '22'])).
% 0.85/1.03  thf('24', plain,
% 0.85/1.03      (![X30 : $i, X31 : $i]:
% 0.85/1.03         (((k7_relat_1 @ X31 @ X30) = (k5_relat_1 @ (k6_relat_1 @ X30) @ X31))
% 0.85/1.03          | ~ (v1_relat_1 @ X31))),
% 0.85/1.03      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.85/1.03  thf('25', plain,
% 0.85/1.03      (![X24 : $i, X25 : $i]:
% 0.85/1.03         ((r1_tarski @ (k5_relat_1 @ (k6_relat_1 @ X25) @ X24) @ X24)
% 0.85/1.03          | ~ (v1_relat_1 @ X24))),
% 0.85/1.03      inference('cnf', [status(esa)], [t76_relat_1])).
% 0.85/1.03  thf('26', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         (((k3_xboole_0 @ X0 @ X1) = (X0)) | ~ (r1_tarski @ X0 @ X1))),
% 0.85/1.03      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.85/1.03  thf('27', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         (~ (v1_relat_1 @ X0)
% 0.85/1.03          | ((k3_xboole_0 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X0)
% 0.85/1.03              = (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 0.85/1.03      inference('sup-', [status(thm)], ['25', '26'])).
% 0.85/1.03  thf('28', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.85/1.03      inference('sup+', [status(thm)], ['19', '20'])).
% 0.85/1.03  thf('29', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         (~ (v1_relat_1 @ X0)
% 0.85/1.03          | ((k3_xboole_0 @ X0 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.85/1.03              = (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 0.85/1.03      inference('demod', [status(thm)], ['27', '28'])).
% 0.85/1.03  thf(fc1_relat_1, axiom,
% 0.85/1.03    (![A:$i,B:$i]:
% 0.85/1.03     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.85/1.03  thf('30', plain,
% 0.85/1.03      (![X12 : $i, X13 : $i]:
% 0.85/1.03         (~ (v1_relat_1 @ X12) | (v1_relat_1 @ (k3_xboole_0 @ X12 @ X13)))),
% 0.85/1.03      inference('cnf', [status(esa)], [fc1_relat_1])).
% 0.85/1.03  thf('31', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         ((v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.85/1.03          | ~ (v1_relat_1 @ X0)
% 0.85/1.03          | ~ (v1_relat_1 @ X0))),
% 0.85/1.03      inference('sup+', [status(thm)], ['29', '30'])).
% 0.85/1.03  thf('32', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         (~ (v1_relat_1 @ X0)
% 0.85/1.03          | (v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 0.85/1.03      inference('simplify', [status(thm)], ['31'])).
% 0.85/1.03  thf('33', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         ((v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.85/1.03          | ~ (v1_relat_1 @ X1)
% 0.85/1.03          | ~ (v1_relat_1 @ X1))),
% 0.85/1.03      inference('sup+', [status(thm)], ['24', '32'])).
% 0.85/1.03  thf('34', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         (~ (v1_relat_1 @ X1) | (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.85/1.03      inference('simplify', [status(thm)], ['33'])).
% 0.85/1.03  thf('35', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.85/1.03         (~ (v1_relat_1 @ X2)
% 0.85/1.03          | ((k3_xboole_0 @ (k7_relat_1 @ X2 @ X1) @ 
% 0.85/1.03              (k7_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 0.85/1.03              = (k7_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0)))),
% 0.85/1.03      inference('clc', [status(thm)], ['23', '34'])).
% 0.85/1.03  thf('36', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         (((k3_xboole_0 @ 
% 0.85/1.03            (k7_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ X1) @ 
% 0.85/1.03            (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.85/1.03            = (k7_relat_1 @ 
% 0.85/1.03               (k7_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ X1) @ X0))
% 0.85/1.03          | ~ (v1_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.85/1.03      inference('sup+', [status(thm)], ['9', '35'])).
% 0.85/1.03  thf('37', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.85/1.03      inference('sup+', [status(thm)], ['19', '20'])).
% 0.85/1.03  thf('38', plain,
% 0.85/1.03      (![X0 : $i]: ((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 0.85/1.03      inference('demod', [status(thm)], ['7', '8'])).
% 0.85/1.03  thf('39', plain,
% 0.85/1.03      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.85/1.03         (((k7_relat_1 @ (k7_relat_1 @ X14 @ X15) @ X16)
% 0.85/1.03            = (k7_relat_1 @ X14 @ (k3_xboole_0 @ X15 @ X16)))
% 0.85/1.03          | ~ (v1_relat_1 @ X14))),
% 0.85/1.03      inference('cnf', [status(esa)], [t100_relat_1])).
% 0.85/1.03  thf('40', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         (((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.85/1.03            = (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))
% 0.85/1.03          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.85/1.03      inference('sup+', [status(thm)], ['38', '39'])).
% 0.85/1.03  thf('41', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.85/1.03      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.85/1.03  thf('42', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.85/1.03           = (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 0.85/1.03      inference('demod', [status(thm)], ['40', '41'])).
% 0.85/1.03  thf('43', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         (~ (v1_relat_1 @ X0)
% 0.85/1.03          | ((k3_xboole_0 @ X0 @ (k7_relat_1 @ X0 @ X1))
% 0.85/1.03              = (k7_relat_1 @ X0 @ X1)))),
% 0.85/1.03      inference('demod', [status(thm)], ['16', '21'])).
% 0.85/1.03  thf('44', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         (((k3_xboole_0 @ (k6_relat_1 @ X1) @ 
% 0.85/1.03            (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.85/1.03            = (k7_relat_1 @ (k6_relat_1 @ X1) @ (k3_xboole_0 @ X1 @ X0)))
% 0.85/1.03          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.85/1.03      inference('sup+', [status(thm)], ['42', '43'])).
% 0.85/1.03  thf('45', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.85/1.03           = (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 0.85/1.03      inference('demod', [status(thm)], ['40', '41'])).
% 0.85/1.03  thf('46', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.85/1.03      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.85/1.03  thf('47', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         ((k3_xboole_0 @ (k6_relat_1 @ X1) @ 
% 0.85/1.03           (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.85/1.03           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 0.85/1.03      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.85/1.03  thf('48', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.85/1.03           = (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 0.85/1.03      inference('demod', [status(thm)], ['40', '41'])).
% 0.85/1.03  thf('49', plain,
% 0.85/1.03      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.85/1.03         (((k7_relat_1 @ (k7_relat_1 @ X14 @ X15) @ X16)
% 0.85/1.03            = (k7_relat_1 @ X14 @ (k3_xboole_0 @ X15 @ X16)))
% 0.85/1.03          | ~ (v1_relat_1 @ X14))),
% 0.85/1.03      inference('cnf', [status(esa)], [t100_relat_1])).
% 0.85/1.03  thf('50', plain,
% 0.85/1.03      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.85/1.03         (((k7_relat_1 @ (k7_relat_1 @ X14 @ X15) @ X16)
% 0.85/1.03            = (k7_relat_1 @ X14 @ (k3_xboole_0 @ X15 @ X16)))
% 0.85/1.03          | ~ (v1_relat_1 @ X14))),
% 0.85/1.03      inference('cnf', [status(esa)], [t100_relat_1])).
% 0.85/1.03  thf('51', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.85/1.03         (((k7_relat_1 @ (k7_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X3)
% 0.85/1.03            = (k7_relat_1 @ (k7_relat_1 @ X2 @ X1) @ (k3_xboole_0 @ X0 @ X3)))
% 0.85/1.03          | ~ (v1_relat_1 @ X2)
% 0.85/1.03          | ~ (v1_relat_1 @ (k7_relat_1 @ X2 @ X1)))),
% 0.85/1.03      inference('sup+', [status(thm)], ['49', '50'])).
% 0.85/1.03  thf('52', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         (~ (v1_relat_1 @ X1) | (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.85/1.03      inference('simplify', [status(thm)], ['33'])).
% 0.85/1.03  thf('53', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.85/1.03         (~ (v1_relat_1 @ X2)
% 0.85/1.03          | ((k7_relat_1 @ (k7_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X3)
% 0.85/1.03              = (k7_relat_1 @ (k7_relat_1 @ X2 @ X1) @ (k3_xboole_0 @ X0 @ X3))))),
% 0.85/1.03      inference('clc', [status(thm)], ['51', '52'])).
% 0.85/1.03  thf('54', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.85/1.03         (((k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X2)
% 0.85/1.03            = (k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X1) @ 
% 0.85/1.03               (k3_xboole_0 @ X0 @ X2)))
% 0.85/1.03          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.85/1.03      inference('sup+', [status(thm)], ['48', '53'])).
% 0.85/1.03  thf('55', plain,
% 0.85/1.03      (![X0 : $i]: ((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 0.85/1.03      inference('demod', [status(thm)], ['7', '8'])).
% 0.85/1.03  thf('56', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.85/1.03      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.85/1.03  thf('57', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.85/1.03         ((k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X2)
% 0.85/1.03           = (k7_relat_1 @ (k6_relat_1 @ X1) @ (k3_xboole_0 @ X0 @ X2)))),
% 0.85/1.03      inference('demod', [status(thm)], ['54', '55', '56'])).
% 0.85/1.03  thf('58', plain,
% 0.85/1.03      (![X0 : $i]: ((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 0.85/1.03      inference('demod', [status(thm)], ['7', '8'])).
% 0.85/1.03  thf('59', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.85/1.03      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.85/1.03  thf('60', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         ((k7_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ X1)
% 0.85/1.03           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.85/1.03      inference('demod', [status(thm)], ['36', '37', '47', '57', '58', '59'])).
% 0.85/1.03  thf('61', plain,
% 0.85/1.03      (![X30 : $i, X31 : $i]:
% 0.85/1.03         (((k7_relat_1 @ X31 @ X30) = (k5_relat_1 @ (k6_relat_1 @ X30) @ X31))
% 0.85/1.03          | ~ (v1_relat_1 @ X31))),
% 0.85/1.03      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.85/1.03  thf('62', plain,
% 0.85/1.03      (![X24 : $i, X25 : $i]:
% 0.85/1.03         ((r1_tarski @ (k5_relat_1 @ X24 @ (k6_relat_1 @ X25)) @ X24)
% 0.85/1.03          | ~ (v1_relat_1 @ X24))),
% 0.85/1.03      inference('cnf', [status(esa)], [t76_relat_1])).
% 0.85/1.03  thf(t25_relat_1, axiom,
% 0.85/1.03    (![A:$i]:
% 0.85/1.03     ( ( v1_relat_1 @ A ) =>
% 0.85/1.03       ( ![B:$i]:
% 0.85/1.03         ( ( v1_relat_1 @ B ) =>
% 0.85/1.03           ( ( r1_tarski @ A @ B ) =>
% 0.85/1.03             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 0.85/1.03               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 0.85/1.03  thf('63', plain,
% 0.85/1.03      (![X17 : $i, X18 : $i]:
% 0.85/1.03         (~ (v1_relat_1 @ X17)
% 0.85/1.03          | (r1_tarski @ (k2_relat_1 @ X18) @ (k2_relat_1 @ X17))
% 0.85/1.03          | ~ (r1_tarski @ X18 @ X17)
% 0.85/1.03          | ~ (v1_relat_1 @ X18))),
% 0.85/1.03      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.85/1.03  thf('64', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         (~ (v1_relat_1 @ X0)
% 0.85/1.03          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 0.85/1.03          | (r1_tarski @ 
% 0.85/1.03             (k2_relat_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1))) @ 
% 0.85/1.03             (k2_relat_1 @ X0))
% 0.85/1.03          | ~ (v1_relat_1 @ X0))),
% 0.85/1.03      inference('sup-', [status(thm)], ['62', '63'])).
% 0.85/1.03  thf('65', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1))) @ 
% 0.85/1.03           (k2_relat_1 @ X0))
% 0.85/1.03          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 0.85/1.03          | ~ (v1_relat_1 @ X0))),
% 0.85/1.03      inference('simplify', [status(thm)], ['64'])).
% 0.85/1.03  thf('66', plain,
% 0.85/1.03      (![X24 : $i, X25 : $i]:
% 0.85/1.03         ((r1_tarski @ (k5_relat_1 @ X24 @ (k6_relat_1 @ X25)) @ X24)
% 0.85/1.03          | ~ (v1_relat_1 @ X24))),
% 0.85/1.03      inference('cnf', [status(esa)], [t76_relat_1])).
% 0.85/1.03  thf('67', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         (((k3_xboole_0 @ X0 @ X1) = (X0)) | ~ (r1_tarski @ X0 @ X1))),
% 0.85/1.03      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.85/1.03  thf('68', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         (~ (v1_relat_1 @ X0)
% 0.85/1.03          | ((k3_xboole_0 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)) @ X0)
% 0.85/1.03              = (k5_relat_1 @ X0 @ (k6_relat_1 @ X1))))),
% 0.85/1.03      inference('sup-', [status(thm)], ['66', '67'])).
% 0.85/1.03  thf('69', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.85/1.03      inference('sup+', [status(thm)], ['19', '20'])).
% 0.85/1.03  thf('70', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         (~ (v1_relat_1 @ X0)
% 0.85/1.03          | ((k3_xboole_0 @ X0 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 0.85/1.03              = (k5_relat_1 @ X0 @ (k6_relat_1 @ X1))))),
% 0.85/1.03      inference('demod', [status(thm)], ['68', '69'])).
% 0.85/1.03  thf('71', plain,
% 0.85/1.03      (![X12 : $i, X13 : $i]:
% 0.85/1.03         (~ (v1_relat_1 @ X12) | (v1_relat_1 @ (k3_xboole_0 @ X12 @ X13)))),
% 0.85/1.03      inference('cnf', [status(esa)], [fc1_relat_1])).
% 0.85/1.03  thf('72', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         ((v1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.85/1.03          | ~ (v1_relat_1 @ X1)
% 0.85/1.03          | ~ (v1_relat_1 @ X1))),
% 0.85/1.03      inference('sup+', [status(thm)], ['70', '71'])).
% 0.85/1.03  thf('73', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         (~ (v1_relat_1 @ X1)
% 0.85/1.03          | (v1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 0.85/1.03      inference('simplify', [status(thm)], ['72'])).
% 0.85/1.03  thf('74', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         (~ (v1_relat_1 @ X0)
% 0.85/1.03          | (r1_tarski @ 
% 0.85/1.03             (k2_relat_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1))) @ 
% 0.85/1.03             (k2_relat_1 @ X0)))),
% 0.85/1.03      inference('clc', [status(thm)], ['65', '73'])).
% 0.85/1.03  thf('75', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         ((r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)) @ 
% 0.85/1.03           (k2_relat_1 @ (k6_relat_1 @ X0)))
% 0.85/1.03          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.85/1.03          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.85/1.03      inference('sup+', [status(thm)], ['61', '74'])).
% 0.85/1.03  thf('76', plain, (![X23 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X23)) = (X23))),
% 0.85/1.03      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.85/1.03  thf('77', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.85/1.03      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.85/1.03  thf('78', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.85/1.03      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.85/1.03  thf('79', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)) @ X0)),
% 0.85/1.03      inference('demod', [status(thm)], ['75', '76', '77', '78'])).
% 0.85/1.03  thf(t79_relat_1, axiom,
% 0.85/1.03    (![A:$i,B:$i]:
% 0.85/1.03     ( ( v1_relat_1 @ B ) =>
% 0.85/1.03       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.85/1.03         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 0.85/1.03  thf('80', plain,
% 0.85/1.03      (![X28 : $i, X29 : $i]:
% 0.85/1.03         (~ (r1_tarski @ (k2_relat_1 @ X28) @ X29)
% 0.85/1.03          | ((k5_relat_1 @ X28 @ (k6_relat_1 @ X29)) = (X28))
% 0.85/1.03          | ~ (v1_relat_1 @ X28))),
% 0.85/1.03      inference('cnf', [status(esa)], [t79_relat_1])).
% 0.85/1.03  thf('81', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         (~ (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.85/1.03          | ((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 0.85/1.03              (k6_relat_1 @ X0)) = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 0.85/1.03      inference('sup-', [status(thm)], ['79', '80'])).
% 0.85/1.03  thf('82', plain,
% 0.85/1.03      (![X30 : $i, X31 : $i]:
% 0.85/1.03         (((k7_relat_1 @ X31 @ X30) = (k5_relat_1 @ (k6_relat_1 @ X30) @ X31))
% 0.85/1.03          | ~ (v1_relat_1 @ X31))),
% 0.85/1.03      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.85/1.03  thf('83', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         (~ (v1_relat_1 @ X1)
% 0.85/1.03          | (v1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 0.85/1.03      inference('simplify', [status(thm)], ['72'])).
% 0.85/1.03  thf('84', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         ((v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.85/1.03          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.85/1.03          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.85/1.03      inference('sup+', [status(thm)], ['82', '83'])).
% 0.85/1.03  thf('85', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.85/1.03      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.85/1.03  thf('86', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.85/1.03      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.85/1.03  thf('87', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 0.85/1.03      inference('demod', [status(thm)], ['84', '85', '86'])).
% 0.85/1.03  thf('88', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         ((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 0.85/1.03           (k6_relat_1 @ X0)) = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 0.85/1.03      inference('demod', [status(thm)], ['81', '87'])).
% 0.85/1.03  thf('89', plain,
% 0.85/1.03      (![X30 : $i, X31 : $i]:
% 0.85/1.03         (((k7_relat_1 @ X31 @ X30) = (k5_relat_1 @ (k6_relat_1 @ X30) @ X31))
% 0.85/1.03          | ~ (v1_relat_1 @ X31))),
% 0.85/1.03      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.85/1.03  thf('90', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         (~ (v1_relat_1 @ X0)
% 0.85/1.03          | ((k3_xboole_0 @ X0 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.85/1.03              = (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 0.85/1.03      inference('demod', [status(thm)], ['27', '28'])).
% 0.85/1.03  thf('91', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         (((k3_xboole_0 @ X1 @ (k7_relat_1 @ X1 @ X0))
% 0.85/1.03            = (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.85/1.03          | ~ (v1_relat_1 @ X1)
% 0.85/1.03          | ~ (v1_relat_1 @ X1))),
% 0.85/1.03      inference('sup+', [status(thm)], ['89', '90'])).
% 0.85/1.03  thf('92', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         (~ (v1_relat_1 @ X1)
% 0.85/1.03          | ((k3_xboole_0 @ X1 @ (k7_relat_1 @ X1 @ X0))
% 0.85/1.03              = (k5_relat_1 @ (k6_relat_1 @ X0) @ X1)))),
% 0.85/1.03      inference('simplify', [status(thm)], ['91'])).
% 0.85/1.03  thf('93', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         ((k3_xboole_0 @ (k6_relat_1 @ X1) @ 
% 0.85/1.03           (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.85/1.03           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 0.85/1.03      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.85/1.03  thf('94', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         (((k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 0.85/1.03            = (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.85/1.03          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.85/1.03      inference('sup+', [status(thm)], ['92', '93'])).
% 0.85/1.03  thf('95', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.85/1.03      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.85/1.03  thf('96', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         ((k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 0.85/1.03           = (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 0.85/1.03      inference('demod', [status(thm)], ['94', '95'])).
% 0.85/1.03  thf('97', plain,
% 0.85/1.03      (![X30 : $i, X31 : $i]:
% 0.85/1.03         (((k7_relat_1 @ X31 @ X30) = (k5_relat_1 @ (k6_relat_1 @ X30) @ X31))
% 0.85/1.03          | ~ (v1_relat_1 @ X31))),
% 0.85/1.03      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.85/1.03  thf(t55_relat_1, axiom,
% 0.85/1.03    (![A:$i]:
% 0.85/1.03     ( ( v1_relat_1 @ A ) =>
% 0.85/1.03       ( ![B:$i]:
% 0.85/1.03         ( ( v1_relat_1 @ B ) =>
% 0.85/1.03           ( ![C:$i]:
% 0.85/1.03             ( ( v1_relat_1 @ C ) =>
% 0.85/1.03               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 0.85/1.03                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 0.85/1.03  thf('98', plain,
% 0.85/1.03      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.85/1.03         (~ (v1_relat_1 @ X19)
% 0.85/1.03          | ((k5_relat_1 @ (k5_relat_1 @ X20 @ X19) @ X21)
% 0.85/1.03              = (k5_relat_1 @ X20 @ (k5_relat_1 @ X19 @ X21)))
% 0.85/1.03          | ~ (v1_relat_1 @ X21)
% 0.85/1.03          | ~ (v1_relat_1 @ X20))),
% 0.85/1.03      inference('cnf', [status(esa)], [t55_relat_1])).
% 0.85/1.03  thf('99', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.85/1.03         (((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 0.85/1.03            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2)))
% 0.85/1.03          | ~ (v1_relat_1 @ X1)
% 0.85/1.03          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.85/1.03          | ~ (v1_relat_1 @ X2)
% 0.85/1.03          | ~ (v1_relat_1 @ X1))),
% 0.85/1.03      inference('sup+', [status(thm)], ['97', '98'])).
% 0.85/1.03  thf('100', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.85/1.03      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.85/1.03  thf('101', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.85/1.03         (((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 0.85/1.03            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2)))
% 0.85/1.03          | ~ (v1_relat_1 @ X1)
% 0.85/1.03          | ~ (v1_relat_1 @ X2)
% 0.85/1.03          | ~ (v1_relat_1 @ X1))),
% 0.85/1.03      inference('demod', [status(thm)], ['99', '100'])).
% 0.85/1.03  thf('102', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.85/1.03         (~ (v1_relat_1 @ X2)
% 0.85/1.03          | ~ (v1_relat_1 @ X1)
% 0.85/1.03          | ((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 0.85/1.03              = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2))))),
% 0.85/1.03      inference('simplify', [status(thm)], ['101'])).
% 0.85/1.03  thf('103', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.85/1.03         (((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X2) @ 
% 0.85/1.03            (k6_relat_1 @ X1))
% 0.85/1.03            = (k5_relat_1 @ (k6_relat_1 @ X2) @ 
% 0.85/1.03               (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))
% 0.85/1.03          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.85/1.03          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.85/1.03      inference('sup+', [status(thm)], ['96', '102'])).
% 0.85/1.03  thf('104', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.85/1.03      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.85/1.03  thf('105', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.85/1.03      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.85/1.03  thf('106', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.85/1.03         ((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X2) @ 
% 0.85/1.03           (k6_relat_1 @ X1))
% 0.85/1.03           = (k5_relat_1 @ (k6_relat_1 @ X2) @ 
% 0.85/1.03              (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 0.85/1.03      inference('demod', [status(thm)], ['103', '104', '105'])).
% 0.85/1.03  thf('107', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.85/1.03           = (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 0.85/1.03      inference('demod', [status(thm)], ['40', '41'])).
% 0.85/1.03  thf('108', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         (~ (v1_relat_1 @ X1) | (r1_tarski @ (k7_relat_1 @ X1 @ X0) @ X1))),
% 0.85/1.03      inference('simplify', [status(thm)], ['13'])).
% 0.85/1.03  thf('109', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         ((r1_tarski @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 0.85/1.03           (k6_relat_1 @ X1))
% 0.85/1.03          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.85/1.03      inference('sup+', [status(thm)], ['107', '108'])).
% 0.85/1.03  thf('110', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.85/1.03      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.85/1.03  thf('111', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         (r1_tarski @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ (k6_relat_1 @ X1))),
% 0.85/1.03      inference('demod', [status(thm)], ['109', '110'])).
% 0.85/1.03  thf('112', plain,
% 0.85/1.03      (![X17 : $i, X18 : $i]:
% 0.85/1.03         (~ (v1_relat_1 @ X17)
% 0.85/1.03          | (r1_tarski @ (k2_relat_1 @ X18) @ (k2_relat_1 @ X17))
% 0.85/1.03          | ~ (r1_tarski @ X18 @ X17)
% 0.85/1.03          | ~ (v1_relat_1 @ X18))),
% 0.85/1.03      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.85/1.03  thf('113', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         (~ (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.85/1.03          | (r1_tarski @ 
% 0.85/1.03             (k2_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1)) @ 
% 0.85/1.03             (k2_relat_1 @ (k6_relat_1 @ X0)))
% 0.85/1.03          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.85/1.03      inference('sup-', [status(thm)], ['111', '112'])).
% 0.85/1.03  thf('114', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 0.85/1.03      inference('demod', [status(thm)], ['84', '85', '86'])).
% 0.85/1.03  thf('115', plain, (![X23 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X23)) = (X23))),
% 0.85/1.03      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.85/1.03  thf('116', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.85/1.03      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.85/1.03  thf('117', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1)) @ X0)),
% 0.85/1.03      inference('demod', [status(thm)], ['113', '114', '115', '116'])).
% 0.85/1.03  thf('118', plain,
% 0.85/1.03      (![X28 : $i, X29 : $i]:
% 0.85/1.03         (~ (r1_tarski @ (k2_relat_1 @ X28) @ X29)
% 0.85/1.03          | ((k5_relat_1 @ X28 @ (k6_relat_1 @ X29)) = (X28))
% 0.85/1.03          | ~ (v1_relat_1 @ X28))),
% 0.85/1.03      inference('cnf', [status(esa)], [t79_relat_1])).
% 0.85/1.03  thf('119', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         (~ (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.85/1.04          | ((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1) @ 
% 0.85/1.04              (k6_relat_1 @ X0)) = (k7_relat_1 @ (k6_relat_1 @ X0) @ X1)))),
% 0.85/1.04      inference('sup-', [status(thm)], ['117', '118'])).
% 0.85/1.04  thf('120', plain,
% 0.85/1.04      (![X0 : $i, X1 : $i]:
% 0.85/1.04         (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 0.85/1.04      inference('demod', [status(thm)], ['84', '85', '86'])).
% 0.85/1.04  thf('121', plain,
% 0.85/1.04      (![X0 : $i, X1 : $i]:
% 0.85/1.04         ((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1) @ 
% 0.85/1.04           (k6_relat_1 @ X0)) = (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 0.85/1.04      inference('demod', [status(thm)], ['119', '120'])).
% 0.85/1.04  thf('122', plain,
% 0.85/1.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.85/1.04         (~ (v1_relat_1 @ X2)
% 0.85/1.04          | ~ (v1_relat_1 @ X1)
% 0.85/1.04          | ((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 0.85/1.04              = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2))))),
% 0.85/1.04      inference('simplify', [status(thm)], ['101'])).
% 0.85/1.04  thf('123', plain,
% 0.85/1.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.85/1.04         (((k5_relat_1 @ 
% 0.85/1.04            (k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X2) @ 
% 0.85/1.04            (k6_relat_1 @ X1))
% 0.85/1.04            = (k5_relat_1 @ (k6_relat_1 @ X2) @ 
% 0.85/1.04               (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))
% 0.85/1.04          | ~ (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.85/1.04          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.85/1.04      inference('sup+', [status(thm)], ['121', '122'])).
% 0.85/1.04  thf('124', plain,
% 0.85/1.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.85/1.04         ((k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X2)
% 0.85/1.04           = (k7_relat_1 @ (k6_relat_1 @ X1) @ (k3_xboole_0 @ X0 @ X2)))),
% 0.85/1.04      inference('demod', [status(thm)], ['54', '55', '56'])).
% 0.85/1.04  thf('125', plain,
% 0.85/1.04      (![X0 : $i, X1 : $i]:
% 0.85/1.04         ((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1) @ 
% 0.85/1.04           (k6_relat_1 @ X0)) = (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 0.85/1.04      inference('demod', [status(thm)], ['119', '120'])).
% 0.85/1.04  thf('126', plain,
% 0.85/1.04      (![X0 : $i, X1 : $i]:
% 0.85/1.04         (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 0.85/1.04      inference('demod', [status(thm)], ['84', '85', '86'])).
% 0.85/1.04  thf('127', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.85/1.04      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.85/1.04  thf('128', plain,
% 0.85/1.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.85/1.04         ((k7_relat_1 @ (k6_relat_1 @ X1) @ (k3_xboole_0 @ X0 @ X2))
% 0.85/1.04           = (k5_relat_1 @ (k6_relat_1 @ X2) @ 
% 0.85/1.04              (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 0.85/1.04      inference('demod', [status(thm)], ['123', '124', '125', '126', '127'])).
% 0.85/1.04  thf('129', plain,
% 0.85/1.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.85/1.04         ((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X2) @ 
% 0.85/1.04           (k6_relat_1 @ X1))
% 0.85/1.04           = (k7_relat_1 @ (k6_relat_1 @ X1) @ (k3_xboole_0 @ X0 @ X2)))),
% 0.85/1.04      inference('demod', [status(thm)], ['106', '128'])).
% 0.85/1.04  thf('130', plain,
% 0.85/1.04      (![X0 : $i, X1 : $i]:
% 0.85/1.04         ((k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 0.85/1.04           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 0.85/1.04      inference('demod', [status(thm)], ['88', '129'])).
% 0.85/1.04  thf('131', plain,
% 0.85/1.04      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.85/1.04      inference('sup+', [status(thm)], ['19', '20'])).
% 0.85/1.04  thf('132', plain,
% 0.85/1.04      (![X0 : $i, X1 : $i]:
% 0.85/1.04         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.85/1.04           = (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 0.85/1.04      inference('demod', [status(thm)], ['40', '41'])).
% 0.85/1.04  thf('133', plain,
% 0.85/1.04      (![X0 : $i, X1 : $i]:
% 0.85/1.04         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.85/1.04           = (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 0.85/1.04      inference('sup+', [status(thm)], ['131', '132'])).
% 0.85/1.04  thf('134', plain,
% 0.85/1.04      (![X0 : $i, X1 : $i]:
% 0.85/1.04         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.85/1.04           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 0.85/1.04      inference('sup+', [status(thm)], ['130', '133'])).
% 0.85/1.04  thf('135', plain,
% 0.85/1.04      (![X0 : $i, X1 : $i]:
% 0.85/1.04         ((k7_relat_1 @ (k6_relat_1 @ X1) @ (k3_xboole_0 @ X1 @ X0))
% 0.85/1.04           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.85/1.04      inference('demod', [status(thm)], ['60', '134'])).
% 0.85/1.04  thf('136', plain,
% 0.85/1.04      (![X0 : $i, X1 : $i]:
% 0.85/1.04         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.85/1.04           = (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 0.85/1.04      inference('demod', [status(thm)], ['40', '41'])).
% 0.85/1.04  thf('137', plain,
% 0.85/1.04      (![X0 : $i, X1 : $i]:
% 0.85/1.04         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.85/1.04           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.85/1.04      inference('sup+', [status(thm)], ['135', '136'])).
% 0.85/1.04  thf('138', plain,
% 0.85/1.04      (((k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B))
% 0.85/1.04         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.85/1.04      inference('demod', [status(thm)], ['4', '137'])).
% 0.85/1.04  thf('139', plain, ($false), inference('simplify', [status(thm)], ['138'])).
% 0.85/1.04  
% 0.85/1.04  % SZS output end Refutation
% 0.85/1.04  
% 0.85/1.04  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
