%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OKgE4jhzJ2

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:20 EST 2020

% Result     : Theorem 0.50s
% Output     : Refutation 0.50s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 199 expanded)
%              Number of leaves         :   22 (  70 expanded)
%              Depth                    :   19
%              Number of atoms          :  680 (1643 expanded)
%              Number of equality atoms :   45 ( 110 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t146_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
         => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t146_funct_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('1',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X13 @ X14 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X13 ) @ X14 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('2',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('4',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) )
    = sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('5',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_tarski @ X3 @ X2 )
      = ( k2_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X4 @ X5 ) )
      = ( k3_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X4 @ X5 ) )
      = ( k3_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X13 @ X14 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X13 ) @ X14 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('11',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) ) @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k3_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X0 )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k3_xboole_0 @ X0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['10','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) )
    = sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('20',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X13 @ X14 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X13 ) @ X14 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('21',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X13 @ X14 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X13 ) @ X14 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('22',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) ) @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) @ X2 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','24'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('26',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k3_xboole_0 @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) @ X2 ) @ X2 ) ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ ( k1_relat_1 @ X0 ) ) @ X2 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ sk_A @ X0 ) @ X0 )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['18','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_A @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ sk_A ) ) @ ( k3_xboole_0 @ ( k1_relat_1 @ X0 ) @ sk_A ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ sk_A ) ) @ ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','32'])).

thf('34',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['4','33'])).

thf('35',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) @ sk_A ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('38',plain,
    ( ( k3_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) @ sk_A )
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('40',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['1','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('43',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) )
    = sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf('44',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) )
    = sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ ( k1_relat_1 @ X0 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( r1_tarski @ sk_A @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['44','47'])).

thf('49',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    r1_tarski @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('52',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( sk_A
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['41','42','43','52','53'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('55',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X8 @ X9 ) )
        = ( k9_relat_1 @ X8 @ X9 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('56',plain,(
    ! [X10: $i] :
      ( ( ( k10_relat_1 @ X10 @ ( k2_relat_1 @ X10 ) )
        = ( k1_relat_1 @ X10 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['57','58'])).

thf(t139_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('60',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X16 @ X15 ) @ X17 )
        = ( k3_xboole_0 @ X15 @ ( k10_relat_1 @ X16 @ X17 ) ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_A @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ sk_A ) ) @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ sk_A ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['54','64'])).

thf('66',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    $false ),
    inference(demod,[status(thm)],['0','67'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OKgE4jhzJ2
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:53:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.50/0.72  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.50/0.72  % Solved by: fo/fo7.sh
% 0.50/0.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.50/0.72  % done 285 iterations in 0.273s
% 0.50/0.72  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.50/0.72  % SZS output start Refutation
% 0.50/0.72  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.50/0.72  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.50/0.72  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.50/0.72  thf(sk_B_type, type, sk_B: $i).
% 0.50/0.72  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.50/0.72  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.50/0.72  thf(sk_A_type, type, sk_A: $i).
% 0.50/0.72  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.50/0.72  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.50/0.72  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.50/0.72  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.50/0.72  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.50/0.72  thf(t146_funct_1, conjecture,
% 0.50/0.72    (![A:$i,B:$i]:
% 0.50/0.72     ( ( v1_relat_1 @ B ) =>
% 0.50/0.72       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.50/0.72         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 0.50/0.72  thf(zf_stmt_0, negated_conjecture,
% 0.50/0.72    (~( ![A:$i,B:$i]:
% 0.50/0.72        ( ( v1_relat_1 @ B ) =>
% 0.50/0.72          ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.50/0.72            ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )),
% 0.50/0.72    inference('cnf.neg', [status(esa)], [t146_funct_1])).
% 0.50/0.72  thf('0', plain,
% 0.50/0.72      (~ (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 0.50/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.72  thf(t90_relat_1, axiom,
% 0.50/0.72    (![A:$i,B:$i]:
% 0.50/0.72     ( ( v1_relat_1 @ B ) =>
% 0.50/0.72       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 0.50/0.72         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.50/0.72  thf('1', plain,
% 0.50/0.72      (![X13 : $i, X14 : $i]:
% 0.50/0.72         (((k1_relat_1 @ (k7_relat_1 @ X13 @ X14))
% 0.50/0.72            = (k3_xboole_0 @ (k1_relat_1 @ X13) @ X14))
% 0.50/0.72          | ~ (v1_relat_1 @ X13))),
% 0.50/0.72      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.50/0.72  thf('2', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.50/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.72  thf(t28_xboole_1, axiom,
% 0.50/0.72    (![A:$i,B:$i]:
% 0.50/0.72     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.50/0.72  thf('3', plain,
% 0.50/0.72      (![X0 : $i, X1 : $i]:
% 0.50/0.72         (((k3_xboole_0 @ X0 @ X1) = (X0)) | ~ (r1_tarski @ X0 @ X1))),
% 0.50/0.72      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.50/0.72  thf('4', plain, (((k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)) = (sk_A))),
% 0.50/0.72      inference('sup-', [status(thm)], ['2', '3'])).
% 0.50/0.72  thf(commutativity_k2_tarski, axiom,
% 0.50/0.72    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.50/0.72  thf('5', plain,
% 0.50/0.72      (![X2 : $i, X3 : $i]: ((k2_tarski @ X3 @ X2) = (k2_tarski @ X2 @ X3))),
% 0.50/0.72      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.50/0.72  thf(t12_setfam_1, axiom,
% 0.50/0.72    (![A:$i,B:$i]:
% 0.50/0.72     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.50/0.72  thf('6', plain,
% 0.50/0.72      (![X4 : $i, X5 : $i]:
% 0.50/0.72         ((k1_setfam_1 @ (k2_tarski @ X4 @ X5)) = (k3_xboole_0 @ X4 @ X5))),
% 0.50/0.72      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.50/0.72  thf('7', plain,
% 0.50/0.72      (![X0 : $i, X1 : $i]:
% 0.50/0.72         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.50/0.72      inference('sup+', [status(thm)], ['5', '6'])).
% 0.50/0.72  thf('8', plain,
% 0.50/0.72      (![X4 : $i, X5 : $i]:
% 0.50/0.72         ((k1_setfam_1 @ (k2_tarski @ X4 @ X5)) = (k3_xboole_0 @ X4 @ X5))),
% 0.50/0.72      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.50/0.72  thf('9', plain,
% 0.50/0.72      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.50/0.72      inference('sup+', [status(thm)], ['7', '8'])).
% 0.50/0.72  thf('10', plain,
% 0.50/0.72      (![X13 : $i, X14 : $i]:
% 0.50/0.72         (((k1_relat_1 @ (k7_relat_1 @ X13 @ X14))
% 0.50/0.72            = (k3_xboole_0 @ (k1_relat_1 @ X13) @ X14))
% 0.50/0.72          | ~ (v1_relat_1 @ X13))),
% 0.50/0.72      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.50/0.72  thf(t87_relat_1, axiom,
% 0.50/0.72    (![A:$i,B:$i]:
% 0.50/0.72     ( ( v1_relat_1 @ B ) =>
% 0.50/0.72       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 0.50/0.72  thf('11', plain,
% 0.50/0.72      (![X11 : $i, X12 : $i]:
% 0.50/0.72         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X11 @ X12)) @ X12)
% 0.50/0.72          | ~ (v1_relat_1 @ X11))),
% 0.50/0.72      inference('cnf', [status(esa)], [t87_relat_1])).
% 0.50/0.72  thf('12', plain,
% 0.50/0.72      (![X0 : $i, X1 : $i]:
% 0.50/0.72         (((k3_xboole_0 @ X0 @ X1) = (X0)) | ~ (r1_tarski @ X0 @ X1))),
% 0.50/0.72      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.50/0.72  thf('13', plain,
% 0.50/0.72      (![X0 : $i, X1 : $i]:
% 0.50/0.72         (~ (v1_relat_1 @ X1)
% 0.50/0.72          | ((k3_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X0)
% 0.50/0.72              = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 0.50/0.72      inference('sup-', [status(thm)], ['11', '12'])).
% 0.50/0.72  thf('14', plain,
% 0.50/0.72      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.50/0.72      inference('sup+', [status(thm)], ['7', '8'])).
% 0.50/0.72  thf('15', plain,
% 0.50/0.72      (![X0 : $i, X1 : $i]:
% 0.50/0.72         (~ (v1_relat_1 @ X1)
% 0.50/0.72          | ((k3_xboole_0 @ X0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.50/0.72              = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 0.50/0.72      inference('demod', [status(thm)], ['13', '14'])).
% 0.50/0.72  thf('16', plain,
% 0.50/0.72      (![X0 : $i, X1 : $i]:
% 0.50/0.72         (((k3_xboole_0 @ X0 @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0))
% 0.50/0.72            = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.50/0.72          | ~ (v1_relat_1 @ X1)
% 0.50/0.72          | ~ (v1_relat_1 @ X1))),
% 0.50/0.72      inference('sup+', [status(thm)], ['10', '15'])).
% 0.50/0.72  thf('17', plain,
% 0.50/0.72      (![X0 : $i, X1 : $i]:
% 0.50/0.72         (~ (v1_relat_1 @ X1)
% 0.50/0.72          | ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0))
% 0.50/0.72              = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 0.50/0.72      inference('simplify', [status(thm)], ['16'])).
% 0.50/0.72  thf('18', plain, (((k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)) = (sk_A))),
% 0.50/0.72      inference('sup-', [status(thm)], ['2', '3'])).
% 0.50/0.72  thf('19', plain,
% 0.50/0.72      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.50/0.72      inference('sup+', [status(thm)], ['7', '8'])).
% 0.50/0.72  thf('20', plain,
% 0.50/0.72      (![X13 : $i, X14 : $i]:
% 0.50/0.72         (((k1_relat_1 @ (k7_relat_1 @ X13 @ X14))
% 0.50/0.72            = (k3_xboole_0 @ (k1_relat_1 @ X13) @ X14))
% 0.50/0.72          | ~ (v1_relat_1 @ X13))),
% 0.50/0.72      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.50/0.72  thf('21', plain,
% 0.50/0.72      (![X13 : $i, X14 : $i]:
% 0.50/0.72         (((k1_relat_1 @ (k7_relat_1 @ X13 @ X14))
% 0.50/0.72            = (k3_xboole_0 @ (k1_relat_1 @ X13) @ X14))
% 0.50/0.72          | ~ (v1_relat_1 @ X13))),
% 0.50/0.72      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.50/0.72  thf('22', plain,
% 0.50/0.72      (![X11 : $i, X12 : $i]:
% 0.50/0.72         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X11 @ X12)) @ X12)
% 0.50/0.72          | ~ (v1_relat_1 @ X11))),
% 0.50/0.72      inference('cnf', [status(esa)], [t87_relat_1])).
% 0.50/0.72  thf('23', plain,
% 0.50/0.72      (![X0 : $i, X1 : $i]:
% 0.50/0.72         ((r1_tarski @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0) @ X0)
% 0.50/0.72          | ~ (v1_relat_1 @ X1)
% 0.50/0.72          | ~ (v1_relat_1 @ X1))),
% 0.50/0.72      inference('sup+', [status(thm)], ['21', '22'])).
% 0.50/0.72  thf('24', plain,
% 0.50/0.72      (![X0 : $i, X1 : $i]:
% 0.50/0.72         (~ (v1_relat_1 @ X1)
% 0.50/0.72          | (r1_tarski @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0) @ X0))),
% 0.50/0.72      inference('simplify', [status(thm)], ['23'])).
% 0.50/0.72  thf('25', plain,
% 0.50/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.72         ((r1_tarski @ 
% 0.50/0.72           (k3_xboole_0 @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0) @ X2) @ X2)
% 0.50/0.72          | ~ (v1_relat_1 @ X1)
% 0.50/0.72          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.50/0.72      inference('sup+', [status(thm)], ['20', '24'])).
% 0.50/0.72  thf(dt_k7_relat_1, axiom,
% 0.50/0.72    (![A:$i,B:$i]:
% 0.50/0.72     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.50/0.72  thf('26', plain,
% 0.50/0.72      (![X6 : $i, X7 : $i]:
% 0.50/0.72         (~ (v1_relat_1 @ X6) | (v1_relat_1 @ (k7_relat_1 @ X6 @ X7)))),
% 0.50/0.72      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.50/0.72  thf('27', plain,
% 0.50/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.72         (~ (v1_relat_1 @ X1)
% 0.50/0.72          | (r1_tarski @ 
% 0.50/0.72             (k3_xboole_0 @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0) @ X2) @ X2))),
% 0.50/0.72      inference('clc', [status(thm)], ['25', '26'])).
% 0.50/0.72  thf('28', plain,
% 0.50/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.72         ((r1_tarski @ 
% 0.50/0.72           (k3_xboole_0 @ (k3_xboole_0 @ X1 @ (k1_relat_1 @ X0)) @ X2) @ X2)
% 0.50/0.72          | ~ (v1_relat_1 @ X0))),
% 0.50/0.72      inference('sup+', [status(thm)], ['19', '27'])).
% 0.50/0.72  thf('29', plain,
% 0.50/0.72      (![X0 : $i]:
% 0.50/0.72         ((r1_tarski @ (k3_xboole_0 @ sk_A @ X0) @ X0) | ~ (v1_relat_1 @ sk_B))),
% 0.50/0.72      inference('sup+', [status(thm)], ['18', '28'])).
% 0.50/0.72  thf('30', plain, ((v1_relat_1 @ sk_B)),
% 0.50/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.72  thf('31', plain, (![X0 : $i]: (r1_tarski @ (k3_xboole_0 @ sk_A @ X0) @ X0)),
% 0.50/0.72      inference('demod', [status(thm)], ['29', '30'])).
% 0.50/0.72  thf('32', plain,
% 0.50/0.72      (![X0 : $i]:
% 0.50/0.72         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X0 @ sk_A)) @ 
% 0.50/0.72           (k3_xboole_0 @ (k1_relat_1 @ X0) @ sk_A))
% 0.50/0.72          | ~ (v1_relat_1 @ X0))),
% 0.50/0.72      inference('sup+', [status(thm)], ['17', '31'])).
% 0.50/0.72  thf('33', plain,
% 0.50/0.72      (![X0 : $i]:
% 0.50/0.72         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X0 @ sk_A)) @ 
% 0.50/0.72           (k3_xboole_0 @ sk_A @ (k1_relat_1 @ X0)))
% 0.50/0.72          | ~ (v1_relat_1 @ X0))),
% 0.50/0.72      inference('sup+', [status(thm)], ['9', '32'])).
% 0.50/0.72  thf('34', plain,
% 0.50/0.72      (((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) @ sk_A)
% 0.50/0.72        | ~ (v1_relat_1 @ sk_B))),
% 0.50/0.72      inference('sup+', [status(thm)], ['4', '33'])).
% 0.50/0.72  thf('35', plain, ((v1_relat_1 @ sk_B)),
% 0.50/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.72  thf('36', plain,
% 0.50/0.72      ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) @ sk_A)),
% 0.50/0.72      inference('demod', [status(thm)], ['34', '35'])).
% 0.50/0.72  thf('37', plain,
% 0.50/0.72      (![X0 : $i, X1 : $i]:
% 0.50/0.72         (((k3_xboole_0 @ X0 @ X1) = (X0)) | ~ (r1_tarski @ X0 @ X1))),
% 0.50/0.72      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.50/0.72  thf('38', plain,
% 0.50/0.72      (((k3_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) @ sk_A)
% 0.50/0.72         = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.50/0.72      inference('sup-', [status(thm)], ['36', '37'])).
% 0.50/0.72  thf('39', plain,
% 0.50/0.72      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.50/0.72      inference('sup+', [status(thm)], ['7', '8'])).
% 0.50/0.72  thf('40', plain,
% 0.50/0.72      (((k3_xboole_0 @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.50/0.72         = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.50/0.72      inference('demod', [status(thm)], ['38', '39'])).
% 0.50/0.72  thf('41', plain,
% 0.50/0.72      ((((k3_xboole_0 @ sk_A @ (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.50/0.72          = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.50/0.72        | ~ (v1_relat_1 @ sk_B))),
% 0.50/0.72      inference('sup+', [status(thm)], ['1', '40'])).
% 0.50/0.72  thf('42', plain,
% 0.50/0.72      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.50/0.72      inference('sup+', [status(thm)], ['7', '8'])).
% 0.50/0.72  thf('43', plain, (((k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)) = (sk_A))),
% 0.50/0.72      inference('sup-', [status(thm)], ['2', '3'])).
% 0.50/0.72  thf('44', plain, (((k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)) = (sk_A))),
% 0.50/0.72      inference('sup-', [status(thm)], ['2', '3'])).
% 0.50/0.72  thf('45', plain,
% 0.50/0.72      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.50/0.72      inference('sup+', [status(thm)], ['7', '8'])).
% 0.50/0.72  thf('46', plain,
% 0.50/0.72      (![X0 : $i, X1 : $i]:
% 0.50/0.72         (~ (v1_relat_1 @ X1)
% 0.50/0.72          | (r1_tarski @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0) @ X0))),
% 0.50/0.72      inference('simplify', [status(thm)], ['23'])).
% 0.50/0.72  thf('47', plain,
% 0.50/0.72      (![X0 : $i, X1 : $i]:
% 0.50/0.72         ((r1_tarski @ (k3_xboole_0 @ X1 @ (k1_relat_1 @ X0)) @ X1)
% 0.50/0.72          | ~ (v1_relat_1 @ X0))),
% 0.50/0.72      inference('sup+', [status(thm)], ['45', '46'])).
% 0.50/0.72  thf('48', plain, (((r1_tarski @ sk_A @ sk_A) | ~ (v1_relat_1 @ sk_B))),
% 0.50/0.72      inference('sup+', [status(thm)], ['44', '47'])).
% 0.50/0.72  thf('49', plain, ((v1_relat_1 @ sk_B)),
% 0.50/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.72  thf('50', plain, ((r1_tarski @ sk_A @ sk_A)),
% 0.50/0.72      inference('demod', [status(thm)], ['48', '49'])).
% 0.50/0.72  thf('51', plain,
% 0.50/0.72      (![X0 : $i, X1 : $i]:
% 0.50/0.72         (((k3_xboole_0 @ X0 @ X1) = (X0)) | ~ (r1_tarski @ X0 @ X1))),
% 0.50/0.72      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.50/0.72  thf('52', plain, (((k3_xboole_0 @ sk_A @ sk_A) = (sk_A))),
% 0.50/0.72      inference('sup-', [status(thm)], ['50', '51'])).
% 0.50/0.72  thf('53', plain, ((v1_relat_1 @ sk_B)),
% 0.50/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.72  thf('54', plain, (((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.50/0.72      inference('demod', [status(thm)], ['41', '42', '43', '52', '53'])).
% 0.50/0.72  thf(t148_relat_1, axiom,
% 0.50/0.72    (![A:$i,B:$i]:
% 0.50/0.72     ( ( v1_relat_1 @ B ) =>
% 0.50/0.72       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.50/0.72  thf('55', plain,
% 0.50/0.72      (![X8 : $i, X9 : $i]:
% 0.50/0.72         (((k2_relat_1 @ (k7_relat_1 @ X8 @ X9)) = (k9_relat_1 @ X8 @ X9))
% 0.50/0.72          | ~ (v1_relat_1 @ X8))),
% 0.50/0.72      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.50/0.72  thf(t169_relat_1, axiom,
% 0.50/0.72    (![A:$i]:
% 0.50/0.72     ( ( v1_relat_1 @ A ) =>
% 0.50/0.72       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.50/0.72  thf('56', plain,
% 0.50/0.72      (![X10 : $i]:
% 0.50/0.72         (((k10_relat_1 @ X10 @ (k2_relat_1 @ X10)) = (k1_relat_1 @ X10))
% 0.50/0.72          | ~ (v1_relat_1 @ X10))),
% 0.50/0.72      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.50/0.72  thf('57', plain,
% 0.50/0.72      (![X0 : $i, X1 : $i]:
% 0.50/0.72         (((k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0))
% 0.50/0.72            = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.50/0.72          | ~ (v1_relat_1 @ X1)
% 0.50/0.72          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.50/0.72      inference('sup+', [status(thm)], ['55', '56'])).
% 0.50/0.72  thf('58', plain,
% 0.50/0.72      (![X6 : $i, X7 : $i]:
% 0.50/0.72         (~ (v1_relat_1 @ X6) | (v1_relat_1 @ (k7_relat_1 @ X6 @ X7)))),
% 0.50/0.72      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.50/0.72  thf('59', plain,
% 0.50/0.72      (![X0 : $i, X1 : $i]:
% 0.50/0.72         (~ (v1_relat_1 @ X1)
% 0.50/0.72          | ((k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0))
% 0.50/0.72              = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 0.50/0.72      inference('clc', [status(thm)], ['57', '58'])).
% 0.50/0.72  thf(t139_funct_1, axiom,
% 0.50/0.72    (![A:$i,B:$i,C:$i]:
% 0.50/0.72     ( ( v1_relat_1 @ C ) =>
% 0.50/0.72       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.50/0.72         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.50/0.72  thf('60', plain,
% 0.50/0.72      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.50/0.72         (((k10_relat_1 @ (k7_relat_1 @ X16 @ X15) @ X17)
% 0.50/0.72            = (k3_xboole_0 @ X15 @ (k10_relat_1 @ X16 @ X17)))
% 0.50/0.72          | ~ (v1_relat_1 @ X16))),
% 0.50/0.72      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.50/0.72  thf('61', plain,
% 0.50/0.72      (![X0 : $i, X1 : $i]:
% 0.50/0.72         (((k1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.50/0.72            = (k3_xboole_0 @ X0 @ (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0))))
% 0.50/0.72          | ~ (v1_relat_1 @ X1)
% 0.50/0.72          | ~ (v1_relat_1 @ X1))),
% 0.50/0.72      inference('sup+', [status(thm)], ['59', '60'])).
% 0.50/0.72  thf('62', plain,
% 0.50/0.72      (![X0 : $i, X1 : $i]:
% 0.50/0.72         (~ (v1_relat_1 @ X1)
% 0.50/0.72          | ((k1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.50/0.72              = (k3_xboole_0 @ X0 @ (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0)))))),
% 0.50/0.72      inference('simplify', [status(thm)], ['61'])).
% 0.50/0.72  thf('63', plain, (![X0 : $i]: (r1_tarski @ (k3_xboole_0 @ sk_A @ X0) @ X0)),
% 0.50/0.72      inference('demod', [status(thm)], ['29', '30'])).
% 0.50/0.72  thf('64', plain,
% 0.50/0.72      (![X0 : $i]:
% 0.50/0.72         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X0 @ sk_A)) @ 
% 0.50/0.72           (k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ sk_A)))
% 0.50/0.72          | ~ (v1_relat_1 @ X0))),
% 0.50/0.72      inference('sup+', [status(thm)], ['62', '63'])).
% 0.50/0.72  thf('65', plain,
% 0.50/0.72      (((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 0.50/0.72        | ~ (v1_relat_1 @ sk_B))),
% 0.50/0.72      inference('sup+', [status(thm)], ['54', '64'])).
% 0.50/0.72  thf('66', plain, ((v1_relat_1 @ sk_B)),
% 0.50/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.72  thf('67', plain,
% 0.50/0.72      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 0.50/0.72      inference('demod', [status(thm)], ['65', '66'])).
% 0.50/0.72  thf('68', plain, ($false), inference('demod', [status(thm)], ['0', '67'])).
% 0.50/0.72  
% 0.50/0.72  % SZS output end Refutation
% 0.50/0.72  
% 0.50/0.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
