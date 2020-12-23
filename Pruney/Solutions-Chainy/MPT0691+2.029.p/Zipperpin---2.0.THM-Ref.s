%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rIxp7R0Gzf

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:21 EST 2020

% Result     : Theorem 1.50s
% Output     : Refutation 1.50s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 359 expanded)
%              Number of leaves         :   24 ( 117 expanded)
%              Depth                    :   28
%              Number of atoms          :  909 (3250 expanded)
%              Number of equality atoms :   53 ( 158 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

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

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X20 @ X21 ) )
        = ( k9_relat_1 @ X20 @ X21 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('2',plain,(
    ! [X24: $i] :
      ( ( ( k10_relat_1 @ X24 @ ( k2_relat_1 @ X24 ) )
        = ( k1_relat_1 @ X24 ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['3','4'])).

thf('6',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('7',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_xboole_0 @ X16 @ X17 )
        = X16 )
      | ~ ( r1_tarski @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('8',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) )
    = sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X24: $i] :
      ( ( ( k10_relat_1 @ X24 @ ( k2_relat_1 @ X24 ) )
        = ( k1_relat_1 @ X24 ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('10',plain,(
    ! [X24: $i] :
      ( ( ( k10_relat_1 @ X24 @ ( k2_relat_1 @ X24 ) )
        = ( k1_relat_1 @ X24 ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('11',plain,(
    ! [X22: $i,X23: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X22 @ X23 ) @ ( k1_relat_1 @ X22 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('12',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_xboole_0 @ X16 @ X17 )
        = X16 )
      | ~ ( r1_tarski @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k3_xboole_0 @ ( k10_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) )
        = ( k10_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k3_xboole_0 @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ X1 ) )
        = ( k10_relat_1 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(t139_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('16',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X31 @ X30 ) @ X32 )
        = ( k3_xboole_0 @ X30 @ ( k10_relat_1 @ X31 @ X32 ) ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('17',plain,(
    ! [X22: $i,X23: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X22 @ X23 ) @ ( k1_relat_1 @ X22 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) ) ) ),
    inference(clc,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X1 @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ ( k1_relat_1 @ X1 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['15','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k10_relat_1 @ X1 @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ ( k1_relat_1 @ X1 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('25',plain,(
    ! [X28: $i,X29: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X28 @ X29 ) ) @ X29 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('26',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ( X0
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('31',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('32',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_xboole_0 @ X12 @ X11 )
        = X11 )
      | ~ ( r1_tarski @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('33',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('34',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X8 @ X10 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ X0 )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r1_tarski @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['30','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_xboole_0 @ X12 @ X11 )
        = X11 )
      | ~ ( r1_tarski @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('40',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) ) ) )
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( ( k2_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['29','40'])).

thf('42',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('43',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k10_relat_1 @ X1 @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ ( k1_relat_1 @ X1 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ sk_B @ X0 ) @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k10_relat_1 @ sk_B @ X0 ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k10_relat_1 @ sk_B @ X0 ) )
      | ( ( k1_relat_1 @ sk_B )
        = ( k10_relat_1 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ( ( k1_relat_1 @ sk_B )
      = ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['9','50'])).

thf('52',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('53',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['51','53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) ) ) ),
    inference(clc,[status(thm)],['18','19'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X0 @ ( k1_relat_1 @ sk_B ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ ( k1_relat_1 @ sk_B ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['8','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ( X0
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('62',plain,
    ( ( sk_A
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( sk_A
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X31 @ X30 ) @ X32 )
        = ( k3_xboole_0 @ X30 @ ( k10_relat_1 @ X31 @ X32 ) ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k3_xboole_0 @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ X1 ) )
        = ( k10_relat_1 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) )
        = ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k3_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) )
        = ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) @ X0 ) ) ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ X0 ) ) )
        = ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['64','69'])).

thf('71',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['52'])).

thf(t18_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf('72',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ~ ( r1_tarski @ X13 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t18_xboole_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_xboole_0 @ X16 @ X17 )
        = X16 )
      | ~ ( r1_tarski @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ X0 ) )
      = ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['70','77','78'])).

thf('80',plain,
    ( ( ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['5','79'])).

thf('81',plain,
    ( sk_A
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('82',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    = sk_A ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('84',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['52'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('86',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ~ ( r1_tarski @ X13 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t18_xboole_1])).

thf('87',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['84','87'])).

thf('89',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['83','88'])).

thf('90',plain,(
    $false ),
    inference(demod,[status(thm)],['0','89'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rIxp7R0Gzf
% 0.12/0.33  % Computer   : n023.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:04:21 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 1.50/1.69  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.50/1.69  % Solved by: fo/fo7.sh
% 1.50/1.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.50/1.69  % done 2700 iterations in 1.244s
% 1.50/1.69  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.50/1.69  % SZS output start Refutation
% 1.50/1.69  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.50/1.69  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.50/1.69  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 1.50/1.69  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.50/1.69  thf(sk_B_type, type, sk_B: $i).
% 1.50/1.69  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.50/1.69  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.50/1.69  thf(sk_A_type, type, sk_A: $i).
% 1.50/1.69  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.50/1.69  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 1.50/1.69  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.50/1.69  thf(t146_funct_1, conjecture,
% 1.50/1.69    (![A:$i,B:$i]:
% 1.50/1.69     ( ( v1_relat_1 @ B ) =>
% 1.50/1.69       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 1.50/1.69         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 1.50/1.69  thf(zf_stmt_0, negated_conjecture,
% 1.50/1.69    (~( ![A:$i,B:$i]:
% 1.50/1.69        ( ( v1_relat_1 @ B ) =>
% 1.50/1.69          ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 1.50/1.69            ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )),
% 1.50/1.69    inference('cnf.neg', [status(esa)], [t146_funct_1])).
% 1.50/1.69  thf('0', plain,
% 1.50/1.69      (~ (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 1.50/1.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.69  thf(t148_relat_1, axiom,
% 1.50/1.69    (![A:$i,B:$i]:
% 1.50/1.69     ( ( v1_relat_1 @ B ) =>
% 1.50/1.69       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 1.50/1.69  thf('1', plain,
% 1.50/1.69      (![X20 : $i, X21 : $i]:
% 1.50/1.69         (((k2_relat_1 @ (k7_relat_1 @ X20 @ X21)) = (k9_relat_1 @ X20 @ X21))
% 1.50/1.69          | ~ (v1_relat_1 @ X20))),
% 1.50/1.69      inference('cnf', [status(esa)], [t148_relat_1])).
% 1.50/1.69  thf(t169_relat_1, axiom,
% 1.50/1.69    (![A:$i]:
% 1.50/1.69     ( ( v1_relat_1 @ A ) =>
% 1.50/1.69       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 1.50/1.69  thf('2', plain,
% 1.50/1.69      (![X24 : $i]:
% 1.50/1.69         (((k10_relat_1 @ X24 @ (k2_relat_1 @ X24)) = (k1_relat_1 @ X24))
% 1.50/1.69          | ~ (v1_relat_1 @ X24))),
% 1.50/1.69      inference('cnf', [status(esa)], [t169_relat_1])).
% 1.50/1.69  thf('3', plain,
% 1.50/1.69      (![X0 : $i, X1 : $i]:
% 1.50/1.69         (((k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0))
% 1.50/1.69            = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 1.50/1.69          | ~ (v1_relat_1 @ X1)
% 1.50/1.69          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 1.50/1.69      inference('sup+', [status(thm)], ['1', '2'])).
% 1.50/1.69  thf(dt_k7_relat_1, axiom,
% 1.50/1.69    (![A:$i,B:$i]:
% 1.50/1.69     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 1.50/1.69  thf('4', plain,
% 1.50/1.69      (![X18 : $i, X19 : $i]:
% 1.50/1.69         (~ (v1_relat_1 @ X18) | (v1_relat_1 @ (k7_relat_1 @ X18 @ X19)))),
% 1.50/1.69      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 1.50/1.69  thf('5', plain,
% 1.50/1.69      (![X0 : $i, X1 : $i]:
% 1.50/1.69         (~ (v1_relat_1 @ X1)
% 1.50/1.69          | ((k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0))
% 1.50/1.69              = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 1.50/1.69      inference('clc', [status(thm)], ['3', '4'])).
% 1.50/1.69  thf('6', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 1.50/1.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.69  thf(t28_xboole_1, axiom,
% 1.50/1.69    (![A:$i,B:$i]:
% 1.50/1.69     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.50/1.69  thf('7', plain,
% 1.50/1.69      (![X16 : $i, X17 : $i]:
% 1.50/1.69         (((k3_xboole_0 @ X16 @ X17) = (X16)) | ~ (r1_tarski @ X16 @ X17))),
% 1.50/1.69      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.50/1.69  thf('8', plain, (((k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)) = (sk_A))),
% 1.50/1.69      inference('sup-', [status(thm)], ['6', '7'])).
% 1.50/1.69  thf('9', plain,
% 1.50/1.69      (![X24 : $i]:
% 1.50/1.69         (((k10_relat_1 @ X24 @ (k2_relat_1 @ X24)) = (k1_relat_1 @ X24))
% 1.50/1.69          | ~ (v1_relat_1 @ X24))),
% 1.50/1.69      inference('cnf', [status(esa)], [t169_relat_1])).
% 1.50/1.69  thf('10', plain,
% 1.50/1.69      (![X24 : $i]:
% 1.50/1.69         (((k10_relat_1 @ X24 @ (k2_relat_1 @ X24)) = (k1_relat_1 @ X24))
% 1.50/1.69          | ~ (v1_relat_1 @ X24))),
% 1.50/1.69      inference('cnf', [status(esa)], [t169_relat_1])).
% 1.50/1.69  thf(t167_relat_1, axiom,
% 1.50/1.69    (![A:$i,B:$i]:
% 1.50/1.69     ( ( v1_relat_1 @ B ) =>
% 1.50/1.69       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 1.50/1.69  thf('11', plain,
% 1.50/1.69      (![X22 : $i, X23 : $i]:
% 1.50/1.69         ((r1_tarski @ (k10_relat_1 @ X22 @ X23) @ (k1_relat_1 @ X22))
% 1.50/1.69          | ~ (v1_relat_1 @ X22))),
% 1.50/1.69      inference('cnf', [status(esa)], [t167_relat_1])).
% 1.50/1.69  thf('12', plain,
% 1.50/1.69      (![X16 : $i, X17 : $i]:
% 1.50/1.69         (((k3_xboole_0 @ X16 @ X17) = (X16)) | ~ (r1_tarski @ X16 @ X17))),
% 1.50/1.69      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.50/1.69  thf('13', plain,
% 1.50/1.69      (![X0 : $i, X1 : $i]:
% 1.50/1.69         (~ (v1_relat_1 @ X0)
% 1.50/1.69          | ((k3_xboole_0 @ (k10_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0))
% 1.50/1.69              = (k10_relat_1 @ X0 @ X1)))),
% 1.50/1.69      inference('sup-', [status(thm)], ['11', '12'])).
% 1.50/1.69  thf(commutativity_k3_xboole_0, axiom,
% 1.50/1.69    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.50/1.69  thf('14', plain,
% 1.50/1.69      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.50/1.69      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.50/1.69  thf('15', plain,
% 1.50/1.69      (![X0 : $i, X1 : $i]:
% 1.50/1.69         (~ (v1_relat_1 @ X0)
% 1.50/1.69          | ((k3_xboole_0 @ (k1_relat_1 @ X0) @ (k10_relat_1 @ X0 @ X1))
% 1.50/1.69              = (k10_relat_1 @ X0 @ X1)))),
% 1.50/1.69      inference('demod', [status(thm)], ['13', '14'])).
% 1.50/1.69  thf(t139_funct_1, axiom,
% 1.50/1.69    (![A:$i,B:$i,C:$i]:
% 1.50/1.69     ( ( v1_relat_1 @ C ) =>
% 1.50/1.69       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 1.50/1.69         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 1.50/1.69  thf('16', plain,
% 1.50/1.69      (![X30 : $i, X31 : $i, X32 : $i]:
% 1.50/1.69         (((k10_relat_1 @ (k7_relat_1 @ X31 @ X30) @ X32)
% 1.50/1.69            = (k3_xboole_0 @ X30 @ (k10_relat_1 @ X31 @ X32)))
% 1.50/1.69          | ~ (v1_relat_1 @ X31))),
% 1.50/1.69      inference('cnf', [status(esa)], [t139_funct_1])).
% 1.50/1.69  thf('17', plain,
% 1.50/1.69      (![X22 : $i, X23 : $i]:
% 1.50/1.69         ((r1_tarski @ (k10_relat_1 @ X22 @ X23) @ (k1_relat_1 @ X22))
% 1.50/1.69          | ~ (v1_relat_1 @ X22))),
% 1.50/1.69      inference('cnf', [status(esa)], [t167_relat_1])).
% 1.50/1.69  thf('18', plain,
% 1.50/1.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.50/1.69         ((r1_tarski @ (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0)) @ 
% 1.50/1.69           (k1_relat_1 @ (k7_relat_1 @ X1 @ X2)))
% 1.50/1.69          | ~ (v1_relat_1 @ X1)
% 1.50/1.69          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X2)))),
% 1.50/1.69      inference('sup+', [status(thm)], ['16', '17'])).
% 1.50/1.69  thf('19', plain,
% 1.50/1.69      (![X18 : $i, X19 : $i]:
% 1.50/1.69         (~ (v1_relat_1 @ X18) | (v1_relat_1 @ (k7_relat_1 @ X18 @ X19)))),
% 1.50/1.69      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 1.50/1.69  thf('20', plain,
% 1.50/1.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.50/1.69         (~ (v1_relat_1 @ X1)
% 1.50/1.69          | (r1_tarski @ (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0)) @ 
% 1.50/1.69             (k1_relat_1 @ (k7_relat_1 @ X1 @ X2))))),
% 1.50/1.69      inference('clc', [status(thm)], ['18', '19'])).
% 1.50/1.69  thf('21', plain,
% 1.50/1.69      (![X0 : $i, X1 : $i]:
% 1.50/1.69         ((r1_tarski @ (k10_relat_1 @ X1 @ X0) @ 
% 1.50/1.69           (k1_relat_1 @ (k7_relat_1 @ X1 @ (k1_relat_1 @ X1))))
% 1.50/1.69          | ~ (v1_relat_1 @ X1)
% 1.50/1.69          | ~ (v1_relat_1 @ X1))),
% 1.50/1.69      inference('sup+', [status(thm)], ['15', '20'])).
% 1.50/1.69  thf('22', plain,
% 1.50/1.69      (![X0 : $i, X1 : $i]:
% 1.50/1.69         (~ (v1_relat_1 @ X1)
% 1.50/1.69          | (r1_tarski @ (k10_relat_1 @ X1 @ X0) @ 
% 1.50/1.69             (k1_relat_1 @ (k7_relat_1 @ X1 @ (k1_relat_1 @ X1)))))),
% 1.50/1.69      inference('simplify', [status(thm)], ['21'])).
% 1.50/1.69  thf('23', plain,
% 1.50/1.69      (![X0 : $i]:
% 1.50/1.69         ((r1_tarski @ (k1_relat_1 @ X0) @ 
% 1.50/1.69           (k1_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X0))))
% 1.50/1.69          | ~ (v1_relat_1 @ X0)
% 1.50/1.69          | ~ (v1_relat_1 @ X0))),
% 1.50/1.69      inference('sup+', [status(thm)], ['10', '22'])).
% 1.50/1.69  thf('24', plain,
% 1.50/1.69      (![X0 : $i]:
% 1.50/1.69         (~ (v1_relat_1 @ X0)
% 1.50/1.69          | (r1_tarski @ (k1_relat_1 @ X0) @ 
% 1.50/1.69             (k1_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X0)))))),
% 1.50/1.69      inference('simplify', [status(thm)], ['23'])).
% 1.50/1.69  thf(t87_relat_1, axiom,
% 1.50/1.69    (![A:$i,B:$i]:
% 1.50/1.69     ( ( v1_relat_1 @ B ) =>
% 1.50/1.69       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 1.50/1.69  thf('25', plain,
% 1.50/1.69      (![X28 : $i, X29 : $i]:
% 1.50/1.69         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X28 @ X29)) @ X29)
% 1.50/1.69          | ~ (v1_relat_1 @ X28))),
% 1.50/1.69      inference('cnf', [status(esa)], [t87_relat_1])).
% 1.50/1.69  thf(d10_xboole_0, axiom,
% 1.50/1.69    (![A:$i,B:$i]:
% 1.50/1.69     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.50/1.69  thf('26', plain,
% 1.50/1.69      (![X2 : $i, X4 : $i]:
% 1.50/1.69         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 1.50/1.69      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.50/1.69  thf('27', plain,
% 1.50/1.69      (![X0 : $i, X1 : $i]:
% 1.50/1.69         (~ (v1_relat_1 @ X1)
% 1.50/1.69          | ~ (r1_tarski @ X0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 1.50/1.69          | ((X0) = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 1.50/1.69      inference('sup-', [status(thm)], ['25', '26'])).
% 1.50/1.69  thf('28', plain,
% 1.50/1.69      (![X0 : $i]:
% 1.50/1.69         (~ (v1_relat_1 @ X0)
% 1.50/1.69          | ((k1_relat_1 @ X0)
% 1.50/1.69              = (k1_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X0))))
% 1.50/1.69          | ~ (v1_relat_1 @ X0))),
% 1.50/1.69      inference('sup-', [status(thm)], ['24', '27'])).
% 1.50/1.69  thf('29', plain,
% 1.50/1.69      (![X0 : $i]:
% 1.50/1.69         (((k1_relat_1 @ X0)
% 1.50/1.69            = (k1_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X0))))
% 1.50/1.69          | ~ (v1_relat_1 @ X0))),
% 1.50/1.69      inference('simplify', [status(thm)], ['28'])).
% 1.50/1.69  thf('30', plain,
% 1.50/1.69      (![X0 : $i]:
% 1.50/1.69         (~ (v1_relat_1 @ X0)
% 1.50/1.69          | (r1_tarski @ (k1_relat_1 @ X0) @ 
% 1.50/1.69             (k1_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X0)))))),
% 1.50/1.69      inference('simplify', [status(thm)], ['23'])).
% 1.50/1.69  thf('31', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 1.50/1.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.69  thf(t12_xboole_1, axiom,
% 1.50/1.69    (![A:$i,B:$i]:
% 1.50/1.69     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 1.50/1.69  thf('32', plain,
% 1.50/1.69      (![X11 : $i, X12 : $i]:
% 1.50/1.69         (((k2_xboole_0 @ X12 @ X11) = (X11)) | ~ (r1_tarski @ X12 @ X11))),
% 1.50/1.69      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.50/1.69  thf('33', plain,
% 1.50/1.69      (((k2_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)) = (k1_relat_1 @ sk_B))),
% 1.50/1.69      inference('sup-', [status(thm)], ['31', '32'])).
% 1.50/1.69  thf(t11_xboole_1, axiom,
% 1.50/1.69    (![A:$i,B:$i,C:$i]:
% 1.50/1.69     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 1.50/1.69  thf('34', plain,
% 1.50/1.69      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.50/1.69         ((r1_tarski @ X8 @ X9) | ~ (r1_tarski @ (k2_xboole_0 @ X8 @ X10) @ X9))),
% 1.50/1.69      inference('cnf', [status(esa)], [t11_xboole_1])).
% 1.50/1.69  thf('35', plain,
% 1.50/1.69      (![X0 : $i]:
% 1.50/1.69         (~ (r1_tarski @ (k1_relat_1 @ sk_B) @ X0) | (r1_tarski @ sk_A @ X0))),
% 1.50/1.69      inference('sup-', [status(thm)], ['33', '34'])).
% 1.50/1.69  thf('36', plain,
% 1.50/1.69      ((~ (v1_relat_1 @ sk_B)
% 1.50/1.69        | (r1_tarski @ sk_A @ 
% 1.50/1.69           (k1_relat_1 @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_B)))))),
% 1.50/1.69      inference('sup-', [status(thm)], ['30', '35'])).
% 1.50/1.69  thf('37', plain, ((v1_relat_1 @ sk_B)),
% 1.50/1.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.69  thf('38', plain,
% 1.50/1.69      ((r1_tarski @ sk_A @ 
% 1.50/1.69        (k1_relat_1 @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_B))))),
% 1.50/1.69      inference('demod', [status(thm)], ['36', '37'])).
% 1.50/1.69  thf('39', plain,
% 1.50/1.69      (![X11 : $i, X12 : $i]:
% 1.50/1.69         (((k2_xboole_0 @ X12 @ X11) = (X11)) | ~ (r1_tarski @ X12 @ X11))),
% 1.50/1.69      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.50/1.69  thf('40', plain,
% 1.50/1.69      (((k2_xboole_0 @ sk_A @ 
% 1.50/1.69         (k1_relat_1 @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_B))))
% 1.50/1.69         = (k1_relat_1 @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_B))))),
% 1.50/1.69      inference('sup-', [status(thm)], ['38', '39'])).
% 1.50/1.69  thf('41', plain,
% 1.50/1.69      ((((k2_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B))
% 1.50/1.69          = (k1_relat_1 @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_B))))
% 1.50/1.69        | ~ (v1_relat_1 @ sk_B))),
% 1.50/1.69      inference('sup+', [status(thm)], ['29', '40'])).
% 1.50/1.69  thf('42', plain,
% 1.50/1.69      (((k2_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)) = (k1_relat_1 @ sk_B))),
% 1.50/1.69      inference('sup-', [status(thm)], ['31', '32'])).
% 1.50/1.69  thf('43', plain, ((v1_relat_1 @ sk_B)),
% 1.50/1.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.69  thf('44', plain,
% 1.50/1.69      (((k1_relat_1 @ sk_B)
% 1.50/1.69         = (k1_relat_1 @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_B))))),
% 1.50/1.69      inference('demod', [status(thm)], ['41', '42', '43'])).
% 1.50/1.69  thf('45', plain,
% 1.50/1.69      (![X0 : $i, X1 : $i]:
% 1.50/1.69         (~ (v1_relat_1 @ X1)
% 1.50/1.69          | (r1_tarski @ (k10_relat_1 @ X1 @ X0) @ 
% 1.50/1.69             (k1_relat_1 @ (k7_relat_1 @ X1 @ (k1_relat_1 @ X1)))))),
% 1.50/1.69      inference('simplify', [status(thm)], ['21'])).
% 1.50/1.69  thf('46', plain,
% 1.50/1.69      (![X0 : $i]:
% 1.50/1.69         ((r1_tarski @ (k10_relat_1 @ sk_B @ X0) @ (k1_relat_1 @ sk_B))
% 1.50/1.69          | ~ (v1_relat_1 @ sk_B))),
% 1.50/1.69      inference('sup+', [status(thm)], ['44', '45'])).
% 1.50/1.69  thf('47', plain, ((v1_relat_1 @ sk_B)),
% 1.50/1.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.69  thf('48', plain,
% 1.50/1.69      (![X0 : $i]:
% 1.50/1.69         (r1_tarski @ (k10_relat_1 @ sk_B @ X0) @ (k1_relat_1 @ sk_B))),
% 1.50/1.69      inference('demod', [status(thm)], ['46', '47'])).
% 1.50/1.69  thf('49', plain,
% 1.50/1.69      (![X2 : $i, X4 : $i]:
% 1.50/1.69         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 1.50/1.69      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.50/1.69  thf('50', plain,
% 1.50/1.69      (![X0 : $i]:
% 1.50/1.69         (~ (r1_tarski @ (k1_relat_1 @ sk_B) @ (k10_relat_1 @ sk_B @ X0))
% 1.50/1.69          | ((k1_relat_1 @ sk_B) = (k10_relat_1 @ sk_B @ X0)))),
% 1.50/1.69      inference('sup-', [status(thm)], ['48', '49'])).
% 1.50/1.69  thf('51', plain,
% 1.50/1.69      ((~ (r1_tarski @ (k1_relat_1 @ sk_B) @ (k1_relat_1 @ sk_B))
% 1.50/1.69        | ~ (v1_relat_1 @ sk_B)
% 1.50/1.69        | ((k1_relat_1 @ sk_B) = (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B))))),
% 1.50/1.69      inference('sup-', [status(thm)], ['9', '50'])).
% 1.50/1.69  thf('52', plain,
% 1.50/1.69      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 1.50/1.69      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.50/1.69  thf('53', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 1.50/1.69      inference('simplify', [status(thm)], ['52'])).
% 1.50/1.69  thf('54', plain, ((v1_relat_1 @ sk_B)),
% 1.50/1.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.69  thf('55', plain,
% 1.50/1.69      (((k1_relat_1 @ sk_B) = (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B)))),
% 1.50/1.69      inference('demod', [status(thm)], ['51', '53', '54'])).
% 1.50/1.69  thf('56', plain,
% 1.50/1.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.50/1.69         (~ (v1_relat_1 @ X1)
% 1.50/1.69          | (r1_tarski @ (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0)) @ 
% 1.50/1.69             (k1_relat_1 @ (k7_relat_1 @ X1 @ X2))))),
% 1.50/1.69      inference('clc', [status(thm)], ['18', '19'])).
% 1.50/1.69  thf('57', plain,
% 1.50/1.69      (![X0 : $i]:
% 1.50/1.69         ((r1_tarski @ (k3_xboole_0 @ X0 @ (k1_relat_1 @ sk_B)) @ 
% 1.50/1.69           (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)))
% 1.50/1.69          | ~ (v1_relat_1 @ sk_B))),
% 1.50/1.69      inference('sup+', [status(thm)], ['55', '56'])).
% 1.50/1.69  thf('58', plain, ((v1_relat_1 @ sk_B)),
% 1.50/1.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.69  thf('59', plain,
% 1.50/1.69      (![X0 : $i]:
% 1.50/1.69         (r1_tarski @ (k3_xboole_0 @ X0 @ (k1_relat_1 @ sk_B)) @ 
% 1.50/1.69          (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)))),
% 1.50/1.69      inference('demod', [status(thm)], ['57', '58'])).
% 1.50/1.69  thf('60', plain,
% 1.50/1.69      ((r1_tarski @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 1.50/1.69      inference('sup+', [status(thm)], ['8', '59'])).
% 1.50/1.69  thf('61', plain,
% 1.50/1.69      (![X0 : $i, X1 : $i]:
% 1.50/1.69         (~ (v1_relat_1 @ X1)
% 1.50/1.69          | ~ (r1_tarski @ X0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 1.50/1.69          | ((X0) = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 1.50/1.69      inference('sup-', [status(thm)], ['25', '26'])).
% 1.50/1.69  thf('62', plain,
% 1.50/1.69      ((((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 1.50/1.69        | ~ (v1_relat_1 @ sk_B))),
% 1.50/1.69      inference('sup-', [status(thm)], ['60', '61'])).
% 1.50/1.69  thf('63', plain, ((v1_relat_1 @ sk_B)),
% 1.50/1.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.69  thf('64', plain, (((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 1.50/1.69      inference('demod', [status(thm)], ['62', '63'])).
% 1.50/1.69  thf('65', plain,
% 1.50/1.69      (![X30 : $i, X31 : $i, X32 : $i]:
% 1.50/1.69         (((k10_relat_1 @ (k7_relat_1 @ X31 @ X30) @ X32)
% 1.50/1.69            = (k3_xboole_0 @ X30 @ (k10_relat_1 @ X31 @ X32)))
% 1.50/1.69          | ~ (v1_relat_1 @ X31))),
% 1.50/1.69      inference('cnf', [status(esa)], [t139_funct_1])).
% 1.50/1.69  thf('66', plain,
% 1.50/1.69      (![X0 : $i, X1 : $i]:
% 1.50/1.69         (~ (v1_relat_1 @ X0)
% 1.50/1.69          | ((k3_xboole_0 @ (k1_relat_1 @ X0) @ (k10_relat_1 @ X0 @ X1))
% 1.50/1.69              = (k10_relat_1 @ X0 @ X1)))),
% 1.50/1.69      inference('demod', [status(thm)], ['13', '14'])).
% 1.50/1.69  thf('67', plain,
% 1.50/1.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.50/1.69         (((k3_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X2)) @ 
% 1.50/1.69            (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0)))
% 1.50/1.69            = (k10_relat_1 @ (k7_relat_1 @ X1 @ X2) @ X0))
% 1.50/1.69          | ~ (v1_relat_1 @ X1)
% 1.50/1.69          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X2)))),
% 1.50/1.69      inference('sup+', [status(thm)], ['65', '66'])).
% 1.50/1.69  thf('68', plain,
% 1.50/1.69      (![X18 : $i, X19 : $i]:
% 1.50/1.69         (~ (v1_relat_1 @ X18) | (v1_relat_1 @ (k7_relat_1 @ X18 @ X19)))),
% 1.50/1.69      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 1.50/1.69  thf('69', plain,
% 1.50/1.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.50/1.69         (~ (v1_relat_1 @ X1)
% 1.50/1.69          | ((k3_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X2)) @ 
% 1.50/1.69              (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0)))
% 1.50/1.69              = (k10_relat_1 @ (k7_relat_1 @ X1 @ X2) @ X0)))),
% 1.50/1.69      inference('clc', [status(thm)], ['67', '68'])).
% 1.50/1.69  thf('70', plain,
% 1.50/1.69      (![X0 : $i]:
% 1.50/1.69         (((k3_xboole_0 @ sk_A @ 
% 1.50/1.69            (k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ X0)))
% 1.50/1.69            = (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0))
% 1.50/1.69          | ~ (v1_relat_1 @ sk_B))),
% 1.50/1.69      inference('sup+', [status(thm)], ['64', '69'])).
% 1.50/1.69  thf('71', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 1.50/1.69      inference('simplify', [status(thm)], ['52'])).
% 1.50/1.69  thf(t18_xboole_1, axiom,
% 1.50/1.69    (![A:$i,B:$i,C:$i]:
% 1.50/1.69     ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) => ( r1_tarski @ A @ B ) ))).
% 1.50/1.69  thf('72', plain,
% 1.50/1.69      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.50/1.69         ((r1_tarski @ X13 @ X14)
% 1.50/1.69          | ~ (r1_tarski @ X13 @ (k3_xboole_0 @ X14 @ X15)))),
% 1.50/1.69      inference('cnf', [status(esa)], [t18_xboole_1])).
% 1.50/1.69  thf('73', plain,
% 1.50/1.69      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 1.50/1.69      inference('sup-', [status(thm)], ['71', '72'])).
% 1.50/1.69  thf('74', plain,
% 1.50/1.69      (![X16 : $i, X17 : $i]:
% 1.50/1.69         (((k3_xboole_0 @ X16 @ X17) = (X16)) | ~ (r1_tarski @ X16 @ X17))),
% 1.50/1.69      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.50/1.69  thf('75', plain,
% 1.50/1.69      (![X0 : $i, X1 : $i]:
% 1.50/1.69         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 1.50/1.69           = (k3_xboole_0 @ X0 @ X1))),
% 1.50/1.69      inference('sup-', [status(thm)], ['73', '74'])).
% 1.50/1.69  thf('76', plain,
% 1.50/1.69      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.50/1.69      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.50/1.69  thf('77', plain,
% 1.50/1.69      (![X0 : $i, X1 : $i]:
% 1.50/1.69         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 1.50/1.69           = (k3_xboole_0 @ X0 @ X1))),
% 1.50/1.69      inference('demod', [status(thm)], ['75', '76'])).
% 1.50/1.69  thf('78', plain, ((v1_relat_1 @ sk_B)),
% 1.50/1.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.69  thf('79', plain,
% 1.50/1.69      (![X0 : $i]:
% 1.50/1.69         ((k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ X0))
% 1.50/1.69           = (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0))),
% 1.50/1.69      inference('demod', [status(thm)], ['70', '77', '78'])).
% 1.50/1.69  thf('80', plain,
% 1.50/1.69      ((((k3_xboole_0 @ sk_A @ 
% 1.50/1.69          (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 1.50/1.69          = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 1.50/1.69        | ~ (v1_relat_1 @ sk_B))),
% 1.50/1.69      inference('sup+', [status(thm)], ['5', '79'])).
% 1.50/1.69  thf('81', plain, (((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 1.50/1.69      inference('demod', [status(thm)], ['62', '63'])).
% 1.50/1.69  thf('82', plain, ((v1_relat_1 @ sk_B)),
% 1.50/1.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.69  thf('83', plain,
% 1.50/1.69      (((k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 1.50/1.69         = (sk_A))),
% 1.50/1.69      inference('demod', [status(thm)], ['80', '81', '82'])).
% 1.50/1.69  thf('84', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 1.50/1.69      inference('simplify', [status(thm)], ['52'])).
% 1.50/1.69  thf('85', plain,
% 1.50/1.69      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.50/1.69      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.50/1.69  thf('86', plain,
% 1.50/1.69      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.50/1.69         ((r1_tarski @ X13 @ X14)
% 1.50/1.69          | ~ (r1_tarski @ X13 @ (k3_xboole_0 @ X14 @ X15)))),
% 1.50/1.69      inference('cnf', [status(esa)], [t18_xboole_1])).
% 1.50/1.69  thf('87', plain,
% 1.50/1.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.50/1.69         (~ (r1_tarski @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r1_tarski @ X2 @ X0))),
% 1.50/1.69      inference('sup-', [status(thm)], ['85', '86'])).
% 1.50/1.69  thf('88', plain,
% 1.50/1.69      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 1.50/1.69      inference('sup-', [status(thm)], ['84', '87'])).
% 1.50/1.69  thf('89', plain,
% 1.50/1.69      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 1.50/1.69      inference('sup+', [status(thm)], ['83', '88'])).
% 1.50/1.69  thf('90', plain, ($false), inference('demod', [status(thm)], ['0', '89'])).
% 1.50/1.69  
% 1.50/1.69  % SZS output end Refutation
% 1.50/1.69  
% 1.50/1.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
