%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Bo7YHrMnr5

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:21 EST 2020

% Result     : Theorem 2.25s
% Output     : Refutation 2.25s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 269 expanded)
%              Number of leaves         :   25 (  91 expanded)
%              Depth                    :   23
%              Number of atoms          :  919 (2251 expanded)
%              Number of equality atoms :   54 ( 118 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ! [X23: $i,X24: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X23 @ X24 ) )
        = ( k9_relat_1 @ X23 @ X24 ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('2',plain,(
    ! [X27: $i] :
      ( ( ( k10_relat_1 @ X27 @ ( k2_relat_1 @ X27 ) )
        = ( k1_relat_1 @ X27 ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
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
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X21 @ X22 ) ) ) ),
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
    ! [X27: $i] :
      ( ( ( k10_relat_1 @ X27 @ ( k2_relat_1 @ X27 ) )
        = ( k1_relat_1 @ X27 ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('11',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t108_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ B ) ) )).

thf('12',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ( r1_tarski @ ( k3_xboole_0 @ X5 @ X7 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t108_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_A @ X0 ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_xboole_0 @ X16 @ X17 )
        = X16 )
      | ~ ( r1_tarski @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ sk_A @ X0 ) @ ( k1_relat_1 @ sk_B ) )
      = ( k3_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k3_xboole_0 @ sk_A @ X0 ) )
      = ( k3_xboole_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('18',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('19',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('20',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['19'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('21',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ X18 @ X19 )
      | ~ ( r1_tarski @ X20 @ X19 )
      | ( r1_tarski @ ( k2_xboole_0 @ X18 @ X20 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['18','22'])).

thf('24',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['19'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('25',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X8 @ X10 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['23','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k3_xboole_0 @ sk_A @ X0 ) )
      = ( k1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['17','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k3_xboole_0 @ X0 @ sk_A ) )
      = ( k1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['10','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('33',plain,(
    ! [X25: $i,X26: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X25 @ X26 ) @ ( k1_relat_1 @ X25 ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('34',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X13 @ X14 )
      | ~ ( r1_tarski @ X14 @ X15 )
      | ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X1 @ X2 ) @ ( k2_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ sk_B @ X1 ) @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['31','36'])).

thf('38',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X1: $i] :
      ( r1_tarski @ ( k10_relat_1 @ sk_B @ X1 ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k10_relat_1 @ sk_B @ X0 ) )
      | ( ( k1_relat_1 @ sk_B )
        = ( k10_relat_1 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ( ( k1_relat_1 @ sk_B )
      = ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['9','41'])).

thf('43',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['19'])).

thf('44',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf(t139_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('46',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X29 @ X28 ) @ X30 )
        = ( k3_xboole_0 @ X28 @ ( k10_relat_1 @ X29 @ X30 ) ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('47',plain,(
    ! [X25: $i,X26: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X25 @ X26 ) @ ( k1_relat_1 @ X25 ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X0 @ ( k1_relat_1 @ sk_B ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['45','50'])).

thf('52',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ ( k1_relat_1 @ sk_B ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['8','53'])).

thf('55',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X29 @ X28 ) @ X30 )
        = ( k3_xboole_0 @ X28 @ ( k10_relat_1 @ X29 @ X30 ) ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('56',plain,(
    ! [X27: $i] :
      ( ( ( k10_relat_1 @ X27 @ ( k2_relat_1 @ X27 ) )
        = ( k1_relat_1 @ X27 ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ( X0
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( sk_A
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['54','63'])).

thf('65',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( sk_A
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X29 @ X28 ) @ X30 )
        = ( k3_xboole_0 @ X28 @ ( k10_relat_1 @ X29 @ X30 ) ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('68',plain,(
    ! [X25: $i,X26: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X25 @ X26 ) @ ( k1_relat_1 @ X25 ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('69',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_xboole_0 @ X16 @ X17 )
        = X16 )
      | ~ ( r1_tarski @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k3_xboole_0 @ ( k10_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) )
        = ( k10_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k3_xboole_0 @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ X1 ) )
        = ( k10_relat_1 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) )
        = ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['67','72'])).

thf('74',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k3_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) )
        = ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) @ X0 ) ) ) ),
    inference(clc,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ X0 ) ) )
        = ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['66','75'])).

thf('77',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('78',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_xboole_0 @ X16 @ X17 )
        = X16 )
      | ~ ( r1_tarski @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ X0 ) )
      = ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['76','81','82'])).

thf('84',plain,
    ( ( ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['5','83'])).

thf('85',plain,
    ( sk_A
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('86',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    = sk_A ),
    inference(demod,[status(thm)],['84','85','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('89',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('91',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['87','90'])).

thf('92',plain,(
    $false ),
    inference(demod,[status(thm)],['0','91'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Bo7YHrMnr5
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:43:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 2.25/2.42  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.25/2.42  % Solved by: fo/fo7.sh
% 2.25/2.42  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.25/2.42  % done 3660 iterations in 1.957s
% 2.25/2.42  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.25/2.42  % SZS output start Refutation
% 2.25/2.42  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.25/2.42  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.25/2.42  thf(sk_A_type, type, sk_A: $i).
% 2.25/2.42  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 2.25/2.42  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.25/2.42  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 2.25/2.42  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.25/2.42  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.25/2.42  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 2.25/2.42  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.25/2.42  thf(sk_B_type, type, sk_B: $i).
% 2.25/2.42  thf(t146_funct_1, conjecture,
% 2.25/2.42    (![A:$i,B:$i]:
% 2.25/2.42     ( ( v1_relat_1 @ B ) =>
% 2.25/2.42       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 2.25/2.42         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 2.25/2.42  thf(zf_stmt_0, negated_conjecture,
% 2.25/2.42    (~( ![A:$i,B:$i]:
% 2.25/2.42        ( ( v1_relat_1 @ B ) =>
% 2.25/2.42          ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 2.25/2.42            ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )),
% 2.25/2.42    inference('cnf.neg', [status(esa)], [t146_funct_1])).
% 2.25/2.42  thf('0', plain,
% 2.25/2.42      (~ (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 2.25/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.42  thf(t148_relat_1, axiom,
% 2.25/2.42    (![A:$i,B:$i]:
% 2.25/2.42     ( ( v1_relat_1 @ B ) =>
% 2.25/2.42       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 2.25/2.42  thf('1', plain,
% 2.25/2.42      (![X23 : $i, X24 : $i]:
% 2.25/2.42         (((k2_relat_1 @ (k7_relat_1 @ X23 @ X24)) = (k9_relat_1 @ X23 @ X24))
% 2.25/2.42          | ~ (v1_relat_1 @ X23))),
% 2.25/2.42      inference('cnf', [status(esa)], [t148_relat_1])).
% 2.25/2.42  thf(t169_relat_1, axiom,
% 2.25/2.42    (![A:$i]:
% 2.25/2.42     ( ( v1_relat_1 @ A ) =>
% 2.25/2.42       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 2.25/2.42  thf('2', plain,
% 2.25/2.42      (![X27 : $i]:
% 2.25/2.42         (((k10_relat_1 @ X27 @ (k2_relat_1 @ X27)) = (k1_relat_1 @ X27))
% 2.25/2.42          | ~ (v1_relat_1 @ X27))),
% 2.25/2.42      inference('cnf', [status(esa)], [t169_relat_1])).
% 2.25/2.42  thf('3', plain,
% 2.25/2.42      (![X0 : $i, X1 : $i]:
% 2.25/2.42         (((k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0))
% 2.25/2.42            = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 2.25/2.42          | ~ (v1_relat_1 @ X1)
% 2.25/2.42          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 2.25/2.42      inference('sup+', [status(thm)], ['1', '2'])).
% 2.25/2.42  thf(dt_k7_relat_1, axiom,
% 2.25/2.42    (![A:$i,B:$i]:
% 2.25/2.42     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 2.25/2.42  thf('4', plain,
% 2.25/2.42      (![X21 : $i, X22 : $i]:
% 2.25/2.42         (~ (v1_relat_1 @ X21) | (v1_relat_1 @ (k7_relat_1 @ X21 @ X22)))),
% 2.25/2.42      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 2.25/2.42  thf('5', plain,
% 2.25/2.42      (![X0 : $i, X1 : $i]:
% 2.25/2.42         (~ (v1_relat_1 @ X1)
% 2.25/2.42          | ((k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0))
% 2.25/2.42              = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 2.25/2.42      inference('clc', [status(thm)], ['3', '4'])).
% 2.25/2.42  thf('6', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 2.25/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.42  thf(t28_xboole_1, axiom,
% 2.25/2.42    (![A:$i,B:$i]:
% 2.25/2.42     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 2.25/2.42  thf('7', plain,
% 2.25/2.42      (![X16 : $i, X17 : $i]:
% 2.25/2.42         (((k3_xboole_0 @ X16 @ X17) = (X16)) | ~ (r1_tarski @ X16 @ X17))),
% 2.25/2.42      inference('cnf', [status(esa)], [t28_xboole_1])).
% 2.25/2.42  thf('8', plain, (((k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)) = (sk_A))),
% 2.25/2.42      inference('sup-', [status(thm)], ['6', '7'])).
% 2.25/2.42  thf('9', plain,
% 2.25/2.42      (![X27 : $i]:
% 2.25/2.42         (((k10_relat_1 @ X27 @ (k2_relat_1 @ X27)) = (k1_relat_1 @ X27))
% 2.25/2.42          | ~ (v1_relat_1 @ X27))),
% 2.25/2.42      inference('cnf', [status(esa)], [t169_relat_1])).
% 2.25/2.42  thf(commutativity_k3_xboole_0, axiom,
% 2.25/2.42    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 2.25/2.42  thf('10', plain,
% 2.25/2.42      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.25/2.42      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.25/2.42  thf('11', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 2.25/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.42  thf(t108_xboole_1, axiom,
% 2.25/2.42    (![A:$i,B:$i,C:$i]:
% 2.25/2.42     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ B ) ))).
% 2.25/2.42  thf('12', plain,
% 2.25/2.42      (![X5 : $i, X6 : $i, X7 : $i]:
% 2.25/2.42         (~ (r1_tarski @ X5 @ X6) | (r1_tarski @ (k3_xboole_0 @ X5 @ X7) @ X6))),
% 2.25/2.42      inference('cnf', [status(esa)], [t108_xboole_1])).
% 2.25/2.42  thf('13', plain,
% 2.25/2.42      (![X0 : $i]:
% 2.25/2.42         (r1_tarski @ (k3_xboole_0 @ sk_A @ X0) @ (k1_relat_1 @ sk_B))),
% 2.25/2.42      inference('sup-', [status(thm)], ['11', '12'])).
% 2.25/2.42  thf('14', plain,
% 2.25/2.42      (![X16 : $i, X17 : $i]:
% 2.25/2.42         (((k3_xboole_0 @ X16 @ X17) = (X16)) | ~ (r1_tarski @ X16 @ X17))),
% 2.25/2.42      inference('cnf', [status(esa)], [t28_xboole_1])).
% 2.25/2.42  thf('15', plain,
% 2.25/2.42      (![X0 : $i]:
% 2.25/2.42         ((k3_xboole_0 @ (k3_xboole_0 @ sk_A @ X0) @ (k1_relat_1 @ sk_B))
% 2.25/2.42           = (k3_xboole_0 @ sk_A @ X0))),
% 2.25/2.42      inference('sup-', [status(thm)], ['13', '14'])).
% 2.25/2.42  thf('16', plain,
% 2.25/2.42      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.25/2.42      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.25/2.42  thf('17', plain,
% 2.25/2.42      (![X0 : $i]:
% 2.25/2.42         ((k3_xboole_0 @ (k1_relat_1 @ sk_B) @ (k3_xboole_0 @ sk_A @ X0))
% 2.25/2.42           = (k3_xboole_0 @ sk_A @ X0))),
% 2.25/2.42      inference('demod', [status(thm)], ['15', '16'])).
% 2.25/2.42  thf(t17_xboole_1, axiom,
% 2.25/2.42    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 2.25/2.42  thf('18', plain,
% 2.25/2.42      (![X11 : $i, X12 : $i]: (r1_tarski @ (k3_xboole_0 @ X11 @ X12) @ X11)),
% 2.25/2.42      inference('cnf', [status(esa)], [t17_xboole_1])).
% 2.25/2.42  thf(d10_xboole_0, axiom,
% 2.25/2.42    (![A:$i,B:$i]:
% 2.25/2.42     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.25/2.42  thf('19', plain,
% 2.25/2.42      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 2.25/2.42      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.25/2.42  thf('20', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 2.25/2.42      inference('simplify', [status(thm)], ['19'])).
% 2.25/2.42  thf(t8_xboole_1, axiom,
% 2.25/2.42    (![A:$i,B:$i,C:$i]:
% 2.25/2.42     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 2.25/2.42       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 2.25/2.42  thf('21', plain,
% 2.25/2.42      (![X18 : $i, X19 : $i, X20 : $i]:
% 2.25/2.42         (~ (r1_tarski @ X18 @ X19)
% 2.25/2.42          | ~ (r1_tarski @ X20 @ X19)
% 2.25/2.42          | (r1_tarski @ (k2_xboole_0 @ X18 @ X20) @ X19))),
% 2.25/2.42      inference('cnf', [status(esa)], [t8_xboole_1])).
% 2.25/2.42  thf('22', plain,
% 2.25/2.42      (![X0 : $i, X1 : $i]:
% 2.25/2.42         ((r1_tarski @ (k2_xboole_0 @ X0 @ X1) @ X0) | ~ (r1_tarski @ X1 @ X0))),
% 2.25/2.42      inference('sup-', [status(thm)], ['20', '21'])).
% 2.25/2.42  thf('23', plain,
% 2.25/2.42      (![X0 : $i, X1 : $i]:
% 2.25/2.42         (r1_tarski @ (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)) @ X0)),
% 2.25/2.42      inference('sup-', [status(thm)], ['18', '22'])).
% 2.25/2.42  thf('24', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 2.25/2.42      inference('simplify', [status(thm)], ['19'])).
% 2.25/2.42  thf(t11_xboole_1, axiom,
% 2.25/2.42    (![A:$i,B:$i,C:$i]:
% 2.25/2.42     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 2.25/2.42  thf('25', plain,
% 2.25/2.42      (![X8 : $i, X9 : $i, X10 : $i]:
% 2.25/2.42         ((r1_tarski @ X8 @ X9) | ~ (r1_tarski @ (k2_xboole_0 @ X8 @ X10) @ X9))),
% 2.25/2.42      inference('cnf', [status(esa)], [t11_xboole_1])).
% 2.25/2.42  thf('26', plain,
% 2.25/2.42      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 2.25/2.42      inference('sup-', [status(thm)], ['24', '25'])).
% 2.25/2.42  thf('27', plain,
% 2.25/2.42      (![X2 : $i, X4 : $i]:
% 2.25/2.42         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 2.25/2.42      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.25/2.42  thf('28', plain,
% 2.25/2.42      (![X0 : $i, X1 : $i]:
% 2.25/2.42         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 2.25/2.42          | ((k2_xboole_0 @ X1 @ X0) = (X1)))),
% 2.25/2.42      inference('sup-', [status(thm)], ['26', '27'])).
% 2.25/2.42  thf('29', plain,
% 2.25/2.42      (![X0 : $i, X1 : $i]:
% 2.25/2.42         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)) = (X0))),
% 2.25/2.42      inference('sup-', [status(thm)], ['23', '28'])).
% 2.25/2.42  thf('30', plain,
% 2.25/2.42      (![X0 : $i]:
% 2.25/2.42         ((k2_xboole_0 @ (k1_relat_1 @ sk_B) @ (k3_xboole_0 @ sk_A @ X0))
% 2.25/2.42           = (k1_relat_1 @ sk_B))),
% 2.25/2.42      inference('sup+', [status(thm)], ['17', '29'])).
% 2.25/2.42  thf('31', plain,
% 2.25/2.42      (![X0 : $i]:
% 2.25/2.42         ((k2_xboole_0 @ (k1_relat_1 @ sk_B) @ (k3_xboole_0 @ X0 @ sk_A))
% 2.25/2.42           = (k1_relat_1 @ sk_B))),
% 2.25/2.42      inference('sup+', [status(thm)], ['10', '30'])).
% 2.25/2.42  thf('32', plain,
% 2.25/2.42      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 2.25/2.42      inference('sup-', [status(thm)], ['24', '25'])).
% 2.25/2.42  thf(t167_relat_1, axiom,
% 2.25/2.42    (![A:$i,B:$i]:
% 2.25/2.42     ( ( v1_relat_1 @ B ) =>
% 2.25/2.42       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 2.25/2.42  thf('33', plain,
% 2.25/2.42      (![X25 : $i, X26 : $i]:
% 2.25/2.42         ((r1_tarski @ (k10_relat_1 @ X25 @ X26) @ (k1_relat_1 @ X25))
% 2.25/2.42          | ~ (v1_relat_1 @ X25))),
% 2.25/2.42      inference('cnf', [status(esa)], [t167_relat_1])).
% 2.25/2.42  thf(t1_xboole_1, axiom,
% 2.25/2.42    (![A:$i,B:$i,C:$i]:
% 2.25/2.42     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 2.25/2.42       ( r1_tarski @ A @ C ) ))).
% 2.25/2.42  thf('34', plain,
% 2.25/2.42      (![X13 : $i, X14 : $i, X15 : $i]:
% 2.25/2.42         (~ (r1_tarski @ X13 @ X14)
% 2.25/2.42          | ~ (r1_tarski @ X14 @ X15)
% 2.25/2.42          | (r1_tarski @ X13 @ X15))),
% 2.25/2.42      inference('cnf', [status(esa)], [t1_xboole_1])).
% 2.25/2.42  thf('35', plain,
% 2.25/2.42      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.25/2.42         (~ (v1_relat_1 @ X0)
% 2.25/2.42          | (r1_tarski @ (k10_relat_1 @ X0 @ X1) @ X2)
% 2.25/2.42          | ~ (r1_tarski @ (k1_relat_1 @ X0) @ X2))),
% 2.25/2.42      inference('sup-', [status(thm)], ['33', '34'])).
% 2.25/2.42  thf('36', plain,
% 2.25/2.42      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.25/2.42         ((r1_tarski @ (k10_relat_1 @ X1 @ X2) @ 
% 2.25/2.42           (k2_xboole_0 @ (k1_relat_1 @ X1) @ X0))
% 2.25/2.42          | ~ (v1_relat_1 @ X1))),
% 2.25/2.42      inference('sup-', [status(thm)], ['32', '35'])).
% 2.25/2.42  thf('37', plain,
% 2.25/2.42      (![X1 : $i]:
% 2.25/2.42         ((r1_tarski @ (k10_relat_1 @ sk_B @ X1) @ (k1_relat_1 @ sk_B))
% 2.25/2.42          | ~ (v1_relat_1 @ sk_B))),
% 2.25/2.42      inference('sup+', [status(thm)], ['31', '36'])).
% 2.25/2.42  thf('38', plain, ((v1_relat_1 @ sk_B)),
% 2.25/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.42  thf('39', plain,
% 2.25/2.42      (![X1 : $i]:
% 2.25/2.42         (r1_tarski @ (k10_relat_1 @ sk_B @ X1) @ (k1_relat_1 @ sk_B))),
% 2.25/2.42      inference('demod', [status(thm)], ['37', '38'])).
% 2.25/2.42  thf('40', plain,
% 2.25/2.42      (![X2 : $i, X4 : $i]:
% 2.25/2.42         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 2.25/2.42      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.25/2.42  thf('41', plain,
% 2.25/2.42      (![X0 : $i]:
% 2.25/2.42         (~ (r1_tarski @ (k1_relat_1 @ sk_B) @ (k10_relat_1 @ sk_B @ X0))
% 2.25/2.42          | ((k1_relat_1 @ sk_B) = (k10_relat_1 @ sk_B @ X0)))),
% 2.25/2.42      inference('sup-', [status(thm)], ['39', '40'])).
% 2.25/2.42  thf('42', plain,
% 2.25/2.42      ((~ (r1_tarski @ (k1_relat_1 @ sk_B) @ (k1_relat_1 @ sk_B))
% 2.25/2.42        | ~ (v1_relat_1 @ sk_B)
% 2.25/2.42        | ((k1_relat_1 @ sk_B) = (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B))))),
% 2.25/2.42      inference('sup-', [status(thm)], ['9', '41'])).
% 2.25/2.42  thf('43', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 2.25/2.42      inference('simplify', [status(thm)], ['19'])).
% 2.25/2.42  thf('44', plain, ((v1_relat_1 @ sk_B)),
% 2.25/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.42  thf('45', plain,
% 2.25/2.42      (((k1_relat_1 @ sk_B) = (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B)))),
% 2.25/2.42      inference('demod', [status(thm)], ['42', '43', '44'])).
% 2.25/2.42  thf(t139_funct_1, axiom,
% 2.25/2.42    (![A:$i,B:$i,C:$i]:
% 2.25/2.42     ( ( v1_relat_1 @ C ) =>
% 2.25/2.42       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 2.25/2.42         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 2.25/2.42  thf('46', plain,
% 2.25/2.42      (![X28 : $i, X29 : $i, X30 : $i]:
% 2.25/2.42         (((k10_relat_1 @ (k7_relat_1 @ X29 @ X28) @ X30)
% 2.25/2.42            = (k3_xboole_0 @ X28 @ (k10_relat_1 @ X29 @ X30)))
% 2.25/2.42          | ~ (v1_relat_1 @ X29))),
% 2.25/2.42      inference('cnf', [status(esa)], [t139_funct_1])).
% 2.25/2.42  thf('47', plain,
% 2.25/2.42      (![X25 : $i, X26 : $i]:
% 2.25/2.42         ((r1_tarski @ (k10_relat_1 @ X25 @ X26) @ (k1_relat_1 @ X25))
% 2.25/2.42          | ~ (v1_relat_1 @ X25))),
% 2.25/2.42      inference('cnf', [status(esa)], [t167_relat_1])).
% 2.25/2.42  thf('48', plain,
% 2.25/2.42      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.25/2.42         ((r1_tarski @ (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0)) @ 
% 2.25/2.42           (k1_relat_1 @ (k7_relat_1 @ X1 @ X2)))
% 2.25/2.42          | ~ (v1_relat_1 @ X1)
% 2.25/2.42          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X2)))),
% 2.25/2.42      inference('sup+', [status(thm)], ['46', '47'])).
% 2.25/2.42  thf('49', plain,
% 2.25/2.42      (![X21 : $i, X22 : $i]:
% 2.25/2.42         (~ (v1_relat_1 @ X21) | (v1_relat_1 @ (k7_relat_1 @ X21 @ X22)))),
% 2.25/2.42      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 2.25/2.42  thf('50', plain,
% 2.25/2.42      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.25/2.42         (~ (v1_relat_1 @ X1)
% 2.25/2.42          | (r1_tarski @ (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0)) @ 
% 2.25/2.42             (k1_relat_1 @ (k7_relat_1 @ X1 @ X2))))),
% 2.25/2.42      inference('clc', [status(thm)], ['48', '49'])).
% 2.25/2.42  thf('51', plain,
% 2.25/2.42      (![X0 : $i]:
% 2.25/2.42         ((r1_tarski @ (k3_xboole_0 @ X0 @ (k1_relat_1 @ sk_B)) @ 
% 2.25/2.42           (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)))
% 2.25/2.42          | ~ (v1_relat_1 @ sk_B))),
% 2.25/2.42      inference('sup+', [status(thm)], ['45', '50'])).
% 2.25/2.42  thf('52', plain, ((v1_relat_1 @ sk_B)),
% 2.25/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.42  thf('53', plain,
% 2.25/2.42      (![X0 : $i]:
% 2.25/2.42         (r1_tarski @ (k3_xboole_0 @ X0 @ (k1_relat_1 @ sk_B)) @ 
% 2.25/2.42          (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)))),
% 2.25/2.42      inference('demod', [status(thm)], ['51', '52'])).
% 2.25/2.42  thf('54', plain,
% 2.25/2.42      ((r1_tarski @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 2.25/2.42      inference('sup+', [status(thm)], ['8', '53'])).
% 2.25/2.42  thf('55', plain,
% 2.25/2.42      (![X28 : $i, X29 : $i, X30 : $i]:
% 2.25/2.42         (((k10_relat_1 @ (k7_relat_1 @ X29 @ X28) @ X30)
% 2.25/2.42            = (k3_xboole_0 @ X28 @ (k10_relat_1 @ X29 @ X30)))
% 2.25/2.42          | ~ (v1_relat_1 @ X29))),
% 2.25/2.42      inference('cnf', [status(esa)], [t139_funct_1])).
% 2.25/2.42  thf('56', plain,
% 2.25/2.42      (![X27 : $i]:
% 2.25/2.42         (((k10_relat_1 @ X27 @ (k2_relat_1 @ X27)) = (k1_relat_1 @ X27))
% 2.25/2.42          | ~ (v1_relat_1 @ X27))),
% 2.25/2.42      inference('cnf', [status(esa)], [t169_relat_1])).
% 2.25/2.42  thf('57', plain,
% 2.25/2.42      (![X0 : $i, X1 : $i]:
% 2.25/2.42         (((k3_xboole_0 @ X0 @ 
% 2.25/2.42            (k10_relat_1 @ X1 @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X0))))
% 2.25/2.42            = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 2.25/2.42          | ~ (v1_relat_1 @ X1)
% 2.25/2.42          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 2.25/2.42      inference('sup+', [status(thm)], ['55', '56'])).
% 2.25/2.42  thf('58', plain,
% 2.25/2.42      (![X21 : $i, X22 : $i]:
% 2.25/2.42         (~ (v1_relat_1 @ X21) | (v1_relat_1 @ (k7_relat_1 @ X21 @ X22)))),
% 2.25/2.42      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 2.25/2.42  thf('59', plain,
% 2.25/2.42      (![X0 : $i, X1 : $i]:
% 2.25/2.42         (~ (v1_relat_1 @ X1)
% 2.25/2.42          | ((k3_xboole_0 @ X0 @ 
% 2.25/2.42              (k10_relat_1 @ X1 @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X0))))
% 2.25/2.42              = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 2.25/2.42      inference('clc', [status(thm)], ['57', '58'])).
% 2.25/2.42  thf('60', plain,
% 2.25/2.42      (![X11 : $i, X12 : $i]: (r1_tarski @ (k3_xboole_0 @ X11 @ X12) @ X11)),
% 2.25/2.42      inference('cnf', [status(esa)], [t17_xboole_1])).
% 2.25/2.42  thf('61', plain,
% 2.25/2.42      (![X0 : $i, X1 : $i]:
% 2.25/2.42         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X0)
% 2.25/2.42          | ~ (v1_relat_1 @ X1))),
% 2.25/2.42      inference('sup+', [status(thm)], ['59', '60'])).
% 2.25/2.42  thf('62', plain,
% 2.25/2.42      (![X2 : $i, X4 : $i]:
% 2.25/2.42         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 2.25/2.42      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.25/2.42  thf('63', plain,
% 2.25/2.42      (![X0 : $i, X1 : $i]:
% 2.25/2.42         (~ (v1_relat_1 @ X1)
% 2.25/2.42          | ~ (r1_tarski @ X0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 2.25/2.42          | ((X0) = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 2.25/2.42      inference('sup-', [status(thm)], ['61', '62'])).
% 2.25/2.42  thf('64', plain,
% 2.25/2.42      ((((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 2.25/2.42        | ~ (v1_relat_1 @ sk_B))),
% 2.25/2.42      inference('sup-', [status(thm)], ['54', '63'])).
% 2.25/2.42  thf('65', plain, ((v1_relat_1 @ sk_B)),
% 2.25/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.42  thf('66', plain, (((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 2.25/2.42      inference('demod', [status(thm)], ['64', '65'])).
% 2.25/2.42  thf('67', plain,
% 2.25/2.42      (![X28 : $i, X29 : $i, X30 : $i]:
% 2.25/2.42         (((k10_relat_1 @ (k7_relat_1 @ X29 @ X28) @ X30)
% 2.25/2.42            = (k3_xboole_0 @ X28 @ (k10_relat_1 @ X29 @ X30)))
% 2.25/2.42          | ~ (v1_relat_1 @ X29))),
% 2.25/2.42      inference('cnf', [status(esa)], [t139_funct_1])).
% 2.25/2.42  thf('68', plain,
% 2.25/2.42      (![X25 : $i, X26 : $i]:
% 2.25/2.42         ((r1_tarski @ (k10_relat_1 @ X25 @ X26) @ (k1_relat_1 @ X25))
% 2.25/2.42          | ~ (v1_relat_1 @ X25))),
% 2.25/2.42      inference('cnf', [status(esa)], [t167_relat_1])).
% 2.25/2.42  thf('69', plain,
% 2.25/2.42      (![X16 : $i, X17 : $i]:
% 2.25/2.42         (((k3_xboole_0 @ X16 @ X17) = (X16)) | ~ (r1_tarski @ X16 @ X17))),
% 2.25/2.42      inference('cnf', [status(esa)], [t28_xboole_1])).
% 2.25/2.42  thf('70', plain,
% 2.25/2.42      (![X0 : $i, X1 : $i]:
% 2.25/2.42         (~ (v1_relat_1 @ X0)
% 2.25/2.42          | ((k3_xboole_0 @ (k10_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0))
% 2.25/2.42              = (k10_relat_1 @ X0 @ X1)))),
% 2.25/2.42      inference('sup-', [status(thm)], ['68', '69'])).
% 2.25/2.42  thf('71', plain,
% 2.25/2.42      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.25/2.42      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.25/2.42  thf('72', plain,
% 2.25/2.42      (![X0 : $i, X1 : $i]:
% 2.25/2.42         (~ (v1_relat_1 @ X0)
% 2.25/2.42          | ((k3_xboole_0 @ (k1_relat_1 @ X0) @ (k10_relat_1 @ X0 @ X1))
% 2.25/2.42              = (k10_relat_1 @ X0 @ X1)))),
% 2.25/2.42      inference('demod', [status(thm)], ['70', '71'])).
% 2.25/2.42  thf('73', plain,
% 2.25/2.42      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.25/2.42         (((k3_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X2)) @ 
% 2.25/2.42            (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0)))
% 2.25/2.42            = (k10_relat_1 @ (k7_relat_1 @ X1 @ X2) @ X0))
% 2.25/2.42          | ~ (v1_relat_1 @ X1)
% 2.25/2.42          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X2)))),
% 2.25/2.42      inference('sup+', [status(thm)], ['67', '72'])).
% 2.25/2.42  thf('74', plain,
% 2.25/2.42      (![X21 : $i, X22 : $i]:
% 2.25/2.42         (~ (v1_relat_1 @ X21) | (v1_relat_1 @ (k7_relat_1 @ X21 @ X22)))),
% 2.25/2.42      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 2.25/2.42  thf('75', plain,
% 2.25/2.42      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.25/2.42         (~ (v1_relat_1 @ X1)
% 2.25/2.42          | ((k3_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X2)) @ 
% 2.25/2.42              (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0)))
% 2.25/2.42              = (k10_relat_1 @ (k7_relat_1 @ X1 @ X2) @ X0)))),
% 2.25/2.42      inference('clc', [status(thm)], ['73', '74'])).
% 2.25/2.42  thf('76', plain,
% 2.25/2.42      (![X0 : $i]:
% 2.25/2.42         (((k3_xboole_0 @ sk_A @ 
% 2.25/2.42            (k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ X0)))
% 2.25/2.42            = (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0))
% 2.25/2.42          | ~ (v1_relat_1 @ sk_B))),
% 2.25/2.42      inference('sup+', [status(thm)], ['66', '75'])).
% 2.25/2.42  thf('77', plain,
% 2.25/2.42      (![X11 : $i, X12 : $i]: (r1_tarski @ (k3_xboole_0 @ X11 @ X12) @ X11)),
% 2.25/2.42      inference('cnf', [status(esa)], [t17_xboole_1])).
% 2.25/2.42  thf('78', plain,
% 2.25/2.42      (![X16 : $i, X17 : $i]:
% 2.25/2.42         (((k3_xboole_0 @ X16 @ X17) = (X16)) | ~ (r1_tarski @ X16 @ X17))),
% 2.25/2.42      inference('cnf', [status(esa)], [t28_xboole_1])).
% 2.25/2.42  thf('79', plain,
% 2.25/2.42      (![X0 : $i, X1 : $i]:
% 2.25/2.42         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 2.25/2.42           = (k3_xboole_0 @ X0 @ X1))),
% 2.25/2.42      inference('sup-', [status(thm)], ['77', '78'])).
% 2.25/2.42  thf('80', plain,
% 2.25/2.42      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.25/2.42      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.25/2.42  thf('81', plain,
% 2.25/2.42      (![X0 : $i, X1 : $i]:
% 2.25/2.42         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 2.25/2.42           = (k3_xboole_0 @ X0 @ X1))),
% 2.25/2.42      inference('demod', [status(thm)], ['79', '80'])).
% 2.25/2.42  thf('82', plain, ((v1_relat_1 @ sk_B)),
% 2.25/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.42  thf('83', plain,
% 2.25/2.42      (![X0 : $i]:
% 2.25/2.42         ((k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ X0))
% 2.25/2.42           = (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0))),
% 2.25/2.42      inference('demod', [status(thm)], ['76', '81', '82'])).
% 2.25/2.42  thf('84', plain,
% 2.25/2.42      ((((k3_xboole_0 @ sk_A @ 
% 2.25/2.42          (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 2.25/2.42          = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 2.25/2.42        | ~ (v1_relat_1 @ sk_B))),
% 2.25/2.42      inference('sup+', [status(thm)], ['5', '83'])).
% 2.25/2.42  thf('85', plain, (((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 2.25/2.42      inference('demod', [status(thm)], ['64', '65'])).
% 2.25/2.42  thf('86', plain, ((v1_relat_1 @ sk_B)),
% 2.25/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.42  thf('87', plain,
% 2.25/2.42      (((k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 2.25/2.42         = (sk_A))),
% 2.25/2.42      inference('demod', [status(thm)], ['84', '85', '86'])).
% 2.25/2.42  thf('88', plain,
% 2.25/2.42      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.25/2.42      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.25/2.42  thf('89', plain,
% 2.25/2.42      (![X11 : $i, X12 : $i]: (r1_tarski @ (k3_xboole_0 @ X11 @ X12) @ X11)),
% 2.25/2.42      inference('cnf', [status(esa)], [t17_xboole_1])).
% 2.25/2.42  thf('90', plain,
% 2.25/2.42      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 2.25/2.42      inference('sup+', [status(thm)], ['88', '89'])).
% 2.25/2.42  thf('91', plain,
% 2.25/2.42      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 2.25/2.42      inference('sup+', [status(thm)], ['87', '90'])).
% 2.25/2.42  thf('92', plain, ($false), inference('demod', [status(thm)], ['0', '91'])).
% 2.25/2.42  
% 2.25/2.42  % SZS output end Refutation
% 2.25/2.42  
% 2.26/2.43  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
