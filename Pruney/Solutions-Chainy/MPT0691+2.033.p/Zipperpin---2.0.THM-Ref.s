%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SzT28kl8e5

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:22 EST 2020

% Result     : Theorem 2.42s
% Output     : Refutation 2.42s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 214 expanded)
%              Number of leaves         :   22 (  74 expanded)
%              Depth                    :   21
%              Number of atoms          :  822 (1861 expanded)
%              Number of equality atoms :   49 ( 100 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X17: $i,X18: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X17 @ X18 ) )
        = ( k9_relat_1 @ X17 @ X18 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('2',plain,(
    ! [X21: $i] :
      ( ( ( k10_relat_1 @ X21 @ ( k2_relat_1 @ X21 ) )
        = ( k1_relat_1 @ X21 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
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
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['3','4'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('6',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('7',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('8',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X21: $i] :
      ( ( ( k10_relat_1 @ X21 @ ( k2_relat_1 @ X21 ) )
        = ( k1_relat_1 @ X21 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('11',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X19 @ X20 ) @ ( k1_relat_1 @ X19 ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

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
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_xboole_0 @ ( k10_relat_1 @ X0 @ X1 ) @ X2 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k3_xboole_0 @ ( k10_relat_1 @ X0 @ X2 ) @ X1 ) )
      | ( ( k1_relat_1 @ X0 )
        = ( k3_xboole_0 @ ( k10_relat_1 @ X0 @ X2 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k3_xboole_0 @ ( k1_relat_1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k3_xboole_0 @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = ( k3_xboole_0 @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k3_xboole_0 @ ( k1_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k3_xboole_0 @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['9','17'])).

thf('19',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['6'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('23',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','24'])).

thf('26',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('27',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ~ ( r1_tarski @ X11 @ X12 )
      | ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('33',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) )
    = sk_A ),
    inference('sup-',[status(thm)],['31','32'])).

thf(t139_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('34',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X26 @ X25 ) @ X27 )
        = ( k3_xboole_0 @ X25 @ ( k10_relat_1 @ X26 @ X27 ) ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('35',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X19 @ X20 ) @ ( k1_relat_1 @ X19 ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( r1_tarski @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['33','38'])).

thf('40',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X26 @ X25 ) @ X27 )
        = ( k3_xboole_0 @ X25 @ ( k10_relat_1 @ X26 @ X27 ) ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('43',plain,(
    ! [X21: $i] :
      ( ( ( k10_relat_1 @ X21 @ ( k2_relat_1 @ X21 ) )
        = ( k1_relat_1 @ X21 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ( X0
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( sk_A
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['41','50'])).

thf('52',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( sk_A
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X26 @ X25 ) @ X27 )
        = ( k3_xboole_0 @ X25 @ ( k10_relat_1 @ X26 @ X27 ) ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('55',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X19 @ X20 ) @ ( k1_relat_1 @ X19 ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('56',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k3_xboole_0 @ ( k10_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) )
        = ( k10_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k3_xboole_0 @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ X1 ) )
        = ( k10_relat_1 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) )
        = ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['54','59'])).

thf('61',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k3_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) )
        = ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) @ X0 ) ) ) ),
    inference(clc,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ X0 ) ) )
        = ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['53','62'])).

thf('64',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('65',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ X0 ) )
      = ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['63','68','69'])).

thf('71',plain,
    ( ( ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['5','70'])).

thf('72',plain,
    ( sk_A
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('73',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    = sk_A ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('76',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    $false ),
    inference(demod,[status(thm)],['0','76'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SzT28kl8e5
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:26:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.42/2.66  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.42/2.66  % Solved by: fo/fo7.sh
% 2.42/2.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.42/2.66  % done 3003 iterations in 2.206s
% 2.42/2.66  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.42/2.66  % SZS output start Refutation
% 2.42/2.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.42/2.66  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 2.42/2.66  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.42/2.66  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.42/2.66  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.42/2.66  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.42/2.66  thf(sk_B_type, type, sk_B: $i).
% 2.42/2.66  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 2.42/2.66  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 2.42/2.66  thf(sk_A_type, type, sk_A: $i).
% 2.42/2.66  thf(t146_funct_1, conjecture,
% 2.42/2.66    (![A:$i,B:$i]:
% 2.42/2.66     ( ( v1_relat_1 @ B ) =>
% 2.42/2.66       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 2.42/2.66         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 2.42/2.66  thf(zf_stmt_0, negated_conjecture,
% 2.42/2.66    (~( ![A:$i,B:$i]:
% 2.42/2.66        ( ( v1_relat_1 @ B ) =>
% 2.42/2.66          ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 2.42/2.66            ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )),
% 2.42/2.66    inference('cnf.neg', [status(esa)], [t146_funct_1])).
% 2.42/2.66  thf('0', plain,
% 2.42/2.66      (~ (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 2.42/2.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.42/2.66  thf(t148_relat_1, axiom,
% 2.42/2.66    (![A:$i,B:$i]:
% 2.42/2.66     ( ( v1_relat_1 @ B ) =>
% 2.42/2.66       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 2.42/2.66  thf('1', plain,
% 2.42/2.66      (![X17 : $i, X18 : $i]:
% 2.42/2.66         (((k2_relat_1 @ (k7_relat_1 @ X17 @ X18)) = (k9_relat_1 @ X17 @ X18))
% 2.42/2.66          | ~ (v1_relat_1 @ X17))),
% 2.42/2.66      inference('cnf', [status(esa)], [t148_relat_1])).
% 2.42/2.66  thf(t169_relat_1, axiom,
% 2.42/2.66    (![A:$i]:
% 2.42/2.66     ( ( v1_relat_1 @ A ) =>
% 2.42/2.66       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 2.42/2.66  thf('2', plain,
% 2.42/2.66      (![X21 : $i]:
% 2.42/2.66         (((k10_relat_1 @ X21 @ (k2_relat_1 @ X21)) = (k1_relat_1 @ X21))
% 2.42/2.66          | ~ (v1_relat_1 @ X21))),
% 2.42/2.66      inference('cnf', [status(esa)], [t169_relat_1])).
% 2.42/2.66  thf('3', plain,
% 2.42/2.66      (![X0 : $i, X1 : $i]:
% 2.42/2.66         (((k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0))
% 2.42/2.66            = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 2.42/2.66          | ~ (v1_relat_1 @ X1)
% 2.42/2.66          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 2.42/2.66      inference('sup+', [status(thm)], ['1', '2'])).
% 2.42/2.66  thf(dt_k7_relat_1, axiom,
% 2.42/2.66    (![A:$i,B:$i]:
% 2.42/2.66     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 2.42/2.66  thf('4', plain,
% 2.42/2.66      (![X15 : $i, X16 : $i]:
% 2.42/2.66         (~ (v1_relat_1 @ X15) | (v1_relat_1 @ (k7_relat_1 @ X15 @ X16)))),
% 2.42/2.66      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 2.42/2.66  thf('5', plain,
% 2.42/2.66      (![X0 : $i, X1 : $i]:
% 2.42/2.66         (~ (v1_relat_1 @ X1)
% 2.42/2.66          | ((k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0))
% 2.42/2.66              = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 2.42/2.66      inference('clc', [status(thm)], ['3', '4'])).
% 2.42/2.66  thf(d10_xboole_0, axiom,
% 2.42/2.66    (![A:$i,B:$i]:
% 2.42/2.66     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.42/2.66  thf('6', plain,
% 2.42/2.66      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 2.42/2.66      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.42/2.66  thf('7', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 2.42/2.66      inference('simplify', [status(thm)], ['6'])).
% 2.42/2.66  thf(t28_xboole_1, axiom,
% 2.42/2.66    (![A:$i,B:$i]:
% 2.42/2.66     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 2.42/2.66  thf('8', plain,
% 2.42/2.66      (![X13 : $i, X14 : $i]:
% 2.42/2.66         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 2.42/2.66      inference('cnf', [status(esa)], [t28_xboole_1])).
% 2.42/2.66  thf('9', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 2.42/2.66      inference('sup-', [status(thm)], ['7', '8'])).
% 2.42/2.66  thf('10', plain,
% 2.42/2.66      (![X21 : $i]:
% 2.42/2.66         (((k10_relat_1 @ X21 @ (k2_relat_1 @ X21)) = (k1_relat_1 @ X21))
% 2.42/2.66          | ~ (v1_relat_1 @ X21))),
% 2.42/2.66      inference('cnf', [status(esa)], [t169_relat_1])).
% 2.42/2.66  thf(t167_relat_1, axiom,
% 2.42/2.66    (![A:$i,B:$i]:
% 2.42/2.66     ( ( v1_relat_1 @ B ) =>
% 2.42/2.66       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 2.42/2.66  thf('11', plain,
% 2.42/2.66      (![X19 : $i, X20 : $i]:
% 2.42/2.66         ((r1_tarski @ (k10_relat_1 @ X19 @ X20) @ (k1_relat_1 @ X19))
% 2.42/2.66          | ~ (v1_relat_1 @ X19))),
% 2.42/2.66      inference('cnf', [status(esa)], [t167_relat_1])).
% 2.42/2.66  thf(t108_xboole_1, axiom,
% 2.42/2.66    (![A:$i,B:$i,C:$i]:
% 2.42/2.66     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ B ) ))).
% 2.42/2.66  thf('12', plain,
% 2.42/2.66      (![X5 : $i, X6 : $i, X7 : $i]:
% 2.42/2.66         (~ (r1_tarski @ X5 @ X6) | (r1_tarski @ (k3_xboole_0 @ X5 @ X7) @ X6))),
% 2.42/2.66      inference('cnf', [status(esa)], [t108_xboole_1])).
% 2.42/2.66  thf('13', plain,
% 2.42/2.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.42/2.66         (~ (v1_relat_1 @ X0)
% 2.42/2.66          | (r1_tarski @ (k3_xboole_0 @ (k10_relat_1 @ X0 @ X1) @ X2) @ 
% 2.42/2.66             (k1_relat_1 @ X0)))),
% 2.42/2.66      inference('sup-', [status(thm)], ['11', '12'])).
% 2.42/2.66  thf('14', plain,
% 2.42/2.66      (![X2 : $i, X4 : $i]:
% 2.42/2.66         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 2.42/2.66      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.42/2.66  thf('15', plain,
% 2.42/2.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.42/2.66         (~ (v1_relat_1 @ X0)
% 2.42/2.66          | ~ (r1_tarski @ (k1_relat_1 @ X0) @ 
% 2.42/2.66               (k3_xboole_0 @ (k10_relat_1 @ X0 @ X2) @ X1))
% 2.42/2.66          | ((k1_relat_1 @ X0) = (k3_xboole_0 @ (k10_relat_1 @ X0 @ X2) @ X1)))),
% 2.42/2.66      inference('sup-', [status(thm)], ['13', '14'])).
% 2.42/2.66  thf('16', plain,
% 2.42/2.66      (![X0 : $i, X1 : $i]:
% 2.42/2.66         (~ (r1_tarski @ (k1_relat_1 @ X0) @ 
% 2.42/2.66             (k3_xboole_0 @ (k1_relat_1 @ X0) @ X1))
% 2.42/2.66          | ~ (v1_relat_1 @ X0)
% 2.42/2.66          | ((k1_relat_1 @ X0)
% 2.42/2.66              = (k3_xboole_0 @ (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)) @ X1))
% 2.42/2.66          | ~ (v1_relat_1 @ X0))),
% 2.42/2.66      inference('sup-', [status(thm)], ['10', '15'])).
% 2.42/2.66  thf('17', plain,
% 2.42/2.66      (![X0 : $i, X1 : $i]:
% 2.42/2.66         (((k1_relat_1 @ X0)
% 2.42/2.66            = (k3_xboole_0 @ (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)) @ X1))
% 2.42/2.66          | ~ (v1_relat_1 @ X0)
% 2.42/2.66          | ~ (r1_tarski @ (k1_relat_1 @ X0) @ 
% 2.42/2.66               (k3_xboole_0 @ (k1_relat_1 @ X0) @ X1)))),
% 2.42/2.66      inference('simplify', [status(thm)], ['16'])).
% 2.42/2.66  thf('18', plain,
% 2.42/2.66      (![X0 : $i]:
% 2.42/2.66         (~ (r1_tarski @ (k1_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 2.42/2.66          | ~ (v1_relat_1 @ X0)
% 2.42/2.66          | ((k1_relat_1 @ X0)
% 2.42/2.66              = (k3_xboole_0 @ (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)) @ 
% 2.42/2.66                 (k1_relat_1 @ X0))))),
% 2.42/2.66      inference('sup-', [status(thm)], ['9', '17'])).
% 2.42/2.66  thf('19', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 2.42/2.66      inference('simplify', [status(thm)], ['6'])).
% 2.42/2.66  thf(commutativity_k3_xboole_0, axiom,
% 2.42/2.66    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 2.42/2.66  thf('20', plain,
% 2.42/2.66      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.42/2.66      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.42/2.66  thf('21', plain,
% 2.42/2.66      (![X0 : $i]:
% 2.42/2.66         (~ (v1_relat_1 @ X0)
% 2.42/2.66          | ((k1_relat_1 @ X0)
% 2.42/2.66              = (k3_xboole_0 @ (k1_relat_1 @ X0) @ 
% 2.42/2.66                 (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))))),
% 2.42/2.66      inference('demod', [status(thm)], ['18', '19', '20'])).
% 2.42/2.66  thf('22', plain,
% 2.42/2.66      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.42/2.66      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.42/2.66  thf(t17_xboole_1, axiom,
% 2.42/2.66    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 2.42/2.67  thf('23', plain,
% 2.42/2.67      (![X8 : $i, X9 : $i]: (r1_tarski @ (k3_xboole_0 @ X8 @ X9) @ X8)),
% 2.42/2.67      inference('cnf', [status(esa)], [t17_xboole_1])).
% 2.42/2.67  thf('24', plain,
% 2.42/2.67      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 2.42/2.67      inference('sup+', [status(thm)], ['22', '23'])).
% 2.42/2.67  thf('25', plain,
% 2.42/2.67      (![X0 : $i]:
% 2.42/2.67         ((r1_tarski @ (k1_relat_1 @ X0) @ 
% 2.42/2.67           (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 2.42/2.67          | ~ (v1_relat_1 @ X0))),
% 2.42/2.67      inference('sup+', [status(thm)], ['21', '24'])).
% 2.42/2.67  thf('26', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 2.42/2.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.42/2.67  thf(t1_xboole_1, axiom,
% 2.42/2.67    (![A:$i,B:$i,C:$i]:
% 2.42/2.67     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 2.42/2.67       ( r1_tarski @ A @ C ) ))).
% 2.42/2.67  thf('27', plain,
% 2.42/2.67      (![X10 : $i, X11 : $i, X12 : $i]:
% 2.42/2.67         (~ (r1_tarski @ X10 @ X11)
% 2.42/2.67          | ~ (r1_tarski @ X11 @ X12)
% 2.42/2.67          | (r1_tarski @ X10 @ X12))),
% 2.42/2.67      inference('cnf', [status(esa)], [t1_xboole_1])).
% 2.42/2.67  thf('28', plain,
% 2.42/2.67      (![X0 : $i]:
% 2.42/2.67         ((r1_tarski @ sk_A @ X0) | ~ (r1_tarski @ (k1_relat_1 @ sk_B) @ X0))),
% 2.42/2.67      inference('sup-', [status(thm)], ['26', '27'])).
% 2.42/2.67  thf('29', plain,
% 2.42/2.67      ((~ (v1_relat_1 @ sk_B)
% 2.42/2.67        | (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B))))),
% 2.42/2.67      inference('sup-', [status(thm)], ['25', '28'])).
% 2.42/2.67  thf('30', plain, ((v1_relat_1 @ sk_B)),
% 2.42/2.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.42/2.67  thf('31', plain,
% 2.42/2.67      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B)))),
% 2.42/2.67      inference('demod', [status(thm)], ['29', '30'])).
% 2.42/2.67  thf('32', plain,
% 2.42/2.67      (![X13 : $i, X14 : $i]:
% 2.42/2.67         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 2.42/2.67      inference('cnf', [status(esa)], [t28_xboole_1])).
% 2.42/2.67  thf('33', plain,
% 2.42/2.67      (((k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B)))
% 2.42/2.67         = (sk_A))),
% 2.42/2.67      inference('sup-', [status(thm)], ['31', '32'])).
% 2.42/2.67  thf(t139_funct_1, axiom,
% 2.42/2.67    (![A:$i,B:$i,C:$i]:
% 2.42/2.67     ( ( v1_relat_1 @ C ) =>
% 2.42/2.67       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 2.42/2.67         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 2.42/2.67  thf('34', plain,
% 2.42/2.67      (![X25 : $i, X26 : $i, X27 : $i]:
% 2.42/2.67         (((k10_relat_1 @ (k7_relat_1 @ X26 @ X25) @ X27)
% 2.42/2.67            = (k3_xboole_0 @ X25 @ (k10_relat_1 @ X26 @ X27)))
% 2.42/2.67          | ~ (v1_relat_1 @ X26))),
% 2.42/2.67      inference('cnf', [status(esa)], [t139_funct_1])).
% 2.42/2.67  thf('35', plain,
% 2.42/2.67      (![X19 : $i, X20 : $i]:
% 2.42/2.67         ((r1_tarski @ (k10_relat_1 @ X19 @ X20) @ (k1_relat_1 @ X19))
% 2.42/2.67          | ~ (v1_relat_1 @ X19))),
% 2.42/2.67      inference('cnf', [status(esa)], [t167_relat_1])).
% 2.42/2.67  thf('36', plain,
% 2.42/2.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.42/2.67         ((r1_tarski @ (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0)) @ 
% 2.42/2.67           (k1_relat_1 @ (k7_relat_1 @ X1 @ X2)))
% 2.42/2.67          | ~ (v1_relat_1 @ X1)
% 2.42/2.67          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X2)))),
% 2.42/2.67      inference('sup+', [status(thm)], ['34', '35'])).
% 2.42/2.67  thf('37', plain,
% 2.42/2.67      (![X15 : $i, X16 : $i]:
% 2.42/2.67         (~ (v1_relat_1 @ X15) | (v1_relat_1 @ (k7_relat_1 @ X15 @ X16)))),
% 2.42/2.67      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 2.42/2.67  thf('38', plain,
% 2.42/2.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.42/2.67         (~ (v1_relat_1 @ X1)
% 2.42/2.67          | (r1_tarski @ (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0)) @ 
% 2.42/2.67             (k1_relat_1 @ (k7_relat_1 @ X1 @ X2))))),
% 2.42/2.67      inference('clc', [status(thm)], ['36', '37'])).
% 2.42/2.67  thf('39', plain,
% 2.42/2.67      (((r1_tarski @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 2.42/2.67        | ~ (v1_relat_1 @ sk_B))),
% 2.42/2.67      inference('sup+', [status(thm)], ['33', '38'])).
% 2.42/2.67  thf('40', plain, ((v1_relat_1 @ sk_B)),
% 2.42/2.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.42/2.67  thf('41', plain,
% 2.42/2.67      ((r1_tarski @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 2.42/2.67      inference('demod', [status(thm)], ['39', '40'])).
% 2.42/2.67  thf('42', plain,
% 2.42/2.67      (![X25 : $i, X26 : $i, X27 : $i]:
% 2.42/2.67         (((k10_relat_1 @ (k7_relat_1 @ X26 @ X25) @ X27)
% 2.42/2.67            = (k3_xboole_0 @ X25 @ (k10_relat_1 @ X26 @ X27)))
% 2.42/2.67          | ~ (v1_relat_1 @ X26))),
% 2.42/2.67      inference('cnf', [status(esa)], [t139_funct_1])).
% 2.42/2.67  thf('43', plain,
% 2.42/2.67      (![X21 : $i]:
% 2.42/2.67         (((k10_relat_1 @ X21 @ (k2_relat_1 @ X21)) = (k1_relat_1 @ X21))
% 2.42/2.67          | ~ (v1_relat_1 @ X21))),
% 2.42/2.67      inference('cnf', [status(esa)], [t169_relat_1])).
% 2.42/2.67  thf('44', plain,
% 2.42/2.67      (![X0 : $i, X1 : $i]:
% 2.42/2.67         (((k3_xboole_0 @ X0 @ 
% 2.42/2.67            (k10_relat_1 @ X1 @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X0))))
% 2.42/2.67            = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 2.42/2.67          | ~ (v1_relat_1 @ X1)
% 2.42/2.67          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 2.42/2.67      inference('sup+', [status(thm)], ['42', '43'])).
% 2.42/2.67  thf('45', plain,
% 2.42/2.67      (![X15 : $i, X16 : $i]:
% 2.42/2.67         (~ (v1_relat_1 @ X15) | (v1_relat_1 @ (k7_relat_1 @ X15 @ X16)))),
% 2.42/2.67      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 2.42/2.67  thf('46', plain,
% 2.42/2.67      (![X0 : $i, X1 : $i]:
% 2.42/2.67         (~ (v1_relat_1 @ X1)
% 2.42/2.67          | ((k3_xboole_0 @ X0 @ 
% 2.42/2.67              (k10_relat_1 @ X1 @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X0))))
% 2.42/2.67              = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 2.42/2.67      inference('clc', [status(thm)], ['44', '45'])).
% 2.42/2.67  thf('47', plain,
% 2.42/2.67      (![X8 : $i, X9 : $i]: (r1_tarski @ (k3_xboole_0 @ X8 @ X9) @ X8)),
% 2.42/2.67      inference('cnf', [status(esa)], [t17_xboole_1])).
% 2.42/2.67  thf('48', plain,
% 2.42/2.67      (![X0 : $i, X1 : $i]:
% 2.42/2.67         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X0)
% 2.42/2.67          | ~ (v1_relat_1 @ X1))),
% 2.42/2.67      inference('sup+', [status(thm)], ['46', '47'])).
% 2.42/2.67  thf('49', plain,
% 2.42/2.67      (![X2 : $i, X4 : $i]:
% 2.42/2.67         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 2.42/2.67      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.42/2.67  thf('50', plain,
% 2.42/2.67      (![X0 : $i, X1 : $i]:
% 2.42/2.67         (~ (v1_relat_1 @ X1)
% 2.42/2.67          | ~ (r1_tarski @ X0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 2.42/2.67          | ((X0) = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 2.42/2.67      inference('sup-', [status(thm)], ['48', '49'])).
% 2.42/2.67  thf('51', plain,
% 2.42/2.67      ((((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 2.42/2.67        | ~ (v1_relat_1 @ sk_B))),
% 2.42/2.67      inference('sup-', [status(thm)], ['41', '50'])).
% 2.42/2.67  thf('52', plain, ((v1_relat_1 @ sk_B)),
% 2.42/2.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.42/2.67  thf('53', plain, (((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 2.42/2.67      inference('demod', [status(thm)], ['51', '52'])).
% 2.42/2.67  thf('54', plain,
% 2.42/2.67      (![X25 : $i, X26 : $i, X27 : $i]:
% 2.42/2.67         (((k10_relat_1 @ (k7_relat_1 @ X26 @ X25) @ X27)
% 2.42/2.67            = (k3_xboole_0 @ X25 @ (k10_relat_1 @ X26 @ X27)))
% 2.42/2.67          | ~ (v1_relat_1 @ X26))),
% 2.42/2.67      inference('cnf', [status(esa)], [t139_funct_1])).
% 2.42/2.67  thf('55', plain,
% 2.42/2.67      (![X19 : $i, X20 : $i]:
% 2.42/2.67         ((r1_tarski @ (k10_relat_1 @ X19 @ X20) @ (k1_relat_1 @ X19))
% 2.42/2.67          | ~ (v1_relat_1 @ X19))),
% 2.42/2.67      inference('cnf', [status(esa)], [t167_relat_1])).
% 2.42/2.67  thf('56', plain,
% 2.42/2.67      (![X13 : $i, X14 : $i]:
% 2.42/2.67         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 2.42/2.67      inference('cnf', [status(esa)], [t28_xboole_1])).
% 2.42/2.67  thf('57', plain,
% 2.42/2.67      (![X0 : $i, X1 : $i]:
% 2.42/2.67         (~ (v1_relat_1 @ X0)
% 2.42/2.67          | ((k3_xboole_0 @ (k10_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0))
% 2.42/2.67              = (k10_relat_1 @ X0 @ X1)))),
% 2.42/2.67      inference('sup-', [status(thm)], ['55', '56'])).
% 2.42/2.67  thf('58', plain,
% 2.42/2.67      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.42/2.67      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.42/2.67  thf('59', plain,
% 2.42/2.67      (![X0 : $i, X1 : $i]:
% 2.42/2.67         (~ (v1_relat_1 @ X0)
% 2.42/2.67          | ((k3_xboole_0 @ (k1_relat_1 @ X0) @ (k10_relat_1 @ X0 @ X1))
% 2.42/2.67              = (k10_relat_1 @ X0 @ X1)))),
% 2.42/2.67      inference('demod', [status(thm)], ['57', '58'])).
% 2.42/2.67  thf('60', plain,
% 2.42/2.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.42/2.67         (((k3_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X2)) @ 
% 2.42/2.67            (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0)))
% 2.42/2.67            = (k10_relat_1 @ (k7_relat_1 @ X1 @ X2) @ X0))
% 2.42/2.67          | ~ (v1_relat_1 @ X1)
% 2.42/2.67          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X2)))),
% 2.42/2.67      inference('sup+', [status(thm)], ['54', '59'])).
% 2.42/2.67  thf('61', plain,
% 2.42/2.67      (![X15 : $i, X16 : $i]:
% 2.42/2.67         (~ (v1_relat_1 @ X15) | (v1_relat_1 @ (k7_relat_1 @ X15 @ X16)))),
% 2.42/2.67      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 2.42/2.67  thf('62', plain,
% 2.42/2.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.42/2.67         (~ (v1_relat_1 @ X1)
% 2.42/2.67          | ((k3_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X2)) @ 
% 2.42/2.67              (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0)))
% 2.42/2.67              = (k10_relat_1 @ (k7_relat_1 @ X1 @ X2) @ X0)))),
% 2.42/2.67      inference('clc', [status(thm)], ['60', '61'])).
% 2.42/2.67  thf('63', plain,
% 2.42/2.67      (![X0 : $i]:
% 2.42/2.67         (((k3_xboole_0 @ sk_A @ 
% 2.42/2.67            (k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ X0)))
% 2.42/2.67            = (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0))
% 2.42/2.67          | ~ (v1_relat_1 @ sk_B))),
% 2.42/2.67      inference('sup+', [status(thm)], ['53', '62'])).
% 2.42/2.67  thf('64', plain,
% 2.42/2.67      (![X8 : $i, X9 : $i]: (r1_tarski @ (k3_xboole_0 @ X8 @ X9) @ X8)),
% 2.42/2.67      inference('cnf', [status(esa)], [t17_xboole_1])).
% 2.42/2.67  thf('65', plain,
% 2.42/2.67      (![X13 : $i, X14 : $i]:
% 2.42/2.67         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 2.42/2.67      inference('cnf', [status(esa)], [t28_xboole_1])).
% 2.42/2.67  thf('66', plain,
% 2.42/2.67      (![X0 : $i, X1 : $i]:
% 2.42/2.67         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 2.42/2.67           = (k3_xboole_0 @ X0 @ X1))),
% 2.42/2.67      inference('sup-', [status(thm)], ['64', '65'])).
% 2.42/2.67  thf('67', plain,
% 2.42/2.67      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.42/2.67      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.42/2.67  thf('68', plain,
% 2.42/2.67      (![X0 : $i, X1 : $i]:
% 2.42/2.67         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 2.42/2.67           = (k3_xboole_0 @ X0 @ X1))),
% 2.42/2.67      inference('demod', [status(thm)], ['66', '67'])).
% 2.42/2.67  thf('69', plain, ((v1_relat_1 @ sk_B)),
% 2.42/2.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.42/2.67  thf('70', plain,
% 2.42/2.67      (![X0 : $i]:
% 2.42/2.67         ((k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ X0))
% 2.42/2.67           = (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0))),
% 2.42/2.67      inference('demod', [status(thm)], ['63', '68', '69'])).
% 2.42/2.67  thf('71', plain,
% 2.42/2.67      ((((k3_xboole_0 @ sk_A @ 
% 2.42/2.67          (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 2.42/2.67          = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 2.42/2.67        | ~ (v1_relat_1 @ sk_B))),
% 2.42/2.67      inference('sup+', [status(thm)], ['5', '70'])).
% 2.42/2.67  thf('72', plain, (((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 2.42/2.67      inference('demod', [status(thm)], ['51', '52'])).
% 2.42/2.67  thf('73', plain, ((v1_relat_1 @ sk_B)),
% 2.42/2.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.42/2.67  thf('74', plain,
% 2.42/2.67      (((k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 2.42/2.67         = (sk_A))),
% 2.42/2.67      inference('demod', [status(thm)], ['71', '72', '73'])).
% 2.42/2.67  thf('75', plain,
% 2.42/2.67      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 2.42/2.67      inference('sup+', [status(thm)], ['22', '23'])).
% 2.42/2.67  thf('76', plain,
% 2.42/2.67      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 2.42/2.67      inference('sup+', [status(thm)], ['74', '75'])).
% 2.42/2.67  thf('77', plain, ($false), inference('demod', [status(thm)], ['0', '76'])).
% 2.42/2.67  
% 2.42/2.67  % SZS output end Refutation
% 2.42/2.67  
% 2.42/2.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
