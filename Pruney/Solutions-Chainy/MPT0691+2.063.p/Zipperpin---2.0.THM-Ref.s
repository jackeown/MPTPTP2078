%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6Ecy7P4XA6

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:26 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 268 expanded)
%              Number of leaves         :   26 (  89 expanded)
%              Depth                    :   35
%              Number of atoms          :  918 (2440 expanded)
%              Number of equality atoms :   48 (  97 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

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

thf(t139_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('1',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X29 @ X28 ) @ X30 )
        = ( k3_xboole_0 @ X28 @ ( k10_relat_1 @ X29 @ X30 ) ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X18 @ X19 ) )
        = ( k9_relat_1 @ X18 @ X19 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('3',plain,(
    ! [X22: $i] :
      ( ( ( k10_relat_1 @ X22 @ ( k2_relat_1 @ X22 ) )
        = ( k1_relat_1 @ X22 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X22: $i] :
      ( ( ( k10_relat_1 @ X22 @ ( k2_relat_1 @ X22 ) )
        = ( k1_relat_1 @ X22 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('10',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X20 @ X21 ) @ ( k1_relat_1 @ X20 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('11',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_xboole_0 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k3_xboole_0 @ ( k10_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) )
        = ( k10_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X20 @ X21 ) @ ( k1_relat_1 @ X20 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('14',plain,(
    ! [X22: $i] :
      ( ( ( k10_relat_1 @ X22 @ ( k2_relat_1 @ X22 ) )
        = ( k1_relat_1 @ X22 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('15',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X29 @ X28 ) @ X30 )
        = ( k3_xboole_0 @ X28 @ ( k10_relat_1 @ X29 @ X30 ) ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('16',plain,(
    ! [X26: $i,X27: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X26 @ X27 ) ) @ X27 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf('17',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X20 @ X21 ) @ ( k1_relat_1 @ X20 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('18',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X9 @ X10 )
      | ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) @ X0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['15','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ ( k1_relat_1 @ X0 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X1 @ ( k1_relat_1 @ X0 ) ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X9 @ X10 )
      | ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k3_xboole_0 @ X0 @ ( k1_relat_1 @ X1 ) ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_xboole_0 @ ( k10_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X2 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['13','28'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('30',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k3_xboole_0 @ ( k10_relat_1 @ X0 @ X2 ) @ ( k1_relat_1 @ X1 ) ) )
      | ( ( k1_relat_1 @ X0 )
        = ( k3_xboole_0 @ ( k10_relat_1 @ X0 @ X2 ) @ ( k1_relat_1 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X1 ) @ ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k1_relat_1 @ X1 )
        = ( k3_xboole_0 @ ( k10_relat_1 @ X1 @ X0 ) @ ( k1_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ X1 )
        = ( k3_xboole_0 @ ( k10_relat_1 @ X1 @ X0 ) @ ( k1_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X1 ) @ ( k10_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k3_xboole_0 @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['9','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('36',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k3_xboole_0 @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['34','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = ( k3_xboole_0 @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X1 @ ( k1_relat_1 @ X0 ) ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X9 @ X10 )
      | ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_xboole_0 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('49',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) )
    = sk_A ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X29 @ X28 ) @ X30 )
        = ( k3_xboole_0 @ X28 @ ( k10_relat_1 @ X29 @ X30 ) ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('51',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X20 @ X21 ) @ ( k1_relat_1 @ X20 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) ) ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( r1_tarski @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['49','54'])).

thf('56',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X26: $i,X27: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X26 @ X27 ) ) @ X27 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf('59',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ( X0
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( sk_A
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['57','60'])).

thf('62',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( sk_A
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) ) ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ X0 ) ) @ sk_A )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ X0 ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_xboole_0 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ X0 ) ) @ sk_A )
      = ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( ( k3_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) @ sk_A )
      = ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['8','69'])).

thf('71',plain,
    ( sk_A
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('72',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['35'])).

thf('73',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_xboole_0 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['70','71','74','75'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('77',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('78',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    = ( k5_xboole_0 @ sk_A @ sk_A ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('79',plain,(
    ! [X13: $i] :
      ( ( k5_xboole_0 @ X13 @ X13 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('80',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['78','79'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('81',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k4_xboole_0 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('82',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,(
    $false ),
    inference(demod,[status(thm)],['0','83'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6Ecy7P4XA6
% 0.14/0.36  % Computer   : n008.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 09:43:30 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.21/0.36  % Python version: Python 3.6.8
% 0.21/0.36  % Running in FO mode
% 0.38/0.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.62  % Solved by: fo/fo7.sh
% 0.38/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.62  % done 235 iterations in 0.149s
% 0.38/0.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.62  % SZS output start Refutation
% 0.38/0.62  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.38/0.62  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.38/0.62  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.38/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.62  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.38/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.62  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.38/0.62  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.38/0.62  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.38/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.62  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.38/0.62  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.38/0.62  thf(t146_funct_1, conjecture,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( v1_relat_1 @ B ) =>
% 0.38/0.62       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.38/0.62         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 0.38/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.62    (~( ![A:$i,B:$i]:
% 0.38/0.62        ( ( v1_relat_1 @ B ) =>
% 0.38/0.62          ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.38/0.62            ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )),
% 0.38/0.62    inference('cnf.neg', [status(esa)], [t146_funct_1])).
% 0.38/0.62  thf('0', plain,
% 0.38/0.62      (~ (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf(t139_funct_1, axiom,
% 0.38/0.62    (![A:$i,B:$i,C:$i]:
% 0.38/0.62     ( ( v1_relat_1 @ C ) =>
% 0.38/0.62       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.38/0.62         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.38/0.62  thf('1', plain,
% 0.38/0.62      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.38/0.62         (((k10_relat_1 @ (k7_relat_1 @ X29 @ X28) @ X30)
% 0.38/0.62            = (k3_xboole_0 @ X28 @ (k10_relat_1 @ X29 @ X30)))
% 0.38/0.62          | ~ (v1_relat_1 @ X29))),
% 0.38/0.62      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.38/0.62  thf(t148_relat_1, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( v1_relat_1 @ B ) =>
% 0.38/0.62       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.38/0.62  thf('2', plain,
% 0.38/0.62      (![X18 : $i, X19 : $i]:
% 0.38/0.62         (((k2_relat_1 @ (k7_relat_1 @ X18 @ X19)) = (k9_relat_1 @ X18 @ X19))
% 0.38/0.62          | ~ (v1_relat_1 @ X18))),
% 0.38/0.62      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.38/0.62  thf(t169_relat_1, axiom,
% 0.38/0.62    (![A:$i]:
% 0.38/0.62     ( ( v1_relat_1 @ A ) =>
% 0.38/0.62       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.38/0.62  thf('3', plain,
% 0.38/0.62      (![X22 : $i]:
% 0.38/0.62         (((k10_relat_1 @ X22 @ (k2_relat_1 @ X22)) = (k1_relat_1 @ X22))
% 0.38/0.62          | ~ (v1_relat_1 @ X22))),
% 0.38/0.62      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.38/0.62  thf('4', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]:
% 0.38/0.62         (((k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0))
% 0.38/0.62            = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.38/0.62          | ~ (v1_relat_1 @ X1)
% 0.38/0.62          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.38/0.62      inference('sup+', [status(thm)], ['2', '3'])).
% 0.38/0.62  thf(dt_k7_relat_1, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.38/0.62  thf('5', plain,
% 0.38/0.62      (![X16 : $i, X17 : $i]:
% 0.38/0.62         (~ (v1_relat_1 @ X16) | (v1_relat_1 @ (k7_relat_1 @ X16 @ X17)))),
% 0.38/0.62      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.38/0.62  thf('6', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]:
% 0.38/0.62         (~ (v1_relat_1 @ X1)
% 0.38/0.62          | ((k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0))
% 0.38/0.62              = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 0.38/0.62      inference('clc', [status(thm)], ['4', '5'])).
% 0.38/0.62  thf('7', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]:
% 0.38/0.62         (((k3_xboole_0 @ X0 @ (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0)))
% 0.38/0.62            = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.38/0.62          | ~ (v1_relat_1 @ X1)
% 0.38/0.62          | ~ (v1_relat_1 @ X1))),
% 0.38/0.62      inference('sup+', [status(thm)], ['1', '6'])).
% 0.38/0.62  thf('8', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]:
% 0.38/0.62         (~ (v1_relat_1 @ X1)
% 0.38/0.62          | ((k3_xboole_0 @ X0 @ (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0)))
% 0.38/0.62              = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 0.38/0.62      inference('simplify', [status(thm)], ['7'])).
% 0.38/0.62  thf('9', plain,
% 0.38/0.62      (![X22 : $i]:
% 0.38/0.62         (((k10_relat_1 @ X22 @ (k2_relat_1 @ X22)) = (k1_relat_1 @ X22))
% 0.38/0.62          | ~ (v1_relat_1 @ X22))),
% 0.38/0.62      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.38/0.62  thf(t167_relat_1, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( v1_relat_1 @ B ) =>
% 0.38/0.62       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 0.38/0.62  thf('10', plain,
% 0.38/0.62      (![X20 : $i, X21 : $i]:
% 0.38/0.62         ((r1_tarski @ (k10_relat_1 @ X20 @ X21) @ (k1_relat_1 @ X20))
% 0.38/0.62          | ~ (v1_relat_1 @ X20))),
% 0.38/0.62      inference('cnf', [status(esa)], [t167_relat_1])).
% 0.38/0.62  thf(t28_xboole_1, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.38/0.62  thf('11', plain,
% 0.38/0.62      (![X11 : $i, X12 : $i]:
% 0.38/0.62         (((k3_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_tarski @ X11 @ X12))),
% 0.38/0.62      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.38/0.62  thf('12', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]:
% 0.38/0.62         (~ (v1_relat_1 @ X0)
% 0.38/0.62          | ((k3_xboole_0 @ (k10_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0))
% 0.38/0.62              = (k10_relat_1 @ X0 @ X1)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['10', '11'])).
% 0.38/0.62  thf('13', plain,
% 0.38/0.62      (![X20 : $i, X21 : $i]:
% 0.38/0.62         ((r1_tarski @ (k10_relat_1 @ X20 @ X21) @ (k1_relat_1 @ X20))
% 0.38/0.62          | ~ (v1_relat_1 @ X20))),
% 0.38/0.62      inference('cnf', [status(esa)], [t167_relat_1])).
% 0.38/0.62  thf('14', plain,
% 0.38/0.62      (![X22 : $i]:
% 0.38/0.62         (((k10_relat_1 @ X22 @ (k2_relat_1 @ X22)) = (k1_relat_1 @ X22))
% 0.38/0.62          | ~ (v1_relat_1 @ X22))),
% 0.38/0.62      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.38/0.62  thf('15', plain,
% 0.38/0.62      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.38/0.62         (((k10_relat_1 @ (k7_relat_1 @ X29 @ X28) @ X30)
% 0.38/0.62            = (k3_xboole_0 @ X28 @ (k10_relat_1 @ X29 @ X30)))
% 0.38/0.62          | ~ (v1_relat_1 @ X29))),
% 0.38/0.62      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.38/0.62  thf(t87_relat_1, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( v1_relat_1 @ B ) =>
% 0.38/0.62       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 0.38/0.62  thf('16', plain,
% 0.38/0.62      (![X26 : $i, X27 : $i]:
% 0.38/0.62         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X26 @ X27)) @ X27)
% 0.38/0.62          | ~ (v1_relat_1 @ X26))),
% 0.38/0.62      inference('cnf', [status(esa)], [t87_relat_1])).
% 0.38/0.62  thf('17', plain,
% 0.38/0.62      (![X20 : $i, X21 : $i]:
% 0.38/0.62         ((r1_tarski @ (k10_relat_1 @ X20 @ X21) @ (k1_relat_1 @ X20))
% 0.38/0.62          | ~ (v1_relat_1 @ X20))),
% 0.38/0.62      inference('cnf', [status(esa)], [t167_relat_1])).
% 0.38/0.62  thf(t1_xboole_1, axiom,
% 0.38/0.62    (![A:$i,B:$i,C:$i]:
% 0.38/0.62     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.38/0.62       ( r1_tarski @ A @ C ) ))).
% 0.38/0.62  thf('18', plain,
% 0.38/0.62      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.38/0.62         (~ (r1_tarski @ X8 @ X9)
% 0.38/0.62          | ~ (r1_tarski @ X9 @ X10)
% 0.38/0.62          | (r1_tarski @ X8 @ X10))),
% 0.38/0.62      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.38/0.62  thf('19', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.62         (~ (v1_relat_1 @ X0)
% 0.38/0.62          | (r1_tarski @ (k10_relat_1 @ X0 @ X1) @ X2)
% 0.38/0.62          | ~ (r1_tarski @ (k1_relat_1 @ X0) @ X2))),
% 0.38/0.62      inference('sup-', [status(thm)], ['17', '18'])).
% 0.38/0.62  thf('20', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.62         (~ (v1_relat_1 @ X1)
% 0.38/0.62          | (r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2) @ X0)
% 0.38/0.62          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['16', '19'])).
% 0.38/0.62  thf('21', plain,
% 0.38/0.62      (![X16 : $i, X17 : $i]:
% 0.38/0.62         (~ (v1_relat_1 @ X16) | (v1_relat_1 @ (k7_relat_1 @ X16 @ X17)))),
% 0.38/0.62      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.38/0.62  thf('22', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.62         ((r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2) @ X0)
% 0.38/0.62          | ~ (v1_relat_1 @ X1))),
% 0.38/0.62      inference('clc', [status(thm)], ['20', '21'])).
% 0.38/0.62  thf('23', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.62         ((r1_tarski @ (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0)) @ X2)
% 0.38/0.62          | ~ (v1_relat_1 @ X1)
% 0.38/0.62          | ~ (v1_relat_1 @ X1))),
% 0.38/0.62      inference('sup+', [status(thm)], ['15', '22'])).
% 0.38/0.62  thf('24', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.62         (~ (v1_relat_1 @ X1)
% 0.38/0.62          | (r1_tarski @ (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0)) @ X2))),
% 0.38/0.62      inference('simplify', [status(thm)], ['23'])).
% 0.38/0.62  thf('25', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]:
% 0.38/0.62         ((r1_tarski @ (k3_xboole_0 @ X1 @ (k1_relat_1 @ X0)) @ X1)
% 0.38/0.62          | ~ (v1_relat_1 @ X0)
% 0.38/0.62          | ~ (v1_relat_1 @ X0))),
% 0.38/0.62      inference('sup+', [status(thm)], ['14', '24'])).
% 0.38/0.62  thf('26', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]:
% 0.38/0.62         (~ (v1_relat_1 @ X0)
% 0.38/0.62          | (r1_tarski @ (k3_xboole_0 @ X1 @ (k1_relat_1 @ X0)) @ X1))),
% 0.38/0.62      inference('simplify', [status(thm)], ['25'])).
% 0.38/0.62  thf('27', plain,
% 0.38/0.62      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.38/0.62         (~ (r1_tarski @ X8 @ X9)
% 0.38/0.62          | ~ (r1_tarski @ X9 @ X10)
% 0.38/0.62          | (r1_tarski @ X8 @ X10))),
% 0.38/0.62      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.38/0.62  thf('28', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.62         (~ (v1_relat_1 @ X1)
% 0.38/0.62          | (r1_tarski @ (k3_xboole_0 @ X0 @ (k1_relat_1 @ X1)) @ X2)
% 0.38/0.62          | ~ (r1_tarski @ X0 @ X2))),
% 0.38/0.62      inference('sup-', [status(thm)], ['26', '27'])).
% 0.38/0.62  thf('29', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.62         (~ (v1_relat_1 @ X0)
% 0.38/0.62          | (r1_tarski @ 
% 0.38/0.62             (k3_xboole_0 @ (k10_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X2)) @ 
% 0.38/0.62             (k1_relat_1 @ X0))
% 0.38/0.62          | ~ (v1_relat_1 @ X2))),
% 0.38/0.62      inference('sup-', [status(thm)], ['13', '28'])).
% 0.38/0.62  thf(d10_xboole_0, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.38/0.62  thf('30', plain,
% 0.38/0.62      (![X0 : $i, X2 : $i]:
% 0.38/0.62         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.38/0.62      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.38/0.62  thf('31', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.62         (~ (v1_relat_1 @ X1)
% 0.38/0.62          | ~ (v1_relat_1 @ X0)
% 0.38/0.62          | ~ (r1_tarski @ (k1_relat_1 @ X0) @ 
% 0.38/0.62               (k3_xboole_0 @ (k10_relat_1 @ X0 @ X2) @ (k1_relat_1 @ X1)))
% 0.38/0.62          | ((k1_relat_1 @ X0)
% 0.38/0.62              = (k3_xboole_0 @ (k10_relat_1 @ X0 @ X2) @ (k1_relat_1 @ X1))))),
% 0.38/0.62      inference('sup-', [status(thm)], ['29', '30'])).
% 0.38/0.62  thf('32', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]:
% 0.38/0.62         (~ (r1_tarski @ (k1_relat_1 @ X1) @ (k10_relat_1 @ X1 @ X0))
% 0.38/0.62          | ~ (v1_relat_1 @ X1)
% 0.38/0.62          | ((k1_relat_1 @ X1)
% 0.38/0.62              = (k3_xboole_0 @ (k10_relat_1 @ X1 @ X0) @ (k1_relat_1 @ X1)))
% 0.38/0.62          | ~ (v1_relat_1 @ X1)
% 0.38/0.62          | ~ (v1_relat_1 @ X1))),
% 0.38/0.62      inference('sup-', [status(thm)], ['12', '31'])).
% 0.38/0.62  thf('33', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]:
% 0.38/0.62         (((k1_relat_1 @ X1)
% 0.38/0.62            = (k3_xboole_0 @ (k10_relat_1 @ X1 @ X0) @ (k1_relat_1 @ X1)))
% 0.38/0.62          | ~ (v1_relat_1 @ X1)
% 0.38/0.62          | ~ (r1_tarski @ (k1_relat_1 @ X1) @ (k10_relat_1 @ X1 @ X0)))),
% 0.38/0.62      inference('simplify', [status(thm)], ['32'])).
% 0.38/0.62  thf('34', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         (~ (r1_tarski @ (k1_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.38/0.62          | ~ (v1_relat_1 @ X0)
% 0.38/0.62          | ~ (v1_relat_1 @ X0)
% 0.38/0.62          | ((k1_relat_1 @ X0)
% 0.38/0.62              = (k3_xboole_0 @ (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)) @ 
% 0.38/0.62                 (k1_relat_1 @ X0))))),
% 0.38/0.62      inference('sup-', [status(thm)], ['9', '33'])).
% 0.38/0.62  thf('35', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.38/0.62      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.38/0.62  thf('36', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.38/0.62      inference('simplify', [status(thm)], ['35'])).
% 0.38/0.62  thf('37', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         (~ (v1_relat_1 @ X0)
% 0.38/0.62          | ~ (v1_relat_1 @ X0)
% 0.38/0.62          | ((k1_relat_1 @ X0)
% 0.38/0.62              = (k3_xboole_0 @ (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)) @ 
% 0.38/0.62                 (k1_relat_1 @ X0))))),
% 0.38/0.62      inference('demod', [status(thm)], ['34', '36'])).
% 0.38/0.62  thf('38', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         (((k1_relat_1 @ X0)
% 0.38/0.62            = (k3_xboole_0 @ (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)) @ 
% 0.38/0.62               (k1_relat_1 @ X0)))
% 0.38/0.62          | ~ (v1_relat_1 @ X0))),
% 0.38/0.62      inference('simplify', [status(thm)], ['37'])).
% 0.38/0.62  thf('39', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]:
% 0.38/0.62         (~ (v1_relat_1 @ X0)
% 0.38/0.62          | (r1_tarski @ (k3_xboole_0 @ X1 @ (k1_relat_1 @ X0)) @ X1))),
% 0.38/0.62      inference('simplify', [status(thm)], ['25'])).
% 0.38/0.62  thf('40', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         ((r1_tarski @ (k1_relat_1 @ X0) @ 
% 0.38/0.62           (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 0.38/0.62          | ~ (v1_relat_1 @ X0)
% 0.38/0.62          | ~ (v1_relat_1 @ X0))),
% 0.38/0.62      inference('sup+', [status(thm)], ['38', '39'])).
% 0.38/0.62  thf('41', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         (~ (v1_relat_1 @ X0)
% 0.38/0.62          | (r1_tarski @ (k1_relat_1 @ X0) @ 
% 0.38/0.62             (k10_relat_1 @ X0 @ (k2_relat_1 @ X0))))),
% 0.38/0.62      inference('simplify', [status(thm)], ['40'])).
% 0.38/0.62  thf('42', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('43', plain,
% 0.38/0.62      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.38/0.62         (~ (r1_tarski @ X8 @ X9)
% 0.38/0.62          | ~ (r1_tarski @ X9 @ X10)
% 0.38/0.62          | (r1_tarski @ X8 @ X10))),
% 0.38/0.62      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.38/0.62  thf('44', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         ((r1_tarski @ sk_A @ X0) | ~ (r1_tarski @ (k1_relat_1 @ sk_B) @ X0))),
% 0.38/0.62      inference('sup-', [status(thm)], ['42', '43'])).
% 0.38/0.62  thf('45', plain,
% 0.38/0.62      ((~ (v1_relat_1 @ sk_B)
% 0.38/0.62        | (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B))))),
% 0.38/0.62      inference('sup-', [status(thm)], ['41', '44'])).
% 0.38/0.62  thf('46', plain, ((v1_relat_1 @ sk_B)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('47', plain,
% 0.38/0.62      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B)))),
% 0.38/0.62      inference('demod', [status(thm)], ['45', '46'])).
% 0.38/0.62  thf('48', plain,
% 0.38/0.62      (![X11 : $i, X12 : $i]:
% 0.38/0.62         (((k3_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_tarski @ X11 @ X12))),
% 0.38/0.62      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.38/0.62  thf('49', plain,
% 0.38/0.62      (((k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B)))
% 0.38/0.62         = (sk_A))),
% 0.38/0.62      inference('sup-', [status(thm)], ['47', '48'])).
% 0.38/0.62  thf('50', plain,
% 0.38/0.62      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.38/0.62         (((k10_relat_1 @ (k7_relat_1 @ X29 @ X28) @ X30)
% 0.38/0.62            = (k3_xboole_0 @ X28 @ (k10_relat_1 @ X29 @ X30)))
% 0.38/0.62          | ~ (v1_relat_1 @ X29))),
% 0.38/0.62      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.38/0.62  thf('51', plain,
% 0.38/0.62      (![X20 : $i, X21 : $i]:
% 0.38/0.62         ((r1_tarski @ (k10_relat_1 @ X20 @ X21) @ (k1_relat_1 @ X20))
% 0.38/0.62          | ~ (v1_relat_1 @ X20))),
% 0.38/0.62      inference('cnf', [status(esa)], [t167_relat_1])).
% 0.38/0.62  thf('52', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.62         ((r1_tarski @ (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0)) @ 
% 0.38/0.62           (k1_relat_1 @ (k7_relat_1 @ X1 @ X2)))
% 0.38/0.62          | ~ (v1_relat_1 @ X1)
% 0.38/0.62          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X2)))),
% 0.38/0.62      inference('sup+', [status(thm)], ['50', '51'])).
% 0.38/0.62  thf('53', plain,
% 0.38/0.62      (![X16 : $i, X17 : $i]:
% 0.38/0.62         (~ (v1_relat_1 @ X16) | (v1_relat_1 @ (k7_relat_1 @ X16 @ X17)))),
% 0.38/0.62      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.38/0.62  thf('54', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.62         (~ (v1_relat_1 @ X1)
% 0.38/0.62          | (r1_tarski @ (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0)) @ 
% 0.38/0.62             (k1_relat_1 @ (k7_relat_1 @ X1 @ X2))))),
% 0.38/0.62      inference('clc', [status(thm)], ['52', '53'])).
% 0.38/0.62  thf('55', plain,
% 0.38/0.62      (((r1_tarski @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.38/0.62        | ~ (v1_relat_1 @ sk_B))),
% 0.38/0.62      inference('sup+', [status(thm)], ['49', '54'])).
% 0.38/0.62  thf('56', plain, ((v1_relat_1 @ sk_B)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('57', plain,
% 0.38/0.62      ((r1_tarski @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.38/0.62      inference('demod', [status(thm)], ['55', '56'])).
% 0.38/0.62  thf('58', plain,
% 0.38/0.62      (![X26 : $i, X27 : $i]:
% 0.38/0.62         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X26 @ X27)) @ X27)
% 0.38/0.62          | ~ (v1_relat_1 @ X26))),
% 0.38/0.62      inference('cnf', [status(esa)], [t87_relat_1])).
% 0.38/0.62  thf('59', plain,
% 0.38/0.62      (![X0 : $i, X2 : $i]:
% 0.38/0.62         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.38/0.62      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.38/0.62  thf('60', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]:
% 0.38/0.62         (~ (v1_relat_1 @ X1)
% 0.38/0.62          | ~ (r1_tarski @ X0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.38/0.62          | ((X0) = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 0.38/0.62      inference('sup-', [status(thm)], ['58', '59'])).
% 0.38/0.62  thf('61', plain,
% 0.38/0.62      ((((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.38/0.62        | ~ (v1_relat_1 @ sk_B))),
% 0.38/0.62      inference('sup-', [status(thm)], ['57', '60'])).
% 0.38/0.62  thf('62', plain, ((v1_relat_1 @ sk_B)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('63', plain, (((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.38/0.62      inference('demod', [status(thm)], ['61', '62'])).
% 0.38/0.62  thf('64', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.62         (~ (v1_relat_1 @ X1)
% 0.38/0.62          | (r1_tarski @ (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0)) @ 
% 0.38/0.62             (k1_relat_1 @ (k7_relat_1 @ X1 @ X2))))),
% 0.38/0.62      inference('clc', [status(thm)], ['52', '53'])).
% 0.38/0.62  thf('65', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         ((r1_tarski @ (k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ X0)) @ sk_A)
% 0.38/0.62          | ~ (v1_relat_1 @ sk_B))),
% 0.38/0.62      inference('sup+', [status(thm)], ['63', '64'])).
% 0.38/0.62  thf('66', plain, ((v1_relat_1 @ sk_B)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('67', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         (r1_tarski @ (k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ X0)) @ sk_A)),
% 0.38/0.62      inference('demod', [status(thm)], ['65', '66'])).
% 0.38/0.62  thf('68', plain,
% 0.38/0.62      (![X11 : $i, X12 : $i]:
% 0.38/0.62         (((k3_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_tarski @ X11 @ X12))),
% 0.38/0.62      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.38/0.62  thf('69', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         ((k3_xboole_0 @ (k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ X0)) @ 
% 0.38/0.62           sk_A) = (k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ X0)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['67', '68'])).
% 0.38/0.62  thf('70', plain,
% 0.38/0.62      ((((k3_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) @ sk_A)
% 0.38/0.62          = (k3_xboole_0 @ sk_A @ 
% 0.38/0.62             (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A))))
% 0.38/0.62        | ~ (v1_relat_1 @ sk_B))),
% 0.38/0.62      inference('sup+', [status(thm)], ['8', '69'])).
% 0.38/0.62  thf('71', plain, (((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.38/0.62      inference('demod', [status(thm)], ['61', '62'])).
% 0.38/0.62  thf('72', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.38/0.62      inference('simplify', [status(thm)], ['35'])).
% 0.38/0.62  thf('73', plain,
% 0.38/0.62      (![X11 : $i, X12 : $i]:
% 0.38/0.62         (((k3_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_tarski @ X11 @ X12))),
% 0.38/0.62      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.38/0.62  thf('74', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.38/0.62      inference('sup-', [status(thm)], ['72', '73'])).
% 0.38/0.62  thf('75', plain, ((v1_relat_1 @ sk_B)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('76', plain,
% 0.38/0.62      (((sk_A)
% 0.38/0.62         = (k3_xboole_0 @ sk_A @ 
% 0.38/0.62            (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A))))),
% 0.38/0.62      inference('demod', [status(thm)], ['70', '71', '74', '75'])).
% 0.38/0.62  thf(t100_xboole_1, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.38/0.62  thf('77', plain,
% 0.38/0.62      (![X6 : $i, X7 : $i]:
% 0.38/0.62         ((k4_xboole_0 @ X6 @ X7)
% 0.38/0.62           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.38/0.62      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.38/0.62  thf('78', plain,
% 0.38/0.62      (((k4_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 0.38/0.62         = (k5_xboole_0 @ sk_A @ sk_A))),
% 0.38/0.62      inference('sup+', [status(thm)], ['76', '77'])).
% 0.38/0.62  thf(t92_xboole_1, axiom,
% 0.38/0.62    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.38/0.62  thf('79', plain, (![X13 : $i]: ((k5_xboole_0 @ X13 @ X13) = (k1_xboole_0))),
% 0.38/0.62      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.38/0.62  thf('80', plain,
% 0.38/0.62      (((k4_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 0.38/0.62         = (k1_xboole_0))),
% 0.38/0.62      inference('demod', [status(thm)], ['78', '79'])).
% 0.38/0.62  thf(l32_xboole_1, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.38/0.62  thf('81', plain,
% 0.38/0.62      (![X3 : $i, X4 : $i]:
% 0.38/0.62         ((r1_tarski @ X3 @ X4) | ((k4_xboole_0 @ X3 @ X4) != (k1_xboole_0)))),
% 0.38/0.62      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.38/0.62  thf('82', plain,
% 0.38/0.62      ((((k1_xboole_0) != (k1_xboole_0))
% 0.38/0.62        | (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A))))),
% 0.38/0.62      inference('sup-', [status(thm)], ['80', '81'])).
% 0.38/0.62  thf('83', plain,
% 0.38/0.62      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 0.38/0.62      inference('simplify', [status(thm)], ['82'])).
% 0.38/0.62  thf('84', plain, ($false), inference('demod', [status(thm)], ['0', '83'])).
% 0.38/0.62  
% 0.38/0.62  % SZS output end Refutation
% 0.38/0.62  
% 0.38/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
