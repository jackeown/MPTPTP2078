%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2B1Izat7B6

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:21 EST 2020

% Result     : Theorem 1.16s
% Output     : Refutation 1.16s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 167 expanded)
%              Number of leaves         :   25 (  58 expanded)
%              Depth                    :   24
%              Number of atoms          :  872 (1373 expanded)
%              Number of equality atoms :   43 (  62 expanded)
%              Maximal formula depth    :   10 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

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
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X31 @ X30 ) @ X32 )
        = ( k3_xboole_0 @ X30 @ ( k10_relat_1 @ X31 @ X32 ) ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('2',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('3',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k3_xboole_0 @ X18 @ X19 )
        = X18 )
      | ~ ( r1_tarski @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('4',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) )
    = sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('5',plain,(
    ! [X27: $i] :
      ( ( ( k10_relat_1 @ X27 @ ( k2_relat_1 @ X27 ) )
        = ( k1_relat_1 @ X27 ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf(t170_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k10_relat_1 @ B @ ( k2_relat_1 @ B ) ) ) ) )).

thf('6',plain,(
    ! [X28: $i,X29: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X28 @ X29 ) @ ( k10_relat_1 @ X28 @ ( k2_relat_1 @ X28 ) ) )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t170_relat_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('10',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t108_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ B ) ) )).

thf('11',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ( r1_tarski @ ( k3_xboole_0 @ X5 @ X7 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t108_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_A @ X0 ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k3_xboole_0 @ X18 @ X19 )
        = X18 )
      | ~ ( r1_tarski @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ sk_A @ X0 ) @ ( k1_relat_1 @ sk_B ) )
      = ( k3_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k3_xboole_0 @ sk_A @ X0 ) )
      = ( k3_xboole_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('17',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X13 @ X14 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('18',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('19',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['18'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('20',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r1_tarski @ X20 @ X21 )
      | ~ ( r1_tarski @ X22 @ X21 )
      | ( r1_tarski @ ( k2_xboole_0 @ X20 @ X22 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['17','21'])).

thf('23',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['18'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('24',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X8 @ X10 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['22','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k3_xboole_0 @ sk_A @ X0 ) )
      = ( k1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['16','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k3_xboole_0 @ X0 @ sk_A ) )
      = ( k1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['9','29'])).

thf('31',plain,(
    ! [X27: $i] :
      ( ( ( k10_relat_1 @ X27 @ ( k2_relat_1 @ X27 ) )
        = ( k1_relat_1 @ X27 ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('32',plain,(
    ! [X28: $i,X29: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X28 @ X29 ) @ ( k10_relat_1 @ X28 @ ( k2_relat_1 @ X28 ) ) )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t170_relat_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('35',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_xboole_0 @ X12 @ X11 )
        = X11 )
      | ~ ( r1_tarski @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_xboole_0 @ ( k10_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('38',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X8 @ X10 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ X2 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X0 @ X2 ) @ ( k2_xboole_0 @ ( k1_relat_1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ sk_B @ X1 ) @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['30','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X1: $i] :
      ( r1_tarski @ ( k10_relat_1 @ sk_B @ X1 ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k10_relat_1 @ sk_B @ X0 ) )
      | ( ( k1_relat_1 @ sk_B )
        = ( k10_relat_1 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( k1_relat_1 @ sk_B )
      = ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['8','45'])).

thf('47',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X31 @ X30 ) @ X32 )
        = ( k3_xboole_0 @ X30 @ ( k10_relat_1 @ X31 @ X32 ) ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('52',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) ) ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X0 @ ( k1_relat_1 @ sk_B ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['48','53'])).

thf('55',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ ( k1_relat_1 @ sk_B ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['4','56'])).

thf('58',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X31 @ X30 ) @ X32 )
        = ( k3_xboole_0 @ X30 @ ( k10_relat_1 @ X31 @ X32 ) ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('59',plain,(
    ! [X27: $i] :
      ( ( ( k10_relat_1 @ X27 @ ( k2_relat_1 @ X27 ) )
        = ( k1_relat_1 @ X27 ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X13 @ X14 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ( X0
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( sk_A
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['57','66'])).

thf('68',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( sk_A
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('70',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X25 @ X26 ) )
        = ( k9_relat_1 @ X25 @ X26 ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( r1_tarski @ sk_A @ ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['69','74'])).

thf('76',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,
    ( ( r1_tarski @ sk_A @ ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['1','77'])).

thf('79',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    r1_tarski @ sk_A @ ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X13 @ X14 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('82',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['80','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('86',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X13 @ X14 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['84','87'])).

thf('89',plain,(
    $false ),
    inference(demod,[status(thm)],['0','88'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2B1Izat7B6
% 0.13/0.33  % Computer   : n017.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:10:46 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 1.16/1.35  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.16/1.35  % Solved by: fo/fo7.sh
% 1.16/1.35  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.16/1.35  % done 2071 iterations in 0.901s
% 1.16/1.35  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.16/1.35  % SZS output start Refutation
% 1.16/1.35  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.16/1.35  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.16/1.35  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 1.16/1.35  thf(sk_B_type, type, sk_B: $i).
% 1.16/1.35  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 1.16/1.35  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.16/1.35  thf(sk_A_type, type, sk_A: $i).
% 1.16/1.35  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.16/1.35  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.16/1.35  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.16/1.35  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.16/1.35  thf(t146_funct_1, conjecture,
% 1.16/1.35    (![A:$i,B:$i]:
% 1.16/1.35     ( ( v1_relat_1 @ B ) =>
% 1.16/1.35       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 1.16/1.35         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 1.16/1.35  thf(zf_stmt_0, negated_conjecture,
% 1.16/1.35    (~( ![A:$i,B:$i]:
% 1.16/1.35        ( ( v1_relat_1 @ B ) =>
% 1.16/1.35          ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 1.16/1.35            ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )),
% 1.16/1.35    inference('cnf.neg', [status(esa)], [t146_funct_1])).
% 1.16/1.35  thf('0', plain,
% 1.16/1.35      (~ (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 1.16/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.16/1.35  thf(t139_funct_1, axiom,
% 1.16/1.35    (![A:$i,B:$i,C:$i]:
% 1.16/1.35     ( ( v1_relat_1 @ C ) =>
% 1.16/1.35       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 1.16/1.35         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 1.16/1.35  thf('1', plain,
% 1.16/1.35      (![X30 : $i, X31 : $i, X32 : $i]:
% 1.16/1.35         (((k10_relat_1 @ (k7_relat_1 @ X31 @ X30) @ X32)
% 1.16/1.35            = (k3_xboole_0 @ X30 @ (k10_relat_1 @ X31 @ X32)))
% 1.16/1.35          | ~ (v1_relat_1 @ X31))),
% 1.16/1.35      inference('cnf', [status(esa)], [t139_funct_1])).
% 1.16/1.35  thf('2', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 1.16/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.16/1.35  thf(t28_xboole_1, axiom,
% 1.16/1.35    (![A:$i,B:$i]:
% 1.16/1.35     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.16/1.35  thf('3', plain,
% 1.16/1.35      (![X18 : $i, X19 : $i]:
% 1.16/1.35         (((k3_xboole_0 @ X18 @ X19) = (X18)) | ~ (r1_tarski @ X18 @ X19))),
% 1.16/1.35      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.16/1.35  thf('4', plain, (((k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)) = (sk_A))),
% 1.16/1.35      inference('sup-', [status(thm)], ['2', '3'])).
% 1.16/1.35  thf(t169_relat_1, axiom,
% 1.16/1.35    (![A:$i]:
% 1.16/1.35     ( ( v1_relat_1 @ A ) =>
% 1.16/1.35       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 1.16/1.35  thf('5', plain,
% 1.16/1.35      (![X27 : $i]:
% 1.16/1.35         (((k10_relat_1 @ X27 @ (k2_relat_1 @ X27)) = (k1_relat_1 @ X27))
% 1.16/1.35          | ~ (v1_relat_1 @ X27))),
% 1.16/1.35      inference('cnf', [status(esa)], [t169_relat_1])).
% 1.16/1.35  thf(t170_relat_1, axiom,
% 1.16/1.35    (![A:$i,B:$i]:
% 1.16/1.35     ( ( v1_relat_1 @ B ) =>
% 1.16/1.35       ( r1_tarski @
% 1.16/1.35         ( k10_relat_1 @ B @ A ) @ ( k10_relat_1 @ B @ ( k2_relat_1 @ B ) ) ) ))).
% 1.16/1.35  thf('6', plain,
% 1.16/1.35      (![X28 : $i, X29 : $i]:
% 1.16/1.35         ((r1_tarski @ (k10_relat_1 @ X28 @ X29) @ 
% 1.16/1.35           (k10_relat_1 @ X28 @ (k2_relat_1 @ X28)))
% 1.16/1.35          | ~ (v1_relat_1 @ X28))),
% 1.16/1.35      inference('cnf', [status(esa)], [t170_relat_1])).
% 1.16/1.35  thf('7', plain,
% 1.16/1.35      (![X0 : $i]:
% 1.16/1.35         ((r1_tarski @ (k1_relat_1 @ X0) @ 
% 1.16/1.35           (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 1.16/1.35          | ~ (v1_relat_1 @ X0)
% 1.16/1.35          | ~ (v1_relat_1 @ X0))),
% 1.16/1.35      inference('sup+', [status(thm)], ['5', '6'])).
% 1.16/1.35  thf('8', plain,
% 1.16/1.35      (![X0 : $i]:
% 1.16/1.35         (~ (v1_relat_1 @ X0)
% 1.16/1.35          | (r1_tarski @ (k1_relat_1 @ X0) @ 
% 1.16/1.35             (k10_relat_1 @ X0 @ (k2_relat_1 @ X0))))),
% 1.16/1.35      inference('simplify', [status(thm)], ['7'])).
% 1.16/1.35  thf(commutativity_k3_xboole_0, axiom,
% 1.16/1.35    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.16/1.35  thf('9', plain,
% 1.16/1.35      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.16/1.35      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.16/1.35  thf('10', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 1.16/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.16/1.35  thf(t108_xboole_1, axiom,
% 1.16/1.35    (![A:$i,B:$i,C:$i]:
% 1.16/1.35     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ B ) ))).
% 1.16/1.35  thf('11', plain,
% 1.16/1.35      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.16/1.35         (~ (r1_tarski @ X5 @ X6) | (r1_tarski @ (k3_xboole_0 @ X5 @ X7) @ X6))),
% 1.16/1.35      inference('cnf', [status(esa)], [t108_xboole_1])).
% 1.16/1.35  thf('12', plain,
% 1.16/1.35      (![X0 : $i]:
% 1.16/1.35         (r1_tarski @ (k3_xboole_0 @ sk_A @ X0) @ (k1_relat_1 @ sk_B))),
% 1.16/1.35      inference('sup-', [status(thm)], ['10', '11'])).
% 1.16/1.35  thf('13', plain,
% 1.16/1.35      (![X18 : $i, X19 : $i]:
% 1.16/1.35         (((k3_xboole_0 @ X18 @ X19) = (X18)) | ~ (r1_tarski @ X18 @ X19))),
% 1.16/1.35      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.16/1.35  thf('14', plain,
% 1.16/1.35      (![X0 : $i]:
% 1.16/1.35         ((k3_xboole_0 @ (k3_xboole_0 @ sk_A @ X0) @ (k1_relat_1 @ sk_B))
% 1.16/1.35           = (k3_xboole_0 @ sk_A @ X0))),
% 1.16/1.35      inference('sup-', [status(thm)], ['12', '13'])).
% 1.16/1.35  thf('15', plain,
% 1.16/1.35      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.16/1.35      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.16/1.35  thf('16', plain,
% 1.16/1.35      (![X0 : $i]:
% 1.16/1.35         ((k3_xboole_0 @ (k1_relat_1 @ sk_B) @ (k3_xboole_0 @ sk_A @ X0))
% 1.16/1.35           = (k3_xboole_0 @ sk_A @ X0))),
% 1.16/1.35      inference('demod', [status(thm)], ['14', '15'])).
% 1.16/1.35  thf(t17_xboole_1, axiom,
% 1.16/1.35    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 1.16/1.35  thf('17', plain,
% 1.16/1.35      (![X13 : $i, X14 : $i]: (r1_tarski @ (k3_xboole_0 @ X13 @ X14) @ X13)),
% 1.16/1.35      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.16/1.35  thf(d10_xboole_0, axiom,
% 1.16/1.35    (![A:$i,B:$i]:
% 1.16/1.35     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.16/1.35  thf('18', plain,
% 1.16/1.35      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 1.16/1.35      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.16/1.35  thf('19', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 1.16/1.35      inference('simplify', [status(thm)], ['18'])).
% 1.16/1.35  thf(t8_xboole_1, axiom,
% 1.16/1.35    (![A:$i,B:$i,C:$i]:
% 1.16/1.35     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 1.16/1.35       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 1.16/1.35  thf('20', plain,
% 1.16/1.35      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.16/1.35         (~ (r1_tarski @ X20 @ X21)
% 1.16/1.35          | ~ (r1_tarski @ X22 @ X21)
% 1.16/1.35          | (r1_tarski @ (k2_xboole_0 @ X20 @ X22) @ X21))),
% 1.16/1.35      inference('cnf', [status(esa)], [t8_xboole_1])).
% 1.16/1.35  thf('21', plain,
% 1.16/1.35      (![X0 : $i, X1 : $i]:
% 1.16/1.35         ((r1_tarski @ (k2_xboole_0 @ X0 @ X1) @ X0) | ~ (r1_tarski @ X1 @ X0))),
% 1.16/1.35      inference('sup-', [status(thm)], ['19', '20'])).
% 1.16/1.35  thf('22', plain,
% 1.16/1.35      (![X0 : $i, X1 : $i]:
% 1.16/1.35         (r1_tarski @ (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)) @ X0)),
% 1.16/1.35      inference('sup-', [status(thm)], ['17', '21'])).
% 1.16/1.35  thf('23', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 1.16/1.35      inference('simplify', [status(thm)], ['18'])).
% 1.16/1.35  thf(t11_xboole_1, axiom,
% 1.16/1.35    (![A:$i,B:$i,C:$i]:
% 1.16/1.35     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 1.16/1.35  thf('24', plain,
% 1.16/1.35      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.16/1.35         ((r1_tarski @ X8 @ X9) | ~ (r1_tarski @ (k2_xboole_0 @ X8 @ X10) @ X9))),
% 1.16/1.35      inference('cnf', [status(esa)], [t11_xboole_1])).
% 1.16/1.35  thf('25', plain,
% 1.16/1.35      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 1.16/1.35      inference('sup-', [status(thm)], ['23', '24'])).
% 1.16/1.35  thf('26', plain,
% 1.16/1.35      (![X2 : $i, X4 : $i]:
% 1.16/1.35         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 1.16/1.35      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.16/1.35  thf('27', plain,
% 1.16/1.35      (![X0 : $i, X1 : $i]:
% 1.16/1.35         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 1.16/1.35          | ((k2_xboole_0 @ X1 @ X0) = (X1)))),
% 1.16/1.35      inference('sup-', [status(thm)], ['25', '26'])).
% 1.16/1.35  thf('28', plain,
% 1.16/1.35      (![X0 : $i, X1 : $i]:
% 1.16/1.35         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)) = (X0))),
% 1.16/1.35      inference('sup-', [status(thm)], ['22', '27'])).
% 1.16/1.35  thf('29', plain,
% 1.16/1.35      (![X0 : $i]:
% 1.16/1.35         ((k2_xboole_0 @ (k1_relat_1 @ sk_B) @ (k3_xboole_0 @ sk_A @ X0))
% 1.16/1.35           = (k1_relat_1 @ sk_B))),
% 1.16/1.35      inference('sup+', [status(thm)], ['16', '28'])).
% 1.16/1.35  thf('30', plain,
% 1.16/1.35      (![X0 : $i]:
% 1.16/1.35         ((k2_xboole_0 @ (k1_relat_1 @ sk_B) @ (k3_xboole_0 @ X0 @ sk_A))
% 1.16/1.35           = (k1_relat_1 @ sk_B))),
% 1.16/1.35      inference('sup+', [status(thm)], ['9', '29'])).
% 1.16/1.35  thf('31', plain,
% 1.16/1.35      (![X27 : $i]:
% 1.16/1.35         (((k10_relat_1 @ X27 @ (k2_relat_1 @ X27)) = (k1_relat_1 @ X27))
% 1.16/1.35          | ~ (v1_relat_1 @ X27))),
% 1.16/1.35      inference('cnf', [status(esa)], [t169_relat_1])).
% 1.16/1.35  thf('32', plain,
% 1.16/1.35      (![X28 : $i, X29 : $i]:
% 1.16/1.35         ((r1_tarski @ (k10_relat_1 @ X28 @ X29) @ 
% 1.16/1.35           (k10_relat_1 @ X28 @ (k2_relat_1 @ X28)))
% 1.16/1.35          | ~ (v1_relat_1 @ X28))),
% 1.16/1.35      inference('cnf', [status(esa)], [t170_relat_1])).
% 1.16/1.35  thf('33', plain,
% 1.16/1.35      (![X0 : $i, X1 : $i]:
% 1.16/1.35         ((r1_tarski @ (k10_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0))
% 1.16/1.35          | ~ (v1_relat_1 @ X0)
% 1.16/1.35          | ~ (v1_relat_1 @ X0))),
% 1.16/1.35      inference('sup+', [status(thm)], ['31', '32'])).
% 1.16/1.35  thf('34', plain,
% 1.16/1.35      (![X0 : $i, X1 : $i]:
% 1.16/1.35         (~ (v1_relat_1 @ X0)
% 1.16/1.35          | (r1_tarski @ (k10_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0)))),
% 1.16/1.35      inference('simplify', [status(thm)], ['33'])).
% 1.16/1.35  thf(t12_xboole_1, axiom,
% 1.16/1.35    (![A:$i,B:$i]:
% 1.16/1.35     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 1.16/1.35  thf('35', plain,
% 1.16/1.35      (![X11 : $i, X12 : $i]:
% 1.16/1.35         (((k2_xboole_0 @ X12 @ X11) = (X11)) | ~ (r1_tarski @ X12 @ X11))),
% 1.16/1.35      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.16/1.35  thf('36', plain,
% 1.16/1.35      (![X0 : $i, X1 : $i]:
% 1.16/1.35         (~ (v1_relat_1 @ X0)
% 1.16/1.35          | ((k2_xboole_0 @ (k10_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0))
% 1.16/1.35              = (k1_relat_1 @ X0)))),
% 1.16/1.35      inference('sup-', [status(thm)], ['34', '35'])).
% 1.16/1.35  thf('37', plain,
% 1.16/1.35      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 1.16/1.35      inference('sup-', [status(thm)], ['23', '24'])).
% 1.16/1.35  thf('38', plain,
% 1.16/1.35      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.16/1.35         ((r1_tarski @ X8 @ X9) | ~ (r1_tarski @ (k2_xboole_0 @ X8 @ X10) @ X9))),
% 1.16/1.35      inference('cnf', [status(esa)], [t11_xboole_1])).
% 1.16/1.35  thf('39', plain,
% 1.16/1.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.16/1.35         (r1_tarski @ X2 @ (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0))),
% 1.16/1.35      inference('sup-', [status(thm)], ['37', '38'])).
% 1.16/1.35  thf('40', plain,
% 1.16/1.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.16/1.35         ((r1_tarski @ (k10_relat_1 @ X0 @ X2) @ 
% 1.16/1.35           (k2_xboole_0 @ (k1_relat_1 @ X0) @ X1))
% 1.16/1.35          | ~ (v1_relat_1 @ X0))),
% 1.16/1.35      inference('sup+', [status(thm)], ['36', '39'])).
% 1.16/1.35  thf('41', plain,
% 1.16/1.35      (![X1 : $i]:
% 1.16/1.35         ((r1_tarski @ (k10_relat_1 @ sk_B @ X1) @ (k1_relat_1 @ sk_B))
% 1.16/1.35          | ~ (v1_relat_1 @ sk_B))),
% 1.16/1.35      inference('sup+', [status(thm)], ['30', '40'])).
% 1.16/1.35  thf('42', plain, ((v1_relat_1 @ sk_B)),
% 1.16/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.16/1.35  thf('43', plain,
% 1.16/1.35      (![X1 : $i]:
% 1.16/1.35         (r1_tarski @ (k10_relat_1 @ sk_B @ X1) @ (k1_relat_1 @ sk_B))),
% 1.16/1.35      inference('demod', [status(thm)], ['41', '42'])).
% 1.16/1.35  thf('44', plain,
% 1.16/1.35      (![X2 : $i, X4 : $i]:
% 1.16/1.35         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 1.16/1.35      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.16/1.35  thf('45', plain,
% 1.16/1.35      (![X0 : $i]:
% 1.16/1.35         (~ (r1_tarski @ (k1_relat_1 @ sk_B) @ (k10_relat_1 @ sk_B @ X0))
% 1.16/1.35          | ((k1_relat_1 @ sk_B) = (k10_relat_1 @ sk_B @ X0)))),
% 1.16/1.35      inference('sup-', [status(thm)], ['43', '44'])).
% 1.16/1.35  thf('46', plain,
% 1.16/1.35      ((~ (v1_relat_1 @ sk_B)
% 1.16/1.35        | ((k1_relat_1 @ sk_B) = (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B))))),
% 1.16/1.35      inference('sup-', [status(thm)], ['8', '45'])).
% 1.16/1.35  thf('47', plain, ((v1_relat_1 @ sk_B)),
% 1.16/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.16/1.35  thf('48', plain,
% 1.16/1.35      (((k1_relat_1 @ sk_B) = (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B)))),
% 1.16/1.35      inference('demod', [status(thm)], ['46', '47'])).
% 1.16/1.35  thf('49', plain,
% 1.16/1.35      (![X30 : $i, X31 : $i, X32 : $i]:
% 1.16/1.35         (((k10_relat_1 @ (k7_relat_1 @ X31 @ X30) @ X32)
% 1.16/1.35            = (k3_xboole_0 @ X30 @ (k10_relat_1 @ X31 @ X32)))
% 1.16/1.35          | ~ (v1_relat_1 @ X31))),
% 1.16/1.35      inference('cnf', [status(esa)], [t139_funct_1])).
% 1.16/1.35  thf('50', plain,
% 1.16/1.35      (![X0 : $i, X1 : $i]:
% 1.16/1.35         (~ (v1_relat_1 @ X0)
% 1.16/1.35          | (r1_tarski @ (k10_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0)))),
% 1.16/1.35      inference('simplify', [status(thm)], ['33'])).
% 1.16/1.35  thf('51', plain,
% 1.16/1.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.16/1.35         ((r1_tarski @ (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0)) @ 
% 1.16/1.35           (k1_relat_1 @ (k7_relat_1 @ X1 @ X2)))
% 1.16/1.35          | ~ (v1_relat_1 @ X1)
% 1.16/1.35          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X2)))),
% 1.16/1.35      inference('sup+', [status(thm)], ['49', '50'])).
% 1.16/1.35  thf(dt_k7_relat_1, axiom,
% 1.16/1.35    (![A:$i,B:$i]:
% 1.16/1.35     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 1.16/1.35  thf('52', plain,
% 1.16/1.35      (![X23 : $i, X24 : $i]:
% 1.16/1.35         (~ (v1_relat_1 @ X23) | (v1_relat_1 @ (k7_relat_1 @ X23 @ X24)))),
% 1.16/1.35      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 1.16/1.35  thf('53', plain,
% 1.16/1.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.16/1.35         (~ (v1_relat_1 @ X1)
% 1.16/1.35          | (r1_tarski @ (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0)) @ 
% 1.16/1.35             (k1_relat_1 @ (k7_relat_1 @ X1 @ X2))))),
% 1.16/1.35      inference('clc', [status(thm)], ['51', '52'])).
% 1.16/1.35  thf('54', plain,
% 1.16/1.35      (![X0 : $i]:
% 1.16/1.35         ((r1_tarski @ (k3_xboole_0 @ X0 @ (k1_relat_1 @ sk_B)) @ 
% 1.16/1.35           (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)))
% 1.16/1.35          | ~ (v1_relat_1 @ sk_B))),
% 1.16/1.35      inference('sup+', [status(thm)], ['48', '53'])).
% 1.16/1.35  thf('55', plain, ((v1_relat_1 @ sk_B)),
% 1.16/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.16/1.35  thf('56', plain,
% 1.16/1.35      (![X0 : $i]:
% 1.16/1.35         (r1_tarski @ (k3_xboole_0 @ X0 @ (k1_relat_1 @ sk_B)) @ 
% 1.16/1.35          (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)))),
% 1.16/1.35      inference('demod', [status(thm)], ['54', '55'])).
% 1.16/1.35  thf('57', plain,
% 1.16/1.35      ((r1_tarski @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 1.16/1.35      inference('sup+', [status(thm)], ['4', '56'])).
% 1.16/1.35  thf('58', plain,
% 1.16/1.35      (![X30 : $i, X31 : $i, X32 : $i]:
% 1.16/1.35         (((k10_relat_1 @ (k7_relat_1 @ X31 @ X30) @ X32)
% 1.16/1.35            = (k3_xboole_0 @ X30 @ (k10_relat_1 @ X31 @ X32)))
% 1.16/1.35          | ~ (v1_relat_1 @ X31))),
% 1.16/1.35      inference('cnf', [status(esa)], [t139_funct_1])).
% 1.16/1.35  thf('59', plain,
% 1.16/1.35      (![X27 : $i]:
% 1.16/1.35         (((k10_relat_1 @ X27 @ (k2_relat_1 @ X27)) = (k1_relat_1 @ X27))
% 1.16/1.35          | ~ (v1_relat_1 @ X27))),
% 1.16/1.35      inference('cnf', [status(esa)], [t169_relat_1])).
% 1.16/1.35  thf('60', plain,
% 1.16/1.35      (![X0 : $i, X1 : $i]:
% 1.16/1.35         (((k3_xboole_0 @ X0 @ 
% 1.16/1.35            (k10_relat_1 @ X1 @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X0))))
% 1.16/1.35            = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 1.16/1.35          | ~ (v1_relat_1 @ X1)
% 1.16/1.35          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 1.16/1.35      inference('sup+', [status(thm)], ['58', '59'])).
% 1.16/1.35  thf('61', plain,
% 1.16/1.35      (![X23 : $i, X24 : $i]:
% 1.16/1.35         (~ (v1_relat_1 @ X23) | (v1_relat_1 @ (k7_relat_1 @ X23 @ X24)))),
% 1.16/1.35      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 1.16/1.35  thf('62', plain,
% 1.16/1.35      (![X0 : $i, X1 : $i]:
% 1.16/1.35         (~ (v1_relat_1 @ X1)
% 1.16/1.35          | ((k3_xboole_0 @ X0 @ 
% 1.16/1.35              (k10_relat_1 @ X1 @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X0))))
% 1.16/1.35              = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 1.16/1.35      inference('clc', [status(thm)], ['60', '61'])).
% 1.16/1.35  thf('63', plain,
% 1.16/1.35      (![X13 : $i, X14 : $i]: (r1_tarski @ (k3_xboole_0 @ X13 @ X14) @ X13)),
% 1.16/1.35      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.16/1.35  thf('64', plain,
% 1.16/1.35      (![X0 : $i, X1 : $i]:
% 1.16/1.35         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X0)
% 1.16/1.35          | ~ (v1_relat_1 @ X1))),
% 1.16/1.35      inference('sup+', [status(thm)], ['62', '63'])).
% 1.16/1.35  thf('65', plain,
% 1.16/1.35      (![X2 : $i, X4 : $i]:
% 1.16/1.35         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 1.16/1.35      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.16/1.35  thf('66', plain,
% 1.16/1.35      (![X0 : $i, X1 : $i]:
% 1.16/1.35         (~ (v1_relat_1 @ X1)
% 1.16/1.35          | ~ (r1_tarski @ X0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 1.16/1.35          | ((X0) = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 1.16/1.35      inference('sup-', [status(thm)], ['64', '65'])).
% 1.16/1.35  thf('67', plain,
% 1.16/1.35      ((((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 1.16/1.35        | ~ (v1_relat_1 @ sk_B))),
% 1.16/1.35      inference('sup-', [status(thm)], ['57', '66'])).
% 1.16/1.35  thf('68', plain, ((v1_relat_1 @ sk_B)),
% 1.16/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.16/1.35  thf('69', plain, (((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 1.16/1.35      inference('demod', [status(thm)], ['67', '68'])).
% 1.16/1.35  thf(t148_relat_1, axiom,
% 1.16/1.35    (![A:$i,B:$i]:
% 1.16/1.35     ( ( v1_relat_1 @ B ) =>
% 1.16/1.35       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 1.16/1.35  thf('70', plain,
% 1.16/1.35      (![X25 : $i, X26 : $i]:
% 1.16/1.35         (((k2_relat_1 @ (k7_relat_1 @ X25 @ X26)) = (k9_relat_1 @ X25 @ X26))
% 1.16/1.35          | ~ (v1_relat_1 @ X25))),
% 1.16/1.35      inference('cnf', [status(esa)], [t148_relat_1])).
% 1.16/1.35  thf('71', plain,
% 1.16/1.35      (![X0 : $i]:
% 1.16/1.35         (~ (v1_relat_1 @ X0)
% 1.16/1.35          | (r1_tarski @ (k1_relat_1 @ X0) @ 
% 1.16/1.35             (k10_relat_1 @ X0 @ (k2_relat_1 @ X0))))),
% 1.16/1.35      inference('simplify', [status(thm)], ['7'])).
% 1.16/1.35  thf('72', plain,
% 1.16/1.35      (![X0 : $i, X1 : $i]:
% 1.16/1.35         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ 
% 1.16/1.35           (k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0)))
% 1.16/1.35          | ~ (v1_relat_1 @ X1)
% 1.16/1.35          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 1.16/1.35      inference('sup+', [status(thm)], ['70', '71'])).
% 1.16/1.35  thf('73', plain,
% 1.16/1.35      (![X23 : $i, X24 : $i]:
% 1.16/1.35         (~ (v1_relat_1 @ X23) | (v1_relat_1 @ (k7_relat_1 @ X23 @ X24)))),
% 1.16/1.35      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 1.16/1.35  thf('74', plain,
% 1.16/1.35      (![X0 : $i, X1 : $i]:
% 1.16/1.35         (~ (v1_relat_1 @ X1)
% 1.16/1.35          | (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ 
% 1.16/1.35             (k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0))))),
% 1.16/1.35      inference('clc', [status(thm)], ['72', '73'])).
% 1.16/1.35  thf('75', plain,
% 1.16/1.35      (((r1_tarski @ sk_A @ 
% 1.16/1.35         (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ (k9_relat_1 @ sk_B @ sk_A)))
% 1.16/1.35        | ~ (v1_relat_1 @ sk_B))),
% 1.16/1.35      inference('sup+', [status(thm)], ['69', '74'])).
% 1.16/1.35  thf('76', plain, ((v1_relat_1 @ sk_B)),
% 1.16/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.16/1.35  thf('77', plain,
% 1.16/1.35      ((r1_tarski @ sk_A @ 
% 1.16/1.35        (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ (k9_relat_1 @ sk_B @ sk_A)))),
% 1.16/1.35      inference('demod', [status(thm)], ['75', '76'])).
% 1.16/1.35  thf('78', plain,
% 1.16/1.35      (((r1_tarski @ sk_A @ 
% 1.16/1.35         (k3_xboole_0 @ sk_A @ 
% 1.16/1.35          (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A))))
% 1.16/1.35        | ~ (v1_relat_1 @ sk_B))),
% 1.16/1.35      inference('sup+', [status(thm)], ['1', '77'])).
% 1.16/1.35  thf('79', plain, ((v1_relat_1 @ sk_B)),
% 1.16/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.16/1.35  thf('80', plain,
% 1.16/1.35      ((r1_tarski @ sk_A @ 
% 1.16/1.35        (k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A))))),
% 1.16/1.35      inference('demod', [status(thm)], ['78', '79'])).
% 1.16/1.35  thf('81', plain,
% 1.16/1.35      (![X13 : $i, X14 : $i]: (r1_tarski @ (k3_xboole_0 @ X13 @ X14) @ X13)),
% 1.16/1.35      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.16/1.35  thf('82', plain,
% 1.16/1.35      (![X2 : $i, X4 : $i]:
% 1.16/1.35         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 1.16/1.35      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.16/1.35  thf('83', plain,
% 1.16/1.35      (![X0 : $i, X1 : $i]:
% 1.16/1.35         (~ (r1_tarski @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 1.16/1.35          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 1.16/1.35      inference('sup-', [status(thm)], ['81', '82'])).
% 1.16/1.35  thf('84', plain,
% 1.16/1.35      (((sk_A)
% 1.16/1.35         = (k3_xboole_0 @ sk_A @ 
% 1.16/1.35            (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A))))),
% 1.16/1.35      inference('sup-', [status(thm)], ['80', '83'])).
% 1.16/1.35  thf('85', plain,
% 1.16/1.35      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.16/1.35      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.16/1.35  thf('86', plain,
% 1.16/1.35      (![X13 : $i, X14 : $i]: (r1_tarski @ (k3_xboole_0 @ X13 @ X14) @ X13)),
% 1.16/1.35      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.16/1.35  thf('87', plain,
% 1.16/1.35      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 1.16/1.35      inference('sup+', [status(thm)], ['85', '86'])).
% 1.16/1.35  thf('88', plain,
% 1.16/1.35      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 1.16/1.35      inference('sup+', [status(thm)], ['84', '87'])).
% 1.16/1.35  thf('89', plain, ($false), inference('demod', [status(thm)], ['0', '88'])).
% 1.16/1.35  
% 1.16/1.35  % SZS output end Refutation
% 1.16/1.35  
% 1.16/1.36  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
