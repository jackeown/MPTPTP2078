%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RyQjyp16XS

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:22 EST 2020

% Result     : Theorem 2.65s
% Output     : Refutation 2.65s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 195 expanded)
%              Number of leaves         :   21 (  66 expanded)
%              Depth                    :   24
%              Number of atoms          :  712 (1686 expanded)
%              Number of equality atoms :   39 (  85 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('1',plain,(
    ! [X16: $i] :
      ( ( ( k10_relat_1 @ X16 @ ( k2_relat_1 @ X16 ) )
        = ( k1_relat_1 @ X16 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf(t139_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('2',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X23 @ X22 ) @ X24 )
        = ( k3_xboole_0 @ X22 @ ( k10_relat_1 @ X23 @ X24 ) ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

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

thf('3',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t108_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ B ) ) )).

thf('4',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ( r1_tarski @ ( k3_xboole_0 @ X5 @ X7 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t108_xboole_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_A @ X0 ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('6',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ sk_A @ X0 ) @ ( k1_relat_1 @ sk_B ) )
      = ( k3_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k3_xboole_0 @ sk_A @ X0 ) )
      = ( k3_xboole_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k10_relat_1 @ ( k7_relat_1 @ X1 @ sk_A ) @ X0 ) )
        = ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','9'])).

thf('11',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X23 @ X22 ) @ X24 )
        = ( k3_xboole_0 @ X22 @ ( k10_relat_1 @ X23 @ X24 ) ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('13',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('14',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['13'])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('15',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X20 ) @ X21 )
      | ( ( k7_relat_1 @ X20 @ X21 )
        = X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X23 @ X22 ) @ X24 )
        = ( k3_xboole_0 @ X22 @ ( k10_relat_1 @ X23 @ X24 ) ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('18',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ( r1_tarski @ ( k3_xboole_0 @ X5 @ X7 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t108_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_xboole_0 @ ( k10_relat_1 @ X0 @ X1 ) @ X2 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['12','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) @ ( k1_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['11','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) @ ( k1_relat_1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k3_xboole_0 @ ( k10_relat_1 @ ( k7_relat_1 @ X0 @ X2 ) @ X1 ) @ ( k1_relat_1 @ X0 ) )
        = ( k10_relat_1 @ ( k7_relat_1 @ X0 @ X2 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k3_xboole_0 @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ ( k7_relat_1 @ X0 @ X2 ) @ X1 ) )
        = ( k10_relat_1 @ ( k7_relat_1 @ X0 @ X2 ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ X0 ) )
        = ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['10','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ X0 ) )
      = ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('36',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) @ ( k10_relat_1 @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['34','37'])).

thf('39',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) @ ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['1','38'])).

thf('40',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('41',plain,(
    ! [X16: $i] :
      ( ( ( k10_relat_1 @ X16 @ ( k2_relat_1 @ X16 ) )
        = ( k1_relat_1 @ X16 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ X0 ) )
      = ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('43',plain,
    ( ( ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) )
      = ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('46',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) )
    = sk_A ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( sk_A
    = ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['43','46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('50',plain,
    ( ( r1_tarski @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r1_tarski @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['40','50'])).

thf('52',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X16: $i] :
      ( ( ( k10_relat_1 @ X16 @ ( k2_relat_1 @ X16 ) )
        = ( k1_relat_1 @ X16 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference(clc,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
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
    inference('sup-',[status(thm)],['53','60'])).

thf('62',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( sk_A
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['39','63'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('65',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X14 @ X15 ) )
        = ( k9_relat_1 @ X14 @ X15 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('66',plain,(
    ~ ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ~ ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['64','69'])).

thf('71',plain,(
    ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','70'])).

thf('72',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    $false ),
    inference(demod,[status(thm)],['71','72'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RyQjyp16XS
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:09:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 2.65/2.87  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.65/2.87  % Solved by: fo/fo7.sh
% 2.65/2.87  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.65/2.87  % done 2817 iterations in 2.427s
% 2.65/2.87  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.65/2.87  % SZS output start Refutation
% 2.65/2.87  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.65/2.87  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 2.65/2.87  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.65/2.87  thf(sk_B_type, type, sk_B: $i).
% 2.65/2.87  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.65/2.87  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.65/2.87  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 2.65/2.87  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 2.65/2.87  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.65/2.87  thf(sk_A_type, type, sk_A: $i).
% 2.65/2.87  thf(dt_k7_relat_1, axiom,
% 2.65/2.87    (![A:$i,B:$i]:
% 2.65/2.87     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 2.65/2.87  thf('0', plain,
% 2.65/2.87      (![X12 : $i, X13 : $i]:
% 2.65/2.87         (~ (v1_relat_1 @ X12) | (v1_relat_1 @ (k7_relat_1 @ X12 @ X13)))),
% 2.65/2.87      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 2.65/2.87  thf(t169_relat_1, axiom,
% 2.65/2.87    (![A:$i]:
% 2.65/2.87     ( ( v1_relat_1 @ A ) =>
% 2.65/2.87       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 2.65/2.87  thf('1', plain,
% 2.65/2.87      (![X16 : $i]:
% 2.65/2.87         (((k10_relat_1 @ X16 @ (k2_relat_1 @ X16)) = (k1_relat_1 @ X16))
% 2.65/2.87          | ~ (v1_relat_1 @ X16))),
% 2.65/2.87      inference('cnf', [status(esa)], [t169_relat_1])).
% 2.65/2.87  thf(t139_funct_1, axiom,
% 2.65/2.87    (![A:$i,B:$i,C:$i]:
% 2.65/2.87     ( ( v1_relat_1 @ C ) =>
% 2.65/2.87       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 2.65/2.87         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 2.65/2.87  thf('2', plain,
% 2.65/2.87      (![X22 : $i, X23 : $i, X24 : $i]:
% 2.65/2.87         (((k10_relat_1 @ (k7_relat_1 @ X23 @ X22) @ X24)
% 2.65/2.87            = (k3_xboole_0 @ X22 @ (k10_relat_1 @ X23 @ X24)))
% 2.65/2.87          | ~ (v1_relat_1 @ X23))),
% 2.65/2.87      inference('cnf', [status(esa)], [t139_funct_1])).
% 2.65/2.87  thf(t146_funct_1, conjecture,
% 2.65/2.87    (![A:$i,B:$i]:
% 2.65/2.87     ( ( v1_relat_1 @ B ) =>
% 2.65/2.87       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 2.65/2.87         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 2.65/2.87  thf(zf_stmt_0, negated_conjecture,
% 2.65/2.87    (~( ![A:$i,B:$i]:
% 2.65/2.87        ( ( v1_relat_1 @ B ) =>
% 2.65/2.87          ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 2.65/2.87            ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )),
% 2.65/2.87    inference('cnf.neg', [status(esa)], [t146_funct_1])).
% 2.65/2.87  thf('3', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 2.65/2.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.65/2.87  thf(t108_xboole_1, axiom,
% 2.65/2.87    (![A:$i,B:$i,C:$i]:
% 2.65/2.87     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ B ) ))).
% 2.65/2.87  thf('4', plain,
% 2.65/2.87      (![X5 : $i, X6 : $i, X7 : $i]:
% 2.65/2.87         (~ (r1_tarski @ X5 @ X6) | (r1_tarski @ (k3_xboole_0 @ X5 @ X7) @ X6))),
% 2.65/2.87      inference('cnf', [status(esa)], [t108_xboole_1])).
% 2.65/2.87  thf('5', plain,
% 2.65/2.87      (![X0 : $i]:
% 2.65/2.87         (r1_tarski @ (k3_xboole_0 @ sk_A @ X0) @ (k1_relat_1 @ sk_B))),
% 2.65/2.87      inference('sup-', [status(thm)], ['3', '4'])).
% 2.65/2.87  thf(t28_xboole_1, axiom,
% 2.65/2.87    (![A:$i,B:$i]:
% 2.65/2.87     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 2.65/2.87  thf('6', plain,
% 2.65/2.87      (![X10 : $i, X11 : $i]:
% 2.65/2.87         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 2.65/2.87      inference('cnf', [status(esa)], [t28_xboole_1])).
% 2.65/2.87  thf('7', plain,
% 2.65/2.87      (![X0 : $i]:
% 2.65/2.87         ((k3_xboole_0 @ (k3_xboole_0 @ sk_A @ X0) @ (k1_relat_1 @ sk_B))
% 2.65/2.87           = (k3_xboole_0 @ sk_A @ X0))),
% 2.65/2.87      inference('sup-', [status(thm)], ['5', '6'])).
% 2.65/2.87  thf(commutativity_k3_xboole_0, axiom,
% 2.65/2.87    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 2.65/2.87  thf('8', plain,
% 2.65/2.87      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.65/2.87      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.65/2.87  thf('9', plain,
% 2.65/2.87      (![X0 : $i]:
% 2.65/2.87         ((k3_xboole_0 @ (k1_relat_1 @ sk_B) @ (k3_xboole_0 @ sk_A @ X0))
% 2.65/2.87           = (k3_xboole_0 @ sk_A @ X0))),
% 2.65/2.87      inference('demod', [status(thm)], ['7', '8'])).
% 2.65/2.87  thf('10', plain,
% 2.65/2.87      (![X0 : $i, X1 : $i]:
% 2.65/2.87         (((k3_xboole_0 @ (k1_relat_1 @ sk_B) @ 
% 2.65/2.87            (k10_relat_1 @ (k7_relat_1 @ X1 @ sk_A) @ X0))
% 2.65/2.87            = (k3_xboole_0 @ sk_A @ (k10_relat_1 @ X1 @ X0)))
% 2.65/2.87          | ~ (v1_relat_1 @ X1))),
% 2.65/2.87      inference('sup+', [status(thm)], ['2', '9'])).
% 2.65/2.87  thf('11', plain,
% 2.65/2.87      (![X22 : $i, X23 : $i, X24 : $i]:
% 2.65/2.87         (((k10_relat_1 @ (k7_relat_1 @ X23 @ X22) @ X24)
% 2.65/2.87            = (k3_xboole_0 @ X22 @ (k10_relat_1 @ X23 @ X24)))
% 2.65/2.87          | ~ (v1_relat_1 @ X23))),
% 2.65/2.87      inference('cnf', [status(esa)], [t139_funct_1])).
% 2.65/2.87  thf('12', plain,
% 2.65/2.87      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.65/2.87      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.65/2.87  thf(d10_xboole_0, axiom,
% 2.65/2.87    (![A:$i,B:$i]:
% 2.65/2.87     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.65/2.87  thf('13', plain,
% 2.65/2.87      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 2.65/2.87      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.65/2.87  thf('14', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 2.65/2.87      inference('simplify', [status(thm)], ['13'])).
% 2.65/2.87  thf(t97_relat_1, axiom,
% 2.65/2.87    (![A:$i,B:$i]:
% 2.65/2.87     ( ( v1_relat_1 @ B ) =>
% 2.65/2.87       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 2.65/2.87         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 2.65/2.87  thf('15', plain,
% 2.65/2.87      (![X20 : $i, X21 : $i]:
% 2.65/2.87         (~ (r1_tarski @ (k1_relat_1 @ X20) @ X21)
% 2.65/2.87          | ((k7_relat_1 @ X20 @ X21) = (X20))
% 2.65/2.87          | ~ (v1_relat_1 @ X20))),
% 2.65/2.87      inference('cnf', [status(esa)], [t97_relat_1])).
% 2.65/2.87  thf('16', plain,
% 2.65/2.87      (![X0 : $i]:
% 2.65/2.87         (~ (v1_relat_1 @ X0) | ((k7_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (X0)))),
% 2.65/2.87      inference('sup-', [status(thm)], ['14', '15'])).
% 2.65/2.87  thf('17', plain,
% 2.65/2.87      (![X22 : $i, X23 : $i, X24 : $i]:
% 2.65/2.87         (((k10_relat_1 @ (k7_relat_1 @ X23 @ X22) @ X24)
% 2.65/2.87            = (k3_xboole_0 @ X22 @ (k10_relat_1 @ X23 @ X24)))
% 2.65/2.87          | ~ (v1_relat_1 @ X23))),
% 2.65/2.87      inference('cnf', [status(esa)], [t139_funct_1])).
% 2.65/2.87  thf(t17_xboole_1, axiom,
% 2.65/2.87    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 2.65/2.87  thf('18', plain,
% 2.65/2.87      (![X8 : $i, X9 : $i]: (r1_tarski @ (k3_xboole_0 @ X8 @ X9) @ X8)),
% 2.65/2.87      inference('cnf', [status(esa)], [t17_xboole_1])).
% 2.65/2.87  thf('19', plain,
% 2.65/2.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.65/2.87         ((r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0) @ X1)
% 2.65/2.87          | ~ (v1_relat_1 @ X2))),
% 2.65/2.87      inference('sup+', [status(thm)], ['17', '18'])).
% 2.65/2.87  thf('20', plain,
% 2.65/2.87      (![X0 : $i, X1 : $i]:
% 2.65/2.87         ((r1_tarski @ (k10_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0))
% 2.65/2.87          | ~ (v1_relat_1 @ X0)
% 2.65/2.87          | ~ (v1_relat_1 @ X0))),
% 2.65/2.87      inference('sup+', [status(thm)], ['16', '19'])).
% 2.65/2.87  thf('21', plain,
% 2.65/2.87      (![X0 : $i, X1 : $i]:
% 2.65/2.87         (~ (v1_relat_1 @ X0)
% 2.65/2.87          | (r1_tarski @ (k10_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0)))),
% 2.65/2.87      inference('simplify', [status(thm)], ['20'])).
% 2.65/2.87  thf('22', plain,
% 2.65/2.87      (![X5 : $i, X6 : $i, X7 : $i]:
% 2.65/2.87         (~ (r1_tarski @ X5 @ X6) | (r1_tarski @ (k3_xboole_0 @ X5 @ X7) @ X6))),
% 2.65/2.87      inference('cnf', [status(esa)], [t108_xboole_1])).
% 2.65/2.87  thf('23', plain,
% 2.65/2.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.65/2.87         (~ (v1_relat_1 @ X0)
% 2.65/2.87          | (r1_tarski @ (k3_xboole_0 @ (k10_relat_1 @ X0 @ X1) @ X2) @ 
% 2.65/2.87             (k1_relat_1 @ X0)))),
% 2.65/2.87      inference('sup-', [status(thm)], ['21', '22'])).
% 2.65/2.87  thf('24', plain,
% 2.65/2.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.65/2.87         ((r1_tarski @ (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0)) @ 
% 2.65/2.87           (k1_relat_1 @ X1))
% 2.65/2.87          | ~ (v1_relat_1 @ X1))),
% 2.65/2.87      inference('sup+', [status(thm)], ['12', '23'])).
% 2.65/2.87  thf('25', plain,
% 2.65/2.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.65/2.87         ((r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0) @ 
% 2.65/2.87           (k1_relat_1 @ X2))
% 2.65/2.87          | ~ (v1_relat_1 @ X2)
% 2.65/2.87          | ~ (v1_relat_1 @ X2))),
% 2.65/2.87      inference('sup+', [status(thm)], ['11', '24'])).
% 2.65/2.87  thf('26', plain,
% 2.65/2.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.65/2.87         (~ (v1_relat_1 @ X2)
% 2.65/2.87          | (r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0) @ 
% 2.65/2.87             (k1_relat_1 @ X2)))),
% 2.65/2.87      inference('simplify', [status(thm)], ['25'])).
% 2.65/2.87  thf('27', plain,
% 2.65/2.87      (![X10 : $i, X11 : $i]:
% 2.65/2.87         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 2.65/2.87      inference('cnf', [status(esa)], [t28_xboole_1])).
% 2.65/2.87  thf('28', plain,
% 2.65/2.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.65/2.87         (~ (v1_relat_1 @ X0)
% 2.65/2.87          | ((k3_xboole_0 @ (k10_relat_1 @ (k7_relat_1 @ X0 @ X2) @ X1) @ 
% 2.65/2.87              (k1_relat_1 @ X0)) = (k10_relat_1 @ (k7_relat_1 @ X0 @ X2) @ X1)))),
% 2.65/2.87      inference('sup-', [status(thm)], ['26', '27'])).
% 2.65/2.87  thf('29', plain,
% 2.65/2.87      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.65/2.87      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.65/2.87  thf('30', plain,
% 2.65/2.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.65/2.87         (~ (v1_relat_1 @ X0)
% 2.65/2.87          | ((k3_xboole_0 @ (k1_relat_1 @ X0) @ 
% 2.65/2.87              (k10_relat_1 @ (k7_relat_1 @ X0 @ X2) @ X1))
% 2.65/2.87              = (k10_relat_1 @ (k7_relat_1 @ X0 @ X2) @ X1)))),
% 2.65/2.87      inference('demod', [status(thm)], ['28', '29'])).
% 2.65/2.87  thf('31', plain,
% 2.65/2.87      (![X0 : $i]:
% 2.65/2.87         (((k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ X0))
% 2.65/2.87            = (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0))
% 2.65/2.87          | ~ (v1_relat_1 @ sk_B)
% 2.65/2.87          | ~ (v1_relat_1 @ sk_B))),
% 2.65/2.87      inference('sup+', [status(thm)], ['10', '30'])).
% 2.65/2.87  thf('32', plain, ((v1_relat_1 @ sk_B)),
% 2.65/2.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.65/2.87  thf('33', plain, ((v1_relat_1 @ sk_B)),
% 2.65/2.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.65/2.87  thf('34', plain,
% 2.65/2.87      (![X0 : $i]:
% 2.65/2.87         ((k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ X0))
% 2.65/2.87           = (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0))),
% 2.65/2.87      inference('demod', [status(thm)], ['31', '32', '33'])).
% 2.65/2.87  thf('35', plain,
% 2.65/2.87      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.65/2.87      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.65/2.87  thf('36', plain,
% 2.65/2.87      (![X8 : $i, X9 : $i]: (r1_tarski @ (k3_xboole_0 @ X8 @ X9) @ X8)),
% 2.65/2.87      inference('cnf', [status(esa)], [t17_xboole_1])).
% 2.65/2.87  thf('37', plain,
% 2.65/2.87      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 2.65/2.87      inference('sup+', [status(thm)], ['35', '36'])).
% 2.65/2.87  thf('38', plain,
% 2.65/2.87      (![X0 : $i]:
% 2.65/2.87         (r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0) @ 
% 2.65/2.87          (k10_relat_1 @ sk_B @ X0))),
% 2.65/2.87      inference('sup+', [status(thm)], ['34', '37'])).
% 2.65/2.87  thf('39', plain,
% 2.65/2.87      (((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) @ 
% 2.65/2.87         (k10_relat_1 @ sk_B @ (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))))
% 2.65/2.87        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 2.65/2.87      inference('sup+', [status(thm)], ['1', '38'])).
% 2.65/2.87  thf('40', plain,
% 2.65/2.87      (![X12 : $i, X13 : $i]:
% 2.65/2.87         (~ (v1_relat_1 @ X12) | (v1_relat_1 @ (k7_relat_1 @ X12 @ X13)))),
% 2.65/2.87      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 2.65/2.87  thf('41', plain,
% 2.65/2.87      (![X16 : $i]:
% 2.65/2.87         (((k10_relat_1 @ X16 @ (k2_relat_1 @ X16)) = (k1_relat_1 @ X16))
% 2.65/2.87          | ~ (v1_relat_1 @ X16))),
% 2.65/2.87      inference('cnf', [status(esa)], [t169_relat_1])).
% 2.65/2.87  thf('42', plain,
% 2.65/2.87      (![X0 : $i]:
% 2.65/2.87         ((k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ X0))
% 2.65/2.87           = (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0))),
% 2.65/2.87      inference('demod', [status(thm)], ['31', '32', '33'])).
% 2.65/2.87  thf('43', plain,
% 2.65/2.87      ((((k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B))
% 2.65/2.87          = (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ (k2_relat_1 @ sk_B)))
% 2.65/2.87        | ~ (v1_relat_1 @ sk_B))),
% 2.65/2.87      inference('sup+', [status(thm)], ['41', '42'])).
% 2.65/2.87  thf('44', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 2.65/2.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.65/2.87  thf('45', plain,
% 2.65/2.87      (![X10 : $i, X11 : $i]:
% 2.65/2.87         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 2.65/2.87      inference('cnf', [status(esa)], [t28_xboole_1])).
% 2.65/2.87  thf('46', plain, (((k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)) = (sk_A))),
% 2.65/2.87      inference('sup-', [status(thm)], ['44', '45'])).
% 2.65/2.87  thf('47', plain, ((v1_relat_1 @ sk_B)),
% 2.65/2.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.65/2.87  thf('48', plain,
% 2.65/2.87      (((sk_A)
% 2.65/2.87         = (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ (k2_relat_1 @ sk_B)))),
% 2.65/2.87      inference('demod', [status(thm)], ['43', '46', '47'])).
% 2.65/2.87  thf('49', plain,
% 2.65/2.87      (![X0 : $i, X1 : $i]:
% 2.65/2.87         (~ (v1_relat_1 @ X0)
% 2.65/2.87          | (r1_tarski @ (k10_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0)))),
% 2.65/2.87      inference('simplify', [status(thm)], ['20'])).
% 2.65/2.87  thf('50', plain,
% 2.65/2.87      (((r1_tarski @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 2.65/2.87        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 2.65/2.87      inference('sup+', [status(thm)], ['48', '49'])).
% 2.65/2.87  thf('51', plain,
% 2.65/2.87      ((~ (v1_relat_1 @ sk_B)
% 2.65/2.87        | (r1_tarski @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))))),
% 2.65/2.87      inference('sup-', [status(thm)], ['40', '50'])).
% 2.65/2.87  thf('52', plain, ((v1_relat_1 @ sk_B)),
% 2.65/2.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.65/2.87  thf('53', plain,
% 2.65/2.87      ((r1_tarski @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 2.65/2.87      inference('demod', [status(thm)], ['51', '52'])).
% 2.65/2.87  thf('54', plain,
% 2.65/2.87      (![X16 : $i]:
% 2.65/2.87         (((k10_relat_1 @ X16 @ (k2_relat_1 @ X16)) = (k1_relat_1 @ X16))
% 2.65/2.87          | ~ (v1_relat_1 @ X16))),
% 2.65/2.87      inference('cnf', [status(esa)], [t169_relat_1])).
% 2.65/2.87  thf('55', plain,
% 2.65/2.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.65/2.87         ((r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0) @ X1)
% 2.65/2.87          | ~ (v1_relat_1 @ X2))),
% 2.65/2.87      inference('sup+', [status(thm)], ['17', '18'])).
% 2.65/2.87  thf('56', plain,
% 2.65/2.87      (![X0 : $i, X1 : $i]:
% 2.65/2.87         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X0)
% 2.65/2.87          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 2.65/2.87          | ~ (v1_relat_1 @ X1))),
% 2.65/2.87      inference('sup+', [status(thm)], ['54', '55'])).
% 2.65/2.87  thf('57', plain,
% 2.65/2.87      (![X12 : $i, X13 : $i]:
% 2.65/2.87         (~ (v1_relat_1 @ X12) | (v1_relat_1 @ (k7_relat_1 @ X12 @ X13)))),
% 2.65/2.87      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 2.65/2.87  thf('58', plain,
% 2.65/2.87      (![X0 : $i, X1 : $i]:
% 2.65/2.87         (~ (v1_relat_1 @ X1)
% 2.65/2.87          | (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X0))),
% 2.65/2.87      inference('clc', [status(thm)], ['56', '57'])).
% 2.65/2.87  thf('59', plain,
% 2.65/2.87      (![X2 : $i, X4 : $i]:
% 2.65/2.87         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 2.65/2.87      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.65/2.87  thf('60', plain,
% 2.65/2.87      (![X0 : $i, X1 : $i]:
% 2.65/2.87         (~ (v1_relat_1 @ X1)
% 2.65/2.87          | ~ (r1_tarski @ X0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 2.65/2.87          | ((X0) = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 2.65/2.87      inference('sup-', [status(thm)], ['58', '59'])).
% 2.65/2.87  thf('61', plain,
% 2.65/2.87      ((((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 2.65/2.87        | ~ (v1_relat_1 @ sk_B))),
% 2.65/2.87      inference('sup-', [status(thm)], ['53', '60'])).
% 2.65/2.87  thf('62', plain, ((v1_relat_1 @ sk_B)),
% 2.65/2.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.65/2.87  thf('63', plain, (((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 2.65/2.87      inference('demod', [status(thm)], ['61', '62'])).
% 2.65/2.87  thf('64', plain,
% 2.65/2.87      (((r1_tarski @ sk_A @ 
% 2.65/2.87         (k10_relat_1 @ sk_B @ (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))))
% 2.65/2.87        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 2.65/2.87      inference('demod', [status(thm)], ['39', '63'])).
% 2.65/2.87  thf(t148_relat_1, axiom,
% 2.65/2.87    (![A:$i,B:$i]:
% 2.65/2.87     ( ( v1_relat_1 @ B ) =>
% 2.65/2.87       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 2.65/2.87  thf('65', plain,
% 2.65/2.87      (![X14 : $i, X15 : $i]:
% 2.65/2.87         (((k2_relat_1 @ (k7_relat_1 @ X14 @ X15)) = (k9_relat_1 @ X14 @ X15))
% 2.65/2.87          | ~ (v1_relat_1 @ X14))),
% 2.65/2.87      inference('cnf', [status(esa)], [t148_relat_1])).
% 2.65/2.87  thf('66', plain,
% 2.65/2.87      (~ (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 2.65/2.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.65/2.87  thf('67', plain,
% 2.65/2.87      ((~ (r1_tarski @ sk_A @ 
% 2.65/2.87           (k10_relat_1 @ sk_B @ (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))))
% 2.65/2.87        | ~ (v1_relat_1 @ sk_B))),
% 2.65/2.87      inference('sup-', [status(thm)], ['65', '66'])).
% 2.65/2.87  thf('68', plain, ((v1_relat_1 @ sk_B)),
% 2.65/2.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.65/2.87  thf('69', plain,
% 2.65/2.87      (~ (r1_tarski @ sk_A @ 
% 2.65/2.87          (k10_relat_1 @ sk_B @ (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))))),
% 2.65/2.87      inference('demod', [status(thm)], ['67', '68'])).
% 2.65/2.87  thf('70', plain, (~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))),
% 2.65/2.87      inference('clc', [status(thm)], ['64', '69'])).
% 2.65/2.87  thf('71', plain, (~ (v1_relat_1 @ sk_B)),
% 2.65/2.87      inference('sup-', [status(thm)], ['0', '70'])).
% 2.65/2.87  thf('72', plain, ((v1_relat_1 @ sk_B)),
% 2.65/2.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.65/2.87  thf('73', plain, ($false), inference('demod', [status(thm)], ['71', '72'])).
% 2.65/2.87  
% 2.65/2.87  % SZS output end Refutation
% 2.65/2.87  
% 2.65/2.88  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
