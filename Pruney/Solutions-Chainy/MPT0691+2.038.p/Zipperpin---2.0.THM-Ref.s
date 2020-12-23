%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ATvTb1l9Yd

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:22 EST 2020

% Result     : Theorem 9.13s
% Output     : Refutation 9.13s
% Verified   : 
% Statistics : Number of formulae       :  158 ( 375 expanded)
%              Number of leaves         :   24 ( 122 expanded)
%              Depth                    :   25
%              Number of atoms          : 1259 (3183 expanded)
%              Number of equality atoms :   73 ( 175 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X19 @ X20 ) )
        = ( k9_relat_1 @ X19 @ X20 ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

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

thf('1',plain,(
    ~ ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ~ ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('6',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('7',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('8',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) )
    = sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('9',plain,(
    ! [X21: $i] :
      ( ( ( k10_relat_1 @ X21 @ ( k2_relat_1 @ X21 ) )
        = ( k1_relat_1 @ X21 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf(t139_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('10',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X25 @ X24 ) @ X26 )
        = ( k3_xboole_0 @ X24 @ ( k10_relat_1 @ X25 @ X26 ) ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ ( k2_relat_1 @ X0 ) )
        = ( k3_xboole_0 @ X1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k10_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ ( k2_relat_1 @ X0 ) )
        = ( k3_xboole_0 @ X1 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X25 @ X24 ) @ X26 )
        = ( k3_xboole_0 @ X24 @ ( k10_relat_1 @ X25 @ X26 ) ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('14',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('15',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ ( k10_relat_1 @ X1 @ X0 ) ) @ X0 )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['13','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ ( k1_relat_1 @ X0 ) ) ) @ ( k2_relat_1 @ X0 ) )
        = ( k10_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['12','18'])).

thf('20',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k10_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ ( k1_relat_1 @ X0 ) ) ) @ ( k2_relat_1 @ X0 ) )
        = ( k10_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( ( k10_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ sk_A ) @ ( k2_relat_1 @ sk_B ) )
      = ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['8','21'])).

thf('23',plain,(
    ! [X21: $i] :
      ( ( ( k10_relat_1 @ X21 @ ( k2_relat_1 @ X21 ) )
        = ( k1_relat_1 @ X21 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('24',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['14'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('26',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ X14 @ X15 )
      | ~ ( r1_tarski @ X16 @ X15 )
      | ( r1_tarski @ ( k2_xboole_0 @ X14 @ X16 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) @ ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['14'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('30',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X5 @ X7 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( k2_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['28','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('36',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X22 ) @ X23 )
      | ( ( k7_relat_1 @ X22 @ X23 )
        = X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k7_relat_1 @ X1 @ ( k2_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) )
      = sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['34','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X25 @ X24 ) @ X26 )
        = ( k3_xboole_0 @ X24 @ ( k10_relat_1 @ X25 @ X26 ) ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('42',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X10 @ X11 ) @ X10 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ sk_B @ X0 ) @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['40','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k10_relat_1 @ sk_B @ X0 ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k10_relat_1 @ sk_B @ X0 ) )
      | ( ( k1_relat_1 @ sk_B )
        = ( k10_relat_1 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ( ( k1_relat_1 @ sk_B )
      = ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['23','48'])).

thf('50',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['14'])).

thf('51',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X25 @ X24 ) @ X26 )
        = ( k3_xboole_0 @ X24 @ ( k10_relat_1 @ X25 @ X26 ) ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ ( k10_relat_1 @ X2 @ X0 ) @ X1 )
        = ( k10_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ X0 )
        = ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) @ ( k2_relat_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['52','55'])).

thf('57',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ X0 )
      = ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('60',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) )
    = sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

thf('61',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( k10_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ sk_A ) @ ( k2_relat_1 @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['22','58','59','60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ ( k10_relat_1 @ X2 @ X0 ) @ X1 )
        = ( k10_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('64',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['14'])).

thf('65',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X22 ) @ X23 )
      | ( ( k7_relat_1 @ X22 @ X23 )
        = X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X10 @ X11 ) @ X10 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('71',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_xboole_0 @ X9 @ X8 )
        = X8 )
      | ~ ( r1_tarski @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X5 @ X7 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ ( k3_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_xboole_0 @ ( k10_relat_1 @ X0 @ X1 ) @ X2 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['69','74'])).

thf('76',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k3_xboole_0 @ ( k10_relat_1 @ X0 @ X2 ) @ X1 ) )
      | ( ( k1_relat_1 @ X0 )
        = ( k3_xboole_0 @ ( k10_relat_1 @ X0 @ X2 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X2 ) @ ( k10_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ( ( k1_relat_1 @ X2 )
        = ( k3_xboole_0 @ ( k10_relat_1 @ X2 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['63','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_relat_1 @ X2 )
        = ( k3_xboole_0 @ ( k10_relat_1 @ X2 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X2 ) @ ( k10_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,
    ( ~ ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) @ sk_A )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
    | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
      = ( k3_xboole_0 @ ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['62','79'])).

thf('81',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('82',plain,(
    ! [X21: $i] :
      ( ( ( k10_relat_1 @ X21 @ ( k2_relat_1 @ X21 ) )
        = ( k1_relat_1 @ X21 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('83',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X25 @ X24 ) @ X26 )
        = ( k3_xboole_0 @ X24 @ ( k10_relat_1 @ X25 @ X26 ) ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('84',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k10_relat_1 @ sk_B @ X0 ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('86',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X10 @ X11 ) @ X10 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_xboole_0 @ X9 @ X8 )
        = X8 )
      | ~ ( r1_tarski @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X5 @ X7 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('91',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ ( k3_xboole_0 @ X2 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ ( k10_relat_1 @ sk_B @ X0 ) ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['84','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ X1 ) @ X0 ) @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['83','92'])).

thf('94',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ X1 ) @ X0 ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['82','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['81','96'])).

thf('98',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) @ ( k1_relat_1 @ sk_B ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X21: $i] :
      ( ( ( k10_relat_1 @ X21 @ ( k2_relat_1 @ X21 ) )
        = ( k1_relat_1 @ X21 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('105',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference(clc,[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ ( k3_xboole_0 @ X2 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('110',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['103','110'])).

thf('112',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ X0 )
      = ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('116',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) )
    = sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('118',plain,
    ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
    | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
      = sk_A ) ),
    inference(demod,[status(thm)],['80','113','114','115','116','117'])).

thf('119',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['5','118'])).

thf('120',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X21: $i] :
      ( ( ( k10_relat_1 @ X21 @ ( k2_relat_1 @ X21 ) )
        = ( k1_relat_1 @ X21 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('123',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X25 @ X24 ) @ X26 )
        = ( k3_xboole_0 @ X24 @ ( k10_relat_1 @ X25 @ X26 ) ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('125',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) @ ( k10_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ ( k10_relat_1 @ X1 @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['122','125'])).

thf('127',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ ( k10_relat_1 @ X1 @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ) ),
    inference(clc,[status(thm)],['126','127'])).

thf('129',plain,
    ( ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['121','128'])).

thf('130',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('132',plain,(
    $false ),
    inference(demod,[status(thm)],['4','131'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ATvTb1l9Yd
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:38:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 9.13/9.29  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 9.13/9.29  % Solved by: fo/fo7.sh
% 9.13/9.29  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 9.13/9.29  % done 12602 iterations in 8.803s
% 9.13/9.29  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 9.13/9.29  % SZS output start Refutation
% 9.13/9.29  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 9.13/9.29  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 9.13/9.29  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 9.13/9.29  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 9.13/9.29  thf(sk_B_type, type, sk_B: $i).
% 9.13/9.29  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 9.13/9.29  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 9.13/9.29  thf(sk_A_type, type, sk_A: $i).
% 9.13/9.29  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 9.13/9.29  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 9.13/9.29  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 9.13/9.29  thf(t148_relat_1, axiom,
% 9.13/9.29    (![A:$i,B:$i]:
% 9.13/9.29     ( ( v1_relat_1 @ B ) =>
% 9.13/9.29       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 9.13/9.29  thf('0', plain,
% 9.13/9.29      (![X19 : $i, X20 : $i]:
% 9.13/9.29         (((k2_relat_1 @ (k7_relat_1 @ X19 @ X20)) = (k9_relat_1 @ X19 @ X20))
% 9.13/9.29          | ~ (v1_relat_1 @ X19))),
% 9.13/9.29      inference('cnf', [status(esa)], [t148_relat_1])).
% 9.13/9.29  thf(t146_funct_1, conjecture,
% 9.13/9.29    (![A:$i,B:$i]:
% 9.13/9.29     ( ( v1_relat_1 @ B ) =>
% 9.13/9.29       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 9.13/9.29         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 9.13/9.29  thf(zf_stmt_0, negated_conjecture,
% 9.13/9.29    (~( ![A:$i,B:$i]:
% 9.13/9.29        ( ( v1_relat_1 @ B ) =>
% 9.13/9.29          ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 9.13/9.29            ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )),
% 9.13/9.29    inference('cnf.neg', [status(esa)], [t146_funct_1])).
% 9.13/9.29  thf('1', plain,
% 9.13/9.29      (~ (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 9.13/9.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.13/9.29  thf('2', plain,
% 9.13/9.29      ((~ (r1_tarski @ sk_A @ 
% 9.13/9.29           (k10_relat_1 @ sk_B @ (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))))
% 9.13/9.29        | ~ (v1_relat_1 @ sk_B))),
% 9.13/9.29      inference('sup-', [status(thm)], ['0', '1'])).
% 9.13/9.29  thf('3', plain, ((v1_relat_1 @ sk_B)),
% 9.13/9.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.13/9.29  thf('4', plain,
% 9.13/9.29      (~ (r1_tarski @ sk_A @ 
% 9.13/9.29          (k10_relat_1 @ sk_B @ (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))))),
% 9.13/9.29      inference('demod', [status(thm)], ['2', '3'])).
% 9.13/9.29  thf(dt_k7_relat_1, axiom,
% 9.13/9.29    (![A:$i,B:$i]:
% 9.13/9.29     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 9.13/9.29  thf('5', plain,
% 9.13/9.29      (![X17 : $i, X18 : $i]:
% 9.13/9.29         (~ (v1_relat_1 @ X17) | (v1_relat_1 @ (k7_relat_1 @ X17 @ X18)))),
% 9.13/9.29      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 9.13/9.29  thf('6', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 9.13/9.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.13/9.29  thf(t28_xboole_1, axiom,
% 9.13/9.29    (![A:$i,B:$i]:
% 9.13/9.29     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 9.13/9.29  thf('7', plain,
% 9.13/9.29      (![X12 : $i, X13 : $i]:
% 9.13/9.29         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 9.13/9.29      inference('cnf', [status(esa)], [t28_xboole_1])).
% 9.13/9.29  thf('8', plain, (((k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)) = (sk_A))),
% 9.13/9.29      inference('sup-', [status(thm)], ['6', '7'])).
% 9.13/9.29  thf(t169_relat_1, axiom,
% 9.13/9.29    (![A:$i]:
% 9.13/9.29     ( ( v1_relat_1 @ A ) =>
% 9.13/9.29       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 9.13/9.29  thf('9', plain,
% 9.13/9.29      (![X21 : $i]:
% 9.13/9.29         (((k10_relat_1 @ X21 @ (k2_relat_1 @ X21)) = (k1_relat_1 @ X21))
% 9.13/9.29          | ~ (v1_relat_1 @ X21))),
% 9.13/9.29      inference('cnf', [status(esa)], [t169_relat_1])).
% 9.13/9.29  thf(t139_funct_1, axiom,
% 9.13/9.29    (![A:$i,B:$i,C:$i]:
% 9.13/9.29     ( ( v1_relat_1 @ C ) =>
% 9.13/9.29       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 9.13/9.29         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 9.13/9.29  thf('10', plain,
% 9.13/9.29      (![X24 : $i, X25 : $i, X26 : $i]:
% 9.13/9.29         (((k10_relat_1 @ (k7_relat_1 @ X25 @ X24) @ X26)
% 9.13/9.29            = (k3_xboole_0 @ X24 @ (k10_relat_1 @ X25 @ X26)))
% 9.13/9.29          | ~ (v1_relat_1 @ X25))),
% 9.13/9.29      inference('cnf', [status(esa)], [t139_funct_1])).
% 9.13/9.29  thf('11', plain,
% 9.13/9.29      (![X0 : $i, X1 : $i]:
% 9.13/9.29         (((k10_relat_1 @ (k7_relat_1 @ X0 @ X1) @ (k2_relat_1 @ X0))
% 9.13/9.29            = (k3_xboole_0 @ X1 @ (k1_relat_1 @ X0)))
% 9.13/9.29          | ~ (v1_relat_1 @ X0)
% 9.13/9.29          | ~ (v1_relat_1 @ X0))),
% 9.13/9.29      inference('sup+', [status(thm)], ['9', '10'])).
% 9.13/9.29  thf('12', plain,
% 9.13/9.29      (![X0 : $i, X1 : $i]:
% 9.13/9.29         (~ (v1_relat_1 @ X0)
% 9.13/9.29          | ((k10_relat_1 @ (k7_relat_1 @ X0 @ X1) @ (k2_relat_1 @ X0))
% 9.13/9.29              = (k3_xboole_0 @ X1 @ (k1_relat_1 @ X0))))),
% 9.13/9.29      inference('simplify', [status(thm)], ['11'])).
% 9.13/9.29  thf('13', plain,
% 9.13/9.29      (![X24 : $i, X25 : $i, X26 : $i]:
% 9.13/9.29         (((k10_relat_1 @ (k7_relat_1 @ X25 @ X24) @ X26)
% 9.13/9.29            = (k3_xboole_0 @ X24 @ (k10_relat_1 @ X25 @ X26)))
% 9.13/9.29          | ~ (v1_relat_1 @ X25))),
% 9.13/9.29      inference('cnf', [status(esa)], [t139_funct_1])).
% 9.13/9.29  thf(d10_xboole_0, axiom,
% 9.13/9.29    (![A:$i,B:$i]:
% 9.13/9.29     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 9.13/9.29  thf('14', plain,
% 9.13/9.29      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 9.13/9.29      inference('cnf', [status(esa)], [d10_xboole_0])).
% 9.13/9.29  thf('15', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 9.13/9.29      inference('simplify', [status(thm)], ['14'])).
% 9.13/9.29  thf('16', plain,
% 9.13/9.29      (![X12 : $i, X13 : $i]:
% 9.13/9.29         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 9.13/9.29      inference('cnf', [status(esa)], [t28_xboole_1])).
% 9.13/9.29  thf('17', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 9.13/9.29      inference('sup-', [status(thm)], ['15', '16'])).
% 9.13/9.29  thf('18', plain,
% 9.13/9.29      (![X0 : $i, X1 : $i]:
% 9.13/9.29         (((k10_relat_1 @ (k7_relat_1 @ X1 @ (k10_relat_1 @ X1 @ X0)) @ X0)
% 9.13/9.29            = (k10_relat_1 @ X1 @ X0))
% 9.13/9.29          | ~ (v1_relat_1 @ X1))),
% 9.13/9.29      inference('sup+', [status(thm)], ['13', '17'])).
% 9.13/9.29  thf('19', plain,
% 9.13/9.29      (![X0 : $i, X1 : $i]:
% 9.13/9.29         (((k10_relat_1 @ 
% 9.13/9.29            (k7_relat_1 @ (k7_relat_1 @ X0 @ X1) @ 
% 9.13/9.29             (k3_xboole_0 @ X1 @ (k1_relat_1 @ X0))) @ 
% 9.13/9.29            (k2_relat_1 @ X0))
% 9.13/9.29            = (k10_relat_1 @ (k7_relat_1 @ X0 @ X1) @ (k2_relat_1 @ X0)))
% 9.13/9.29          | ~ (v1_relat_1 @ X0)
% 9.13/9.29          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ X1)))),
% 9.13/9.29      inference('sup+', [status(thm)], ['12', '18'])).
% 9.13/9.29  thf('20', plain,
% 9.13/9.29      (![X17 : $i, X18 : $i]:
% 9.13/9.29         (~ (v1_relat_1 @ X17) | (v1_relat_1 @ (k7_relat_1 @ X17 @ X18)))),
% 9.13/9.29      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 9.13/9.29  thf('21', plain,
% 9.13/9.29      (![X0 : $i, X1 : $i]:
% 9.13/9.29         (~ (v1_relat_1 @ X0)
% 9.13/9.29          | ((k10_relat_1 @ 
% 9.13/9.29              (k7_relat_1 @ (k7_relat_1 @ X0 @ X1) @ 
% 9.13/9.29               (k3_xboole_0 @ X1 @ (k1_relat_1 @ X0))) @ 
% 9.13/9.29              (k2_relat_1 @ X0))
% 9.13/9.29              = (k10_relat_1 @ (k7_relat_1 @ X0 @ X1) @ (k2_relat_1 @ X0))))),
% 9.13/9.29      inference('clc', [status(thm)], ['19', '20'])).
% 9.13/9.29  thf('22', plain,
% 9.13/9.29      ((((k10_relat_1 @ (k7_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ sk_A) @ 
% 9.13/9.29          (k2_relat_1 @ sk_B))
% 9.13/9.29          = (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ (k2_relat_1 @ sk_B)))
% 9.13/9.29        | ~ (v1_relat_1 @ sk_B))),
% 9.13/9.29      inference('sup+', [status(thm)], ['8', '21'])).
% 9.13/9.29  thf('23', plain,
% 9.13/9.29      (![X21 : $i]:
% 9.13/9.29         (((k10_relat_1 @ X21 @ (k2_relat_1 @ X21)) = (k1_relat_1 @ X21))
% 9.13/9.29          | ~ (v1_relat_1 @ X21))),
% 9.13/9.29      inference('cnf', [status(esa)], [t169_relat_1])).
% 9.13/9.29  thf('24', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 9.13/9.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.13/9.29  thf('25', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 9.13/9.29      inference('simplify', [status(thm)], ['14'])).
% 9.13/9.29  thf(t8_xboole_1, axiom,
% 9.13/9.29    (![A:$i,B:$i,C:$i]:
% 9.13/9.29     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 9.13/9.29       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 9.13/9.29  thf('26', plain,
% 9.13/9.29      (![X14 : $i, X15 : $i, X16 : $i]:
% 9.13/9.29         (~ (r1_tarski @ X14 @ X15)
% 9.13/9.29          | ~ (r1_tarski @ X16 @ X15)
% 9.13/9.29          | (r1_tarski @ (k2_xboole_0 @ X14 @ X16) @ X15))),
% 9.13/9.29      inference('cnf', [status(esa)], [t8_xboole_1])).
% 9.13/9.29  thf('27', plain,
% 9.13/9.29      (![X0 : $i, X1 : $i]:
% 9.13/9.29         ((r1_tarski @ (k2_xboole_0 @ X0 @ X1) @ X0) | ~ (r1_tarski @ X1 @ X0))),
% 9.13/9.29      inference('sup-', [status(thm)], ['25', '26'])).
% 9.13/9.29  thf('28', plain,
% 9.13/9.29      ((r1_tarski @ (k2_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A) @ 
% 9.13/9.29        (k1_relat_1 @ sk_B))),
% 9.13/9.29      inference('sup-', [status(thm)], ['24', '27'])).
% 9.13/9.29  thf('29', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 9.13/9.29      inference('simplify', [status(thm)], ['14'])).
% 9.13/9.29  thf(t11_xboole_1, axiom,
% 9.13/9.29    (![A:$i,B:$i,C:$i]:
% 9.13/9.29     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 9.13/9.29  thf('30', plain,
% 9.13/9.29      (![X5 : $i, X6 : $i, X7 : $i]:
% 9.13/9.29         ((r1_tarski @ X5 @ X6) | ~ (r1_tarski @ (k2_xboole_0 @ X5 @ X7) @ X6))),
% 9.13/9.29      inference('cnf', [status(esa)], [t11_xboole_1])).
% 9.13/9.29  thf('31', plain,
% 9.13/9.29      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 9.13/9.29      inference('sup-', [status(thm)], ['29', '30'])).
% 9.13/9.29  thf('32', plain,
% 9.13/9.29      (![X2 : $i, X4 : $i]:
% 9.13/9.29         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 9.13/9.29      inference('cnf', [status(esa)], [d10_xboole_0])).
% 9.13/9.29  thf('33', plain,
% 9.13/9.29      (![X0 : $i, X1 : $i]:
% 9.13/9.29         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 9.13/9.29          | ((k2_xboole_0 @ X1 @ X0) = (X1)))),
% 9.13/9.29      inference('sup-', [status(thm)], ['31', '32'])).
% 9.13/9.29  thf('34', plain,
% 9.13/9.29      (((k2_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A) = (k1_relat_1 @ sk_B))),
% 9.13/9.29      inference('sup-', [status(thm)], ['28', '33'])).
% 9.13/9.29  thf('35', plain,
% 9.13/9.29      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 9.13/9.29      inference('sup-', [status(thm)], ['29', '30'])).
% 9.13/9.29  thf(t97_relat_1, axiom,
% 9.13/9.29    (![A:$i,B:$i]:
% 9.13/9.29     ( ( v1_relat_1 @ B ) =>
% 9.13/9.29       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 9.13/9.29         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 9.13/9.29  thf('36', plain,
% 9.13/9.29      (![X22 : $i, X23 : $i]:
% 9.13/9.29         (~ (r1_tarski @ (k1_relat_1 @ X22) @ X23)
% 9.13/9.29          | ((k7_relat_1 @ X22 @ X23) = (X22))
% 9.13/9.29          | ~ (v1_relat_1 @ X22))),
% 9.13/9.29      inference('cnf', [status(esa)], [t97_relat_1])).
% 9.13/9.29  thf('37', plain,
% 9.13/9.29      (![X0 : $i, X1 : $i]:
% 9.13/9.29         (~ (v1_relat_1 @ X1)
% 9.13/9.29          | ((k7_relat_1 @ X1 @ (k2_xboole_0 @ (k1_relat_1 @ X1) @ X0)) = (X1)))),
% 9.13/9.29      inference('sup-', [status(thm)], ['35', '36'])).
% 9.13/9.29  thf('38', plain,
% 9.13/9.29      ((((k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_B)) = (sk_B))
% 9.13/9.29        | ~ (v1_relat_1 @ sk_B))),
% 9.13/9.29      inference('sup+', [status(thm)], ['34', '37'])).
% 9.13/9.29  thf('39', plain, ((v1_relat_1 @ sk_B)),
% 9.13/9.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.13/9.29  thf('40', plain, (((k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_B)) = (sk_B))),
% 9.13/9.29      inference('demod', [status(thm)], ['38', '39'])).
% 9.13/9.29  thf('41', plain,
% 9.13/9.29      (![X24 : $i, X25 : $i, X26 : $i]:
% 9.13/9.29         (((k10_relat_1 @ (k7_relat_1 @ X25 @ X24) @ X26)
% 9.13/9.29            = (k3_xboole_0 @ X24 @ (k10_relat_1 @ X25 @ X26)))
% 9.13/9.29          | ~ (v1_relat_1 @ X25))),
% 9.13/9.29      inference('cnf', [status(esa)], [t139_funct_1])).
% 9.13/9.29  thf(t17_xboole_1, axiom,
% 9.13/9.29    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 9.13/9.29  thf('42', plain,
% 9.13/9.29      (![X10 : $i, X11 : $i]: (r1_tarski @ (k3_xboole_0 @ X10 @ X11) @ X10)),
% 9.13/9.29      inference('cnf', [status(esa)], [t17_xboole_1])).
% 9.13/9.29  thf('43', plain,
% 9.13/9.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.13/9.29         ((r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0) @ X1)
% 9.13/9.29          | ~ (v1_relat_1 @ X2))),
% 9.13/9.29      inference('sup+', [status(thm)], ['41', '42'])).
% 9.13/9.29  thf('44', plain,
% 9.13/9.29      (![X0 : $i]:
% 9.13/9.29         ((r1_tarski @ (k10_relat_1 @ sk_B @ X0) @ (k1_relat_1 @ sk_B))
% 9.13/9.29          | ~ (v1_relat_1 @ sk_B))),
% 9.13/9.29      inference('sup+', [status(thm)], ['40', '43'])).
% 9.13/9.29  thf('45', plain, ((v1_relat_1 @ sk_B)),
% 9.13/9.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.13/9.29  thf('46', plain,
% 9.13/9.29      (![X0 : $i]:
% 9.13/9.29         (r1_tarski @ (k10_relat_1 @ sk_B @ X0) @ (k1_relat_1 @ sk_B))),
% 9.13/9.29      inference('demod', [status(thm)], ['44', '45'])).
% 9.13/9.29  thf('47', plain,
% 9.13/9.29      (![X2 : $i, X4 : $i]:
% 9.13/9.29         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 9.13/9.29      inference('cnf', [status(esa)], [d10_xboole_0])).
% 9.13/9.29  thf('48', plain,
% 9.13/9.29      (![X0 : $i]:
% 9.13/9.29         (~ (r1_tarski @ (k1_relat_1 @ sk_B) @ (k10_relat_1 @ sk_B @ X0))
% 9.13/9.29          | ((k1_relat_1 @ sk_B) = (k10_relat_1 @ sk_B @ X0)))),
% 9.13/9.29      inference('sup-', [status(thm)], ['46', '47'])).
% 9.13/9.29  thf('49', plain,
% 9.13/9.29      ((~ (r1_tarski @ (k1_relat_1 @ sk_B) @ (k1_relat_1 @ sk_B))
% 9.13/9.29        | ~ (v1_relat_1 @ sk_B)
% 9.13/9.29        | ((k1_relat_1 @ sk_B) = (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B))))),
% 9.13/9.29      inference('sup-', [status(thm)], ['23', '48'])).
% 9.13/9.29  thf('50', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 9.13/9.29      inference('simplify', [status(thm)], ['14'])).
% 9.13/9.29  thf('51', plain, ((v1_relat_1 @ sk_B)),
% 9.13/9.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.13/9.29  thf('52', plain,
% 9.13/9.29      (((k1_relat_1 @ sk_B) = (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B)))),
% 9.13/9.29      inference('demod', [status(thm)], ['49', '50', '51'])).
% 9.13/9.29  thf('53', plain,
% 9.13/9.29      (![X24 : $i, X25 : $i, X26 : $i]:
% 9.13/9.29         (((k10_relat_1 @ (k7_relat_1 @ X25 @ X24) @ X26)
% 9.13/9.29            = (k3_xboole_0 @ X24 @ (k10_relat_1 @ X25 @ X26)))
% 9.13/9.29          | ~ (v1_relat_1 @ X25))),
% 9.13/9.29      inference('cnf', [status(esa)], [t139_funct_1])).
% 9.13/9.29  thf(commutativity_k3_xboole_0, axiom,
% 9.13/9.29    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 9.13/9.29  thf('54', plain,
% 9.13/9.29      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 9.13/9.29      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 9.13/9.29  thf('55', plain,
% 9.13/9.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.13/9.29         (((k3_xboole_0 @ (k10_relat_1 @ X2 @ X0) @ X1)
% 9.13/9.29            = (k10_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0))
% 9.13/9.29          | ~ (v1_relat_1 @ X2))),
% 9.13/9.29      inference('sup+', [status(thm)], ['53', '54'])).
% 9.13/9.29  thf('56', plain,
% 9.13/9.29      (![X0 : $i]:
% 9.13/9.29         (((k3_xboole_0 @ (k1_relat_1 @ sk_B) @ X0)
% 9.13/9.29            = (k10_relat_1 @ (k7_relat_1 @ sk_B @ X0) @ (k2_relat_1 @ sk_B)))
% 9.13/9.29          | ~ (v1_relat_1 @ sk_B))),
% 9.13/9.29      inference('sup+', [status(thm)], ['52', '55'])).
% 9.13/9.29  thf('57', plain, ((v1_relat_1 @ sk_B)),
% 9.13/9.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.13/9.29  thf('58', plain,
% 9.13/9.29      (![X0 : $i]:
% 9.13/9.29         ((k3_xboole_0 @ (k1_relat_1 @ sk_B) @ X0)
% 9.13/9.29           = (k10_relat_1 @ (k7_relat_1 @ sk_B @ X0) @ (k2_relat_1 @ sk_B)))),
% 9.13/9.29      inference('demod', [status(thm)], ['56', '57'])).
% 9.13/9.29  thf('59', plain,
% 9.13/9.29      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 9.13/9.29      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 9.13/9.29  thf('60', plain, (((k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)) = (sk_A))),
% 9.13/9.29      inference('sup-', [status(thm)], ['6', '7'])).
% 9.13/9.29  thf('61', plain, ((v1_relat_1 @ sk_B)),
% 9.13/9.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.13/9.29  thf('62', plain,
% 9.13/9.29      (((k10_relat_1 @ (k7_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ sk_A) @ 
% 9.13/9.29         (k2_relat_1 @ sk_B)) = (sk_A))),
% 9.13/9.29      inference('demod', [status(thm)], ['22', '58', '59', '60', '61'])).
% 9.13/9.29  thf('63', plain,
% 9.13/9.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.13/9.29         (((k3_xboole_0 @ (k10_relat_1 @ X2 @ X0) @ X1)
% 9.13/9.29            = (k10_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0))
% 9.13/9.29          | ~ (v1_relat_1 @ X2))),
% 9.13/9.29      inference('sup+', [status(thm)], ['53', '54'])).
% 9.13/9.29  thf('64', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 9.13/9.29      inference('simplify', [status(thm)], ['14'])).
% 9.13/9.29  thf('65', plain,
% 9.13/9.29      (![X22 : $i, X23 : $i]:
% 9.13/9.29         (~ (r1_tarski @ (k1_relat_1 @ X22) @ X23)
% 9.13/9.29          | ((k7_relat_1 @ X22 @ X23) = (X22))
% 9.13/9.29          | ~ (v1_relat_1 @ X22))),
% 9.13/9.29      inference('cnf', [status(esa)], [t97_relat_1])).
% 9.13/9.29  thf('66', plain,
% 9.13/9.29      (![X0 : $i]:
% 9.13/9.29         (~ (v1_relat_1 @ X0) | ((k7_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (X0)))),
% 9.13/9.29      inference('sup-', [status(thm)], ['64', '65'])).
% 9.13/9.29  thf('67', plain,
% 9.13/9.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.13/9.29         ((r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0) @ X1)
% 9.13/9.29          | ~ (v1_relat_1 @ X2))),
% 9.13/9.29      inference('sup+', [status(thm)], ['41', '42'])).
% 9.13/9.29  thf('68', plain,
% 9.13/9.29      (![X0 : $i, X1 : $i]:
% 9.13/9.29         ((r1_tarski @ (k10_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0))
% 9.13/9.29          | ~ (v1_relat_1 @ X0)
% 9.13/9.29          | ~ (v1_relat_1 @ X0))),
% 9.13/9.29      inference('sup+', [status(thm)], ['66', '67'])).
% 9.13/9.29  thf('69', plain,
% 9.13/9.29      (![X0 : $i, X1 : $i]:
% 9.13/9.29         (~ (v1_relat_1 @ X0)
% 9.13/9.29          | (r1_tarski @ (k10_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0)))),
% 9.13/9.29      inference('simplify', [status(thm)], ['68'])).
% 9.13/9.29  thf('70', plain,
% 9.13/9.29      (![X10 : $i, X11 : $i]: (r1_tarski @ (k3_xboole_0 @ X10 @ X11) @ X10)),
% 9.13/9.29      inference('cnf', [status(esa)], [t17_xboole_1])).
% 9.13/9.29  thf(t12_xboole_1, axiom,
% 9.13/9.29    (![A:$i,B:$i]:
% 9.13/9.29     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 9.13/9.29  thf('71', plain,
% 9.13/9.29      (![X8 : $i, X9 : $i]:
% 9.13/9.29         (((k2_xboole_0 @ X9 @ X8) = (X8)) | ~ (r1_tarski @ X9 @ X8))),
% 9.13/9.29      inference('cnf', [status(esa)], [t12_xboole_1])).
% 9.13/9.29  thf('72', plain,
% 9.13/9.29      (![X0 : $i, X1 : $i]:
% 9.13/9.29         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 9.13/9.29      inference('sup-', [status(thm)], ['70', '71'])).
% 9.13/9.29  thf('73', plain,
% 9.13/9.29      (![X5 : $i, X6 : $i, X7 : $i]:
% 9.13/9.29         ((r1_tarski @ X5 @ X6) | ~ (r1_tarski @ (k2_xboole_0 @ X5 @ X7) @ X6))),
% 9.13/9.29      inference('cnf', [status(esa)], [t11_xboole_1])).
% 9.13/9.29  thf('74', plain,
% 9.13/9.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.13/9.29         (~ (r1_tarski @ X0 @ X1) | (r1_tarski @ (k3_xboole_0 @ X0 @ X2) @ X1))),
% 9.13/9.29      inference('sup-', [status(thm)], ['72', '73'])).
% 9.13/9.29  thf('75', plain,
% 9.13/9.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.13/9.29         (~ (v1_relat_1 @ X0)
% 9.13/9.29          | (r1_tarski @ (k3_xboole_0 @ (k10_relat_1 @ X0 @ X1) @ X2) @ 
% 9.13/9.29             (k1_relat_1 @ X0)))),
% 9.13/9.29      inference('sup-', [status(thm)], ['69', '74'])).
% 9.13/9.29  thf('76', plain,
% 9.13/9.29      (![X2 : $i, X4 : $i]:
% 9.13/9.29         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 9.13/9.29      inference('cnf', [status(esa)], [d10_xboole_0])).
% 9.13/9.29  thf('77', plain,
% 9.13/9.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.13/9.29         (~ (v1_relat_1 @ X0)
% 9.13/9.29          | ~ (r1_tarski @ (k1_relat_1 @ X0) @ 
% 9.13/9.29               (k3_xboole_0 @ (k10_relat_1 @ X0 @ X2) @ X1))
% 9.13/9.29          | ((k1_relat_1 @ X0) = (k3_xboole_0 @ (k10_relat_1 @ X0 @ X2) @ X1)))),
% 9.13/9.29      inference('sup-', [status(thm)], ['75', '76'])).
% 9.13/9.29  thf('78', plain,
% 9.13/9.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.13/9.29         (~ (r1_tarski @ (k1_relat_1 @ X2) @ 
% 9.13/9.29             (k10_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0))
% 9.13/9.29          | ~ (v1_relat_1 @ X2)
% 9.13/9.29          | ((k1_relat_1 @ X2) = (k3_xboole_0 @ (k10_relat_1 @ X2 @ X0) @ X1))
% 9.13/9.29          | ~ (v1_relat_1 @ X2))),
% 9.13/9.29      inference('sup-', [status(thm)], ['63', '77'])).
% 9.13/9.29  thf('79', plain,
% 9.13/9.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.13/9.29         (((k1_relat_1 @ X2) = (k3_xboole_0 @ (k10_relat_1 @ X2 @ X0) @ X1))
% 9.13/9.29          | ~ (v1_relat_1 @ X2)
% 9.13/9.29          | ~ (r1_tarski @ (k1_relat_1 @ X2) @ 
% 9.13/9.29               (k10_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0)))),
% 9.13/9.29      inference('simplify', [status(thm)], ['78'])).
% 9.13/9.29  thf('80', plain,
% 9.13/9.29      ((~ (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) @ sk_A)
% 9.13/9.29        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))
% 9.13/9.29        | ((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))
% 9.13/9.29            = (k3_xboole_0 @ 
% 9.13/9.29               (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ (k2_relat_1 @ sk_B)) @ 
% 9.13/9.29               sk_A)))),
% 9.13/9.29      inference('sup-', [status(thm)], ['62', '79'])).
% 9.13/9.29  thf('81', plain,
% 9.13/9.29      (![X17 : $i, X18 : $i]:
% 9.13/9.29         (~ (v1_relat_1 @ X17) | (v1_relat_1 @ (k7_relat_1 @ X17 @ X18)))),
% 9.13/9.29      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 9.13/9.29  thf('82', plain,
% 9.13/9.29      (![X21 : $i]:
% 9.13/9.29         (((k10_relat_1 @ X21 @ (k2_relat_1 @ X21)) = (k1_relat_1 @ X21))
% 9.13/9.29          | ~ (v1_relat_1 @ X21))),
% 9.13/9.29      inference('cnf', [status(esa)], [t169_relat_1])).
% 9.13/9.29  thf('83', plain,
% 9.13/9.29      (![X24 : $i, X25 : $i, X26 : $i]:
% 9.13/9.29         (((k10_relat_1 @ (k7_relat_1 @ X25 @ X24) @ X26)
% 9.13/9.29            = (k3_xboole_0 @ X24 @ (k10_relat_1 @ X25 @ X26)))
% 9.13/9.29          | ~ (v1_relat_1 @ X25))),
% 9.13/9.29      inference('cnf', [status(esa)], [t139_funct_1])).
% 9.13/9.29  thf('84', plain,
% 9.13/9.29      (![X0 : $i]:
% 9.13/9.29         (r1_tarski @ (k10_relat_1 @ sk_B @ X0) @ (k1_relat_1 @ sk_B))),
% 9.13/9.29      inference('demod', [status(thm)], ['44', '45'])).
% 9.13/9.29  thf('85', plain,
% 9.13/9.29      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 9.13/9.29      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 9.13/9.29  thf('86', plain,
% 9.13/9.29      (![X10 : $i, X11 : $i]: (r1_tarski @ (k3_xboole_0 @ X10 @ X11) @ X10)),
% 9.13/9.29      inference('cnf', [status(esa)], [t17_xboole_1])).
% 9.13/9.29  thf('87', plain,
% 9.13/9.29      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 9.13/9.29      inference('sup+', [status(thm)], ['85', '86'])).
% 9.13/9.29  thf('88', plain,
% 9.13/9.29      (![X8 : $i, X9 : $i]:
% 9.13/9.29         (((k2_xboole_0 @ X9 @ X8) = (X8)) | ~ (r1_tarski @ X9 @ X8))),
% 9.13/9.29      inference('cnf', [status(esa)], [t12_xboole_1])).
% 9.13/9.29  thf('89', plain,
% 9.13/9.29      (![X0 : $i, X1 : $i]:
% 9.13/9.29         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0) = (X0))),
% 9.13/9.29      inference('sup-', [status(thm)], ['87', '88'])).
% 9.13/9.29  thf('90', plain,
% 9.13/9.29      (![X5 : $i, X6 : $i, X7 : $i]:
% 9.13/9.29         ((r1_tarski @ X5 @ X6) | ~ (r1_tarski @ (k2_xboole_0 @ X5 @ X7) @ X6))),
% 9.13/9.29      inference('cnf', [status(esa)], [t11_xboole_1])).
% 9.13/9.29  thf('91', plain,
% 9.13/9.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.13/9.29         (~ (r1_tarski @ X0 @ X1) | (r1_tarski @ (k3_xboole_0 @ X2 @ X0) @ X1))),
% 9.13/9.29      inference('sup-', [status(thm)], ['89', '90'])).
% 9.13/9.29  thf('92', plain,
% 9.13/9.29      (![X0 : $i, X1 : $i]:
% 9.13/9.29         (r1_tarski @ (k3_xboole_0 @ X1 @ (k10_relat_1 @ sk_B @ X0)) @ 
% 9.13/9.29          (k1_relat_1 @ sk_B))),
% 9.13/9.29      inference('sup-', [status(thm)], ['84', '91'])).
% 9.13/9.29  thf('93', plain,
% 9.13/9.29      (![X0 : $i, X1 : $i]:
% 9.13/9.29         ((r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ sk_B @ X1) @ X0) @ 
% 9.13/9.29           (k1_relat_1 @ sk_B))
% 9.13/9.29          | ~ (v1_relat_1 @ sk_B))),
% 9.13/9.29      inference('sup+', [status(thm)], ['83', '92'])).
% 9.13/9.29  thf('94', plain, ((v1_relat_1 @ sk_B)),
% 9.13/9.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.13/9.29  thf('95', plain,
% 9.13/9.29      (![X0 : $i, X1 : $i]:
% 9.13/9.29         (r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ sk_B @ X1) @ X0) @ 
% 9.13/9.29          (k1_relat_1 @ sk_B))),
% 9.13/9.29      inference('demod', [status(thm)], ['93', '94'])).
% 9.13/9.29  thf('96', plain,
% 9.13/9.29      (![X0 : $i]:
% 9.13/9.29         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)) @ 
% 9.13/9.29           (k1_relat_1 @ sk_B))
% 9.13/9.29          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ X0)))),
% 9.13/9.29      inference('sup+', [status(thm)], ['82', '95'])).
% 9.13/9.29  thf('97', plain,
% 9.13/9.29      (![X0 : $i]:
% 9.13/9.29         (~ (v1_relat_1 @ sk_B)
% 9.13/9.29          | (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)) @ 
% 9.13/9.29             (k1_relat_1 @ sk_B)))),
% 9.13/9.29      inference('sup-', [status(thm)], ['81', '96'])).
% 9.13/9.29  thf('98', plain, ((v1_relat_1 @ sk_B)),
% 9.13/9.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.13/9.29  thf('99', plain,
% 9.13/9.29      (![X0 : $i]:
% 9.13/9.29         (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)) @ 
% 9.13/9.29          (k1_relat_1 @ sk_B))),
% 9.13/9.29      inference('demod', [status(thm)], ['97', '98'])).
% 9.13/9.29  thf('100', plain,
% 9.13/9.29      (![X12 : $i, X13 : $i]:
% 9.13/9.29         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 9.13/9.29      inference('cnf', [status(esa)], [t28_xboole_1])).
% 9.13/9.29  thf('101', plain,
% 9.13/9.29      (![X0 : $i]:
% 9.13/9.29         ((k3_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)) @ 
% 9.13/9.29           (k1_relat_1 @ sk_B)) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)))),
% 9.13/9.29      inference('sup-', [status(thm)], ['99', '100'])).
% 9.13/9.29  thf('102', plain,
% 9.13/9.29      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 9.13/9.29      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 9.13/9.29  thf('103', plain,
% 9.13/9.29      (![X0 : $i]:
% 9.13/9.29         ((k3_xboole_0 @ (k1_relat_1 @ sk_B) @ 
% 9.13/9.29           (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)))
% 9.13/9.29           = (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)))),
% 9.13/9.29      inference('demod', [status(thm)], ['101', '102'])).
% 9.13/9.29  thf('104', plain,
% 9.13/9.29      (![X21 : $i]:
% 9.13/9.29         (((k10_relat_1 @ X21 @ (k2_relat_1 @ X21)) = (k1_relat_1 @ X21))
% 9.13/9.29          | ~ (v1_relat_1 @ X21))),
% 9.13/9.29      inference('cnf', [status(esa)], [t169_relat_1])).
% 9.13/9.29  thf('105', plain,
% 9.13/9.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.13/9.29         ((r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0) @ X1)
% 9.13/9.29          | ~ (v1_relat_1 @ X2))),
% 9.13/9.29      inference('sup+', [status(thm)], ['41', '42'])).
% 9.13/9.29  thf('106', plain,
% 9.13/9.29      (![X0 : $i, X1 : $i]:
% 9.13/9.29         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X0)
% 9.13/9.29          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 9.13/9.29          | ~ (v1_relat_1 @ X1))),
% 9.13/9.29      inference('sup+', [status(thm)], ['104', '105'])).
% 9.13/9.29  thf('107', plain,
% 9.13/9.29      (![X17 : $i, X18 : $i]:
% 9.13/9.29         (~ (v1_relat_1 @ X17) | (v1_relat_1 @ (k7_relat_1 @ X17 @ X18)))),
% 9.13/9.29      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 9.13/9.29  thf('108', plain,
% 9.13/9.29      (![X0 : $i, X1 : $i]:
% 9.13/9.29         (~ (v1_relat_1 @ X1)
% 9.13/9.29          | (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X0))),
% 9.13/9.29      inference('clc', [status(thm)], ['106', '107'])).
% 9.13/9.29  thf('109', plain,
% 9.13/9.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.13/9.29         (~ (r1_tarski @ X0 @ X1) | (r1_tarski @ (k3_xboole_0 @ X2 @ X0) @ X1))),
% 9.13/9.29      inference('sup-', [status(thm)], ['89', '90'])).
% 9.13/9.29  thf('110', plain,
% 9.13/9.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.13/9.29         (~ (v1_relat_1 @ X1)
% 9.13/9.29          | (r1_tarski @ 
% 9.13/9.29             (k3_xboole_0 @ X2 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))) @ X0))),
% 9.13/9.29      inference('sup-', [status(thm)], ['108', '109'])).
% 9.13/9.29  thf('111', plain,
% 9.13/9.29      (![X0 : $i]:
% 9.13/9.29         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)) @ X0)
% 9.13/9.29          | ~ (v1_relat_1 @ sk_B))),
% 9.13/9.29      inference('sup+', [status(thm)], ['103', '110'])).
% 9.13/9.29  thf('112', plain, ((v1_relat_1 @ sk_B)),
% 9.13/9.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.13/9.29  thf('113', plain,
% 9.13/9.29      (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)) @ X0)),
% 9.13/9.29      inference('demod', [status(thm)], ['111', '112'])).
% 9.13/9.29  thf('114', plain,
% 9.13/9.29      (![X0 : $i]:
% 9.13/9.29         ((k3_xboole_0 @ (k1_relat_1 @ sk_B) @ X0)
% 9.13/9.29           = (k10_relat_1 @ (k7_relat_1 @ sk_B @ X0) @ (k2_relat_1 @ sk_B)))),
% 9.13/9.29      inference('demod', [status(thm)], ['56', '57'])).
% 9.13/9.29  thf('115', plain,
% 9.13/9.29      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 9.13/9.29      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 9.13/9.29  thf('116', plain, (((k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)) = (sk_A))),
% 9.13/9.29      inference('sup-', [status(thm)], ['6', '7'])).
% 9.13/9.29  thf('117', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 9.13/9.29      inference('sup-', [status(thm)], ['15', '16'])).
% 9.13/9.29  thf('118', plain,
% 9.13/9.29      ((~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))
% 9.13/9.29        | ((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) = (sk_A)))),
% 9.13/9.29      inference('demod', [status(thm)],
% 9.13/9.29                ['80', '113', '114', '115', '116', '117'])).
% 9.13/9.29  thf('119', plain,
% 9.13/9.29      ((~ (v1_relat_1 @ sk_B)
% 9.13/9.29        | ((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) = (sk_A)))),
% 9.13/9.29      inference('sup-', [status(thm)], ['5', '118'])).
% 9.13/9.29  thf('120', plain, ((v1_relat_1 @ sk_B)),
% 9.13/9.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.13/9.29  thf('121', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) = (sk_A))),
% 9.13/9.29      inference('demod', [status(thm)], ['119', '120'])).
% 9.13/9.29  thf('122', plain,
% 9.13/9.29      (![X21 : $i]:
% 9.13/9.29         (((k10_relat_1 @ X21 @ (k2_relat_1 @ X21)) = (k1_relat_1 @ X21))
% 9.13/9.29          | ~ (v1_relat_1 @ X21))),
% 9.13/9.29      inference('cnf', [status(esa)], [t169_relat_1])).
% 9.13/9.29  thf('123', plain,
% 9.13/9.29      (![X24 : $i, X25 : $i, X26 : $i]:
% 9.13/9.29         (((k10_relat_1 @ (k7_relat_1 @ X25 @ X24) @ X26)
% 9.13/9.29            = (k3_xboole_0 @ X24 @ (k10_relat_1 @ X25 @ X26)))
% 9.13/9.29          | ~ (v1_relat_1 @ X25))),
% 9.13/9.29      inference('cnf', [status(esa)], [t139_funct_1])).
% 9.13/9.29  thf('124', plain,
% 9.13/9.29      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 9.13/9.29      inference('sup+', [status(thm)], ['85', '86'])).
% 9.13/9.29  thf('125', plain,
% 9.13/9.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.13/9.29         ((r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0) @ 
% 9.13/9.29           (k10_relat_1 @ X2 @ X0))
% 9.13/9.29          | ~ (v1_relat_1 @ X2))),
% 9.13/9.29      inference('sup+', [status(thm)], ['123', '124'])).
% 9.13/9.29  thf('126', plain,
% 9.13/9.29      (![X0 : $i, X1 : $i]:
% 9.13/9.29         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ 
% 9.13/9.29           (k10_relat_1 @ X1 @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X0))))
% 9.13/9.29          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 9.13/9.29          | ~ (v1_relat_1 @ X1))),
% 9.13/9.29      inference('sup+', [status(thm)], ['122', '125'])).
% 9.13/9.29  thf('127', plain,
% 9.13/9.29      (![X17 : $i, X18 : $i]:
% 9.13/9.29         (~ (v1_relat_1 @ X17) | (v1_relat_1 @ (k7_relat_1 @ X17 @ X18)))),
% 9.13/9.29      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 9.13/9.29  thf('128', plain,
% 9.13/9.29      (![X0 : $i, X1 : $i]:
% 9.13/9.29         (~ (v1_relat_1 @ X1)
% 9.13/9.29          | (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ 
% 9.13/9.29             (k10_relat_1 @ X1 @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X0)))))),
% 9.13/9.29      inference('clc', [status(thm)], ['126', '127'])).
% 9.13/9.29  thf('129', plain,
% 9.13/9.29      (((r1_tarski @ sk_A @ 
% 9.13/9.29         (k10_relat_1 @ sk_B @ (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))))
% 9.13/9.29        | ~ (v1_relat_1 @ sk_B))),
% 9.13/9.29      inference('sup+', [status(thm)], ['121', '128'])).
% 9.13/9.29  thf('130', plain, ((v1_relat_1 @ sk_B)),
% 9.13/9.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.13/9.29  thf('131', plain,
% 9.13/9.29      ((r1_tarski @ sk_A @ 
% 9.13/9.29        (k10_relat_1 @ sk_B @ (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))))),
% 9.13/9.29      inference('demod', [status(thm)], ['129', '130'])).
% 9.13/9.29  thf('132', plain, ($false), inference('demod', [status(thm)], ['4', '131'])).
% 9.13/9.29  
% 9.13/9.29  % SZS output end Refutation
% 9.13/9.29  
% 9.15/9.30  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
