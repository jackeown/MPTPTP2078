%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qsHyvJNARI

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:24 EST 2020

% Result     : Theorem 0.83s
% Output     : Refutation 0.83s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 218 expanded)
%              Number of leaves         :   37 (  82 expanded)
%              Depth                    :   24
%              Number of atoms          :  825 (1663 expanded)
%              Number of equality atoms :   65 ( 121 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

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
    ! [X71: $i,X72: $i,X73: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X72 @ X71 ) @ X73 )
        = ( k3_xboole_0 @ X71 @ ( k10_relat_1 @ X72 @ X73 ) ) )
      | ~ ( v1_relat_1 @ X72 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X46: $i,X47: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X46 @ X47 ) )
      = ( k3_xboole_0 @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('3',plain,(
    ! [X71: $i,X72: $i,X73: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X72 @ X71 ) @ X73 )
        = ( k1_setfam_1 @ ( k2_tarski @ X71 @ ( k10_relat_1 @ X72 @ X73 ) ) ) )
      | ~ ( v1_relat_1 @ X72 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('4',plain,(
    ! [X51: $i,X52: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X51 @ X52 ) )
        = ( k9_relat_1 @ X51 @ X52 ) )
      | ~ ( v1_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('5',plain,(
    ! [X58: $i] :
      ( ( ( k10_relat_1 @ X58 @ ( k2_relat_1 @ X58 ) )
        = ( k1_relat_1 @ X58 ) )
      | ~ ( v1_relat_1 @ X58 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X49: $i,X50: $i] :
      ( ~ ( v1_relat_1 @ X49 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X49 @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X49: $i,X50: $i] :
      ( ~ ( v1_relat_1 @ X49 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X49 @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('10',plain,(
    ! [X68: $i,X69: $i] :
      ( ( ( k7_relat_1 @ X69 @ X68 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X68 ) @ X69 ) )
      | ~ ( v1_relat_1 @ X69 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('11',plain,(
    ! [X62: $i,X63: $i] :
      ( ~ ( v1_relat_1 @ X62 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X63 @ X62 ) )
        = ( k10_relat_1 @ X63 @ ( k1_relat_1 @ X62 ) ) )
      | ~ ( v1_relat_1 @ X63 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('12',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('13',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_xboole_0 @ X13 @ X12 )
        = X12 )
      | ~ ( r1_tarski @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('14',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('15',plain,(
    ! [X65: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X65 ) )
      = X65 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('16',plain,(
    ! [X58: $i] :
      ( ( ( k10_relat_1 @ X58 @ ( k2_relat_1 @ X58 ) )
        = ( k1_relat_1 @ X58 ) )
      | ~ ( v1_relat_1 @ X58 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
        = ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X64: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X64 ) )
      = X64 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('19',plain,(
    ! [X48: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf(t175_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) )
        = ( k2_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('21',plain,(
    ! [X59: $i,X60: $i,X61: $i] :
      ( ( ( k10_relat_1 @ X59 @ ( k2_xboole_0 @ X60 @ X61 ) )
        = ( k2_xboole_0 @ ( k10_relat_1 @ X59 @ X60 ) @ ( k10_relat_1 @ X59 @ X61 ) ) )
      | ~ ( v1_relat_1 @ X59 ) ) ),
    inference(cnf,[status(esa)],[t175_relat_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X1 ) )
        = ( k2_xboole_0 @ X0 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X64: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X64 ) )
      = X64 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('24',plain,(
    ! [X56: $i,X57: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X56 @ X57 ) @ ( k1_relat_1 @ X56 ) )
      | ~ ( v1_relat_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X48: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('28',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( X1 != X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('29',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['28'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('30',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r1_tarski @ X16 @ X17 )
      | ~ ( r1_tarski @ X18 @ X17 )
      | ( r1_tarski @ ( k2_xboole_0 @ X16 @ X18 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ X0 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['27','31'])).

thf('33',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['28'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('34',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X9 @ X11 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['32','37'])).

thf('39',plain,(
    ! [X48: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['22','38','39'])).

thf('41',plain,
    ( ( k10_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
    = sk_A ),
    inference('sup+',[status(thm)],['14','40'])).

thf('42',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) )
      = sk_A )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['11','41'])).

thf('43',plain,(
    ! [X48: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('44',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,
    ( ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
      = sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['10','45'])).

thf('47',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X56: $i,X57: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X56 @ X57 ) @ ( k1_relat_1 @ X56 ) )
      | ~ ( v1_relat_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) @ sk_A )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','50'])).

thf('52',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) @ sk_A ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_A @ ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) )
      | ( sk_A
        = ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ( sk_A
      = ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['8','55'])).

thf('57',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['46','47'])).

thf('58',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['28'])).

thf('59',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( sk_A
    = ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['56','57','58','59'])).

thf('61',plain,
    ( ( sk_A
      = ( k1_setfam_1 @ ( k2_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['3','60'])).

thf('62',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( sk_A
    = ( k1_setfam_1 @ ( k2_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('64',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('65',plain,(
    ! [X46: $i,X47: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X46 @ X47 ) )
      = ( k3_xboole_0 @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('66',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k1_setfam_1 @ ( k2_tarski @ X7 @ X8 ) ) ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    = ( k5_xboole_0 @ sk_A @ sk_A ) ),
    inference('sup+',[status(thm)],['63','66'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('69',plain,(
    ! [X46: $i,X47: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X46 @ X47 ) )
      = ( k3_xboole_0 @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k1_setfam_1 @ ( k2_tarski @ X7 @ X8 ) ) ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['28'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('74',plain,(
    ! [X4: $i,X6: $i] :
      ( ( ( k4_xboole_0 @ X4 @ X6 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['72','75'])).

thf('77',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['67','76'])).

thf('78',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( ( k4_xboole_0 @ X4 @ X5 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('79',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    $false ),
    inference(demod,[status(thm)],['0','80'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qsHyvJNARI
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:00:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.83/0.99  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.83/0.99  % Solved by: fo/fo7.sh
% 0.83/0.99  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.83/0.99  % done 1165 iterations in 0.562s
% 0.83/0.99  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.83/0.99  % SZS output start Refutation
% 0.83/0.99  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.83/0.99  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.83/0.99  thf(sk_B_type, type, sk_B: $i).
% 0.83/0.99  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.83/0.99  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.83/0.99  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.83/0.99  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.83/0.99  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.83/0.99  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.83/0.99  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.83/0.99  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.83/0.99  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.83/0.99  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.83/0.99  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.83/0.99  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.83/0.99  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.83/0.99  thf(sk_A_type, type, sk_A: $i).
% 0.83/0.99  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.83/0.99  thf(t146_funct_1, conjecture,
% 0.83/0.99    (![A:$i,B:$i]:
% 0.83/0.99     ( ( v1_relat_1 @ B ) =>
% 0.83/0.99       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.83/0.99         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 0.83/0.99  thf(zf_stmt_0, negated_conjecture,
% 0.83/0.99    (~( ![A:$i,B:$i]:
% 0.83/0.99        ( ( v1_relat_1 @ B ) =>
% 0.83/0.99          ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.83/0.99            ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )),
% 0.83/0.99    inference('cnf.neg', [status(esa)], [t146_funct_1])).
% 0.83/0.99  thf('0', plain,
% 0.83/0.99      (~ (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 0.83/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/0.99  thf(t139_funct_1, axiom,
% 0.83/0.99    (![A:$i,B:$i,C:$i]:
% 0.83/0.99     ( ( v1_relat_1 @ C ) =>
% 0.83/0.99       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.83/0.99         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.83/0.99  thf('1', plain,
% 0.83/0.99      (![X71 : $i, X72 : $i, X73 : $i]:
% 0.83/0.99         (((k10_relat_1 @ (k7_relat_1 @ X72 @ X71) @ X73)
% 0.83/0.99            = (k3_xboole_0 @ X71 @ (k10_relat_1 @ X72 @ X73)))
% 0.83/0.99          | ~ (v1_relat_1 @ X72))),
% 0.83/0.99      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.83/0.99  thf(t12_setfam_1, axiom,
% 0.83/0.99    (![A:$i,B:$i]:
% 0.83/0.99     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.83/0.99  thf('2', plain,
% 0.83/0.99      (![X46 : $i, X47 : $i]:
% 0.83/0.99         ((k1_setfam_1 @ (k2_tarski @ X46 @ X47)) = (k3_xboole_0 @ X46 @ X47))),
% 0.83/0.99      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.83/0.99  thf('3', plain,
% 0.83/0.99      (![X71 : $i, X72 : $i, X73 : $i]:
% 0.83/0.99         (((k10_relat_1 @ (k7_relat_1 @ X72 @ X71) @ X73)
% 0.83/0.99            = (k1_setfam_1 @ (k2_tarski @ X71 @ (k10_relat_1 @ X72 @ X73))))
% 0.83/0.99          | ~ (v1_relat_1 @ X72))),
% 0.83/0.99      inference('demod', [status(thm)], ['1', '2'])).
% 0.83/0.99  thf(t148_relat_1, axiom,
% 0.83/0.99    (![A:$i,B:$i]:
% 0.83/0.99     ( ( v1_relat_1 @ B ) =>
% 0.83/0.99       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.83/0.99  thf('4', plain,
% 0.83/0.99      (![X51 : $i, X52 : $i]:
% 0.83/0.99         (((k2_relat_1 @ (k7_relat_1 @ X51 @ X52)) = (k9_relat_1 @ X51 @ X52))
% 0.83/0.99          | ~ (v1_relat_1 @ X51))),
% 0.83/0.99      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.83/0.99  thf(t169_relat_1, axiom,
% 0.83/0.99    (![A:$i]:
% 0.83/0.99     ( ( v1_relat_1 @ A ) =>
% 0.83/0.99       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.83/0.99  thf('5', plain,
% 0.83/0.99      (![X58 : $i]:
% 0.83/0.99         (((k10_relat_1 @ X58 @ (k2_relat_1 @ X58)) = (k1_relat_1 @ X58))
% 0.83/0.99          | ~ (v1_relat_1 @ X58))),
% 0.83/0.99      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.83/0.99  thf('6', plain,
% 0.83/0.99      (![X0 : $i, X1 : $i]:
% 0.83/0.99         (((k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0))
% 0.83/0.99            = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.83/0.99          | ~ (v1_relat_1 @ X1)
% 0.83/0.99          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.83/0.99      inference('sup+', [status(thm)], ['4', '5'])).
% 0.83/0.99  thf(dt_k7_relat_1, axiom,
% 0.83/0.99    (![A:$i,B:$i]:
% 0.83/0.99     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.83/0.99  thf('7', plain,
% 0.83/0.99      (![X49 : $i, X50 : $i]:
% 0.83/0.99         (~ (v1_relat_1 @ X49) | (v1_relat_1 @ (k7_relat_1 @ X49 @ X50)))),
% 0.83/0.99      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.83/0.99  thf('8', plain,
% 0.83/0.99      (![X0 : $i, X1 : $i]:
% 0.83/0.99         (~ (v1_relat_1 @ X1)
% 0.83/0.99          | ((k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0))
% 0.83/0.99              = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 0.83/0.99      inference('clc', [status(thm)], ['6', '7'])).
% 0.83/0.99  thf('9', plain,
% 0.83/0.99      (![X49 : $i, X50 : $i]:
% 0.83/0.99         (~ (v1_relat_1 @ X49) | (v1_relat_1 @ (k7_relat_1 @ X49 @ X50)))),
% 0.83/0.99      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.83/0.99  thf(t94_relat_1, axiom,
% 0.83/0.99    (![A:$i,B:$i]:
% 0.83/0.99     ( ( v1_relat_1 @ B ) =>
% 0.83/0.99       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.83/0.99  thf('10', plain,
% 0.83/0.99      (![X68 : $i, X69 : $i]:
% 0.83/0.99         (((k7_relat_1 @ X69 @ X68) = (k5_relat_1 @ (k6_relat_1 @ X68) @ X69))
% 0.83/0.99          | ~ (v1_relat_1 @ X69))),
% 0.83/0.99      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.83/0.99  thf(t182_relat_1, axiom,
% 0.83/0.99    (![A:$i]:
% 0.83/0.99     ( ( v1_relat_1 @ A ) =>
% 0.83/0.99       ( ![B:$i]:
% 0.83/0.99         ( ( v1_relat_1 @ B ) =>
% 0.83/0.99           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.83/0.99             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.83/0.99  thf('11', plain,
% 0.83/0.99      (![X62 : $i, X63 : $i]:
% 0.83/0.99         (~ (v1_relat_1 @ X62)
% 0.83/0.99          | ((k1_relat_1 @ (k5_relat_1 @ X63 @ X62))
% 0.83/0.99              = (k10_relat_1 @ X63 @ (k1_relat_1 @ X62)))
% 0.83/0.99          | ~ (v1_relat_1 @ X63))),
% 0.83/0.99      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.83/0.99  thf('12', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.83/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/0.99  thf(t12_xboole_1, axiom,
% 0.83/0.99    (![A:$i,B:$i]:
% 0.83/0.99     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.83/0.99  thf('13', plain,
% 0.83/0.99      (![X12 : $i, X13 : $i]:
% 0.83/0.99         (((k2_xboole_0 @ X13 @ X12) = (X12)) | ~ (r1_tarski @ X13 @ X12))),
% 0.83/0.99      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.83/0.99  thf('14', plain,
% 0.83/0.99      (((k2_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)) = (k1_relat_1 @ sk_B))),
% 0.83/0.99      inference('sup-', [status(thm)], ['12', '13'])).
% 0.83/0.99  thf(t71_relat_1, axiom,
% 0.83/0.99    (![A:$i]:
% 0.83/0.99     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.83/0.99       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.83/0.99  thf('15', plain, (![X65 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X65)) = (X65))),
% 0.83/0.99      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.83/0.99  thf('16', plain,
% 0.83/0.99      (![X58 : $i]:
% 0.83/0.99         (((k10_relat_1 @ X58 @ (k2_relat_1 @ X58)) = (k1_relat_1 @ X58))
% 0.83/0.99          | ~ (v1_relat_1 @ X58))),
% 0.83/0.99      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.83/0.99  thf('17', plain,
% 0.83/0.99      (![X0 : $i]:
% 0.83/0.99         (((k10_relat_1 @ (k6_relat_1 @ X0) @ X0)
% 0.83/0.99            = (k1_relat_1 @ (k6_relat_1 @ X0)))
% 0.83/0.99          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.83/0.99      inference('sup+', [status(thm)], ['15', '16'])).
% 0.83/0.99  thf('18', plain, (![X64 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X64)) = (X64))),
% 0.83/0.99      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.83/0.99  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.83/0.99  thf('19', plain, (![X48 : $i]: (v1_relat_1 @ (k6_relat_1 @ X48))),
% 0.83/0.99      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.83/0.99  thf('20', plain,
% 0.83/0.99      (![X0 : $i]: ((k10_relat_1 @ (k6_relat_1 @ X0) @ X0) = (X0))),
% 0.83/0.99      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.83/0.99  thf(t175_relat_1, axiom,
% 0.83/0.99    (![A:$i,B:$i,C:$i]:
% 0.83/0.99     ( ( v1_relat_1 @ C ) =>
% 0.83/0.99       ( ( k10_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) ) =
% 0.83/0.99         ( k2_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.83/0.99  thf('21', plain,
% 0.83/0.99      (![X59 : $i, X60 : $i, X61 : $i]:
% 0.83/0.99         (((k10_relat_1 @ X59 @ (k2_xboole_0 @ X60 @ X61))
% 0.83/0.99            = (k2_xboole_0 @ (k10_relat_1 @ X59 @ X60) @ 
% 0.83/0.99               (k10_relat_1 @ X59 @ X61)))
% 0.83/0.99          | ~ (v1_relat_1 @ X59))),
% 0.83/0.99      inference('cnf', [status(esa)], [t175_relat_1])).
% 0.83/0.99  thf('22', plain,
% 0.83/0.99      (![X0 : $i, X1 : $i]:
% 0.83/0.99         (((k10_relat_1 @ (k6_relat_1 @ X0) @ (k2_xboole_0 @ X0 @ X1))
% 0.83/0.99            = (k2_xboole_0 @ X0 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1)))
% 0.83/0.99          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.83/0.99      inference('sup+', [status(thm)], ['20', '21'])).
% 0.83/0.99  thf('23', plain, (![X64 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X64)) = (X64))),
% 0.83/0.99      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.83/0.99  thf(t167_relat_1, axiom,
% 0.83/0.99    (![A:$i,B:$i]:
% 0.83/0.99     ( ( v1_relat_1 @ B ) =>
% 0.83/0.99       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 0.83/0.99  thf('24', plain,
% 0.83/0.99      (![X56 : $i, X57 : $i]:
% 0.83/0.99         ((r1_tarski @ (k10_relat_1 @ X56 @ X57) @ (k1_relat_1 @ X56))
% 0.83/0.99          | ~ (v1_relat_1 @ X56))),
% 0.83/0.99      inference('cnf', [status(esa)], [t167_relat_1])).
% 0.83/0.99  thf('25', plain,
% 0.83/0.99      (![X0 : $i, X1 : $i]:
% 0.83/0.99         ((r1_tarski @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X0)
% 0.83/0.99          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.83/0.99      inference('sup+', [status(thm)], ['23', '24'])).
% 0.83/0.99  thf('26', plain, (![X48 : $i]: (v1_relat_1 @ (k6_relat_1 @ X48))),
% 0.83/0.99      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.83/0.99  thf('27', plain,
% 0.83/0.99      (![X0 : $i, X1 : $i]:
% 0.83/0.99         (r1_tarski @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X0)),
% 0.83/0.99      inference('demod', [status(thm)], ['25', '26'])).
% 0.83/0.99  thf(d10_xboole_0, axiom,
% 0.83/0.99    (![A:$i,B:$i]:
% 0.83/0.99     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.83/0.99  thf('28', plain,
% 0.83/0.99      (![X1 : $i, X2 : $i]: ((r1_tarski @ X1 @ X2) | ((X1) != (X2)))),
% 0.83/0.99      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.83/0.99  thf('29', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 0.83/0.99      inference('simplify', [status(thm)], ['28'])).
% 0.83/0.99  thf(t8_xboole_1, axiom,
% 0.83/0.99    (![A:$i,B:$i,C:$i]:
% 0.83/0.99     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 0.83/0.99       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 0.83/0.99  thf('30', plain,
% 0.83/0.99      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.83/0.99         (~ (r1_tarski @ X16 @ X17)
% 0.83/0.99          | ~ (r1_tarski @ X18 @ X17)
% 0.83/0.99          | (r1_tarski @ (k2_xboole_0 @ X16 @ X18) @ X17))),
% 0.83/0.99      inference('cnf', [status(esa)], [t8_xboole_1])).
% 0.83/0.99  thf('31', plain,
% 0.83/0.99      (![X0 : $i, X1 : $i]:
% 0.83/0.99         ((r1_tarski @ (k2_xboole_0 @ X0 @ X1) @ X0) | ~ (r1_tarski @ X1 @ X0))),
% 0.83/0.99      inference('sup-', [status(thm)], ['29', '30'])).
% 0.83/0.99  thf('32', plain,
% 0.83/0.99      (![X0 : $i, X1 : $i]:
% 0.83/0.99         (r1_tarski @ 
% 0.83/0.99          (k2_xboole_0 @ X0 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1)) @ X0)),
% 0.83/0.99      inference('sup-', [status(thm)], ['27', '31'])).
% 0.83/0.99  thf('33', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 0.83/0.99      inference('simplify', [status(thm)], ['28'])).
% 0.83/0.99  thf(t11_xboole_1, axiom,
% 0.83/0.99    (![A:$i,B:$i,C:$i]:
% 0.83/0.99     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.83/0.99  thf('34', plain,
% 0.83/0.99      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.83/0.99         ((r1_tarski @ X9 @ X10)
% 0.83/0.99          | ~ (r1_tarski @ (k2_xboole_0 @ X9 @ X11) @ X10))),
% 0.83/0.99      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.83/0.99  thf('35', plain,
% 0.83/0.99      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 0.83/0.99      inference('sup-', [status(thm)], ['33', '34'])).
% 0.83/0.99  thf('36', plain,
% 0.83/0.99      (![X1 : $i, X3 : $i]:
% 0.83/0.99         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 0.83/0.99      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.83/0.99  thf('37', plain,
% 0.83/0.99      (![X0 : $i, X1 : $i]:
% 0.83/0.99         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 0.83/0.99          | ((k2_xboole_0 @ X1 @ X0) = (X1)))),
% 0.83/0.99      inference('sup-', [status(thm)], ['35', '36'])).
% 0.83/0.99  thf('38', plain,
% 0.83/0.99      (![X0 : $i, X1 : $i]:
% 0.83/0.99         ((k2_xboole_0 @ X0 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1)) = (X0))),
% 0.83/0.99      inference('sup-', [status(thm)], ['32', '37'])).
% 0.83/0.99  thf('39', plain, (![X48 : $i]: (v1_relat_1 @ (k6_relat_1 @ X48))),
% 0.83/0.99      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.83/0.99  thf('40', plain,
% 0.83/0.99      (![X0 : $i, X1 : $i]:
% 0.83/0.99         ((k10_relat_1 @ (k6_relat_1 @ X0) @ (k2_xboole_0 @ X0 @ X1)) = (X0))),
% 0.83/0.99      inference('demod', [status(thm)], ['22', '38', '39'])).
% 0.83/0.99  thf('41', plain,
% 0.83/0.99      (((k10_relat_1 @ (k6_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B)) = (sk_A))),
% 0.83/0.99      inference('sup+', [status(thm)], ['14', '40'])).
% 0.83/0.99  thf('42', plain,
% 0.83/0.99      ((((k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)) = (sk_A))
% 0.83/0.99        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A))
% 0.83/0.99        | ~ (v1_relat_1 @ sk_B))),
% 0.83/0.99      inference('sup+', [status(thm)], ['11', '41'])).
% 0.83/0.99  thf('43', plain, (![X48 : $i]: (v1_relat_1 @ (k6_relat_1 @ X48))),
% 0.83/0.99      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.83/0.99  thf('44', plain, ((v1_relat_1 @ sk_B)),
% 0.83/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/0.99  thf('45', plain,
% 0.83/0.99      (((k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)) = (sk_A))),
% 0.83/0.99      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.83/0.99  thf('46', plain,
% 0.83/0.99      ((((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) = (sk_A))
% 0.83/0.99        | ~ (v1_relat_1 @ sk_B))),
% 0.83/0.99      inference('sup+', [status(thm)], ['10', '45'])).
% 0.83/0.99  thf('47', plain, ((v1_relat_1 @ sk_B)),
% 0.83/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/0.99  thf('48', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) = (sk_A))),
% 0.83/0.99      inference('demod', [status(thm)], ['46', '47'])).
% 0.83/0.99  thf('49', plain,
% 0.83/0.99      (![X56 : $i, X57 : $i]:
% 0.83/0.99         ((r1_tarski @ (k10_relat_1 @ X56 @ X57) @ (k1_relat_1 @ X56))
% 0.83/0.99          | ~ (v1_relat_1 @ X56))),
% 0.83/0.99      inference('cnf', [status(esa)], [t167_relat_1])).
% 0.83/0.99  thf('50', plain,
% 0.83/0.99      (![X0 : $i]:
% 0.83/0.99         ((r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0) @ sk_A)
% 0.83/0.99          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.83/0.99      inference('sup+', [status(thm)], ['48', '49'])).
% 0.83/0.99  thf('51', plain,
% 0.83/0.99      (![X0 : $i]:
% 0.83/0.99         (~ (v1_relat_1 @ sk_B)
% 0.83/0.99          | (r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0) @ sk_A))),
% 0.83/0.99      inference('sup-', [status(thm)], ['9', '50'])).
% 0.83/0.99  thf('52', plain, ((v1_relat_1 @ sk_B)),
% 0.83/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/0.99  thf('53', plain,
% 0.83/0.99      (![X0 : $i]:
% 0.83/0.99         (r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0) @ sk_A)),
% 0.83/0.99      inference('demod', [status(thm)], ['51', '52'])).
% 0.83/0.99  thf('54', plain,
% 0.83/0.99      (![X1 : $i, X3 : $i]:
% 0.83/0.99         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 0.83/0.99      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.83/0.99  thf('55', plain,
% 0.83/0.99      (![X0 : $i]:
% 0.83/0.99         (~ (r1_tarski @ sk_A @ (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0))
% 0.83/0.99          | ((sk_A) = (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0)))),
% 0.83/0.99      inference('sup-', [status(thm)], ['53', '54'])).
% 0.83/0.99  thf('56', plain,
% 0.83/0.99      ((~ (r1_tarski @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.83/0.99        | ~ (v1_relat_1 @ sk_B)
% 0.83/0.99        | ((sk_A)
% 0.83/0.99            = (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ 
% 0.83/0.99               (k9_relat_1 @ sk_B @ sk_A))))),
% 0.83/0.99      inference('sup-', [status(thm)], ['8', '55'])).
% 0.83/0.99  thf('57', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) = (sk_A))),
% 0.83/0.99      inference('demod', [status(thm)], ['46', '47'])).
% 0.83/0.99  thf('58', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 0.83/0.99      inference('simplify', [status(thm)], ['28'])).
% 0.83/0.99  thf('59', plain, ((v1_relat_1 @ sk_B)),
% 0.83/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/0.99  thf('60', plain,
% 0.83/0.99      (((sk_A)
% 0.83/0.99         = (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ 
% 0.83/0.99            (k9_relat_1 @ sk_B @ sk_A)))),
% 0.83/0.99      inference('demod', [status(thm)], ['56', '57', '58', '59'])).
% 0.83/0.99  thf('61', plain,
% 0.83/0.99      ((((sk_A)
% 0.83/0.99          = (k1_setfam_1 @ 
% 0.83/0.99             (k2_tarski @ sk_A @ 
% 0.83/0.99              (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))))
% 0.83/0.99        | ~ (v1_relat_1 @ sk_B))),
% 0.83/0.99      inference('sup+', [status(thm)], ['3', '60'])).
% 0.83/0.99  thf('62', plain, ((v1_relat_1 @ sk_B)),
% 0.83/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/0.99  thf('63', plain,
% 0.83/0.99      (((sk_A)
% 0.83/0.99         = (k1_setfam_1 @ 
% 0.83/0.99            (k2_tarski @ sk_A @ 
% 0.83/0.99             (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))))),
% 0.83/0.99      inference('demod', [status(thm)], ['61', '62'])).
% 0.83/0.99  thf(t100_xboole_1, axiom,
% 0.83/0.99    (![A:$i,B:$i]:
% 0.83/0.99     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.83/0.99  thf('64', plain,
% 0.83/0.99      (![X7 : $i, X8 : $i]:
% 0.83/0.99         ((k4_xboole_0 @ X7 @ X8)
% 0.83/0.99           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.83/0.99      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.83/0.99  thf('65', plain,
% 0.83/0.99      (![X46 : $i, X47 : $i]:
% 0.83/0.99         ((k1_setfam_1 @ (k2_tarski @ X46 @ X47)) = (k3_xboole_0 @ X46 @ X47))),
% 0.83/0.99      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.83/0.99  thf('66', plain,
% 0.83/0.99      (![X7 : $i, X8 : $i]:
% 0.83/0.99         ((k4_xboole_0 @ X7 @ X8)
% 0.83/0.99           = (k5_xboole_0 @ X7 @ (k1_setfam_1 @ (k2_tarski @ X7 @ X8))))),
% 0.83/0.99      inference('demod', [status(thm)], ['64', '65'])).
% 0.83/0.99  thf('67', plain,
% 0.83/0.99      (((k4_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 0.83/0.99         = (k5_xboole_0 @ sk_A @ sk_A))),
% 0.83/0.99      inference('sup+', [status(thm)], ['63', '66'])).
% 0.83/0.99  thf(idempotence_k3_xboole_0, axiom,
% 0.83/0.99    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.83/0.99  thf('68', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.83/0.99      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.83/0.99  thf('69', plain,
% 0.83/0.99      (![X46 : $i, X47 : $i]:
% 0.83/0.99         ((k1_setfam_1 @ (k2_tarski @ X46 @ X47)) = (k3_xboole_0 @ X46 @ X47))),
% 0.83/0.99      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.83/0.99  thf('70', plain,
% 0.83/0.99      (![X0 : $i]: ((k1_setfam_1 @ (k2_tarski @ X0 @ X0)) = (X0))),
% 0.83/0.99      inference('demod', [status(thm)], ['68', '69'])).
% 0.83/0.99  thf('71', plain,
% 0.83/0.99      (![X7 : $i, X8 : $i]:
% 0.83/0.99         ((k4_xboole_0 @ X7 @ X8)
% 0.83/0.99           = (k5_xboole_0 @ X7 @ (k1_setfam_1 @ (k2_tarski @ X7 @ X8))))),
% 0.83/0.99      inference('demod', [status(thm)], ['64', '65'])).
% 0.83/0.99  thf('72', plain,
% 0.83/0.99      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.83/0.99      inference('sup+', [status(thm)], ['70', '71'])).
% 0.83/0.99  thf('73', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 0.83/0.99      inference('simplify', [status(thm)], ['28'])).
% 0.83/0.99  thf(l32_xboole_1, axiom,
% 0.83/0.99    (![A:$i,B:$i]:
% 0.83/0.99     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.83/0.99  thf('74', plain,
% 0.83/0.99      (![X4 : $i, X6 : $i]:
% 0.83/0.99         (((k4_xboole_0 @ X4 @ X6) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ X6))),
% 0.83/0.99      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.83/0.99  thf('75', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.83/0.99      inference('sup-', [status(thm)], ['73', '74'])).
% 0.83/0.99  thf('76', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.83/0.99      inference('sup+', [status(thm)], ['72', '75'])).
% 0.83/0.99  thf('77', plain,
% 0.83/0.99      (((k4_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 0.83/0.99         = (k1_xboole_0))),
% 0.83/0.99      inference('demod', [status(thm)], ['67', '76'])).
% 0.83/0.99  thf('78', plain,
% 0.83/0.99      (![X4 : $i, X5 : $i]:
% 0.83/0.99         ((r1_tarski @ X4 @ X5) | ((k4_xboole_0 @ X4 @ X5) != (k1_xboole_0)))),
% 0.83/0.99      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.83/0.99  thf('79', plain,
% 0.83/0.99      ((((k1_xboole_0) != (k1_xboole_0))
% 0.83/0.99        | (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A))))),
% 0.83/0.99      inference('sup-', [status(thm)], ['77', '78'])).
% 0.83/0.99  thf('80', plain,
% 0.83/0.99      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 0.83/0.99      inference('simplify', [status(thm)], ['79'])).
% 0.83/0.99  thf('81', plain, ($false), inference('demod', [status(thm)], ['0', '80'])).
% 0.83/0.99  
% 0.83/0.99  % SZS output end Refutation
% 0.83/0.99  
% 0.83/1.00  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
