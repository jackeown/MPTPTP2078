%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.blXYXOIxSm

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:24 EST 2020

% Result     : Theorem 1.72s
% Output     : Refutation 1.72s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 386 expanded)
%              Number of leaves         :   37 ( 143 expanded)
%              Depth                    :   29
%              Number of atoms          : 1017 (3227 expanded)
%              Number of equality atoms :   83 ( 267 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

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
    ! [X69: $i,X70: $i,X71: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X70 @ X69 ) @ X71 )
        = ( k3_xboole_0 @ X69 @ ( k10_relat_1 @ X70 @ X71 ) ) )
      | ~ ( v1_relat_1 @ X70 ) ) ),
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
    ! [X69: $i,X70: $i,X71: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X70 @ X69 ) @ X71 )
        = ( k1_setfam_1 @ ( k2_tarski @ X69 @ ( k10_relat_1 @ X70 @ X71 ) ) ) )
      | ~ ( v1_relat_1 @ X70 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X69: $i,X70: $i,X71: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X70 @ X69 ) @ X71 )
        = ( k1_setfam_1 @ ( k2_tarski @ X69 @ ( k10_relat_1 @ X70 @ X71 ) ) ) )
      | ~ ( v1_relat_1 @ X70 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('5',plain,(
    ! [X57: $i] :
      ( ( ( k10_relat_1 @ X57 @ ( k2_relat_1 @ X57 ) )
        = ( k1_relat_1 @ X57 ) )
      | ~ ( v1_relat_1 @ X57 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ ( k10_relat_1 @ X1 @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) )
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
      | ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ ( k10_relat_1 @ X1 @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X69: $i,X70: $i,X71: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X70 @ X69 ) @ X71 )
        = ( k1_setfam_1 @ ( k2_tarski @ X69 @ ( k10_relat_1 @ X70 @ X71 ) ) ) )
      | ~ ( v1_relat_1 @ X70 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('10',plain,(
    ! [X49: $i,X50: $i] :
      ( ~ ( v1_relat_1 @ X49 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X49 @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('11',plain,(
    ! [X67: $i,X68: $i] :
      ( ( ( k7_relat_1 @ X68 @ X67 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X67 ) @ X68 ) )
      | ~ ( v1_relat_1 @ X68 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('12',plain,(
    ! [X61: $i,X62: $i] :
      ( ~ ( v1_relat_1 @ X61 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X62 @ X61 ) )
        = ( k10_relat_1 @ X62 @ ( k1_relat_1 @ X61 ) ) )
      | ~ ( v1_relat_1 @ X62 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('13',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('14',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_xboole_0 @ X13 @ X12 )
        = X12 )
      | ~ ( r1_tarski @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('15',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('16',plain,(
    ! [X64: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X64 ) )
      = X64 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('17',plain,(
    ! [X57: $i] :
      ( ( ( k10_relat_1 @ X57 @ ( k2_relat_1 @ X57 ) )
        = ( k1_relat_1 @ X57 ) )
      | ~ ( v1_relat_1 @ X57 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
        = ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X63: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X63 ) )
      = X63 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('20',plain,(
    ! [X48: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf(t175_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) )
        = ( k2_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('22',plain,(
    ! [X58: $i,X59: $i,X60: $i] :
      ( ( ( k10_relat_1 @ X58 @ ( k2_xboole_0 @ X59 @ X60 ) )
        = ( k2_xboole_0 @ ( k10_relat_1 @ X58 @ X59 ) @ ( k10_relat_1 @ X58 @ X60 ) ) )
      | ~ ( v1_relat_1 @ X58 ) ) ),
    inference(cnf,[status(esa)],[t175_relat_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X1 ) )
        = ( k2_xboole_0 @ X0 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X48: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ X0 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ X0 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('27',plain,(
    ! [X55: $i,X56: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X55 @ X56 ) @ ( k1_relat_1 @ X55 ) )
      | ~ ( v1_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('28',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ X1 ) )
      | ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ ( k6_relat_1 @ X1 ) ) @ ( k2_xboole_0 @ X1 @ ( k10_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) )
      | ( ( k1_relat_1 @ ( k6_relat_1 @ X1 ) )
        = ( k10_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X63: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X63 ) )
      = X63 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('32',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ X14 @ ( k2_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('33',plain,(
    ! [X63: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X63 ) )
      = X63 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ X0 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('35',plain,(
    ! [X48: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ X1 @ ( k10_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['30','31','32','33','34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['25','36'])).

thf('38',plain,
    ( ( k10_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
    = sk_A ),
    inference('sup+',[status(thm)],['15','37'])).

thf('39',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) )
      = sk_A )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['12','38'])).

thf('40',plain,(
    ! [X48: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('41',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,
    ( ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
      = sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['11','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X55: $i,X56: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X55 @ X56 ) @ ( k1_relat_1 @ X55 ) )
      | ~ ( v1_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) @ sk_A )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','47'])).

thf('49',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) @ sk_A ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_A @ ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) )
      | ( sk_A
        = ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_A @ ( k1_setfam_1 @ ( k2_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ( sk_A
        = ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','52'])).

thf('54',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_A @ ( k1_setfam_1 @ ( k2_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ X0 ) ) ) )
      | ( sk_A
        = ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ( sk_A
      = ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['8','55'])).

thf('57',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['43','44'])).

thf('58',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( X1 != X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('59',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( sk_A
    = ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['56','57','59','60'])).

thf('62',plain,
    ( ( sk_A
      = ( k1_setfam_1 @ ( k2_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['3','61'])).

thf('63',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( sk_A
    = ( k1_setfam_1 @ ( k2_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('65',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('66',plain,(
    ! [X46: $i,X47: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X46 @ X47 ) )
      = ( k3_xboole_0 @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('67',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k1_setfam_1 @ ( k2_tarski @ X7 @ X8 ) ) ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) )
    = ( k5_xboole_0 @ sk_A @ sk_A ) ),
    inference('sup+',[status(thm)],['64','67'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('70',plain,(
    ! [X46: $i,X47: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X46 @ X47 ) )
      = ( k3_xboole_0 @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k1_setfam_1 @ ( k2_tarski @ X7 @ X8 ) ) ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['58'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('75',plain,(
    ! [X4: $i,X6: $i] :
      ( ( ( k4_xboole_0 @ X4 @ X6 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['73','76'])).

thf('78',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['68','77'])).

thf('79',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( ( k4_xboole_0 @ X4 @ X5 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('80',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['58'])).

thf(t162_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( r1_tarski @ B @ C )
         => ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B )
            = ( k9_relat_1 @ A @ B ) ) ) ) )).

thf('83',plain,(
    ! [X52: $i,X53: $i,X54: $i] :
      ( ~ ( r1_tarski @ X52 @ X53 )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X54 @ X53 ) @ X52 )
        = ( k9_relat_1 @ X54 @ X52 ) )
      | ~ ( v1_relat_1 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t162_relat_1])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X0 )
        = ( k9_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X49: $i,X50: $i] :
      ( ~ ( v1_relat_1 @ X49 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X49 @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('86',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['43','44'])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('87',plain,(
    ! [X51: $i] :
      ( ( ( k9_relat_1 @ X51 @ ( k1_relat_1 @ X51 ) )
        = ( k2_relat_1 @ X51 ) )
      | ~ ( v1_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('88',plain,
    ( ( ( k9_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ sk_A )
      = ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( k9_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ sk_A )
      = ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['85','88'])).

thf('90',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( k9_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ sk_A )
    = ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,
    ( ( ( k9_relat_1 @ sk_B @ sk_A )
      = ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['84','91'])).

thf('93',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( k9_relat_1 @ sk_B @ sk_A )
    = ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['81','94'])).

thf('96',plain,(
    $false ),
    inference(demod,[status(thm)],['0','95'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.blXYXOIxSm
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:56:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.72/1.92  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.72/1.92  % Solved by: fo/fo7.sh
% 1.72/1.92  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.72/1.92  % done 2710 iterations in 1.459s
% 1.72/1.92  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.72/1.92  % SZS output start Refutation
% 1.72/1.92  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.72/1.92  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.72/1.92  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 1.72/1.92  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 1.72/1.92  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.72/1.92  thf(sk_A_type, type, sk_A: $i).
% 1.72/1.92  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.72/1.92  thf(sk_B_type, type, sk_B: $i).
% 1.72/1.92  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 1.72/1.92  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.72/1.92  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.72/1.92  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.72/1.92  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.72/1.92  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.72/1.92  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.72/1.92  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.72/1.92  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.72/1.92  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.72/1.92  thf(t146_funct_1, conjecture,
% 1.72/1.92    (![A:$i,B:$i]:
% 1.72/1.92     ( ( v1_relat_1 @ B ) =>
% 1.72/1.92       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 1.72/1.92         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 1.72/1.92  thf(zf_stmt_0, negated_conjecture,
% 1.72/1.92    (~( ![A:$i,B:$i]:
% 1.72/1.92        ( ( v1_relat_1 @ B ) =>
% 1.72/1.92          ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 1.72/1.92            ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )),
% 1.72/1.92    inference('cnf.neg', [status(esa)], [t146_funct_1])).
% 1.72/1.92  thf('0', plain,
% 1.72/1.92      (~ (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 1.72/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.92  thf(t139_funct_1, axiom,
% 1.72/1.92    (![A:$i,B:$i,C:$i]:
% 1.72/1.92     ( ( v1_relat_1 @ C ) =>
% 1.72/1.92       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 1.72/1.92         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 1.72/1.92  thf('1', plain,
% 1.72/1.92      (![X69 : $i, X70 : $i, X71 : $i]:
% 1.72/1.92         (((k10_relat_1 @ (k7_relat_1 @ X70 @ X69) @ X71)
% 1.72/1.92            = (k3_xboole_0 @ X69 @ (k10_relat_1 @ X70 @ X71)))
% 1.72/1.92          | ~ (v1_relat_1 @ X70))),
% 1.72/1.92      inference('cnf', [status(esa)], [t139_funct_1])).
% 1.72/1.92  thf(t12_setfam_1, axiom,
% 1.72/1.92    (![A:$i,B:$i]:
% 1.72/1.92     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.72/1.92  thf('2', plain,
% 1.72/1.92      (![X46 : $i, X47 : $i]:
% 1.72/1.92         ((k1_setfam_1 @ (k2_tarski @ X46 @ X47)) = (k3_xboole_0 @ X46 @ X47))),
% 1.72/1.92      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.72/1.92  thf('3', plain,
% 1.72/1.92      (![X69 : $i, X70 : $i, X71 : $i]:
% 1.72/1.92         (((k10_relat_1 @ (k7_relat_1 @ X70 @ X69) @ X71)
% 1.72/1.92            = (k1_setfam_1 @ (k2_tarski @ X69 @ (k10_relat_1 @ X70 @ X71))))
% 1.72/1.92          | ~ (v1_relat_1 @ X70))),
% 1.72/1.92      inference('demod', [status(thm)], ['1', '2'])).
% 1.72/1.92  thf('4', plain,
% 1.72/1.92      (![X69 : $i, X70 : $i, X71 : $i]:
% 1.72/1.92         (((k10_relat_1 @ (k7_relat_1 @ X70 @ X69) @ X71)
% 1.72/1.92            = (k1_setfam_1 @ (k2_tarski @ X69 @ (k10_relat_1 @ X70 @ X71))))
% 1.72/1.92          | ~ (v1_relat_1 @ X70))),
% 1.72/1.92      inference('demod', [status(thm)], ['1', '2'])).
% 1.72/1.92  thf(t169_relat_1, axiom,
% 1.72/1.92    (![A:$i]:
% 1.72/1.92     ( ( v1_relat_1 @ A ) =>
% 1.72/1.92       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 1.72/1.92  thf('5', plain,
% 1.72/1.92      (![X57 : $i]:
% 1.72/1.92         (((k10_relat_1 @ X57 @ (k2_relat_1 @ X57)) = (k1_relat_1 @ X57))
% 1.72/1.92          | ~ (v1_relat_1 @ X57))),
% 1.72/1.92      inference('cnf', [status(esa)], [t169_relat_1])).
% 1.72/1.92  thf('6', plain,
% 1.72/1.92      (![X0 : $i, X1 : $i]:
% 1.72/1.92         (((k1_setfam_1 @ 
% 1.72/1.92            (k2_tarski @ X0 @ 
% 1.72/1.92             (k10_relat_1 @ X1 @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X0)))))
% 1.72/1.92            = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 1.72/1.92          | ~ (v1_relat_1 @ X1)
% 1.72/1.92          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 1.72/1.92      inference('sup+', [status(thm)], ['4', '5'])).
% 1.72/1.92  thf(dt_k7_relat_1, axiom,
% 1.72/1.92    (![A:$i,B:$i]:
% 1.72/1.92     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 1.72/1.92  thf('7', plain,
% 1.72/1.92      (![X49 : $i, X50 : $i]:
% 1.72/1.92         (~ (v1_relat_1 @ X49) | (v1_relat_1 @ (k7_relat_1 @ X49 @ X50)))),
% 1.72/1.92      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 1.72/1.92  thf('8', plain,
% 1.72/1.92      (![X0 : $i, X1 : $i]:
% 1.72/1.92         (~ (v1_relat_1 @ X1)
% 1.72/1.92          | ((k1_setfam_1 @ 
% 1.72/1.92              (k2_tarski @ X0 @ 
% 1.72/1.92               (k10_relat_1 @ X1 @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X0)))))
% 1.72/1.92              = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 1.72/1.92      inference('clc', [status(thm)], ['6', '7'])).
% 1.72/1.92  thf('9', plain,
% 1.72/1.92      (![X69 : $i, X70 : $i, X71 : $i]:
% 1.72/1.92         (((k10_relat_1 @ (k7_relat_1 @ X70 @ X69) @ X71)
% 1.72/1.92            = (k1_setfam_1 @ (k2_tarski @ X69 @ (k10_relat_1 @ X70 @ X71))))
% 1.72/1.92          | ~ (v1_relat_1 @ X70))),
% 1.72/1.92      inference('demod', [status(thm)], ['1', '2'])).
% 1.72/1.92  thf('10', plain,
% 1.72/1.92      (![X49 : $i, X50 : $i]:
% 1.72/1.92         (~ (v1_relat_1 @ X49) | (v1_relat_1 @ (k7_relat_1 @ X49 @ X50)))),
% 1.72/1.92      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 1.72/1.92  thf(t94_relat_1, axiom,
% 1.72/1.92    (![A:$i,B:$i]:
% 1.72/1.92     ( ( v1_relat_1 @ B ) =>
% 1.72/1.92       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 1.72/1.92  thf('11', plain,
% 1.72/1.92      (![X67 : $i, X68 : $i]:
% 1.72/1.92         (((k7_relat_1 @ X68 @ X67) = (k5_relat_1 @ (k6_relat_1 @ X67) @ X68))
% 1.72/1.92          | ~ (v1_relat_1 @ X68))),
% 1.72/1.92      inference('cnf', [status(esa)], [t94_relat_1])).
% 1.72/1.92  thf(t182_relat_1, axiom,
% 1.72/1.92    (![A:$i]:
% 1.72/1.92     ( ( v1_relat_1 @ A ) =>
% 1.72/1.92       ( ![B:$i]:
% 1.72/1.92         ( ( v1_relat_1 @ B ) =>
% 1.72/1.92           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 1.72/1.92             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 1.72/1.92  thf('12', plain,
% 1.72/1.92      (![X61 : $i, X62 : $i]:
% 1.72/1.92         (~ (v1_relat_1 @ X61)
% 1.72/1.92          | ((k1_relat_1 @ (k5_relat_1 @ X62 @ X61))
% 1.72/1.92              = (k10_relat_1 @ X62 @ (k1_relat_1 @ X61)))
% 1.72/1.92          | ~ (v1_relat_1 @ X62))),
% 1.72/1.92      inference('cnf', [status(esa)], [t182_relat_1])).
% 1.72/1.92  thf('13', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 1.72/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.92  thf(t12_xboole_1, axiom,
% 1.72/1.92    (![A:$i,B:$i]:
% 1.72/1.92     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 1.72/1.92  thf('14', plain,
% 1.72/1.92      (![X12 : $i, X13 : $i]:
% 1.72/1.92         (((k2_xboole_0 @ X13 @ X12) = (X12)) | ~ (r1_tarski @ X13 @ X12))),
% 1.72/1.92      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.72/1.92  thf('15', plain,
% 1.72/1.92      (((k2_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)) = (k1_relat_1 @ sk_B))),
% 1.72/1.92      inference('sup-', [status(thm)], ['13', '14'])).
% 1.72/1.92  thf(t71_relat_1, axiom,
% 1.72/1.92    (![A:$i]:
% 1.72/1.92     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 1.72/1.92       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 1.72/1.92  thf('16', plain, (![X64 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X64)) = (X64))),
% 1.72/1.92      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.72/1.92  thf('17', plain,
% 1.72/1.92      (![X57 : $i]:
% 1.72/1.92         (((k10_relat_1 @ X57 @ (k2_relat_1 @ X57)) = (k1_relat_1 @ X57))
% 1.72/1.92          | ~ (v1_relat_1 @ X57))),
% 1.72/1.92      inference('cnf', [status(esa)], [t169_relat_1])).
% 1.72/1.92  thf('18', plain,
% 1.72/1.92      (![X0 : $i]:
% 1.72/1.92         (((k10_relat_1 @ (k6_relat_1 @ X0) @ X0)
% 1.72/1.92            = (k1_relat_1 @ (k6_relat_1 @ X0)))
% 1.72/1.92          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 1.72/1.92      inference('sup+', [status(thm)], ['16', '17'])).
% 1.72/1.92  thf('19', plain, (![X63 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X63)) = (X63))),
% 1.72/1.92      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.72/1.92  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 1.72/1.92  thf('20', plain, (![X48 : $i]: (v1_relat_1 @ (k6_relat_1 @ X48))),
% 1.72/1.92      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.72/1.92  thf('21', plain,
% 1.72/1.92      (![X0 : $i]: ((k10_relat_1 @ (k6_relat_1 @ X0) @ X0) = (X0))),
% 1.72/1.92      inference('demod', [status(thm)], ['18', '19', '20'])).
% 1.72/1.92  thf(t175_relat_1, axiom,
% 1.72/1.92    (![A:$i,B:$i,C:$i]:
% 1.72/1.92     ( ( v1_relat_1 @ C ) =>
% 1.72/1.92       ( ( k10_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) ) =
% 1.72/1.92         ( k2_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 1.72/1.92  thf('22', plain,
% 1.72/1.92      (![X58 : $i, X59 : $i, X60 : $i]:
% 1.72/1.92         (((k10_relat_1 @ X58 @ (k2_xboole_0 @ X59 @ X60))
% 1.72/1.92            = (k2_xboole_0 @ (k10_relat_1 @ X58 @ X59) @ 
% 1.72/1.92               (k10_relat_1 @ X58 @ X60)))
% 1.72/1.92          | ~ (v1_relat_1 @ X58))),
% 1.72/1.92      inference('cnf', [status(esa)], [t175_relat_1])).
% 1.72/1.92  thf('23', plain,
% 1.72/1.92      (![X0 : $i, X1 : $i]:
% 1.72/1.92         (((k10_relat_1 @ (k6_relat_1 @ X0) @ (k2_xboole_0 @ X0 @ X1))
% 1.72/1.92            = (k2_xboole_0 @ X0 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1)))
% 1.72/1.92          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 1.72/1.92      inference('sup+', [status(thm)], ['21', '22'])).
% 1.72/1.92  thf('24', plain, (![X48 : $i]: (v1_relat_1 @ (k6_relat_1 @ X48))),
% 1.72/1.92      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.72/1.92  thf('25', plain,
% 1.72/1.92      (![X0 : $i, X1 : $i]:
% 1.72/1.92         ((k10_relat_1 @ (k6_relat_1 @ X0) @ (k2_xboole_0 @ X0 @ X1))
% 1.72/1.92           = (k2_xboole_0 @ X0 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1)))),
% 1.72/1.92      inference('demod', [status(thm)], ['23', '24'])).
% 1.72/1.92  thf('26', plain,
% 1.72/1.92      (![X0 : $i, X1 : $i]:
% 1.72/1.92         ((k10_relat_1 @ (k6_relat_1 @ X0) @ (k2_xboole_0 @ X0 @ X1))
% 1.72/1.92           = (k2_xboole_0 @ X0 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1)))),
% 1.72/1.92      inference('demod', [status(thm)], ['23', '24'])).
% 1.72/1.92  thf(t167_relat_1, axiom,
% 1.72/1.92    (![A:$i,B:$i]:
% 1.72/1.92     ( ( v1_relat_1 @ B ) =>
% 1.72/1.92       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 1.72/1.92  thf('27', plain,
% 1.72/1.92      (![X55 : $i, X56 : $i]:
% 1.72/1.92         ((r1_tarski @ (k10_relat_1 @ X55 @ X56) @ (k1_relat_1 @ X55))
% 1.72/1.92          | ~ (v1_relat_1 @ X55))),
% 1.72/1.92      inference('cnf', [status(esa)], [t167_relat_1])).
% 1.72/1.92  thf(d10_xboole_0, axiom,
% 1.72/1.92    (![A:$i,B:$i]:
% 1.72/1.92     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.72/1.92  thf('28', plain,
% 1.72/1.92      (![X1 : $i, X3 : $i]:
% 1.72/1.92         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 1.72/1.92      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.72/1.92  thf('29', plain,
% 1.72/1.92      (![X0 : $i, X1 : $i]:
% 1.72/1.92         (~ (v1_relat_1 @ X0)
% 1.72/1.92          | ~ (r1_tarski @ (k1_relat_1 @ X0) @ (k10_relat_1 @ X0 @ X1))
% 1.72/1.92          | ((k1_relat_1 @ X0) = (k10_relat_1 @ X0 @ X1)))),
% 1.72/1.92      inference('sup-', [status(thm)], ['27', '28'])).
% 1.72/1.92  thf('30', plain,
% 1.72/1.92      (![X0 : $i, X1 : $i]:
% 1.72/1.92         (~ (r1_tarski @ (k1_relat_1 @ (k6_relat_1 @ X1)) @ 
% 1.72/1.92             (k2_xboole_0 @ X1 @ (k10_relat_1 @ (k6_relat_1 @ X1) @ X0)))
% 1.72/1.92          | ((k1_relat_1 @ (k6_relat_1 @ X1))
% 1.72/1.92              = (k10_relat_1 @ (k6_relat_1 @ X1) @ (k2_xboole_0 @ X1 @ X0)))
% 1.72/1.92          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 1.72/1.92      inference('sup-', [status(thm)], ['26', '29'])).
% 1.72/1.92  thf('31', plain, (![X63 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X63)) = (X63))),
% 1.72/1.92      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.72/1.92  thf(t7_xboole_1, axiom,
% 1.72/1.92    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 1.72/1.92  thf('32', plain,
% 1.72/1.92      (![X14 : $i, X15 : $i]: (r1_tarski @ X14 @ (k2_xboole_0 @ X14 @ X15))),
% 1.72/1.92      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.72/1.92  thf('33', plain, (![X63 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X63)) = (X63))),
% 1.72/1.92      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.72/1.92  thf('34', plain,
% 1.72/1.92      (![X0 : $i, X1 : $i]:
% 1.72/1.92         ((k10_relat_1 @ (k6_relat_1 @ X0) @ (k2_xboole_0 @ X0 @ X1))
% 1.72/1.92           = (k2_xboole_0 @ X0 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1)))),
% 1.72/1.92      inference('demod', [status(thm)], ['23', '24'])).
% 1.72/1.92  thf('35', plain, (![X48 : $i]: (v1_relat_1 @ (k6_relat_1 @ X48))),
% 1.72/1.92      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.72/1.92  thf('36', plain,
% 1.72/1.92      (![X0 : $i, X1 : $i]:
% 1.72/1.92         ((X1) = (k2_xboole_0 @ X1 @ (k10_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 1.72/1.92      inference('demod', [status(thm)], ['30', '31', '32', '33', '34', '35'])).
% 1.72/1.92  thf('37', plain,
% 1.72/1.92      (![X0 : $i, X1 : $i]:
% 1.72/1.92         ((k10_relat_1 @ (k6_relat_1 @ X0) @ (k2_xboole_0 @ X0 @ X1)) = (X0))),
% 1.72/1.92      inference('demod', [status(thm)], ['25', '36'])).
% 1.72/1.92  thf('38', plain,
% 1.72/1.92      (((k10_relat_1 @ (k6_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B)) = (sk_A))),
% 1.72/1.92      inference('sup+', [status(thm)], ['15', '37'])).
% 1.72/1.92  thf('39', plain,
% 1.72/1.92      ((((k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)) = (sk_A))
% 1.72/1.92        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A))
% 1.72/1.92        | ~ (v1_relat_1 @ sk_B))),
% 1.72/1.92      inference('sup+', [status(thm)], ['12', '38'])).
% 1.72/1.92  thf('40', plain, (![X48 : $i]: (v1_relat_1 @ (k6_relat_1 @ X48))),
% 1.72/1.92      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.72/1.92  thf('41', plain, ((v1_relat_1 @ sk_B)),
% 1.72/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.92  thf('42', plain,
% 1.72/1.92      (((k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)) = (sk_A))),
% 1.72/1.92      inference('demod', [status(thm)], ['39', '40', '41'])).
% 1.72/1.92  thf('43', plain,
% 1.72/1.92      ((((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) = (sk_A))
% 1.72/1.92        | ~ (v1_relat_1 @ sk_B))),
% 1.72/1.92      inference('sup+', [status(thm)], ['11', '42'])).
% 1.72/1.92  thf('44', plain, ((v1_relat_1 @ sk_B)),
% 1.72/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.92  thf('45', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) = (sk_A))),
% 1.72/1.92      inference('demod', [status(thm)], ['43', '44'])).
% 1.72/1.92  thf('46', plain,
% 1.72/1.92      (![X55 : $i, X56 : $i]:
% 1.72/1.92         ((r1_tarski @ (k10_relat_1 @ X55 @ X56) @ (k1_relat_1 @ X55))
% 1.72/1.92          | ~ (v1_relat_1 @ X55))),
% 1.72/1.92      inference('cnf', [status(esa)], [t167_relat_1])).
% 1.72/1.92  thf('47', plain,
% 1.72/1.92      (![X0 : $i]:
% 1.72/1.92         ((r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0) @ sk_A)
% 1.72/1.92          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 1.72/1.92      inference('sup+', [status(thm)], ['45', '46'])).
% 1.72/1.92  thf('48', plain,
% 1.72/1.92      (![X0 : $i]:
% 1.72/1.92         (~ (v1_relat_1 @ sk_B)
% 1.72/1.92          | (r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0) @ sk_A))),
% 1.72/1.92      inference('sup-', [status(thm)], ['10', '47'])).
% 1.72/1.92  thf('49', plain, ((v1_relat_1 @ sk_B)),
% 1.72/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.92  thf('50', plain,
% 1.72/1.92      (![X0 : $i]:
% 1.72/1.92         (r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0) @ sk_A)),
% 1.72/1.92      inference('demod', [status(thm)], ['48', '49'])).
% 1.72/1.92  thf('51', plain,
% 1.72/1.92      (![X1 : $i, X3 : $i]:
% 1.72/1.92         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 1.72/1.92      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.72/1.92  thf('52', plain,
% 1.72/1.92      (![X0 : $i]:
% 1.72/1.92         (~ (r1_tarski @ sk_A @ (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0))
% 1.72/1.92          | ((sk_A) = (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0)))),
% 1.72/1.92      inference('sup-', [status(thm)], ['50', '51'])).
% 1.72/1.92  thf('53', plain,
% 1.72/1.92      (![X0 : $i]:
% 1.72/1.92         (~ (r1_tarski @ sk_A @ 
% 1.72/1.92             (k1_setfam_1 @ (k2_tarski @ sk_A @ (k10_relat_1 @ sk_B @ X0))))
% 1.72/1.92          | ~ (v1_relat_1 @ sk_B)
% 1.72/1.92          | ((sk_A) = (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0)))),
% 1.72/1.92      inference('sup-', [status(thm)], ['9', '52'])).
% 1.72/1.92  thf('54', plain, ((v1_relat_1 @ sk_B)),
% 1.72/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.92  thf('55', plain,
% 1.72/1.92      (![X0 : $i]:
% 1.72/1.92         (~ (r1_tarski @ sk_A @ 
% 1.72/1.92             (k1_setfam_1 @ (k2_tarski @ sk_A @ (k10_relat_1 @ sk_B @ X0))))
% 1.72/1.92          | ((sk_A) = (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0)))),
% 1.72/1.92      inference('demod', [status(thm)], ['53', '54'])).
% 1.72/1.92  thf('56', plain,
% 1.72/1.92      ((~ (r1_tarski @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 1.72/1.92        | ~ (v1_relat_1 @ sk_B)
% 1.72/1.92        | ((sk_A)
% 1.72/1.92            = (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ 
% 1.72/1.92               (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))))),
% 1.72/1.92      inference('sup-', [status(thm)], ['8', '55'])).
% 1.72/1.92  thf('57', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) = (sk_A))),
% 1.72/1.92      inference('demod', [status(thm)], ['43', '44'])).
% 1.72/1.92  thf('58', plain,
% 1.72/1.92      (![X1 : $i, X2 : $i]: ((r1_tarski @ X1 @ X2) | ((X1) != (X2)))),
% 1.72/1.92      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.72/1.92  thf('59', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 1.72/1.92      inference('simplify', [status(thm)], ['58'])).
% 1.72/1.92  thf('60', plain, ((v1_relat_1 @ sk_B)),
% 1.72/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.92  thf('61', plain,
% 1.72/1.92      (((sk_A)
% 1.72/1.92         = (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ 
% 1.72/1.92            (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))))),
% 1.72/1.92      inference('demod', [status(thm)], ['56', '57', '59', '60'])).
% 1.72/1.92  thf('62', plain,
% 1.72/1.92      ((((sk_A)
% 1.72/1.92          = (k1_setfam_1 @ 
% 1.72/1.92             (k2_tarski @ sk_A @ 
% 1.72/1.92              (k10_relat_1 @ sk_B @ (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))))))
% 1.72/1.92        | ~ (v1_relat_1 @ sk_B))),
% 1.72/1.92      inference('sup+', [status(thm)], ['3', '61'])).
% 1.72/1.92  thf('63', plain, ((v1_relat_1 @ sk_B)),
% 1.72/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.92  thf('64', plain,
% 1.72/1.92      (((sk_A)
% 1.72/1.92         = (k1_setfam_1 @ 
% 1.72/1.92            (k2_tarski @ sk_A @ 
% 1.72/1.92             (k10_relat_1 @ sk_B @ (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))))))),
% 1.72/1.92      inference('demod', [status(thm)], ['62', '63'])).
% 1.72/1.92  thf(t100_xboole_1, axiom,
% 1.72/1.92    (![A:$i,B:$i]:
% 1.72/1.92     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.72/1.92  thf('65', plain,
% 1.72/1.92      (![X7 : $i, X8 : $i]:
% 1.72/1.92         ((k4_xboole_0 @ X7 @ X8)
% 1.72/1.92           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 1.72/1.92      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.72/1.92  thf('66', plain,
% 1.72/1.92      (![X46 : $i, X47 : $i]:
% 1.72/1.92         ((k1_setfam_1 @ (k2_tarski @ X46 @ X47)) = (k3_xboole_0 @ X46 @ X47))),
% 1.72/1.92      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.72/1.92  thf('67', plain,
% 1.72/1.92      (![X7 : $i, X8 : $i]:
% 1.72/1.92         ((k4_xboole_0 @ X7 @ X8)
% 1.72/1.92           = (k5_xboole_0 @ X7 @ (k1_setfam_1 @ (k2_tarski @ X7 @ X8))))),
% 1.72/1.92      inference('demod', [status(thm)], ['65', '66'])).
% 1.72/1.92  thf('68', plain,
% 1.72/1.92      (((k4_xboole_0 @ sk_A @ 
% 1.72/1.92         (k10_relat_1 @ sk_B @ (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))))
% 1.72/1.92         = (k5_xboole_0 @ sk_A @ sk_A))),
% 1.72/1.92      inference('sup+', [status(thm)], ['64', '67'])).
% 1.72/1.92  thf(idempotence_k3_xboole_0, axiom,
% 1.72/1.92    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 1.72/1.92  thf('69', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 1.72/1.92      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 1.72/1.92  thf('70', plain,
% 1.72/1.92      (![X46 : $i, X47 : $i]:
% 1.72/1.92         ((k1_setfam_1 @ (k2_tarski @ X46 @ X47)) = (k3_xboole_0 @ X46 @ X47))),
% 1.72/1.92      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.72/1.92  thf('71', plain,
% 1.72/1.92      (![X0 : $i]: ((k1_setfam_1 @ (k2_tarski @ X0 @ X0)) = (X0))),
% 1.72/1.92      inference('demod', [status(thm)], ['69', '70'])).
% 1.72/1.92  thf('72', plain,
% 1.72/1.92      (![X7 : $i, X8 : $i]:
% 1.72/1.92         ((k4_xboole_0 @ X7 @ X8)
% 1.72/1.92           = (k5_xboole_0 @ X7 @ (k1_setfam_1 @ (k2_tarski @ X7 @ X8))))),
% 1.72/1.92      inference('demod', [status(thm)], ['65', '66'])).
% 1.72/1.92  thf('73', plain,
% 1.72/1.92      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.72/1.92      inference('sup+', [status(thm)], ['71', '72'])).
% 1.72/1.92  thf('74', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 1.72/1.92      inference('simplify', [status(thm)], ['58'])).
% 1.72/1.92  thf(l32_xboole_1, axiom,
% 1.72/1.92    (![A:$i,B:$i]:
% 1.72/1.92     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.72/1.92  thf('75', plain,
% 1.72/1.92      (![X4 : $i, X6 : $i]:
% 1.72/1.92         (((k4_xboole_0 @ X4 @ X6) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ X6))),
% 1.72/1.92      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.72/1.92  thf('76', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.72/1.92      inference('sup-', [status(thm)], ['74', '75'])).
% 1.72/1.92  thf('77', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.72/1.92      inference('sup+', [status(thm)], ['73', '76'])).
% 1.72/1.92  thf('78', plain,
% 1.72/1.92      (((k4_xboole_0 @ sk_A @ 
% 1.72/1.92         (k10_relat_1 @ sk_B @ (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))))
% 1.72/1.92         = (k1_xboole_0))),
% 1.72/1.92      inference('demod', [status(thm)], ['68', '77'])).
% 1.72/1.92  thf('79', plain,
% 1.72/1.92      (![X4 : $i, X5 : $i]:
% 1.72/1.92         ((r1_tarski @ X4 @ X5) | ((k4_xboole_0 @ X4 @ X5) != (k1_xboole_0)))),
% 1.72/1.92      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.72/1.92  thf('80', plain,
% 1.72/1.92      ((((k1_xboole_0) != (k1_xboole_0))
% 1.72/1.92        | (r1_tarski @ sk_A @ 
% 1.72/1.92           (k10_relat_1 @ sk_B @ (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))))),
% 1.72/1.92      inference('sup-', [status(thm)], ['78', '79'])).
% 1.72/1.92  thf('81', plain,
% 1.72/1.92      ((r1_tarski @ sk_A @ 
% 1.72/1.92        (k10_relat_1 @ sk_B @ (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))))),
% 1.72/1.92      inference('simplify', [status(thm)], ['80'])).
% 1.72/1.92  thf('82', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 1.72/1.92      inference('simplify', [status(thm)], ['58'])).
% 1.72/1.92  thf(t162_relat_1, axiom,
% 1.72/1.92    (![A:$i]:
% 1.72/1.92     ( ( v1_relat_1 @ A ) =>
% 1.72/1.92       ( ![B:$i,C:$i]:
% 1.72/1.92         ( ( r1_tarski @ B @ C ) =>
% 1.72/1.92           ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B ) =
% 1.72/1.92             ( k9_relat_1 @ A @ B ) ) ) ) ))).
% 1.72/1.92  thf('83', plain,
% 1.72/1.92      (![X52 : $i, X53 : $i, X54 : $i]:
% 1.72/1.92         (~ (r1_tarski @ X52 @ X53)
% 1.72/1.92          | ((k9_relat_1 @ (k7_relat_1 @ X54 @ X53) @ X52)
% 1.72/1.92              = (k9_relat_1 @ X54 @ X52))
% 1.72/1.92          | ~ (v1_relat_1 @ X54))),
% 1.72/1.92      inference('cnf', [status(esa)], [t162_relat_1])).
% 1.72/1.92  thf('84', plain,
% 1.72/1.92      (![X0 : $i, X1 : $i]:
% 1.72/1.92         (~ (v1_relat_1 @ X1)
% 1.72/1.92          | ((k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X0)
% 1.72/1.92              = (k9_relat_1 @ X1 @ X0)))),
% 1.72/1.92      inference('sup-', [status(thm)], ['82', '83'])).
% 1.72/1.92  thf('85', plain,
% 1.72/1.92      (![X49 : $i, X50 : $i]:
% 1.72/1.92         (~ (v1_relat_1 @ X49) | (v1_relat_1 @ (k7_relat_1 @ X49 @ X50)))),
% 1.72/1.92      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 1.72/1.92  thf('86', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) = (sk_A))),
% 1.72/1.92      inference('demod', [status(thm)], ['43', '44'])).
% 1.72/1.92  thf(t146_relat_1, axiom,
% 1.72/1.92    (![A:$i]:
% 1.72/1.92     ( ( v1_relat_1 @ A ) =>
% 1.72/1.92       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 1.72/1.92  thf('87', plain,
% 1.72/1.92      (![X51 : $i]:
% 1.72/1.92         (((k9_relat_1 @ X51 @ (k1_relat_1 @ X51)) = (k2_relat_1 @ X51))
% 1.72/1.92          | ~ (v1_relat_1 @ X51))),
% 1.72/1.92      inference('cnf', [status(esa)], [t146_relat_1])).
% 1.72/1.92  thf('88', plain,
% 1.72/1.92      ((((k9_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ sk_A)
% 1.72/1.92          = (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 1.72/1.92        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 1.72/1.92      inference('sup+', [status(thm)], ['86', '87'])).
% 1.72/1.92  thf('89', plain,
% 1.72/1.92      ((~ (v1_relat_1 @ sk_B)
% 1.72/1.92        | ((k9_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ sk_A)
% 1.72/1.92            = (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))))),
% 1.72/1.92      inference('sup-', [status(thm)], ['85', '88'])).
% 1.72/1.92  thf('90', plain, ((v1_relat_1 @ sk_B)),
% 1.72/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.92  thf('91', plain,
% 1.72/1.92      (((k9_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ sk_A)
% 1.72/1.92         = (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 1.72/1.92      inference('demod', [status(thm)], ['89', '90'])).
% 1.72/1.92  thf('92', plain,
% 1.72/1.92      ((((k9_relat_1 @ sk_B @ sk_A) = (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 1.72/1.92        | ~ (v1_relat_1 @ sk_B))),
% 1.72/1.92      inference('sup+', [status(thm)], ['84', '91'])).
% 1.72/1.92  thf('93', plain, ((v1_relat_1 @ sk_B)),
% 1.72/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.92  thf('94', plain,
% 1.72/1.92      (((k9_relat_1 @ sk_B @ sk_A) = (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 1.72/1.92      inference('demod', [status(thm)], ['92', '93'])).
% 1.72/1.92  thf('95', plain,
% 1.72/1.92      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 1.72/1.92      inference('demod', [status(thm)], ['81', '94'])).
% 1.72/1.92  thf('96', plain, ($false), inference('demod', [status(thm)], ['0', '95'])).
% 1.72/1.92  
% 1.72/1.92  % SZS output end Refutation
% 1.72/1.92  
% 1.76/1.93  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
