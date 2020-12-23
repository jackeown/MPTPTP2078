%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yW6MZs4yTd

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:24 EST 2020

% Result     : Theorem 1.10s
% Output     : Refutation 1.10s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 252 expanded)
%              Number of leaves         :   39 (  91 expanded)
%              Depth                    :   28
%              Number of atoms          :  969 (2086 expanded)
%              Number of equality atoms :   78 ( 150 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

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
    ! [X70: $i,X71: $i,X72: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X71 @ X70 ) @ X72 )
        = ( k3_xboole_0 @ X70 @ ( k10_relat_1 @ X71 @ X72 ) ) )
      | ~ ( v1_relat_1 @ X71 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X47: $i,X48: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X47 @ X48 ) )
      = ( k3_xboole_0 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('3',plain,(
    ! [X70: $i,X71: $i,X72: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X71 @ X70 ) @ X72 )
        = ( k1_setfam_1 @ ( k2_tarski @ X70 @ ( k10_relat_1 @ X71 @ X72 ) ) ) )
      | ~ ( v1_relat_1 @ X71 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X50: $i,X51: $i] :
      ( ~ ( v1_relat_1 @ X50 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X50 @ X51 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( X1 != X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('6',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['5'])).

thf(t162_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( r1_tarski @ B @ C )
         => ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B )
            = ( k9_relat_1 @ A @ B ) ) ) ) )).

thf('7',plain,(
    ! [X53: $i,X54: $i,X55: $i] :
      ( ~ ( r1_tarski @ X53 @ X54 )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X55 @ X54 ) @ X53 )
        = ( k9_relat_1 @ X55 @ X53 ) )
      | ~ ( v1_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t162_relat_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X0 )
        = ( k9_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X50: $i,X51: $i] :
      ( ~ ( v1_relat_1 @ X50 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X50 @ X51 ) ) ) ),
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
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['5'])).

thf('13',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t14_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B )
        & ! [D: $i] :
            ( ( ( r1_tarski @ A @ D )
              & ( r1_tarski @ C @ D ) )
           => ( r1_tarski @ B @ D ) ) )
     => ( B
        = ( k2_xboole_0 @ A @ C ) ) ) )).

thf('14',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X12 @ X13 )
      | ~ ( r1_tarski @ X14 @ X13 )
      | ( r1_tarski @ X14 @ ( sk_D @ X14 @ X13 @ X12 ) )
      | ( X13
        = ( k2_xboole_0 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t14_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ sk_B )
        = ( k2_xboole_0 @ sk_A @ X0 ) )
      | ( r1_tarski @ X0 @ ( sk_D @ X0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) )
      | ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( sk_D @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_B ) @ sk_A ) )
    | ( ( k1_relat_1 @ sk_B )
      = ( k2_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X12 @ X13 )
      | ~ ( r1_tarski @ X14 @ X13 )
      | ~ ( r1_tarski @ X13 @ ( sk_D @ X14 @ X13 @ X12 ) )
      | ( X13
        = ( k2_xboole_0 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t14_xboole_1])).

thf('18',plain,
    ( ( ( k1_relat_1 @ sk_B )
      = ( k2_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
    | ( ( k1_relat_1 @ sk_B )
      = ( k2_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
    | ~ ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['5'])).

thf('20',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( ( k1_relat_1 @ sk_B )
      = ( k2_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
    | ( ( k1_relat_1 @ sk_B )
      = ( k2_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k2_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('23',plain,(
    ! [X65: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X65 ) )
      = X65 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('24',plain,(
    ! [X58: $i] :
      ( ( ( k10_relat_1 @ X58 @ ( k2_relat_1 @ X58 ) )
        = ( k1_relat_1 @ X58 ) )
      | ~ ( v1_relat_1 @ X58 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
        = ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X64: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X64 ) )
      = X64 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('27',plain,(
    ! [X49: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf(t175_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) )
        = ( k2_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('29',plain,(
    ! [X59: $i,X60: $i,X61: $i] :
      ( ( ( k10_relat_1 @ X59 @ ( k2_xboole_0 @ X60 @ X61 ) )
        = ( k2_xboole_0 @ ( k10_relat_1 @ X59 @ X60 ) @ ( k10_relat_1 @ X59 @ X61 ) ) )
      | ~ ( v1_relat_1 @ X59 ) ) ),
    inference(cnf,[status(esa)],[t175_relat_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X1 ) )
        = ( k2_xboole_0 @ X0 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X64: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X64 ) )
      = X64 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('32',plain,(
    ! [X56: $i,X57: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X56 @ X57 ) @ ( k1_relat_1 @ X56 ) )
      | ~ ( v1_relat_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X49: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['5'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('37',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ X17 @ X18 )
      | ~ ( r1_tarski @ X19 @ X18 )
      | ( r1_tarski @ ( k2_xboole_0 @ X17 @ X19 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ X0 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['5'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('41',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X9 @ X11 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['39','44'])).

thf('46',plain,(
    ! [X49: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['30','45','46'])).

thf('48',plain,
    ( ( k10_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
    = sk_A ),
    inference('sup+',[status(thm)],['22','47'])).

thf('49',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) )
      = sk_A )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['11','48'])).

thf('50',plain,(
    ! [X49: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('51',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,
    ( ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
      = sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['10','52'])).

thf('54',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['53','54'])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('56',plain,(
    ! [X52: $i] :
      ( ( ( k9_relat_1 @ X52 @ ( k1_relat_1 @ X52 ) )
        = ( k2_relat_1 @ X52 ) )
      | ~ ( v1_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('57',plain,
    ( ( ( k9_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ sk_A )
      = ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( k9_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ sk_A )
      = ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['9','57'])).

thf('59',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( k9_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ sk_A )
    = ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( ( k9_relat_1 @ sk_B @ sk_A )
      = ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['8','60'])).

thf('62',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( k9_relat_1 @ sk_B @ sk_A )
    = ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X58: $i] :
      ( ( ( k10_relat_1 @ X58 @ ( k2_relat_1 @ X58 ) )
        = ( k1_relat_1 @ X58 ) )
      | ~ ( v1_relat_1 @ X58 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('65',plain,
    ( ( ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ sk_B @ sk_A ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['53','54'])).

thf('67',plain,
    ( ( ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ sk_B @ sk_A ) )
      = sk_A )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ sk_B @ sk_A ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['4','67'])).

thf('69',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ sk_B @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( ( k1_setfam_1 @ ( k2_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) )
      = sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['3','70'])).

thf('72',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( k1_setfam_1 @ ( k2_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) )
    = sk_A ),
    inference(demod,[status(thm)],['71','72'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('74',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('75',plain,(
    ! [X47: $i,X48: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X47 @ X48 ) )
      = ( k3_xboole_0 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('76',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k1_setfam_1 @ ( k2_tarski @ X7 @ X8 ) ) ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    = ( k5_xboole_0 @ sk_A @ sk_A ) ),
    inference('sup+',[status(thm)],['73','76'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('79',plain,(
    ! [X47: $i,X48: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X47 @ X48 ) )
      = ( k3_xboole_0 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k1_setfam_1 @ ( k2_tarski @ X7 @ X8 ) ) ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['5'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('84',plain,(
    ! [X4: $i,X6: $i] :
      ( ( ( k4_xboole_0 @ X4 @ X6 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['82','85'])).

thf('87',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['77','86'])).

thf('88',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( ( k4_xboole_0 @ X4 @ X5 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('89',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,(
    $false ),
    inference(demod,[status(thm)],['0','90'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yW6MZs4yTd
% 0.16/0.38  % Computer   : n011.cluster.edu
% 0.16/0.38  % Model      : x86_64 x86_64
% 0.16/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.38  % Memory     : 8042.1875MB
% 0.16/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.38  % CPULimit   : 60
% 0.16/0.38  % DateTime   : Tue Dec  1 16:03:27 EST 2020
% 0.16/0.38  % CPUTime    : 
% 0.16/0.38  % Running portfolio for 600 s
% 0.16/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.38  % Number of cores: 8
% 0.16/0.38  % Python version: Python 3.6.8
% 0.16/0.39  % Running in FO mode
% 1.10/1.31  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.10/1.31  % Solved by: fo/fo7.sh
% 1.10/1.31  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.10/1.31  % done 1201 iterations in 0.816s
% 1.10/1.31  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.10/1.31  % SZS output start Refutation
% 1.10/1.31  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.10/1.31  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.10/1.31  thf(sk_B_type, type, sk_B: $i).
% 1.10/1.31  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.10/1.31  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 1.10/1.31  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.10/1.31  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.10/1.31  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.10/1.31  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.10/1.31  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 1.10/1.31  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.10/1.31  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.10/1.31  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.10/1.31  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.10/1.31  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 1.10/1.31  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.10/1.31  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 1.10/1.31  thf(sk_A_type, type, sk_A: $i).
% 1.10/1.31  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.10/1.31  thf(t146_funct_1, conjecture,
% 1.10/1.31    (![A:$i,B:$i]:
% 1.10/1.31     ( ( v1_relat_1 @ B ) =>
% 1.10/1.31       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 1.10/1.31         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 1.10/1.31  thf(zf_stmt_0, negated_conjecture,
% 1.10/1.31    (~( ![A:$i,B:$i]:
% 1.10/1.31        ( ( v1_relat_1 @ B ) =>
% 1.10/1.31          ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 1.10/1.31            ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )),
% 1.10/1.31    inference('cnf.neg', [status(esa)], [t146_funct_1])).
% 1.10/1.31  thf('0', plain,
% 1.10/1.31      (~ (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 1.10/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.31  thf(t139_funct_1, axiom,
% 1.10/1.31    (![A:$i,B:$i,C:$i]:
% 1.10/1.31     ( ( v1_relat_1 @ C ) =>
% 1.10/1.31       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 1.10/1.31         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 1.10/1.31  thf('1', plain,
% 1.10/1.31      (![X70 : $i, X71 : $i, X72 : $i]:
% 1.10/1.31         (((k10_relat_1 @ (k7_relat_1 @ X71 @ X70) @ X72)
% 1.10/1.31            = (k3_xboole_0 @ X70 @ (k10_relat_1 @ X71 @ X72)))
% 1.10/1.31          | ~ (v1_relat_1 @ X71))),
% 1.10/1.31      inference('cnf', [status(esa)], [t139_funct_1])).
% 1.10/1.31  thf(t12_setfam_1, axiom,
% 1.10/1.31    (![A:$i,B:$i]:
% 1.10/1.31     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.10/1.31  thf('2', plain,
% 1.10/1.31      (![X47 : $i, X48 : $i]:
% 1.10/1.31         ((k1_setfam_1 @ (k2_tarski @ X47 @ X48)) = (k3_xboole_0 @ X47 @ X48))),
% 1.10/1.31      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.10/1.31  thf('3', plain,
% 1.10/1.31      (![X70 : $i, X71 : $i, X72 : $i]:
% 1.10/1.31         (((k10_relat_1 @ (k7_relat_1 @ X71 @ X70) @ X72)
% 1.10/1.31            = (k1_setfam_1 @ (k2_tarski @ X70 @ (k10_relat_1 @ X71 @ X72))))
% 1.10/1.31          | ~ (v1_relat_1 @ X71))),
% 1.10/1.31      inference('demod', [status(thm)], ['1', '2'])).
% 1.10/1.31  thf(dt_k7_relat_1, axiom,
% 1.10/1.31    (![A:$i,B:$i]:
% 1.10/1.31     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 1.10/1.31  thf('4', plain,
% 1.10/1.31      (![X50 : $i, X51 : $i]:
% 1.10/1.31         (~ (v1_relat_1 @ X50) | (v1_relat_1 @ (k7_relat_1 @ X50 @ X51)))),
% 1.10/1.31      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 1.10/1.31  thf(d10_xboole_0, axiom,
% 1.10/1.31    (![A:$i,B:$i]:
% 1.10/1.31     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.10/1.31  thf('5', plain,
% 1.10/1.31      (![X1 : $i, X2 : $i]: ((r1_tarski @ X1 @ X2) | ((X1) != (X2)))),
% 1.10/1.31      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.10/1.31  thf('6', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 1.10/1.31      inference('simplify', [status(thm)], ['5'])).
% 1.10/1.31  thf(t162_relat_1, axiom,
% 1.10/1.31    (![A:$i]:
% 1.10/1.31     ( ( v1_relat_1 @ A ) =>
% 1.10/1.31       ( ![B:$i,C:$i]:
% 1.10/1.31         ( ( r1_tarski @ B @ C ) =>
% 1.10/1.31           ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B ) =
% 1.10/1.31             ( k9_relat_1 @ A @ B ) ) ) ) ))).
% 1.10/1.31  thf('7', plain,
% 1.10/1.31      (![X53 : $i, X54 : $i, X55 : $i]:
% 1.10/1.31         (~ (r1_tarski @ X53 @ X54)
% 1.10/1.31          | ((k9_relat_1 @ (k7_relat_1 @ X55 @ X54) @ X53)
% 1.10/1.31              = (k9_relat_1 @ X55 @ X53))
% 1.10/1.31          | ~ (v1_relat_1 @ X55))),
% 1.10/1.31      inference('cnf', [status(esa)], [t162_relat_1])).
% 1.10/1.31  thf('8', plain,
% 1.10/1.31      (![X0 : $i, X1 : $i]:
% 1.10/1.31         (~ (v1_relat_1 @ X1)
% 1.10/1.31          | ((k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X0)
% 1.10/1.31              = (k9_relat_1 @ X1 @ X0)))),
% 1.10/1.31      inference('sup-', [status(thm)], ['6', '7'])).
% 1.10/1.31  thf('9', plain,
% 1.10/1.31      (![X50 : $i, X51 : $i]:
% 1.10/1.31         (~ (v1_relat_1 @ X50) | (v1_relat_1 @ (k7_relat_1 @ X50 @ X51)))),
% 1.10/1.31      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 1.10/1.31  thf(t94_relat_1, axiom,
% 1.10/1.31    (![A:$i,B:$i]:
% 1.10/1.31     ( ( v1_relat_1 @ B ) =>
% 1.10/1.31       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 1.10/1.31  thf('10', plain,
% 1.10/1.31      (![X68 : $i, X69 : $i]:
% 1.10/1.31         (((k7_relat_1 @ X69 @ X68) = (k5_relat_1 @ (k6_relat_1 @ X68) @ X69))
% 1.10/1.31          | ~ (v1_relat_1 @ X69))),
% 1.10/1.31      inference('cnf', [status(esa)], [t94_relat_1])).
% 1.10/1.31  thf(t182_relat_1, axiom,
% 1.10/1.31    (![A:$i]:
% 1.10/1.31     ( ( v1_relat_1 @ A ) =>
% 1.10/1.31       ( ![B:$i]:
% 1.10/1.31         ( ( v1_relat_1 @ B ) =>
% 1.10/1.31           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 1.10/1.31             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 1.10/1.31  thf('11', plain,
% 1.10/1.31      (![X62 : $i, X63 : $i]:
% 1.10/1.31         (~ (v1_relat_1 @ X62)
% 1.10/1.31          | ((k1_relat_1 @ (k5_relat_1 @ X63 @ X62))
% 1.10/1.31              = (k10_relat_1 @ X63 @ (k1_relat_1 @ X62)))
% 1.10/1.31          | ~ (v1_relat_1 @ X63))),
% 1.10/1.31      inference('cnf', [status(esa)], [t182_relat_1])).
% 1.10/1.31  thf('12', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 1.10/1.31      inference('simplify', [status(thm)], ['5'])).
% 1.10/1.31  thf('13', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 1.10/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.31  thf(t14_xboole_1, axiom,
% 1.10/1.31    (![A:$i,B:$i,C:$i]:
% 1.10/1.31     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) & 
% 1.10/1.31         ( ![D:$i]:
% 1.10/1.31           ( ( ( r1_tarski @ A @ D ) & ( r1_tarski @ C @ D ) ) =>
% 1.10/1.31             ( r1_tarski @ B @ D ) ) ) ) =>
% 1.10/1.31       ( ( B ) = ( k2_xboole_0 @ A @ C ) ) ))).
% 1.10/1.31  thf('14', plain,
% 1.10/1.31      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.10/1.31         (~ (r1_tarski @ X12 @ X13)
% 1.10/1.31          | ~ (r1_tarski @ X14 @ X13)
% 1.10/1.31          | (r1_tarski @ X14 @ (sk_D @ X14 @ X13 @ X12))
% 1.10/1.31          | ((X13) = (k2_xboole_0 @ X12 @ X14)))),
% 1.10/1.31      inference('cnf', [status(esa)], [t14_xboole_1])).
% 1.10/1.31  thf('15', plain,
% 1.10/1.31      (![X0 : $i]:
% 1.10/1.31         (((k1_relat_1 @ sk_B) = (k2_xboole_0 @ sk_A @ X0))
% 1.10/1.31          | (r1_tarski @ X0 @ (sk_D @ X0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 1.10/1.31          | ~ (r1_tarski @ X0 @ (k1_relat_1 @ sk_B)))),
% 1.10/1.31      inference('sup-', [status(thm)], ['13', '14'])).
% 1.10/1.31  thf('16', plain,
% 1.10/1.31      (((r1_tarski @ (k1_relat_1 @ sk_B) @ 
% 1.10/1.31         (sk_D @ (k1_relat_1 @ sk_B) @ (k1_relat_1 @ sk_B) @ sk_A))
% 1.10/1.31        | ((k1_relat_1 @ sk_B) = (k2_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B))))),
% 1.10/1.31      inference('sup-', [status(thm)], ['12', '15'])).
% 1.10/1.31  thf('17', plain,
% 1.10/1.31      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.10/1.31         (~ (r1_tarski @ X12 @ X13)
% 1.10/1.31          | ~ (r1_tarski @ X14 @ X13)
% 1.10/1.31          | ~ (r1_tarski @ X13 @ (sk_D @ X14 @ X13 @ X12))
% 1.10/1.31          | ((X13) = (k2_xboole_0 @ X12 @ X14)))),
% 1.10/1.31      inference('cnf', [status(esa)], [t14_xboole_1])).
% 1.10/1.31  thf('18', plain,
% 1.10/1.31      ((((k1_relat_1 @ sk_B) = (k2_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)))
% 1.10/1.31        | ((k1_relat_1 @ sk_B) = (k2_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)))
% 1.10/1.31        | ~ (r1_tarski @ (k1_relat_1 @ sk_B) @ (k1_relat_1 @ sk_B))
% 1.10/1.31        | ~ (r1_tarski @ sk_A @ (k1_relat_1 @ sk_B)))),
% 1.10/1.31      inference('sup-', [status(thm)], ['16', '17'])).
% 1.10/1.31  thf('19', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 1.10/1.31      inference('simplify', [status(thm)], ['5'])).
% 1.10/1.31  thf('20', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 1.10/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.31  thf('21', plain,
% 1.10/1.31      ((((k1_relat_1 @ sk_B) = (k2_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)))
% 1.10/1.31        | ((k1_relat_1 @ sk_B) = (k2_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B))))),
% 1.10/1.31      inference('demod', [status(thm)], ['18', '19', '20'])).
% 1.10/1.31  thf('22', plain,
% 1.10/1.31      (((k1_relat_1 @ sk_B) = (k2_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)))),
% 1.10/1.31      inference('simplify', [status(thm)], ['21'])).
% 1.10/1.31  thf(t71_relat_1, axiom,
% 1.10/1.31    (![A:$i]:
% 1.10/1.31     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 1.10/1.31       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 1.10/1.31  thf('23', plain, (![X65 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X65)) = (X65))),
% 1.10/1.31      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.10/1.31  thf(t169_relat_1, axiom,
% 1.10/1.31    (![A:$i]:
% 1.10/1.31     ( ( v1_relat_1 @ A ) =>
% 1.10/1.31       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 1.10/1.31  thf('24', plain,
% 1.10/1.31      (![X58 : $i]:
% 1.10/1.31         (((k10_relat_1 @ X58 @ (k2_relat_1 @ X58)) = (k1_relat_1 @ X58))
% 1.10/1.31          | ~ (v1_relat_1 @ X58))),
% 1.10/1.31      inference('cnf', [status(esa)], [t169_relat_1])).
% 1.10/1.31  thf('25', plain,
% 1.10/1.31      (![X0 : $i]:
% 1.10/1.31         (((k10_relat_1 @ (k6_relat_1 @ X0) @ X0)
% 1.10/1.31            = (k1_relat_1 @ (k6_relat_1 @ X0)))
% 1.10/1.31          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 1.10/1.31      inference('sup+', [status(thm)], ['23', '24'])).
% 1.10/1.31  thf('26', plain, (![X64 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X64)) = (X64))),
% 1.10/1.31      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.10/1.31  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 1.10/1.31  thf('27', plain, (![X49 : $i]: (v1_relat_1 @ (k6_relat_1 @ X49))),
% 1.10/1.31      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.10/1.31  thf('28', plain,
% 1.10/1.31      (![X0 : $i]: ((k10_relat_1 @ (k6_relat_1 @ X0) @ X0) = (X0))),
% 1.10/1.31      inference('demod', [status(thm)], ['25', '26', '27'])).
% 1.10/1.31  thf(t175_relat_1, axiom,
% 1.10/1.31    (![A:$i,B:$i,C:$i]:
% 1.10/1.31     ( ( v1_relat_1 @ C ) =>
% 1.10/1.31       ( ( k10_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) ) =
% 1.10/1.31         ( k2_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 1.10/1.31  thf('29', plain,
% 1.10/1.31      (![X59 : $i, X60 : $i, X61 : $i]:
% 1.10/1.31         (((k10_relat_1 @ X59 @ (k2_xboole_0 @ X60 @ X61))
% 1.10/1.31            = (k2_xboole_0 @ (k10_relat_1 @ X59 @ X60) @ 
% 1.10/1.31               (k10_relat_1 @ X59 @ X61)))
% 1.10/1.31          | ~ (v1_relat_1 @ X59))),
% 1.10/1.31      inference('cnf', [status(esa)], [t175_relat_1])).
% 1.10/1.31  thf('30', plain,
% 1.10/1.31      (![X0 : $i, X1 : $i]:
% 1.10/1.31         (((k10_relat_1 @ (k6_relat_1 @ X0) @ (k2_xboole_0 @ X0 @ X1))
% 1.10/1.31            = (k2_xboole_0 @ X0 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1)))
% 1.10/1.31          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 1.10/1.31      inference('sup+', [status(thm)], ['28', '29'])).
% 1.10/1.31  thf('31', plain, (![X64 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X64)) = (X64))),
% 1.10/1.31      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.10/1.31  thf(t167_relat_1, axiom,
% 1.10/1.31    (![A:$i,B:$i]:
% 1.10/1.31     ( ( v1_relat_1 @ B ) =>
% 1.10/1.31       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 1.10/1.31  thf('32', plain,
% 1.10/1.31      (![X56 : $i, X57 : $i]:
% 1.10/1.31         ((r1_tarski @ (k10_relat_1 @ X56 @ X57) @ (k1_relat_1 @ X56))
% 1.10/1.31          | ~ (v1_relat_1 @ X56))),
% 1.10/1.31      inference('cnf', [status(esa)], [t167_relat_1])).
% 1.10/1.31  thf('33', plain,
% 1.10/1.31      (![X0 : $i, X1 : $i]:
% 1.10/1.31         ((r1_tarski @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X0)
% 1.10/1.31          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 1.10/1.31      inference('sup+', [status(thm)], ['31', '32'])).
% 1.10/1.31  thf('34', plain, (![X49 : $i]: (v1_relat_1 @ (k6_relat_1 @ X49))),
% 1.10/1.31      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.10/1.31  thf('35', plain,
% 1.10/1.31      (![X0 : $i, X1 : $i]:
% 1.10/1.31         (r1_tarski @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X0)),
% 1.10/1.31      inference('demod', [status(thm)], ['33', '34'])).
% 1.10/1.31  thf('36', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 1.10/1.31      inference('simplify', [status(thm)], ['5'])).
% 1.10/1.31  thf(t8_xboole_1, axiom,
% 1.10/1.31    (![A:$i,B:$i,C:$i]:
% 1.10/1.31     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 1.10/1.31       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 1.10/1.31  thf('37', plain,
% 1.10/1.31      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.10/1.31         (~ (r1_tarski @ X17 @ X18)
% 1.10/1.31          | ~ (r1_tarski @ X19 @ X18)
% 1.10/1.31          | (r1_tarski @ (k2_xboole_0 @ X17 @ X19) @ X18))),
% 1.10/1.31      inference('cnf', [status(esa)], [t8_xboole_1])).
% 1.10/1.31  thf('38', plain,
% 1.10/1.31      (![X0 : $i, X1 : $i]:
% 1.10/1.31         ((r1_tarski @ (k2_xboole_0 @ X0 @ X1) @ X0) | ~ (r1_tarski @ X1 @ X0))),
% 1.10/1.31      inference('sup-', [status(thm)], ['36', '37'])).
% 1.10/1.31  thf('39', plain,
% 1.10/1.31      (![X0 : $i, X1 : $i]:
% 1.10/1.31         (r1_tarski @ 
% 1.10/1.31          (k2_xboole_0 @ X0 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1)) @ X0)),
% 1.10/1.31      inference('sup-', [status(thm)], ['35', '38'])).
% 1.10/1.31  thf('40', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 1.10/1.31      inference('simplify', [status(thm)], ['5'])).
% 1.10/1.31  thf(t11_xboole_1, axiom,
% 1.10/1.31    (![A:$i,B:$i,C:$i]:
% 1.10/1.31     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 1.10/1.31  thf('41', plain,
% 1.10/1.31      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.10/1.31         ((r1_tarski @ X9 @ X10)
% 1.10/1.31          | ~ (r1_tarski @ (k2_xboole_0 @ X9 @ X11) @ X10))),
% 1.10/1.31      inference('cnf', [status(esa)], [t11_xboole_1])).
% 1.10/1.31  thf('42', plain,
% 1.10/1.31      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 1.10/1.31      inference('sup-', [status(thm)], ['40', '41'])).
% 1.10/1.31  thf('43', plain,
% 1.10/1.31      (![X1 : $i, X3 : $i]:
% 1.10/1.31         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 1.10/1.31      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.10/1.31  thf('44', plain,
% 1.10/1.31      (![X0 : $i, X1 : $i]:
% 1.10/1.31         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 1.10/1.31          | ((k2_xboole_0 @ X1 @ X0) = (X1)))),
% 1.10/1.31      inference('sup-', [status(thm)], ['42', '43'])).
% 1.10/1.31  thf('45', plain,
% 1.10/1.31      (![X0 : $i, X1 : $i]:
% 1.10/1.31         ((k2_xboole_0 @ X0 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1)) = (X0))),
% 1.10/1.31      inference('sup-', [status(thm)], ['39', '44'])).
% 1.10/1.31  thf('46', plain, (![X49 : $i]: (v1_relat_1 @ (k6_relat_1 @ X49))),
% 1.10/1.31      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.10/1.31  thf('47', plain,
% 1.10/1.31      (![X0 : $i, X1 : $i]:
% 1.10/1.31         ((k10_relat_1 @ (k6_relat_1 @ X0) @ (k2_xboole_0 @ X0 @ X1)) = (X0))),
% 1.10/1.31      inference('demod', [status(thm)], ['30', '45', '46'])).
% 1.10/1.31  thf('48', plain,
% 1.10/1.31      (((k10_relat_1 @ (k6_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B)) = (sk_A))),
% 1.10/1.31      inference('sup+', [status(thm)], ['22', '47'])).
% 1.10/1.31  thf('49', plain,
% 1.10/1.31      ((((k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)) = (sk_A))
% 1.10/1.31        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A))
% 1.10/1.31        | ~ (v1_relat_1 @ sk_B))),
% 1.10/1.31      inference('sup+', [status(thm)], ['11', '48'])).
% 1.10/1.31  thf('50', plain, (![X49 : $i]: (v1_relat_1 @ (k6_relat_1 @ X49))),
% 1.10/1.31      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.10/1.31  thf('51', plain, ((v1_relat_1 @ sk_B)),
% 1.10/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.31  thf('52', plain,
% 1.10/1.31      (((k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)) = (sk_A))),
% 1.10/1.31      inference('demod', [status(thm)], ['49', '50', '51'])).
% 1.10/1.31  thf('53', plain,
% 1.10/1.31      ((((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) = (sk_A))
% 1.10/1.31        | ~ (v1_relat_1 @ sk_B))),
% 1.10/1.31      inference('sup+', [status(thm)], ['10', '52'])).
% 1.10/1.31  thf('54', plain, ((v1_relat_1 @ sk_B)),
% 1.10/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.31  thf('55', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) = (sk_A))),
% 1.10/1.31      inference('demod', [status(thm)], ['53', '54'])).
% 1.10/1.31  thf(t146_relat_1, axiom,
% 1.10/1.31    (![A:$i]:
% 1.10/1.31     ( ( v1_relat_1 @ A ) =>
% 1.10/1.31       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 1.10/1.31  thf('56', plain,
% 1.10/1.31      (![X52 : $i]:
% 1.10/1.31         (((k9_relat_1 @ X52 @ (k1_relat_1 @ X52)) = (k2_relat_1 @ X52))
% 1.10/1.31          | ~ (v1_relat_1 @ X52))),
% 1.10/1.31      inference('cnf', [status(esa)], [t146_relat_1])).
% 1.10/1.31  thf('57', plain,
% 1.10/1.31      ((((k9_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ sk_A)
% 1.10/1.31          = (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 1.10/1.31        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 1.10/1.31      inference('sup+', [status(thm)], ['55', '56'])).
% 1.10/1.31  thf('58', plain,
% 1.10/1.31      ((~ (v1_relat_1 @ sk_B)
% 1.10/1.31        | ((k9_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ sk_A)
% 1.10/1.31            = (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))))),
% 1.10/1.31      inference('sup-', [status(thm)], ['9', '57'])).
% 1.10/1.31  thf('59', plain, ((v1_relat_1 @ sk_B)),
% 1.10/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.31  thf('60', plain,
% 1.10/1.31      (((k9_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ sk_A)
% 1.10/1.31         = (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 1.10/1.31      inference('demod', [status(thm)], ['58', '59'])).
% 1.10/1.31  thf('61', plain,
% 1.10/1.31      ((((k9_relat_1 @ sk_B @ sk_A) = (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 1.10/1.31        | ~ (v1_relat_1 @ sk_B))),
% 1.10/1.31      inference('sup+', [status(thm)], ['8', '60'])).
% 1.10/1.31  thf('62', plain, ((v1_relat_1 @ sk_B)),
% 1.10/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.31  thf('63', plain,
% 1.10/1.31      (((k9_relat_1 @ sk_B @ sk_A) = (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 1.10/1.31      inference('demod', [status(thm)], ['61', '62'])).
% 1.10/1.31  thf('64', plain,
% 1.10/1.31      (![X58 : $i]:
% 1.10/1.31         (((k10_relat_1 @ X58 @ (k2_relat_1 @ X58)) = (k1_relat_1 @ X58))
% 1.10/1.31          | ~ (v1_relat_1 @ X58))),
% 1.10/1.31      inference('cnf', [status(esa)], [t169_relat_1])).
% 1.10/1.31  thf('65', plain,
% 1.10/1.31      ((((k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ (k9_relat_1 @ sk_B @ sk_A))
% 1.10/1.31          = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 1.10/1.31        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 1.10/1.31      inference('sup+', [status(thm)], ['63', '64'])).
% 1.10/1.31  thf('66', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) = (sk_A))),
% 1.10/1.31      inference('demod', [status(thm)], ['53', '54'])).
% 1.10/1.31  thf('67', plain,
% 1.10/1.31      ((((k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ (k9_relat_1 @ sk_B @ sk_A))
% 1.10/1.31          = (sk_A))
% 1.10/1.31        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 1.10/1.31      inference('demod', [status(thm)], ['65', '66'])).
% 1.10/1.31  thf('68', plain,
% 1.10/1.31      ((~ (v1_relat_1 @ sk_B)
% 1.10/1.31        | ((k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ 
% 1.10/1.31            (k9_relat_1 @ sk_B @ sk_A)) = (sk_A)))),
% 1.10/1.31      inference('sup-', [status(thm)], ['4', '67'])).
% 1.10/1.31  thf('69', plain, ((v1_relat_1 @ sk_B)),
% 1.10/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.31  thf('70', plain,
% 1.10/1.31      (((k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ (k9_relat_1 @ sk_B @ sk_A))
% 1.10/1.31         = (sk_A))),
% 1.10/1.31      inference('demod', [status(thm)], ['68', '69'])).
% 1.10/1.31  thf('71', plain,
% 1.10/1.31      ((((k1_setfam_1 @ 
% 1.10/1.31          (k2_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A))))
% 1.10/1.31          = (sk_A))
% 1.10/1.31        | ~ (v1_relat_1 @ sk_B))),
% 1.10/1.31      inference('sup+', [status(thm)], ['3', '70'])).
% 1.10/1.31  thf('72', plain, ((v1_relat_1 @ sk_B)),
% 1.10/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.31  thf('73', plain,
% 1.10/1.31      (((k1_setfam_1 @ 
% 1.10/1.31         (k2_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A))))
% 1.10/1.31         = (sk_A))),
% 1.10/1.31      inference('demod', [status(thm)], ['71', '72'])).
% 1.10/1.31  thf(t100_xboole_1, axiom,
% 1.10/1.31    (![A:$i,B:$i]:
% 1.10/1.31     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.10/1.31  thf('74', plain,
% 1.10/1.31      (![X7 : $i, X8 : $i]:
% 1.10/1.31         ((k4_xboole_0 @ X7 @ X8)
% 1.10/1.31           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 1.10/1.31      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.10/1.31  thf('75', plain,
% 1.10/1.31      (![X47 : $i, X48 : $i]:
% 1.10/1.31         ((k1_setfam_1 @ (k2_tarski @ X47 @ X48)) = (k3_xboole_0 @ X47 @ X48))),
% 1.10/1.31      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.10/1.31  thf('76', plain,
% 1.10/1.31      (![X7 : $i, X8 : $i]:
% 1.10/1.31         ((k4_xboole_0 @ X7 @ X8)
% 1.10/1.31           = (k5_xboole_0 @ X7 @ (k1_setfam_1 @ (k2_tarski @ X7 @ X8))))),
% 1.10/1.31      inference('demod', [status(thm)], ['74', '75'])).
% 1.10/1.31  thf('77', plain,
% 1.10/1.31      (((k4_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 1.10/1.31         = (k5_xboole_0 @ sk_A @ sk_A))),
% 1.10/1.31      inference('sup+', [status(thm)], ['73', '76'])).
% 1.10/1.31  thf(idempotence_k3_xboole_0, axiom,
% 1.10/1.31    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 1.10/1.31  thf('78', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 1.10/1.31      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 1.10/1.31  thf('79', plain,
% 1.10/1.31      (![X47 : $i, X48 : $i]:
% 1.10/1.31         ((k1_setfam_1 @ (k2_tarski @ X47 @ X48)) = (k3_xboole_0 @ X47 @ X48))),
% 1.10/1.31      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.10/1.31  thf('80', plain,
% 1.10/1.31      (![X0 : $i]: ((k1_setfam_1 @ (k2_tarski @ X0 @ X0)) = (X0))),
% 1.10/1.31      inference('demod', [status(thm)], ['78', '79'])).
% 1.10/1.31  thf('81', plain,
% 1.10/1.31      (![X7 : $i, X8 : $i]:
% 1.10/1.31         ((k4_xboole_0 @ X7 @ X8)
% 1.10/1.31           = (k5_xboole_0 @ X7 @ (k1_setfam_1 @ (k2_tarski @ X7 @ X8))))),
% 1.10/1.31      inference('demod', [status(thm)], ['74', '75'])).
% 1.10/1.31  thf('82', plain,
% 1.10/1.31      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.10/1.31      inference('sup+', [status(thm)], ['80', '81'])).
% 1.10/1.31  thf('83', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 1.10/1.31      inference('simplify', [status(thm)], ['5'])).
% 1.10/1.31  thf(l32_xboole_1, axiom,
% 1.10/1.31    (![A:$i,B:$i]:
% 1.10/1.31     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.10/1.31  thf('84', plain,
% 1.10/1.31      (![X4 : $i, X6 : $i]:
% 1.10/1.31         (((k4_xboole_0 @ X4 @ X6) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ X6))),
% 1.10/1.31      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.10/1.31  thf('85', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.10/1.31      inference('sup-', [status(thm)], ['83', '84'])).
% 1.10/1.31  thf('86', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.10/1.31      inference('sup+', [status(thm)], ['82', '85'])).
% 1.10/1.31  thf('87', plain,
% 1.10/1.31      (((k4_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 1.10/1.31         = (k1_xboole_0))),
% 1.10/1.31      inference('demod', [status(thm)], ['77', '86'])).
% 1.10/1.31  thf('88', plain,
% 1.10/1.31      (![X4 : $i, X5 : $i]:
% 1.10/1.31         ((r1_tarski @ X4 @ X5) | ((k4_xboole_0 @ X4 @ X5) != (k1_xboole_0)))),
% 1.10/1.31      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.10/1.31  thf('89', plain,
% 1.10/1.31      ((((k1_xboole_0) != (k1_xboole_0))
% 1.10/1.31        | (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A))))),
% 1.10/1.31      inference('sup-', [status(thm)], ['87', '88'])).
% 1.10/1.31  thf('90', plain,
% 1.10/1.31      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 1.10/1.31      inference('simplify', [status(thm)], ['89'])).
% 1.10/1.31  thf('91', plain, ($false), inference('demod', [status(thm)], ['0', '90'])).
% 1.10/1.31  
% 1.10/1.31  % SZS output end Refutation
% 1.10/1.31  
% 1.10/1.32  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
