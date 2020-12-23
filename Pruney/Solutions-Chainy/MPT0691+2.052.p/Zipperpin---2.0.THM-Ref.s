%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Ewdc5ihyW2

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:25 EST 2020

% Result     : Theorem 0.91s
% Output     : Refutation 0.91s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 217 expanded)
%              Number of leaves         :   37 (  81 expanded)
%              Depth                    :   28
%              Number of atoms          :  868 (1719 expanded)
%              Number of equality atoms :   72 ( 129 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

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
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('6',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
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

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('12',plain,(
    ! [X65: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X65 ) )
      = X65 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('13',plain,(
    ! [X58: $i] :
      ( ( ( k10_relat_1 @ X58 @ ( k2_relat_1 @ X58 ) )
        = ( k1_relat_1 @ X58 ) )
      | ~ ( v1_relat_1 @ X58 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
        = ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X64: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X64 ) )
      = X64 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('16',plain,(
    ! [X49: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['5'])).

thf('19',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('20',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_xboole_0 @ X12 @ X11 )
        = X11 )
      | ~ ( r1_tarski @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('21',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(t175_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) )
        = ( k2_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('22',plain,(
    ! [X59: $i,X60: $i,X61: $i] :
      ( ( ( k10_relat_1 @ X59 @ ( k2_xboole_0 @ X60 @ X61 ) )
        = ( k2_xboole_0 @ ( k10_relat_1 @ X59 @ X60 ) @ ( k10_relat_1 @ X59 @ X61 ) ) )
      | ~ ( v1_relat_1 @ X59 ) ) ),
    inference(cnf,[status(esa)],[t175_relat_1])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('23',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X8 @ X10 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ ( k10_relat_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X3 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k10_relat_1 @ X2 @ X1 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k1_relat_1 @ sk_B ) ) @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ X1 @ sk_A ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ X0 @ sk_A ) @ ( k10_relat_1 @ X0 @ ( k1_relat_1 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['18','25'])).

thf('27',plain,
    ( ( r1_tarski @ sk_A @ ( k10_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['17','26'])).

thf('28',plain,(
    ! [X49: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('29',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X64: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X64 ) )
      = X64 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('31',plain,(
    ! [X56: $i,X57: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X56 @ X57 ) @ ( k1_relat_1 @ X56 ) )
      | ~ ( v1_relat_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('32',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ X1 ) )
      | ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ( ( k1_relat_1 @ ( k6_relat_1 @ X0 ) )
        = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X64: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X64 ) )
      = X64 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('36',plain,(
    ! [X49: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ( X0
        = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,
    ( sk_A
    = ( k10_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['29','37'])).

thf('39',plain,
    ( ( sk_A
      = ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['11','38'])).

thf('40',plain,(
    ! [X49: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('41',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( sk_A
    = ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,
    ( ( sk_A
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['10','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( sk_A
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('46',plain,(
    ! [X52: $i] :
      ( ( ( k9_relat_1 @ X52 @ ( k1_relat_1 @ X52 ) )
        = ( k2_relat_1 @ X52 ) )
      | ~ ( v1_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('47',plain,
    ( ( ( k9_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ sk_A )
      = ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( k9_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ sk_A )
      = ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['9','47'])).

thf('49',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( k9_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ sk_A )
    = ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( ( k9_relat_1 @ sk_B @ sk_A )
      = ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['8','50'])).

thf('52',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( k9_relat_1 @ sk_B @ sk_A )
    = ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X58: $i] :
      ( ( ( k10_relat_1 @ X58 @ ( k2_relat_1 @ X58 ) )
        = ( k1_relat_1 @ X58 ) )
      | ~ ( v1_relat_1 @ X58 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('55',plain,
    ( ( ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ sk_B @ sk_A ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,
    ( sk_A
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('57',plain,
    ( ( ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ sk_B @ sk_A ) )
      = sk_A )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ sk_B @ sk_A ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['4','57'])).

thf('59',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ sk_B @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( ( k1_setfam_1 @ ( k2_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) )
      = sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['3','60'])).

thf('62',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( k1_setfam_1 @ ( k2_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) )
    = sk_A ),
    inference(demod,[status(thm)],['61','62'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('64',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('65',plain,(
    ! [X47: $i,X48: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X47 @ X48 ) )
      = ( k3_xboole_0 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('66',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k1_setfam_1 @ ( k2_tarski @ X6 @ X7 ) ) ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    = ( k5_xboole_0 @ sk_A @ sk_A ) ),
    inference('sup+',[status(thm)],['63','66'])).

thf('68',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['5'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('69',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_xboole_0 @ X16 @ X17 )
        = X16 )
      | ~ ( r1_tarski @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('70',plain,(
    ! [X47: $i,X48: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X47 @ X48 ) )
      = ( k3_xboole_0 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('71',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X16 @ X17 ) )
        = X16 )
      | ~ ( r1_tarski @ X16 @ X17 ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['68','71'])).

thf('73',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k1_setfam_1 @ ( k2_tarski @ X6 @ X7 ) ) ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['5'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('76',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['74','77'])).

thf('79',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['67','78'])).

thf('80',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k4_xboole_0 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('81',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    $false ),
    inference(demod,[status(thm)],['0','82'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Ewdc5ihyW2
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:53:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.91/1.08  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.91/1.08  % Solved by: fo/fo7.sh
% 0.91/1.08  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.91/1.08  % done 1074 iterations in 0.636s
% 0.91/1.08  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.91/1.08  % SZS output start Refutation
% 0.91/1.08  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.91/1.08  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.91/1.08  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.91/1.08  thf(sk_B_type, type, sk_B: $i).
% 0.91/1.08  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.91/1.08  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.91/1.08  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.91/1.08  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.91/1.08  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.91/1.08  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.91/1.08  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.91/1.08  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.91/1.08  thf(sk_A_type, type, sk_A: $i).
% 0.91/1.08  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.91/1.08  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.91/1.08  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.91/1.08  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.91/1.08  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.91/1.08  thf(t146_funct_1, conjecture,
% 0.91/1.08    (![A:$i,B:$i]:
% 0.91/1.08     ( ( v1_relat_1 @ B ) =>
% 0.91/1.08       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.91/1.08         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 0.91/1.08  thf(zf_stmt_0, negated_conjecture,
% 0.91/1.08    (~( ![A:$i,B:$i]:
% 0.91/1.08        ( ( v1_relat_1 @ B ) =>
% 0.91/1.08          ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.91/1.08            ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )),
% 0.91/1.08    inference('cnf.neg', [status(esa)], [t146_funct_1])).
% 0.91/1.08  thf('0', plain,
% 0.91/1.08      (~ (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 0.91/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.08  thf(t139_funct_1, axiom,
% 0.91/1.08    (![A:$i,B:$i,C:$i]:
% 0.91/1.08     ( ( v1_relat_1 @ C ) =>
% 0.91/1.08       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.91/1.08         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.91/1.08  thf('1', plain,
% 0.91/1.08      (![X70 : $i, X71 : $i, X72 : $i]:
% 0.91/1.08         (((k10_relat_1 @ (k7_relat_1 @ X71 @ X70) @ X72)
% 0.91/1.08            = (k3_xboole_0 @ X70 @ (k10_relat_1 @ X71 @ X72)))
% 0.91/1.08          | ~ (v1_relat_1 @ X71))),
% 0.91/1.08      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.91/1.08  thf(t12_setfam_1, axiom,
% 0.91/1.08    (![A:$i,B:$i]:
% 0.91/1.08     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.91/1.08  thf('2', plain,
% 0.91/1.08      (![X47 : $i, X48 : $i]:
% 0.91/1.08         ((k1_setfam_1 @ (k2_tarski @ X47 @ X48)) = (k3_xboole_0 @ X47 @ X48))),
% 0.91/1.08      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.91/1.08  thf('3', plain,
% 0.91/1.08      (![X70 : $i, X71 : $i, X72 : $i]:
% 0.91/1.08         (((k10_relat_1 @ (k7_relat_1 @ X71 @ X70) @ X72)
% 0.91/1.08            = (k1_setfam_1 @ (k2_tarski @ X70 @ (k10_relat_1 @ X71 @ X72))))
% 0.91/1.08          | ~ (v1_relat_1 @ X71))),
% 0.91/1.08      inference('demod', [status(thm)], ['1', '2'])).
% 0.91/1.08  thf(dt_k7_relat_1, axiom,
% 0.91/1.08    (![A:$i,B:$i]:
% 0.91/1.08     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.91/1.08  thf('4', plain,
% 0.91/1.08      (![X50 : $i, X51 : $i]:
% 0.91/1.08         (~ (v1_relat_1 @ X50) | (v1_relat_1 @ (k7_relat_1 @ X50 @ X51)))),
% 0.91/1.08      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.91/1.08  thf(d10_xboole_0, axiom,
% 0.91/1.08    (![A:$i,B:$i]:
% 0.91/1.08     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.91/1.08  thf('5', plain,
% 0.91/1.08      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.91/1.08      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.91/1.08  thf('6', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.91/1.08      inference('simplify', [status(thm)], ['5'])).
% 0.91/1.08  thf(t162_relat_1, axiom,
% 0.91/1.08    (![A:$i]:
% 0.91/1.08     ( ( v1_relat_1 @ A ) =>
% 0.91/1.08       ( ![B:$i,C:$i]:
% 0.91/1.08         ( ( r1_tarski @ B @ C ) =>
% 0.91/1.08           ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B ) =
% 0.91/1.08             ( k9_relat_1 @ A @ B ) ) ) ) ))).
% 0.91/1.08  thf('7', plain,
% 0.91/1.08      (![X53 : $i, X54 : $i, X55 : $i]:
% 0.91/1.08         (~ (r1_tarski @ X53 @ X54)
% 0.91/1.08          | ((k9_relat_1 @ (k7_relat_1 @ X55 @ X54) @ X53)
% 0.91/1.08              = (k9_relat_1 @ X55 @ X53))
% 0.91/1.08          | ~ (v1_relat_1 @ X55))),
% 0.91/1.08      inference('cnf', [status(esa)], [t162_relat_1])).
% 0.91/1.08  thf('8', plain,
% 0.91/1.08      (![X0 : $i, X1 : $i]:
% 0.91/1.08         (~ (v1_relat_1 @ X1)
% 0.91/1.08          | ((k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X0)
% 0.91/1.08              = (k9_relat_1 @ X1 @ X0)))),
% 0.91/1.08      inference('sup-', [status(thm)], ['6', '7'])).
% 0.91/1.08  thf('9', plain,
% 0.91/1.08      (![X50 : $i, X51 : $i]:
% 0.91/1.08         (~ (v1_relat_1 @ X50) | (v1_relat_1 @ (k7_relat_1 @ X50 @ X51)))),
% 0.91/1.08      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.91/1.08  thf(t94_relat_1, axiom,
% 0.91/1.08    (![A:$i,B:$i]:
% 0.91/1.08     ( ( v1_relat_1 @ B ) =>
% 0.91/1.08       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.91/1.08  thf('10', plain,
% 0.91/1.08      (![X68 : $i, X69 : $i]:
% 0.91/1.08         (((k7_relat_1 @ X69 @ X68) = (k5_relat_1 @ (k6_relat_1 @ X68) @ X69))
% 0.91/1.08          | ~ (v1_relat_1 @ X69))),
% 0.91/1.08      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.91/1.08  thf(t182_relat_1, axiom,
% 0.91/1.08    (![A:$i]:
% 0.91/1.08     ( ( v1_relat_1 @ A ) =>
% 0.91/1.08       ( ![B:$i]:
% 0.91/1.08         ( ( v1_relat_1 @ B ) =>
% 0.91/1.08           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.91/1.08             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.91/1.08  thf('11', plain,
% 0.91/1.08      (![X62 : $i, X63 : $i]:
% 0.91/1.08         (~ (v1_relat_1 @ X62)
% 0.91/1.08          | ((k1_relat_1 @ (k5_relat_1 @ X63 @ X62))
% 0.91/1.08              = (k10_relat_1 @ X63 @ (k1_relat_1 @ X62)))
% 0.91/1.08          | ~ (v1_relat_1 @ X63))),
% 0.91/1.08      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.91/1.08  thf(t71_relat_1, axiom,
% 0.91/1.08    (![A:$i]:
% 0.91/1.08     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.91/1.08       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.91/1.08  thf('12', plain, (![X65 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X65)) = (X65))),
% 0.91/1.08      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.91/1.08  thf(t169_relat_1, axiom,
% 0.91/1.08    (![A:$i]:
% 0.91/1.08     ( ( v1_relat_1 @ A ) =>
% 0.91/1.08       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.91/1.08  thf('13', plain,
% 0.91/1.08      (![X58 : $i]:
% 0.91/1.08         (((k10_relat_1 @ X58 @ (k2_relat_1 @ X58)) = (k1_relat_1 @ X58))
% 0.91/1.08          | ~ (v1_relat_1 @ X58))),
% 0.91/1.08      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.91/1.08  thf('14', plain,
% 0.91/1.08      (![X0 : $i]:
% 0.91/1.08         (((k10_relat_1 @ (k6_relat_1 @ X0) @ X0)
% 0.91/1.08            = (k1_relat_1 @ (k6_relat_1 @ X0)))
% 0.91/1.08          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.91/1.08      inference('sup+', [status(thm)], ['12', '13'])).
% 0.91/1.08  thf('15', plain, (![X64 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X64)) = (X64))),
% 0.91/1.08      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.91/1.08  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.91/1.08  thf('16', plain, (![X49 : $i]: (v1_relat_1 @ (k6_relat_1 @ X49))),
% 0.91/1.08      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.91/1.08  thf('17', plain,
% 0.91/1.08      (![X0 : $i]: ((k10_relat_1 @ (k6_relat_1 @ X0) @ X0) = (X0))),
% 0.91/1.08      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.91/1.08  thf('18', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.91/1.08      inference('simplify', [status(thm)], ['5'])).
% 0.91/1.08  thf('19', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.91/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.08  thf(t12_xboole_1, axiom,
% 0.91/1.08    (![A:$i,B:$i]:
% 0.91/1.08     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.91/1.08  thf('20', plain,
% 0.91/1.08      (![X11 : $i, X12 : $i]:
% 0.91/1.08         (((k2_xboole_0 @ X12 @ X11) = (X11)) | ~ (r1_tarski @ X12 @ X11))),
% 0.91/1.08      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.91/1.08  thf('21', plain,
% 0.91/1.08      (((k2_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)) = (k1_relat_1 @ sk_B))),
% 0.91/1.08      inference('sup-', [status(thm)], ['19', '20'])).
% 0.91/1.08  thf(t175_relat_1, axiom,
% 0.91/1.08    (![A:$i,B:$i,C:$i]:
% 0.91/1.08     ( ( v1_relat_1 @ C ) =>
% 0.91/1.08       ( ( k10_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) ) =
% 0.91/1.08         ( k2_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.91/1.08  thf('22', plain,
% 0.91/1.08      (![X59 : $i, X60 : $i, X61 : $i]:
% 0.91/1.08         (((k10_relat_1 @ X59 @ (k2_xboole_0 @ X60 @ X61))
% 0.91/1.08            = (k2_xboole_0 @ (k10_relat_1 @ X59 @ X60) @ 
% 0.91/1.08               (k10_relat_1 @ X59 @ X61)))
% 0.91/1.08          | ~ (v1_relat_1 @ X59))),
% 0.91/1.08      inference('cnf', [status(esa)], [t175_relat_1])).
% 0.91/1.08  thf(t11_xboole_1, axiom,
% 0.91/1.08    (![A:$i,B:$i,C:$i]:
% 0.91/1.08     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.91/1.08  thf('23', plain,
% 0.91/1.08      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.91/1.08         ((r1_tarski @ X8 @ X9) | ~ (r1_tarski @ (k2_xboole_0 @ X8 @ X10) @ X9))),
% 0.91/1.08      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.91/1.08  thf('24', plain,
% 0.91/1.08      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.91/1.08         (~ (r1_tarski @ (k10_relat_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X3)
% 0.91/1.08          | ~ (v1_relat_1 @ X2)
% 0.91/1.08          | (r1_tarski @ (k10_relat_1 @ X2 @ X1) @ X3))),
% 0.91/1.08      inference('sup-', [status(thm)], ['22', '23'])).
% 0.91/1.08  thf('25', plain,
% 0.91/1.08      (![X0 : $i, X1 : $i]:
% 0.91/1.08         (~ (r1_tarski @ (k10_relat_1 @ X1 @ (k1_relat_1 @ sk_B)) @ X0)
% 0.91/1.08          | (r1_tarski @ (k10_relat_1 @ X1 @ sk_A) @ X0)
% 0.91/1.08          | ~ (v1_relat_1 @ X1))),
% 0.91/1.08      inference('sup-', [status(thm)], ['21', '24'])).
% 0.91/1.08  thf('26', plain,
% 0.91/1.08      (![X0 : $i]:
% 0.91/1.08         (~ (v1_relat_1 @ X0)
% 0.91/1.08          | (r1_tarski @ (k10_relat_1 @ X0 @ sk_A) @ 
% 0.91/1.08             (k10_relat_1 @ X0 @ (k1_relat_1 @ sk_B))))),
% 0.91/1.08      inference('sup-', [status(thm)], ['18', '25'])).
% 0.91/1.08  thf('27', plain,
% 0.91/1.08      (((r1_tarski @ sk_A @ 
% 0.91/1.08         (k10_relat_1 @ (k6_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B)))
% 0.91/1.08        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A)))),
% 0.91/1.08      inference('sup+', [status(thm)], ['17', '26'])).
% 0.91/1.08  thf('28', plain, (![X49 : $i]: (v1_relat_1 @ (k6_relat_1 @ X49))),
% 0.91/1.08      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.91/1.08  thf('29', plain,
% 0.91/1.08      ((r1_tarski @ sk_A @ 
% 0.91/1.08        (k10_relat_1 @ (k6_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B)))),
% 0.91/1.08      inference('demod', [status(thm)], ['27', '28'])).
% 0.91/1.08  thf('30', plain, (![X64 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X64)) = (X64))),
% 0.91/1.08      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.91/1.08  thf(t167_relat_1, axiom,
% 0.91/1.08    (![A:$i,B:$i]:
% 0.91/1.08     ( ( v1_relat_1 @ B ) =>
% 0.91/1.08       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 0.91/1.08  thf('31', plain,
% 0.91/1.08      (![X56 : $i, X57 : $i]:
% 0.91/1.08         ((r1_tarski @ (k10_relat_1 @ X56 @ X57) @ (k1_relat_1 @ X56))
% 0.91/1.08          | ~ (v1_relat_1 @ X56))),
% 0.91/1.08      inference('cnf', [status(esa)], [t167_relat_1])).
% 0.91/1.08  thf('32', plain,
% 0.91/1.08      (![X0 : $i, X2 : $i]:
% 0.91/1.08         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.91/1.08      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.91/1.08  thf('33', plain,
% 0.91/1.08      (![X0 : $i, X1 : $i]:
% 0.91/1.08         (~ (v1_relat_1 @ X0)
% 0.91/1.08          | ~ (r1_tarski @ (k1_relat_1 @ X0) @ (k10_relat_1 @ X0 @ X1))
% 0.91/1.08          | ((k1_relat_1 @ X0) = (k10_relat_1 @ X0 @ X1)))),
% 0.91/1.08      inference('sup-', [status(thm)], ['31', '32'])).
% 0.91/1.08  thf('34', plain,
% 0.91/1.08      (![X0 : $i, X1 : $i]:
% 0.91/1.08         (~ (r1_tarski @ X0 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.91/1.08          | ((k1_relat_1 @ (k6_relat_1 @ X0))
% 0.91/1.08              = (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.91/1.08          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.91/1.08      inference('sup-', [status(thm)], ['30', '33'])).
% 0.91/1.08  thf('35', plain, (![X64 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X64)) = (X64))),
% 0.91/1.08      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.91/1.08  thf('36', plain, (![X49 : $i]: (v1_relat_1 @ (k6_relat_1 @ X49))),
% 0.91/1.08      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.91/1.08  thf('37', plain,
% 0.91/1.08      (![X0 : $i, X1 : $i]:
% 0.91/1.08         (~ (r1_tarski @ X0 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.91/1.08          | ((X0) = (k10_relat_1 @ (k6_relat_1 @ X0) @ X1)))),
% 0.91/1.08      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.91/1.08  thf('38', plain,
% 0.91/1.08      (((sk_A) = (k10_relat_1 @ (k6_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B)))),
% 0.91/1.08      inference('sup-', [status(thm)], ['29', '37'])).
% 0.91/1.08  thf('39', plain,
% 0.91/1.08      ((((sk_A) = (k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)))
% 0.91/1.08        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A))
% 0.91/1.08        | ~ (v1_relat_1 @ sk_B))),
% 0.91/1.08      inference('sup+', [status(thm)], ['11', '38'])).
% 0.91/1.08  thf('40', plain, (![X49 : $i]: (v1_relat_1 @ (k6_relat_1 @ X49))),
% 0.91/1.08      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.91/1.08  thf('41', plain, ((v1_relat_1 @ sk_B)),
% 0.91/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.08  thf('42', plain,
% 0.91/1.08      (((sk_A) = (k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)))),
% 0.91/1.08      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.91/1.08  thf('43', plain,
% 0.91/1.08      ((((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.91/1.08        | ~ (v1_relat_1 @ sk_B))),
% 0.91/1.08      inference('sup+', [status(thm)], ['10', '42'])).
% 0.91/1.08  thf('44', plain, ((v1_relat_1 @ sk_B)),
% 0.91/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.08  thf('45', plain, (((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.91/1.08      inference('demod', [status(thm)], ['43', '44'])).
% 0.91/1.08  thf(t146_relat_1, axiom,
% 0.91/1.08    (![A:$i]:
% 0.91/1.08     ( ( v1_relat_1 @ A ) =>
% 0.91/1.08       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.91/1.08  thf('46', plain,
% 0.91/1.08      (![X52 : $i]:
% 0.91/1.08         (((k9_relat_1 @ X52 @ (k1_relat_1 @ X52)) = (k2_relat_1 @ X52))
% 0.91/1.08          | ~ (v1_relat_1 @ X52))),
% 0.91/1.08      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.91/1.08  thf('47', plain,
% 0.91/1.08      ((((k9_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ sk_A)
% 0.91/1.08          = (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.91/1.08        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.91/1.08      inference('sup+', [status(thm)], ['45', '46'])).
% 0.91/1.08  thf('48', plain,
% 0.91/1.08      ((~ (v1_relat_1 @ sk_B)
% 0.91/1.08        | ((k9_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ sk_A)
% 0.91/1.08            = (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))))),
% 0.91/1.08      inference('sup-', [status(thm)], ['9', '47'])).
% 0.91/1.08  thf('49', plain, ((v1_relat_1 @ sk_B)),
% 0.91/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.08  thf('50', plain,
% 0.91/1.08      (((k9_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ sk_A)
% 0.91/1.08         = (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.91/1.08      inference('demod', [status(thm)], ['48', '49'])).
% 0.91/1.08  thf('51', plain,
% 0.91/1.08      ((((k9_relat_1 @ sk_B @ sk_A) = (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.91/1.08        | ~ (v1_relat_1 @ sk_B))),
% 0.91/1.08      inference('sup+', [status(thm)], ['8', '50'])).
% 0.91/1.08  thf('52', plain, ((v1_relat_1 @ sk_B)),
% 0.91/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.08  thf('53', plain,
% 0.91/1.08      (((k9_relat_1 @ sk_B @ sk_A) = (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.91/1.08      inference('demod', [status(thm)], ['51', '52'])).
% 0.91/1.08  thf('54', plain,
% 0.91/1.08      (![X58 : $i]:
% 0.91/1.08         (((k10_relat_1 @ X58 @ (k2_relat_1 @ X58)) = (k1_relat_1 @ X58))
% 0.91/1.08          | ~ (v1_relat_1 @ X58))),
% 0.91/1.08      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.91/1.08  thf('55', plain,
% 0.91/1.08      ((((k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ (k9_relat_1 @ sk_B @ sk_A))
% 0.91/1.08          = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.91/1.08        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.91/1.08      inference('sup+', [status(thm)], ['53', '54'])).
% 0.91/1.08  thf('56', plain, (((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.91/1.08      inference('demod', [status(thm)], ['43', '44'])).
% 0.91/1.08  thf('57', plain,
% 0.91/1.08      ((((k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ (k9_relat_1 @ sk_B @ sk_A))
% 0.91/1.08          = (sk_A))
% 0.91/1.08        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.91/1.08      inference('demod', [status(thm)], ['55', '56'])).
% 0.91/1.08  thf('58', plain,
% 0.91/1.08      ((~ (v1_relat_1 @ sk_B)
% 0.91/1.08        | ((k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ 
% 0.91/1.08            (k9_relat_1 @ sk_B @ sk_A)) = (sk_A)))),
% 0.91/1.08      inference('sup-', [status(thm)], ['4', '57'])).
% 0.91/1.08  thf('59', plain, ((v1_relat_1 @ sk_B)),
% 0.91/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.08  thf('60', plain,
% 0.91/1.08      (((k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ (k9_relat_1 @ sk_B @ sk_A))
% 0.91/1.08         = (sk_A))),
% 0.91/1.08      inference('demod', [status(thm)], ['58', '59'])).
% 0.91/1.08  thf('61', plain,
% 0.91/1.08      ((((k1_setfam_1 @ 
% 0.91/1.08          (k2_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A))))
% 0.91/1.08          = (sk_A))
% 0.91/1.08        | ~ (v1_relat_1 @ sk_B))),
% 0.91/1.08      inference('sup+', [status(thm)], ['3', '60'])).
% 0.91/1.08  thf('62', plain, ((v1_relat_1 @ sk_B)),
% 0.91/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.08  thf('63', plain,
% 0.91/1.08      (((k1_setfam_1 @ 
% 0.91/1.08         (k2_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A))))
% 0.91/1.08         = (sk_A))),
% 0.91/1.08      inference('demod', [status(thm)], ['61', '62'])).
% 0.91/1.08  thf(t100_xboole_1, axiom,
% 0.91/1.08    (![A:$i,B:$i]:
% 0.91/1.08     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.91/1.08  thf('64', plain,
% 0.91/1.08      (![X6 : $i, X7 : $i]:
% 0.91/1.08         ((k4_xboole_0 @ X6 @ X7)
% 0.91/1.08           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.91/1.08      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.91/1.08  thf('65', plain,
% 0.91/1.08      (![X47 : $i, X48 : $i]:
% 0.91/1.08         ((k1_setfam_1 @ (k2_tarski @ X47 @ X48)) = (k3_xboole_0 @ X47 @ X48))),
% 0.91/1.08      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.91/1.08  thf('66', plain,
% 0.91/1.08      (![X6 : $i, X7 : $i]:
% 0.91/1.08         ((k4_xboole_0 @ X6 @ X7)
% 0.91/1.08           = (k5_xboole_0 @ X6 @ (k1_setfam_1 @ (k2_tarski @ X6 @ X7))))),
% 0.91/1.08      inference('demod', [status(thm)], ['64', '65'])).
% 0.91/1.08  thf('67', plain,
% 0.91/1.08      (((k4_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 0.91/1.08         = (k5_xboole_0 @ sk_A @ sk_A))),
% 0.91/1.08      inference('sup+', [status(thm)], ['63', '66'])).
% 0.91/1.08  thf('68', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.91/1.08      inference('simplify', [status(thm)], ['5'])).
% 0.91/1.08  thf(t28_xboole_1, axiom,
% 0.91/1.08    (![A:$i,B:$i]:
% 0.91/1.08     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.91/1.08  thf('69', plain,
% 0.91/1.08      (![X16 : $i, X17 : $i]:
% 0.91/1.08         (((k3_xboole_0 @ X16 @ X17) = (X16)) | ~ (r1_tarski @ X16 @ X17))),
% 0.91/1.08      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.91/1.08  thf('70', plain,
% 0.91/1.08      (![X47 : $i, X48 : $i]:
% 0.91/1.08         ((k1_setfam_1 @ (k2_tarski @ X47 @ X48)) = (k3_xboole_0 @ X47 @ X48))),
% 0.91/1.08      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.91/1.08  thf('71', plain,
% 0.91/1.08      (![X16 : $i, X17 : $i]:
% 0.91/1.08         (((k1_setfam_1 @ (k2_tarski @ X16 @ X17)) = (X16))
% 0.91/1.08          | ~ (r1_tarski @ X16 @ X17))),
% 0.91/1.08      inference('demod', [status(thm)], ['69', '70'])).
% 0.91/1.08  thf('72', plain,
% 0.91/1.08      (![X0 : $i]: ((k1_setfam_1 @ (k2_tarski @ X0 @ X0)) = (X0))),
% 0.91/1.08      inference('sup-', [status(thm)], ['68', '71'])).
% 0.91/1.08  thf('73', plain,
% 0.91/1.08      (![X6 : $i, X7 : $i]:
% 0.91/1.08         ((k4_xboole_0 @ X6 @ X7)
% 0.91/1.08           = (k5_xboole_0 @ X6 @ (k1_setfam_1 @ (k2_tarski @ X6 @ X7))))),
% 0.91/1.08      inference('demod', [status(thm)], ['64', '65'])).
% 0.91/1.08  thf('74', plain,
% 0.91/1.08      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.91/1.08      inference('sup+', [status(thm)], ['72', '73'])).
% 0.91/1.08  thf('75', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.91/1.08      inference('simplify', [status(thm)], ['5'])).
% 0.91/1.08  thf(l32_xboole_1, axiom,
% 0.91/1.08    (![A:$i,B:$i]:
% 0.91/1.08     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.91/1.08  thf('76', plain,
% 0.91/1.08      (![X3 : $i, X5 : $i]:
% 0.91/1.08         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.91/1.08      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.91/1.08  thf('77', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.91/1.08      inference('sup-', [status(thm)], ['75', '76'])).
% 0.91/1.08  thf('78', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.91/1.08      inference('sup+', [status(thm)], ['74', '77'])).
% 0.91/1.08  thf('79', plain,
% 0.91/1.08      (((k4_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 0.91/1.08         = (k1_xboole_0))),
% 0.91/1.08      inference('demod', [status(thm)], ['67', '78'])).
% 0.91/1.08  thf('80', plain,
% 0.91/1.08      (![X3 : $i, X4 : $i]:
% 0.91/1.08         ((r1_tarski @ X3 @ X4) | ((k4_xboole_0 @ X3 @ X4) != (k1_xboole_0)))),
% 0.91/1.08      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.91/1.08  thf('81', plain,
% 0.91/1.08      ((((k1_xboole_0) != (k1_xboole_0))
% 0.91/1.08        | (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A))))),
% 0.91/1.08      inference('sup-', [status(thm)], ['79', '80'])).
% 0.91/1.08  thf('82', plain,
% 0.91/1.08      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 0.91/1.08      inference('simplify', [status(thm)], ['81'])).
% 0.91/1.08  thf('83', plain, ($false), inference('demod', [status(thm)], ['0', '82'])).
% 0.91/1.08  
% 0.91/1.08  % SZS output end Refutation
% 0.91/1.08  
% 0.91/1.09  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
