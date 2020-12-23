%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GQ8brAXZ6q

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:45 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 230 expanded)
%              Number of leaves         :   39 (  85 expanded)
%              Depth                    :   34
%              Number of atoms          :  945 (2186 expanded)
%              Number of equality atoms :   63 (  95 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t157_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) )
          & ( r1_tarski @ A @ ( k1_relat_1 @ C ) )
          & ( v2_funct_1 @ C ) )
       => ( r1_tarski @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) )
            & ( r1_tarski @ A @ ( k1_relat_1 @ C ) )
            & ( v2_funct_1 @ C ) )
         => ( r1_tarski @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t157_funct_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t152_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( r1_tarski @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) @ A ) ) ) )).

thf('1',plain,(
    ! [X70: $i,X71: $i] :
      ( ~ ( v2_funct_1 @ X70 )
      | ( r1_tarski @ ( k10_relat_1 @ X70 @ ( k9_relat_1 @ X70 @ X71 ) ) @ X71 )
      | ~ ( v1_funct_1 @ X70 )
      | ~ ( v1_relat_1 @ X70 ) ) ),
    inference(cnf,[status(esa)],[t152_funct_1])).

thf(t139_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('2',plain,(
    ! [X67: $i,X68: $i,X69: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X68 @ X67 ) @ X69 )
        = ( k3_xboole_0 @ X67 @ ( k10_relat_1 @ X68 @ X69 ) ) )
      | ~ ( v1_relat_1 @ X68 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X43: $i,X44: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X43 @ X44 ) )
      = ( k3_xboole_0 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('4',plain,(
    ! [X67: $i,X68: $i,X69: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X68 @ X67 ) @ X69 )
        = ( k1_setfam_1 @ ( k2_tarski @ X67 @ ( k10_relat_1 @ X68 @ X69 ) ) ) )
      | ~ ( v1_relat_1 @ X68 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( v1_relat_1 @ X45 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X45 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('6',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( X1 != X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('7',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t162_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( r1_tarski @ B @ C )
         => ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B )
            = ( k9_relat_1 @ A @ B ) ) ) ) )).

thf('8',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ~ ( r1_tarski @ X48 @ X49 )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X50 @ X49 ) @ X48 )
        = ( k9_relat_1 @ X50 @ X48 ) )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t162_relat_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X0 )
        = ( k9_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( v1_relat_1 @ X45 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X45 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('11',plain,(
    ! [X63: $i,X64: $i] :
      ( ( ( k7_relat_1 @ X64 @ X63 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X63 ) @ X64 ) )
      | ~ ( v1_relat_1 @ X64 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('12',plain,(
    ! [X55: $i,X56: $i] :
      ( ~ ( v1_relat_1 @ X55 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X56 @ X55 ) )
        = ( k10_relat_1 @ X56 @ ( k1_relat_1 @ X55 ) ) )
      | ~ ( v1_relat_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('13',plain,(
    ! [X58: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X58 ) )
      = X58 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('14',plain,(
    ! [X51: $i] :
      ( ( ( k10_relat_1 @ X51 @ ( k2_relat_1 @ X51 ) )
        = ( k1_relat_1 @ X51 ) )
      | ~ ( v1_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
        = ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X57: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X57 ) )
      = X57 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('17',plain,(
    ! [X65: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X65 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t178_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('20',plain,(
    ! [X52: $i,X53: $i,X54: $i] :
      ( ~ ( r1_tarski @ X52 @ X53 )
      | ~ ( v1_relat_1 @ X54 )
      | ( r1_tarski @ ( k10_relat_1 @ X54 @ X52 ) @ ( k10_relat_1 @ X54 @ X53 ) ) ) ),
    inference(cnf,[status(esa)],[t178_relat_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X0 @ sk_A ) @ ( k10_relat_1 @ X0 @ ( k1_relat_1 @ sk_C ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( r1_tarski @ sk_A @ ( k10_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X65: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X65 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('24',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( r1_tarski @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['12','24'])).

thf('26',plain,(
    ! [X65: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X65 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('27',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,
    ( ( r1_tarski @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['11','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('32',plain,(
    ! [X61: $i,X62: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X61 @ X62 ) ) @ X62 )
      | ~ ( v1_relat_1 @ X61 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf('33',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ( X0
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( sk_A
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( sk_A
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('38',plain,(
    ! [X47: $i] :
      ( ( ( k9_relat_1 @ X47 @ ( k1_relat_1 @ X47 ) )
        = ( k2_relat_1 @ X47 ) )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('39',plain,
    ( ( ( k9_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ sk_A )
      = ( k2_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k9_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ sk_A )
      = ( k2_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['10','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( k9_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ sk_A )
    = ( k2_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ( k9_relat_1 @ sk_C @ sk_A )
      = ( k2_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['9','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( k9_relat_1 @ sk_C @ sk_A )
    = ( k2_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X51: $i] :
      ( ( ( k10_relat_1 @ X51 @ ( k2_relat_1 @ X51 ) )
        = ( k1_relat_1 @ X51 ) )
      | ~ ( v1_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('47',plain,
    ( ( ( k10_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_C @ sk_A ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,
    ( sk_A
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('49',plain,
    ( ( ( k10_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_C @ sk_A ) )
      = sk_A )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k10_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_C @ sk_A ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['5','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( k10_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_C @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( ( k1_setfam_1 @ ( k2_tarski @ sk_A @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) ) ) )
      = sk_A )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['4','52'])).

thf('54',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( k1_setfam_1 @ ( k2_tarski @ sk_A @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) ) ) )
    = sk_A ),
    inference(demod,[status(thm)],['53','54'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('56',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('57',plain,(
    ! [X43: $i,X44: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X43 @ X44 ) )
      = ( k3_xboole_0 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('58',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k1_setfam_1 @ ( k2_tarski @ X7 @ X8 ) ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) ) )
    = ( k5_xboole_0 @ sk_A @ sk_A ) ),
    inference('sup+',[status(thm)],['55','58'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('61',plain,(
    ! [X43: $i,X44: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X43 @ X44 ) )
      = ( k3_xboole_0 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k1_setfam_1 @ ( k2_tarski @ X7 @ X8 ) ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['6'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('66',plain,(
    ! [X4: $i,X6: $i] :
      ( ( ( k4_xboole_0 @ X4 @ X6 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['64','67'])).

thf('69',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['59','68'])).

thf('70',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( ( k4_xboole_0 @ X4 @ X5 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('71',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ! [X70: $i,X71: $i] :
      ( ~ ( v2_funct_1 @ X70 )
      | ( r1_tarski @ ( k10_relat_1 @ X70 @ ( k9_relat_1 @ X70 @ X71 ) ) @ X71 )
      | ~ ( v1_funct_1 @ X70 )
      | ~ ( v1_relat_1 @ X70 ) ) ),
    inference(cnf,[status(esa)],[t152_funct_1])).

thf('74',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( r1_tarski @ X0 @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) )
      | ( X0
        = ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( sk_A
      = ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['72','75'])).

thf('77',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( sk_A
    = ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['76','77','78','79'])).

thf('81',plain,(
    r1_tarski @ ( k9_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_C @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ! [X52: $i,X53: $i,X54: $i] :
      ( ~ ( r1_tarski @ X52 @ X53 )
      | ~ ( v1_relat_1 @ X54 )
      | ( r1_tarski @ ( k10_relat_1 @ X54 @ X52 ) @ ( k10_relat_1 @ X54 @ X53 ) ) ) ),
    inference(cnf,[status(esa)],[t178_relat_1])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ sk_C @ sk_A ) ) @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ sk_C @ sk_B ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['80','83'])).

thf('85',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_B ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('87',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X9 @ X10 )
      | ~ ( r1_tarski @ X10 @ X11 )
      | ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ~ ( r1_tarski @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_B ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['1','88'])).

thf('90',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['89','90','91','92'])).

thf('94',plain,(
    $false ),
    inference(demod,[status(thm)],['0','93'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GQ8brAXZ6q
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:22:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.45/0.65  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.65  % Solved by: fo/fo7.sh
% 0.45/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.65  % done 421 iterations in 0.196s
% 0.45/0.65  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.65  % SZS output start Refutation
% 0.45/0.65  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.65  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.65  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.45/0.65  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.45/0.65  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.45/0.65  thf(sk_C_type, type, sk_C: $i).
% 0.45/0.65  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.45/0.65  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.45/0.65  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.45/0.65  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.45/0.65  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.45/0.65  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.45/0.65  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.45/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.65  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.65  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.45/0.65  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.45/0.65  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.45/0.65  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.45/0.65  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.45/0.65  thf(t157_funct_1, conjecture,
% 0.45/0.65    (![A:$i,B:$i,C:$i]:
% 0.45/0.65     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.45/0.65       ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) & 
% 0.45/0.65           ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & ( v2_funct_1 @ C ) ) =>
% 0.45/0.65         ( r1_tarski @ A @ B ) ) ))).
% 0.45/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.65    (~( ![A:$i,B:$i,C:$i]:
% 0.45/0.65        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.45/0.65          ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) & 
% 0.45/0.65              ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & ( v2_funct_1 @ C ) ) =>
% 0.45/0.65            ( r1_tarski @ A @ B ) ) ) )),
% 0.45/0.65    inference('cnf.neg', [status(esa)], [t157_funct_1])).
% 0.45/0.65  thf('0', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf(t152_funct_1, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.45/0.65       ( ( v2_funct_1 @ B ) =>
% 0.45/0.65         ( r1_tarski @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) @ A ) ) ))).
% 0.45/0.65  thf('1', plain,
% 0.45/0.65      (![X70 : $i, X71 : $i]:
% 0.45/0.65         (~ (v2_funct_1 @ X70)
% 0.45/0.65          | (r1_tarski @ (k10_relat_1 @ X70 @ (k9_relat_1 @ X70 @ X71)) @ X71)
% 0.45/0.65          | ~ (v1_funct_1 @ X70)
% 0.45/0.65          | ~ (v1_relat_1 @ X70))),
% 0.45/0.65      inference('cnf', [status(esa)], [t152_funct_1])).
% 0.45/0.65  thf(t139_funct_1, axiom,
% 0.45/0.65    (![A:$i,B:$i,C:$i]:
% 0.45/0.65     ( ( v1_relat_1 @ C ) =>
% 0.45/0.65       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.45/0.65         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.45/0.65  thf('2', plain,
% 0.45/0.65      (![X67 : $i, X68 : $i, X69 : $i]:
% 0.45/0.65         (((k10_relat_1 @ (k7_relat_1 @ X68 @ X67) @ X69)
% 0.45/0.65            = (k3_xboole_0 @ X67 @ (k10_relat_1 @ X68 @ X69)))
% 0.45/0.65          | ~ (v1_relat_1 @ X68))),
% 0.45/0.65      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.45/0.65  thf(t12_setfam_1, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.45/0.65  thf('3', plain,
% 0.45/0.65      (![X43 : $i, X44 : $i]:
% 0.45/0.65         ((k1_setfam_1 @ (k2_tarski @ X43 @ X44)) = (k3_xboole_0 @ X43 @ X44))),
% 0.45/0.65      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.45/0.65  thf('4', plain,
% 0.45/0.65      (![X67 : $i, X68 : $i, X69 : $i]:
% 0.45/0.65         (((k10_relat_1 @ (k7_relat_1 @ X68 @ X67) @ X69)
% 0.45/0.65            = (k1_setfam_1 @ (k2_tarski @ X67 @ (k10_relat_1 @ X68 @ X69))))
% 0.45/0.65          | ~ (v1_relat_1 @ X68))),
% 0.45/0.65      inference('demod', [status(thm)], ['2', '3'])).
% 0.45/0.65  thf(dt_k7_relat_1, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.45/0.65  thf('5', plain,
% 0.45/0.65      (![X45 : $i, X46 : $i]:
% 0.45/0.65         (~ (v1_relat_1 @ X45) | (v1_relat_1 @ (k7_relat_1 @ X45 @ X46)))),
% 0.45/0.65      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.45/0.65  thf(d10_xboole_0, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.45/0.65  thf('6', plain,
% 0.45/0.65      (![X1 : $i, X2 : $i]: ((r1_tarski @ X1 @ X2) | ((X1) != (X2)))),
% 0.45/0.65      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.45/0.65  thf('7', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 0.45/0.65      inference('simplify', [status(thm)], ['6'])).
% 0.45/0.65  thf(t162_relat_1, axiom,
% 0.45/0.65    (![A:$i]:
% 0.45/0.65     ( ( v1_relat_1 @ A ) =>
% 0.45/0.65       ( ![B:$i,C:$i]:
% 0.45/0.65         ( ( r1_tarski @ B @ C ) =>
% 0.45/0.65           ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B ) =
% 0.45/0.65             ( k9_relat_1 @ A @ B ) ) ) ) ))).
% 0.45/0.65  thf('8', plain,
% 0.45/0.65      (![X48 : $i, X49 : $i, X50 : $i]:
% 0.45/0.65         (~ (r1_tarski @ X48 @ X49)
% 0.45/0.65          | ((k9_relat_1 @ (k7_relat_1 @ X50 @ X49) @ X48)
% 0.45/0.65              = (k9_relat_1 @ X50 @ X48))
% 0.45/0.65          | ~ (v1_relat_1 @ X50))),
% 0.45/0.65      inference('cnf', [status(esa)], [t162_relat_1])).
% 0.45/0.65  thf('9', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         (~ (v1_relat_1 @ X1)
% 0.45/0.65          | ((k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X0)
% 0.45/0.65              = (k9_relat_1 @ X1 @ X0)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['7', '8'])).
% 0.45/0.65  thf('10', plain,
% 0.45/0.65      (![X45 : $i, X46 : $i]:
% 0.45/0.65         (~ (v1_relat_1 @ X45) | (v1_relat_1 @ (k7_relat_1 @ X45 @ X46)))),
% 0.45/0.65      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.45/0.65  thf(t94_relat_1, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( v1_relat_1 @ B ) =>
% 0.45/0.65       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.45/0.65  thf('11', plain,
% 0.45/0.65      (![X63 : $i, X64 : $i]:
% 0.45/0.65         (((k7_relat_1 @ X64 @ X63) = (k5_relat_1 @ (k6_relat_1 @ X63) @ X64))
% 0.45/0.65          | ~ (v1_relat_1 @ X64))),
% 0.45/0.65      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.45/0.65  thf(t182_relat_1, axiom,
% 0.45/0.65    (![A:$i]:
% 0.45/0.65     ( ( v1_relat_1 @ A ) =>
% 0.45/0.65       ( ![B:$i]:
% 0.45/0.65         ( ( v1_relat_1 @ B ) =>
% 0.45/0.65           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.45/0.65             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.45/0.65  thf('12', plain,
% 0.45/0.65      (![X55 : $i, X56 : $i]:
% 0.45/0.65         (~ (v1_relat_1 @ X55)
% 0.45/0.65          | ((k1_relat_1 @ (k5_relat_1 @ X56 @ X55))
% 0.45/0.65              = (k10_relat_1 @ X56 @ (k1_relat_1 @ X55)))
% 0.45/0.65          | ~ (v1_relat_1 @ X56))),
% 0.45/0.65      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.45/0.65  thf(t71_relat_1, axiom,
% 0.45/0.65    (![A:$i]:
% 0.45/0.65     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.45/0.65       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.45/0.65  thf('13', plain, (![X58 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X58)) = (X58))),
% 0.45/0.65      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.45/0.65  thf(t169_relat_1, axiom,
% 0.45/0.65    (![A:$i]:
% 0.45/0.65     ( ( v1_relat_1 @ A ) =>
% 0.45/0.65       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.45/0.65  thf('14', plain,
% 0.45/0.65      (![X51 : $i]:
% 0.45/0.65         (((k10_relat_1 @ X51 @ (k2_relat_1 @ X51)) = (k1_relat_1 @ X51))
% 0.45/0.65          | ~ (v1_relat_1 @ X51))),
% 0.45/0.65      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.45/0.65  thf('15', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         (((k10_relat_1 @ (k6_relat_1 @ X0) @ X0)
% 0.45/0.65            = (k1_relat_1 @ (k6_relat_1 @ X0)))
% 0.45/0.65          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.45/0.65      inference('sup+', [status(thm)], ['13', '14'])).
% 0.45/0.65  thf('16', plain, (![X57 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X57)) = (X57))),
% 0.45/0.65      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.45/0.65  thf(fc3_funct_1, axiom,
% 0.45/0.65    (![A:$i]:
% 0.45/0.65     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.45/0.65       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.45/0.65  thf('17', plain, (![X65 : $i]: (v1_relat_1 @ (k6_relat_1 @ X65))),
% 0.45/0.65      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.45/0.65  thf('18', plain,
% 0.45/0.65      (![X0 : $i]: ((k10_relat_1 @ (k6_relat_1 @ X0) @ X0) = (X0))),
% 0.45/0.65      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.45/0.65  thf('19', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_C))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf(t178_relat_1, axiom,
% 0.45/0.65    (![A:$i,B:$i,C:$i]:
% 0.45/0.65     ( ( v1_relat_1 @ C ) =>
% 0.45/0.65       ( ( r1_tarski @ A @ B ) =>
% 0.45/0.65         ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.45/0.65  thf('20', plain,
% 0.45/0.65      (![X52 : $i, X53 : $i, X54 : $i]:
% 0.45/0.65         (~ (r1_tarski @ X52 @ X53)
% 0.45/0.65          | ~ (v1_relat_1 @ X54)
% 0.45/0.65          | (r1_tarski @ (k10_relat_1 @ X54 @ X52) @ (k10_relat_1 @ X54 @ X53)))),
% 0.45/0.65      inference('cnf', [status(esa)], [t178_relat_1])).
% 0.45/0.65  thf('21', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         ((r1_tarski @ (k10_relat_1 @ X0 @ sk_A) @ 
% 0.45/0.65           (k10_relat_1 @ X0 @ (k1_relat_1 @ sk_C)))
% 0.45/0.65          | ~ (v1_relat_1 @ X0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['19', '20'])).
% 0.45/0.65  thf('22', plain,
% 0.45/0.65      (((r1_tarski @ sk_A @ 
% 0.45/0.65         (k10_relat_1 @ (k6_relat_1 @ sk_A) @ (k1_relat_1 @ sk_C)))
% 0.45/0.65        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A)))),
% 0.45/0.65      inference('sup+', [status(thm)], ['18', '21'])).
% 0.45/0.65  thf('23', plain, (![X65 : $i]: (v1_relat_1 @ (k6_relat_1 @ X65))),
% 0.45/0.65      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.45/0.65  thf('24', plain,
% 0.45/0.65      ((r1_tarski @ sk_A @ 
% 0.45/0.65        (k10_relat_1 @ (k6_relat_1 @ sk_A) @ (k1_relat_1 @ sk_C)))),
% 0.45/0.65      inference('demod', [status(thm)], ['22', '23'])).
% 0.45/0.65  thf('25', plain,
% 0.45/0.65      (((r1_tarski @ sk_A @ 
% 0.45/0.65         (k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_C)))
% 0.45/0.65        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A))
% 0.45/0.65        | ~ (v1_relat_1 @ sk_C))),
% 0.45/0.65      inference('sup+', [status(thm)], ['12', '24'])).
% 0.45/0.65  thf('26', plain, (![X65 : $i]: (v1_relat_1 @ (k6_relat_1 @ X65))),
% 0.45/0.65      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.45/0.65  thf('27', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('28', plain,
% 0.45/0.65      ((r1_tarski @ sk_A @ 
% 0.45/0.65        (k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_C)))),
% 0.45/0.65      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.45/0.65  thf('29', plain,
% 0.45/0.65      (((r1_tarski @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_C @ sk_A)))
% 0.45/0.65        | ~ (v1_relat_1 @ sk_C))),
% 0.45/0.65      inference('sup+', [status(thm)], ['11', '28'])).
% 0.45/0.65  thf('30', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('31', plain,
% 0.45/0.65      ((r1_tarski @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_C @ sk_A)))),
% 0.45/0.65      inference('demod', [status(thm)], ['29', '30'])).
% 0.45/0.65  thf(t87_relat_1, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( v1_relat_1 @ B ) =>
% 0.45/0.65       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 0.45/0.65  thf('32', plain,
% 0.45/0.65      (![X61 : $i, X62 : $i]:
% 0.45/0.65         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X61 @ X62)) @ X62)
% 0.45/0.65          | ~ (v1_relat_1 @ X61))),
% 0.45/0.65      inference('cnf', [status(esa)], [t87_relat_1])).
% 0.45/0.65  thf('33', plain,
% 0.45/0.65      (![X1 : $i, X3 : $i]:
% 0.45/0.65         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 0.45/0.65      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.45/0.65  thf('34', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         (~ (v1_relat_1 @ X1)
% 0.45/0.65          | ~ (r1_tarski @ X0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.45/0.65          | ((X0) = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 0.45/0.65      inference('sup-', [status(thm)], ['32', '33'])).
% 0.45/0.65  thf('35', plain,
% 0.45/0.65      ((((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_C @ sk_A)))
% 0.45/0.65        | ~ (v1_relat_1 @ sk_C))),
% 0.45/0.65      inference('sup-', [status(thm)], ['31', '34'])).
% 0.45/0.65  thf('36', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('37', plain, (((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_C @ sk_A)))),
% 0.45/0.65      inference('demod', [status(thm)], ['35', '36'])).
% 0.45/0.65  thf(t146_relat_1, axiom,
% 0.45/0.65    (![A:$i]:
% 0.45/0.65     ( ( v1_relat_1 @ A ) =>
% 0.45/0.65       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.45/0.65  thf('38', plain,
% 0.45/0.65      (![X47 : $i]:
% 0.45/0.65         (((k9_relat_1 @ X47 @ (k1_relat_1 @ X47)) = (k2_relat_1 @ X47))
% 0.45/0.65          | ~ (v1_relat_1 @ X47))),
% 0.45/0.65      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.45/0.65  thf('39', plain,
% 0.45/0.65      ((((k9_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ sk_A)
% 0.45/0.65          = (k2_relat_1 @ (k7_relat_1 @ sk_C @ sk_A)))
% 0.45/0.65        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_C @ sk_A)))),
% 0.45/0.65      inference('sup+', [status(thm)], ['37', '38'])).
% 0.45/0.65  thf('40', plain,
% 0.45/0.65      ((~ (v1_relat_1 @ sk_C)
% 0.45/0.65        | ((k9_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ sk_A)
% 0.45/0.65            = (k2_relat_1 @ (k7_relat_1 @ sk_C @ sk_A))))),
% 0.45/0.65      inference('sup-', [status(thm)], ['10', '39'])).
% 0.45/0.65  thf('41', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('42', plain,
% 0.45/0.65      (((k9_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ sk_A)
% 0.45/0.65         = (k2_relat_1 @ (k7_relat_1 @ sk_C @ sk_A)))),
% 0.45/0.65      inference('demod', [status(thm)], ['40', '41'])).
% 0.45/0.65  thf('43', plain,
% 0.45/0.65      ((((k9_relat_1 @ sk_C @ sk_A) = (k2_relat_1 @ (k7_relat_1 @ sk_C @ sk_A)))
% 0.45/0.65        | ~ (v1_relat_1 @ sk_C))),
% 0.45/0.65      inference('sup+', [status(thm)], ['9', '42'])).
% 0.45/0.65  thf('44', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('45', plain,
% 0.45/0.65      (((k9_relat_1 @ sk_C @ sk_A) = (k2_relat_1 @ (k7_relat_1 @ sk_C @ sk_A)))),
% 0.45/0.65      inference('demod', [status(thm)], ['43', '44'])).
% 0.45/0.65  thf('46', plain,
% 0.45/0.65      (![X51 : $i]:
% 0.45/0.65         (((k10_relat_1 @ X51 @ (k2_relat_1 @ X51)) = (k1_relat_1 @ X51))
% 0.45/0.65          | ~ (v1_relat_1 @ X51))),
% 0.45/0.65      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.45/0.65  thf('47', plain,
% 0.45/0.65      ((((k10_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ (k9_relat_1 @ sk_C @ sk_A))
% 0.45/0.65          = (k1_relat_1 @ (k7_relat_1 @ sk_C @ sk_A)))
% 0.45/0.65        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_C @ sk_A)))),
% 0.45/0.65      inference('sup+', [status(thm)], ['45', '46'])).
% 0.45/0.65  thf('48', plain, (((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_C @ sk_A)))),
% 0.45/0.65      inference('demod', [status(thm)], ['35', '36'])).
% 0.45/0.65  thf('49', plain,
% 0.45/0.65      ((((k10_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ (k9_relat_1 @ sk_C @ sk_A))
% 0.45/0.65          = (sk_A))
% 0.45/0.65        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_C @ sk_A)))),
% 0.45/0.65      inference('demod', [status(thm)], ['47', '48'])).
% 0.45/0.65  thf('50', plain,
% 0.45/0.65      ((~ (v1_relat_1 @ sk_C)
% 0.45/0.65        | ((k10_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ 
% 0.45/0.65            (k9_relat_1 @ sk_C @ sk_A)) = (sk_A)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['5', '49'])).
% 0.45/0.65  thf('51', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('52', plain,
% 0.45/0.65      (((k10_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ (k9_relat_1 @ sk_C @ sk_A))
% 0.45/0.65         = (sk_A))),
% 0.45/0.65      inference('demod', [status(thm)], ['50', '51'])).
% 0.45/0.65  thf('53', plain,
% 0.45/0.65      ((((k1_setfam_1 @ 
% 0.45/0.65          (k2_tarski @ sk_A @ (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A))))
% 0.45/0.65          = (sk_A))
% 0.45/0.65        | ~ (v1_relat_1 @ sk_C))),
% 0.45/0.65      inference('sup+', [status(thm)], ['4', '52'])).
% 0.45/0.65  thf('54', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('55', plain,
% 0.45/0.65      (((k1_setfam_1 @ 
% 0.45/0.65         (k2_tarski @ sk_A @ (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A))))
% 0.45/0.65         = (sk_A))),
% 0.45/0.65      inference('demod', [status(thm)], ['53', '54'])).
% 0.45/0.65  thf(t100_xboole_1, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.45/0.65  thf('56', plain,
% 0.45/0.65      (![X7 : $i, X8 : $i]:
% 0.45/0.65         ((k4_xboole_0 @ X7 @ X8)
% 0.45/0.65           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.45/0.65      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.45/0.65  thf('57', plain,
% 0.45/0.65      (![X43 : $i, X44 : $i]:
% 0.45/0.65         ((k1_setfam_1 @ (k2_tarski @ X43 @ X44)) = (k3_xboole_0 @ X43 @ X44))),
% 0.45/0.65      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.45/0.65  thf('58', plain,
% 0.45/0.65      (![X7 : $i, X8 : $i]:
% 0.45/0.65         ((k4_xboole_0 @ X7 @ X8)
% 0.45/0.65           = (k5_xboole_0 @ X7 @ (k1_setfam_1 @ (k2_tarski @ X7 @ X8))))),
% 0.45/0.65      inference('demod', [status(thm)], ['56', '57'])).
% 0.45/0.65  thf('59', plain,
% 0.45/0.65      (((k4_xboole_0 @ sk_A @ (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A)))
% 0.45/0.65         = (k5_xboole_0 @ sk_A @ sk_A))),
% 0.45/0.65      inference('sup+', [status(thm)], ['55', '58'])).
% 0.45/0.65  thf(idempotence_k3_xboole_0, axiom,
% 0.45/0.65    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.45/0.65  thf('60', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.45/0.65      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.45/0.65  thf('61', plain,
% 0.45/0.65      (![X43 : $i, X44 : $i]:
% 0.45/0.65         ((k1_setfam_1 @ (k2_tarski @ X43 @ X44)) = (k3_xboole_0 @ X43 @ X44))),
% 0.45/0.65      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.45/0.65  thf('62', plain,
% 0.45/0.65      (![X0 : $i]: ((k1_setfam_1 @ (k2_tarski @ X0 @ X0)) = (X0))),
% 0.45/0.65      inference('demod', [status(thm)], ['60', '61'])).
% 0.45/0.65  thf('63', plain,
% 0.45/0.65      (![X7 : $i, X8 : $i]:
% 0.45/0.65         ((k4_xboole_0 @ X7 @ X8)
% 0.45/0.65           = (k5_xboole_0 @ X7 @ (k1_setfam_1 @ (k2_tarski @ X7 @ X8))))),
% 0.45/0.65      inference('demod', [status(thm)], ['56', '57'])).
% 0.45/0.65  thf('64', plain,
% 0.45/0.65      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.45/0.65      inference('sup+', [status(thm)], ['62', '63'])).
% 0.45/0.65  thf('65', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 0.45/0.65      inference('simplify', [status(thm)], ['6'])).
% 0.45/0.65  thf(l32_xboole_1, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.45/0.65  thf('66', plain,
% 0.45/0.65      (![X4 : $i, X6 : $i]:
% 0.45/0.65         (((k4_xboole_0 @ X4 @ X6) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ X6))),
% 0.45/0.65      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.45/0.65  thf('67', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['65', '66'])).
% 0.45/0.65  thf('68', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.45/0.65      inference('sup+', [status(thm)], ['64', '67'])).
% 0.45/0.65  thf('69', plain,
% 0.45/0.65      (((k4_xboole_0 @ sk_A @ (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A)))
% 0.45/0.65         = (k1_xboole_0))),
% 0.45/0.65      inference('demod', [status(thm)], ['59', '68'])).
% 0.45/0.65  thf('70', plain,
% 0.45/0.65      (![X4 : $i, X5 : $i]:
% 0.45/0.65         ((r1_tarski @ X4 @ X5) | ((k4_xboole_0 @ X4 @ X5) != (k1_xboole_0)))),
% 0.45/0.65      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.45/0.65  thf('71', plain,
% 0.45/0.65      ((((k1_xboole_0) != (k1_xboole_0))
% 0.45/0.65        | (r1_tarski @ sk_A @ (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A))))),
% 0.45/0.65      inference('sup-', [status(thm)], ['69', '70'])).
% 0.45/0.65  thf('72', plain,
% 0.45/0.65      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A)))),
% 0.45/0.65      inference('simplify', [status(thm)], ['71'])).
% 0.45/0.65  thf('73', plain,
% 0.45/0.65      (![X70 : $i, X71 : $i]:
% 0.45/0.65         (~ (v2_funct_1 @ X70)
% 0.45/0.65          | (r1_tarski @ (k10_relat_1 @ X70 @ (k9_relat_1 @ X70 @ X71)) @ X71)
% 0.45/0.65          | ~ (v1_funct_1 @ X70)
% 0.45/0.65          | ~ (v1_relat_1 @ X70))),
% 0.45/0.65      inference('cnf', [status(esa)], [t152_funct_1])).
% 0.45/0.65  thf('74', plain,
% 0.45/0.65      (![X1 : $i, X3 : $i]:
% 0.45/0.65         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 0.45/0.65      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.45/0.65  thf('75', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         (~ (v1_relat_1 @ X1)
% 0.45/0.65          | ~ (v1_funct_1 @ X1)
% 0.45/0.65          | ~ (v2_funct_1 @ X1)
% 0.45/0.65          | ~ (r1_tarski @ X0 @ (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0)))
% 0.45/0.65          | ((X0) = (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0))))),
% 0.45/0.65      inference('sup-', [status(thm)], ['73', '74'])).
% 0.45/0.65  thf('76', plain,
% 0.45/0.65      ((((sk_A) = (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A)))
% 0.45/0.65        | ~ (v2_funct_1 @ sk_C)
% 0.45/0.65        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.65        | ~ (v1_relat_1 @ sk_C))),
% 0.45/0.65      inference('sup-', [status(thm)], ['72', '75'])).
% 0.45/0.65  thf('77', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('78', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('79', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('80', plain,
% 0.45/0.65      (((sk_A) = (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A)))),
% 0.45/0.65      inference('demod', [status(thm)], ['76', '77', '78', '79'])).
% 0.45/0.65  thf('81', plain,
% 0.45/0.65      ((r1_tarski @ (k9_relat_1 @ sk_C @ sk_A) @ (k9_relat_1 @ sk_C @ sk_B))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('82', plain,
% 0.45/0.65      (![X52 : $i, X53 : $i, X54 : $i]:
% 0.45/0.65         (~ (r1_tarski @ X52 @ X53)
% 0.45/0.65          | ~ (v1_relat_1 @ X54)
% 0.45/0.65          | (r1_tarski @ (k10_relat_1 @ X54 @ X52) @ (k10_relat_1 @ X54 @ X53)))),
% 0.45/0.65      inference('cnf', [status(esa)], [t178_relat_1])).
% 0.45/0.65  thf('83', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         ((r1_tarski @ (k10_relat_1 @ X0 @ (k9_relat_1 @ sk_C @ sk_A)) @ 
% 0.45/0.65           (k10_relat_1 @ X0 @ (k9_relat_1 @ sk_C @ sk_B)))
% 0.45/0.65          | ~ (v1_relat_1 @ X0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['81', '82'])).
% 0.45/0.65  thf('84', plain,
% 0.45/0.65      (((r1_tarski @ sk_A @ (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_B)))
% 0.45/0.65        | ~ (v1_relat_1 @ sk_C))),
% 0.45/0.65      inference('sup+', [status(thm)], ['80', '83'])).
% 0.45/0.65  thf('85', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('86', plain,
% 0.45/0.65      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_B)))),
% 0.45/0.65      inference('demod', [status(thm)], ['84', '85'])).
% 0.45/0.65  thf(t1_xboole_1, axiom,
% 0.45/0.65    (![A:$i,B:$i,C:$i]:
% 0.45/0.65     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.45/0.65       ( r1_tarski @ A @ C ) ))).
% 0.45/0.65  thf('87', plain,
% 0.45/0.65      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.45/0.65         (~ (r1_tarski @ X9 @ X10)
% 0.45/0.65          | ~ (r1_tarski @ X10 @ X11)
% 0.45/0.65          | (r1_tarski @ X9 @ X11))),
% 0.45/0.65      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.45/0.65  thf('88', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         ((r1_tarski @ sk_A @ X0)
% 0.45/0.65          | ~ (r1_tarski @ (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_B)) @ 
% 0.45/0.65               X0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['86', '87'])).
% 0.45/0.65  thf('89', plain,
% 0.45/0.65      ((~ (v1_relat_1 @ sk_C)
% 0.45/0.65        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.65        | ~ (v2_funct_1 @ sk_C)
% 0.45/0.65        | (r1_tarski @ sk_A @ sk_B))),
% 0.45/0.65      inference('sup-', [status(thm)], ['1', '88'])).
% 0.45/0.65  thf('90', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('91', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('92', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('93', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.45/0.65      inference('demod', [status(thm)], ['89', '90', '91', '92'])).
% 0.45/0.65  thf('94', plain, ($false), inference('demod', [status(thm)], ['0', '93'])).
% 0.45/0.65  
% 0.45/0.65  % SZS output end Refutation
% 0.45/0.65  
% 0.45/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
