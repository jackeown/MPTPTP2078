%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aJ4AYkmWkJ

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:05 EST 2020

% Result     : Theorem 1.14s
% Output     : Refutation 1.14s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 214 expanded)
%              Number of leaves         :   32 (  76 expanded)
%              Depth                    :   18
%              Number of atoms          :  851 (2061 expanded)
%              Number of equality atoms :   43 ( 105 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t164_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
          & ( v2_funct_1 @ B ) )
       => ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
            & ( v2_funct_1 @ B ) )
         => ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) )
            = A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t164_funct_1])).

thf('0',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t146_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( r1_tarski @ X45 @ ( k1_relat_1 @ X46 ) )
      | ( r1_tarski @ X45 @ ( k10_relat_1 @ X46 @ ( k9_relat_1 @ X46 @ X45 ) ) )
      | ~ ( v1_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t146_funct_1])).

thf('2',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X8: $i,X10: $i] :
      ( ( X8 = X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('6',plain,
    ( ~ ( r1_tarski @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) @ sk_A )
    | ( ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ~ ( r1_tarski @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['6','7'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('9',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_tarski @ X20 @ X19 )
      = ( k2_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('10',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X26 @ X27 ) )
      = ( k3_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X26 @ X27 ) )
      = ( k3_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t43_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('14',plain,(
    ! [X54: $i,X55: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X55 ) @ ( k6_relat_1 @ X54 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X54 @ X55 ) ) ) ),
    inference(cnf,[status(esa)],[t43_funct_1])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('15',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( v1_relat_1 @ X39 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X40 @ X39 ) )
        = ( k10_relat_1 @ X40 @ ( k1_relat_1 @ X39 ) ) )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('16',plain,(
    ! [X32: $i,X33: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X32 @ X33 ) @ ( k1_relat_1 @ X32 ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['14','18'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('20',plain,(
    ! [X41: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X41 ) )
      = X41 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('21',plain,(
    ! [X41: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X41 ) )
      = X41 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('22',plain,(
    ! [X43: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('23',plain,(
    ! [X43: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['19','20','21','22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['13','24'])).

thf(t170_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k10_relat_1 @ B @ ( k2_relat_1 @ B ) ) ) ) )).

thf('26',plain,(
    ! [X34: $i,X35: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X34 @ X35 ) @ ( k10_relat_1 @ X34 @ ( k2_relat_1 @ X34 ) ) )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t170_relat_1])).

thf('27',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ( X8 != X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('28',plain,(
    ! [X9: $i] :
      ( r1_tarski @ X9 @ X9 ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( r1_tarski @ X45 @ ( k1_relat_1 @ X46 ) )
      | ( r1_tarski @ X45 @ ( k10_relat_1 @ X46 @ ( k9_relat_1 @ X46 @ X45 ) ) )
      | ~ ( v1_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t146_funct_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('31',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X13 @ X14 )
      | ~ ( r1_tarski @ X14 @ X15 )
      | ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( r1_tarski @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X32: $i,X33: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X32 @ X33 ) @ ( k1_relat_1 @ X32 ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('36',plain,(
    ! [X8: $i,X10: $i] :
      ( ( X8 = X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ X1 ) )
      | ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X34: $i,X35: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X34 @ X35 ) @ ( k10_relat_1 @ X34 @ ( k2_relat_1 @ X34 ) ) )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t170_relat_1])).

thf('41',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('42',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X13 @ X14 )
      | ~ ( r1_tarski @ X14 @ X15 )
      | ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ~ ( r1_tarski @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('47',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_xboole_0 @ X12 @ X11 )
        = X11 )
      | ~ ( r1_tarski @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('48',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) )
    = ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( ( k2_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) )
      = ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['39','48'])).

thf('50',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_xboole_0 @ X12 @ X11 )
        = X11 )
      | ~ ( r1_tarski @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('52',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['49','52','53'])).

thf('55',plain,(
    ! [X9: $i] :
      ( r1_tarski @ X9 @ X9 ) ),
    inference(simplify,[status(thm)],['27'])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('56',plain,(
    ! [X47: $i,X48: $i] :
      ( ~ ( r1_tarski @ X47 @ ( k2_relat_1 @ X48 ) )
      | ( ( k9_relat_1 @ X48 @ ( k10_relat_1 @ X48 @ X47 ) )
        = X47 )
      | ~ ( v1_funct_1 @ X48 )
      | ~ ( v1_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( ( k9_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) )
      = ( k2_relat_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['54','57'])).

thf('59',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( k9_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) )
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf(t148_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('62',plain,(
    ! [X49: $i,X50: $i] :
      ( ( ( k9_relat_1 @ X50 @ ( k10_relat_1 @ X50 @ X49 ) )
        = ( k3_xboole_0 @ X49 @ ( k9_relat_1 @ X50 @ ( k1_relat_1 @ X50 ) ) ) )
      | ~ ( v1_funct_1 @ X50 )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t148_funct_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ X0 ) )
        = ( k3_xboole_0 @ X0 @ ( k2_relat_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ X0 ) )
      = ( k3_xboole_0 @ X0 @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf(t157_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) )
          & ( r1_tarski @ A @ ( k1_relat_1 @ C ) )
          & ( v2_funct_1 @ C ) )
       => ( r1_tarski @ A @ B ) ) ) )).

thf('67',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ( r1_tarski @ X51 @ X52 )
      | ~ ( v1_relat_1 @ X53 )
      | ~ ( v1_funct_1 @ X53 )
      | ~ ( v2_funct_1 @ X53 )
      | ~ ( r1_tarski @ X51 @ ( k1_relat_1 @ X53 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X53 @ X51 ) @ ( k9_relat_1 @ X53 @ X52 ) ) ) ),
    inference(cnf,[status(esa)],[t157_funct_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ X0 @ ( k2_relat_1 @ sk_B ) ) @ ( k9_relat_1 @ sk_B @ X1 ) )
      | ~ ( r1_tarski @ ( k10_relat_1 @ sk_B @ X0 ) @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v2_funct_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B )
      | ( r1_tarski @ ( k10_relat_1 @ sk_B @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['49','52','53'])).

thf('70',plain,(
    ! [X34: $i,X35: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X34 @ X35 ) @ ( k10_relat_1 @ X34 @ ( k2_relat_1 @ X34 ) ) )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t170_relat_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ sk_B @ X0 ) @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k10_relat_1 @ sk_B @ X0 ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ X0 @ ( k2_relat_1 @ sk_B ) ) @ ( k9_relat_1 @ sk_B @ X1 ) )
      | ( r1_tarski @ ( k10_relat_1 @ sk_B @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['68','73','74','75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ X0 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['25','77'])).

thf('79',plain,(
    $false ),
    inference(demod,[status(thm)],['8','78'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aJ4AYkmWkJ
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:45:24 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 1.14/1.32  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.14/1.32  % Solved by: fo/fo7.sh
% 1.14/1.32  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.14/1.32  % done 2718 iterations in 0.868s
% 1.14/1.32  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.14/1.32  % SZS output start Refutation
% 1.14/1.32  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 1.14/1.32  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.14/1.32  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.14/1.32  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.14/1.32  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.14/1.32  thf(sk_B_type, type, sk_B: $i).
% 1.14/1.32  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.14/1.32  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.14/1.32  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 1.14/1.32  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.14/1.32  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.14/1.32  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.14/1.32  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.14/1.32  thf(sk_A_type, type, sk_A: $i).
% 1.14/1.32  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.14/1.32  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.14/1.32  thf(t164_funct_1, conjecture,
% 1.14/1.32    (![A:$i,B:$i]:
% 1.14/1.32     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.14/1.32       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & ( v2_funct_1 @ B ) ) =>
% 1.14/1.32         ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 1.14/1.32  thf(zf_stmt_0, negated_conjecture,
% 1.14/1.32    (~( ![A:$i,B:$i]:
% 1.14/1.32        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.14/1.32          ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & ( v2_funct_1 @ B ) ) =>
% 1.14/1.32            ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) = ( A ) ) ) ) )),
% 1.14/1.32    inference('cnf.neg', [status(esa)], [t164_funct_1])).
% 1.14/1.32  thf('0', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 1.14/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.32  thf(t146_funct_1, axiom,
% 1.14/1.32    (![A:$i,B:$i]:
% 1.14/1.32     ( ( v1_relat_1 @ B ) =>
% 1.14/1.32       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 1.14/1.32         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 1.14/1.32  thf('1', plain,
% 1.14/1.32      (![X45 : $i, X46 : $i]:
% 1.14/1.32         (~ (r1_tarski @ X45 @ (k1_relat_1 @ X46))
% 1.14/1.32          | (r1_tarski @ X45 @ (k10_relat_1 @ X46 @ (k9_relat_1 @ X46 @ X45)))
% 1.14/1.32          | ~ (v1_relat_1 @ X46))),
% 1.14/1.32      inference('cnf', [status(esa)], [t146_funct_1])).
% 1.14/1.32  thf('2', plain,
% 1.14/1.32      ((~ (v1_relat_1 @ sk_B)
% 1.14/1.32        | (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A))))),
% 1.14/1.32      inference('sup-', [status(thm)], ['0', '1'])).
% 1.14/1.32  thf('3', plain, ((v1_relat_1 @ sk_B)),
% 1.14/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.32  thf('4', plain,
% 1.14/1.32      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 1.14/1.32      inference('demod', [status(thm)], ['2', '3'])).
% 1.14/1.32  thf(d10_xboole_0, axiom,
% 1.14/1.32    (![A:$i,B:$i]:
% 1.14/1.32     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.14/1.32  thf('5', plain,
% 1.14/1.32      (![X8 : $i, X10 : $i]:
% 1.14/1.32         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 1.14/1.32      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.14/1.32  thf('6', plain,
% 1.14/1.32      ((~ (r1_tarski @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) @ sk_A)
% 1.14/1.32        | ((k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) = (sk_A)))),
% 1.14/1.32      inference('sup-', [status(thm)], ['4', '5'])).
% 1.14/1.32  thf('7', plain,
% 1.14/1.32      (((k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) != (sk_A))),
% 1.14/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.32  thf('8', plain,
% 1.14/1.32      (~ (r1_tarski @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) @ sk_A)),
% 1.14/1.32      inference('simplify_reflect-', [status(thm)], ['6', '7'])).
% 1.14/1.32  thf(commutativity_k2_tarski, axiom,
% 1.14/1.32    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 1.14/1.32  thf('9', plain,
% 1.14/1.32      (![X19 : $i, X20 : $i]:
% 1.14/1.32         ((k2_tarski @ X20 @ X19) = (k2_tarski @ X19 @ X20))),
% 1.14/1.32      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.14/1.32  thf(t12_setfam_1, axiom,
% 1.14/1.32    (![A:$i,B:$i]:
% 1.14/1.32     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.14/1.32  thf('10', plain,
% 1.14/1.32      (![X26 : $i, X27 : $i]:
% 1.14/1.32         ((k1_setfam_1 @ (k2_tarski @ X26 @ X27)) = (k3_xboole_0 @ X26 @ X27))),
% 1.14/1.32      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.14/1.32  thf('11', plain,
% 1.14/1.32      (![X0 : $i, X1 : $i]:
% 1.14/1.32         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 1.14/1.32      inference('sup+', [status(thm)], ['9', '10'])).
% 1.14/1.32  thf('12', plain,
% 1.14/1.32      (![X26 : $i, X27 : $i]:
% 1.14/1.32         ((k1_setfam_1 @ (k2_tarski @ X26 @ X27)) = (k3_xboole_0 @ X26 @ X27))),
% 1.14/1.32      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.14/1.32  thf('13', plain,
% 1.14/1.32      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.14/1.32      inference('sup+', [status(thm)], ['11', '12'])).
% 1.14/1.32  thf(t43_funct_1, axiom,
% 1.14/1.32    (![A:$i,B:$i]:
% 1.14/1.32     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 1.14/1.32       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.14/1.32  thf('14', plain,
% 1.14/1.32      (![X54 : $i, X55 : $i]:
% 1.14/1.32         ((k5_relat_1 @ (k6_relat_1 @ X55) @ (k6_relat_1 @ X54))
% 1.14/1.32           = (k6_relat_1 @ (k3_xboole_0 @ X54 @ X55)))),
% 1.14/1.32      inference('cnf', [status(esa)], [t43_funct_1])).
% 1.14/1.32  thf(t182_relat_1, axiom,
% 1.14/1.32    (![A:$i]:
% 1.14/1.32     ( ( v1_relat_1 @ A ) =>
% 1.14/1.32       ( ![B:$i]:
% 1.14/1.32         ( ( v1_relat_1 @ B ) =>
% 1.14/1.32           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 1.14/1.32             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 1.14/1.32  thf('15', plain,
% 1.14/1.32      (![X39 : $i, X40 : $i]:
% 1.14/1.32         (~ (v1_relat_1 @ X39)
% 1.14/1.32          | ((k1_relat_1 @ (k5_relat_1 @ X40 @ X39))
% 1.14/1.32              = (k10_relat_1 @ X40 @ (k1_relat_1 @ X39)))
% 1.14/1.32          | ~ (v1_relat_1 @ X40))),
% 1.14/1.32      inference('cnf', [status(esa)], [t182_relat_1])).
% 1.14/1.32  thf(t167_relat_1, axiom,
% 1.14/1.32    (![A:$i,B:$i]:
% 1.14/1.32     ( ( v1_relat_1 @ B ) =>
% 1.14/1.32       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 1.14/1.32  thf('16', plain,
% 1.14/1.32      (![X32 : $i, X33 : $i]:
% 1.14/1.32         ((r1_tarski @ (k10_relat_1 @ X32 @ X33) @ (k1_relat_1 @ X32))
% 1.14/1.32          | ~ (v1_relat_1 @ X32))),
% 1.14/1.32      inference('cnf', [status(esa)], [t167_relat_1])).
% 1.14/1.32  thf('17', plain,
% 1.14/1.32      (![X0 : $i, X1 : $i]:
% 1.14/1.32         ((r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X1 @ X0)) @ 
% 1.14/1.32           (k1_relat_1 @ X1))
% 1.14/1.32          | ~ (v1_relat_1 @ X1)
% 1.14/1.32          | ~ (v1_relat_1 @ X0)
% 1.14/1.32          | ~ (v1_relat_1 @ X1))),
% 1.14/1.32      inference('sup+', [status(thm)], ['15', '16'])).
% 1.14/1.32  thf('18', plain,
% 1.14/1.32      (![X0 : $i, X1 : $i]:
% 1.14/1.32         (~ (v1_relat_1 @ X0)
% 1.14/1.32          | ~ (v1_relat_1 @ X1)
% 1.14/1.32          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X1 @ X0)) @ 
% 1.14/1.32             (k1_relat_1 @ X1)))),
% 1.14/1.32      inference('simplify', [status(thm)], ['17'])).
% 1.14/1.32  thf('19', plain,
% 1.14/1.32      (![X0 : $i, X1 : $i]:
% 1.14/1.32         ((r1_tarski @ (k1_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))) @ 
% 1.14/1.32           (k1_relat_1 @ (k6_relat_1 @ X0)))
% 1.14/1.32          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 1.14/1.32          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 1.14/1.32      inference('sup+', [status(thm)], ['14', '18'])).
% 1.14/1.32  thf(t71_relat_1, axiom,
% 1.14/1.32    (![A:$i]:
% 1.14/1.32     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 1.14/1.32       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 1.14/1.32  thf('20', plain, (![X41 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X41)) = (X41))),
% 1.14/1.32      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.14/1.32  thf('21', plain, (![X41 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X41)) = (X41))),
% 1.14/1.32      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.14/1.32  thf(fc4_funct_1, axiom,
% 1.14/1.32    (![A:$i]:
% 1.14/1.32     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 1.14/1.32       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 1.14/1.32  thf('22', plain, (![X43 : $i]: (v1_relat_1 @ (k6_relat_1 @ X43))),
% 1.14/1.32      inference('cnf', [status(esa)], [fc4_funct_1])).
% 1.14/1.32  thf('23', plain, (![X43 : $i]: (v1_relat_1 @ (k6_relat_1 @ X43))),
% 1.14/1.32      inference('cnf', [status(esa)], [fc4_funct_1])).
% 1.14/1.32  thf('24', plain,
% 1.14/1.32      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 1.14/1.32      inference('demod', [status(thm)], ['19', '20', '21', '22', '23'])).
% 1.14/1.32  thf('25', plain,
% 1.14/1.32      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 1.14/1.32      inference('sup+', [status(thm)], ['13', '24'])).
% 1.14/1.32  thf(t170_relat_1, axiom,
% 1.14/1.32    (![A:$i,B:$i]:
% 1.14/1.32     ( ( v1_relat_1 @ B ) =>
% 1.14/1.32       ( r1_tarski @
% 1.14/1.32         ( k10_relat_1 @ B @ A ) @ ( k10_relat_1 @ B @ ( k2_relat_1 @ B ) ) ) ))).
% 1.14/1.32  thf('26', plain,
% 1.14/1.32      (![X34 : $i, X35 : $i]:
% 1.14/1.32         ((r1_tarski @ (k10_relat_1 @ X34 @ X35) @ 
% 1.14/1.32           (k10_relat_1 @ X34 @ (k2_relat_1 @ X34)))
% 1.14/1.32          | ~ (v1_relat_1 @ X34))),
% 1.14/1.32      inference('cnf', [status(esa)], [t170_relat_1])).
% 1.14/1.32  thf('27', plain,
% 1.14/1.32      (![X8 : $i, X9 : $i]: ((r1_tarski @ X8 @ X9) | ((X8) != (X9)))),
% 1.14/1.32      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.14/1.32  thf('28', plain, (![X9 : $i]: (r1_tarski @ X9 @ X9)),
% 1.14/1.32      inference('simplify', [status(thm)], ['27'])).
% 1.14/1.32  thf('29', plain,
% 1.14/1.32      (![X45 : $i, X46 : $i]:
% 1.14/1.32         (~ (r1_tarski @ X45 @ (k1_relat_1 @ X46))
% 1.14/1.32          | (r1_tarski @ X45 @ (k10_relat_1 @ X46 @ (k9_relat_1 @ X46 @ X45)))
% 1.14/1.32          | ~ (v1_relat_1 @ X46))),
% 1.14/1.32      inference('cnf', [status(esa)], [t146_funct_1])).
% 1.14/1.32  thf('30', plain,
% 1.14/1.32      (![X0 : $i]:
% 1.14/1.32         (~ (v1_relat_1 @ X0)
% 1.14/1.32          | (r1_tarski @ (k1_relat_1 @ X0) @ 
% 1.14/1.32             (k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))))),
% 1.14/1.32      inference('sup-', [status(thm)], ['28', '29'])).
% 1.14/1.32  thf(t1_xboole_1, axiom,
% 1.14/1.32    (![A:$i,B:$i,C:$i]:
% 1.14/1.32     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 1.14/1.32       ( r1_tarski @ A @ C ) ))).
% 1.14/1.32  thf('31', plain,
% 1.14/1.32      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.14/1.32         (~ (r1_tarski @ X13 @ X14)
% 1.14/1.32          | ~ (r1_tarski @ X14 @ X15)
% 1.14/1.32          | (r1_tarski @ X13 @ X15))),
% 1.14/1.32      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.14/1.32  thf('32', plain,
% 1.14/1.32      (![X0 : $i, X1 : $i]:
% 1.14/1.32         (~ (v1_relat_1 @ X0)
% 1.14/1.32          | (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 1.14/1.32          | ~ (r1_tarski @ 
% 1.14/1.32               (k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0))) @ X1))),
% 1.14/1.32      inference('sup-', [status(thm)], ['30', '31'])).
% 1.14/1.32  thf('33', plain,
% 1.14/1.32      (![X0 : $i]:
% 1.14/1.32         (~ (v1_relat_1 @ X0)
% 1.14/1.32          | (r1_tarski @ (k1_relat_1 @ X0) @ 
% 1.14/1.32             (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 1.14/1.32          | ~ (v1_relat_1 @ X0))),
% 1.14/1.32      inference('sup-', [status(thm)], ['26', '32'])).
% 1.14/1.32  thf('34', plain,
% 1.14/1.32      (![X0 : $i]:
% 1.14/1.32         ((r1_tarski @ (k1_relat_1 @ X0) @ 
% 1.14/1.32           (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 1.14/1.32          | ~ (v1_relat_1 @ X0))),
% 1.14/1.32      inference('simplify', [status(thm)], ['33'])).
% 1.14/1.32  thf('35', plain,
% 1.14/1.32      (![X32 : $i, X33 : $i]:
% 1.14/1.32         ((r1_tarski @ (k10_relat_1 @ X32 @ X33) @ (k1_relat_1 @ X32))
% 1.14/1.32          | ~ (v1_relat_1 @ X32))),
% 1.14/1.32      inference('cnf', [status(esa)], [t167_relat_1])).
% 1.14/1.32  thf('36', plain,
% 1.14/1.32      (![X8 : $i, X10 : $i]:
% 1.14/1.32         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 1.14/1.32      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.14/1.32  thf('37', plain,
% 1.14/1.32      (![X0 : $i, X1 : $i]:
% 1.14/1.32         (~ (v1_relat_1 @ X0)
% 1.14/1.32          | ~ (r1_tarski @ (k1_relat_1 @ X0) @ (k10_relat_1 @ X0 @ X1))
% 1.14/1.32          | ((k1_relat_1 @ X0) = (k10_relat_1 @ X0 @ X1)))),
% 1.14/1.32      inference('sup-', [status(thm)], ['35', '36'])).
% 1.14/1.32  thf('38', plain,
% 1.14/1.32      (![X0 : $i]:
% 1.14/1.32         (~ (v1_relat_1 @ X0)
% 1.14/1.32          | ((k1_relat_1 @ X0) = (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 1.14/1.32          | ~ (v1_relat_1 @ X0))),
% 1.14/1.32      inference('sup-', [status(thm)], ['34', '37'])).
% 1.14/1.32  thf('39', plain,
% 1.14/1.32      (![X0 : $i]:
% 1.14/1.32         (((k1_relat_1 @ X0) = (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 1.14/1.32          | ~ (v1_relat_1 @ X0))),
% 1.14/1.32      inference('simplify', [status(thm)], ['38'])).
% 1.14/1.32  thf('40', plain,
% 1.14/1.32      (![X34 : $i, X35 : $i]:
% 1.14/1.32         ((r1_tarski @ (k10_relat_1 @ X34 @ X35) @ 
% 1.14/1.32           (k10_relat_1 @ X34 @ (k2_relat_1 @ X34)))
% 1.14/1.32          | ~ (v1_relat_1 @ X34))),
% 1.14/1.32      inference('cnf', [status(esa)], [t170_relat_1])).
% 1.14/1.32  thf('41', plain,
% 1.14/1.32      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 1.14/1.32      inference('demod', [status(thm)], ['2', '3'])).
% 1.14/1.32  thf('42', plain,
% 1.14/1.32      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.14/1.32         (~ (r1_tarski @ X13 @ X14)
% 1.14/1.32          | ~ (r1_tarski @ X14 @ X15)
% 1.14/1.32          | (r1_tarski @ X13 @ X15))),
% 1.14/1.32      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.14/1.32  thf('43', plain,
% 1.14/1.32      (![X0 : $i]:
% 1.14/1.32         ((r1_tarski @ sk_A @ X0)
% 1.14/1.32          | ~ (r1_tarski @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) @ 
% 1.14/1.32               X0))),
% 1.14/1.32      inference('sup-', [status(thm)], ['41', '42'])).
% 1.14/1.32  thf('44', plain,
% 1.14/1.32      ((~ (v1_relat_1 @ sk_B)
% 1.14/1.32        | (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B))))),
% 1.14/1.32      inference('sup-', [status(thm)], ['40', '43'])).
% 1.14/1.32  thf('45', plain, ((v1_relat_1 @ sk_B)),
% 1.14/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.32  thf('46', plain,
% 1.14/1.32      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B)))),
% 1.14/1.32      inference('demod', [status(thm)], ['44', '45'])).
% 1.14/1.32  thf(t12_xboole_1, axiom,
% 1.14/1.32    (![A:$i,B:$i]:
% 1.14/1.32     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 1.14/1.32  thf('47', plain,
% 1.14/1.32      (![X11 : $i, X12 : $i]:
% 1.14/1.32         (((k2_xboole_0 @ X12 @ X11) = (X11)) | ~ (r1_tarski @ X12 @ X11))),
% 1.14/1.32      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.14/1.32  thf('48', plain,
% 1.14/1.32      (((k2_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B)))
% 1.14/1.32         = (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B)))),
% 1.14/1.32      inference('sup-', [status(thm)], ['46', '47'])).
% 1.14/1.32  thf('49', plain,
% 1.14/1.32      ((((k2_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B))
% 1.14/1.32          = (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B)))
% 1.14/1.32        | ~ (v1_relat_1 @ sk_B))),
% 1.14/1.32      inference('sup+', [status(thm)], ['39', '48'])).
% 1.14/1.32  thf('50', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 1.14/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.32  thf('51', plain,
% 1.14/1.32      (![X11 : $i, X12 : $i]:
% 1.14/1.32         (((k2_xboole_0 @ X12 @ X11) = (X11)) | ~ (r1_tarski @ X12 @ X11))),
% 1.14/1.32      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.14/1.32  thf('52', plain,
% 1.14/1.32      (((k2_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)) = (k1_relat_1 @ sk_B))),
% 1.14/1.32      inference('sup-', [status(thm)], ['50', '51'])).
% 1.14/1.32  thf('53', plain, ((v1_relat_1 @ sk_B)),
% 1.14/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.32  thf('54', plain,
% 1.14/1.32      (((k1_relat_1 @ sk_B) = (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B)))),
% 1.14/1.32      inference('demod', [status(thm)], ['49', '52', '53'])).
% 1.14/1.32  thf('55', plain, (![X9 : $i]: (r1_tarski @ X9 @ X9)),
% 1.14/1.32      inference('simplify', [status(thm)], ['27'])).
% 1.14/1.32  thf(t147_funct_1, axiom,
% 1.14/1.32    (![A:$i,B:$i]:
% 1.14/1.32     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.14/1.32       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 1.14/1.32         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 1.14/1.32  thf('56', plain,
% 1.14/1.32      (![X47 : $i, X48 : $i]:
% 1.14/1.32         (~ (r1_tarski @ X47 @ (k2_relat_1 @ X48))
% 1.14/1.32          | ((k9_relat_1 @ X48 @ (k10_relat_1 @ X48 @ X47)) = (X47))
% 1.14/1.32          | ~ (v1_funct_1 @ X48)
% 1.14/1.32          | ~ (v1_relat_1 @ X48))),
% 1.14/1.32      inference('cnf', [status(esa)], [t147_funct_1])).
% 1.14/1.32  thf('57', plain,
% 1.14/1.32      (![X0 : $i]:
% 1.14/1.32         (~ (v1_relat_1 @ X0)
% 1.14/1.32          | ~ (v1_funct_1 @ X0)
% 1.14/1.32          | ((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 1.14/1.32              = (k2_relat_1 @ X0)))),
% 1.14/1.32      inference('sup-', [status(thm)], ['55', '56'])).
% 1.14/1.32  thf('58', plain,
% 1.14/1.32      ((((k9_relat_1 @ sk_B @ (k1_relat_1 @ sk_B)) = (k2_relat_1 @ sk_B))
% 1.14/1.32        | ~ (v1_funct_1 @ sk_B)
% 1.14/1.32        | ~ (v1_relat_1 @ sk_B))),
% 1.14/1.32      inference('sup+', [status(thm)], ['54', '57'])).
% 1.14/1.32  thf('59', plain, ((v1_funct_1 @ sk_B)),
% 1.14/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.32  thf('60', plain, ((v1_relat_1 @ sk_B)),
% 1.14/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.32  thf('61', plain,
% 1.14/1.32      (((k9_relat_1 @ sk_B @ (k1_relat_1 @ sk_B)) = (k2_relat_1 @ sk_B))),
% 1.14/1.32      inference('demod', [status(thm)], ['58', '59', '60'])).
% 1.14/1.32  thf(t148_funct_1, axiom,
% 1.14/1.32    (![A:$i,B:$i]:
% 1.14/1.32     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.14/1.32       ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) =
% 1.14/1.32         ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ))).
% 1.14/1.32  thf('62', plain,
% 1.14/1.32      (![X49 : $i, X50 : $i]:
% 1.14/1.32         (((k9_relat_1 @ X50 @ (k10_relat_1 @ X50 @ X49))
% 1.14/1.32            = (k3_xboole_0 @ X49 @ (k9_relat_1 @ X50 @ (k1_relat_1 @ X50))))
% 1.14/1.32          | ~ (v1_funct_1 @ X50)
% 1.14/1.32          | ~ (v1_relat_1 @ X50))),
% 1.14/1.32      inference('cnf', [status(esa)], [t148_funct_1])).
% 1.14/1.32  thf('63', plain,
% 1.14/1.32      (![X0 : $i]:
% 1.14/1.32         (((k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ X0))
% 1.14/1.32            = (k3_xboole_0 @ X0 @ (k2_relat_1 @ sk_B)))
% 1.14/1.32          | ~ (v1_relat_1 @ sk_B)
% 1.14/1.32          | ~ (v1_funct_1 @ sk_B))),
% 1.14/1.32      inference('sup+', [status(thm)], ['61', '62'])).
% 1.14/1.32  thf('64', plain, ((v1_relat_1 @ sk_B)),
% 1.14/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.32  thf('65', plain, ((v1_funct_1 @ sk_B)),
% 1.14/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.32  thf('66', plain,
% 1.14/1.32      (![X0 : $i]:
% 1.14/1.32         ((k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ X0))
% 1.14/1.32           = (k3_xboole_0 @ X0 @ (k2_relat_1 @ sk_B)))),
% 1.14/1.32      inference('demod', [status(thm)], ['63', '64', '65'])).
% 1.14/1.32  thf(t157_funct_1, axiom,
% 1.14/1.32    (![A:$i,B:$i,C:$i]:
% 1.14/1.32     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 1.14/1.32       ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) & 
% 1.14/1.32           ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & ( v2_funct_1 @ C ) ) =>
% 1.14/1.32         ( r1_tarski @ A @ B ) ) ))).
% 1.14/1.32  thf('67', plain,
% 1.14/1.32      (![X51 : $i, X52 : $i, X53 : $i]:
% 1.14/1.32         ((r1_tarski @ X51 @ X52)
% 1.14/1.32          | ~ (v1_relat_1 @ X53)
% 1.14/1.32          | ~ (v1_funct_1 @ X53)
% 1.14/1.32          | ~ (v2_funct_1 @ X53)
% 1.14/1.32          | ~ (r1_tarski @ X51 @ (k1_relat_1 @ X53))
% 1.14/1.32          | ~ (r1_tarski @ (k9_relat_1 @ X53 @ X51) @ (k9_relat_1 @ X53 @ X52)))),
% 1.14/1.32      inference('cnf', [status(esa)], [t157_funct_1])).
% 1.14/1.32  thf('68', plain,
% 1.14/1.32      (![X0 : $i, X1 : $i]:
% 1.14/1.32         (~ (r1_tarski @ (k3_xboole_0 @ X0 @ (k2_relat_1 @ sk_B)) @ 
% 1.14/1.32             (k9_relat_1 @ sk_B @ X1))
% 1.14/1.32          | ~ (r1_tarski @ (k10_relat_1 @ sk_B @ X0) @ (k1_relat_1 @ sk_B))
% 1.14/1.32          | ~ (v2_funct_1 @ sk_B)
% 1.14/1.32          | ~ (v1_funct_1 @ sk_B)
% 1.14/1.32          | ~ (v1_relat_1 @ sk_B)
% 1.14/1.32          | (r1_tarski @ (k10_relat_1 @ sk_B @ X0) @ X1))),
% 1.14/1.32      inference('sup-', [status(thm)], ['66', '67'])).
% 1.14/1.32  thf('69', plain,
% 1.14/1.32      (((k1_relat_1 @ sk_B) = (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B)))),
% 1.14/1.32      inference('demod', [status(thm)], ['49', '52', '53'])).
% 1.14/1.32  thf('70', plain,
% 1.14/1.32      (![X34 : $i, X35 : $i]:
% 1.14/1.32         ((r1_tarski @ (k10_relat_1 @ X34 @ X35) @ 
% 1.14/1.32           (k10_relat_1 @ X34 @ (k2_relat_1 @ X34)))
% 1.14/1.32          | ~ (v1_relat_1 @ X34))),
% 1.14/1.32      inference('cnf', [status(esa)], [t170_relat_1])).
% 1.14/1.32  thf('71', plain,
% 1.14/1.32      (![X0 : $i]:
% 1.14/1.32         ((r1_tarski @ (k10_relat_1 @ sk_B @ X0) @ (k1_relat_1 @ sk_B))
% 1.14/1.32          | ~ (v1_relat_1 @ sk_B))),
% 1.14/1.32      inference('sup+', [status(thm)], ['69', '70'])).
% 1.14/1.32  thf('72', plain, ((v1_relat_1 @ sk_B)),
% 1.14/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.32  thf('73', plain,
% 1.14/1.32      (![X0 : $i]:
% 1.14/1.32         (r1_tarski @ (k10_relat_1 @ sk_B @ X0) @ (k1_relat_1 @ sk_B))),
% 1.14/1.32      inference('demod', [status(thm)], ['71', '72'])).
% 1.14/1.32  thf('74', plain, ((v2_funct_1 @ sk_B)),
% 1.14/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.32  thf('75', plain, ((v1_funct_1 @ sk_B)),
% 1.14/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.32  thf('76', plain, ((v1_relat_1 @ sk_B)),
% 1.14/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.32  thf('77', plain,
% 1.14/1.32      (![X0 : $i, X1 : $i]:
% 1.14/1.32         (~ (r1_tarski @ (k3_xboole_0 @ X0 @ (k2_relat_1 @ sk_B)) @ 
% 1.14/1.32             (k9_relat_1 @ sk_B @ X1))
% 1.14/1.32          | (r1_tarski @ (k10_relat_1 @ sk_B @ X0) @ X1))),
% 1.14/1.32      inference('demod', [status(thm)], ['68', '73', '74', '75', '76'])).
% 1.14/1.32  thf('78', plain,
% 1.14/1.32      (![X0 : $i]:
% 1.14/1.32         (r1_tarski @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ X0)) @ X0)),
% 1.14/1.32      inference('sup-', [status(thm)], ['25', '77'])).
% 1.14/1.32  thf('79', plain, ($false), inference('demod', [status(thm)], ['8', '78'])).
% 1.14/1.32  
% 1.14/1.32  % SZS output end Refutation
% 1.14/1.32  
% 1.14/1.33  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
