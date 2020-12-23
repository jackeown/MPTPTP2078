%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CMMfy8aAsX

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:18 EST 2020

% Result     : Theorem 0.75s
% Output     : Refutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 210 expanded)
%              Number of leaves         :   32 (  77 expanded)
%              Depth                    :   20
%              Number of atoms          :  698 (1666 expanded)
%              Number of equality atoms :   51 ( 112 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

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

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t162_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( r1_tarski @ B @ C )
         => ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B )
            = ( k9_relat_1 @ A @ B ) ) ) ) )).

thf('3',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( r1_tarski @ X24 @ X25 )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X26 @ X25 ) @ X24 )
        = ( k9_relat_1 @ X26 @ X24 ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t162_relat_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X0 )
        = ( k9_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ X15 @ ( k2_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('7',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('8',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('11',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      | ~ ( r1_tarski @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('13',plain,(
    ! [X8: $i] :
      ( r1_tarski @ k1_xboole_0 @ X8 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('14',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['12','15'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('17',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('18',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('19',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('20',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('21',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_tarski @ X18 @ X17 )
      = ( k2_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('22',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('26',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X28 @ X29 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X28 ) @ X29 ) )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf(t139_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('27',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X31 @ X30 ) @ X32 )
        = ( k3_xboole_0 @ X30 @ ( k10_relat_1 @ X31 @ X32 ) ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('28',plain,(
    ! [X27: $i] :
      ( ( ( k10_relat_1 @ X27 @ ( k2_relat_1 @ X27 ) )
        = ( k1_relat_1 @ X27 ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('34',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ X15 @ ( k2_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      | ~ ( r1_tarski @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['32','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['31','38'])).

thf('40',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ( X0
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( X0
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['26','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ X0 @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k3_xboole_0 @ X1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( X1
        = ( k1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['25','43'])).

thf('45',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['20','44'])).

thf('46',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['1'])).

thf('47',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( sk_A
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('49',plain,(
    ! [X23: $i] :
      ( ( ( k9_relat_1 @ X23 @ ( k1_relat_1 @ X23 ) )
        = ( k2_relat_1 @ X23 ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('50',plain,
    ( ( ( k9_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ sk_A )
      = ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( k9_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ sk_A )
      = ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['5','50'])).

thf('52',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( k9_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ sk_A )
    = ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( ( k9_relat_1 @ sk_B @ sk_A )
      = ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['4','53'])).

thf('55',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( k9_relat_1 @ sk_B @ sk_A )
    = ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('58',plain,
    ( ( ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,
    ( sk_A
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('60',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    = sk_A ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['32','37'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['61','64'])).

thf('66',plain,(
    $false ),
    inference(demod,[status(thm)],['0','65'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CMMfy8aAsX
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:59:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.75/0.96  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.75/0.96  % Solved by: fo/fo7.sh
% 0.75/0.96  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.75/0.96  % done 1387 iterations in 0.482s
% 0.75/0.96  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.75/0.96  % SZS output start Refutation
% 0.75/0.96  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.75/0.96  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.75/0.96  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.75/0.96  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.75/0.96  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.75/0.96  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.75/0.96  thf(sk_B_type, type, sk_B: $i).
% 0.75/0.96  thf(sk_A_type, type, sk_A: $i).
% 0.75/0.96  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.75/0.96  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.75/0.96  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.75/0.96  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.75/0.96  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.75/0.96  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.75/0.96  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.75/0.96  thf(t146_funct_1, conjecture,
% 0.75/0.96    (![A:$i,B:$i]:
% 0.75/0.96     ( ( v1_relat_1 @ B ) =>
% 0.75/0.96       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.75/0.96         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 0.75/0.96  thf(zf_stmt_0, negated_conjecture,
% 0.75/0.96    (~( ![A:$i,B:$i]:
% 0.75/0.96        ( ( v1_relat_1 @ B ) =>
% 0.75/0.96          ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.75/0.96            ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )),
% 0.75/0.96    inference('cnf.neg', [status(esa)], [t146_funct_1])).
% 0.75/0.96  thf('0', plain,
% 0.75/0.96      (~ (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf(d10_xboole_0, axiom,
% 0.75/0.96    (![A:$i,B:$i]:
% 0.75/0.96     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.75/0.96  thf('1', plain,
% 0.75/0.96      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 0.75/0.96      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.75/0.96  thf('2', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.75/0.96      inference('simplify', [status(thm)], ['1'])).
% 0.75/0.96  thf(t162_relat_1, axiom,
% 0.75/0.96    (![A:$i]:
% 0.75/0.96     ( ( v1_relat_1 @ A ) =>
% 0.75/0.96       ( ![B:$i,C:$i]:
% 0.75/0.96         ( ( r1_tarski @ B @ C ) =>
% 0.75/0.96           ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B ) =
% 0.75/0.96             ( k9_relat_1 @ A @ B ) ) ) ) ))).
% 0.75/0.96  thf('3', plain,
% 0.75/0.96      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.75/0.96         (~ (r1_tarski @ X24 @ X25)
% 0.75/0.96          | ((k9_relat_1 @ (k7_relat_1 @ X26 @ X25) @ X24)
% 0.75/0.96              = (k9_relat_1 @ X26 @ X24))
% 0.75/0.96          | ~ (v1_relat_1 @ X26))),
% 0.75/0.96      inference('cnf', [status(esa)], [t162_relat_1])).
% 0.75/0.96  thf('4', plain,
% 0.75/0.96      (![X0 : $i, X1 : $i]:
% 0.75/0.96         (~ (v1_relat_1 @ X1)
% 0.75/0.96          | ((k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X0)
% 0.75/0.96              = (k9_relat_1 @ X1 @ X0)))),
% 0.75/0.96      inference('sup-', [status(thm)], ['2', '3'])).
% 0.75/0.96  thf(dt_k7_relat_1, axiom,
% 0.75/0.96    (![A:$i,B:$i]:
% 0.75/0.96     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.75/0.96  thf('5', plain,
% 0.75/0.96      (![X21 : $i, X22 : $i]:
% 0.75/0.96         (~ (v1_relat_1 @ X21) | (v1_relat_1 @ (k7_relat_1 @ X21 @ X22)))),
% 0.75/0.96      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.75/0.96  thf(t7_xboole_1, axiom,
% 0.75/0.96    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.75/0.96  thf('6', plain,
% 0.75/0.96      (![X15 : $i, X16 : $i]: (r1_tarski @ X15 @ (k2_xboole_0 @ X15 @ X16))),
% 0.75/0.96      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.75/0.96  thf('7', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf(t1_xboole_1, axiom,
% 0.75/0.96    (![A:$i,B:$i,C:$i]:
% 0.75/0.96     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.75/0.96       ( r1_tarski @ A @ C ) ))).
% 0.75/0.96  thf('8', plain,
% 0.75/0.96      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.75/0.96         (~ (r1_tarski @ X5 @ X6)
% 0.75/0.96          | ~ (r1_tarski @ X6 @ X7)
% 0.75/0.96          | (r1_tarski @ X5 @ X7))),
% 0.75/0.96      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.75/0.96  thf('9', plain,
% 0.75/0.96      (![X0 : $i]:
% 0.75/0.96         ((r1_tarski @ sk_A @ X0) | ~ (r1_tarski @ (k1_relat_1 @ sk_B) @ X0))),
% 0.75/0.96      inference('sup-', [status(thm)], ['7', '8'])).
% 0.75/0.96  thf('10', plain,
% 0.75/0.96      (![X0 : $i]:
% 0.75/0.96         (r1_tarski @ sk_A @ (k2_xboole_0 @ (k1_relat_1 @ sk_B) @ X0))),
% 0.75/0.96      inference('sup-', [status(thm)], ['6', '9'])).
% 0.75/0.96  thf(t43_xboole_1, axiom,
% 0.75/0.96    (![A:$i,B:$i,C:$i]:
% 0.75/0.96     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 0.75/0.96       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 0.75/0.96  thf('11', plain,
% 0.75/0.96      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.75/0.96         ((r1_tarski @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 0.75/0.96          | ~ (r1_tarski @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 0.75/0.96      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.75/0.96  thf('12', plain,
% 0.75/0.96      (![X0 : $i]:
% 0.75/0.96         (r1_tarski @ (k4_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)) @ X0)),
% 0.75/0.96      inference('sup-', [status(thm)], ['10', '11'])).
% 0.75/0.96  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.75/0.96  thf('13', plain, (![X8 : $i]: (r1_tarski @ k1_xboole_0 @ X8)),
% 0.75/0.96      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.75/0.96  thf('14', plain,
% 0.75/0.96      (![X2 : $i, X4 : $i]:
% 0.75/0.96         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 0.75/0.96      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.75/0.96  thf('15', plain,
% 0.75/0.96      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.75/0.96      inference('sup-', [status(thm)], ['13', '14'])).
% 0.75/0.96  thf('16', plain,
% 0.75/0.96      (((k4_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)) = (k1_xboole_0))),
% 0.75/0.96      inference('sup-', [status(thm)], ['12', '15'])).
% 0.75/0.96  thf(t48_xboole_1, axiom,
% 0.75/0.96    (![A:$i,B:$i]:
% 0.75/0.96     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.75/0.96  thf('17', plain,
% 0.75/0.96      (![X13 : $i, X14 : $i]:
% 0.75/0.96         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 0.75/0.96           = (k3_xboole_0 @ X13 @ X14))),
% 0.75/0.96      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.75/0.96  thf('18', plain,
% 0.75/0.96      (((k4_xboole_0 @ sk_A @ k1_xboole_0)
% 0.75/0.96         = (k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.75/0.96      inference('sup+', [status(thm)], ['16', '17'])).
% 0.75/0.96  thf(t3_boole, axiom,
% 0.75/0.96    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.75/0.96  thf('19', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.75/0.96      inference('cnf', [status(esa)], [t3_boole])).
% 0.75/0.96  thf('20', plain, (((sk_A) = (k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.75/0.96      inference('demod', [status(thm)], ['18', '19'])).
% 0.75/0.96  thf(commutativity_k2_tarski, axiom,
% 0.75/0.96    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.75/0.96  thf('21', plain,
% 0.75/0.96      (![X17 : $i, X18 : $i]:
% 0.75/0.96         ((k2_tarski @ X18 @ X17) = (k2_tarski @ X17 @ X18))),
% 0.75/0.96      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.75/0.96  thf(t12_setfam_1, axiom,
% 0.75/0.96    (![A:$i,B:$i]:
% 0.75/0.96     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.75/0.96  thf('22', plain,
% 0.75/0.96      (![X19 : $i, X20 : $i]:
% 0.75/0.96         ((k1_setfam_1 @ (k2_tarski @ X19 @ X20)) = (k3_xboole_0 @ X19 @ X20))),
% 0.75/0.96      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.75/0.96  thf('23', plain,
% 0.75/0.96      (![X0 : $i, X1 : $i]:
% 0.75/0.96         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.75/0.96      inference('sup+', [status(thm)], ['21', '22'])).
% 0.75/0.96  thf('24', plain,
% 0.75/0.96      (![X19 : $i, X20 : $i]:
% 0.75/0.96         ((k1_setfam_1 @ (k2_tarski @ X19 @ X20)) = (k3_xboole_0 @ X19 @ X20))),
% 0.75/0.96      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.75/0.96  thf('25', plain,
% 0.75/0.96      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.75/0.96      inference('sup+', [status(thm)], ['23', '24'])).
% 0.75/0.96  thf(t90_relat_1, axiom,
% 0.75/0.96    (![A:$i,B:$i]:
% 0.75/0.96     ( ( v1_relat_1 @ B ) =>
% 0.75/0.96       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 0.75/0.96         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.75/0.96  thf('26', plain,
% 0.75/0.96      (![X28 : $i, X29 : $i]:
% 0.75/0.96         (((k1_relat_1 @ (k7_relat_1 @ X28 @ X29))
% 0.75/0.96            = (k3_xboole_0 @ (k1_relat_1 @ X28) @ X29))
% 0.75/0.96          | ~ (v1_relat_1 @ X28))),
% 0.75/0.96      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.75/0.96  thf(t139_funct_1, axiom,
% 0.75/0.96    (![A:$i,B:$i,C:$i]:
% 0.75/0.96     ( ( v1_relat_1 @ C ) =>
% 0.75/0.96       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.75/0.96         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.75/0.96  thf('27', plain,
% 0.75/0.96      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.75/0.96         (((k10_relat_1 @ (k7_relat_1 @ X31 @ X30) @ X32)
% 0.75/0.96            = (k3_xboole_0 @ X30 @ (k10_relat_1 @ X31 @ X32)))
% 0.75/0.96          | ~ (v1_relat_1 @ X31))),
% 0.75/0.96      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.75/0.96  thf(t169_relat_1, axiom,
% 0.75/0.96    (![A:$i]:
% 0.75/0.96     ( ( v1_relat_1 @ A ) =>
% 0.75/0.96       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.75/0.96  thf('28', plain,
% 0.75/0.96      (![X27 : $i]:
% 0.75/0.96         (((k10_relat_1 @ X27 @ (k2_relat_1 @ X27)) = (k1_relat_1 @ X27))
% 0.75/0.96          | ~ (v1_relat_1 @ X27))),
% 0.75/0.96      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.75/0.96  thf('29', plain,
% 0.75/0.96      (![X0 : $i, X1 : $i]:
% 0.75/0.96         (((k3_xboole_0 @ X0 @ 
% 0.75/0.96            (k10_relat_1 @ X1 @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X0))))
% 0.75/0.96            = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.75/0.96          | ~ (v1_relat_1 @ X1)
% 0.75/0.96          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.75/0.96      inference('sup+', [status(thm)], ['27', '28'])).
% 0.75/0.96  thf('30', plain,
% 0.75/0.96      (![X21 : $i, X22 : $i]:
% 0.75/0.96         (~ (v1_relat_1 @ X21) | (v1_relat_1 @ (k7_relat_1 @ X21 @ X22)))),
% 0.75/0.96      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.75/0.96  thf('31', plain,
% 0.75/0.96      (![X0 : $i, X1 : $i]:
% 0.75/0.96         (~ (v1_relat_1 @ X1)
% 0.75/0.96          | ((k3_xboole_0 @ X0 @ 
% 0.75/0.96              (k10_relat_1 @ X1 @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X0))))
% 0.75/0.96              = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 0.75/0.96      inference('clc', [status(thm)], ['29', '30'])).
% 0.75/0.96  thf('32', plain,
% 0.75/0.96      (![X13 : $i, X14 : $i]:
% 0.75/0.96         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 0.75/0.96           = (k3_xboole_0 @ X13 @ X14))),
% 0.75/0.96      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.75/0.96  thf(commutativity_k2_xboole_0, axiom,
% 0.75/0.96    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.75/0.96  thf('33', plain,
% 0.75/0.96      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.75/0.96      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.75/0.96  thf('34', plain,
% 0.75/0.96      (![X15 : $i, X16 : $i]: (r1_tarski @ X15 @ (k2_xboole_0 @ X15 @ X16))),
% 0.75/0.96      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.75/0.96  thf('35', plain,
% 0.75/0.96      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.75/0.96      inference('sup+', [status(thm)], ['33', '34'])).
% 0.75/0.96  thf('36', plain,
% 0.75/0.96      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.75/0.96         ((r1_tarski @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 0.75/0.96          | ~ (r1_tarski @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 0.75/0.96      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.75/0.96  thf('37', plain,
% 0.75/0.96      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 0.75/0.96      inference('sup-', [status(thm)], ['35', '36'])).
% 0.75/0.96  thf('38', plain,
% 0.75/0.96      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.75/0.96      inference('sup+', [status(thm)], ['32', '37'])).
% 0.75/0.96  thf('39', plain,
% 0.75/0.96      (![X0 : $i, X1 : $i]:
% 0.75/0.96         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X0)
% 0.75/0.96          | ~ (v1_relat_1 @ X1))),
% 0.75/0.96      inference('sup+', [status(thm)], ['31', '38'])).
% 0.75/0.96  thf('40', plain,
% 0.75/0.96      (![X2 : $i, X4 : $i]:
% 0.75/0.96         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 0.75/0.96      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.75/0.96  thf('41', plain,
% 0.75/0.96      (![X0 : $i, X1 : $i]:
% 0.75/0.96         (~ (v1_relat_1 @ X1)
% 0.75/0.96          | ~ (r1_tarski @ X0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.75/0.96          | ((X0) = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 0.75/0.96      inference('sup-', [status(thm)], ['39', '40'])).
% 0.75/0.96  thf('42', plain,
% 0.75/0.96      (![X0 : $i, X1 : $i]:
% 0.75/0.96         (~ (r1_tarski @ X0 @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0))
% 0.75/0.96          | ~ (v1_relat_1 @ X1)
% 0.75/0.96          | ((X0) = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.75/0.96          | ~ (v1_relat_1 @ X1))),
% 0.75/0.96      inference('sup-', [status(thm)], ['26', '41'])).
% 0.75/0.96  thf('43', plain,
% 0.75/0.96      (![X0 : $i, X1 : $i]:
% 0.75/0.96         (((X0) = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.75/0.96          | ~ (v1_relat_1 @ X1)
% 0.75/0.96          | ~ (r1_tarski @ X0 @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0)))),
% 0.75/0.96      inference('simplify', [status(thm)], ['42'])).
% 0.75/0.96  thf('44', plain,
% 0.75/0.96      (![X0 : $i, X1 : $i]:
% 0.75/0.96         (~ (r1_tarski @ X1 @ (k3_xboole_0 @ X1 @ (k1_relat_1 @ X0)))
% 0.75/0.96          | ~ (v1_relat_1 @ X0)
% 0.75/0.96          | ((X1) = (k1_relat_1 @ (k7_relat_1 @ X0 @ X1))))),
% 0.75/0.96      inference('sup-', [status(thm)], ['25', '43'])).
% 0.75/0.96  thf('45', plain,
% 0.75/0.96      ((~ (r1_tarski @ sk_A @ sk_A)
% 0.75/0.96        | ((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.75/0.96        | ~ (v1_relat_1 @ sk_B))),
% 0.75/0.96      inference('sup-', [status(thm)], ['20', '44'])).
% 0.75/0.96  thf('46', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.75/0.96      inference('simplify', [status(thm)], ['1'])).
% 0.75/0.96  thf('47', plain, ((v1_relat_1 @ sk_B)),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf('48', plain, (((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.75/0.96      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.75/0.96  thf(t146_relat_1, axiom,
% 0.75/0.96    (![A:$i]:
% 0.75/0.96     ( ( v1_relat_1 @ A ) =>
% 0.75/0.96       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.75/0.96  thf('49', plain,
% 0.75/0.96      (![X23 : $i]:
% 0.75/0.96         (((k9_relat_1 @ X23 @ (k1_relat_1 @ X23)) = (k2_relat_1 @ X23))
% 0.75/0.96          | ~ (v1_relat_1 @ X23))),
% 0.75/0.96      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.75/0.96  thf('50', plain,
% 0.75/0.96      ((((k9_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ sk_A)
% 0.75/0.96          = (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.75/0.96        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.75/0.96      inference('sup+', [status(thm)], ['48', '49'])).
% 0.75/0.96  thf('51', plain,
% 0.75/0.96      ((~ (v1_relat_1 @ sk_B)
% 0.75/0.96        | ((k9_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ sk_A)
% 0.75/0.96            = (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))))),
% 0.75/0.96      inference('sup-', [status(thm)], ['5', '50'])).
% 0.75/0.96  thf('52', plain, ((v1_relat_1 @ sk_B)),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf('53', plain,
% 0.75/0.96      (((k9_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ sk_A)
% 0.75/0.96         = (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.75/0.96      inference('demod', [status(thm)], ['51', '52'])).
% 0.75/0.96  thf('54', plain,
% 0.75/0.96      ((((k9_relat_1 @ sk_B @ sk_A) = (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.75/0.96        | ~ (v1_relat_1 @ sk_B))),
% 0.75/0.96      inference('sup+', [status(thm)], ['4', '53'])).
% 0.75/0.96  thf('55', plain, ((v1_relat_1 @ sk_B)),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf('56', plain,
% 0.75/0.96      (((k9_relat_1 @ sk_B @ sk_A) = (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.75/0.96      inference('demod', [status(thm)], ['54', '55'])).
% 0.75/0.96  thf('57', plain,
% 0.75/0.96      (![X0 : $i, X1 : $i]:
% 0.75/0.96         (~ (v1_relat_1 @ X1)
% 0.75/0.96          | ((k3_xboole_0 @ X0 @ 
% 0.75/0.96              (k10_relat_1 @ X1 @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X0))))
% 0.75/0.96              = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 0.75/0.96      inference('clc', [status(thm)], ['29', '30'])).
% 0.75/0.96  thf('58', plain,
% 0.75/0.96      ((((k3_xboole_0 @ sk_A @ 
% 0.75/0.96          (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 0.75/0.96          = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.75/0.96        | ~ (v1_relat_1 @ sk_B))),
% 0.75/0.96      inference('sup+', [status(thm)], ['56', '57'])).
% 0.75/0.96  thf('59', plain, (((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.75/0.96      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.75/0.96  thf('60', plain, ((v1_relat_1 @ sk_B)),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf('61', plain,
% 0.75/0.96      (((k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 0.75/0.96         = (sk_A))),
% 0.75/0.96      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.75/0.96  thf('62', plain,
% 0.75/0.96      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.75/0.96      inference('sup+', [status(thm)], ['23', '24'])).
% 0.75/0.96  thf('63', plain,
% 0.75/0.96      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.75/0.96      inference('sup+', [status(thm)], ['32', '37'])).
% 0.75/0.96  thf('64', plain,
% 0.75/0.96      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.75/0.96      inference('sup+', [status(thm)], ['62', '63'])).
% 0.75/0.96  thf('65', plain,
% 0.75/0.96      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 0.75/0.96      inference('sup+', [status(thm)], ['61', '64'])).
% 0.75/0.96  thf('66', plain, ($false), inference('demod', [status(thm)], ['0', '65'])).
% 0.75/0.96  
% 0.75/0.96  % SZS output end Refutation
% 0.75/0.96  
% 0.75/0.97  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
