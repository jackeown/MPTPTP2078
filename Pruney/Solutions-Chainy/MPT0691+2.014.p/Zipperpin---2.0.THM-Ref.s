%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2Dbksin9KI

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:19 EST 2020

% Result     : Theorem 0.57s
% Output     : Refutation 0.57s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 183 expanded)
%              Number of leaves         :   32 (  68 expanded)
%              Depth                    :   19
%              Number of atoms          :  655 (1465 expanded)
%              Number of equality atoms :   48 ( 100 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

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

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

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
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
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
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
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

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('32',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ( X0
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( X0
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['26','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ X0 @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k3_xboole_0 @ X1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( X1
        = ( k1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['25','37'])).

thf('39',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['20','38'])).

thf('40',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['1'])).

thf('41',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( sk_A
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('43',plain,(
    ! [X23: $i] :
      ( ( ( k9_relat_1 @ X23 @ ( k1_relat_1 @ X23 ) )
        = ( k2_relat_1 @ X23 ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('44',plain,
    ( ( ( k9_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ sk_A )
      = ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( k9_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ sk_A )
      = ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['5','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( k9_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ sk_A )
    = ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( ( k9_relat_1 @ sk_B @ sk_A )
      = ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['4','47'])).

thf('49',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( k9_relat_1 @ sk_B @ sk_A )
    = ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('52',plain,
    ( ( ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,
    ( sk_A
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('54',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    = sk_A ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('57',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['55','58'])).

thf('60',plain,(
    $false ),
    inference(demod,[status(thm)],['0','59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2Dbksin9KI
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:01:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 0.57/0.76  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.57/0.76  % Solved by: fo/fo7.sh
% 0.57/0.76  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.57/0.76  % done 1047 iterations in 0.316s
% 0.57/0.76  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.57/0.76  % SZS output start Refutation
% 0.57/0.76  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.57/0.76  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.57/0.76  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.57/0.76  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.57/0.76  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.57/0.76  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.57/0.76  thf(sk_B_type, type, sk_B: $i).
% 0.57/0.76  thf(sk_A_type, type, sk_A: $i).
% 0.57/0.76  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.57/0.76  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.57/0.76  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.57/0.76  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.57/0.76  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.57/0.76  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.57/0.76  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.57/0.76  thf(t146_funct_1, conjecture,
% 0.57/0.76    (![A:$i,B:$i]:
% 0.57/0.76     ( ( v1_relat_1 @ B ) =>
% 0.57/0.76       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.57/0.76         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 0.57/0.76  thf(zf_stmt_0, negated_conjecture,
% 0.57/0.76    (~( ![A:$i,B:$i]:
% 0.57/0.76        ( ( v1_relat_1 @ B ) =>
% 0.57/0.76          ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.57/0.76            ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )),
% 0.57/0.76    inference('cnf.neg', [status(esa)], [t146_funct_1])).
% 0.57/0.76  thf('0', plain,
% 0.57/0.76      (~ (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 0.57/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.76  thf(d10_xboole_0, axiom,
% 0.57/0.76    (![A:$i,B:$i]:
% 0.57/0.76     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.57/0.76  thf('1', plain,
% 0.57/0.76      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.57/0.76      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.57/0.76  thf('2', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.57/0.76      inference('simplify', [status(thm)], ['1'])).
% 0.57/0.76  thf(t162_relat_1, axiom,
% 0.57/0.76    (![A:$i]:
% 0.57/0.76     ( ( v1_relat_1 @ A ) =>
% 0.57/0.76       ( ![B:$i,C:$i]:
% 0.57/0.76         ( ( r1_tarski @ B @ C ) =>
% 0.57/0.76           ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B ) =
% 0.57/0.76             ( k9_relat_1 @ A @ B ) ) ) ) ))).
% 0.57/0.76  thf('3', plain,
% 0.57/0.76      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.57/0.76         (~ (r1_tarski @ X24 @ X25)
% 0.57/0.76          | ((k9_relat_1 @ (k7_relat_1 @ X26 @ X25) @ X24)
% 0.57/0.76              = (k9_relat_1 @ X26 @ X24))
% 0.57/0.76          | ~ (v1_relat_1 @ X26))),
% 0.57/0.76      inference('cnf', [status(esa)], [t162_relat_1])).
% 0.57/0.76  thf('4', plain,
% 0.57/0.76      (![X0 : $i, X1 : $i]:
% 0.57/0.76         (~ (v1_relat_1 @ X1)
% 0.57/0.76          | ((k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X0)
% 0.57/0.76              = (k9_relat_1 @ X1 @ X0)))),
% 0.57/0.76      inference('sup-', [status(thm)], ['2', '3'])).
% 0.57/0.76  thf(dt_k7_relat_1, axiom,
% 0.57/0.76    (![A:$i,B:$i]:
% 0.57/0.76     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.57/0.76  thf('5', plain,
% 0.57/0.76      (![X21 : $i, X22 : $i]:
% 0.57/0.76         (~ (v1_relat_1 @ X21) | (v1_relat_1 @ (k7_relat_1 @ X21 @ X22)))),
% 0.57/0.76      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.57/0.76  thf(t7_xboole_1, axiom,
% 0.57/0.76    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.57/0.76  thf('6', plain,
% 0.57/0.76      (![X15 : $i, X16 : $i]: (r1_tarski @ X15 @ (k2_xboole_0 @ X15 @ X16))),
% 0.57/0.76      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.57/0.76  thf('7', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.57/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.76  thf(t1_xboole_1, axiom,
% 0.57/0.76    (![A:$i,B:$i,C:$i]:
% 0.57/0.76     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.57/0.76       ( r1_tarski @ A @ C ) ))).
% 0.57/0.76  thf('8', plain,
% 0.57/0.76      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.57/0.76         (~ (r1_tarski @ X5 @ X6)
% 0.57/0.76          | ~ (r1_tarski @ X6 @ X7)
% 0.57/0.76          | (r1_tarski @ X5 @ X7))),
% 0.57/0.76      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.57/0.76  thf('9', plain,
% 0.57/0.76      (![X0 : $i]:
% 0.57/0.76         ((r1_tarski @ sk_A @ X0) | ~ (r1_tarski @ (k1_relat_1 @ sk_B) @ X0))),
% 0.57/0.76      inference('sup-', [status(thm)], ['7', '8'])).
% 0.57/0.76  thf('10', plain,
% 0.57/0.76      (![X0 : $i]:
% 0.57/0.76         (r1_tarski @ sk_A @ (k2_xboole_0 @ (k1_relat_1 @ sk_B) @ X0))),
% 0.57/0.76      inference('sup-', [status(thm)], ['6', '9'])).
% 0.57/0.76  thf(t43_xboole_1, axiom,
% 0.57/0.76    (![A:$i,B:$i,C:$i]:
% 0.57/0.76     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 0.57/0.76       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 0.57/0.76  thf('11', plain,
% 0.57/0.76      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.57/0.76         ((r1_tarski @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 0.57/0.76          | ~ (r1_tarski @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 0.57/0.76      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.57/0.76  thf('12', plain,
% 0.57/0.76      (![X0 : $i]:
% 0.57/0.76         (r1_tarski @ (k4_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)) @ X0)),
% 0.57/0.76      inference('sup-', [status(thm)], ['10', '11'])).
% 0.57/0.76  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.57/0.76  thf('13', plain, (![X8 : $i]: (r1_tarski @ k1_xboole_0 @ X8)),
% 0.57/0.76      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.57/0.76  thf('14', plain,
% 0.57/0.76      (![X0 : $i, X2 : $i]:
% 0.57/0.76         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.57/0.76      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.57/0.76  thf('15', plain,
% 0.57/0.76      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.57/0.76      inference('sup-', [status(thm)], ['13', '14'])).
% 0.57/0.76  thf('16', plain,
% 0.57/0.76      (((k4_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)) = (k1_xboole_0))),
% 0.57/0.76      inference('sup-', [status(thm)], ['12', '15'])).
% 0.57/0.76  thf(t48_xboole_1, axiom,
% 0.57/0.76    (![A:$i,B:$i]:
% 0.57/0.76     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.57/0.76  thf('17', plain,
% 0.57/0.76      (![X13 : $i, X14 : $i]:
% 0.57/0.76         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 0.57/0.76           = (k3_xboole_0 @ X13 @ X14))),
% 0.57/0.76      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.57/0.76  thf('18', plain,
% 0.57/0.76      (((k4_xboole_0 @ sk_A @ k1_xboole_0)
% 0.57/0.76         = (k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.57/0.76      inference('sup+', [status(thm)], ['16', '17'])).
% 0.57/0.76  thf(t3_boole, axiom,
% 0.57/0.76    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.57/0.76  thf('19', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.57/0.76      inference('cnf', [status(esa)], [t3_boole])).
% 0.57/0.76  thf('20', plain, (((sk_A) = (k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.57/0.76      inference('demod', [status(thm)], ['18', '19'])).
% 0.57/0.76  thf(commutativity_k2_tarski, axiom,
% 0.57/0.76    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.57/0.76  thf('21', plain,
% 0.57/0.76      (![X17 : $i, X18 : $i]:
% 0.57/0.76         ((k2_tarski @ X18 @ X17) = (k2_tarski @ X17 @ X18))),
% 0.57/0.76      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.57/0.76  thf(t12_setfam_1, axiom,
% 0.57/0.76    (![A:$i,B:$i]:
% 0.57/0.76     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.57/0.76  thf('22', plain,
% 0.57/0.76      (![X19 : $i, X20 : $i]:
% 0.57/0.76         ((k1_setfam_1 @ (k2_tarski @ X19 @ X20)) = (k3_xboole_0 @ X19 @ X20))),
% 0.57/0.76      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.57/0.76  thf('23', plain,
% 0.57/0.76      (![X0 : $i, X1 : $i]:
% 0.57/0.76         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.57/0.76      inference('sup+', [status(thm)], ['21', '22'])).
% 0.57/0.76  thf('24', plain,
% 0.57/0.76      (![X19 : $i, X20 : $i]:
% 0.57/0.76         ((k1_setfam_1 @ (k2_tarski @ X19 @ X20)) = (k3_xboole_0 @ X19 @ X20))),
% 0.57/0.76      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.57/0.76  thf('25', plain,
% 0.57/0.76      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.57/0.76      inference('sup+', [status(thm)], ['23', '24'])).
% 0.57/0.76  thf(t90_relat_1, axiom,
% 0.57/0.76    (![A:$i,B:$i]:
% 0.57/0.76     ( ( v1_relat_1 @ B ) =>
% 0.57/0.76       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 0.57/0.76         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.57/0.76  thf('26', plain,
% 0.57/0.76      (![X28 : $i, X29 : $i]:
% 0.57/0.76         (((k1_relat_1 @ (k7_relat_1 @ X28 @ X29))
% 0.57/0.76            = (k3_xboole_0 @ (k1_relat_1 @ X28) @ X29))
% 0.57/0.76          | ~ (v1_relat_1 @ X28))),
% 0.57/0.76      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.57/0.76  thf(t139_funct_1, axiom,
% 0.57/0.76    (![A:$i,B:$i,C:$i]:
% 0.57/0.76     ( ( v1_relat_1 @ C ) =>
% 0.57/0.76       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.57/0.76         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.57/0.76  thf('27', plain,
% 0.57/0.76      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.57/0.76         (((k10_relat_1 @ (k7_relat_1 @ X31 @ X30) @ X32)
% 0.57/0.76            = (k3_xboole_0 @ X30 @ (k10_relat_1 @ X31 @ X32)))
% 0.57/0.76          | ~ (v1_relat_1 @ X31))),
% 0.57/0.76      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.57/0.76  thf(t169_relat_1, axiom,
% 0.57/0.76    (![A:$i]:
% 0.57/0.76     ( ( v1_relat_1 @ A ) =>
% 0.57/0.76       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.57/0.76  thf('28', plain,
% 0.57/0.76      (![X27 : $i]:
% 0.57/0.76         (((k10_relat_1 @ X27 @ (k2_relat_1 @ X27)) = (k1_relat_1 @ X27))
% 0.57/0.76          | ~ (v1_relat_1 @ X27))),
% 0.57/0.76      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.57/0.76  thf('29', plain,
% 0.57/0.76      (![X0 : $i, X1 : $i]:
% 0.57/0.76         (((k3_xboole_0 @ X0 @ 
% 0.57/0.76            (k10_relat_1 @ X1 @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X0))))
% 0.57/0.76            = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.57/0.76          | ~ (v1_relat_1 @ X1)
% 0.57/0.76          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.57/0.76      inference('sup+', [status(thm)], ['27', '28'])).
% 0.57/0.76  thf('30', plain,
% 0.57/0.76      (![X21 : $i, X22 : $i]:
% 0.57/0.76         (~ (v1_relat_1 @ X21) | (v1_relat_1 @ (k7_relat_1 @ X21 @ X22)))),
% 0.57/0.76      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.57/0.76  thf('31', plain,
% 0.57/0.76      (![X0 : $i, X1 : $i]:
% 0.57/0.76         (~ (v1_relat_1 @ X1)
% 0.57/0.76          | ((k3_xboole_0 @ X0 @ 
% 0.57/0.76              (k10_relat_1 @ X1 @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X0))))
% 0.57/0.76              = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 0.57/0.76      inference('clc', [status(thm)], ['29', '30'])).
% 0.57/0.76  thf(t17_xboole_1, axiom,
% 0.57/0.76    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.57/0.76  thf('32', plain,
% 0.57/0.76      (![X3 : $i, X4 : $i]: (r1_tarski @ (k3_xboole_0 @ X3 @ X4) @ X3)),
% 0.57/0.76      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.57/0.76  thf('33', plain,
% 0.57/0.76      (![X0 : $i, X1 : $i]:
% 0.57/0.76         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X0)
% 0.57/0.76          | ~ (v1_relat_1 @ X1))),
% 0.57/0.76      inference('sup+', [status(thm)], ['31', '32'])).
% 0.57/0.76  thf('34', plain,
% 0.57/0.76      (![X0 : $i, X2 : $i]:
% 0.57/0.76         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.57/0.76      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.57/0.76  thf('35', plain,
% 0.57/0.76      (![X0 : $i, X1 : $i]:
% 0.57/0.76         (~ (v1_relat_1 @ X1)
% 0.57/0.76          | ~ (r1_tarski @ X0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.57/0.76          | ((X0) = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 0.57/0.76      inference('sup-', [status(thm)], ['33', '34'])).
% 0.57/0.76  thf('36', plain,
% 0.57/0.76      (![X0 : $i, X1 : $i]:
% 0.57/0.76         (~ (r1_tarski @ X0 @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0))
% 0.57/0.76          | ~ (v1_relat_1 @ X1)
% 0.57/0.76          | ((X0) = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.57/0.76          | ~ (v1_relat_1 @ X1))),
% 0.57/0.76      inference('sup-', [status(thm)], ['26', '35'])).
% 0.57/0.76  thf('37', plain,
% 0.57/0.76      (![X0 : $i, X1 : $i]:
% 0.57/0.76         (((X0) = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.57/0.76          | ~ (v1_relat_1 @ X1)
% 0.57/0.76          | ~ (r1_tarski @ X0 @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0)))),
% 0.57/0.76      inference('simplify', [status(thm)], ['36'])).
% 0.57/0.76  thf('38', plain,
% 0.57/0.76      (![X0 : $i, X1 : $i]:
% 0.57/0.76         (~ (r1_tarski @ X1 @ (k3_xboole_0 @ X1 @ (k1_relat_1 @ X0)))
% 0.57/0.76          | ~ (v1_relat_1 @ X0)
% 0.57/0.76          | ((X1) = (k1_relat_1 @ (k7_relat_1 @ X0 @ X1))))),
% 0.57/0.76      inference('sup-', [status(thm)], ['25', '37'])).
% 0.57/0.76  thf('39', plain,
% 0.57/0.76      ((~ (r1_tarski @ sk_A @ sk_A)
% 0.57/0.76        | ((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.57/0.76        | ~ (v1_relat_1 @ sk_B))),
% 0.57/0.76      inference('sup-', [status(thm)], ['20', '38'])).
% 0.57/0.76  thf('40', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.57/0.76      inference('simplify', [status(thm)], ['1'])).
% 0.57/0.76  thf('41', plain, ((v1_relat_1 @ sk_B)),
% 0.57/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.76  thf('42', plain, (((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.57/0.76      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.57/0.76  thf(t146_relat_1, axiom,
% 0.57/0.76    (![A:$i]:
% 0.57/0.76     ( ( v1_relat_1 @ A ) =>
% 0.57/0.76       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.57/0.76  thf('43', plain,
% 0.57/0.76      (![X23 : $i]:
% 0.57/0.76         (((k9_relat_1 @ X23 @ (k1_relat_1 @ X23)) = (k2_relat_1 @ X23))
% 0.57/0.76          | ~ (v1_relat_1 @ X23))),
% 0.57/0.76      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.57/0.76  thf('44', plain,
% 0.57/0.76      ((((k9_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ sk_A)
% 0.57/0.76          = (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.57/0.76        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.57/0.76      inference('sup+', [status(thm)], ['42', '43'])).
% 0.57/0.76  thf('45', plain,
% 0.57/0.76      ((~ (v1_relat_1 @ sk_B)
% 0.57/0.76        | ((k9_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ sk_A)
% 0.57/0.76            = (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))))),
% 0.57/0.76      inference('sup-', [status(thm)], ['5', '44'])).
% 0.57/0.76  thf('46', plain, ((v1_relat_1 @ sk_B)),
% 0.57/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.76  thf('47', plain,
% 0.57/0.76      (((k9_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ sk_A)
% 0.57/0.76         = (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.57/0.76      inference('demod', [status(thm)], ['45', '46'])).
% 0.57/0.76  thf('48', plain,
% 0.57/0.76      ((((k9_relat_1 @ sk_B @ sk_A) = (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.57/0.76        | ~ (v1_relat_1 @ sk_B))),
% 0.57/0.76      inference('sup+', [status(thm)], ['4', '47'])).
% 0.57/0.76  thf('49', plain, ((v1_relat_1 @ sk_B)),
% 0.57/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.76  thf('50', plain,
% 0.57/0.76      (((k9_relat_1 @ sk_B @ sk_A) = (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.57/0.76      inference('demod', [status(thm)], ['48', '49'])).
% 0.57/0.76  thf('51', plain,
% 0.57/0.76      (![X0 : $i, X1 : $i]:
% 0.57/0.76         (~ (v1_relat_1 @ X1)
% 0.57/0.76          | ((k3_xboole_0 @ X0 @ 
% 0.57/0.76              (k10_relat_1 @ X1 @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X0))))
% 0.57/0.76              = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 0.57/0.76      inference('clc', [status(thm)], ['29', '30'])).
% 0.57/0.76  thf('52', plain,
% 0.57/0.76      ((((k3_xboole_0 @ sk_A @ 
% 0.57/0.76          (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 0.57/0.76          = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.57/0.76        | ~ (v1_relat_1 @ sk_B))),
% 0.57/0.76      inference('sup+', [status(thm)], ['50', '51'])).
% 0.57/0.76  thf('53', plain, (((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.57/0.76      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.57/0.76  thf('54', plain, ((v1_relat_1 @ sk_B)),
% 0.57/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.76  thf('55', plain,
% 0.57/0.76      (((k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 0.57/0.76         = (sk_A))),
% 0.57/0.76      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.57/0.76  thf('56', plain,
% 0.57/0.76      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.57/0.76      inference('sup+', [status(thm)], ['23', '24'])).
% 0.57/0.76  thf('57', plain,
% 0.57/0.76      (![X3 : $i, X4 : $i]: (r1_tarski @ (k3_xboole_0 @ X3 @ X4) @ X3)),
% 0.57/0.76      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.57/0.76  thf('58', plain,
% 0.57/0.76      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.57/0.76      inference('sup+', [status(thm)], ['56', '57'])).
% 0.57/0.76  thf('59', plain,
% 0.57/0.76      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 0.57/0.76      inference('sup+', [status(thm)], ['55', '58'])).
% 0.57/0.76  thf('60', plain, ($false), inference('demod', [status(thm)], ['0', '59'])).
% 0.57/0.76  
% 0.57/0.76  % SZS output end Refutation
% 0.57/0.76  
% 0.60/0.77  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
