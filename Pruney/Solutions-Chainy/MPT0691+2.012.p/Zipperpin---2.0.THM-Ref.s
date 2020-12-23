%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IyCIzTdYiL

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:19 EST 2020

% Result     : Theorem 1.35s
% Output     : Refutation 1.35s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 233 expanded)
%              Number of leaves         :   32 (  83 expanded)
%              Depth                    :   20
%              Number of atoms          :  751 (1803 expanded)
%              Number of equality atoms :   56 ( 132 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( r1_tarski @ X26 @ X27 )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X28 @ X27 ) @ X26 )
        = ( k9_relat_1 @ X28 @ X26 ) )
      | ~ ( v1_relat_1 @ X28 ) ) ),
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
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('6',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('7',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X3 @ X5 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('10',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_xboole_0 @ X7 @ X6 )
        = X6 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('11',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X3 @ X5 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ X0 )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('15',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X14 @ X15 ) @ X16 )
      | ~ ( r1_tarski @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('17',plain,(
    ! [X11: $i] :
      ( r1_tarski @ k1_xboole_0 @ X11 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['16','19'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('21',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('22',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('23',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X12 ) )
      = ( k2_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('24',plain,(
    ! [X11: $i] :
      ( r1_tarski @ k1_xboole_0 @ X11 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('25',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_xboole_0 @ X7 @ X6 )
        = X6 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['22','29'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('31',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_tarski @ X20 @ X19 )
      = ( k2_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('32',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('36',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X30 @ X31 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X30 ) @ X31 ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf(t139_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('37',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X33 @ X32 ) @ X34 )
        = ( k3_xboole_0 @ X32 @ ( k10_relat_1 @ X33 @ X34 ) ) )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('38',plain,(
    ! [X29: $i] :
      ( ( ( k10_relat_1 @ X29 @ ( k2_relat_1 @ X29 ) )
        = ( k1_relat_1 @ X29 ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t18_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf('43',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X8 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t18_xboole_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['41','44'])).

thf('46',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ( X0
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( X0
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['36','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ X0 @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k3_xboole_0 @ X1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( X1
        = ( k1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['35','49'])).

thf('51',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['30','50'])).

thf('52',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['1'])).

thf('53',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( sk_A
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('55',plain,(
    ! [X25: $i] :
      ( ( ( k9_relat_1 @ X25 @ ( k1_relat_1 @ X25 ) )
        = ( k2_relat_1 @ X25 ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('56',plain,
    ( ( ( k9_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ sk_A )
      = ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( k9_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ sk_A )
      = ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['5','56'])).

thf('58',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( k9_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ sk_A )
    = ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( ( k9_relat_1 @ sk_B @ sk_A )
      = ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['4','59'])).

thf('61',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( k9_relat_1 @ sk_B @ sk_A )
    = ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('64',plain,
    ( ( ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,
    ( sk_A
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('66',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    = sk_A ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['1'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('70',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X8 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t18_xboole_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['68','71'])).

thf('73',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['67','72'])).

thf('74',plain,(
    $false ),
    inference(demod,[status(thm)],['0','73'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IyCIzTdYiL
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:30:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.35/1.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.35/1.55  % Solved by: fo/fo7.sh
% 1.35/1.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.35/1.55  % done 3290 iterations in 1.114s
% 1.35/1.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.35/1.55  % SZS output start Refutation
% 1.35/1.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.35/1.55  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.35/1.55  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.35/1.55  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.35/1.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.35/1.55  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 1.35/1.55  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.35/1.55  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.35/1.55  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 1.35/1.55  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 1.35/1.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.35/1.55  thf(sk_A_type, type, sk_A: $i).
% 1.35/1.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.35/1.55  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.35/1.55  thf(sk_B_type, type, sk_B: $i).
% 1.35/1.55  thf(t146_funct_1, conjecture,
% 1.35/1.55    (![A:$i,B:$i]:
% 1.35/1.55     ( ( v1_relat_1 @ B ) =>
% 1.35/1.55       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 1.35/1.55         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 1.35/1.55  thf(zf_stmt_0, negated_conjecture,
% 1.35/1.55    (~( ![A:$i,B:$i]:
% 1.35/1.55        ( ( v1_relat_1 @ B ) =>
% 1.35/1.55          ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 1.35/1.55            ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )),
% 1.35/1.55    inference('cnf.neg', [status(esa)], [t146_funct_1])).
% 1.35/1.55  thf('0', plain,
% 1.35/1.55      (~ (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 1.35/1.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.55  thf(d10_xboole_0, axiom,
% 1.35/1.55    (![A:$i,B:$i]:
% 1.35/1.55     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.35/1.55  thf('1', plain,
% 1.35/1.55      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 1.35/1.55      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.35/1.55  thf('2', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.35/1.55      inference('simplify', [status(thm)], ['1'])).
% 1.35/1.55  thf(t162_relat_1, axiom,
% 1.35/1.55    (![A:$i]:
% 1.35/1.55     ( ( v1_relat_1 @ A ) =>
% 1.35/1.55       ( ![B:$i,C:$i]:
% 1.35/1.55         ( ( r1_tarski @ B @ C ) =>
% 1.35/1.55           ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B ) =
% 1.35/1.55             ( k9_relat_1 @ A @ B ) ) ) ) ))).
% 1.35/1.55  thf('3', plain,
% 1.35/1.55      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.35/1.55         (~ (r1_tarski @ X26 @ X27)
% 1.35/1.55          | ((k9_relat_1 @ (k7_relat_1 @ X28 @ X27) @ X26)
% 1.35/1.55              = (k9_relat_1 @ X28 @ X26))
% 1.35/1.55          | ~ (v1_relat_1 @ X28))),
% 1.35/1.55      inference('cnf', [status(esa)], [t162_relat_1])).
% 1.35/1.55  thf('4', plain,
% 1.35/1.55      (![X0 : $i, X1 : $i]:
% 1.35/1.55         (~ (v1_relat_1 @ X1)
% 1.35/1.55          | ((k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X0)
% 1.35/1.55              = (k9_relat_1 @ X1 @ X0)))),
% 1.35/1.55      inference('sup-', [status(thm)], ['2', '3'])).
% 1.35/1.55  thf(dt_k7_relat_1, axiom,
% 1.35/1.55    (![A:$i,B:$i]:
% 1.35/1.55     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 1.35/1.55  thf('5', plain,
% 1.35/1.55      (![X23 : $i, X24 : $i]:
% 1.35/1.55         (~ (v1_relat_1 @ X23) | (v1_relat_1 @ (k7_relat_1 @ X23 @ X24)))),
% 1.35/1.55      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 1.35/1.55  thf('6', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.35/1.55      inference('simplify', [status(thm)], ['1'])).
% 1.35/1.55  thf(t11_xboole_1, axiom,
% 1.35/1.55    (![A:$i,B:$i,C:$i]:
% 1.35/1.55     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 1.35/1.55  thf('7', plain,
% 1.35/1.55      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.35/1.55         ((r1_tarski @ X3 @ X4) | ~ (r1_tarski @ (k2_xboole_0 @ X3 @ X5) @ X4))),
% 1.35/1.55      inference('cnf', [status(esa)], [t11_xboole_1])).
% 1.35/1.55  thf('8', plain,
% 1.35/1.55      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 1.35/1.55      inference('sup-', [status(thm)], ['6', '7'])).
% 1.35/1.55  thf('9', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 1.35/1.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.55  thf(t12_xboole_1, axiom,
% 1.35/1.55    (![A:$i,B:$i]:
% 1.35/1.55     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 1.35/1.55  thf('10', plain,
% 1.35/1.55      (![X6 : $i, X7 : $i]:
% 1.35/1.55         (((k2_xboole_0 @ X7 @ X6) = (X6)) | ~ (r1_tarski @ X7 @ X6))),
% 1.35/1.55      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.35/1.55  thf('11', plain,
% 1.35/1.55      (((k2_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)) = (k1_relat_1 @ sk_B))),
% 1.35/1.55      inference('sup-', [status(thm)], ['9', '10'])).
% 1.35/1.55  thf('12', plain,
% 1.35/1.55      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.35/1.55         ((r1_tarski @ X3 @ X4) | ~ (r1_tarski @ (k2_xboole_0 @ X3 @ X5) @ X4))),
% 1.35/1.55      inference('cnf', [status(esa)], [t11_xboole_1])).
% 1.35/1.55  thf('13', plain,
% 1.35/1.55      (![X0 : $i]:
% 1.35/1.55         (~ (r1_tarski @ (k1_relat_1 @ sk_B) @ X0) | (r1_tarski @ sk_A @ X0))),
% 1.35/1.55      inference('sup-', [status(thm)], ['11', '12'])).
% 1.35/1.55  thf('14', plain,
% 1.35/1.55      (![X0 : $i]:
% 1.35/1.55         (r1_tarski @ sk_A @ (k2_xboole_0 @ (k1_relat_1 @ sk_B) @ X0))),
% 1.35/1.55      inference('sup-', [status(thm)], ['8', '13'])).
% 1.35/1.55  thf(t43_xboole_1, axiom,
% 1.35/1.55    (![A:$i,B:$i,C:$i]:
% 1.35/1.55     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 1.35/1.55       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 1.35/1.55  thf('15', plain,
% 1.35/1.55      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.35/1.55         ((r1_tarski @ (k4_xboole_0 @ X14 @ X15) @ X16)
% 1.35/1.55          | ~ (r1_tarski @ X14 @ (k2_xboole_0 @ X15 @ X16)))),
% 1.35/1.55      inference('cnf', [status(esa)], [t43_xboole_1])).
% 1.35/1.55  thf('16', plain,
% 1.35/1.55      (![X0 : $i]:
% 1.35/1.55         (r1_tarski @ (k4_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)) @ X0)),
% 1.35/1.55      inference('sup-', [status(thm)], ['14', '15'])).
% 1.35/1.55  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 1.35/1.55  thf('17', plain, (![X11 : $i]: (r1_tarski @ k1_xboole_0 @ X11)),
% 1.35/1.55      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.35/1.55  thf('18', plain,
% 1.35/1.55      (![X0 : $i, X2 : $i]:
% 1.35/1.55         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.35/1.55      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.35/1.55  thf('19', plain,
% 1.35/1.55      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 1.35/1.55      inference('sup-', [status(thm)], ['17', '18'])).
% 1.35/1.55  thf('20', plain,
% 1.35/1.55      (((k4_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)) = (k1_xboole_0))),
% 1.35/1.55      inference('sup-', [status(thm)], ['16', '19'])).
% 1.35/1.55  thf(t48_xboole_1, axiom,
% 1.35/1.55    (![A:$i,B:$i]:
% 1.35/1.55     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.35/1.55  thf('21', plain,
% 1.35/1.55      (![X17 : $i, X18 : $i]:
% 1.35/1.55         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 1.35/1.55           = (k3_xboole_0 @ X17 @ X18))),
% 1.35/1.55      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.35/1.55  thf('22', plain,
% 1.35/1.55      (((k4_xboole_0 @ sk_A @ k1_xboole_0)
% 1.35/1.55         = (k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)))),
% 1.35/1.55      inference('sup+', [status(thm)], ['20', '21'])).
% 1.35/1.55  thf(t39_xboole_1, axiom,
% 1.35/1.55    (![A:$i,B:$i]:
% 1.35/1.55     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.35/1.55  thf('23', plain,
% 1.35/1.55      (![X12 : $i, X13 : $i]:
% 1.35/1.55         ((k2_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X12))
% 1.35/1.55           = (k2_xboole_0 @ X12 @ X13))),
% 1.35/1.55      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.35/1.55  thf('24', plain, (![X11 : $i]: (r1_tarski @ k1_xboole_0 @ X11)),
% 1.35/1.55      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.35/1.55  thf('25', plain,
% 1.35/1.55      (![X6 : $i, X7 : $i]:
% 1.35/1.55         (((k2_xboole_0 @ X7 @ X6) = (X6)) | ~ (r1_tarski @ X7 @ X6))),
% 1.35/1.55      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.35/1.55  thf('26', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.35/1.55      inference('sup-', [status(thm)], ['24', '25'])).
% 1.35/1.55  thf('27', plain,
% 1.35/1.55      (![X0 : $i]:
% 1.35/1.55         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 1.35/1.55      inference('sup+', [status(thm)], ['23', '26'])).
% 1.35/1.55  thf('28', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.35/1.55      inference('sup-', [status(thm)], ['24', '25'])).
% 1.35/1.55  thf('29', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.35/1.55      inference('sup+', [status(thm)], ['27', '28'])).
% 1.35/1.55  thf('30', plain, (((sk_A) = (k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)))),
% 1.35/1.55      inference('demod', [status(thm)], ['22', '29'])).
% 1.35/1.55  thf(commutativity_k2_tarski, axiom,
% 1.35/1.55    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 1.35/1.55  thf('31', plain,
% 1.35/1.55      (![X19 : $i, X20 : $i]:
% 1.35/1.55         ((k2_tarski @ X20 @ X19) = (k2_tarski @ X19 @ X20))),
% 1.35/1.55      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.35/1.55  thf(t12_setfam_1, axiom,
% 1.35/1.55    (![A:$i,B:$i]:
% 1.35/1.55     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.35/1.55  thf('32', plain,
% 1.35/1.55      (![X21 : $i, X22 : $i]:
% 1.35/1.55         ((k1_setfam_1 @ (k2_tarski @ X21 @ X22)) = (k3_xboole_0 @ X21 @ X22))),
% 1.35/1.55      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.35/1.55  thf('33', plain,
% 1.35/1.55      (![X0 : $i, X1 : $i]:
% 1.35/1.55         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 1.35/1.55      inference('sup+', [status(thm)], ['31', '32'])).
% 1.35/1.55  thf('34', plain,
% 1.35/1.55      (![X21 : $i, X22 : $i]:
% 1.35/1.55         ((k1_setfam_1 @ (k2_tarski @ X21 @ X22)) = (k3_xboole_0 @ X21 @ X22))),
% 1.35/1.55      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.35/1.55  thf('35', plain,
% 1.35/1.55      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.35/1.55      inference('sup+', [status(thm)], ['33', '34'])).
% 1.35/1.55  thf(t90_relat_1, axiom,
% 1.35/1.55    (![A:$i,B:$i]:
% 1.35/1.55     ( ( v1_relat_1 @ B ) =>
% 1.35/1.55       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 1.35/1.55         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 1.35/1.55  thf('36', plain,
% 1.35/1.55      (![X30 : $i, X31 : $i]:
% 1.35/1.55         (((k1_relat_1 @ (k7_relat_1 @ X30 @ X31))
% 1.35/1.55            = (k3_xboole_0 @ (k1_relat_1 @ X30) @ X31))
% 1.35/1.55          | ~ (v1_relat_1 @ X30))),
% 1.35/1.55      inference('cnf', [status(esa)], [t90_relat_1])).
% 1.35/1.55  thf(t139_funct_1, axiom,
% 1.35/1.55    (![A:$i,B:$i,C:$i]:
% 1.35/1.55     ( ( v1_relat_1 @ C ) =>
% 1.35/1.55       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 1.35/1.55         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 1.35/1.55  thf('37', plain,
% 1.35/1.55      (![X32 : $i, X33 : $i, X34 : $i]:
% 1.35/1.55         (((k10_relat_1 @ (k7_relat_1 @ X33 @ X32) @ X34)
% 1.35/1.55            = (k3_xboole_0 @ X32 @ (k10_relat_1 @ X33 @ X34)))
% 1.35/1.55          | ~ (v1_relat_1 @ X33))),
% 1.35/1.55      inference('cnf', [status(esa)], [t139_funct_1])).
% 1.35/1.55  thf(t169_relat_1, axiom,
% 1.35/1.55    (![A:$i]:
% 1.35/1.55     ( ( v1_relat_1 @ A ) =>
% 1.35/1.55       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 1.35/1.55  thf('38', plain,
% 1.35/1.55      (![X29 : $i]:
% 1.35/1.55         (((k10_relat_1 @ X29 @ (k2_relat_1 @ X29)) = (k1_relat_1 @ X29))
% 1.35/1.55          | ~ (v1_relat_1 @ X29))),
% 1.35/1.55      inference('cnf', [status(esa)], [t169_relat_1])).
% 1.35/1.55  thf('39', plain,
% 1.35/1.55      (![X0 : $i, X1 : $i]:
% 1.35/1.55         (((k3_xboole_0 @ X0 @ 
% 1.35/1.55            (k10_relat_1 @ X1 @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X0))))
% 1.35/1.55            = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 1.35/1.55          | ~ (v1_relat_1 @ X1)
% 1.35/1.55          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 1.35/1.55      inference('sup+', [status(thm)], ['37', '38'])).
% 1.35/1.55  thf('40', plain,
% 1.35/1.55      (![X23 : $i, X24 : $i]:
% 1.35/1.55         (~ (v1_relat_1 @ X23) | (v1_relat_1 @ (k7_relat_1 @ X23 @ X24)))),
% 1.35/1.55      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 1.35/1.55  thf('41', plain,
% 1.35/1.55      (![X0 : $i, X1 : $i]:
% 1.35/1.55         (~ (v1_relat_1 @ X1)
% 1.35/1.55          | ((k3_xboole_0 @ X0 @ 
% 1.35/1.55              (k10_relat_1 @ X1 @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X0))))
% 1.35/1.55              = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 1.35/1.55      inference('clc', [status(thm)], ['39', '40'])).
% 1.35/1.55  thf('42', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.35/1.55      inference('simplify', [status(thm)], ['1'])).
% 1.35/1.55  thf(t18_xboole_1, axiom,
% 1.35/1.55    (![A:$i,B:$i,C:$i]:
% 1.35/1.55     ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) => ( r1_tarski @ A @ B ) ))).
% 1.35/1.55  thf('43', plain,
% 1.35/1.55      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.35/1.55         ((r1_tarski @ X8 @ X9) | ~ (r1_tarski @ X8 @ (k3_xboole_0 @ X9 @ X10)))),
% 1.35/1.55      inference('cnf', [status(esa)], [t18_xboole_1])).
% 1.35/1.55  thf('44', plain,
% 1.35/1.55      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 1.35/1.55      inference('sup-', [status(thm)], ['42', '43'])).
% 1.35/1.55  thf('45', plain,
% 1.35/1.55      (![X0 : $i, X1 : $i]:
% 1.35/1.55         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X0)
% 1.35/1.55          | ~ (v1_relat_1 @ X1))),
% 1.35/1.55      inference('sup+', [status(thm)], ['41', '44'])).
% 1.35/1.55  thf('46', plain,
% 1.35/1.55      (![X0 : $i, X2 : $i]:
% 1.35/1.55         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.35/1.55      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.35/1.55  thf('47', plain,
% 1.35/1.55      (![X0 : $i, X1 : $i]:
% 1.35/1.55         (~ (v1_relat_1 @ X1)
% 1.35/1.55          | ~ (r1_tarski @ X0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 1.35/1.55          | ((X0) = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 1.35/1.55      inference('sup-', [status(thm)], ['45', '46'])).
% 1.35/1.55  thf('48', plain,
% 1.35/1.55      (![X0 : $i, X1 : $i]:
% 1.35/1.55         (~ (r1_tarski @ X0 @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0))
% 1.35/1.55          | ~ (v1_relat_1 @ X1)
% 1.35/1.55          | ((X0) = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 1.35/1.55          | ~ (v1_relat_1 @ X1))),
% 1.35/1.55      inference('sup-', [status(thm)], ['36', '47'])).
% 1.35/1.55  thf('49', plain,
% 1.35/1.55      (![X0 : $i, X1 : $i]:
% 1.35/1.55         (((X0) = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 1.35/1.55          | ~ (v1_relat_1 @ X1)
% 1.35/1.55          | ~ (r1_tarski @ X0 @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0)))),
% 1.35/1.55      inference('simplify', [status(thm)], ['48'])).
% 1.35/1.55  thf('50', plain,
% 1.35/1.55      (![X0 : $i, X1 : $i]:
% 1.35/1.55         (~ (r1_tarski @ X1 @ (k3_xboole_0 @ X1 @ (k1_relat_1 @ X0)))
% 1.35/1.55          | ~ (v1_relat_1 @ X0)
% 1.35/1.55          | ((X1) = (k1_relat_1 @ (k7_relat_1 @ X0 @ X1))))),
% 1.35/1.55      inference('sup-', [status(thm)], ['35', '49'])).
% 1.35/1.55  thf('51', plain,
% 1.35/1.55      ((~ (r1_tarski @ sk_A @ sk_A)
% 1.35/1.55        | ((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 1.35/1.55        | ~ (v1_relat_1 @ sk_B))),
% 1.35/1.55      inference('sup-', [status(thm)], ['30', '50'])).
% 1.35/1.55  thf('52', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.35/1.55      inference('simplify', [status(thm)], ['1'])).
% 1.35/1.55  thf('53', plain, ((v1_relat_1 @ sk_B)),
% 1.35/1.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.55  thf('54', plain, (((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 1.35/1.55      inference('demod', [status(thm)], ['51', '52', '53'])).
% 1.35/1.55  thf(t146_relat_1, axiom,
% 1.35/1.55    (![A:$i]:
% 1.35/1.55     ( ( v1_relat_1 @ A ) =>
% 1.35/1.55       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 1.35/1.55  thf('55', plain,
% 1.35/1.55      (![X25 : $i]:
% 1.35/1.55         (((k9_relat_1 @ X25 @ (k1_relat_1 @ X25)) = (k2_relat_1 @ X25))
% 1.35/1.55          | ~ (v1_relat_1 @ X25))),
% 1.35/1.55      inference('cnf', [status(esa)], [t146_relat_1])).
% 1.35/1.55  thf('56', plain,
% 1.35/1.55      ((((k9_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ sk_A)
% 1.35/1.55          = (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 1.35/1.55        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 1.35/1.55      inference('sup+', [status(thm)], ['54', '55'])).
% 1.35/1.55  thf('57', plain,
% 1.35/1.55      ((~ (v1_relat_1 @ sk_B)
% 1.35/1.55        | ((k9_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ sk_A)
% 1.35/1.55            = (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))))),
% 1.35/1.55      inference('sup-', [status(thm)], ['5', '56'])).
% 1.35/1.55  thf('58', plain, ((v1_relat_1 @ sk_B)),
% 1.35/1.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.55  thf('59', plain,
% 1.35/1.55      (((k9_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ sk_A)
% 1.35/1.55         = (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 1.35/1.55      inference('demod', [status(thm)], ['57', '58'])).
% 1.35/1.55  thf('60', plain,
% 1.35/1.55      ((((k9_relat_1 @ sk_B @ sk_A) = (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 1.35/1.55        | ~ (v1_relat_1 @ sk_B))),
% 1.35/1.55      inference('sup+', [status(thm)], ['4', '59'])).
% 1.35/1.55  thf('61', plain, ((v1_relat_1 @ sk_B)),
% 1.35/1.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.55  thf('62', plain,
% 1.35/1.55      (((k9_relat_1 @ sk_B @ sk_A) = (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 1.35/1.55      inference('demod', [status(thm)], ['60', '61'])).
% 1.35/1.55  thf('63', plain,
% 1.35/1.55      (![X0 : $i, X1 : $i]:
% 1.35/1.55         (~ (v1_relat_1 @ X1)
% 1.35/1.55          | ((k3_xboole_0 @ X0 @ 
% 1.35/1.55              (k10_relat_1 @ X1 @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X0))))
% 1.35/1.55              = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 1.35/1.55      inference('clc', [status(thm)], ['39', '40'])).
% 1.35/1.55  thf('64', plain,
% 1.35/1.55      ((((k3_xboole_0 @ sk_A @ 
% 1.35/1.55          (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 1.35/1.55          = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 1.35/1.55        | ~ (v1_relat_1 @ sk_B))),
% 1.35/1.55      inference('sup+', [status(thm)], ['62', '63'])).
% 1.35/1.55  thf('65', plain, (((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 1.35/1.55      inference('demod', [status(thm)], ['51', '52', '53'])).
% 1.35/1.55  thf('66', plain, ((v1_relat_1 @ sk_B)),
% 1.35/1.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.55  thf('67', plain,
% 1.35/1.56      (((k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 1.35/1.56         = (sk_A))),
% 1.35/1.56      inference('demod', [status(thm)], ['64', '65', '66'])).
% 1.35/1.56  thf('68', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.35/1.56      inference('simplify', [status(thm)], ['1'])).
% 1.35/1.56  thf('69', plain,
% 1.35/1.56      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.35/1.56      inference('sup+', [status(thm)], ['33', '34'])).
% 1.35/1.56  thf('70', plain,
% 1.35/1.56      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.35/1.56         ((r1_tarski @ X8 @ X9) | ~ (r1_tarski @ X8 @ (k3_xboole_0 @ X9 @ X10)))),
% 1.35/1.56      inference('cnf', [status(esa)], [t18_xboole_1])).
% 1.35/1.56  thf('71', plain,
% 1.35/1.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.35/1.56         (~ (r1_tarski @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r1_tarski @ X2 @ X0))),
% 1.35/1.56      inference('sup-', [status(thm)], ['69', '70'])).
% 1.35/1.56  thf('72', plain,
% 1.35/1.56      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 1.35/1.56      inference('sup-', [status(thm)], ['68', '71'])).
% 1.35/1.56  thf('73', plain,
% 1.35/1.56      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 1.35/1.56      inference('sup+', [status(thm)], ['67', '72'])).
% 1.35/1.56  thf('74', plain, ($false), inference('demod', [status(thm)], ['0', '73'])).
% 1.35/1.56  
% 1.35/1.56  % SZS output end Refutation
% 1.35/1.56  
% 1.35/1.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
