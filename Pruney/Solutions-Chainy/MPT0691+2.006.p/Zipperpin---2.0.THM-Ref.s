%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Yjzm2uu2rv

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:18 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 215 expanded)
%              Number of leaves         :   32 (  78 expanded)
%              Depth                    :   22
%              Number of atoms          :  717 (1681 expanded)
%              Number of equality atoms :   56 ( 126 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

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
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( r1_tarski @ X23 @ X24 )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X25 @ X24 ) @ X23 )
        = ( k9_relat_1 @ X25 @ X23 ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
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
    ! [X20: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('6',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('7',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('8',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('9',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      | ~ ( r1_tarski @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('13',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ X14 @ ( k2_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      | ~ ( r1_tarski @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['6','21'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('23',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('24',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['22','25'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('27',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('28',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('30',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('31',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_tarski @ X17 @ X16 )
      = ( k2_tarski @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('32',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
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
    ! [X27: $i,X28: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X27 @ X28 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X27 ) @ X28 ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf(t139_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('37',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X30 @ X29 ) @ X31 )
        = ( k3_xboole_0 @ X29 @ ( k10_relat_1 @ X30 @ X31 ) ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('38',plain,(
    ! [X26: $i] :
      ( ( ( k10_relat_1 @ X26 @ ( k2_relat_1 @ X26 ) )
        = ( k1_relat_1 @ X26 ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['39','40'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('42',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ( X0
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( X0
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['36','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ X0 @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k3_xboole_0 @ X1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( X1
        = ( k1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['35','47'])).

thf('49',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['30','48'])).

thf('50',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['1'])).

thf('51',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( sk_A
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('53',plain,(
    ! [X22: $i] :
      ( ( ( k9_relat_1 @ X22 @ ( k1_relat_1 @ X22 ) )
        = ( k2_relat_1 @ X22 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('54',plain,
    ( ( ( k9_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ sk_A )
      = ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( k9_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ sk_A )
      = ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['5','54'])).

thf('56',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( k9_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ sk_A )
    = ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( ( k9_relat_1 @ sk_B @ sk_A )
      = ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['4','57'])).

thf('59',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( k9_relat_1 @ sk_B @ sk_A )
    = ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('62',plain,
    ( ( ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,
    ( sk_A
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('64',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    = sk_A ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('67',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['65','68'])).

thf('70',plain,(
    $false ),
    inference(demod,[status(thm)],['0','69'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Yjzm2uu2rv
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:28:12 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.36/0.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.60  % Solved by: fo/fo7.sh
% 0.36/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.60  % done 477 iterations in 0.151s
% 0.36/0.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.60  % SZS output start Refutation
% 0.36/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.60  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.36/0.60  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.36/0.60  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.36/0.60  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.36/0.60  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.36/0.60  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.36/0.60  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.36/0.60  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.36/0.60  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.36/0.60  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.36/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.60  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.36/0.60  thf(t146_funct_1, conjecture,
% 0.36/0.60    (![A:$i,B:$i]:
% 0.36/0.60     ( ( v1_relat_1 @ B ) =>
% 0.36/0.60       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.36/0.60         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 0.36/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.60    (~( ![A:$i,B:$i]:
% 0.36/0.60        ( ( v1_relat_1 @ B ) =>
% 0.36/0.60          ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.36/0.60            ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )),
% 0.36/0.60    inference('cnf.neg', [status(esa)], [t146_funct_1])).
% 0.36/0.60  thf('0', plain,
% 0.36/0.60      (~ (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf(d10_xboole_0, axiom,
% 0.36/0.60    (![A:$i,B:$i]:
% 0.36/0.60     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.36/0.60  thf('1', plain,
% 0.36/0.60      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 0.36/0.60      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.36/0.60  thf('2', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.36/0.60      inference('simplify', [status(thm)], ['1'])).
% 0.36/0.60  thf(t162_relat_1, axiom,
% 0.36/0.60    (![A:$i]:
% 0.36/0.60     ( ( v1_relat_1 @ A ) =>
% 0.36/0.60       ( ![B:$i,C:$i]:
% 0.36/0.60         ( ( r1_tarski @ B @ C ) =>
% 0.36/0.60           ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B ) =
% 0.36/0.60             ( k9_relat_1 @ A @ B ) ) ) ) ))).
% 0.36/0.60  thf('3', plain,
% 0.36/0.60      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.36/0.60         (~ (r1_tarski @ X23 @ X24)
% 0.36/0.60          | ((k9_relat_1 @ (k7_relat_1 @ X25 @ X24) @ X23)
% 0.36/0.60              = (k9_relat_1 @ X25 @ X23))
% 0.36/0.60          | ~ (v1_relat_1 @ X25))),
% 0.36/0.60      inference('cnf', [status(esa)], [t162_relat_1])).
% 0.36/0.60  thf('4', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]:
% 0.36/0.60         (~ (v1_relat_1 @ X1)
% 0.36/0.60          | ((k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X0)
% 0.36/0.60              = (k9_relat_1 @ X1 @ X0)))),
% 0.36/0.60      inference('sup-', [status(thm)], ['2', '3'])).
% 0.36/0.60  thf(dt_k7_relat_1, axiom,
% 0.36/0.60    (![A:$i,B:$i]:
% 0.36/0.60     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.36/0.60  thf('5', plain,
% 0.36/0.60      (![X20 : $i, X21 : $i]:
% 0.36/0.60         (~ (v1_relat_1 @ X20) | (v1_relat_1 @ (k7_relat_1 @ X20 @ X21)))),
% 0.36/0.60      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.36/0.60  thf('6', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf(t3_boole, axiom,
% 0.36/0.60    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.36/0.60  thf('7', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.36/0.60      inference('cnf', [status(esa)], [t3_boole])).
% 0.36/0.60  thf('8', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.36/0.60      inference('simplify', [status(thm)], ['1'])).
% 0.36/0.60  thf(t43_xboole_1, axiom,
% 0.36/0.60    (![A:$i,B:$i,C:$i]:
% 0.36/0.60     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 0.36/0.60       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 0.36/0.60  thf('9', plain,
% 0.36/0.60      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.36/0.60         ((r1_tarski @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 0.36/0.60          | ~ (r1_tarski @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 0.36/0.60      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.36/0.60  thf('10', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]:
% 0.36/0.60         (r1_tarski @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ X0)),
% 0.36/0.60      inference('sup-', [status(thm)], ['8', '9'])).
% 0.36/0.60  thf('11', plain,
% 0.36/0.60      (![X0 : $i]: (r1_tarski @ (k2_xboole_0 @ k1_xboole_0 @ X0) @ X0)),
% 0.36/0.60      inference('sup+', [status(thm)], ['7', '10'])).
% 0.36/0.60  thf(commutativity_k2_xboole_0, axiom,
% 0.36/0.60    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.36/0.60  thf('12', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.36/0.60      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.36/0.60  thf(t7_xboole_1, axiom,
% 0.36/0.60    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.36/0.60  thf('13', plain,
% 0.36/0.60      (![X14 : $i, X15 : $i]: (r1_tarski @ X14 @ (k2_xboole_0 @ X14 @ X15))),
% 0.36/0.60      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.36/0.60  thf('14', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.36/0.60      inference('sup+', [status(thm)], ['12', '13'])).
% 0.36/0.60  thf('15', plain,
% 0.36/0.60      (![X2 : $i, X4 : $i]:
% 0.36/0.60         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 0.36/0.60      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.36/0.60  thf('16', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]:
% 0.36/0.60         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 0.36/0.60          | ((k2_xboole_0 @ X1 @ X0) = (X0)))),
% 0.36/0.60      inference('sup-', [status(thm)], ['14', '15'])).
% 0.36/0.60  thf('17', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.36/0.60      inference('sup-', [status(thm)], ['11', '16'])).
% 0.36/0.60  thf('18', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.36/0.60      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.36/0.60  thf('19', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.36/0.60      inference('sup+', [status(thm)], ['17', '18'])).
% 0.36/0.60  thf('20', plain,
% 0.36/0.60      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.36/0.60         ((r1_tarski @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 0.36/0.60          | ~ (r1_tarski @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 0.36/0.60      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.36/0.60  thf('21', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]:
% 0.36/0.60         (~ (r1_tarski @ X1 @ X0)
% 0.36/0.60          | (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ k1_xboole_0))),
% 0.36/0.60      inference('sup-', [status(thm)], ['19', '20'])).
% 0.36/0.60  thf('22', plain,
% 0.36/0.60      ((r1_tarski @ (k4_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)) @ k1_xboole_0)),
% 0.36/0.60      inference('sup-', [status(thm)], ['6', '21'])).
% 0.36/0.60  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.36/0.60  thf('23', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.36/0.60      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.36/0.60  thf('24', plain,
% 0.36/0.60      (![X2 : $i, X4 : $i]:
% 0.36/0.60         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 0.36/0.60      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.36/0.60  thf('25', plain,
% 0.36/0.60      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.36/0.60      inference('sup-', [status(thm)], ['23', '24'])).
% 0.36/0.60  thf('26', plain,
% 0.36/0.60      (((k4_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)) = (k1_xboole_0))),
% 0.36/0.60      inference('sup-', [status(thm)], ['22', '25'])).
% 0.36/0.60  thf(t48_xboole_1, axiom,
% 0.36/0.60    (![A:$i,B:$i]:
% 0.36/0.60     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.36/0.60  thf('27', plain,
% 0.36/0.60      (![X12 : $i, X13 : $i]:
% 0.36/0.60         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 0.36/0.60           = (k3_xboole_0 @ X12 @ X13))),
% 0.36/0.60      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.36/0.60  thf('28', plain,
% 0.36/0.60      (((k4_xboole_0 @ sk_A @ k1_xboole_0)
% 0.36/0.60         = (k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.36/0.60      inference('sup+', [status(thm)], ['26', '27'])).
% 0.36/0.60  thf('29', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.36/0.60      inference('cnf', [status(esa)], [t3_boole])).
% 0.36/0.60  thf('30', plain, (((sk_A) = (k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.36/0.60      inference('demod', [status(thm)], ['28', '29'])).
% 0.36/0.60  thf(commutativity_k2_tarski, axiom,
% 0.36/0.60    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.36/0.60  thf('31', plain,
% 0.36/0.60      (![X16 : $i, X17 : $i]:
% 0.36/0.60         ((k2_tarski @ X17 @ X16) = (k2_tarski @ X16 @ X17))),
% 0.36/0.60      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.36/0.60  thf(t12_setfam_1, axiom,
% 0.36/0.60    (![A:$i,B:$i]:
% 0.36/0.60     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.36/0.60  thf('32', plain,
% 0.36/0.60      (![X18 : $i, X19 : $i]:
% 0.36/0.60         ((k1_setfam_1 @ (k2_tarski @ X18 @ X19)) = (k3_xboole_0 @ X18 @ X19))),
% 0.36/0.60      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.36/0.60  thf('33', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]:
% 0.36/0.60         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.36/0.60      inference('sup+', [status(thm)], ['31', '32'])).
% 0.36/0.60  thf('34', plain,
% 0.36/0.60      (![X18 : $i, X19 : $i]:
% 0.36/0.60         ((k1_setfam_1 @ (k2_tarski @ X18 @ X19)) = (k3_xboole_0 @ X18 @ X19))),
% 0.36/0.60      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.36/0.60  thf('35', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.36/0.60      inference('sup+', [status(thm)], ['33', '34'])).
% 0.36/0.60  thf(t90_relat_1, axiom,
% 0.36/0.60    (![A:$i,B:$i]:
% 0.36/0.60     ( ( v1_relat_1 @ B ) =>
% 0.36/0.60       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 0.36/0.60         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.36/0.60  thf('36', plain,
% 0.36/0.60      (![X27 : $i, X28 : $i]:
% 0.36/0.60         (((k1_relat_1 @ (k7_relat_1 @ X27 @ X28))
% 0.36/0.60            = (k3_xboole_0 @ (k1_relat_1 @ X27) @ X28))
% 0.36/0.60          | ~ (v1_relat_1 @ X27))),
% 0.36/0.60      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.36/0.60  thf(t139_funct_1, axiom,
% 0.36/0.60    (![A:$i,B:$i,C:$i]:
% 0.36/0.60     ( ( v1_relat_1 @ C ) =>
% 0.36/0.60       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.36/0.60         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.36/0.60  thf('37', plain,
% 0.36/0.60      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.36/0.60         (((k10_relat_1 @ (k7_relat_1 @ X30 @ X29) @ X31)
% 0.36/0.60            = (k3_xboole_0 @ X29 @ (k10_relat_1 @ X30 @ X31)))
% 0.36/0.60          | ~ (v1_relat_1 @ X30))),
% 0.36/0.60      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.36/0.60  thf(t169_relat_1, axiom,
% 0.36/0.60    (![A:$i]:
% 0.36/0.60     ( ( v1_relat_1 @ A ) =>
% 0.36/0.60       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.36/0.60  thf('38', plain,
% 0.36/0.60      (![X26 : $i]:
% 0.36/0.60         (((k10_relat_1 @ X26 @ (k2_relat_1 @ X26)) = (k1_relat_1 @ X26))
% 0.36/0.60          | ~ (v1_relat_1 @ X26))),
% 0.36/0.60      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.36/0.60  thf('39', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]:
% 0.36/0.60         (((k3_xboole_0 @ X0 @ 
% 0.36/0.60            (k10_relat_1 @ X1 @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X0))))
% 0.36/0.60            = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.36/0.60          | ~ (v1_relat_1 @ X1)
% 0.36/0.60          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.36/0.60      inference('sup+', [status(thm)], ['37', '38'])).
% 0.36/0.60  thf('40', plain,
% 0.36/0.60      (![X20 : $i, X21 : $i]:
% 0.36/0.60         (~ (v1_relat_1 @ X20) | (v1_relat_1 @ (k7_relat_1 @ X20 @ X21)))),
% 0.36/0.60      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.36/0.60  thf('41', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]:
% 0.36/0.60         (~ (v1_relat_1 @ X1)
% 0.36/0.60          | ((k3_xboole_0 @ X0 @ 
% 0.36/0.60              (k10_relat_1 @ X1 @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X0))))
% 0.36/0.60              = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 0.36/0.60      inference('clc', [status(thm)], ['39', '40'])).
% 0.36/0.60  thf(t17_xboole_1, axiom,
% 0.36/0.60    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.36/0.60  thf('42', plain,
% 0.36/0.60      (![X5 : $i, X6 : $i]: (r1_tarski @ (k3_xboole_0 @ X5 @ X6) @ X5)),
% 0.36/0.60      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.36/0.60  thf('43', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]:
% 0.36/0.60         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X0)
% 0.36/0.60          | ~ (v1_relat_1 @ X1))),
% 0.36/0.60      inference('sup+', [status(thm)], ['41', '42'])).
% 0.36/0.60  thf('44', plain,
% 0.36/0.60      (![X2 : $i, X4 : $i]:
% 0.36/0.60         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 0.36/0.60      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.36/0.60  thf('45', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]:
% 0.36/0.60         (~ (v1_relat_1 @ X1)
% 0.36/0.60          | ~ (r1_tarski @ X0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.36/0.60          | ((X0) = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 0.36/0.60      inference('sup-', [status(thm)], ['43', '44'])).
% 0.36/0.60  thf('46', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]:
% 0.36/0.60         (~ (r1_tarski @ X0 @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0))
% 0.36/0.60          | ~ (v1_relat_1 @ X1)
% 0.36/0.60          | ((X0) = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.36/0.60          | ~ (v1_relat_1 @ X1))),
% 0.36/0.60      inference('sup-', [status(thm)], ['36', '45'])).
% 0.36/0.60  thf('47', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]:
% 0.36/0.60         (((X0) = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.36/0.60          | ~ (v1_relat_1 @ X1)
% 0.36/0.60          | ~ (r1_tarski @ X0 @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0)))),
% 0.36/0.60      inference('simplify', [status(thm)], ['46'])).
% 0.36/0.60  thf('48', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]:
% 0.36/0.60         (~ (r1_tarski @ X1 @ (k3_xboole_0 @ X1 @ (k1_relat_1 @ X0)))
% 0.36/0.60          | ~ (v1_relat_1 @ X0)
% 0.36/0.60          | ((X1) = (k1_relat_1 @ (k7_relat_1 @ X0 @ X1))))),
% 0.36/0.60      inference('sup-', [status(thm)], ['35', '47'])).
% 0.36/0.60  thf('49', plain,
% 0.36/0.60      ((~ (r1_tarski @ sk_A @ sk_A)
% 0.36/0.60        | ((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.36/0.60        | ~ (v1_relat_1 @ sk_B))),
% 0.36/0.60      inference('sup-', [status(thm)], ['30', '48'])).
% 0.36/0.60  thf('50', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.36/0.60      inference('simplify', [status(thm)], ['1'])).
% 0.36/0.60  thf('51', plain, ((v1_relat_1 @ sk_B)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('52', plain, (((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.36/0.60      inference('demod', [status(thm)], ['49', '50', '51'])).
% 0.36/0.60  thf(t146_relat_1, axiom,
% 0.36/0.60    (![A:$i]:
% 0.36/0.60     ( ( v1_relat_1 @ A ) =>
% 0.36/0.60       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.36/0.60  thf('53', plain,
% 0.36/0.60      (![X22 : $i]:
% 0.36/0.60         (((k9_relat_1 @ X22 @ (k1_relat_1 @ X22)) = (k2_relat_1 @ X22))
% 0.36/0.60          | ~ (v1_relat_1 @ X22))),
% 0.36/0.60      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.36/0.60  thf('54', plain,
% 0.36/0.60      ((((k9_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ sk_A)
% 0.36/0.60          = (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.36/0.60        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.36/0.60      inference('sup+', [status(thm)], ['52', '53'])).
% 0.36/0.60  thf('55', plain,
% 0.36/0.60      ((~ (v1_relat_1 @ sk_B)
% 0.36/0.60        | ((k9_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ sk_A)
% 0.36/0.60            = (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))))),
% 0.36/0.60      inference('sup-', [status(thm)], ['5', '54'])).
% 0.36/0.60  thf('56', plain, ((v1_relat_1 @ sk_B)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('57', plain,
% 0.36/0.60      (((k9_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ sk_A)
% 0.36/0.60         = (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.36/0.60      inference('demod', [status(thm)], ['55', '56'])).
% 0.36/0.60  thf('58', plain,
% 0.36/0.60      ((((k9_relat_1 @ sk_B @ sk_A) = (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.36/0.60        | ~ (v1_relat_1 @ sk_B))),
% 0.36/0.60      inference('sup+', [status(thm)], ['4', '57'])).
% 0.36/0.60  thf('59', plain, ((v1_relat_1 @ sk_B)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('60', plain,
% 0.36/0.60      (((k9_relat_1 @ sk_B @ sk_A) = (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.36/0.60      inference('demod', [status(thm)], ['58', '59'])).
% 0.36/0.60  thf('61', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]:
% 0.36/0.60         (~ (v1_relat_1 @ X1)
% 0.36/0.60          | ((k3_xboole_0 @ X0 @ 
% 0.36/0.60              (k10_relat_1 @ X1 @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X0))))
% 0.36/0.60              = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 0.36/0.60      inference('clc', [status(thm)], ['39', '40'])).
% 0.36/0.60  thf('62', plain,
% 0.36/0.60      ((((k3_xboole_0 @ sk_A @ 
% 0.36/0.60          (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 0.36/0.60          = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.36/0.60        | ~ (v1_relat_1 @ sk_B))),
% 0.36/0.60      inference('sup+', [status(thm)], ['60', '61'])).
% 0.36/0.60  thf('63', plain, (((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.36/0.60      inference('demod', [status(thm)], ['49', '50', '51'])).
% 0.36/0.60  thf('64', plain, ((v1_relat_1 @ sk_B)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('65', plain,
% 0.36/0.60      (((k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 0.36/0.60         = (sk_A))),
% 0.36/0.60      inference('demod', [status(thm)], ['62', '63', '64'])).
% 0.36/0.60  thf('66', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.36/0.60      inference('sup+', [status(thm)], ['33', '34'])).
% 0.36/0.60  thf('67', plain,
% 0.36/0.60      (![X5 : $i, X6 : $i]: (r1_tarski @ (k3_xboole_0 @ X5 @ X6) @ X5)),
% 0.36/0.60      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.36/0.60  thf('68', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.36/0.60      inference('sup+', [status(thm)], ['66', '67'])).
% 0.36/0.60  thf('69', plain,
% 0.36/0.60      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 0.36/0.60      inference('sup+', [status(thm)], ['65', '68'])).
% 0.36/0.60  thf('70', plain, ($false), inference('demod', [status(thm)], ['0', '69'])).
% 0.36/0.60  
% 0.36/0.60  % SZS output end Refutation
% 0.36/0.60  
% 0.36/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
