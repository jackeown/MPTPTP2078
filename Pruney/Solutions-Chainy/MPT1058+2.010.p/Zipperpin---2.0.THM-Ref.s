%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wP6fNSMhSZ

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:38 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 136 expanded)
%              Number of leaves         :   33 (  59 expanded)
%              Depth                    :   13
%              Number of atoms          :  671 (1054 expanded)
%              Number of equality atoms :   46 (  79 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(t139_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('0',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X30 @ X29 ) @ X31 )
        = ( k3_xboole_0 @ X29 @ ( k10_relat_1 @ X30 @ X31 ) ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf(t175_funct_2,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B )
         => ( ( k10_relat_1 @ A @ C )
            = ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ! [B: $i,C: $i] :
            ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B )
           => ( ( k10_relat_1 @ A @ C )
              = ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t175_funct_2])).

thf('1',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('2',plain,(
    ! [X22: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X22 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('3',plain,(
    ! [X18: $i] :
      ( ( ( k10_relat_1 @ X18 @ ( k2_relat_1 @ X18 ) )
        = ( k1_relat_1 @ X18 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
        = ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X21: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X21 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('6',plain,(
    ! [X27: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf(t145_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ) )).

thf('8',plain,(
    ! [X32: $i,X33: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X32 @ ( k10_relat_1 @ X32 @ X33 ) ) @ X33 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t145_funct_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X27: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('11',plain,(
    ! [X28: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('13',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    r1_tarski @ ( k9_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C ) ) @ ( k10_relat_1 @ sk_A @ sk_C ) ) @ sk_B ),
    inference('sup-',[status(thm)],['1','14'])).

thf('16',plain,(
    ! [X21: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X21 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('18',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['17'])).

thf(t163_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) )
          & ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('19',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( r1_tarski @ X34 @ ( k1_relat_1 @ X35 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X35 @ X34 ) @ X36 )
      | ( r1_tarski @ X34 @ ( k10_relat_1 @ X35 @ X36 ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t163_funct_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ X1 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','20'])).

thf('22',plain,(
    ! [X21: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X21 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('23',plain,(
    ! [X28: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('24',plain,(
    ! [X27: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) @ X1 )
      | ( r1_tarski @ X0 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['21','22','23','24'])).

thf('26',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C ) @ ( k10_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['15','25'])).

thf('27',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('28',plain,
    ( ~ ( r1_tarski @ ( k10_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C ) ) @ sk_B ) @ ( k10_relat_1 @ sk_A @ sk_C ) )
    | ( ( k10_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C ) ) @ sk_B )
      = ( k10_relat_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('29',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k7_relat_1 @ X26 @ X25 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X25 ) @ X26 ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('30',plain,(
    ! [X21: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X21 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('31',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X20 @ X19 ) )
        = ( k10_relat_1 @ X20 @ ( k1_relat_1 @ X19 ) ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X27: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
        = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['29','34'])).

thf('36',plain,(
    ! [X21: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X21 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('37',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X23 @ X24 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X23 ) @ X24 ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( k3_xboole_0 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X27: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X27: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('42',plain,(
    ! [X27: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['35','40','41','42'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('44',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_tarski @ X13 @ X12 )
      = ( k2_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('45',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('49',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('50',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['48','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['35','40','41','42'])).

thf('54',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) )
    = ( k10_relat_1 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['28','43','52','53'])).

thf('55',plain,
    ( ( ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C )
      = ( k10_relat_1 @ sk_A @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['0','54'])).

thf('56',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C )
    = ( k10_relat_1 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ( k10_relat_1 @ sk_A @ sk_C )
 != ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['57','58'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wP6fNSMhSZ
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:49:54 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.45/0.70  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.70  % Solved by: fo/fo7.sh
% 0.45/0.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.70  % done 420 iterations in 0.243s
% 0.45/0.70  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.70  % SZS output start Refutation
% 0.45/0.70  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.45/0.70  thf(sk_C_type, type, sk_C: $i).
% 0.45/0.70  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.45/0.70  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.45/0.70  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.45/0.70  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.45/0.70  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.70  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.45/0.70  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.45/0.70  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.45/0.70  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.70  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.45/0.70  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.45/0.70  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.45/0.70  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.70  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.45/0.70  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.45/0.70  thf(t139_funct_1, axiom,
% 0.45/0.70    (![A:$i,B:$i,C:$i]:
% 0.45/0.70     ( ( v1_relat_1 @ C ) =>
% 0.45/0.70       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.45/0.70         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.45/0.70  thf('0', plain,
% 0.45/0.70      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.45/0.70         (((k10_relat_1 @ (k7_relat_1 @ X30 @ X29) @ X31)
% 0.45/0.70            = (k3_xboole_0 @ X29 @ (k10_relat_1 @ X30 @ X31)))
% 0.45/0.70          | ~ (v1_relat_1 @ X30))),
% 0.45/0.70      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.45/0.70  thf(t175_funct_2, conjecture,
% 0.45/0.70    (![A:$i]:
% 0.45/0.70     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.45/0.70       ( ![B:$i,C:$i]:
% 0.45/0.70         ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.45/0.70           ( ( k10_relat_1 @ A @ C ) =
% 0.45/0.70             ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ))).
% 0.45/0.70  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.70    (~( ![A:$i]:
% 0.45/0.70        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.45/0.70          ( ![B:$i,C:$i]:
% 0.45/0.70            ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.45/0.70              ( ( k10_relat_1 @ A @ C ) =
% 0.45/0.70                ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ) )),
% 0.45/0.70    inference('cnf.neg', [status(esa)], [t175_funct_2])).
% 0.45/0.70  thf('1', plain, ((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C) @ sk_B)),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf(t71_relat_1, axiom,
% 0.45/0.70    (![A:$i]:
% 0.45/0.70     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.45/0.70       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.45/0.70  thf('2', plain, (![X22 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X22)) = (X22))),
% 0.45/0.70      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.45/0.70  thf(t169_relat_1, axiom,
% 0.45/0.70    (![A:$i]:
% 0.45/0.70     ( ( v1_relat_1 @ A ) =>
% 0.45/0.70       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.45/0.70  thf('3', plain,
% 0.45/0.70      (![X18 : $i]:
% 0.45/0.70         (((k10_relat_1 @ X18 @ (k2_relat_1 @ X18)) = (k1_relat_1 @ X18))
% 0.45/0.70          | ~ (v1_relat_1 @ X18))),
% 0.45/0.70      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.45/0.70  thf('4', plain,
% 0.45/0.70      (![X0 : $i]:
% 0.45/0.70         (((k10_relat_1 @ (k6_relat_1 @ X0) @ X0)
% 0.45/0.70            = (k1_relat_1 @ (k6_relat_1 @ X0)))
% 0.45/0.70          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.45/0.70      inference('sup+', [status(thm)], ['2', '3'])).
% 0.45/0.70  thf('5', plain, (![X21 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X21)) = (X21))),
% 0.45/0.70      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.45/0.70  thf(fc3_funct_1, axiom,
% 0.45/0.70    (![A:$i]:
% 0.45/0.70     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.45/0.70       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.45/0.70  thf('6', plain, (![X27 : $i]: (v1_relat_1 @ (k6_relat_1 @ X27))),
% 0.45/0.70      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.45/0.70  thf('7', plain,
% 0.45/0.70      (![X0 : $i]: ((k10_relat_1 @ (k6_relat_1 @ X0) @ X0) = (X0))),
% 0.45/0.70      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.45/0.70  thf(t145_funct_1, axiom,
% 0.45/0.70    (![A:$i,B:$i]:
% 0.45/0.70     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.45/0.70       ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ))).
% 0.45/0.70  thf('8', plain,
% 0.45/0.70      (![X32 : $i, X33 : $i]:
% 0.45/0.70         ((r1_tarski @ (k9_relat_1 @ X32 @ (k10_relat_1 @ X32 @ X33)) @ X33)
% 0.45/0.70          | ~ (v1_funct_1 @ X32)
% 0.45/0.70          | ~ (v1_relat_1 @ X32))),
% 0.45/0.70      inference('cnf', [status(esa)], [t145_funct_1])).
% 0.45/0.70  thf('9', plain,
% 0.45/0.70      (![X0 : $i]:
% 0.45/0.70         ((r1_tarski @ (k9_relat_1 @ (k6_relat_1 @ X0) @ X0) @ X0)
% 0.45/0.70          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.45/0.70          | ~ (v1_funct_1 @ (k6_relat_1 @ X0)))),
% 0.45/0.70      inference('sup+', [status(thm)], ['7', '8'])).
% 0.45/0.70  thf('10', plain, (![X27 : $i]: (v1_relat_1 @ (k6_relat_1 @ X27))),
% 0.45/0.70      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.45/0.70  thf('11', plain, (![X28 : $i]: (v1_funct_1 @ (k6_relat_1 @ X28))),
% 0.45/0.70      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.45/0.70  thf('12', plain,
% 0.45/0.70      (![X0 : $i]: (r1_tarski @ (k9_relat_1 @ (k6_relat_1 @ X0) @ X0) @ X0)),
% 0.45/0.70      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.45/0.70  thf(t1_xboole_1, axiom,
% 0.45/0.70    (![A:$i,B:$i,C:$i]:
% 0.45/0.70     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.45/0.70       ( r1_tarski @ A @ C ) ))).
% 0.45/0.70  thf('13', plain,
% 0.45/0.70      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.45/0.70         (~ (r1_tarski @ X5 @ X6)
% 0.45/0.70          | ~ (r1_tarski @ X6 @ X7)
% 0.45/0.70          | (r1_tarski @ X5 @ X7))),
% 0.45/0.70      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.45/0.70  thf('14', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i]:
% 0.45/0.70         ((r1_tarski @ (k9_relat_1 @ (k6_relat_1 @ X0) @ X0) @ X1)
% 0.45/0.70          | ~ (r1_tarski @ X0 @ X1))),
% 0.45/0.70      inference('sup-', [status(thm)], ['12', '13'])).
% 0.45/0.70  thf('15', plain,
% 0.45/0.70      ((r1_tarski @ 
% 0.45/0.70        (k9_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C)) @ 
% 0.45/0.70         (k10_relat_1 @ sk_A @ sk_C)) @ 
% 0.45/0.70        sk_B)),
% 0.45/0.70      inference('sup-', [status(thm)], ['1', '14'])).
% 0.45/0.70  thf('16', plain, (![X21 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X21)) = (X21))),
% 0.45/0.70      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.45/0.70  thf(d10_xboole_0, axiom,
% 0.45/0.70    (![A:$i,B:$i]:
% 0.45/0.70     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.45/0.70  thf('17', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.45/0.70      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.45/0.70  thf('18', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.45/0.70      inference('simplify', [status(thm)], ['17'])).
% 0.45/0.70  thf(t163_funct_1, axiom,
% 0.45/0.70    (![A:$i,B:$i,C:$i]:
% 0.45/0.70     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.45/0.70       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & 
% 0.45/0.70           ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) ) =>
% 0.45/0.70         ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.45/0.70  thf('19', plain,
% 0.45/0.70      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.45/0.70         (~ (r1_tarski @ X34 @ (k1_relat_1 @ X35))
% 0.45/0.70          | ~ (r1_tarski @ (k9_relat_1 @ X35 @ X34) @ X36)
% 0.45/0.70          | (r1_tarski @ X34 @ (k10_relat_1 @ X35 @ X36))
% 0.45/0.70          | ~ (v1_funct_1 @ X35)
% 0.45/0.70          | ~ (v1_relat_1 @ X35))),
% 0.45/0.70      inference('cnf', [status(esa)], [t163_funct_1])).
% 0.45/0.70  thf('20', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i]:
% 0.45/0.70         (~ (v1_relat_1 @ X0)
% 0.45/0.70          | ~ (v1_funct_1 @ X0)
% 0.45/0.70          | (r1_tarski @ (k1_relat_1 @ X0) @ (k10_relat_1 @ X0 @ X1))
% 0.45/0.70          | ~ (r1_tarski @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)) @ X1))),
% 0.45/0.70      inference('sup-', [status(thm)], ['18', '19'])).
% 0.45/0.70  thf('21', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i]:
% 0.45/0.70         (~ (r1_tarski @ (k9_relat_1 @ (k6_relat_1 @ X0) @ X0) @ X1)
% 0.45/0.70          | (r1_tarski @ (k1_relat_1 @ (k6_relat_1 @ X0)) @ 
% 0.45/0.70             (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.45/0.70          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 0.45/0.70          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.45/0.70      inference('sup-', [status(thm)], ['16', '20'])).
% 0.45/0.70  thf('22', plain, (![X21 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X21)) = (X21))),
% 0.45/0.70      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.45/0.70  thf('23', plain, (![X28 : $i]: (v1_funct_1 @ (k6_relat_1 @ X28))),
% 0.45/0.70      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.45/0.70  thf('24', plain, (![X27 : $i]: (v1_relat_1 @ (k6_relat_1 @ X27))),
% 0.45/0.70      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.45/0.70  thf('25', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i]:
% 0.45/0.70         (~ (r1_tarski @ (k9_relat_1 @ (k6_relat_1 @ X0) @ X0) @ X1)
% 0.45/0.70          | (r1_tarski @ X0 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1)))),
% 0.45/0.70      inference('demod', [status(thm)], ['21', '22', '23', '24'])).
% 0.45/0.70  thf('26', plain,
% 0.45/0.70      ((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C) @ 
% 0.45/0.70        (k10_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C)) @ sk_B))),
% 0.45/0.70      inference('sup-', [status(thm)], ['15', '25'])).
% 0.45/0.70  thf('27', plain,
% 0.45/0.70      (![X0 : $i, X2 : $i]:
% 0.45/0.70         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.45/0.70      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.45/0.70  thf('28', plain,
% 0.45/0.70      ((~ (r1_tarski @ 
% 0.45/0.70           (k10_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C)) @ sk_B) @ 
% 0.45/0.70           (k10_relat_1 @ sk_A @ sk_C))
% 0.45/0.70        | ((k10_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C)) @ sk_B)
% 0.45/0.70            = (k10_relat_1 @ sk_A @ sk_C)))),
% 0.45/0.70      inference('sup-', [status(thm)], ['26', '27'])).
% 0.45/0.70  thf(t94_relat_1, axiom,
% 0.45/0.70    (![A:$i,B:$i]:
% 0.45/0.70     ( ( v1_relat_1 @ B ) =>
% 0.45/0.70       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.45/0.70  thf('29', plain,
% 0.45/0.70      (![X25 : $i, X26 : $i]:
% 0.45/0.70         (((k7_relat_1 @ X26 @ X25) = (k5_relat_1 @ (k6_relat_1 @ X25) @ X26))
% 0.45/0.70          | ~ (v1_relat_1 @ X26))),
% 0.45/0.70      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.45/0.70  thf('30', plain, (![X21 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X21)) = (X21))),
% 0.45/0.70      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.45/0.70  thf(t182_relat_1, axiom,
% 0.45/0.70    (![A:$i]:
% 0.45/0.70     ( ( v1_relat_1 @ A ) =>
% 0.45/0.70       ( ![B:$i]:
% 0.45/0.70         ( ( v1_relat_1 @ B ) =>
% 0.45/0.70           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.45/0.70             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.45/0.70  thf('31', plain,
% 0.45/0.70      (![X19 : $i, X20 : $i]:
% 0.45/0.70         (~ (v1_relat_1 @ X19)
% 0.45/0.70          | ((k1_relat_1 @ (k5_relat_1 @ X20 @ X19))
% 0.45/0.70              = (k10_relat_1 @ X20 @ (k1_relat_1 @ X19)))
% 0.45/0.70          | ~ (v1_relat_1 @ X20))),
% 0.45/0.70      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.45/0.70  thf('32', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i]:
% 0.45/0.70         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.45/0.70            = (k10_relat_1 @ X1 @ X0))
% 0.45/0.70          | ~ (v1_relat_1 @ X1)
% 0.45/0.70          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.45/0.70      inference('sup+', [status(thm)], ['30', '31'])).
% 0.45/0.70  thf('33', plain, (![X27 : $i]: (v1_relat_1 @ (k6_relat_1 @ X27))),
% 0.45/0.70      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.45/0.70  thf('34', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i]:
% 0.45/0.70         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.45/0.70            = (k10_relat_1 @ X1 @ X0))
% 0.45/0.70          | ~ (v1_relat_1 @ X1))),
% 0.45/0.70      inference('demod', [status(thm)], ['32', '33'])).
% 0.45/0.70  thf('35', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i]:
% 0.45/0.70         (((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.45/0.70            = (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.45/0.70          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.45/0.70          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.45/0.70      inference('sup+', [status(thm)], ['29', '34'])).
% 0.45/0.70  thf('36', plain, (![X21 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X21)) = (X21))),
% 0.45/0.70      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.45/0.70  thf(t90_relat_1, axiom,
% 0.45/0.70    (![A:$i,B:$i]:
% 0.45/0.70     ( ( v1_relat_1 @ B ) =>
% 0.45/0.70       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 0.45/0.70         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.45/0.70  thf('37', plain,
% 0.45/0.70      (![X23 : $i, X24 : $i]:
% 0.45/0.70         (((k1_relat_1 @ (k7_relat_1 @ X23 @ X24))
% 0.45/0.70            = (k3_xboole_0 @ (k1_relat_1 @ X23) @ X24))
% 0.45/0.70          | ~ (v1_relat_1 @ X23))),
% 0.45/0.70      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.45/0.70  thf('38', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i]:
% 0.45/0.70         (((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.45/0.70            = (k3_xboole_0 @ X0 @ X1))
% 0.45/0.70          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.45/0.70      inference('sup+', [status(thm)], ['36', '37'])).
% 0.45/0.70  thf('39', plain, (![X27 : $i]: (v1_relat_1 @ (k6_relat_1 @ X27))),
% 0.45/0.70      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.45/0.70  thf('40', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i]:
% 0.45/0.70         ((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.45/0.70           = (k3_xboole_0 @ X0 @ X1))),
% 0.45/0.70      inference('demod', [status(thm)], ['38', '39'])).
% 0.45/0.70  thf('41', plain, (![X27 : $i]: (v1_relat_1 @ (k6_relat_1 @ X27))),
% 0.45/0.70      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.45/0.70  thf('42', plain, (![X27 : $i]: (v1_relat_1 @ (k6_relat_1 @ X27))),
% 0.45/0.70      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.45/0.70  thf('43', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i]:
% 0.45/0.70         ((k3_xboole_0 @ X1 @ X0) = (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 0.45/0.70      inference('demod', [status(thm)], ['35', '40', '41', '42'])).
% 0.45/0.70  thf(commutativity_k2_tarski, axiom,
% 0.45/0.70    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.45/0.70  thf('44', plain,
% 0.45/0.70      (![X12 : $i, X13 : $i]:
% 0.45/0.70         ((k2_tarski @ X13 @ X12) = (k2_tarski @ X12 @ X13))),
% 0.45/0.70      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.45/0.70  thf(t12_setfam_1, axiom,
% 0.45/0.70    (![A:$i,B:$i]:
% 0.45/0.70     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.45/0.70  thf('45', plain,
% 0.45/0.70      (![X16 : $i, X17 : $i]:
% 0.45/0.70         ((k1_setfam_1 @ (k2_tarski @ X16 @ X17)) = (k3_xboole_0 @ X16 @ X17))),
% 0.45/0.70      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.45/0.70  thf('46', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i]:
% 0.45/0.70         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.45/0.70      inference('sup+', [status(thm)], ['44', '45'])).
% 0.45/0.70  thf('47', plain,
% 0.45/0.70      (![X16 : $i, X17 : $i]:
% 0.45/0.70         ((k1_setfam_1 @ (k2_tarski @ X16 @ X17)) = (k3_xboole_0 @ X16 @ X17))),
% 0.45/0.70      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.45/0.70  thf('48', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.45/0.70      inference('sup+', [status(thm)], ['46', '47'])).
% 0.45/0.70  thf(t48_xboole_1, axiom,
% 0.45/0.70    (![A:$i,B:$i]:
% 0.45/0.70     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.45/0.70  thf('49', plain,
% 0.45/0.70      (![X10 : $i, X11 : $i]:
% 0.45/0.70         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 0.45/0.70           = (k3_xboole_0 @ X10 @ X11))),
% 0.45/0.70      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.45/0.70  thf(t36_xboole_1, axiom,
% 0.45/0.70    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.45/0.70  thf('50', plain,
% 0.45/0.70      (![X8 : $i, X9 : $i]: (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X8)),
% 0.45/0.70      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.45/0.70  thf('51', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.45/0.70      inference('sup+', [status(thm)], ['49', '50'])).
% 0.45/0.70  thf('52', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.45/0.70      inference('sup+', [status(thm)], ['48', '51'])).
% 0.45/0.70  thf('53', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i]:
% 0.45/0.70         ((k3_xboole_0 @ X1 @ X0) = (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 0.45/0.70      inference('demod', [status(thm)], ['35', '40', '41', '42'])).
% 0.45/0.70  thf('54', plain,
% 0.45/0.70      (((k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C))
% 0.45/0.70         = (k10_relat_1 @ sk_A @ sk_C))),
% 0.45/0.70      inference('demod', [status(thm)], ['28', '43', '52', '53'])).
% 0.45/0.70  thf('55', plain,
% 0.45/0.70      ((((k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C)
% 0.45/0.70          = (k10_relat_1 @ sk_A @ sk_C))
% 0.45/0.70        | ~ (v1_relat_1 @ sk_A))),
% 0.45/0.70      inference('sup+', [status(thm)], ['0', '54'])).
% 0.45/0.70  thf('56', plain, ((v1_relat_1 @ sk_A)),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('57', plain,
% 0.45/0.70      (((k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C)
% 0.45/0.70         = (k10_relat_1 @ sk_A @ sk_C))),
% 0.45/0.70      inference('demod', [status(thm)], ['55', '56'])).
% 0.45/0.70  thf('58', plain,
% 0.45/0.70      (((k10_relat_1 @ sk_A @ sk_C)
% 0.45/0.70         != (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C))),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('59', plain, ($false),
% 0.45/0.70      inference('simplify_reflect-', [status(thm)], ['57', '58'])).
% 0.45/0.70  
% 0.45/0.70  % SZS output end Refutation
% 0.45/0.70  
% 0.45/0.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
