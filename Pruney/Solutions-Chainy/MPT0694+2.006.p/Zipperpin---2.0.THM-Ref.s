%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NgRnLo1RhK

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:33 EST 2020

% Result     : Theorem 2.65s
% Output     : Refutation 2.65s
% Verified   : 
% Statistics : Number of formulae       :   75 (  97 expanded)
%              Number of leaves         :   24 (  39 expanded)
%              Depth                    :   15
%              Number of atoms          :  729 ( 978 expanded)
%              Number of equality atoms :   20 (  36 expanded)
%              Maximal formula depth    :   17 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('0',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_tarski @ X9 @ X8 )
      = ( k2_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf(fc8_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) )
        & ( v1_funct_1 @ ( k7_relat_1 @ A @ B ) ) ) ) )).

thf('2',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 )
      | ( v1_funct_1 @ ( k7_relat_1 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[fc8_funct_1])).

thf(t139_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('3',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X25 @ X24 ) @ X26 )
        = ( k3_xboole_0 @ X24 @ ( k10_relat_1 @ X25 @ X26 ) ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('5',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X25 @ X24 ) @ X26 )
        = ( k1_setfam_1 @ ( k2_tarski @ X24 @ ( k10_relat_1 @ X25 @ X26 ) ) ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('7',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['5','8'])).

thf(t162_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( r1_tarski @ B @ C )
         => ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B )
            = ( k9_relat_1 @ A @ B ) ) ) ) )).

thf('10',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ X19 @ X20 )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X21 @ X20 ) @ X19 )
        = ( k9_relat_1 @ X21 @ X19 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t162_relat_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X3 )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X3 @ X0 ) @ ( k10_relat_1 @ ( k7_relat_1 @ X2 @ X0 ) @ X1 ) )
        = ( k9_relat_1 @ X3 @ ( k10_relat_1 @ ( k7_relat_1 @ X2 @ X0 ) @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t145_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ) )).

thf('12',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X27 @ ( k10_relat_1 @ X27 @ X28 ) ) @ X28 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t145_funct_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X2 @ ( k10_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ ( k7_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k9_relat_1 @ X2 @ ( k10_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) ) @ X2 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['1','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) ) @ X2 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X25 @ X24 ) @ X26 )
        = ( k1_setfam_1 @ ( k2_tarski @ X24 @ ( k10_relat_1 @ X25 @ X26 ) ) ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t154_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( r1_tarski @ ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf('20',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X16 @ ( k3_xboole_0 @ X17 @ X18 ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ X16 @ X17 ) @ ( k9_relat_1 @ X16 @ X18 ) ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t154_relat_1])).

thf('21',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('22',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('23',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X16 @ ( k1_setfam_1 @ ( k2_tarski @ X17 @ X18 ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k9_relat_1 @ X16 @ X17 ) @ ( k9_relat_1 @ X16 @ X18 ) ) ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf(t18_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf('24',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X2 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t18_xboole_1])).

thf('25',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('26',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X3 @ X4 ) ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X2 @ X0 ) ) ) @ ( k9_relat_1 @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X3 @ ( k10_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) ) @ ( k9_relat_1 @ X3 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference('sup+',[status(thm)],['19','27'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('29',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X5 @ X7 )
      | ( r1_tarski @ X5 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('30',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('31',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X5 @ X7 )
      | ( r1_tarski @ X5 @ ( k1_setfam_1 @ ( k2_tarski @ X6 @ X7 ) ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X3 )
      | ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k10_relat_1 @ ( k7_relat_1 @ X3 @ X0 ) @ X2 ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ X4 ) ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k10_relat_1 @ ( k7_relat_1 @ X3 @ X0 ) @ X2 ) ) @ X4 ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ( r1_tarski @ ( k9_relat_1 @ X2 @ ( k10_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k9_relat_1 @ X2 @ X1 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['18','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X2 @ ( k10_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k9_relat_1 @ X2 @ X1 ) @ X0 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) ) @ ( k1_setfam_1 @ ( k2_tarski @ X2 @ ( k9_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','34'])).

thf('36',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X25 @ X24 ) @ X26 )
        = ( k1_setfam_1 @ ( k2_tarski @ X24 @ ( k10_relat_1 @ X25 @ X26 ) ) ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t149_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( r1_tarski @ ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( r1_tarski @ ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t149_funct_1])).

thf('37',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_C @ ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_C @ sk_B ) ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ sk_C @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('39',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('40',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_C @ ( k1_setfam_1 @ ( k2_tarski @ sk_A @ ( k10_relat_1 @ sk_C @ sk_B ) ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k9_relat_1 @ sk_C @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_tarski @ X9 @ X8 )
      = ( k2_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('42',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_C @ ( k1_setfam_1 @ ( k2_tarski @ sk_A @ ( k10_relat_1 @ sk_C @ sk_B ) ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( k9_relat_1 @ sk_C @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ sk_B ) ) @ ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( k9_relat_1 @ sk_C @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['36','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ sk_B ) ) @ ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( k9_relat_1 @ sk_C @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['35','45'])).

thf('47',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    $false ),
    inference(demod,[status(thm)],['46','47','48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NgRnLo1RhK
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:36:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 2.65/2.83  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.65/2.83  % Solved by: fo/fo7.sh
% 2.65/2.83  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.65/2.83  % done 2124 iterations in 2.378s
% 2.65/2.83  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.65/2.83  % SZS output start Refutation
% 2.65/2.83  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 2.65/2.83  thf(sk_A_type, type, sk_A: $i).
% 2.65/2.83  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.65/2.83  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 2.65/2.83  thf(sk_C_type, type, sk_C: $i).
% 2.65/2.83  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.65/2.83  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 2.65/2.83  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 2.65/2.83  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.65/2.83  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 2.65/2.83  thf(sk_B_type, type, sk_B: $i).
% 2.65/2.83  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.65/2.83  thf(commutativity_k2_tarski, axiom,
% 2.65/2.83    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 2.65/2.83  thf('0', plain,
% 2.65/2.83      (![X8 : $i, X9 : $i]: ((k2_tarski @ X9 @ X8) = (k2_tarski @ X8 @ X9))),
% 2.65/2.83      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 2.65/2.83  thf(dt_k7_relat_1, axiom,
% 2.65/2.83    (![A:$i,B:$i]:
% 2.65/2.83     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 2.65/2.83  thf('1', plain,
% 2.65/2.83      (![X14 : $i, X15 : $i]:
% 2.65/2.83         (~ (v1_relat_1 @ X14) | (v1_relat_1 @ (k7_relat_1 @ X14 @ X15)))),
% 2.65/2.83      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 2.65/2.83  thf(fc8_funct_1, axiom,
% 2.65/2.83    (![A:$i,B:$i]:
% 2.65/2.83     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.65/2.83       ( ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) & 
% 2.65/2.83         ( v1_funct_1 @ ( k7_relat_1 @ A @ B ) ) ) ))).
% 2.65/2.83  thf('2', plain,
% 2.65/2.83      (![X22 : $i, X23 : $i]:
% 2.65/2.83         (~ (v1_funct_1 @ X22)
% 2.65/2.83          | ~ (v1_relat_1 @ X22)
% 2.65/2.83          | (v1_funct_1 @ (k7_relat_1 @ X22 @ X23)))),
% 2.65/2.83      inference('cnf', [status(esa)], [fc8_funct_1])).
% 2.65/2.83  thf(t139_funct_1, axiom,
% 2.65/2.83    (![A:$i,B:$i,C:$i]:
% 2.65/2.83     ( ( v1_relat_1 @ C ) =>
% 2.65/2.83       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 2.65/2.83         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 2.65/2.83  thf('3', plain,
% 2.65/2.83      (![X24 : $i, X25 : $i, X26 : $i]:
% 2.65/2.83         (((k10_relat_1 @ (k7_relat_1 @ X25 @ X24) @ X26)
% 2.65/2.83            = (k3_xboole_0 @ X24 @ (k10_relat_1 @ X25 @ X26)))
% 2.65/2.83          | ~ (v1_relat_1 @ X25))),
% 2.65/2.83      inference('cnf', [status(esa)], [t139_funct_1])).
% 2.65/2.83  thf(t12_setfam_1, axiom,
% 2.65/2.83    (![A:$i,B:$i]:
% 2.65/2.83     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 2.65/2.83  thf('4', plain,
% 2.65/2.83      (![X12 : $i, X13 : $i]:
% 2.65/2.83         ((k1_setfam_1 @ (k2_tarski @ X12 @ X13)) = (k3_xboole_0 @ X12 @ X13))),
% 2.65/2.83      inference('cnf', [status(esa)], [t12_setfam_1])).
% 2.65/2.83  thf('5', plain,
% 2.65/2.83      (![X24 : $i, X25 : $i, X26 : $i]:
% 2.65/2.83         (((k10_relat_1 @ (k7_relat_1 @ X25 @ X24) @ X26)
% 2.65/2.83            = (k1_setfam_1 @ (k2_tarski @ X24 @ (k10_relat_1 @ X25 @ X26))))
% 2.65/2.83          | ~ (v1_relat_1 @ X25))),
% 2.65/2.83      inference('demod', [status(thm)], ['3', '4'])).
% 2.65/2.83  thf(t17_xboole_1, axiom,
% 2.65/2.83    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 2.65/2.83  thf('6', plain,
% 2.65/2.83      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 2.65/2.83      inference('cnf', [status(esa)], [t17_xboole_1])).
% 2.65/2.83  thf('7', plain,
% 2.65/2.83      (![X12 : $i, X13 : $i]:
% 2.65/2.83         ((k1_setfam_1 @ (k2_tarski @ X12 @ X13)) = (k3_xboole_0 @ X12 @ X13))),
% 2.65/2.83      inference('cnf', [status(esa)], [t12_setfam_1])).
% 2.65/2.83  thf('8', plain,
% 2.65/2.83      (![X0 : $i, X1 : $i]:
% 2.65/2.83         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)) @ X0)),
% 2.65/2.83      inference('demod', [status(thm)], ['6', '7'])).
% 2.65/2.83  thf('9', plain,
% 2.65/2.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.65/2.83         ((r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0) @ X1)
% 2.65/2.83          | ~ (v1_relat_1 @ X2))),
% 2.65/2.83      inference('sup+', [status(thm)], ['5', '8'])).
% 2.65/2.83  thf(t162_relat_1, axiom,
% 2.65/2.83    (![A:$i]:
% 2.65/2.83     ( ( v1_relat_1 @ A ) =>
% 2.65/2.83       ( ![B:$i,C:$i]:
% 2.65/2.83         ( ( r1_tarski @ B @ C ) =>
% 2.65/2.83           ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B ) =
% 2.65/2.83             ( k9_relat_1 @ A @ B ) ) ) ) ))).
% 2.65/2.83  thf('10', plain,
% 2.65/2.83      (![X19 : $i, X20 : $i, X21 : $i]:
% 2.65/2.83         (~ (r1_tarski @ X19 @ X20)
% 2.65/2.83          | ((k9_relat_1 @ (k7_relat_1 @ X21 @ X20) @ X19)
% 2.65/2.83              = (k9_relat_1 @ X21 @ X19))
% 2.65/2.83          | ~ (v1_relat_1 @ X21))),
% 2.65/2.83      inference('cnf', [status(esa)], [t162_relat_1])).
% 2.65/2.83  thf('11', plain,
% 2.65/2.83      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.65/2.83         (~ (v1_relat_1 @ X2)
% 2.65/2.83          | ~ (v1_relat_1 @ X3)
% 2.65/2.83          | ((k9_relat_1 @ (k7_relat_1 @ X3 @ X0) @ 
% 2.65/2.83              (k10_relat_1 @ (k7_relat_1 @ X2 @ X0) @ X1))
% 2.65/2.83              = (k9_relat_1 @ X3 @ (k10_relat_1 @ (k7_relat_1 @ X2 @ X0) @ X1))))),
% 2.65/2.83      inference('sup-', [status(thm)], ['9', '10'])).
% 2.65/2.83  thf(t145_funct_1, axiom,
% 2.65/2.83    (![A:$i,B:$i]:
% 2.65/2.83     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.65/2.83       ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ))).
% 2.65/2.83  thf('12', plain,
% 2.65/2.83      (![X27 : $i, X28 : $i]:
% 2.65/2.83         ((r1_tarski @ (k9_relat_1 @ X27 @ (k10_relat_1 @ X27 @ X28)) @ X28)
% 2.65/2.83          | ~ (v1_funct_1 @ X27)
% 2.65/2.83          | ~ (v1_relat_1 @ X27))),
% 2.65/2.83      inference('cnf', [status(esa)], [t145_funct_1])).
% 2.65/2.83  thf('13', plain,
% 2.65/2.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.65/2.83         ((r1_tarski @ 
% 2.65/2.83           (k9_relat_1 @ X2 @ (k10_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0)) @ X0)
% 2.65/2.83          | ~ (v1_relat_1 @ X2)
% 2.65/2.83          | ~ (v1_relat_1 @ X2)
% 2.65/2.83          | ~ (v1_relat_1 @ (k7_relat_1 @ X2 @ X1))
% 2.65/2.83          | ~ (v1_funct_1 @ (k7_relat_1 @ X2 @ X1)))),
% 2.65/2.83      inference('sup+', [status(thm)], ['11', '12'])).
% 2.65/2.83  thf('14', plain,
% 2.65/2.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.65/2.83         (~ (v1_funct_1 @ (k7_relat_1 @ X2 @ X1))
% 2.65/2.83          | ~ (v1_relat_1 @ (k7_relat_1 @ X2 @ X1))
% 2.65/2.83          | ~ (v1_relat_1 @ X2)
% 2.65/2.83          | (r1_tarski @ 
% 2.65/2.83             (k9_relat_1 @ X2 @ (k10_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0)) @ 
% 2.65/2.83             X0))),
% 2.65/2.83      inference('simplify', [status(thm)], ['13'])).
% 2.65/2.83  thf('15', plain,
% 2.65/2.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.65/2.83         (~ (v1_relat_1 @ X1)
% 2.65/2.83          | ~ (v1_funct_1 @ X1)
% 2.65/2.83          | (r1_tarski @ 
% 2.65/2.83             (k9_relat_1 @ X1 @ (k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)) @ 
% 2.65/2.83             X2)
% 2.65/2.83          | ~ (v1_relat_1 @ X1)
% 2.65/2.83          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 2.65/2.83      inference('sup-', [status(thm)], ['2', '14'])).
% 2.65/2.83  thf('16', plain,
% 2.65/2.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.65/2.83         (~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 2.65/2.83          | (r1_tarski @ 
% 2.65/2.83             (k9_relat_1 @ X1 @ (k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)) @ 
% 2.65/2.83             X2)
% 2.65/2.83          | ~ (v1_funct_1 @ X1)
% 2.65/2.83          | ~ (v1_relat_1 @ X1))),
% 2.65/2.83      inference('simplify', [status(thm)], ['15'])).
% 2.65/2.83  thf('17', plain,
% 2.65/2.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.65/2.83         (~ (v1_relat_1 @ X1)
% 2.65/2.83          | ~ (v1_relat_1 @ X1)
% 2.65/2.83          | ~ (v1_funct_1 @ X1)
% 2.65/2.83          | (r1_tarski @ 
% 2.65/2.83             (k9_relat_1 @ X1 @ (k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)) @ 
% 2.65/2.83             X2))),
% 2.65/2.83      inference('sup-', [status(thm)], ['1', '16'])).
% 2.65/2.83  thf('18', plain,
% 2.65/2.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.65/2.83         ((r1_tarski @ 
% 2.65/2.83           (k9_relat_1 @ X1 @ (k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)) @ X2)
% 2.65/2.83          | ~ (v1_funct_1 @ X1)
% 2.65/2.83          | ~ (v1_relat_1 @ X1))),
% 2.65/2.83      inference('simplify', [status(thm)], ['17'])).
% 2.65/2.83  thf('19', plain,
% 2.65/2.83      (![X24 : $i, X25 : $i, X26 : $i]:
% 2.65/2.83         (((k10_relat_1 @ (k7_relat_1 @ X25 @ X24) @ X26)
% 2.65/2.83            = (k1_setfam_1 @ (k2_tarski @ X24 @ (k10_relat_1 @ X25 @ X26))))
% 2.65/2.83          | ~ (v1_relat_1 @ X25))),
% 2.65/2.83      inference('demod', [status(thm)], ['3', '4'])).
% 2.65/2.83  thf(t154_relat_1, axiom,
% 2.65/2.83    (![A:$i,B:$i,C:$i]:
% 2.65/2.83     ( ( v1_relat_1 @ C ) =>
% 2.65/2.83       ( r1_tarski @
% 2.65/2.83         ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) @ 
% 2.65/2.83         ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 2.65/2.83  thf('20', plain,
% 2.65/2.83      (![X16 : $i, X17 : $i, X18 : $i]:
% 2.65/2.83         ((r1_tarski @ (k9_relat_1 @ X16 @ (k3_xboole_0 @ X17 @ X18)) @ 
% 2.65/2.83           (k3_xboole_0 @ (k9_relat_1 @ X16 @ X17) @ (k9_relat_1 @ X16 @ X18)))
% 2.65/2.83          | ~ (v1_relat_1 @ X16))),
% 2.65/2.83      inference('cnf', [status(esa)], [t154_relat_1])).
% 2.65/2.83  thf('21', plain,
% 2.65/2.83      (![X12 : $i, X13 : $i]:
% 2.65/2.83         ((k1_setfam_1 @ (k2_tarski @ X12 @ X13)) = (k3_xboole_0 @ X12 @ X13))),
% 2.65/2.83      inference('cnf', [status(esa)], [t12_setfam_1])).
% 2.65/2.83  thf('22', plain,
% 2.65/2.83      (![X12 : $i, X13 : $i]:
% 2.65/2.83         ((k1_setfam_1 @ (k2_tarski @ X12 @ X13)) = (k3_xboole_0 @ X12 @ X13))),
% 2.65/2.83      inference('cnf', [status(esa)], [t12_setfam_1])).
% 2.65/2.83  thf('23', plain,
% 2.65/2.83      (![X16 : $i, X17 : $i, X18 : $i]:
% 2.65/2.83         ((r1_tarski @ 
% 2.65/2.83           (k9_relat_1 @ X16 @ (k1_setfam_1 @ (k2_tarski @ X17 @ X18))) @ 
% 2.65/2.83           (k1_setfam_1 @ 
% 2.65/2.83            (k2_tarski @ (k9_relat_1 @ X16 @ X17) @ (k9_relat_1 @ X16 @ X18))))
% 2.65/2.83          | ~ (v1_relat_1 @ X16))),
% 2.65/2.83      inference('demod', [status(thm)], ['20', '21', '22'])).
% 2.65/2.83  thf(t18_xboole_1, axiom,
% 2.65/2.83    (![A:$i,B:$i,C:$i]:
% 2.65/2.83     ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) => ( r1_tarski @ A @ B ) ))).
% 2.65/2.83  thf('24', plain,
% 2.65/2.83      (![X2 : $i, X3 : $i, X4 : $i]:
% 2.65/2.83         ((r1_tarski @ X2 @ X3) | ~ (r1_tarski @ X2 @ (k3_xboole_0 @ X3 @ X4)))),
% 2.65/2.83      inference('cnf', [status(esa)], [t18_xboole_1])).
% 2.65/2.83  thf('25', plain,
% 2.65/2.83      (![X12 : $i, X13 : $i]:
% 2.65/2.83         ((k1_setfam_1 @ (k2_tarski @ X12 @ X13)) = (k3_xboole_0 @ X12 @ X13))),
% 2.65/2.83      inference('cnf', [status(esa)], [t12_setfam_1])).
% 2.65/2.83  thf('26', plain,
% 2.65/2.83      (![X2 : $i, X3 : $i, X4 : $i]:
% 2.65/2.83         ((r1_tarski @ X2 @ X3)
% 2.65/2.83          | ~ (r1_tarski @ X2 @ (k1_setfam_1 @ (k2_tarski @ X3 @ X4))))),
% 2.65/2.83      inference('demod', [status(thm)], ['24', '25'])).
% 2.65/2.83  thf('27', plain,
% 2.65/2.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.65/2.83         (~ (v1_relat_1 @ X1)
% 2.65/2.83          | (r1_tarski @ 
% 2.65/2.83             (k9_relat_1 @ X1 @ (k1_setfam_1 @ (k2_tarski @ X2 @ X0))) @ 
% 2.65/2.83             (k9_relat_1 @ X1 @ X2)))),
% 2.65/2.83      inference('sup-', [status(thm)], ['23', '26'])).
% 2.65/2.83  thf('28', plain,
% 2.65/2.83      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.65/2.83         ((r1_tarski @ 
% 2.65/2.83           (k9_relat_1 @ X3 @ (k10_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0)) @ 
% 2.65/2.83           (k9_relat_1 @ X3 @ X1))
% 2.65/2.83          | ~ (v1_relat_1 @ X2)
% 2.65/2.83          | ~ (v1_relat_1 @ X3))),
% 2.65/2.83      inference('sup+', [status(thm)], ['19', '27'])).
% 2.65/2.83  thf(t19_xboole_1, axiom,
% 2.65/2.83    (![A:$i,B:$i,C:$i]:
% 2.65/2.83     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 2.65/2.83       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 2.65/2.83  thf('29', plain,
% 2.65/2.83      (![X5 : $i, X6 : $i, X7 : $i]:
% 2.65/2.83         (~ (r1_tarski @ X5 @ X6)
% 2.65/2.83          | ~ (r1_tarski @ X5 @ X7)
% 2.65/2.83          | (r1_tarski @ X5 @ (k3_xboole_0 @ X6 @ X7)))),
% 2.65/2.83      inference('cnf', [status(esa)], [t19_xboole_1])).
% 2.65/2.83  thf('30', plain,
% 2.65/2.83      (![X12 : $i, X13 : $i]:
% 2.65/2.83         ((k1_setfam_1 @ (k2_tarski @ X12 @ X13)) = (k3_xboole_0 @ X12 @ X13))),
% 2.65/2.83      inference('cnf', [status(esa)], [t12_setfam_1])).
% 2.65/2.83  thf('31', plain,
% 2.65/2.83      (![X5 : $i, X6 : $i, X7 : $i]:
% 2.65/2.83         (~ (r1_tarski @ X5 @ X6)
% 2.65/2.83          | ~ (r1_tarski @ X5 @ X7)
% 2.65/2.83          | (r1_tarski @ X5 @ (k1_setfam_1 @ (k2_tarski @ X6 @ X7))))),
% 2.65/2.83      inference('demod', [status(thm)], ['29', '30'])).
% 2.65/2.83  thf('32', plain,
% 2.65/2.83      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 2.65/2.83         (~ (v1_relat_1 @ X1)
% 2.65/2.83          | ~ (v1_relat_1 @ X3)
% 2.65/2.83          | (r1_tarski @ 
% 2.65/2.83             (k9_relat_1 @ X1 @ (k10_relat_1 @ (k7_relat_1 @ X3 @ X0) @ X2)) @ 
% 2.65/2.83             (k1_setfam_1 @ (k2_tarski @ (k9_relat_1 @ X1 @ X0) @ X4)))
% 2.65/2.83          | ~ (r1_tarski @ 
% 2.65/2.83               (k9_relat_1 @ X1 @ (k10_relat_1 @ (k7_relat_1 @ X3 @ X0) @ X2)) @ 
% 2.65/2.83               X4))),
% 2.65/2.83      inference('sup-', [status(thm)], ['28', '31'])).
% 2.65/2.83  thf('33', plain,
% 2.65/2.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.65/2.83         (~ (v1_relat_1 @ X2)
% 2.65/2.83          | ~ (v1_funct_1 @ X2)
% 2.65/2.83          | (r1_tarski @ 
% 2.65/2.83             (k9_relat_1 @ X2 @ (k10_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0)) @ 
% 2.65/2.83             (k1_setfam_1 @ (k2_tarski @ (k9_relat_1 @ X2 @ X1) @ X0)))
% 2.65/2.83          | ~ (v1_relat_1 @ X2)
% 2.65/2.83          | ~ (v1_relat_1 @ X2))),
% 2.65/2.83      inference('sup-', [status(thm)], ['18', '32'])).
% 2.65/2.83  thf('34', plain,
% 2.65/2.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.65/2.83         ((r1_tarski @ 
% 2.65/2.83           (k9_relat_1 @ X2 @ (k10_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0)) @ 
% 2.65/2.83           (k1_setfam_1 @ (k2_tarski @ (k9_relat_1 @ X2 @ X1) @ X0)))
% 2.65/2.83          | ~ (v1_funct_1 @ X2)
% 2.65/2.83          | ~ (v1_relat_1 @ X2))),
% 2.65/2.83      inference('simplify', [status(thm)], ['33'])).
% 2.65/2.83  thf('35', plain,
% 2.65/2.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.65/2.83         ((r1_tarski @ 
% 2.65/2.83           (k9_relat_1 @ X1 @ (k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)) @ 
% 2.65/2.83           (k1_setfam_1 @ (k2_tarski @ X2 @ (k9_relat_1 @ X1 @ X0))))
% 2.65/2.83          | ~ (v1_relat_1 @ X1)
% 2.65/2.83          | ~ (v1_funct_1 @ X1))),
% 2.65/2.83      inference('sup+', [status(thm)], ['0', '34'])).
% 2.65/2.83  thf('36', plain,
% 2.65/2.83      (![X24 : $i, X25 : $i, X26 : $i]:
% 2.65/2.83         (((k10_relat_1 @ (k7_relat_1 @ X25 @ X24) @ X26)
% 2.65/2.83            = (k1_setfam_1 @ (k2_tarski @ X24 @ (k10_relat_1 @ X25 @ X26))))
% 2.65/2.83          | ~ (v1_relat_1 @ X25))),
% 2.65/2.83      inference('demod', [status(thm)], ['3', '4'])).
% 2.65/2.83  thf(t149_funct_1, conjecture,
% 2.65/2.83    (![A:$i,B:$i,C:$i]:
% 2.65/2.83     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 2.65/2.83       ( r1_tarski @
% 2.65/2.83         ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) @ 
% 2.65/2.83         ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ B ) ) ))).
% 2.65/2.83  thf(zf_stmt_0, negated_conjecture,
% 2.65/2.83    (~( ![A:$i,B:$i,C:$i]:
% 2.65/2.83        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 2.65/2.83          ( r1_tarski @
% 2.65/2.83            ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) @ 
% 2.65/2.83            ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ B ) ) ) )),
% 2.65/2.83    inference('cnf.neg', [status(esa)], [t149_funct_1])).
% 2.65/2.83  thf('37', plain,
% 2.65/2.83      (~ (r1_tarski @ 
% 2.65/2.83          (k9_relat_1 @ sk_C @ 
% 2.65/2.83           (k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_C @ sk_B))) @ 
% 2.65/2.83          (k3_xboole_0 @ (k9_relat_1 @ sk_C @ sk_A) @ sk_B))),
% 2.65/2.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.65/2.83  thf('38', plain,
% 2.65/2.83      (![X12 : $i, X13 : $i]:
% 2.65/2.83         ((k1_setfam_1 @ (k2_tarski @ X12 @ X13)) = (k3_xboole_0 @ X12 @ X13))),
% 2.65/2.83      inference('cnf', [status(esa)], [t12_setfam_1])).
% 2.65/2.83  thf('39', plain,
% 2.65/2.83      (![X12 : $i, X13 : $i]:
% 2.65/2.83         ((k1_setfam_1 @ (k2_tarski @ X12 @ X13)) = (k3_xboole_0 @ X12 @ X13))),
% 2.65/2.83      inference('cnf', [status(esa)], [t12_setfam_1])).
% 2.65/2.83  thf('40', plain,
% 2.65/2.83      (~ (r1_tarski @ 
% 2.65/2.83          (k9_relat_1 @ sk_C @ 
% 2.65/2.83           (k1_setfam_1 @ (k2_tarski @ sk_A @ (k10_relat_1 @ sk_C @ sk_B)))) @ 
% 2.65/2.83          (k1_setfam_1 @ (k2_tarski @ (k9_relat_1 @ sk_C @ sk_A) @ sk_B)))),
% 2.65/2.83      inference('demod', [status(thm)], ['37', '38', '39'])).
% 2.65/2.83  thf('41', plain,
% 2.65/2.83      (![X8 : $i, X9 : $i]: ((k2_tarski @ X9 @ X8) = (k2_tarski @ X8 @ X9))),
% 2.65/2.83      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 2.65/2.83  thf('42', plain,
% 2.65/2.83      (~ (r1_tarski @ 
% 2.65/2.83          (k9_relat_1 @ sk_C @ 
% 2.65/2.83           (k1_setfam_1 @ (k2_tarski @ sk_A @ (k10_relat_1 @ sk_C @ sk_B)))) @ 
% 2.65/2.83          (k1_setfam_1 @ (k2_tarski @ sk_B @ (k9_relat_1 @ sk_C @ sk_A))))),
% 2.65/2.83      inference('demod', [status(thm)], ['40', '41'])).
% 2.65/2.83  thf('43', plain,
% 2.65/2.83      ((~ (r1_tarski @ 
% 2.65/2.83           (k9_relat_1 @ sk_C @ 
% 2.65/2.83            (k10_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ sk_B)) @ 
% 2.65/2.83           (k1_setfam_1 @ (k2_tarski @ sk_B @ (k9_relat_1 @ sk_C @ sk_A))))
% 2.65/2.83        | ~ (v1_relat_1 @ sk_C))),
% 2.65/2.83      inference('sup-', [status(thm)], ['36', '42'])).
% 2.65/2.83  thf('44', plain, ((v1_relat_1 @ sk_C)),
% 2.65/2.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.65/2.83  thf('45', plain,
% 2.65/2.83      (~ (r1_tarski @ 
% 2.65/2.83          (k9_relat_1 @ sk_C @ 
% 2.65/2.83           (k10_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ sk_B)) @ 
% 2.65/2.83          (k1_setfam_1 @ (k2_tarski @ sk_B @ (k9_relat_1 @ sk_C @ sk_A))))),
% 2.65/2.83      inference('demod', [status(thm)], ['43', '44'])).
% 2.65/2.83  thf('46', plain, ((~ (v1_funct_1 @ sk_C) | ~ (v1_relat_1 @ sk_C))),
% 2.65/2.83      inference('sup-', [status(thm)], ['35', '45'])).
% 2.65/2.83  thf('47', plain, ((v1_funct_1 @ sk_C)),
% 2.65/2.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.65/2.83  thf('48', plain, ((v1_relat_1 @ sk_C)),
% 2.65/2.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.65/2.83  thf('49', plain, ($false),
% 2.65/2.83      inference('demod', [status(thm)], ['46', '47', '48'])).
% 2.65/2.83  
% 2.65/2.83  % SZS output end Refutation
% 2.65/2.83  
% 2.65/2.84  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
