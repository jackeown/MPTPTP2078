%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.V86yLLYPVs

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:23 EST 2020

% Result     : Theorem 5.13s
% Output     : Refutation 5.13s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 103 expanded)
%              Number of leaves         :   19 (  39 expanded)
%              Depth                    :   16
%              Number of atoms          :  749 (1009 expanded)
%              Number of equality atoms :   52 (  77 expanded)
%              Maximal formula depth    :   13 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_wellord1_type,type,(
    k2_wellord1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t127_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k8_relat_1 @ A @ ( k8_relat_1 @ B @ C ) )
        = ( k8_relat_1 @ ( k3_xboole_0 @ A @ B ) @ C ) ) ) )).

thf('5',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k8_relat_1 @ X25 @ ( k8_relat_1 @ X26 @ X27 ) )
        = ( k8_relat_1 @ ( k3_xboole_0 @ X25 @ X26 ) @ X27 ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t127_relat_1])).

thf(t17_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_wellord1 @ B @ A )
        = ( k7_relat_1 @ ( k8_relat_1 @ A @ B ) @ A ) ) ) )).

thf('6',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k2_wellord1 @ X32 @ X31 )
        = ( k7_relat_1 @ ( k8_relat_1 @ X31 @ X32 ) @ X31 ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t17_wellord1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_wellord1 @ ( k8_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k7_relat_1 @ ( k8_relat_1 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) @ X2 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(dt_k8_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X20: $i,X21: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X20 @ X21 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relat_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_wellord1 @ ( k8_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k7_relat_1 @ ( k8_relat_1 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) @ X2 ) ) ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_wellord1 @ ( k8_relat_1 @ X1 @ X2 ) @ X0 )
        = ( k7_relat_1 @ ( k8_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['4','9'])).

thf(t140_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ ( k8_relat_1 @ A @ C ) @ B )
        = ( k8_relat_1 @ A @ ( k7_relat_1 @ C @ B ) ) ) ) )).

thf('11',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k7_relat_1 @ ( k8_relat_1 @ X28 @ X29 ) @ X30 )
        = ( k8_relat_1 @ X28 @ ( k7_relat_1 @ X29 @ X30 ) ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t140_relat_1])).

thf('12',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k2_wellord1 @ X32 @ X31 )
        = ( k7_relat_1 @ ( k8_relat_1 @ X31 @ X32 ) @ X31 ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t17_wellord1])).

thf('13',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k7_relat_1 @ ( k8_relat_1 @ X28 @ X29 ) @ X30 )
        = ( k8_relat_1 @ X28 @ ( k7_relat_1 @ X29 @ X30 ) ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t140_relat_1])).

thf('14',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k8_relat_1 @ X25 @ ( k8_relat_1 @ X26 @ X27 ) )
        = ( k8_relat_1 @ ( k3_xboole_0 @ X25 @ X26 ) @ X27 ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t127_relat_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k8_relat_1 @ X3 @ ( k7_relat_1 @ ( k8_relat_1 @ X2 @ X1 ) @ X0 ) )
        = ( k8_relat_1 @ ( k3_xboole_0 @ X3 @ X2 ) @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('16',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k8_relat_1 @ X3 @ ( k7_relat_1 @ ( k8_relat_1 @ X2 @ X1 ) @ X0 ) )
        = ( k8_relat_1 @ ( k3_xboole_0 @ X3 @ X2 ) @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k8_relat_1 @ X2 @ ( k2_wellord1 @ X1 @ X0 ) )
        = ( k8_relat_1 @ ( k3_xboole_0 @ X2 @ X0 ) @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['12','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k8_relat_1 @ X2 @ ( k2_wellord1 @ X1 @ X0 ) )
        = ( k8_relat_1 @ ( k3_xboole_0 @ X2 @ X0 ) @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k8_relat_1 @ X2 @ ( k2_wellord1 @ X1 @ X0 ) )
        = ( k7_relat_1 @ ( k8_relat_1 @ ( k3_xboole_0 @ X2 @ X0 ) @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k8_relat_1 @ X2 @ ( k2_wellord1 @ X1 @ X0 ) )
        = ( k7_relat_1 @ ( k8_relat_1 @ ( k3_xboole_0 @ X2 @ X0 ) @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k8_relat_1 @ X2 @ ( k2_wellord1 @ X1 @ X0 ) )
        = ( k2_wellord1 @ ( k8_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['10','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k8_relat_1 @ X2 @ ( k2_wellord1 @ X1 @ X0 ) )
        = ( k2_wellord1 @ ( k8_relat_1 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k2_wellord1 @ X32 @ X31 )
        = ( k7_relat_1 @ ( k8_relat_1 @ X31 @ X32 ) @ X31 ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t17_wellord1])).

thf('25',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k8_relat_1 @ X25 @ ( k8_relat_1 @ X26 @ X27 ) )
        = ( k8_relat_1 @ ( k3_xboole_0 @ X25 @ X26 ) @ X27 ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t127_relat_1])).

thf('26',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k2_wellord1 @ X32 @ X31 )
        = ( k7_relat_1 @ ( k8_relat_1 @ X31 @ X32 ) @ X31 ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t17_wellord1])).

thf(t100_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('27',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X22 @ X23 ) @ X24 )
        = ( k7_relat_1 @ X22 @ ( k3_xboole_0 @ X23 @ X24 ) ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) @ X2 )
        = ( k7_relat_1 @ ( k8_relat_1 @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X20: $i,X21: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X20 @ X21 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relat_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k7_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) @ X2 )
        = ( k7_relat_1 @ ( k8_relat_1 @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ X2 ) ) ) ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k7_relat_1 @ ( k2_wellord1 @ ( k8_relat_1 @ X1 @ X0 ) @ X2 ) @ X3 )
        = ( k7_relat_1 @ ( k8_relat_1 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) @ ( k3_xboole_0 @ X2 @ X3 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['25','30'])).

thf('32',plain,(
    ! [X20: $i,X21: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X20 @ X21 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relat_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ ( k2_wellord1 @ ( k8_relat_1 @ X1 @ X0 ) @ X2 ) @ X3 )
        = ( k7_relat_1 @ ( k8_relat_1 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k2_wellord1 @ ( k8_relat_1 @ X0 @ X2 ) @ X1 ) @ X0 )
        = ( k2_wellord1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['24','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k7_relat_1 @ ( k2_wellord1 @ ( k8_relat_1 @ X0 @ X2 ) @ X1 ) @ X0 )
        = ( k2_wellord1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k8_relat_1 @ X2 @ ( k2_wellord1 @ X1 @ X0 ) ) @ X2 )
        = ( k2_wellord1 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['23','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k7_relat_1 @ ( k8_relat_1 @ X2 @ ( k2_wellord1 @ X1 @ X0 ) ) @ X2 )
        = ( k2_wellord1 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k2_wellord1 @ X32 @ X31 )
        = ( k7_relat_1 @ ( k8_relat_1 @ X31 @ X32 ) @ X31 ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t17_wellord1])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_wellord1 @ ( k2_wellord1 @ X2 @ X1 ) @ X0 )
        = ( k2_wellord1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k2_wellord1 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k2_wellord1 @ X32 @ X31 )
        = ( k7_relat_1 @ ( k8_relat_1 @ X31 @ X32 ) @ X31 ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t17_wellord1])).

thf('41',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X20: $i,X21: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X20 @ X21 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relat_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k2_wellord1 @ ( k2_wellord1 @ X2 @ X1 ) @ X0 )
        = ( k2_wellord1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['39','44'])).

thf(t26_wellord1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k2_wellord1 @ ( k2_wellord1 @ C @ A ) @ B )
        = ( k2_wellord1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( k2_wellord1 @ ( k2_wellord1 @ C @ A ) @ B )
          = ( k2_wellord1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t26_wellord1])).

thf('46',plain,(
    ( k2_wellord1 @ ( k2_wellord1 @ sk_C @ sk_A ) @ sk_B )
 != ( k2_wellord1 @ sk_C @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('48',plain,(
    ( k2_wellord1 @ ( k2_wellord1 @ sk_C @ sk_A ) @ sk_B )
 != ( k2_wellord1 @ sk_C @ ( k3_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( ( k2_wellord1 @ sk_C @ ( k3_xboole_0 @ sk_A @ sk_B ) )
     != ( k2_wellord1 @ sk_C @ ( k3_xboole_0 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('51',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ( k2_wellord1 @ sk_C @ ( k3_xboole_0 @ sk_B @ sk_A ) )
 != ( k2_wellord1 @ sk_C @ ( k3_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,(
    $false ),
    inference(simplify,[status(thm)],['52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.V86yLLYPVs
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:01:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 5.13/5.35  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 5.13/5.35  % Solved by: fo/fo7.sh
% 5.13/5.35  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.13/5.35  % done 2198 iterations in 4.875s
% 5.13/5.35  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 5.13/5.35  % SZS output start Refutation
% 5.13/5.35  thf(sk_A_type, type, sk_A: $i).
% 5.13/5.35  thf(sk_B_type, type, sk_B: $i).
% 5.13/5.35  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 5.13/5.35  thf(k2_wellord1_type, type, k2_wellord1: $i > $i > $i).
% 5.13/5.35  thf(sk_C_type, type, sk_C: $i).
% 5.13/5.35  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 5.13/5.35  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 5.13/5.35  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 5.13/5.35  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 5.13/5.35  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 5.13/5.35  thf(commutativity_k2_tarski, axiom,
% 5.13/5.35    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 5.13/5.35  thf('0', plain,
% 5.13/5.35      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 5.13/5.35      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 5.13/5.35  thf(t12_setfam_1, axiom,
% 5.13/5.35    (![A:$i,B:$i]:
% 5.13/5.35     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 5.13/5.35  thf('1', plain,
% 5.13/5.35      (![X16 : $i, X17 : $i]:
% 5.13/5.35         ((k1_setfam_1 @ (k2_tarski @ X16 @ X17)) = (k3_xboole_0 @ X16 @ X17))),
% 5.13/5.35      inference('cnf', [status(esa)], [t12_setfam_1])).
% 5.13/5.35  thf('2', plain,
% 5.13/5.35      (![X0 : $i, X1 : $i]:
% 5.13/5.35         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 5.13/5.35      inference('sup+', [status(thm)], ['0', '1'])).
% 5.13/5.35  thf('3', plain,
% 5.13/5.35      (![X16 : $i, X17 : $i]:
% 5.13/5.35         ((k1_setfam_1 @ (k2_tarski @ X16 @ X17)) = (k3_xboole_0 @ X16 @ X17))),
% 5.13/5.35      inference('cnf', [status(esa)], [t12_setfam_1])).
% 5.13/5.35  thf('4', plain,
% 5.13/5.35      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 5.13/5.35      inference('sup+', [status(thm)], ['2', '3'])).
% 5.13/5.35  thf(t127_relat_1, axiom,
% 5.13/5.35    (![A:$i,B:$i,C:$i]:
% 5.13/5.35     ( ( v1_relat_1 @ C ) =>
% 5.13/5.35       ( ( k8_relat_1 @ A @ ( k8_relat_1 @ B @ C ) ) =
% 5.13/5.35         ( k8_relat_1 @ ( k3_xboole_0 @ A @ B ) @ C ) ) ))).
% 5.13/5.35  thf('5', plain,
% 5.13/5.35      (![X25 : $i, X26 : $i, X27 : $i]:
% 5.13/5.35         (((k8_relat_1 @ X25 @ (k8_relat_1 @ X26 @ X27))
% 5.13/5.35            = (k8_relat_1 @ (k3_xboole_0 @ X25 @ X26) @ X27))
% 5.13/5.35          | ~ (v1_relat_1 @ X27))),
% 5.13/5.35      inference('cnf', [status(esa)], [t127_relat_1])).
% 5.13/5.35  thf(t17_wellord1, axiom,
% 5.13/5.35    (![A:$i,B:$i]:
% 5.13/5.35     ( ( v1_relat_1 @ B ) =>
% 5.13/5.35       ( ( k2_wellord1 @ B @ A ) = ( k7_relat_1 @ ( k8_relat_1 @ A @ B ) @ A ) ) ))).
% 5.13/5.35  thf('6', plain,
% 5.13/5.35      (![X31 : $i, X32 : $i]:
% 5.13/5.35         (((k2_wellord1 @ X32 @ X31)
% 5.13/5.35            = (k7_relat_1 @ (k8_relat_1 @ X31 @ X32) @ X31))
% 5.13/5.35          | ~ (v1_relat_1 @ X32))),
% 5.13/5.35      inference('cnf', [status(esa)], [t17_wellord1])).
% 5.13/5.35  thf('7', plain,
% 5.13/5.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.13/5.35         (((k2_wellord1 @ (k8_relat_1 @ X1 @ X0) @ X2)
% 5.13/5.35            = (k7_relat_1 @ (k8_relat_1 @ (k3_xboole_0 @ X2 @ X1) @ X0) @ X2))
% 5.13/5.35          | ~ (v1_relat_1 @ X0)
% 5.13/5.35          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X0)))),
% 5.13/5.35      inference('sup+', [status(thm)], ['5', '6'])).
% 5.13/5.35  thf(dt_k8_relat_1, axiom,
% 5.13/5.35    (![A:$i,B:$i]:
% 5.13/5.35     ( ( v1_relat_1 @ B ) => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ))).
% 5.13/5.35  thf('8', plain,
% 5.13/5.35      (![X20 : $i, X21 : $i]:
% 5.13/5.35         ((v1_relat_1 @ (k8_relat_1 @ X20 @ X21)) | ~ (v1_relat_1 @ X21))),
% 5.13/5.35      inference('cnf', [status(esa)], [dt_k8_relat_1])).
% 5.13/5.35  thf('9', plain,
% 5.13/5.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.13/5.35         (~ (v1_relat_1 @ X0)
% 5.13/5.35          | ((k2_wellord1 @ (k8_relat_1 @ X1 @ X0) @ X2)
% 5.13/5.35              = (k7_relat_1 @ (k8_relat_1 @ (k3_xboole_0 @ X2 @ X1) @ X0) @ X2)))),
% 5.13/5.35      inference('clc', [status(thm)], ['7', '8'])).
% 5.13/5.35  thf('10', plain,
% 5.13/5.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.13/5.35         (((k2_wellord1 @ (k8_relat_1 @ X1 @ X2) @ X0)
% 5.13/5.35            = (k7_relat_1 @ (k8_relat_1 @ (k3_xboole_0 @ X1 @ X0) @ X2) @ X0))
% 5.13/5.35          | ~ (v1_relat_1 @ X2))),
% 5.13/5.35      inference('sup+', [status(thm)], ['4', '9'])).
% 5.13/5.35  thf(t140_relat_1, axiom,
% 5.13/5.35    (![A:$i,B:$i,C:$i]:
% 5.13/5.35     ( ( v1_relat_1 @ C ) =>
% 5.13/5.35       ( ( k7_relat_1 @ ( k8_relat_1 @ A @ C ) @ B ) =
% 5.13/5.35         ( k8_relat_1 @ A @ ( k7_relat_1 @ C @ B ) ) ) ))).
% 5.13/5.35  thf('11', plain,
% 5.13/5.35      (![X28 : $i, X29 : $i, X30 : $i]:
% 5.13/5.35         (((k7_relat_1 @ (k8_relat_1 @ X28 @ X29) @ X30)
% 5.13/5.35            = (k8_relat_1 @ X28 @ (k7_relat_1 @ X29 @ X30)))
% 5.13/5.35          | ~ (v1_relat_1 @ X29))),
% 5.13/5.35      inference('cnf', [status(esa)], [t140_relat_1])).
% 5.13/5.35  thf('12', plain,
% 5.13/5.35      (![X31 : $i, X32 : $i]:
% 5.13/5.35         (((k2_wellord1 @ X32 @ X31)
% 5.13/5.35            = (k7_relat_1 @ (k8_relat_1 @ X31 @ X32) @ X31))
% 5.13/5.35          | ~ (v1_relat_1 @ X32))),
% 5.13/5.35      inference('cnf', [status(esa)], [t17_wellord1])).
% 5.13/5.35  thf('13', plain,
% 5.13/5.35      (![X28 : $i, X29 : $i, X30 : $i]:
% 5.13/5.35         (((k7_relat_1 @ (k8_relat_1 @ X28 @ X29) @ X30)
% 5.13/5.35            = (k8_relat_1 @ X28 @ (k7_relat_1 @ X29 @ X30)))
% 5.13/5.35          | ~ (v1_relat_1 @ X29))),
% 5.13/5.35      inference('cnf', [status(esa)], [t140_relat_1])).
% 5.13/5.35  thf('14', plain,
% 5.13/5.35      (![X25 : $i, X26 : $i, X27 : $i]:
% 5.13/5.35         (((k8_relat_1 @ X25 @ (k8_relat_1 @ X26 @ X27))
% 5.13/5.35            = (k8_relat_1 @ (k3_xboole_0 @ X25 @ X26) @ X27))
% 5.13/5.35          | ~ (v1_relat_1 @ X27))),
% 5.13/5.35      inference('cnf', [status(esa)], [t127_relat_1])).
% 5.13/5.35  thf('15', plain,
% 5.13/5.35      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.13/5.35         (((k8_relat_1 @ X3 @ (k7_relat_1 @ (k8_relat_1 @ X2 @ X1) @ X0))
% 5.13/5.35            = (k8_relat_1 @ (k3_xboole_0 @ X3 @ X2) @ (k7_relat_1 @ X1 @ X0)))
% 5.13/5.35          | ~ (v1_relat_1 @ X1)
% 5.13/5.35          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 5.13/5.35      inference('sup+', [status(thm)], ['13', '14'])).
% 5.13/5.35  thf(dt_k7_relat_1, axiom,
% 5.13/5.35    (![A:$i,B:$i]:
% 5.13/5.35     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 5.13/5.35  thf('16', plain,
% 5.13/5.35      (![X18 : $i, X19 : $i]:
% 5.13/5.35         (~ (v1_relat_1 @ X18) | (v1_relat_1 @ (k7_relat_1 @ X18 @ X19)))),
% 5.13/5.35      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 5.13/5.35  thf('17', plain,
% 5.13/5.35      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.13/5.35         (~ (v1_relat_1 @ X1)
% 5.13/5.35          | ((k8_relat_1 @ X3 @ (k7_relat_1 @ (k8_relat_1 @ X2 @ X1) @ X0))
% 5.13/5.35              = (k8_relat_1 @ (k3_xboole_0 @ X3 @ X2) @ (k7_relat_1 @ X1 @ X0))))),
% 5.13/5.35      inference('clc', [status(thm)], ['15', '16'])).
% 5.13/5.35  thf('18', plain,
% 5.13/5.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.13/5.35         (((k8_relat_1 @ X2 @ (k2_wellord1 @ X1 @ X0))
% 5.13/5.35            = (k8_relat_1 @ (k3_xboole_0 @ X2 @ X0) @ (k7_relat_1 @ X1 @ X0)))
% 5.13/5.35          | ~ (v1_relat_1 @ X1)
% 5.13/5.35          | ~ (v1_relat_1 @ X1))),
% 5.13/5.35      inference('sup+', [status(thm)], ['12', '17'])).
% 5.13/5.35  thf('19', plain,
% 5.13/5.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.13/5.35         (~ (v1_relat_1 @ X1)
% 5.13/5.35          | ((k8_relat_1 @ X2 @ (k2_wellord1 @ X1 @ X0))
% 5.13/5.35              = (k8_relat_1 @ (k3_xboole_0 @ X2 @ X0) @ (k7_relat_1 @ X1 @ X0))))),
% 5.13/5.35      inference('simplify', [status(thm)], ['18'])).
% 5.13/5.35  thf('20', plain,
% 5.13/5.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.13/5.35         (((k8_relat_1 @ X2 @ (k2_wellord1 @ X1 @ X0))
% 5.13/5.35            = (k7_relat_1 @ (k8_relat_1 @ (k3_xboole_0 @ X2 @ X0) @ X1) @ X0))
% 5.13/5.35          | ~ (v1_relat_1 @ X1)
% 5.13/5.35          | ~ (v1_relat_1 @ X1))),
% 5.13/5.35      inference('sup+', [status(thm)], ['11', '19'])).
% 5.13/5.35  thf('21', plain,
% 5.13/5.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.13/5.35         (~ (v1_relat_1 @ X1)
% 5.13/5.35          | ((k8_relat_1 @ X2 @ (k2_wellord1 @ X1 @ X0))
% 5.13/5.35              = (k7_relat_1 @ (k8_relat_1 @ (k3_xboole_0 @ X2 @ X0) @ X1) @ X0)))),
% 5.13/5.35      inference('simplify', [status(thm)], ['20'])).
% 5.13/5.35  thf('22', plain,
% 5.13/5.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.13/5.35         (((k8_relat_1 @ X2 @ (k2_wellord1 @ X1 @ X0))
% 5.13/5.35            = (k2_wellord1 @ (k8_relat_1 @ X2 @ X1) @ X0))
% 5.13/5.35          | ~ (v1_relat_1 @ X1)
% 5.13/5.35          | ~ (v1_relat_1 @ X1))),
% 5.13/5.35      inference('sup+', [status(thm)], ['10', '21'])).
% 5.13/5.35  thf('23', plain,
% 5.13/5.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.13/5.35         (~ (v1_relat_1 @ X1)
% 5.13/5.35          | ((k8_relat_1 @ X2 @ (k2_wellord1 @ X1 @ X0))
% 5.13/5.35              = (k2_wellord1 @ (k8_relat_1 @ X2 @ X1) @ X0)))),
% 5.13/5.35      inference('simplify', [status(thm)], ['22'])).
% 5.13/5.35  thf('24', plain,
% 5.13/5.35      (![X31 : $i, X32 : $i]:
% 5.13/5.35         (((k2_wellord1 @ X32 @ X31)
% 5.13/5.35            = (k7_relat_1 @ (k8_relat_1 @ X31 @ X32) @ X31))
% 5.13/5.35          | ~ (v1_relat_1 @ X32))),
% 5.13/5.35      inference('cnf', [status(esa)], [t17_wellord1])).
% 5.13/5.35  thf('25', plain,
% 5.13/5.35      (![X25 : $i, X26 : $i, X27 : $i]:
% 5.13/5.35         (((k8_relat_1 @ X25 @ (k8_relat_1 @ X26 @ X27))
% 5.13/5.35            = (k8_relat_1 @ (k3_xboole_0 @ X25 @ X26) @ X27))
% 5.13/5.35          | ~ (v1_relat_1 @ X27))),
% 5.13/5.35      inference('cnf', [status(esa)], [t127_relat_1])).
% 5.13/5.35  thf('26', plain,
% 5.13/5.35      (![X31 : $i, X32 : $i]:
% 5.13/5.35         (((k2_wellord1 @ X32 @ X31)
% 5.13/5.35            = (k7_relat_1 @ (k8_relat_1 @ X31 @ X32) @ X31))
% 5.13/5.35          | ~ (v1_relat_1 @ X32))),
% 5.13/5.35      inference('cnf', [status(esa)], [t17_wellord1])).
% 5.13/5.35  thf(t100_relat_1, axiom,
% 5.13/5.35    (![A:$i,B:$i,C:$i]:
% 5.13/5.35     ( ( v1_relat_1 @ C ) =>
% 5.13/5.35       ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 5.13/5.35         ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 5.13/5.35  thf('27', plain,
% 5.13/5.35      (![X22 : $i, X23 : $i, X24 : $i]:
% 5.13/5.35         (((k7_relat_1 @ (k7_relat_1 @ X22 @ X23) @ X24)
% 5.13/5.35            = (k7_relat_1 @ X22 @ (k3_xboole_0 @ X23 @ X24)))
% 5.13/5.35          | ~ (v1_relat_1 @ X22))),
% 5.13/5.35      inference('cnf', [status(esa)], [t100_relat_1])).
% 5.13/5.35  thf('28', plain,
% 5.13/5.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.13/5.35         (((k7_relat_1 @ (k2_wellord1 @ X1 @ X0) @ X2)
% 5.13/5.35            = (k7_relat_1 @ (k8_relat_1 @ X0 @ X1) @ (k3_xboole_0 @ X0 @ X2)))
% 5.13/5.35          | ~ (v1_relat_1 @ X1)
% 5.13/5.35          | ~ (v1_relat_1 @ (k8_relat_1 @ X0 @ X1)))),
% 5.13/5.35      inference('sup+', [status(thm)], ['26', '27'])).
% 5.13/5.35  thf('29', plain,
% 5.13/5.35      (![X20 : $i, X21 : $i]:
% 5.13/5.35         ((v1_relat_1 @ (k8_relat_1 @ X20 @ X21)) | ~ (v1_relat_1 @ X21))),
% 5.13/5.35      inference('cnf', [status(esa)], [dt_k8_relat_1])).
% 5.13/5.35  thf('30', plain,
% 5.13/5.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.13/5.35         (~ (v1_relat_1 @ X1)
% 5.13/5.35          | ((k7_relat_1 @ (k2_wellord1 @ X1 @ X0) @ X2)
% 5.13/5.35              = (k7_relat_1 @ (k8_relat_1 @ X0 @ X1) @ (k3_xboole_0 @ X0 @ X2))))),
% 5.13/5.35      inference('clc', [status(thm)], ['28', '29'])).
% 5.13/5.35  thf('31', plain,
% 5.13/5.35      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.13/5.35         (((k7_relat_1 @ (k2_wellord1 @ (k8_relat_1 @ X1 @ X0) @ X2) @ X3)
% 5.13/5.35            = (k7_relat_1 @ (k8_relat_1 @ (k3_xboole_0 @ X2 @ X1) @ X0) @ 
% 5.13/5.35               (k3_xboole_0 @ X2 @ X3)))
% 5.13/5.35          | ~ (v1_relat_1 @ X0)
% 5.13/5.35          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X0)))),
% 5.13/5.35      inference('sup+', [status(thm)], ['25', '30'])).
% 5.13/5.35  thf('32', plain,
% 5.13/5.35      (![X20 : $i, X21 : $i]:
% 5.13/5.35         ((v1_relat_1 @ (k8_relat_1 @ X20 @ X21)) | ~ (v1_relat_1 @ X21))),
% 5.13/5.35      inference('cnf', [status(esa)], [dt_k8_relat_1])).
% 5.13/5.35  thf('33', plain,
% 5.13/5.35      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.13/5.35         (~ (v1_relat_1 @ X0)
% 5.13/5.35          | ((k7_relat_1 @ (k2_wellord1 @ (k8_relat_1 @ X1 @ X0) @ X2) @ X3)
% 5.13/5.35              = (k7_relat_1 @ (k8_relat_1 @ (k3_xboole_0 @ X2 @ X1) @ X0) @ 
% 5.13/5.35                 (k3_xboole_0 @ X2 @ X3))))),
% 5.13/5.35      inference('clc', [status(thm)], ['31', '32'])).
% 5.13/5.35  thf('34', plain,
% 5.13/5.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.13/5.35         (((k7_relat_1 @ (k2_wellord1 @ (k8_relat_1 @ X0 @ X2) @ X1) @ X0)
% 5.13/5.35            = (k2_wellord1 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 5.13/5.35          | ~ (v1_relat_1 @ X2)
% 5.13/5.35          | ~ (v1_relat_1 @ X2))),
% 5.13/5.35      inference('sup+', [status(thm)], ['24', '33'])).
% 5.13/5.35  thf('35', plain,
% 5.13/5.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.13/5.35         (~ (v1_relat_1 @ X2)
% 5.13/5.35          | ((k7_relat_1 @ (k2_wellord1 @ (k8_relat_1 @ X0 @ X2) @ X1) @ X0)
% 5.13/5.35              = (k2_wellord1 @ X2 @ (k3_xboole_0 @ X1 @ X0))))),
% 5.13/5.35      inference('simplify', [status(thm)], ['34'])).
% 5.13/5.35  thf('36', plain,
% 5.13/5.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.13/5.35         (((k7_relat_1 @ (k8_relat_1 @ X2 @ (k2_wellord1 @ X1 @ X0)) @ X2)
% 5.13/5.35            = (k2_wellord1 @ X1 @ (k3_xboole_0 @ X0 @ X2)))
% 5.13/5.35          | ~ (v1_relat_1 @ X1)
% 5.13/5.35          | ~ (v1_relat_1 @ X1))),
% 5.13/5.35      inference('sup+', [status(thm)], ['23', '35'])).
% 5.13/5.35  thf('37', plain,
% 5.13/5.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.13/5.35         (~ (v1_relat_1 @ X1)
% 5.13/5.35          | ((k7_relat_1 @ (k8_relat_1 @ X2 @ (k2_wellord1 @ X1 @ X0)) @ X2)
% 5.13/5.35              = (k2_wellord1 @ X1 @ (k3_xboole_0 @ X0 @ X2))))),
% 5.13/5.35      inference('simplify', [status(thm)], ['36'])).
% 5.13/5.35  thf('38', plain,
% 5.13/5.35      (![X31 : $i, X32 : $i]:
% 5.13/5.35         (((k2_wellord1 @ X32 @ X31)
% 5.13/5.35            = (k7_relat_1 @ (k8_relat_1 @ X31 @ X32) @ X31))
% 5.13/5.35          | ~ (v1_relat_1 @ X32))),
% 5.13/5.35      inference('cnf', [status(esa)], [t17_wellord1])).
% 5.13/5.35  thf('39', plain,
% 5.13/5.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.13/5.35         (((k2_wellord1 @ (k2_wellord1 @ X2 @ X1) @ X0)
% 5.13/5.35            = (k2_wellord1 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 5.13/5.35          | ~ (v1_relat_1 @ X2)
% 5.13/5.35          | ~ (v1_relat_1 @ (k2_wellord1 @ X2 @ X1)))),
% 5.13/5.35      inference('sup+', [status(thm)], ['37', '38'])).
% 5.13/5.35  thf('40', plain,
% 5.13/5.35      (![X31 : $i, X32 : $i]:
% 5.13/5.35         (((k2_wellord1 @ X32 @ X31)
% 5.13/5.35            = (k7_relat_1 @ (k8_relat_1 @ X31 @ X32) @ X31))
% 5.13/5.35          | ~ (v1_relat_1 @ X32))),
% 5.13/5.35      inference('cnf', [status(esa)], [t17_wellord1])).
% 5.13/5.35  thf('41', plain,
% 5.13/5.35      (![X18 : $i, X19 : $i]:
% 5.13/5.35         (~ (v1_relat_1 @ X18) | (v1_relat_1 @ (k7_relat_1 @ X18 @ X19)))),
% 5.13/5.35      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 5.13/5.35  thf('42', plain,
% 5.13/5.35      (![X0 : $i, X1 : $i]:
% 5.13/5.35         ((v1_relat_1 @ (k2_wellord1 @ X1 @ X0))
% 5.13/5.35          | ~ (v1_relat_1 @ X1)
% 5.13/5.35          | ~ (v1_relat_1 @ (k8_relat_1 @ X0 @ X1)))),
% 5.13/5.35      inference('sup+', [status(thm)], ['40', '41'])).
% 5.13/5.35  thf('43', plain,
% 5.13/5.35      (![X20 : $i, X21 : $i]:
% 5.13/5.35         ((v1_relat_1 @ (k8_relat_1 @ X20 @ X21)) | ~ (v1_relat_1 @ X21))),
% 5.13/5.35      inference('cnf', [status(esa)], [dt_k8_relat_1])).
% 5.13/5.35  thf('44', plain,
% 5.13/5.35      (![X0 : $i, X1 : $i]:
% 5.13/5.35         (~ (v1_relat_1 @ X1) | (v1_relat_1 @ (k2_wellord1 @ X1 @ X0)))),
% 5.13/5.35      inference('clc', [status(thm)], ['42', '43'])).
% 5.13/5.35  thf('45', plain,
% 5.13/5.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.13/5.35         (~ (v1_relat_1 @ X2)
% 5.13/5.35          | ((k2_wellord1 @ (k2_wellord1 @ X2 @ X1) @ X0)
% 5.13/5.35              = (k2_wellord1 @ X2 @ (k3_xboole_0 @ X1 @ X0))))),
% 5.13/5.35      inference('clc', [status(thm)], ['39', '44'])).
% 5.13/5.35  thf(t26_wellord1, conjecture,
% 5.13/5.35    (![A:$i,B:$i,C:$i]:
% 5.13/5.35     ( ( v1_relat_1 @ C ) =>
% 5.13/5.35       ( ( k2_wellord1 @ ( k2_wellord1 @ C @ A ) @ B ) =
% 5.13/5.35         ( k2_wellord1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 5.13/5.35  thf(zf_stmt_0, negated_conjecture,
% 5.13/5.35    (~( ![A:$i,B:$i,C:$i]:
% 5.13/5.35        ( ( v1_relat_1 @ C ) =>
% 5.13/5.35          ( ( k2_wellord1 @ ( k2_wellord1 @ C @ A ) @ B ) =
% 5.13/5.35            ( k2_wellord1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )),
% 5.13/5.35    inference('cnf.neg', [status(esa)], [t26_wellord1])).
% 5.13/5.35  thf('46', plain,
% 5.13/5.35      (((k2_wellord1 @ (k2_wellord1 @ sk_C @ sk_A) @ sk_B)
% 5.13/5.35         != (k2_wellord1 @ sk_C @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 5.13/5.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.13/5.35  thf('47', plain,
% 5.13/5.35      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 5.13/5.35      inference('sup+', [status(thm)], ['2', '3'])).
% 5.13/5.35  thf('48', plain,
% 5.13/5.35      (((k2_wellord1 @ (k2_wellord1 @ sk_C @ sk_A) @ sk_B)
% 5.13/5.35         != (k2_wellord1 @ sk_C @ (k3_xboole_0 @ sk_B @ sk_A)))),
% 5.13/5.35      inference('demod', [status(thm)], ['46', '47'])).
% 5.13/5.35  thf('49', plain,
% 5.13/5.35      ((((k2_wellord1 @ sk_C @ (k3_xboole_0 @ sk_A @ sk_B))
% 5.13/5.35          != (k2_wellord1 @ sk_C @ (k3_xboole_0 @ sk_B @ sk_A)))
% 5.13/5.35        | ~ (v1_relat_1 @ sk_C))),
% 5.13/5.35      inference('sup-', [status(thm)], ['45', '48'])).
% 5.13/5.35  thf('50', plain,
% 5.13/5.35      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 5.13/5.35      inference('sup+', [status(thm)], ['2', '3'])).
% 5.13/5.35  thf('51', plain, ((v1_relat_1 @ sk_C)),
% 5.13/5.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.13/5.35  thf('52', plain,
% 5.13/5.35      (((k2_wellord1 @ sk_C @ (k3_xboole_0 @ sk_B @ sk_A))
% 5.13/5.35         != (k2_wellord1 @ sk_C @ (k3_xboole_0 @ sk_B @ sk_A)))),
% 5.13/5.35      inference('demod', [status(thm)], ['49', '50', '51'])).
% 5.13/5.35  thf('53', plain, ($false), inference('simplify', [status(thm)], ['52'])).
% 5.13/5.35  
% 5.13/5.35  % SZS output end Refutation
% 5.13/5.35  
% 5.13/5.36  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
