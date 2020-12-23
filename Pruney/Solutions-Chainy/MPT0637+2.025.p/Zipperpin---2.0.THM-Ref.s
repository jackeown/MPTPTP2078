%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.F7Gkcbq2ma

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:59 EST 2020

% Result     : Theorem 0.95s
% Output     : Refutation 0.95s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 318 expanded)
%              Number of leaves         :   28 ( 119 expanded)
%              Depth                    :   13
%              Number of atoms          :  702 (2497 expanded)
%              Number of equality atoms :   61 ( 211 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t123_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ B )
        = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k8_relat_1 @ X18 @ X17 )
        = ( k5_relat_1 @ X17 @ ( k6_relat_1 @ X18 ) ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t43_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
        = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t43_funct_1])).

thf('1',plain,(
    ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k6_relat_1 @ sk_A ) )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ sk_B ) )
     != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('3',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('4',plain,(
    ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ sk_B ) )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('6',plain,(
    ! [X21: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X21 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('7',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X25 @ X26 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X25 ) @ X26 ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( k3_xboole_0 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k8_relat_1 @ X18 @ X17 )
        = ( k5_relat_1 @ X17 @ ( k6_relat_1 @ X18 ) ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('12',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k7_relat_1 @ X28 @ X27 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X27 ) @ X28 ) )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('15',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['10','16'])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('18',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X29 ) @ X30 )
      | ( ( k7_relat_1 @ X29 @ X30 )
        = X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ( ( k7_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X2 )
        = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X21: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X21 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t124_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ B )
        = ( k3_xboole_0 @ B @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) )).

thf('21',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k8_relat_1 @ X20 @ X19 )
        = ( k3_xboole_0 @ X19 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X19 ) @ X20 ) ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t124_relat_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
        = ( k3_xboole_0 @ ( k6_relat_1 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k3_xboole_0 @ ( k6_relat_1 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf(fc1_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('25',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[fc1_relat_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( ( k7_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X2 )
        = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['19','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) @ X0 )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['5','29'])).

thf('31',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k8_relat_1 @ X18 @ X17 )
        = ( k5_relat_1 @ X17 @ ( k6_relat_1 @ X18 ) ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('32',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_tarski @ X3 @ X2 )
      = ( k2_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('33',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X22: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X22 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('40',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X23 ) @ X24 )
      | ( ( k5_relat_1 @ X23 @ ( k6_relat_1 @ X24 ) )
        = X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['38','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
        = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['31','44'])).

thf('46',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf(t100_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('48',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X14 @ X15 ) @ X16 )
        = ( k7_relat_1 @ X14 @ ( k3_xboole_0 @ X15 @ X16 ) ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X2 ) @ X1 ) @ X0 )
        = ( k8_relat_1 @ X2 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('52',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k8_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) @ X0 )
      = ( k8_relat_1 @ X2 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['47','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['30','54'])).

thf('56',plain,(
    ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ sk_B ) )
 != ( k8_relat_1 @ sk_B @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['30','54'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['30','54'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ sk_B ) )
 != ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['56','61'])).

thf('63',plain,(
    $false ),
    inference(simplify,[status(thm)],['62'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.F7Gkcbq2ma
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:33:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.95/1.12  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.95/1.12  % Solved by: fo/fo7.sh
% 0.95/1.12  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.95/1.12  % done 1185 iterations in 0.702s
% 0.95/1.12  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.95/1.12  % SZS output start Refutation
% 0.95/1.12  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.95/1.12  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.95/1.12  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.95/1.12  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.95/1.12  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.95/1.12  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.95/1.12  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.95/1.12  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.95/1.12  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.95/1.12  thf(sk_A_type, type, sk_A: $i).
% 0.95/1.12  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.95/1.12  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.95/1.12  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.95/1.12  thf(sk_B_type, type, sk_B: $i).
% 0.95/1.12  thf(t123_relat_1, axiom,
% 0.95/1.12    (![A:$i,B:$i]:
% 0.95/1.12     ( ( v1_relat_1 @ B ) =>
% 0.95/1.12       ( ( k8_relat_1 @ A @ B ) = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ))).
% 0.95/1.12  thf('0', plain,
% 0.95/1.12      (![X17 : $i, X18 : $i]:
% 0.95/1.12         (((k8_relat_1 @ X18 @ X17) = (k5_relat_1 @ X17 @ (k6_relat_1 @ X18)))
% 0.95/1.12          | ~ (v1_relat_1 @ X17))),
% 0.95/1.12      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.95/1.12  thf(t43_funct_1, conjecture,
% 0.95/1.12    (![A:$i,B:$i]:
% 0.95/1.12     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.95/1.12       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.95/1.12  thf(zf_stmt_0, negated_conjecture,
% 0.95/1.12    (~( ![A:$i,B:$i]:
% 0.95/1.12        ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.95/1.12          ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 0.95/1.12    inference('cnf.neg', [status(esa)], [t43_funct_1])).
% 0.95/1.12  thf('1', plain,
% 0.95/1.12      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A))
% 0.95/1.12         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.95/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.95/1.12  thf('2', plain,
% 0.95/1.12      ((((k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B))
% 0.95/1.12          != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))
% 0.95/1.12        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_B)))),
% 0.95/1.12      inference('sup-', [status(thm)], ['0', '1'])).
% 0.95/1.12  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.95/1.12  thf('3', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.95/1.12      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.95/1.12  thf('4', plain,
% 0.95/1.12      (((k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B))
% 0.95/1.12         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.95/1.12      inference('demod', [status(thm)], ['2', '3'])).
% 0.95/1.12  thf(t17_xboole_1, axiom,
% 0.95/1.12    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.95/1.12  thf('5', plain,
% 0.95/1.12      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.95/1.12      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.95/1.12  thf(t71_relat_1, axiom,
% 0.95/1.12    (![A:$i]:
% 0.95/1.12     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.95/1.12       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.95/1.12  thf('6', plain, (![X21 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X21)) = (X21))),
% 0.95/1.12      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.95/1.12  thf(t90_relat_1, axiom,
% 0.95/1.12    (![A:$i,B:$i]:
% 0.95/1.12     ( ( v1_relat_1 @ B ) =>
% 0.95/1.12       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 0.95/1.12         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.95/1.12  thf('7', plain,
% 0.95/1.12      (![X25 : $i, X26 : $i]:
% 0.95/1.12         (((k1_relat_1 @ (k7_relat_1 @ X25 @ X26))
% 0.95/1.12            = (k3_xboole_0 @ (k1_relat_1 @ X25) @ X26))
% 0.95/1.12          | ~ (v1_relat_1 @ X25))),
% 0.95/1.12      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.95/1.12  thf('8', plain,
% 0.95/1.12      (![X0 : $i, X1 : $i]:
% 0.95/1.12         (((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.95/1.12            = (k3_xboole_0 @ X0 @ X1))
% 0.95/1.12          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.95/1.12      inference('sup+', [status(thm)], ['6', '7'])).
% 0.95/1.12  thf('9', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.95/1.12      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.95/1.12  thf('10', plain,
% 0.95/1.12      (![X0 : $i, X1 : $i]:
% 0.95/1.12         ((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.95/1.12           = (k3_xboole_0 @ X0 @ X1))),
% 0.95/1.12      inference('demod', [status(thm)], ['8', '9'])).
% 0.95/1.12  thf('11', plain,
% 0.95/1.12      (![X17 : $i, X18 : $i]:
% 0.95/1.12         (((k8_relat_1 @ X18 @ X17) = (k5_relat_1 @ X17 @ (k6_relat_1 @ X18)))
% 0.95/1.12          | ~ (v1_relat_1 @ X17))),
% 0.95/1.12      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.95/1.12  thf(t94_relat_1, axiom,
% 0.95/1.12    (![A:$i,B:$i]:
% 0.95/1.12     ( ( v1_relat_1 @ B ) =>
% 0.95/1.12       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.95/1.12  thf('12', plain,
% 0.95/1.12      (![X27 : $i, X28 : $i]:
% 0.95/1.12         (((k7_relat_1 @ X28 @ X27) = (k5_relat_1 @ (k6_relat_1 @ X27) @ X28))
% 0.95/1.12          | ~ (v1_relat_1 @ X28))),
% 0.95/1.12      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.95/1.12  thf('13', plain,
% 0.95/1.12      (![X0 : $i, X1 : $i]:
% 0.95/1.12         (((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.95/1.12            = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.95/1.12          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.95/1.12          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.95/1.12      inference('sup+', [status(thm)], ['11', '12'])).
% 0.95/1.12  thf('14', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.95/1.12      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.95/1.12  thf('15', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.95/1.12      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.95/1.12  thf('16', plain,
% 0.95/1.12      (![X0 : $i, X1 : $i]:
% 0.95/1.12         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.95/1.12           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.95/1.12      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.95/1.12  thf('17', plain,
% 0.95/1.12      (![X0 : $i, X1 : $i]:
% 0.95/1.12         ((k1_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 0.95/1.12           = (k3_xboole_0 @ X0 @ X1))),
% 0.95/1.12      inference('demod', [status(thm)], ['10', '16'])).
% 0.95/1.12  thf(t97_relat_1, axiom,
% 0.95/1.12    (![A:$i,B:$i]:
% 0.95/1.12     ( ( v1_relat_1 @ B ) =>
% 0.95/1.12       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.95/1.12         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.95/1.12  thf('18', plain,
% 0.95/1.12      (![X29 : $i, X30 : $i]:
% 0.95/1.12         (~ (r1_tarski @ (k1_relat_1 @ X29) @ X30)
% 0.95/1.12          | ((k7_relat_1 @ X29 @ X30) = (X29))
% 0.95/1.12          | ~ (v1_relat_1 @ X29))),
% 0.95/1.12      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.95/1.12  thf('19', plain,
% 0.95/1.12      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.95/1.12         (~ (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.95/1.12          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.95/1.12          | ((k7_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ X2)
% 0.95/1.12              = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 0.95/1.12      inference('sup-', [status(thm)], ['17', '18'])).
% 0.95/1.12  thf('20', plain, (![X21 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X21)) = (X21))),
% 0.95/1.12      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.95/1.12  thf(t124_relat_1, axiom,
% 0.95/1.12    (![A:$i,B:$i]:
% 0.95/1.12     ( ( v1_relat_1 @ B ) =>
% 0.95/1.12       ( ( k8_relat_1 @ A @ B ) =
% 0.95/1.12         ( k3_xboole_0 @ B @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ))).
% 0.95/1.12  thf('21', plain,
% 0.95/1.12      (![X19 : $i, X20 : $i]:
% 0.95/1.12         (((k8_relat_1 @ X20 @ X19)
% 0.95/1.12            = (k3_xboole_0 @ X19 @ (k2_zfmisc_1 @ (k1_relat_1 @ X19) @ X20)))
% 0.95/1.12          | ~ (v1_relat_1 @ X19))),
% 0.95/1.12      inference('cnf', [status(esa)], [t124_relat_1])).
% 0.95/1.12  thf('22', plain,
% 0.95/1.12      (![X0 : $i, X1 : $i]:
% 0.95/1.12         (((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 0.95/1.12            = (k3_xboole_0 @ (k6_relat_1 @ X0) @ (k2_zfmisc_1 @ X0 @ X1)))
% 0.95/1.12          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.95/1.12      inference('sup+', [status(thm)], ['20', '21'])).
% 0.95/1.12  thf('23', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.95/1.12      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.95/1.12  thf('24', plain,
% 0.95/1.12      (![X0 : $i, X1 : $i]:
% 0.95/1.12         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 0.95/1.12           = (k3_xboole_0 @ (k6_relat_1 @ X0) @ (k2_zfmisc_1 @ X0 @ X1)))),
% 0.95/1.12      inference('demod', [status(thm)], ['22', '23'])).
% 0.95/1.12  thf(fc1_relat_1, axiom,
% 0.95/1.12    (![A:$i,B:$i]:
% 0.95/1.12     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.95/1.12  thf('25', plain,
% 0.95/1.12      (![X12 : $i, X13 : $i]:
% 0.95/1.12         (~ (v1_relat_1 @ X12) | (v1_relat_1 @ (k3_xboole_0 @ X12 @ X13)))),
% 0.95/1.12      inference('cnf', [status(esa)], [fc1_relat_1])).
% 0.95/1.12  thf('26', plain,
% 0.95/1.12      (![X0 : $i, X1 : $i]:
% 0.95/1.12         ((v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.95/1.12          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.95/1.12      inference('sup+', [status(thm)], ['24', '25'])).
% 0.95/1.12  thf('27', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.95/1.12      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.95/1.12  thf('28', plain,
% 0.95/1.12      (![X0 : $i, X1 : $i]:
% 0.95/1.12         (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.95/1.12      inference('demod', [status(thm)], ['26', '27'])).
% 0.95/1.12  thf('29', plain,
% 0.95/1.12      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.95/1.12         (~ (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.95/1.12          | ((k7_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ X2)
% 0.95/1.12              = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 0.95/1.12      inference('demod', [status(thm)], ['19', '28'])).
% 0.95/1.12  thf('30', plain,
% 0.95/1.12      (![X0 : $i, X1 : $i]:
% 0.95/1.12         ((k7_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)) @ X0)
% 0.95/1.12           = (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))),
% 0.95/1.12      inference('sup-', [status(thm)], ['5', '29'])).
% 0.95/1.12  thf('31', plain,
% 0.95/1.12      (![X17 : $i, X18 : $i]:
% 0.95/1.12         (((k8_relat_1 @ X18 @ X17) = (k5_relat_1 @ X17 @ (k6_relat_1 @ X18)))
% 0.95/1.12          | ~ (v1_relat_1 @ X17))),
% 0.95/1.12      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.95/1.12  thf(commutativity_k2_tarski, axiom,
% 0.95/1.12    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.95/1.12  thf('32', plain,
% 0.95/1.12      (![X2 : $i, X3 : $i]: ((k2_tarski @ X3 @ X2) = (k2_tarski @ X2 @ X3))),
% 0.95/1.12      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.95/1.12  thf(t12_setfam_1, axiom,
% 0.95/1.12    (![A:$i,B:$i]:
% 0.95/1.12     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.95/1.12  thf('33', plain,
% 0.95/1.12      (![X9 : $i, X10 : $i]:
% 0.95/1.12         ((k1_setfam_1 @ (k2_tarski @ X9 @ X10)) = (k3_xboole_0 @ X9 @ X10))),
% 0.95/1.12      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.95/1.12  thf('34', plain,
% 0.95/1.12      (![X0 : $i, X1 : $i]:
% 0.95/1.12         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.95/1.12      inference('sup+', [status(thm)], ['32', '33'])).
% 0.95/1.12  thf('35', plain,
% 0.95/1.12      (![X9 : $i, X10 : $i]:
% 0.95/1.12         ((k1_setfam_1 @ (k2_tarski @ X9 @ X10)) = (k3_xboole_0 @ X9 @ X10))),
% 0.95/1.12      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.95/1.12  thf('36', plain,
% 0.95/1.12      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.95/1.12      inference('sup+', [status(thm)], ['34', '35'])).
% 0.95/1.12  thf('37', plain,
% 0.95/1.12      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.95/1.12      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.95/1.12  thf('38', plain,
% 0.95/1.12      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.95/1.12      inference('sup+', [status(thm)], ['36', '37'])).
% 0.95/1.12  thf('39', plain, (![X22 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X22)) = (X22))),
% 0.95/1.12      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.95/1.12  thf(t79_relat_1, axiom,
% 0.95/1.12    (![A:$i,B:$i]:
% 0.95/1.12     ( ( v1_relat_1 @ B ) =>
% 0.95/1.12       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.95/1.12         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 0.95/1.12  thf('40', plain,
% 0.95/1.12      (![X23 : $i, X24 : $i]:
% 0.95/1.12         (~ (r1_tarski @ (k2_relat_1 @ X23) @ X24)
% 0.95/1.12          | ((k5_relat_1 @ X23 @ (k6_relat_1 @ X24)) = (X23))
% 0.95/1.12          | ~ (v1_relat_1 @ X23))),
% 0.95/1.12      inference('cnf', [status(esa)], [t79_relat_1])).
% 0.95/1.12  thf('41', plain,
% 0.95/1.12      (![X0 : $i, X1 : $i]:
% 0.95/1.12         (~ (r1_tarski @ X0 @ X1)
% 0.95/1.12          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.95/1.12          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 0.95/1.12              = (k6_relat_1 @ X0)))),
% 0.95/1.12      inference('sup-', [status(thm)], ['39', '40'])).
% 0.95/1.12  thf('42', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.95/1.12      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.95/1.12  thf('43', plain,
% 0.95/1.12      (![X0 : $i, X1 : $i]:
% 0.95/1.12         (~ (r1_tarski @ X0 @ X1)
% 0.95/1.12          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 0.95/1.12              = (k6_relat_1 @ X0)))),
% 0.95/1.12      inference('demod', [status(thm)], ['41', '42'])).
% 0.95/1.12  thf('44', plain,
% 0.95/1.12      (![X0 : $i, X1 : $i]:
% 0.95/1.12         ((k5_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.95/1.12           (k6_relat_1 @ X0)) = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.95/1.12      inference('sup-', [status(thm)], ['38', '43'])).
% 0.95/1.12  thf('45', plain,
% 0.95/1.12      (![X0 : $i, X1 : $i]:
% 0.95/1.12         (((k8_relat_1 @ X0 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.95/1.12            = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.95/1.12          | ~ (v1_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.95/1.12      inference('sup+', [status(thm)], ['31', '44'])).
% 0.95/1.12  thf('46', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.95/1.12      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.95/1.12  thf('47', plain,
% 0.95/1.12      (![X0 : $i, X1 : $i]:
% 0.95/1.12         ((k8_relat_1 @ X0 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.95/1.12           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.95/1.12      inference('demod', [status(thm)], ['45', '46'])).
% 0.95/1.12  thf(t100_relat_1, axiom,
% 0.95/1.12    (![A:$i,B:$i,C:$i]:
% 0.95/1.12     ( ( v1_relat_1 @ C ) =>
% 0.95/1.12       ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.95/1.12         ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 0.95/1.12  thf('48', plain,
% 0.95/1.12      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.95/1.12         (((k7_relat_1 @ (k7_relat_1 @ X14 @ X15) @ X16)
% 0.95/1.12            = (k7_relat_1 @ X14 @ (k3_xboole_0 @ X15 @ X16)))
% 0.95/1.12          | ~ (v1_relat_1 @ X14))),
% 0.95/1.12      inference('cnf', [status(esa)], [t100_relat_1])).
% 0.95/1.12  thf('49', plain,
% 0.95/1.12      (![X0 : $i, X1 : $i]:
% 0.95/1.12         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.95/1.12           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.95/1.12      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.95/1.12  thf('50', plain,
% 0.95/1.12      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.95/1.12         (((k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X2) @ X1) @ X0)
% 0.95/1.12            = (k8_relat_1 @ X2 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))
% 0.95/1.12          | ~ (v1_relat_1 @ (k6_relat_1 @ X2)))),
% 0.95/1.12      inference('sup+', [status(thm)], ['48', '49'])).
% 0.95/1.12  thf('51', plain,
% 0.95/1.12      (![X0 : $i, X1 : $i]:
% 0.95/1.12         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.95/1.12           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.95/1.12      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.95/1.12  thf('52', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.95/1.12      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.95/1.12  thf('53', plain,
% 0.95/1.12      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.95/1.12         ((k7_relat_1 @ (k8_relat_1 @ X2 @ (k6_relat_1 @ X1)) @ X0)
% 0.95/1.12           = (k8_relat_1 @ X2 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.95/1.12      inference('demod', [status(thm)], ['50', '51', '52'])).
% 0.95/1.12  thf('54', plain,
% 0.95/1.12      (![X0 : $i, X1 : $i]:
% 0.95/1.12         ((k7_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)) @ X0)
% 0.95/1.12           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.95/1.12      inference('demod', [status(thm)], ['47', '53'])).
% 0.95/1.12  thf('55', plain,
% 0.95/1.12      (![X0 : $i, X1 : $i]:
% 0.95/1.12         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 0.95/1.12           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.95/1.12      inference('sup+', [status(thm)], ['30', '54'])).
% 0.95/1.12  thf('56', plain,
% 0.95/1.12      (((k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B))
% 0.95/1.12         != (k8_relat_1 @ sk_B @ (k6_relat_1 @ sk_A)))),
% 0.95/1.12      inference('demod', [status(thm)], ['4', '55'])).
% 0.95/1.12  thf('57', plain,
% 0.95/1.12      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.95/1.12      inference('sup+', [status(thm)], ['34', '35'])).
% 0.95/1.12  thf('58', plain,
% 0.95/1.12      (![X0 : $i, X1 : $i]:
% 0.95/1.12         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 0.95/1.12           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.95/1.12      inference('sup+', [status(thm)], ['30', '54'])).
% 0.95/1.12  thf('59', plain,
% 0.95/1.12      (![X0 : $i, X1 : $i]:
% 0.95/1.12         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 0.95/1.12           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.95/1.12      inference('sup+', [status(thm)], ['57', '58'])).
% 0.95/1.12  thf('60', plain,
% 0.95/1.12      (![X0 : $i, X1 : $i]:
% 0.95/1.12         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 0.95/1.12           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.95/1.12      inference('sup+', [status(thm)], ['30', '54'])).
% 0.95/1.12  thf('61', plain,
% 0.95/1.12      (![X0 : $i, X1 : $i]:
% 0.95/1.12         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 0.95/1.12           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.95/1.12      inference('sup+', [status(thm)], ['59', '60'])).
% 0.95/1.12  thf('62', plain,
% 0.95/1.12      (((k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B))
% 0.95/1.12         != (k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B)))),
% 0.95/1.12      inference('demod', [status(thm)], ['56', '61'])).
% 0.95/1.12  thf('63', plain, ($false), inference('simplify', [status(thm)], ['62'])).
% 0.95/1.12  
% 0.95/1.12  % SZS output end Refutation
% 0.95/1.12  
% 0.95/1.13  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
