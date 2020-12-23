%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8ibrgo8WlK

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:58 EST 2020

% Result     : Theorem 0.53s
% Output     : Refutation 0.53s
% Verified   : 
% Statistics : Number of formulae       :  178 (1775 expanded)
%              Number of leaves         :   30 ( 646 expanded)
%              Depth                    :   19
%              Number of atoms          : 1508 (14699 expanded)
%              Number of equality atoms :  127 (1242 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(t123_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ B )
        = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k8_relat_1 @ X16 @ X15 )
        = ( k5_relat_1 @ X15 @ ( k6_relat_1 @ X16 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
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

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('3',plain,(
    ! [X30: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

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
    ! [X22: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X22 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('7',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X28 ) @ X29 )
      | ( ( k7_relat_1 @ X28 @ X29 )
        = X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X30: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k8_relat_1 @ X16 @ X15 )
        = ( k5_relat_1 @ X15 @ ( k6_relat_1 @ X16 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('12',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k7_relat_1 @ X27 @ X26 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X26 ) @ X27 ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X30: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('15',plain,(
    ! [X30: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['10','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['5','17'])).

thf(t140_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ ( k8_relat_1 @ A @ C ) @ B )
        = ( k8_relat_1 @ A @ ( k7_relat_1 @ C @ B ) ) ) ) )).

thf('19',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k7_relat_1 @ ( k8_relat_1 @ X17 @ X18 ) @ X19 )
        = ( k8_relat_1 @ X17 @ ( k7_relat_1 @ X18 @ X19 ) ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t140_relat_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X2 )
        = ( k8_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X2 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('23',plain,(
    ! [X30: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k8_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k6_relat_1 @ X2 ) )
      = ( k8_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X2 ) ) ) ) ),
    inference(demod,[status(thm)],['20','21','22','23'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('25',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_tarski @ X3 @ X2 )
      = ( k2_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('26',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['5','17'])).

thf(t119_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('31',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k2_relat_1 @ ( k8_relat_1 @ X14 @ X13 ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ X13 ) @ X14 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t119_relat_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ ( k6_relat_1 @ X1 ) ) @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X23: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('34',plain,(
    ! [X23: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('35',plain,(
    ! [X30: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['32','33','34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['29','36'])).

thf('38',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k2_relat_1 @ ( k8_relat_1 @ X14 @ X13 ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ X13 ) @ X14 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t119_relat_1])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('39',plain,(
    ! [X25: $i] :
      ( ( ( k5_relat_1 @ X25 @ ( k6_relat_1 @ ( k2_relat_1 @ X25 ) ) )
        = X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k8_relat_1 @ X0 @ X1 ) @ ( k6_relat_1 @ ( k3_xboole_0 @ ( k2_relat_1 @ X1 ) @ X0 ) ) )
        = ( k8_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k8_relat_1 @ X16 @ X15 )
        = ( k5_relat_1 @ X15 @ ( k6_relat_1 @ X16 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('42',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_relat_1 @ X12 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X30: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k8_relat_1 @ X0 @ X1 ) @ ( k6_relat_1 @ ( k3_xboole_0 @ ( k2_relat_1 @ X1 ) @ X0 ) ) )
        = ( k8_relat_1 @ X0 @ X1 ) ) ) ),
    inference(clc,[status(thm)],['40','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k8_relat_1 @ ( k3_xboole_0 @ X0 @ ( k2_relat_1 @ X1 ) ) @ X1 ) @ ( k6_relat_1 @ ( k3_xboole_0 @ ( k2_relat_1 @ X1 ) @ X0 ) ) )
        = ( k8_relat_1 @ ( k3_xboole_0 @ X0 @ ( k2_relat_1 @ X1 ) ) @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['37','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k8_relat_1 @ ( k3_xboole_0 @ X1 @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) @ ( k6_relat_1 @ X0 ) ) @ ( k6_relat_1 @ ( k3_xboole_0 @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ X1 ) ) )
        = ( k8_relat_1 @ ( k3_xboole_0 @ X1 @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['24','48'])).

thf('50',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k2_relat_1 @ ( k8_relat_1 @ X14 @ X13 ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ X13 ) @ X14 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t119_relat_1])).

thf('51',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k8_relat_1 @ X16 @ X15 )
        = ( k5_relat_1 @ X15 @ ( k6_relat_1 @ X16 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('52',plain,(
    ! [X23: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('53',plain,(
    ! [X25: $i] :
      ( ( ( k5_relat_1 @ X25 @ ( k6_relat_1 @ ( k2_relat_1 @ X25 ) ) )
        = X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X30: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['51','56'])).

thf('58',plain,(
    ! [X30: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k7_relat_1 @ ( k8_relat_1 @ X17 @ X18 ) @ X19 )
        = ( k8_relat_1 @ X17 @ ( k7_relat_1 @ X18 @ X19 ) ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t140_relat_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k8_relat_1 @ X0 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X30: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k8_relat_1 @ X0 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ X0 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k2_relat_1 @ ( k8_relat_1 @ X14 @ X13 ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ X13 ) @ X14 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t119_relat_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('71',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k7_relat_1 @ X27 @ X26 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X26 ) @ X27 ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('72',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_relat_1 @ X12 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X30: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['70','76'])).

thf('78',plain,(
    ! [X30: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k3_xboole_0 @ X1 @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['68','69','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
        = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ ( k2_relat_1 @ ( k6_relat_1 @ X1 ) ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['50','80'])).

thf('82',plain,(
    ! [X23: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['29','36'])).

thf('84',plain,(
    ! [X30: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['81','82','83','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('88',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k2_relat_1 @ ( k8_relat_1 @ X14 @ X13 ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ X13 ) @ X14 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t119_relat_1])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ X0 ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X23: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('91',plain,(
    ! [X23: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('92',plain,(
    ! [X30: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('93',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['89','90','91','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k8_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k6_relat_1 @ X2 ) )
      = ( k8_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X2 ) ) ) ) ),
    inference(demod,[status(thm)],['20','21','22','23'])).

thf('95',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k2_relat_1 @ ( k8_relat_1 @ X14 @ X13 ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ X13 ) @ X14 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t119_relat_1])).

thf('96',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ ( k8_relat_1 @ ( k3_xboole_0 @ X2 @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ ( k8_relat_1 @ X2 @ ( k6_relat_1 @ X0 ) ) ) @ ( k3_xboole_0 @ X2 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X2 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['81','82','83','84'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['81','82','83','84'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('100',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X0 ) @ ( k3_xboole_0 @ X2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['96','97','98','99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['93','100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['86','103'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['5','17'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['81','82','83','84'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['86','103'])).

thf('109',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k7_relat_1 @ X27 @ X26 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X26 ) @ X27 ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t72_relat_1,axiom,(
    ! [A: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ A ) ) )).

thf('110',plain,(
    ! [X24: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ X24 ) )
      = ( k6_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t72_relat_1])).

thf(t54_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('111',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X21 @ X20 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X20 ) @ ( k4_relat_1 @ X21 ) ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X30: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k4_relat_1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['109','114'])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('117',plain,(
    ! [X24: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ X24 ) )
      = ( k6_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t72_relat_1])).

thf('118',plain,(
    ! [X30: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('119',plain,(
    ! [X30: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['115','116','117','118','119'])).

thf('121',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k8_relat_1 @ X16 @ X15 )
        = ( k5_relat_1 @ X15 @ ( k6_relat_1 @ X16 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['115','116','117','118','119'])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
        = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X30: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['120','125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['81','82','83','84'])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['86','103'])).

thf('130',plain,(
    ! [X23: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('131',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k2_relat_1 @ ( k8_relat_1 @ X14 @ X13 ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ X13 ) @ X14 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t119_relat_1])).

thf('132',plain,(
    ! [X25: $i] :
      ( ( ( k5_relat_1 @ X25 @ ( k6_relat_1 @ ( k2_relat_1 @ X25 ) ) )
        = X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('133',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k8_relat_1 @ X16 @ X15 )
        = ( k5_relat_1 @ X15 @ ( k6_relat_1 @ X16 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( ( k8_relat_1 @ ( k2_relat_1 @ X0 ) @ X0 )
        = X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k8_relat_1 @ ( k2_relat_1 @ X0 ) @ X0 )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['134'])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ ( k3_xboole_0 @ ( k2_relat_1 @ X1 ) @ X0 ) @ ( k8_relat_1 @ X0 @ X1 ) )
        = ( k8_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['131','135'])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('138',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k8_relat_1 @ ( k3_xboole_0 @ ( k2_relat_1 @ X1 ) @ X0 ) @ ( k8_relat_1 @ X0 @ X1 ) )
        = ( k8_relat_1 @ X0 @ X1 ) ) ) ),
    inference(clc,[status(thm)],['136','137'])).

thf('139',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['130','138'])).

thf('140',plain,(
    ! [X30: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('141',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('143',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['49','85','104','105','106','107','108','126','127','128','129','141','142'])).

thf('144',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('145',plain,(
    ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','143','144'])).

thf('146',plain,(
    $false ),
    inference(simplify,[status(thm)],['145'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8ibrgo8WlK
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:17:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.53/0.73  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.53/0.73  % Solved by: fo/fo7.sh
% 0.53/0.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.53/0.73  % done 510 iterations in 0.271s
% 0.53/0.73  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.53/0.73  % SZS output start Refutation
% 0.53/0.73  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.53/0.73  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.53/0.73  thf(sk_A_type, type, sk_A: $i).
% 0.53/0.73  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.53/0.73  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.53/0.73  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.53/0.73  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.53/0.73  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.53/0.73  thf(sk_B_type, type, sk_B: $i).
% 0.53/0.73  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.53/0.73  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.53/0.73  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.53/0.73  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.53/0.73  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.53/0.73  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.53/0.73  thf(t123_relat_1, axiom,
% 0.53/0.73    (![A:$i,B:$i]:
% 0.53/0.73     ( ( v1_relat_1 @ B ) =>
% 0.53/0.73       ( ( k8_relat_1 @ A @ B ) = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ))).
% 0.53/0.73  thf('0', plain,
% 0.53/0.73      (![X15 : $i, X16 : $i]:
% 0.53/0.73         (((k8_relat_1 @ X16 @ X15) = (k5_relat_1 @ X15 @ (k6_relat_1 @ X16)))
% 0.53/0.73          | ~ (v1_relat_1 @ X15))),
% 0.53/0.73      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.53/0.73  thf(t43_funct_1, conjecture,
% 0.53/0.73    (![A:$i,B:$i]:
% 0.53/0.73     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.53/0.73       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.53/0.73  thf(zf_stmt_0, negated_conjecture,
% 0.53/0.73    (~( ![A:$i,B:$i]:
% 0.53/0.73        ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.53/0.73          ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 0.53/0.73    inference('cnf.neg', [status(esa)], [t43_funct_1])).
% 0.53/0.73  thf('1', plain,
% 0.53/0.73      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A))
% 0.53/0.73         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('2', plain,
% 0.53/0.73      ((((k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B))
% 0.53/0.73          != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))
% 0.53/0.73        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_B)))),
% 0.53/0.73      inference('sup-', [status(thm)], ['0', '1'])).
% 0.53/0.73  thf(fc3_funct_1, axiom,
% 0.53/0.73    (![A:$i]:
% 0.53/0.73     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.53/0.73       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.53/0.73  thf('3', plain, (![X30 : $i]: (v1_relat_1 @ (k6_relat_1 @ X30))),
% 0.53/0.73      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.53/0.73  thf('4', plain,
% 0.53/0.73      (((k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B))
% 0.53/0.73         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.53/0.73      inference('demod', [status(thm)], ['2', '3'])).
% 0.53/0.73  thf(t17_xboole_1, axiom,
% 0.53/0.73    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.53/0.73  thf('5', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.53/0.73      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.53/0.73  thf(t71_relat_1, axiom,
% 0.53/0.73    (![A:$i]:
% 0.53/0.73     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.53/0.73       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.53/0.73  thf('6', plain, (![X22 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X22)) = (X22))),
% 0.53/0.73      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.53/0.73  thf(t97_relat_1, axiom,
% 0.53/0.73    (![A:$i,B:$i]:
% 0.53/0.73     ( ( v1_relat_1 @ B ) =>
% 0.53/0.73       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.53/0.73         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.53/0.73  thf('7', plain,
% 0.53/0.73      (![X28 : $i, X29 : $i]:
% 0.53/0.73         (~ (r1_tarski @ (k1_relat_1 @ X28) @ X29)
% 0.53/0.73          | ((k7_relat_1 @ X28 @ X29) = (X28))
% 0.53/0.73          | ~ (v1_relat_1 @ X28))),
% 0.53/0.73      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.53/0.73  thf('8', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         (~ (r1_tarski @ X0 @ X1)
% 0.53/0.73          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.53/0.73          | ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1) = (k6_relat_1 @ X0)))),
% 0.53/0.73      inference('sup-', [status(thm)], ['6', '7'])).
% 0.53/0.73  thf('9', plain, (![X30 : $i]: (v1_relat_1 @ (k6_relat_1 @ X30))),
% 0.53/0.73      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.53/0.73  thf('10', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         (~ (r1_tarski @ X0 @ X1)
% 0.53/0.73          | ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1) = (k6_relat_1 @ X0)))),
% 0.53/0.73      inference('demod', [status(thm)], ['8', '9'])).
% 0.53/0.73  thf('11', plain,
% 0.53/0.73      (![X15 : $i, X16 : $i]:
% 0.53/0.73         (((k8_relat_1 @ X16 @ X15) = (k5_relat_1 @ X15 @ (k6_relat_1 @ X16)))
% 0.53/0.73          | ~ (v1_relat_1 @ X15))),
% 0.53/0.73      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.53/0.73  thf(t94_relat_1, axiom,
% 0.53/0.73    (![A:$i,B:$i]:
% 0.53/0.73     ( ( v1_relat_1 @ B ) =>
% 0.53/0.73       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.53/0.73  thf('12', plain,
% 0.53/0.73      (![X26 : $i, X27 : $i]:
% 0.53/0.73         (((k7_relat_1 @ X27 @ X26) = (k5_relat_1 @ (k6_relat_1 @ X26) @ X27))
% 0.53/0.73          | ~ (v1_relat_1 @ X27))),
% 0.53/0.73      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.53/0.73  thf('13', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         (((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.53/0.73            = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.53/0.73          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.53/0.73          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.53/0.73      inference('sup+', [status(thm)], ['11', '12'])).
% 0.53/0.73  thf('14', plain, (![X30 : $i]: (v1_relat_1 @ (k6_relat_1 @ X30))),
% 0.53/0.73      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.53/0.73  thf('15', plain, (![X30 : $i]: (v1_relat_1 @ (k6_relat_1 @ X30))),
% 0.53/0.73      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.53/0.73  thf('16', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.53/0.73           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.53/0.73      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.53/0.73  thf('17', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         (~ (r1_tarski @ X0 @ X1)
% 0.53/0.73          | ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1)) = (k6_relat_1 @ X0)))),
% 0.53/0.73      inference('demod', [status(thm)], ['10', '16'])).
% 0.53/0.73  thf('18', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         ((k8_relat_1 @ (k3_xboole_0 @ X0 @ X1) @ (k6_relat_1 @ X0))
% 0.53/0.73           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.53/0.73      inference('sup-', [status(thm)], ['5', '17'])).
% 0.53/0.73  thf(t140_relat_1, axiom,
% 0.53/0.73    (![A:$i,B:$i,C:$i]:
% 0.53/0.73     ( ( v1_relat_1 @ C ) =>
% 0.53/0.73       ( ( k7_relat_1 @ ( k8_relat_1 @ A @ C ) @ B ) =
% 0.53/0.73         ( k8_relat_1 @ A @ ( k7_relat_1 @ C @ B ) ) ) ))).
% 0.53/0.73  thf('19', plain,
% 0.53/0.73      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.53/0.73         (((k7_relat_1 @ (k8_relat_1 @ X17 @ X18) @ X19)
% 0.53/0.73            = (k8_relat_1 @ X17 @ (k7_relat_1 @ X18 @ X19)))
% 0.53/0.73          | ~ (v1_relat_1 @ X18))),
% 0.53/0.73      inference('cnf', [status(esa)], [t140_relat_1])).
% 0.53/0.73  thf('20', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.73         (((k7_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ X2)
% 0.53/0.73            = (k8_relat_1 @ (k3_xboole_0 @ X1 @ X0) @ 
% 0.53/0.73               (k7_relat_1 @ (k6_relat_1 @ X1) @ X2)))
% 0.53/0.73          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.53/0.73      inference('sup+', [status(thm)], ['18', '19'])).
% 0.53/0.73  thf('21', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.53/0.73           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.53/0.73      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.53/0.73  thf('22', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.53/0.73           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.53/0.73      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.53/0.73  thf('23', plain, (![X30 : $i]: (v1_relat_1 @ (k6_relat_1 @ X30))),
% 0.53/0.73      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.53/0.73  thf('24', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.73         ((k8_relat_1 @ (k3_xboole_0 @ X1 @ X0) @ (k6_relat_1 @ X2))
% 0.53/0.73           = (k8_relat_1 @ (k3_xboole_0 @ X1 @ X0) @ 
% 0.53/0.73              (k8_relat_1 @ X1 @ (k6_relat_1 @ X2))))),
% 0.53/0.73      inference('demod', [status(thm)], ['20', '21', '22', '23'])).
% 0.53/0.73  thf(commutativity_k2_tarski, axiom,
% 0.53/0.73    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.53/0.73  thf('25', plain,
% 0.53/0.73      (![X2 : $i, X3 : $i]: ((k2_tarski @ X3 @ X2) = (k2_tarski @ X2 @ X3))),
% 0.53/0.73      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.53/0.73  thf(t12_setfam_1, axiom,
% 0.53/0.73    (![A:$i,B:$i]:
% 0.53/0.73     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.53/0.73  thf('26', plain,
% 0.53/0.73      (![X9 : $i, X10 : $i]:
% 0.53/0.73         ((k1_setfam_1 @ (k2_tarski @ X9 @ X10)) = (k3_xboole_0 @ X9 @ X10))),
% 0.53/0.73      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.53/0.73  thf('27', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.53/0.73      inference('sup+', [status(thm)], ['25', '26'])).
% 0.53/0.73  thf('28', plain,
% 0.53/0.73      (![X9 : $i, X10 : $i]:
% 0.53/0.73         ((k1_setfam_1 @ (k2_tarski @ X9 @ X10)) = (k3_xboole_0 @ X9 @ X10))),
% 0.53/0.73      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.53/0.73  thf('29', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.53/0.73      inference('sup+', [status(thm)], ['27', '28'])).
% 0.53/0.73  thf('30', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         ((k8_relat_1 @ (k3_xboole_0 @ X0 @ X1) @ (k6_relat_1 @ X0))
% 0.53/0.73           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.53/0.73      inference('sup-', [status(thm)], ['5', '17'])).
% 0.53/0.73  thf(t119_relat_1, axiom,
% 0.53/0.73    (![A:$i,B:$i]:
% 0.53/0.73     ( ( v1_relat_1 @ B ) =>
% 0.53/0.73       ( ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) ) =
% 0.53/0.73         ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.53/0.73  thf('31', plain,
% 0.53/0.73      (![X13 : $i, X14 : $i]:
% 0.53/0.73         (((k2_relat_1 @ (k8_relat_1 @ X14 @ X13))
% 0.53/0.73            = (k3_xboole_0 @ (k2_relat_1 @ X13) @ X14))
% 0.53/0.73          | ~ (v1_relat_1 @ X13))),
% 0.53/0.73      inference('cnf', [status(esa)], [t119_relat_1])).
% 0.53/0.73  thf('32', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         (((k2_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.53/0.73            = (k3_xboole_0 @ (k2_relat_1 @ (k6_relat_1 @ X1)) @ 
% 0.53/0.73               (k3_xboole_0 @ X1 @ X0)))
% 0.53/0.73          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.53/0.73      inference('sup+', [status(thm)], ['30', '31'])).
% 0.53/0.73  thf('33', plain, (![X23 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X23)) = (X23))),
% 0.53/0.73      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.53/0.73  thf('34', plain, (![X23 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X23)) = (X23))),
% 0.53/0.73      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.53/0.73  thf('35', plain, (![X30 : $i]: (v1_relat_1 @ (k6_relat_1 @ X30))),
% 0.53/0.73      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.53/0.73  thf('36', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         ((k3_xboole_0 @ X1 @ X0)
% 0.53/0.73           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.53/0.73      inference('demod', [status(thm)], ['32', '33', '34', '35'])).
% 0.53/0.73  thf('37', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         ((k3_xboole_0 @ X0 @ X1)
% 0.53/0.73           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.53/0.73      inference('sup+', [status(thm)], ['29', '36'])).
% 0.53/0.73  thf('38', plain,
% 0.53/0.73      (![X13 : $i, X14 : $i]:
% 0.53/0.73         (((k2_relat_1 @ (k8_relat_1 @ X14 @ X13))
% 0.53/0.73            = (k3_xboole_0 @ (k2_relat_1 @ X13) @ X14))
% 0.53/0.73          | ~ (v1_relat_1 @ X13))),
% 0.53/0.73      inference('cnf', [status(esa)], [t119_relat_1])).
% 0.53/0.73  thf(t80_relat_1, axiom,
% 0.53/0.73    (![A:$i]:
% 0.53/0.73     ( ( v1_relat_1 @ A ) =>
% 0.53/0.73       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 0.53/0.73  thf('39', plain,
% 0.53/0.73      (![X25 : $i]:
% 0.53/0.73         (((k5_relat_1 @ X25 @ (k6_relat_1 @ (k2_relat_1 @ X25))) = (X25))
% 0.53/0.73          | ~ (v1_relat_1 @ X25))),
% 0.53/0.73      inference('cnf', [status(esa)], [t80_relat_1])).
% 0.53/0.73  thf('40', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         (((k5_relat_1 @ (k8_relat_1 @ X0 @ X1) @ 
% 0.53/0.73            (k6_relat_1 @ (k3_xboole_0 @ (k2_relat_1 @ X1) @ X0)))
% 0.53/0.73            = (k8_relat_1 @ X0 @ X1))
% 0.53/0.73          | ~ (v1_relat_1 @ X1)
% 0.53/0.73          | ~ (v1_relat_1 @ (k8_relat_1 @ X0 @ X1)))),
% 0.53/0.73      inference('sup+', [status(thm)], ['38', '39'])).
% 0.53/0.73  thf('41', plain,
% 0.53/0.73      (![X15 : $i, X16 : $i]:
% 0.53/0.73         (((k8_relat_1 @ X16 @ X15) = (k5_relat_1 @ X15 @ (k6_relat_1 @ X16)))
% 0.53/0.73          | ~ (v1_relat_1 @ X15))),
% 0.53/0.73      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.53/0.73  thf(dt_k5_relat_1, axiom,
% 0.53/0.73    (![A:$i,B:$i]:
% 0.53/0.73     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.53/0.73       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.53/0.73  thf('42', plain,
% 0.53/0.73      (![X11 : $i, X12 : $i]:
% 0.53/0.73         (~ (v1_relat_1 @ X11)
% 0.53/0.73          | ~ (v1_relat_1 @ X12)
% 0.53/0.73          | (v1_relat_1 @ (k5_relat_1 @ X11 @ X12)))),
% 0.53/0.73      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.53/0.73  thf('43', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         ((v1_relat_1 @ (k8_relat_1 @ X1 @ X0))
% 0.53/0.73          | ~ (v1_relat_1 @ X0)
% 0.53/0.73          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.53/0.73          | ~ (v1_relat_1 @ X0))),
% 0.53/0.73      inference('sup+', [status(thm)], ['41', '42'])).
% 0.53/0.73  thf('44', plain, (![X30 : $i]: (v1_relat_1 @ (k6_relat_1 @ X30))),
% 0.53/0.73      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.53/0.73  thf('45', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         ((v1_relat_1 @ (k8_relat_1 @ X1 @ X0))
% 0.53/0.73          | ~ (v1_relat_1 @ X0)
% 0.53/0.73          | ~ (v1_relat_1 @ X0))),
% 0.53/0.73      inference('demod', [status(thm)], ['43', '44'])).
% 0.53/0.73  thf('46', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         (~ (v1_relat_1 @ X0) | (v1_relat_1 @ (k8_relat_1 @ X1 @ X0)))),
% 0.53/0.73      inference('simplify', [status(thm)], ['45'])).
% 0.53/0.73  thf('47', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         (~ (v1_relat_1 @ X1)
% 0.53/0.73          | ((k5_relat_1 @ (k8_relat_1 @ X0 @ X1) @ 
% 0.53/0.73              (k6_relat_1 @ (k3_xboole_0 @ (k2_relat_1 @ X1) @ X0)))
% 0.53/0.73              = (k8_relat_1 @ X0 @ X1)))),
% 0.53/0.73      inference('clc', [status(thm)], ['40', '46'])).
% 0.53/0.73  thf('48', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         (((k5_relat_1 @ 
% 0.53/0.73            (k8_relat_1 @ (k3_xboole_0 @ X0 @ (k2_relat_1 @ X1)) @ X1) @ 
% 0.53/0.73            (k6_relat_1 @ (k3_xboole_0 @ (k2_relat_1 @ X1) @ X0)))
% 0.53/0.73            = (k8_relat_1 @ (k3_xboole_0 @ X0 @ (k2_relat_1 @ X1)) @ X1))
% 0.53/0.73          | ~ (v1_relat_1 @ X1))),
% 0.53/0.73      inference('sup+', [status(thm)], ['37', '47'])).
% 0.53/0.73  thf('49', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         (((k5_relat_1 @ 
% 0.53/0.73            (k8_relat_1 @ 
% 0.53/0.73             (k3_xboole_0 @ X1 @ 
% 0.53/0.73              (k2_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))) @ 
% 0.53/0.73             (k6_relat_1 @ X0)) @ 
% 0.53/0.73            (k6_relat_1 @ 
% 0.53/0.73             (k3_xboole_0 @ 
% 0.53/0.73              (k2_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ X1)))
% 0.53/0.73            = (k8_relat_1 @ 
% 0.53/0.73               (k3_xboole_0 @ X1 @ 
% 0.53/0.73                (k2_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))) @ 
% 0.53/0.73               (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))
% 0.53/0.73          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 0.53/0.73      inference('sup+', [status(thm)], ['24', '48'])).
% 0.53/0.73  thf('50', plain,
% 0.53/0.73      (![X13 : $i, X14 : $i]:
% 0.53/0.73         (((k2_relat_1 @ (k8_relat_1 @ X14 @ X13))
% 0.53/0.73            = (k3_xboole_0 @ (k2_relat_1 @ X13) @ X14))
% 0.53/0.73          | ~ (v1_relat_1 @ X13))),
% 0.53/0.73      inference('cnf', [status(esa)], [t119_relat_1])).
% 0.53/0.73  thf('51', plain,
% 0.53/0.73      (![X15 : $i, X16 : $i]:
% 0.53/0.73         (((k8_relat_1 @ X16 @ X15) = (k5_relat_1 @ X15 @ (k6_relat_1 @ X16)))
% 0.53/0.73          | ~ (v1_relat_1 @ X15))),
% 0.53/0.73      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.53/0.73  thf('52', plain, (![X23 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X23)) = (X23))),
% 0.53/0.73      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.53/0.73  thf('53', plain,
% 0.53/0.73      (![X25 : $i]:
% 0.53/0.73         (((k5_relat_1 @ X25 @ (k6_relat_1 @ (k2_relat_1 @ X25))) = (X25))
% 0.53/0.73          | ~ (v1_relat_1 @ X25))),
% 0.53/0.73      inference('cnf', [status(esa)], [t80_relat_1])).
% 0.53/0.73  thf('54', plain,
% 0.53/0.73      (![X0 : $i]:
% 0.53/0.73         (((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 0.53/0.73            = (k6_relat_1 @ X0))
% 0.53/0.73          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.53/0.73      inference('sup+', [status(thm)], ['52', '53'])).
% 0.53/0.73  thf('55', plain, (![X30 : $i]: (v1_relat_1 @ (k6_relat_1 @ X30))),
% 0.53/0.73      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.53/0.73  thf('56', plain,
% 0.53/0.73      (![X0 : $i]:
% 0.53/0.73         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 0.53/0.73           = (k6_relat_1 @ X0))),
% 0.53/0.73      inference('demod', [status(thm)], ['54', '55'])).
% 0.53/0.73  thf('57', plain,
% 0.53/0.73      (![X0 : $i]:
% 0.53/0.73         (((k8_relat_1 @ X0 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0))
% 0.53/0.73          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.53/0.73      inference('sup+', [status(thm)], ['51', '56'])).
% 0.53/0.73  thf('58', plain, (![X30 : $i]: (v1_relat_1 @ (k6_relat_1 @ X30))),
% 0.53/0.73      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.53/0.73  thf('59', plain,
% 0.53/0.73      (![X0 : $i]: ((k8_relat_1 @ X0 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0))),
% 0.53/0.73      inference('demod', [status(thm)], ['57', '58'])).
% 0.53/0.73  thf('60', plain,
% 0.53/0.73      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.53/0.73         (((k7_relat_1 @ (k8_relat_1 @ X17 @ X18) @ X19)
% 0.53/0.73            = (k8_relat_1 @ X17 @ (k7_relat_1 @ X18 @ X19)))
% 0.53/0.73          | ~ (v1_relat_1 @ X18))),
% 0.53/0.73      inference('cnf', [status(esa)], [t140_relat_1])).
% 0.53/0.73  thf('61', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         (((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.53/0.73            = (k8_relat_1 @ X0 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1)))
% 0.53/0.73          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.53/0.73      inference('sup+', [status(thm)], ['59', '60'])).
% 0.53/0.73  thf('62', plain, (![X30 : $i]: (v1_relat_1 @ (k6_relat_1 @ X30))),
% 0.53/0.73      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.53/0.73  thf('63', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.53/0.73           = (k8_relat_1 @ X0 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1)))),
% 0.53/0.73      inference('demod', [status(thm)], ['61', '62'])).
% 0.53/0.73  thf('64', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.53/0.73           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.53/0.73      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.53/0.73  thf('65', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.53/0.73           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.53/0.73      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.53/0.73  thf('66', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 0.53/0.73           = (k8_relat_1 @ X0 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1))))),
% 0.53/0.73      inference('demod', [status(thm)], ['63', '64', '65'])).
% 0.53/0.73  thf('67', plain,
% 0.53/0.73      (![X13 : $i, X14 : $i]:
% 0.53/0.73         (((k2_relat_1 @ (k8_relat_1 @ X14 @ X13))
% 0.53/0.73            = (k3_xboole_0 @ (k2_relat_1 @ X13) @ X14))
% 0.53/0.73          | ~ (v1_relat_1 @ X13))),
% 0.53/0.73      inference('cnf', [status(esa)], [t119_relat_1])).
% 0.53/0.73  thf('68', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         (((k2_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.53/0.73            = (k3_xboole_0 @ 
% 0.53/0.73               (k2_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ X1))
% 0.53/0.73          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 0.53/0.73      inference('sup+', [status(thm)], ['66', '67'])).
% 0.53/0.73  thf('69', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.53/0.73      inference('sup+', [status(thm)], ['27', '28'])).
% 0.53/0.73  thf('70', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.53/0.73           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.53/0.73      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.53/0.73  thf('71', plain,
% 0.53/0.73      (![X26 : $i, X27 : $i]:
% 0.53/0.73         (((k7_relat_1 @ X27 @ X26) = (k5_relat_1 @ (k6_relat_1 @ X26) @ X27))
% 0.53/0.73          | ~ (v1_relat_1 @ X27))),
% 0.53/0.73      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.53/0.73  thf('72', plain,
% 0.53/0.73      (![X11 : $i, X12 : $i]:
% 0.53/0.73         (~ (v1_relat_1 @ X11)
% 0.53/0.73          | ~ (v1_relat_1 @ X12)
% 0.53/0.73          | (v1_relat_1 @ (k5_relat_1 @ X11 @ X12)))),
% 0.53/0.73      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.53/0.73  thf('73', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         ((v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.53/0.73          | ~ (v1_relat_1 @ X1)
% 0.53/0.73          | ~ (v1_relat_1 @ X1)
% 0.53/0.73          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.53/0.73      inference('sup+', [status(thm)], ['71', '72'])).
% 0.53/0.73  thf('74', plain, (![X30 : $i]: (v1_relat_1 @ (k6_relat_1 @ X30))),
% 0.53/0.73      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.53/0.73  thf('75', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         ((v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.53/0.73          | ~ (v1_relat_1 @ X1)
% 0.53/0.73          | ~ (v1_relat_1 @ X1))),
% 0.53/0.73      inference('demod', [status(thm)], ['73', '74'])).
% 0.53/0.73  thf('76', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         (~ (v1_relat_1 @ X1) | (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.53/0.73      inference('simplify', [status(thm)], ['75'])).
% 0.53/0.73  thf('77', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         ((v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.53/0.73          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.53/0.73      inference('sup+', [status(thm)], ['70', '76'])).
% 0.53/0.73  thf('78', plain, (![X30 : $i]: (v1_relat_1 @ (k6_relat_1 @ X30))),
% 0.53/0.73      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.53/0.73  thf('79', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.53/0.73      inference('demod', [status(thm)], ['77', '78'])).
% 0.53/0.73  thf('80', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         ((k2_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.53/0.73           = (k3_xboole_0 @ X1 @ 
% 0.53/0.73              (k2_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))))),
% 0.53/0.73      inference('demod', [status(thm)], ['68', '69', '79'])).
% 0.53/0.73  thf('81', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         (((k2_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 0.53/0.73            = (k3_xboole_0 @ X0 @ 
% 0.53/0.73               (k3_xboole_0 @ (k2_relat_1 @ (k6_relat_1 @ X1)) @ X0)))
% 0.53/0.73          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.53/0.73      inference('sup+', [status(thm)], ['50', '80'])).
% 0.53/0.73  thf('82', plain, (![X23 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X23)) = (X23))),
% 0.53/0.73      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.53/0.73  thf('83', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         ((k3_xboole_0 @ X0 @ X1)
% 0.53/0.73           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.53/0.73      inference('sup+', [status(thm)], ['29', '36'])).
% 0.53/0.73  thf('84', plain, (![X30 : $i]: (v1_relat_1 @ (k6_relat_1 @ X30))),
% 0.53/0.73      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.53/0.73  thf('85', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         ((k2_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 0.53/0.73           = (k3_xboole_0 @ X0 @ X1))),
% 0.53/0.73      inference('demod', [status(thm)], ['81', '82', '83', '84'])).
% 0.53/0.73  thf('86', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.53/0.73      inference('sup+', [status(thm)], ['27', '28'])).
% 0.53/0.73  thf('87', plain,
% 0.53/0.73      (![X0 : $i]: ((k8_relat_1 @ X0 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0))),
% 0.53/0.73      inference('demod', [status(thm)], ['57', '58'])).
% 0.53/0.73  thf('88', plain,
% 0.53/0.73      (![X13 : $i, X14 : $i]:
% 0.53/0.73         (((k2_relat_1 @ (k8_relat_1 @ X14 @ X13))
% 0.53/0.73            = (k3_xboole_0 @ (k2_relat_1 @ X13) @ X14))
% 0.53/0.73          | ~ (v1_relat_1 @ X13))),
% 0.53/0.73      inference('cnf', [status(esa)], [t119_relat_1])).
% 0.53/0.73  thf('89', plain,
% 0.53/0.73      (![X0 : $i]:
% 0.53/0.73         (((k2_relat_1 @ (k6_relat_1 @ X0))
% 0.53/0.73            = (k3_xboole_0 @ (k2_relat_1 @ (k6_relat_1 @ X0)) @ X0))
% 0.53/0.73          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.53/0.73      inference('sup+', [status(thm)], ['87', '88'])).
% 0.53/0.73  thf('90', plain, (![X23 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X23)) = (X23))),
% 0.53/0.73      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.53/0.73  thf('91', plain, (![X23 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X23)) = (X23))),
% 0.53/0.73      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.53/0.73  thf('92', plain, (![X30 : $i]: (v1_relat_1 @ (k6_relat_1 @ X30))),
% 0.53/0.73      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.53/0.73  thf('93', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.53/0.73      inference('demod', [status(thm)], ['89', '90', '91', '92'])).
% 0.53/0.73  thf('94', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.73         ((k8_relat_1 @ (k3_xboole_0 @ X1 @ X0) @ (k6_relat_1 @ X2))
% 0.53/0.73           = (k8_relat_1 @ (k3_xboole_0 @ X1 @ X0) @ 
% 0.53/0.73              (k8_relat_1 @ X1 @ (k6_relat_1 @ X2))))),
% 0.53/0.73      inference('demod', [status(thm)], ['20', '21', '22', '23'])).
% 0.53/0.73  thf('95', plain,
% 0.53/0.73      (![X13 : $i, X14 : $i]:
% 0.53/0.73         (((k2_relat_1 @ (k8_relat_1 @ X14 @ X13))
% 0.53/0.73            = (k3_xboole_0 @ (k2_relat_1 @ X13) @ X14))
% 0.53/0.73          | ~ (v1_relat_1 @ X13))),
% 0.53/0.73      inference('cnf', [status(esa)], [t119_relat_1])).
% 0.53/0.73  thf('96', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.73         (((k2_relat_1 @ 
% 0.53/0.73            (k8_relat_1 @ (k3_xboole_0 @ X2 @ X1) @ (k6_relat_1 @ X0)))
% 0.53/0.73            = (k3_xboole_0 @ 
% 0.53/0.73               (k2_relat_1 @ (k8_relat_1 @ X2 @ (k6_relat_1 @ X0))) @ 
% 0.53/0.73               (k3_xboole_0 @ X2 @ X1)))
% 0.53/0.73          | ~ (v1_relat_1 @ (k8_relat_1 @ X2 @ (k6_relat_1 @ X0))))),
% 0.53/0.73      inference('sup+', [status(thm)], ['94', '95'])).
% 0.53/0.73  thf('97', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         ((k2_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 0.53/0.73           = (k3_xboole_0 @ X0 @ X1))),
% 0.53/0.73      inference('demod', [status(thm)], ['81', '82', '83', '84'])).
% 0.53/0.73  thf('98', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         ((k2_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 0.53/0.73           = (k3_xboole_0 @ X0 @ X1))),
% 0.53/0.73      inference('demod', [status(thm)], ['81', '82', '83', '84'])).
% 0.53/0.73  thf('99', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.53/0.73      inference('demod', [status(thm)], ['77', '78'])).
% 0.53/0.73  thf('100', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.73         ((k3_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0)
% 0.53/0.73           = (k3_xboole_0 @ (k3_xboole_0 @ X2 @ X0) @ (k3_xboole_0 @ X2 @ X1)))),
% 0.53/0.73      inference('demod', [status(thm)], ['96', '97', '98', '99'])).
% 0.53/0.73  thf('101', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 0.53/0.73           = (k3_xboole_0 @ X1 @ X0))),
% 0.53/0.73      inference('sup+', [status(thm)], ['93', '100'])).
% 0.53/0.73  thf('102', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.53/0.73      inference('sup+', [status(thm)], ['27', '28'])).
% 0.53/0.73  thf('103', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.53/0.73           = (k3_xboole_0 @ X1 @ X0))),
% 0.53/0.73      inference('demod', [status(thm)], ['101', '102'])).
% 0.53/0.73  thf('104', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         ((k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.53/0.73           = (k3_xboole_0 @ X0 @ X1))),
% 0.53/0.73      inference('sup+', [status(thm)], ['86', '103'])).
% 0.53/0.73  thf('105', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         ((k8_relat_1 @ (k3_xboole_0 @ X0 @ X1) @ (k6_relat_1 @ X0))
% 0.53/0.73           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.53/0.73      inference('sup-', [status(thm)], ['5', '17'])).
% 0.53/0.73  thf('106', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         ((k2_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 0.53/0.73           = (k3_xboole_0 @ X0 @ X1))),
% 0.53/0.73      inference('demod', [status(thm)], ['81', '82', '83', '84'])).
% 0.53/0.73  thf('107', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.53/0.73      inference('sup+', [status(thm)], ['27', '28'])).
% 0.53/0.73  thf('108', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         ((k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.53/0.73           = (k3_xboole_0 @ X0 @ X1))),
% 0.53/0.73      inference('sup+', [status(thm)], ['86', '103'])).
% 0.53/0.73  thf('109', plain,
% 0.53/0.73      (![X26 : $i, X27 : $i]:
% 0.53/0.73         (((k7_relat_1 @ X27 @ X26) = (k5_relat_1 @ (k6_relat_1 @ X26) @ X27))
% 0.53/0.73          | ~ (v1_relat_1 @ X27))),
% 0.53/0.73      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.53/0.73  thf(t72_relat_1, axiom,
% 0.53/0.73    (![A:$i]: ( ( k4_relat_1 @ ( k6_relat_1 @ A ) ) = ( k6_relat_1 @ A ) ))).
% 0.53/0.73  thf('110', plain,
% 0.53/0.73      (![X24 : $i]: ((k4_relat_1 @ (k6_relat_1 @ X24)) = (k6_relat_1 @ X24))),
% 0.53/0.73      inference('cnf', [status(esa)], [t72_relat_1])).
% 0.53/0.73  thf(t54_relat_1, axiom,
% 0.53/0.73    (![A:$i]:
% 0.53/0.73     ( ( v1_relat_1 @ A ) =>
% 0.53/0.73       ( ![B:$i]:
% 0.53/0.73         ( ( v1_relat_1 @ B ) =>
% 0.53/0.73           ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.53/0.73             ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) ))).
% 0.53/0.73  thf('111', plain,
% 0.53/0.73      (![X20 : $i, X21 : $i]:
% 0.53/0.73         (~ (v1_relat_1 @ X20)
% 0.53/0.73          | ((k4_relat_1 @ (k5_relat_1 @ X21 @ X20))
% 0.53/0.73              = (k5_relat_1 @ (k4_relat_1 @ X20) @ (k4_relat_1 @ X21)))
% 0.53/0.73          | ~ (v1_relat_1 @ X21))),
% 0.53/0.73      inference('cnf', [status(esa)], [t54_relat_1])).
% 0.53/0.73  thf('112', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         (((k4_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.53/0.73            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k4_relat_1 @ X1)))
% 0.53/0.73          | ~ (v1_relat_1 @ X1)
% 0.53/0.73          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.53/0.73      inference('sup+', [status(thm)], ['110', '111'])).
% 0.53/0.73  thf('113', plain, (![X30 : $i]: (v1_relat_1 @ (k6_relat_1 @ X30))),
% 0.53/0.73      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.53/0.73  thf('114', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         (((k4_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.53/0.73            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k4_relat_1 @ X1)))
% 0.53/0.73          | ~ (v1_relat_1 @ X1))),
% 0.53/0.73      inference('demod', [status(thm)], ['112', '113'])).
% 0.53/0.73  thf('115', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         (((k4_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.53/0.73            = (k5_relat_1 @ (k6_relat_1 @ X1) @ 
% 0.53/0.73               (k4_relat_1 @ (k6_relat_1 @ X0))))
% 0.53/0.73          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.53/0.73          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.53/0.73      inference('sup+', [status(thm)], ['109', '114'])).
% 0.53/0.73  thf('116', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.53/0.73           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.53/0.73      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.53/0.73  thf('117', plain,
% 0.53/0.73      (![X24 : $i]: ((k4_relat_1 @ (k6_relat_1 @ X24)) = (k6_relat_1 @ X24))),
% 0.53/0.73      inference('cnf', [status(esa)], [t72_relat_1])).
% 0.53/0.73  thf('118', plain, (![X30 : $i]: (v1_relat_1 @ (k6_relat_1 @ X30))),
% 0.53/0.73      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.53/0.73  thf('119', plain, (![X30 : $i]: (v1_relat_1 @ (k6_relat_1 @ X30))),
% 0.53/0.73      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.53/0.73  thf('120', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         ((k4_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.53/0.73           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 0.53/0.73      inference('demod', [status(thm)], ['115', '116', '117', '118', '119'])).
% 0.53/0.73  thf('121', plain,
% 0.53/0.73      (![X15 : $i, X16 : $i]:
% 0.53/0.73         (((k8_relat_1 @ X16 @ X15) = (k5_relat_1 @ X15 @ (k6_relat_1 @ X16)))
% 0.53/0.73          | ~ (v1_relat_1 @ X15))),
% 0.53/0.73      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.53/0.73  thf('122', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         ((k4_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.53/0.73           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 0.53/0.73      inference('demod', [status(thm)], ['115', '116', '117', '118', '119'])).
% 0.53/0.73  thf('123', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         (((k4_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 0.53/0.73            = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.53/0.73          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.53/0.73      inference('sup+', [status(thm)], ['121', '122'])).
% 0.53/0.73  thf('124', plain, (![X30 : $i]: (v1_relat_1 @ (k6_relat_1 @ X30))),
% 0.53/0.73      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.53/0.73  thf('125', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         ((k4_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 0.53/0.73           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.53/0.73      inference('demod', [status(thm)], ['123', '124'])).
% 0.53/0.73  thf('126', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 0.53/0.73           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 0.53/0.73      inference('demod', [status(thm)], ['120', '125'])).
% 0.53/0.73  thf('127', plain,
% 0.53/0.73      (![X0 : $i]: ((k8_relat_1 @ X0 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0))),
% 0.53/0.73      inference('demod', [status(thm)], ['57', '58'])).
% 0.53/0.73  thf('128', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         ((k2_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 0.53/0.73           = (k3_xboole_0 @ X0 @ X1))),
% 0.53/0.73      inference('demod', [status(thm)], ['81', '82', '83', '84'])).
% 0.53/0.73  thf('129', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         ((k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.53/0.73           = (k3_xboole_0 @ X0 @ X1))),
% 0.53/0.73      inference('sup+', [status(thm)], ['86', '103'])).
% 0.53/0.73  thf('130', plain, (![X23 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X23)) = (X23))),
% 0.53/0.73      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.53/0.73  thf('131', plain,
% 0.53/0.73      (![X13 : $i, X14 : $i]:
% 0.53/0.73         (((k2_relat_1 @ (k8_relat_1 @ X14 @ X13))
% 0.53/0.73            = (k3_xboole_0 @ (k2_relat_1 @ X13) @ X14))
% 0.53/0.73          | ~ (v1_relat_1 @ X13))),
% 0.53/0.73      inference('cnf', [status(esa)], [t119_relat_1])).
% 0.53/0.73  thf('132', plain,
% 0.53/0.73      (![X25 : $i]:
% 0.53/0.73         (((k5_relat_1 @ X25 @ (k6_relat_1 @ (k2_relat_1 @ X25))) = (X25))
% 0.53/0.73          | ~ (v1_relat_1 @ X25))),
% 0.53/0.73      inference('cnf', [status(esa)], [t80_relat_1])).
% 0.53/0.73  thf('133', plain,
% 0.53/0.73      (![X15 : $i, X16 : $i]:
% 0.53/0.73         (((k8_relat_1 @ X16 @ X15) = (k5_relat_1 @ X15 @ (k6_relat_1 @ X16)))
% 0.53/0.73          | ~ (v1_relat_1 @ X15))),
% 0.53/0.73      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.53/0.73  thf('134', plain,
% 0.53/0.73      (![X0 : $i]:
% 0.53/0.73         (((k8_relat_1 @ (k2_relat_1 @ X0) @ X0) = (X0))
% 0.53/0.73          | ~ (v1_relat_1 @ X0)
% 0.53/0.73          | ~ (v1_relat_1 @ X0))),
% 0.53/0.73      inference('sup+', [status(thm)], ['132', '133'])).
% 0.53/0.73  thf('135', plain,
% 0.53/0.73      (![X0 : $i]:
% 0.53/0.73         (~ (v1_relat_1 @ X0) | ((k8_relat_1 @ (k2_relat_1 @ X0) @ X0) = (X0)))),
% 0.53/0.73      inference('simplify', [status(thm)], ['134'])).
% 0.53/0.73  thf('136', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         (((k8_relat_1 @ (k3_xboole_0 @ (k2_relat_1 @ X1) @ X0) @ 
% 0.53/0.73            (k8_relat_1 @ X0 @ X1)) = (k8_relat_1 @ X0 @ X1))
% 0.53/0.73          | ~ (v1_relat_1 @ X1)
% 0.53/0.73          | ~ (v1_relat_1 @ (k8_relat_1 @ X0 @ X1)))),
% 0.53/0.73      inference('sup+', [status(thm)], ['131', '135'])).
% 0.53/0.73  thf('137', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         (~ (v1_relat_1 @ X0) | (v1_relat_1 @ (k8_relat_1 @ X1 @ X0)))),
% 0.53/0.73      inference('simplify', [status(thm)], ['45'])).
% 0.53/0.73  thf('138', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         (~ (v1_relat_1 @ X1)
% 0.53/0.73          | ((k8_relat_1 @ (k3_xboole_0 @ (k2_relat_1 @ X1) @ X0) @ 
% 0.53/0.73              (k8_relat_1 @ X0 @ X1)) = (k8_relat_1 @ X0 @ X1)))),
% 0.53/0.73      inference('clc', [status(thm)], ['136', '137'])).
% 0.53/0.73  thf('139', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         (((k8_relat_1 @ (k3_xboole_0 @ X0 @ X1) @ 
% 0.53/0.73            (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.53/0.73            = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.53/0.73          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.53/0.73      inference('sup+', [status(thm)], ['130', '138'])).
% 0.53/0.73  thf('140', plain, (![X30 : $i]: (v1_relat_1 @ (k6_relat_1 @ X30))),
% 0.53/0.73      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.53/0.73  thf('141', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         ((k8_relat_1 @ (k3_xboole_0 @ X0 @ X1) @ 
% 0.53/0.73           (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.53/0.73           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.53/0.73      inference('demod', [status(thm)], ['139', '140'])).
% 0.53/0.73  thf('142', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.53/0.73      inference('demod', [status(thm)], ['77', '78'])).
% 0.53/0.73  thf('143', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         ((k6_relat_1 @ (k3_xboole_0 @ X0 @ X1))
% 0.53/0.73           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.53/0.73      inference('demod', [status(thm)],
% 0.53/0.73                ['49', '85', '104', '105', '106', '107', '108', '126', '127', 
% 0.53/0.73                 '128', '129', '141', '142'])).
% 0.53/0.73  thf('144', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.53/0.73      inference('sup+', [status(thm)], ['27', '28'])).
% 0.53/0.73  thf('145', plain,
% 0.53/0.73      (((k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B))
% 0.53/0.73         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.53/0.73      inference('demod', [status(thm)], ['4', '143', '144'])).
% 0.53/0.73  thf('146', plain, ($false), inference('simplify', [status(thm)], ['145'])).
% 0.53/0.73  
% 0.53/0.73  % SZS output end Refutation
% 0.53/0.73  
% 0.53/0.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
