%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.l2MNf3mkJs

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:25 EST 2020

% Result     : Theorem 0.86s
% Output     : Refutation 0.86s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 126 expanded)
%              Number of leaves         :   28 (  50 expanded)
%              Depth                    :   20
%              Number of atoms          :  661 (1007 expanded)
%              Number of equality atoms :   35 (  61 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_wellord1_type,type,(
    k2_wellord1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(t29_wellord1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A )
          = ( k2_wellord1 @ C @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( r1_tarski @ A @ B )
         => ( ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A )
            = ( k2_wellord1 @ C @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t29_wellord1])).

thf('0',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t20_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ B @ A ) ) @ ( k3_relat_1 @ B ) )
        & ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ B @ A ) ) @ A ) ) ) )).

thf('1',plain,(
    ! [X22: $i,X23: $i] :
      ( ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ X22 @ X23 ) ) @ X23 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t20_wellord1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) ) @ sk_B )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('5',plain,(
    ! [X13: $i] :
      ( ( ( k3_relat_1 @ X13 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X13 ) @ ( k2_relat_1 @ X13 ) ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('6',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_tarski @ X6 @ X5 )
      = ( k2_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X9 @ X10 ) )
      = ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X9 @ X10 ) )
      = ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X13: $i] :
      ( ( ( k3_relat_1 @ X13 )
        = ( k2_xboole_0 @ ( k2_relat_1 @ X13 ) @ ( k1_relat_1 @ X13 ) ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(demod,[status(thm)],['5','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('13',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ X3 @ ( k2_xboole_0 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k3_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) ) @ sk_B )
      | ~ ( v1_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['4','17'])).

thf(dt_k2_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k2_wellord1 @ A @ B ) ) ) )).

thf('19',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ( v1_relat_1 @ ( k2_wellord1 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_wellord1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) ) @ sk_B )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['18','19'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('21',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X11 ) @ X12 )
      | ( v4_relat_1 @ X11 @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) )
      | ( v4_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ( v1_relat_1 @ ( k2_wellord1 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_wellord1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) @ sk_B )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('25',plain,(
    ! [X16: $i,X17: $i] :
      ( ( X16
        = ( k7_relat_1 @ X16 @ X17 ) )
      | ~ ( v4_relat_1 @ X16 @ X17 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) )
      | ( ( k2_wellord1 @ X0 @ sk_A )
        = ( k7_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ( v1_relat_1 @ ( k2_wellord1 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_wellord1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( k2_wellord1 @ X0 @ sk_A )
        = ( k7_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf(t27_wellord1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k2_wellord1 @ ( k2_wellord1 @ C @ A ) @ B )
        = ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) ) ) )).

thf('29',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k2_wellord1 @ ( k2_wellord1 @ X24 @ X26 ) @ X25 )
        = ( k2_wellord1 @ ( k2_wellord1 @ X24 @ X25 ) @ X26 ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t27_wellord1])).

thf('30',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X22: $i,X23: $i] :
      ( ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ X22 @ X23 ) ) @ X23 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t20_wellord1])).

thf('32',plain,(
    ! [X13: $i] :
      ( ( ( k3_relat_1 @ X13 )
        = ( k2_xboole_0 @ ( k2_relat_1 @ X13 ) @ ( k1_relat_1 @ X13 ) ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(demod,[status(thm)],['5','10'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k3_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ( v1_relat_1 @ ( k2_wellord1 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_wellord1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) ) @ sk_B )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','39'])).

thf(t125_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k8_relat_1 @ A @ B )
          = B ) ) ) )).

thf('41',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X14 ) @ X15 )
      | ( ( k8_relat_1 @ X15 @ X14 )
        = X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t125_relat_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) )
      | ( ( k8_relat_1 @ sk_B @ ( k2_wellord1 @ X0 @ sk_A ) )
        = ( k2_wellord1 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ( v1_relat_1 @ ( k2_wellord1 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_wellord1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( ( k8_relat_1 @ sk_B @ ( k2_wellord1 @ X0 @ sk_A ) )
        = ( k2_wellord1 @ X0 @ sk_A ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['42','43'])).

thf(t17_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_wellord1 @ B @ A )
        = ( k7_relat_1 @ ( k8_relat_1 @ A @ B ) @ A ) ) ) )).

thf('45',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k2_wellord1 @ X21 @ X20 )
        = ( k7_relat_1 @ ( k8_relat_1 @ X20 @ X21 ) @ X20 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t17_wellord1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( k2_wellord1 @ ( k2_wellord1 @ X0 @ sk_A ) @ sk_B )
        = ( k7_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ( v1_relat_1 @ ( k2_wellord1 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_wellord1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_wellord1 @ ( k2_wellord1 @ X0 @ sk_A ) @ sk_B )
        = ( k7_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( ( k2_wellord1 @ ( k2_wellord1 @ X0 @ sk_B ) @ sk_A )
        = ( k7_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_wellord1 @ ( k2_wellord1 @ X0 @ sk_B ) @ sk_A )
        = ( k7_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ( k2_wellord1 @ ( k2_wellord1 @ sk_C @ sk_B ) @ sk_A )
 != ( k2_wellord1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( ( k7_relat_1 @ ( k2_wellord1 @ sk_C @ sk_A ) @ sk_B )
     != ( k2_wellord1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ( k7_relat_1 @ ( k2_wellord1 @ sk_C @ sk_A ) @ sk_B )
 != ( k2_wellord1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( ( k2_wellord1 @ sk_C @ sk_A )
     != ( k2_wellord1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['28','54'])).

thf('56',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ( k2_wellord1 @ sk_C @ sk_A )
 != ( k2_wellord1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    $false ),
    inference(simplify,[status(thm)],['57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.l2MNf3mkJs
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:47:50 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.86/1.07  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.86/1.07  % Solved by: fo/fo7.sh
% 0.86/1.07  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.86/1.07  % done 810 iterations in 0.627s
% 0.86/1.07  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.86/1.07  % SZS output start Refutation
% 0.86/1.07  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.86/1.07  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.86/1.07  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.86/1.07  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.86/1.07  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.86/1.07  thf(sk_A_type, type, sk_A: $i).
% 0.86/1.07  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.86/1.07  thf(sk_C_type, type, sk_C: $i).
% 0.86/1.07  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.86/1.07  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.86/1.07  thf(k2_wellord1_type, type, k2_wellord1: $i > $i > $i).
% 0.86/1.07  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.86/1.07  thf(sk_B_type, type, sk_B: $i).
% 0.86/1.07  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.86/1.07  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.86/1.07  thf(t29_wellord1, conjecture,
% 0.86/1.07    (![A:$i,B:$i,C:$i]:
% 0.86/1.07     ( ( v1_relat_1 @ C ) =>
% 0.86/1.07       ( ( r1_tarski @ A @ B ) =>
% 0.86/1.07         ( ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) =
% 0.86/1.07           ( k2_wellord1 @ C @ A ) ) ) ))).
% 0.86/1.07  thf(zf_stmt_0, negated_conjecture,
% 0.86/1.07    (~( ![A:$i,B:$i,C:$i]:
% 0.86/1.07        ( ( v1_relat_1 @ C ) =>
% 0.86/1.07          ( ( r1_tarski @ A @ B ) =>
% 0.86/1.07            ( ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) =
% 0.86/1.07              ( k2_wellord1 @ C @ A ) ) ) ) )),
% 0.86/1.07    inference('cnf.neg', [status(esa)], [t29_wellord1])).
% 0.86/1.07  thf('0', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.86/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.07  thf(t20_wellord1, axiom,
% 0.86/1.07    (![A:$i,B:$i]:
% 0.86/1.07     ( ( v1_relat_1 @ B ) =>
% 0.86/1.07       ( ( r1_tarski @
% 0.86/1.07           ( k3_relat_1 @ ( k2_wellord1 @ B @ A ) ) @ ( k3_relat_1 @ B ) ) & 
% 0.86/1.07         ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ B @ A ) ) @ A ) ) ))).
% 0.86/1.07  thf('1', plain,
% 0.86/1.07      (![X22 : $i, X23 : $i]:
% 0.86/1.07         ((r1_tarski @ (k3_relat_1 @ (k2_wellord1 @ X22 @ X23)) @ X23)
% 0.86/1.07          | ~ (v1_relat_1 @ X22))),
% 0.86/1.07      inference('cnf', [status(esa)], [t20_wellord1])).
% 0.86/1.07  thf(t1_xboole_1, axiom,
% 0.86/1.07    (![A:$i,B:$i,C:$i]:
% 0.86/1.07     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.86/1.07       ( r1_tarski @ A @ C ) ))).
% 0.86/1.07  thf('2', plain,
% 0.86/1.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.86/1.07         (~ (r1_tarski @ X0 @ X1)
% 0.86/1.07          | ~ (r1_tarski @ X1 @ X2)
% 0.86/1.07          | (r1_tarski @ X0 @ X2))),
% 0.86/1.07      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.86/1.07  thf('3', plain,
% 0.86/1.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.86/1.07         (~ (v1_relat_1 @ X1)
% 0.86/1.07          | (r1_tarski @ (k3_relat_1 @ (k2_wellord1 @ X1 @ X0)) @ X2)
% 0.86/1.07          | ~ (r1_tarski @ X0 @ X2))),
% 0.86/1.07      inference('sup-', [status(thm)], ['1', '2'])).
% 0.86/1.07  thf('4', plain,
% 0.86/1.07      (![X0 : $i]:
% 0.86/1.07         ((r1_tarski @ (k3_relat_1 @ (k2_wellord1 @ X0 @ sk_A)) @ sk_B)
% 0.86/1.07          | ~ (v1_relat_1 @ X0))),
% 0.86/1.07      inference('sup-', [status(thm)], ['0', '3'])).
% 0.86/1.07  thf(d6_relat_1, axiom,
% 0.86/1.07    (![A:$i]:
% 0.86/1.07     ( ( v1_relat_1 @ A ) =>
% 0.86/1.07       ( ( k3_relat_1 @ A ) =
% 0.86/1.07         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.86/1.07  thf('5', plain,
% 0.86/1.07      (![X13 : $i]:
% 0.86/1.07         (((k3_relat_1 @ X13)
% 0.86/1.07            = (k2_xboole_0 @ (k1_relat_1 @ X13) @ (k2_relat_1 @ X13)))
% 0.86/1.07          | ~ (v1_relat_1 @ X13))),
% 0.86/1.07      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.86/1.07  thf(commutativity_k2_tarski, axiom,
% 0.86/1.07    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.86/1.07  thf('6', plain,
% 0.86/1.07      (![X5 : $i, X6 : $i]: ((k2_tarski @ X6 @ X5) = (k2_tarski @ X5 @ X6))),
% 0.86/1.07      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.86/1.07  thf(l51_zfmisc_1, axiom,
% 0.86/1.07    (![A:$i,B:$i]:
% 0.86/1.07     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.86/1.07  thf('7', plain,
% 0.86/1.07      (![X9 : $i, X10 : $i]:
% 0.86/1.07         ((k3_tarski @ (k2_tarski @ X9 @ X10)) = (k2_xboole_0 @ X9 @ X10))),
% 0.86/1.07      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.86/1.07  thf('8', plain,
% 0.86/1.07      (![X0 : $i, X1 : $i]:
% 0.86/1.07         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.86/1.07      inference('sup+', [status(thm)], ['6', '7'])).
% 0.86/1.07  thf('9', plain,
% 0.86/1.07      (![X9 : $i, X10 : $i]:
% 0.86/1.07         ((k3_tarski @ (k2_tarski @ X9 @ X10)) = (k2_xboole_0 @ X9 @ X10))),
% 0.86/1.07      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.86/1.07  thf('10', plain,
% 0.86/1.07      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.86/1.07      inference('sup+', [status(thm)], ['8', '9'])).
% 0.86/1.07  thf('11', plain,
% 0.86/1.07      (![X13 : $i]:
% 0.86/1.07         (((k3_relat_1 @ X13)
% 0.86/1.07            = (k2_xboole_0 @ (k2_relat_1 @ X13) @ (k1_relat_1 @ X13)))
% 0.86/1.07          | ~ (v1_relat_1 @ X13))),
% 0.86/1.07      inference('demod', [status(thm)], ['5', '10'])).
% 0.86/1.07  thf('12', plain,
% 0.86/1.07      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.86/1.07      inference('sup+', [status(thm)], ['8', '9'])).
% 0.86/1.07  thf(t7_xboole_1, axiom,
% 0.86/1.07    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.86/1.07  thf('13', plain,
% 0.86/1.07      (![X3 : $i, X4 : $i]: (r1_tarski @ X3 @ (k2_xboole_0 @ X3 @ X4))),
% 0.86/1.07      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.86/1.07  thf('14', plain,
% 0.86/1.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.86/1.07         (~ (r1_tarski @ X0 @ X1)
% 0.86/1.07          | ~ (r1_tarski @ X1 @ X2)
% 0.86/1.07          | (r1_tarski @ X0 @ X2))),
% 0.86/1.07      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.86/1.07  thf('15', plain,
% 0.86/1.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.86/1.07         ((r1_tarski @ X1 @ X2) | ~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 0.86/1.07      inference('sup-', [status(thm)], ['13', '14'])).
% 0.86/1.07  thf('16', plain,
% 0.86/1.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.86/1.07         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X2) | (r1_tarski @ X0 @ X2))),
% 0.86/1.07      inference('sup-', [status(thm)], ['12', '15'])).
% 0.86/1.07  thf('17', plain,
% 0.86/1.07      (![X0 : $i, X1 : $i]:
% 0.86/1.07         (~ (r1_tarski @ (k3_relat_1 @ X0) @ X1)
% 0.86/1.07          | ~ (v1_relat_1 @ X0)
% 0.86/1.07          | (r1_tarski @ (k1_relat_1 @ X0) @ X1))),
% 0.86/1.07      inference('sup-', [status(thm)], ['11', '16'])).
% 0.86/1.07  thf('18', plain,
% 0.86/1.07      (![X0 : $i]:
% 0.86/1.07         (~ (v1_relat_1 @ X0)
% 0.86/1.07          | (r1_tarski @ (k1_relat_1 @ (k2_wellord1 @ X0 @ sk_A)) @ sk_B)
% 0.86/1.07          | ~ (v1_relat_1 @ (k2_wellord1 @ X0 @ sk_A)))),
% 0.86/1.07      inference('sup-', [status(thm)], ['4', '17'])).
% 0.86/1.07  thf(dt_k2_wellord1, axiom,
% 0.86/1.07    (![A:$i,B:$i]:
% 0.86/1.07     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k2_wellord1 @ A @ B ) ) ))).
% 0.86/1.07  thf('19', plain,
% 0.86/1.07      (![X18 : $i, X19 : $i]:
% 0.86/1.07         (~ (v1_relat_1 @ X18) | (v1_relat_1 @ (k2_wellord1 @ X18 @ X19)))),
% 0.86/1.07      inference('cnf', [status(esa)], [dt_k2_wellord1])).
% 0.86/1.07  thf('20', plain,
% 0.86/1.07      (![X0 : $i]:
% 0.86/1.07         ((r1_tarski @ (k1_relat_1 @ (k2_wellord1 @ X0 @ sk_A)) @ sk_B)
% 0.86/1.07          | ~ (v1_relat_1 @ X0))),
% 0.86/1.07      inference('clc', [status(thm)], ['18', '19'])).
% 0.86/1.07  thf(d18_relat_1, axiom,
% 0.86/1.07    (![A:$i,B:$i]:
% 0.86/1.07     ( ( v1_relat_1 @ B ) =>
% 0.86/1.07       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.86/1.07  thf('21', plain,
% 0.86/1.07      (![X11 : $i, X12 : $i]:
% 0.86/1.07         (~ (r1_tarski @ (k1_relat_1 @ X11) @ X12)
% 0.86/1.07          | (v4_relat_1 @ X11 @ X12)
% 0.86/1.07          | ~ (v1_relat_1 @ X11))),
% 0.86/1.07      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.86/1.07  thf('22', plain,
% 0.86/1.07      (![X0 : $i]:
% 0.86/1.07         (~ (v1_relat_1 @ X0)
% 0.86/1.07          | ~ (v1_relat_1 @ (k2_wellord1 @ X0 @ sk_A))
% 0.86/1.07          | (v4_relat_1 @ (k2_wellord1 @ X0 @ sk_A) @ sk_B))),
% 0.86/1.07      inference('sup-', [status(thm)], ['20', '21'])).
% 0.86/1.07  thf('23', plain,
% 0.86/1.07      (![X18 : $i, X19 : $i]:
% 0.86/1.07         (~ (v1_relat_1 @ X18) | (v1_relat_1 @ (k2_wellord1 @ X18 @ X19)))),
% 0.86/1.07      inference('cnf', [status(esa)], [dt_k2_wellord1])).
% 0.86/1.07  thf('24', plain,
% 0.86/1.07      (![X0 : $i]:
% 0.86/1.07         ((v4_relat_1 @ (k2_wellord1 @ X0 @ sk_A) @ sk_B) | ~ (v1_relat_1 @ X0))),
% 0.86/1.07      inference('clc', [status(thm)], ['22', '23'])).
% 0.86/1.07  thf(t209_relat_1, axiom,
% 0.86/1.07    (![A:$i,B:$i]:
% 0.86/1.07     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.86/1.07       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.86/1.07  thf('25', plain,
% 0.86/1.07      (![X16 : $i, X17 : $i]:
% 0.86/1.07         (((X16) = (k7_relat_1 @ X16 @ X17))
% 0.86/1.07          | ~ (v4_relat_1 @ X16 @ X17)
% 0.86/1.07          | ~ (v1_relat_1 @ X16))),
% 0.86/1.07      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.86/1.07  thf('26', plain,
% 0.86/1.07      (![X0 : $i]:
% 0.86/1.07         (~ (v1_relat_1 @ X0)
% 0.86/1.07          | ~ (v1_relat_1 @ (k2_wellord1 @ X0 @ sk_A))
% 0.86/1.07          | ((k2_wellord1 @ X0 @ sk_A)
% 0.86/1.07              = (k7_relat_1 @ (k2_wellord1 @ X0 @ sk_A) @ sk_B)))),
% 0.86/1.07      inference('sup-', [status(thm)], ['24', '25'])).
% 0.86/1.07  thf('27', plain,
% 0.86/1.07      (![X18 : $i, X19 : $i]:
% 0.86/1.07         (~ (v1_relat_1 @ X18) | (v1_relat_1 @ (k2_wellord1 @ X18 @ X19)))),
% 0.86/1.07      inference('cnf', [status(esa)], [dt_k2_wellord1])).
% 0.86/1.07  thf('28', plain,
% 0.86/1.07      (![X0 : $i]:
% 0.86/1.07         (((k2_wellord1 @ X0 @ sk_A)
% 0.86/1.07            = (k7_relat_1 @ (k2_wellord1 @ X0 @ sk_A) @ sk_B))
% 0.86/1.07          | ~ (v1_relat_1 @ X0))),
% 0.86/1.07      inference('clc', [status(thm)], ['26', '27'])).
% 0.86/1.07  thf(t27_wellord1, axiom,
% 0.86/1.07    (![A:$i,B:$i,C:$i]:
% 0.86/1.07     ( ( v1_relat_1 @ C ) =>
% 0.86/1.07       ( ( k2_wellord1 @ ( k2_wellord1 @ C @ A ) @ B ) =
% 0.86/1.07         ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) ) ))).
% 0.86/1.07  thf('29', plain,
% 0.86/1.07      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.86/1.07         (((k2_wellord1 @ (k2_wellord1 @ X24 @ X26) @ X25)
% 0.86/1.07            = (k2_wellord1 @ (k2_wellord1 @ X24 @ X25) @ X26))
% 0.86/1.07          | ~ (v1_relat_1 @ X24))),
% 0.86/1.07      inference('cnf', [status(esa)], [t27_wellord1])).
% 0.86/1.07  thf('30', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.86/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.07  thf('31', plain,
% 0.86/1.07      (![X22 : $i, X23 : $i]:
% 0.86/1.07         ((r1_tarski @ (k3_relat_1 @ (k2_wellord1 @ X22 @ X23)) @ X23)
% 0.86/1.07          | ~ (v1_relat_1 @ X22))),
% 0.86/1.07      inference('cnf', [status(esa)], [t20_wellord1])).
% 0.86/1.07  thf('32', plain,
% 0.86/1.07      (![X13 : $i]:
% 0.86/1.07         (((k3_relat_1 @ X13)
% 0.86/1.07            = (k2_xboole_0 @ (k2_relat_1 @ X13) @ (k1_relat_1 @ X13)))
% 0.86/1.07          | ~ (v1_relat_1 @ X13))),
% 0.86/1.07      inference('demod', [status(thm)], ['5', '10'])).
% 0.86/1.07  thf('33', plain,
% 0.86/1.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.86/1.07         ((r1_tarski @ X1 @ X2) | ~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 0.86/1.07      inference('sup-', [status(thm)], ['13', '14'])).
% 0.86/1.07  thf('34', plain,
% 0.86/1.07      (![X0 : $i, X1 : $i]:
% 0.86/1.07         (~ (r1_tarski @ (k3_relat_1 @ X0) @ X1)
% 0.86/1.07          | ~ (v1_relat_1 @ X0)
% 0.86/1.07          | (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 0.86/1.07      inference('sup-', [status(thm)], ['32', '33'])).
% 0.86/1.07  thf('35', plain,
% 0.86/1.07      (![X0 : $i, X1 : $i]:
% 0.86/1.07         (~ (v1_relat_1 @ X1)
% 0.86/1.07          | (r1_tarski @ (k2_relat_1 @ (k2_wellord1 @ X1 @ X0)) @ X0)
% 0.86/1.07          | ~ (v1_relat_1 @ (k2_wellord1 @ X1 @ X0)))),
% 0.86/1.07      inference('sup-', [status(thm)], ['31', '34'])).
% 0.86/1.07  thf('36', plain,
% 0.86/1.07      (![X18 : $i, X19 : $i]:
% 0.86/1.07         (~ (v1_relat_1 @ X18) | (v1_relat_1 @ (k2_wellord1 @ X18 @ X19)))),
% 0.86/1.07      inference('cnf', [status(esa)], [dt_k2_wellord1])).
% 0.86/1.07  thf('37', plain,
% 0.86/1.07      (![X0 : $i, X1 : $i]:
% 0.86/1.07         ((r1_tarski @ (k2_relat_1 @ (k2_wellord1 @ X1 @ X0)) @ X0)
% 0.86/1.07          | ~ (v1_relat_1 @ X1))),
% 0.86/1.07      inference('clc', [status(thm)], ['35', '36'])).
% 0.86/1.07  thf('38', plain,
% 0.86/1.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.86/1.07         (~ (r1_tarski @ X0 @ X1)
% 0.86/1.07          | ~ (r1_tarski @ X1 @ X2)
% 0.86/1.07          | (r1_tarski @ X0 @ X2))),
% 0.86/1.07      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.86/1.07  thf('39', plain,
% 0.86/1.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.86/1.07         (~ (v1_relat_1 @ X1)
% 0.86/1.07          | (r1_tarski @ (k2_relat_1 @ (k2_wellord1 @ X1 @ X0)) @ X2)
% 0.86/1.07          | ~ (r1_tarski @ X0 @ X2))),
% 0.86/1.07      inference('sup-', [status(thm)], ['37', '38'])).
% 0.86/1.07  thf('40', plain,
% 0.86/1.07      (![X0 : $i]:
% 0.86/1.07         ((r1_tarski @ (k2_relat_1 @ (k2_wellord1 @ X0 @ sk_A)) @ sk_B)
% 0.86/1.07          | ~ (v1_relat_1 @ X0))),
% 0.86/1.07      inference('sup-', [status(thm)], ['30', '39'])).
% 0.86/1.07  thf(t125_relat_1, axiom,
% 0.86/1.07    (![A:$i,B:$i]:
% 0.86/1.07     ( ( v1_relat_1 @ B ) =>
% 0.86/1.07       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.86/1.07         ( ( k8_relat_1 @ A @ B ) = ( B ) ) ) ))).
% 0.86/1.07  thf('41', plain,
% 0.86/1.07      (![X14 : $i, X15 : $i]:
% 0.86/1.07         (~ (r1_tarski @ (k2_relat_1 @ X14) @ X15)
% 0.86/1.07          | ((k8_relat_1 @ X15 @ X14) = (X14))
% 0.86/1.07          | ~ (v1_relat_1 @ X14))),
% 0.86/1.07      inference('cnf', [status(esa)], [t125_relat_1])).
% 0.86/1.07  thf('42', plain,
% 0.86/1.07      (![X0 : $i]:
% 0.86/1.07         (~ (v1_relat_1 @ X0)
% 0.86/1.07          | ~ (v1_relat_1 @ (k2_wellord1 @ X0 @ sk_A))
% 0.86/1.07          | ((k8_relat_1 @ sk_B @ (k2_wellord1 @ X0 @ sk_A))
% 0.86/1.07              = (k2_wellord1 @ X0 @ sk_A)))),
% 0.86/1.07      inference('sup-', [status(thm)], ['40', '41'])).
% 0.86/1.07  thf('43', plain,
% 0.86/1.07      (![X18 : $i, X19 : $i]:
% 0.86/1.07         (~ (v1_relat_1 @ X18) | (v1_relat_1 @ (k2_wellord1 @ X18 @ X19)))),
% 0.86/1.07      inference('cnf', [status(esa)], [dt_k2_wellord1])).
% 0.86/1.07  thf('44', plain,
% 0.86/1.07      (![X0 : $i]:
% 0.86/1.07         (((k8_relat_1 @ sk_B @ (k2_wellord1 @ X0 @ sk_A))
% 0.86/1.07            = (k2_wellord1 @ X0 @ sk_A))
% 0.86/1.07          | ~ (v1_relat_1 @ X0))),
% 0.86/1.07      inference('clc', [status(thm)], ['42', '43'])).
% 0.86/1.07  thf(t17_wellord1, axiom,
% 0.86/1.07    (![A:$i,B:$i]:
% 0.86/1.07     ( ( v1_relat_1 @ B ) =>
% 0.86/1.07       ( ( k2_wellord1 @ B @ A ) = ( k7_relat_1 @ ( k8_relat_1 @ A @ B ) @ A ) ) ))).
% 0.86/1.07  thf('45', plain,
% 0.86/1.07      (![X20 : $i, X21 : $i]:
% 0.86/1.07         (((k2_wellord1 @ X21 @ X20)
% 0.86/1.07            = (k7_relat_1 @ (k8_relat_1 @ X20 @ X21) @ X20))
% 0.86/1.07          | ~ (v1_relat_1 @ X21))),
% 0.86/1.07      inference('cnf', [status(esa)], [t17_wellord1])).
% 0.86/1.07  thf('46', plain,
% 0.86/1.07      (![X0 : $i]:
% 0.86/1.07         (((k2_wellord1 @ (k2_wellord1 @ X0 @ sk_A) @ sk_B)
% 0.86/1.07            = (k7_relat_1 @ (k2_wellord1 @ X0 @ sk_A) @ sk_B))
% 0.86/1.07          | ~ (v1_relat_1 @ X0)
% 0.86/1.07          | ~ (v1_relat_1 @ (k2_wellord1 @ X0 @ sk_A)))),
% 0.86/1.07      inference('sup+', [status(thm)], ['44', '45'])).
% 0.86/1.07  thf('47', plain,
% 0.86/1.07      (![X18 : $i, X19 : $i]:
% 0.86/1.07         (~ (v1_relat_1 @ X18) | (v1_relat_1 @ (k2_wellord1 @ X18 @ X19)))),
% 0.86/1.07      inference('cnf', [status(esa)], [dt_k2_wellord1])).
% 0.86/1.07  thf('48', plain,
% 0.86/1.07      (![X0 : $i]:
% 0.86/1.07         (~ (v1_relat_1 @ X0)
% 0.86/1.07          | ((k2_wellord1 @ (k2_wellord1 @ X0 @ sk_A) @ sk_B)
% 0.86/1.07              = (k7_relat_1 @ (k2_wellord1 @ X0 @ sk_A) @ sk_B)))),
% 0.86/1.07      inference('clc', [status(thm)], ['46', '47'])).
% 0.86/1.07  thf('49', plain,
% 0.86/1.07      (![X0 : $i]:
% 0.86/1.07         (((k2_wellord1 @ (k2_wellord1 @ X0 @ sk_B) @ sk_A)
% 0.86/1.07            = (k7_relat_1 @ (k2_wellord1 @ X0 @ sk_A) @ sk_B))
% 0.86/1.07          | ~ (v1_relat_1 @ X0)
% 0.86/1.07          | ~ (v1_relat_1 @ X0))),
% 0.86/1.07      inference('sup+', [status(thm)], ['29', '48'])).
% 0.86/1.07  thf('50', plain,
% 0.86/1.07      (![X0 : $i]:
% 0.86/1.07         (~ (v1_relat_1 @ X0)
% 0.86/1.07          | ((k2_wellord1 @ (k2_wellord1 @ X0 @ sk_B) @ sk_A)
% 0.86/1.07              = (k7_relat_1 @ (k2_wellord1 @ X0 @ sk_A) @ sk_B)))),
% 0.86/1.07      inference('simplify', [status(thm)], ['49'])).
% 0.86/1.07  thf('51', plain,
% 0.86/1.07      (((k2_wellord1 @ (k2_wellord1 @ sk_C @ sk_B) @ sk_A)
% 0.86/1.07         != (k2_wellord1 @ sk_C @ sk_A))),
% 0.86/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.07  thf('52', plain,
% 0.86/1.07      ((((k7_relat_1 @ (k2_wellord1 @ sk_C @ sk_A) @ sk_B)
% 0.86/1.07          != (k2_wellord1 @ sk_C @ sk_A))
% 0.86/1.07        | ~ (v1_relat_1 @ sk_C))),
% 0.86/1.07      inference('sup-', [status(thm)], ['50', '51'])).
% 0.86/1.07  thf('53', plain, ((v1_relat_1 @ sk_C)),
% 0.86/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.07  thf('54', plain,
% 0.86/1.07      (((k7_relat_1 @ (k2_wellord1 @ sk_C @ sk_A) @ sk_B)
% 0.86/1.07         != (k2_wellord1 @ sk_C @ sk_A))),
% 0.86/1.07      inference('demod', [status(thm)], ['52', '53'])).
% 0.86/1.07  thf('55', plain,
% 0.86/1.07      ((((k2_wellord1 @ sk_C @ sk_A) != (k2_wellord1 @ sk_C @ sk_A))
% 0.86/1.07        | ~ (v1_relat_1 @ sk_C))),
% 0.86/1.07      inference('sup-', [status(thm)], ['28', '54'])).
% 0.86/1.07  thf('56', plain, ((v1_relat_1 @ sk_C)),
% 0.86/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.07  thf('57', plain,
% 0.86/1.07      (((k2_wellord1 @ sk_C @ sk_A) != (k2_wellord1 @ sk_C @ sk_A))),
% 0.86/1.07      inference('demod', [status(thm)], ['55', '56'])).
% 0.86/1.07  thf('58', plain, ($false), inference('simplify', [status(thm)], ['57'])).
% 0.86/1.07  
% 0.86/1.07  % SZS output end Refutation
% 0.86/1.07  
% 0.91/1.08  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
