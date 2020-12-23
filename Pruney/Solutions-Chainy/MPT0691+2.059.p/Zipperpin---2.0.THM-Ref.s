%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ejlrodXoTR

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:26 EST 2020

% Result     : Theorem 1.61s
% Output     : Refutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :  172 (1091 expanded)
%              Number of leaves         :   31 ( 349 expanded)
%              Depth                    :   39
%              Number of atoms          : 1471 (10245 expanded)
%              Number of equality atoms :   91 ( 661 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

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
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( r1_tarski @ X38 @ X39 )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X40 @ X39 ) @ X38 )
        = ( k9_relat_1 @ X40 @ X38 ) )
      | ~ ( v1_relat_1 @ X40 ) ) ),
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
    ! [X35: $i,X36: $i] :
      ( ~ ( v1_relat_1 @ X35 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X35 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('6',plain,(
    ! [X41: $i] :
      ( ( ( k10_relat_1 @ X41 @ ( k2_relat_1 @ X41 ) )
        = ( k1_relat_1 @ X41 ) )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf(t98_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = A ) ) )).

thf('7',plain,(
    ! [X48: $i] :
      ( ( ( k7_relat_1 @ X48 @ ( k1_relat_1 @ X48 ) )
        = X48 )
      | ~ ( v1_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t98_relat_1])).

thf(t139_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('8',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X52 @ X51 ) @ X53 )
        = ( k3_xboole_0 @ X51 @ ( k10_relat_1 @ X52 @ X53 ) ) )
      | ~ ( v1_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ X0 @ X1 )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ X1 )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('11',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k10_relat_1 @ X1 @ X0 ) )
        = ( k5_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k10_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
        = ( k5_xboole_0 @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','12'])).

thf('14',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('15',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_xboole_0 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('20',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('21',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_xboole_0 @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['13','18','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_xboole_0 @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k10_relat_1 @ X1 @ X0 ) )
        = ( k5_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k10_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('27',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k4_xboole_0 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k10_relat_1 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ X1 ) @ ( k10_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('31',plain,(
    ! [X44: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X44 ) )
      = X44 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('32',plain,(
    ! [X48: $i] :
      ( ( ( k7_relat_1 @ X48 @ ( k1_relat_1 @ X48 ) )
        = X48 )
      | ~ ( v1_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t98_relat_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('34',plain,(
    ! [X49: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('37',plain,(
    ! [X46: $i,X47: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X46 @ X47 ) ) @ X47 )
      | ~ ( v1_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('38',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X9 @ X10 )
      | ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ sk_A ) ) @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X44: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X44 ) )
      = X44 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t189_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k7_relat_1 @ A @ ( k1_relat_1 @ B ) )
            = ( k7_relat_1 @ A @ ( k1_relat_1 @ ( k7_relat_1 @ B @ ( k1_relat_1 @ A ) ) ) ) ) ) ) )).

thf('42',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( v1_relat_1 @ X42 )
      | ( ( k7_relat_1 @ X43 @ ( k1_relat_1 @ X42 ) )
        = ( k7_relat_1 @ X43 @ ( k1_relat_1 @ ( k7_relat_1 @ X42 @ ( k1_relat_1 @ X43 ) ) ) ) )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t189_relat_1])).

thf('43',plain,(
    ! [X46: $i,X47: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X46 @ X47 ) ) @ X47 )
      | ~ ( v1_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X2 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['42','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) ) @ ( k1_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['41','47'])).

thf('49',plain,(
    ! [X49: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X9 @ X10 )
      | ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) @ X2 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ X0 @ sk_A ) @ X1 ) ) @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['40','52'])).

thf('54',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( v1_relat_1 @ X35 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X35 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ X0 @ sk_A ) @ X1 ) ) @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ X0 ) ) @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['35','55'])).

thf('57',plain,(
    ! [X49: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ X0 ) ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X9 @ X10 )
      | ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ X0 ) ) @ X1 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ X0 ) ) @ ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['30','60'])).

thf('62',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ X0 ) ) @ ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_xboole_0 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ X0 ) ) @ ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( v1_relat_1 @ X42 )
      | ( ( k7_relat_1 @ X43 @ ( k1_relat_1 @ X42 ) )
        = ( k7_relat_1 @ X43 @ ( k1_relat_1 @ ( k7_relat_1 @ X42 @ ( k1_relat_1 @ X43 ) ) ) ) )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t189_relat_1])).

thf('67',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X52 @ X51 ) @ X53 )
        = ( k3_xboole_0 @ X51 @ ( k10_relat_1 @ X52 @ X53 ) ) )
      | ~ ( v1_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) @ X2 )
        = ( k3_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X1 ) ) ) @ ( k10_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) @ X2 )
        = ( k3_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X1 ) ) ) @ ( k10_relat_1 @ X1 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,
    ( ( ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ ( k6_relat_1 @ sk_A ) ) ) @ ( k2_relat_1 @ sk_B ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['65','69'])).

thf('71',plain,(
    ! [X44: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X44 ) )
      = X44 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('72',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X49: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('74',plain,
    ( ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B ) )
    = ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['70','71','72','73'])).

thf('75',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X52 @ X51 ) @ X53 )
        = ( k3_xboole_0 @ X51 @ ( k10_relat_1 @ X52 @ X53 ) ) )
      | ~ ( v1_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('76',plain,
    ( ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B ) )
    = ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['70','71','72','73'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('78',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) )
      | ( ( k1_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ~ ( r1_tarski @ ( k1_relat_1 @ ( k6_relat_1 @ sk_A ) ) @ ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B ) ) )
    | ( ( k1_relat_1 @ ( k6_relat_1 @ sk_A ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['76','79'])).

thf('81',plain,(
    ! [X44: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X44 ) )
      = X44 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('82',plain,(
    ! [X44: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X44 ) )
      = X44 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('83',plain,
    ( ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B ) )
    = ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['70','71','72','73'])).

thf('84',plain,(
    ! [X49: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('85',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B ) ) )
    | ( sk_A
      = ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['80','81','82','83','84'])).

thf('86',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ( sk_A
      = ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['75','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('88',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X9 @ X10 )
      | ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['87','90'])).

thf('92',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_xboole_0 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('95',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) )
    = sk_A ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['1'])).

thf('97',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( sk_A
    = ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['86','95','96','97'])).

thf('99',plain,
    ( sk_A
    = ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['74','98'])).

thf('100',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( v1_relat_1 @ X42 )
      | ( ( k7_relat_1 @ X43 @ ( k1_relat_1 @ X42 ) )
        = ( k7_relat_1 @ X43 @ ( k1_relat_1 @ ( k7_relat_1 @ X42 @ ( k1_relat_1 @ X43 ) ) ) ) )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t189_relat_1])).

thf('101',plain,(
    ! [X46: $i,X47: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X46 @ X47 ) ) @ X47 )
      | ~ ( v1_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X1 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X1 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,
    ( ( r1_tarski @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ ( k6_relat_1 @ sk_A ) ) ) ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['99','103'])).

thf('105',plain,(
    ! [X44: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X44 ) )
      = X44 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('106',plain,(
    ! [X49: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('107',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['104','105','106','107'])).

thf('109',plain,(
    ! [X46: $i,X47: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X46 @ X47 ) ) @ X47 )
      | ~ ( v1_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf('110',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ( X0
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,
    ( ( sk_A
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['108','111'])).

thf('113',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( sk_A
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['112','113'])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('115',plain,(
    ! [X37: $i] :
      ( ( ( k9_relat_1 @ X37 @ ( k1_relat_1 @ X37 ) )
        = ( k2_relat_1 @ X37 ) )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('116',plain,
    ( ( ( k9_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ sk_A )
      = ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['114','115'])).

thf('117',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( k9_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ sk_A )
      = ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['5','116'])).

thf('118',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( k9_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ sk_A )
    = ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,
    ( ( ( k9_relat_1 @ sk_B @ sk_A )
      = ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['4','119'])).

thf('121',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( ( k9_relat_1 @ sk_B @ sk_A )
    = ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X52 @ X51 ) @ X53 )
        = ( k3_xboole_0 @ X51 @ ( k10_relat_1 @ X52 @ X53 ) ) )
      | ~ ( v1_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('124',plain,(
    ! [X41: $i] :
      ( ( ( k10_relat_1 @ X41 @ ( k2_relat_1 @ X41 ) )
        = ( k1_relat_1 @ X41 ) )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( v1_relat_1 @ X35 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X35 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['125','126'])).

thf('128',plain,
    ( ( ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['122','127'])).

thf('129',plain,
    ( sk_A
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('130',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    = sk_A ),
    inference(demod,[status(thm)],['128','129','130'])).

thf('132',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('133',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    = ( k5_xboole_0 @ sk_A @ sk_A ) ),
    inference('sup+',[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['19','22'])).

thf('135',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['133','134'])).

thf('136',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k4_xboole_0 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('137',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['137'])).

thf('139',plain,(
    $false ),
    inference(demod,[status(thm)],['0','138'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ejlrodXoTR
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:46:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 1.61/1.78  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.61/1.78  % Solved by: fo/fo7.sh
% 1.61/1.78  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.61/1.78  % done 2231 iterations in 1.328s
% 1.61/1.78  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.61/1.78  % SZS output start Refutation
% 1.61/1.78  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.61/1.78  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.61/1.78  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 1.61/1.78  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.61/1.78  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.61/1.78  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.61/1.78  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.61/1.78  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.61/1.78  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 1.61/1.78  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.61/1.78  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.61/1.78  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.61/1.78  thf(sk_B_type, type, sk_B: $i).
% 1.61/1.78  thf(sk_A_type, type, sk_A: $i).
% 1.61/1.78  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.61/1.78  thf(t146_funct_1, conjecture,
% 1.61/1.78    (![A:$i,B:$i]:
% 1.61/1.78     ( ( v1_relat_1 @ B ) =>
% 1.61/1.78       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 1.61/1.78         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 1.61/1.78  thf(zf_stmt_0, negated_conjecture,
% 1.61/1.78    (~( ![A:$i,B:$i]:
% 1.61/1.78        ( ( v1_relat_1 @ B ) =>
% 1.61/1.78          ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 1.61/1.78            ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )),
% 1.61/1.78    inference('cnf.neg', [status(esa)], [t146_funct_1])).
% 1.61/1.78  thf('0', plain,
% 1.61/1.78      (~ (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 1.61/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.78  thf(d10_xboole_0, axiom,
% 1.61/1.78    (![A:$i,B:$i]:
% 1.61/1.78     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.61/1.78  thf('1', plain,
% 1.61/1.78      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 1.61/1.78      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.61/1.78  thf('2', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.61/1.78      inference('simplify', [status(thm)], ['1'])).
% 1.61/1.78  thf(t162_relat_1, axiom,
% 1.61/1.78    (![A:$i]:
% 1.61/1.78     ( ( v1_relat_1 @ A ) =>
% 1.61/1.78       ( ![B:$i,C:$i]:
% 1.61/1.78         ( ( r1_tarski @ B @ C ) =>
% 1.61/1.78           ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B ) =
% 1.61/1.78             ( k9_relat_1 @ A @ B ) ) ) ) ))).
% 1.61/1.78  thf('3', plain,
% 1.61/1.78      (![X38 : $i, X39 : $i, X40 : $i]:
% 1.61/1.78         (~ (r1_tarski @ X38 @ X39)
% 1.61/1.78          | ((k9_relat_1 @ (k7_relat_1 @ X40 @ X39) @ X38)
% 1.61/1.78              = (k9_relat_1 @ X40 @ X38))
% 1.61/1.78          | ~ (v1_relat_1 @ X40))),
% 1.61/1.78      inference('cnf', [status(esa)], [t162_relat_1])).
% 1.61/1.78  thf('4', plain,
% 1.61/1.78      (![X0 : $i, X1 : $i]:
% 1.61/1.78         (~ (v1_relat_1 @ X1)
% 1.61/1.78          | ((k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X0)
% 1.61/1.78              = (k9_relat_1 @ X1 @ X0)))),
% 1.61/1.78      inference('sup-', [status(thm)], ['2', '3'])).
% 1.61/1.78  thf(dt_k7_relat_1, axiom,
% 1.61/1.78    (![A:$i,B:$i]:
% 1.61/1.78     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 1.61/1.78  thf('5', plain,
% 1.61/1.78      (![X35 : $i, X36 : $i]:
% 1.61/1.78         (~ (v1_relat_1 @ X35) | (v1_relat_1 @ (k7_relat_1 @ X35 @ X36)))),
% 1.61/1.78      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 1.61/1.78  thf(t169_relat_1, axiom,
% 1.61/1.78    (![A:$i]:
% 1.61/1.78     ( ( v1_relat_1 @ A ) =>
% 1.61/1.78       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 1.61/1.78  thf('6', plain,
% 1.61/1.78      (![X41 : $i]:
% 1.61/1.78         (((k10_relat_1 @ X41 @ (k2_relat_1 @ X41)) = (k1_relat_1 @ X41))
% 1.61/1.78          | ~ (v1_relat_1 @ X41))),
% 1.61/1.78      inference('cnf', [status(esa)], [t169_relat_1])).
% 1.61/1.78  thf(t98_relat_1, axiom,
% 1.61/1.78    (![A:$i]:
% 1.61/1.78     ( ( v1_relat_1 @ A ) =>
% 1.61/1.78       ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( A ) ) ))).
% 1.61/1.78  thf('7', plain,
% 1.61/1.78      (![X48 : $i]:
% 1.61/1.78         (((k7_relat_1 @ X48 @ (k1_relat_1 @ X48)) = (X48))
% 1.61/1.78          | ~ (v1_relat_1 @ X48))),
% 1.61/1.78      inference('cnf', [status(esa)], [t98_relat_1])).
% 1.61/1.78  thf(t139_funct_1, axiom,
% 1.61/1.78    (![A:$i,B:$i,C:$i]:
% 1.61/1.78     ( ( v1_relat_1 @ C ) =>
% 1.61/1.78       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 1.61/1.78         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 1.61/1.78  thf('8', plain,
% 1.61/1.78      (![X51 : $i, X52 : $i, X53 : $i]:
% 1.61/1.78         (((k10_relat_1 @ (k7_relat_1 @ X52 @ X51) @ X53)
% 1.61/1.78            = (k3_xboole_0 @ X51 @ (k10_relat_1 @ X52 @ X53)))
% 1.61/1.78          | ~ (v1_relat_1 @ X52))),
% 1.61/1.78      inference('cnf', [status(esa)], [t139_funct_1])).
% 1.61/1.78  thf('9', plain,
% 1.61/1.78      (![X0 : $i, X1 : $i]:
% 1.61/1.78         (((k10_relat_1 @ X0 @ X1)
% 1.61/1.78            = (k3_xboole_0 @ (k1_relat_1 @ X0) @ (k10_relat_1 @ X0 @ X1)))
% 1.61/1.78          | ~ (v1_relat_1 @ X0)
% 1.61/1.78          | ~ (v1_relat_1 @ X0))),
% 1.61/1.78      inference('sup+', [status(thm)], ['7', '8'])).
% 1.61/1.78  thf('10', plain,
% 1.61/1.78      (![X0 : $i, X1 : $i]:
% 1.61/1.78         (~ (v1_relat_1 @ X0)
% 1.61/1.78          | ((k10_relat_1 @ X0 @ X1)
% 1.61/1.78              = (k3_xboole_0 @ (k1_relat_1 @ X0) @ (k10_relat_1 @ X0 @ X1))))),
% 1.61/1.78      inference('simplify', [status(thm)], ['9'])).
% 1.61/1.78  thf(t100_xboole_1, axiom,
% 1.61/1.78    (![A:$i,B:$i]:
% 1.61/1.78     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.61/1.78  thf('11', plain,
% 1.61/1.78      (![X6 : $i, X7 : $i]:
% 1.61/1.78         ((k4_xboole_0 @ X6 @ X7)
% 1.61/1.78           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 1.61/1.78      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.61/1.78  thf('12', plain,
% 1.61/1.78      (![X0 : $i, X1 : $i]:
% 1.61/1.78         (((k4_xboole_0 @ (k1_relat_1 @ X1) @ (k10_relat_1 @ X1 @ X0))
% 1.61/1.78            = (k5_xboole_0 @ (k1_relat_1 @ X1) @ (k10_relat_1 @ X1 @ X0)))
% 1.61/1.78          | ~ (v1_relat_1 @ X1))),
% 1.61/1.78      inference('sup+', [status(thm)], ['10', '11'])).
% 1.61/1.78  thf('13', plain,
% 1.61/1.78      (![X0 : $i]:
% 1.61/1.78         (((k4_xboole_0 @ (k1_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 1.61/1.78            = (k5_xboole_0 @ (k1_relat_1 @ X0) @ 
% 1.61/1.78               (k10_relat_1 @ X0 @ (k2_relat_1 @ X0))))
% 1.61/1.78          | ~ (v1_relat_1 @ X0)
% 1.61/1.78          | ~ (v1_relat_1 @ X0))),
% 1.61/1.78      inference('sup+', [status(thm)], ['6', '12'])).
% 1.61/1.78  thf('14', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.61/1.78      inference('simplify', [status(thm)], ['1'])).
% 1.61/1.78  thf(t28_xboole_1, axiom,
% 1.61/1.78    (![A:$i,B:$i]:
% 1.61/1.78     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.61/1.78  thf('15', plain,
% 1.61/1.78      (![X11 : $i, X12 : $i]:
% 1.61/1.78         (((k3_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_tarski @ X11 @ X12))),
% 1.61/1.78      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.61/1.78  thf('16', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 1.61/1.78      inference('sup-', [status(thm)], ['14', '15'])).
% 1.61/1.78  thf('17', plain,
% 1.61/1.78      (![X6 : $i, X7 : $i]:
% 1.61/1.78         ((k4_xboole_0 @ X6 @ X7)
% 1.61/1.78           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 1.61/1.78      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.61/1.78  thf('18', plain,
% 1.61/1.78      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.61/1.78      inference('sup+', [status(thm)], ['16', '17'])).
% 1.61/1.78  thf('19', plain,
% 1.61/1.78      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.61/1.78      inference('sup+', [status(thm)], ['16', '17'])).
% 1.61/1.78  thf('20', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.61/1.78      inference('simplify', [status(thm)], ['1'])).
% 1.61/1.78  thf(l32_xboole_1, axiom,
% 1.61/1.78    (![A:$i,B:$i]:
% 1.61/1.78     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.61/1.78  thf('21', plain,
% 1.61/1.78      (![X3 : $i, X5 : $i]:
% 1.61/1.78         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 1.61/1.78      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.61/1.78  thf('22', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.61/1.78      inference('sup-', [status(thm)], ['20', '21'])).
% 1.61/1.78  thf('23', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.61/1.78      inference('sup+', [status(thm)], ['19', '22'])).
% 1.61/1.78  thf('24', plain,
% 1.61/1.78      (![X0 : $i]:
% 1.61/1.78         (((k1_xboole_0)
% 1.61/1.78            = (k5_xboole_0 @ (k1_relat_1 @ X0) @ 
% 1.61/1.78               (k10_relat_1 @ X0 @ (k2_relat_1 @ X0))))
% 1.61/1.78          | ~ (v1_relat_1 @ X0)
% 1.61/1.78          | ~ (v1_relat_1 @ X0))),
% 1.61/1.78      inference('demod', [status(thm)], ['13', '18', '23'])).
% 1.61/1.78  thf('25', plain,
% 1.61/1.78      (![X0 : $i]:
% 1.61/1.78         (~ (v1_relat_1 @ X0)
% 1.61/1.78          | ((k1_xboole_0)
% 1.61/1.78              = (k5_xboole_0 @ (k1_relat_1 @ X0) @ 
% 1.61/1.78                 (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))))),
% 1.61/1.78      inference('simplify', [status(thm)], ['24'])).
% 1.61/1.78  thf('26', plain,
% 1.61/1.78      (![X0 : $i, X1 : $i]:
% 1.61/1.78         (((k4_xboole_0 @ (k1_relat_1 @ X1) @ (k10_relat_1 @ X1 @ X0))
% 1.61/1.78            = (k5_xboole_0 @ (k1_relat_1 @ X1) @ (k10_relat_1 @ X1 @ X0)))
% 1.61/1.78          | ~ (v1_relat_1 @ X1))),
% 1.61/1.78      inference('sup+', [status(thm)], ['10', '11'])).
% 1.61/1.78  thf('27', plain,
% 1.61/1.78      (![X3 : $i, X4 : $i]:
% 1.61/1.78         ((r1_tarski @ X3 @ X4) | ((k4_xboole_0 @ X3 @ X4) != (k1_xboole_0)))),
% 1.61/1.78      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.61/1.78  thf('28', plain,
% 1.61/1.78      (![X0 : $i, X1 : $i]:
% 1.61/1.78         (((k5_xboole_0 @ (k1_relat_1 @ X1) @ (k10_relat_1 @ X1 @ X0))
% 1.61/1.78            != (k1_xboole_0))
% 1.61/1.78          | ~ (v1_relat_1 @ X1)
% 1.61/1.78          | (r1_tarski @ (k1_relat_1 @ X1) @ (k10_relat_1 @ X1 @ X0)))),
% 1.61/1.78      inference('sup-', [status(thm)], ['26', '27'])).
% 1.61/1.78  thf('29', plain,
% 1.61/1.78      (![X0 : $i]:
% 1.61/1.78         (((k1_xboole_0) != (k1_xboole_0))
% 1.61/1.78          | ~ (v1_relat_1 @ X0)
% 1.61/1.78          | (r1_tarski @ (k1_relat_1 @ X0) @ 
% 1.61/1.78             (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 1.61/1.78          | ~ (v1_relat_1 @ X0))),
% 1.61/1.78      inference('sup-', [status(thm)], ['25', '28'])).
% 1.61/1.78  thf('30', plain,
% 1.61/1.78      (![X0 : $i]:
% 1.61/1.78         ((r1_tarski @ (k1_relat_1 @ X0) @ 
% 1.61/1.78           (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 1.61/1.78          | ~ (v1_relat_1 @ X0))),
% 1.61/1.78      inference('simplify', [status(thm)], ['29'])).
% 1.61/1.78  thf(t71_relat_1, axiom,
% 1.61/1.78    (![A:$i]:
% 1.61/1.78     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 1.61/1.78       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 1.61/1.78  thf('31', plain, (![X44 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X44)) = (X44))),
% 1.61/1.78      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.61/1.78  thf('32', plain,
% 1.61/1.78      (![X48 : $i]:
% 1.61/1.78         (((k7_relat_1 @ X48 @ (k1_relat_1 @ X48)) = (X48))
% 1.61/1.78          | ~ (v1_relat_1 @ X48))),
% 1.61/1.78      inference('cnf', [status(esa)], [t98_relat_1])).
% 1.61/1.78  thf('33', plain,
% 1.61/1.78      (![X0 : $i]:
% 1.61/1.78         (((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))
% 1.61/1.78          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 1.61/1.78      inference('sup+', [status(thm)], ['31', '32'])).
% 1.61/1.78  thf(fc4_funct_1, axiom,
% 1.61/1.78    (![A:$i]:
% 1.61/1.78     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 1.61/1.78       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 1.61/1.78  thf('34', plain, (![X49 : $i]: (v1_relat_1 @ (k6_relat_1 @ X49))),
% 1.61/1.78      inference('cnf', [status(esa)], [fc4_funct_1])).
% 1.61/1.78  thf('35', plain,
% 1.61/1.78      (![X0 : $i]: ((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 1.61/1.78      inference('demod', [status(thm)], ['33', '34'])).
% 1.61/1.78  thf('36', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 1.61/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.78  thf(t87_relat_1, axiom,
% 1.61/1.78    (![A:$i,B:$i]:
% 1.61/1.78     ( ( v1_relat_1 @ B ) =>
% 1.61/1.78       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 1.61/1.78  thf('37', plain,
% 1.61/1.78      (![X46 : $i, X47 : $i]:
% 1.61/1.78         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X46 @ X47)) @ X47)
% 1.61/1.78          | ~ (v1_relat_1 @ X46))),
% 1.61/1.78      inference('cnf', [status(esa)], [t87_relat_1])).
% 1.61/1.78  thf(t1_xboole_1, axiom,
% 1.61/1.78    (![A:$i,B:$i,C:$i]:
% 1.61/1.78     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 1.61/1.78       ( r1_tarski @ A @ C ) ))).
% 1.61/1.78  thf('38', plain,
% 1.61/1.78      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.61/1.78         (~ (r1_tarski @ X8 @ X9)
% 1.61/1.78          | ~ (r1_tarski @ X9 @ X10)
% 1.61/1.78          | (r1_tarski @ X8 @ X10))),
% 1.61/1.78      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.61/1.78  thf('39', plain,
% 1.61/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.61/1.78         (~ (v1_relat_1 @ X1)
% 1.61/1.78          | (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X2)
% 1.61/1.78          | ~ (r1_tarski @ X0 @ X2))),
% 1.61/1.78      inference('sup-', [status(thm)], ['37', '38'])).
% 1.61/1.78  thf('40', plain,
% 1.61/1.78      (![X0 : $i]:
% 1.61/1.78         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X0 @ sk_A)) @ 
% 1.61/1.78           (k1_relat_1 @ sk_B))
% 1.61/1.78          | ~ (v1_relat_1 @ X0))),
% 1.61/1.78      inference('sup-', [status(thm)], ['36', '39'])).
% 1.61/1.78  thf('41', plain, (![X44 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X44)) = (X44))),
% 1.61/1.78      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.61/1.78  thf(t189_relat_1, axiom,
% 1.61/1.78    (![A:$i]:
% 1.61/1.78     ( ( v1_relat_1 @ A ) =>
% 1.61/1.78       ( ![B:$i]:
% 1.61/1.78         ( ( v1_relat_1 @ B ) =>
% 1.61/1.78           ( ( k7_relat_1 @ A @ ( k1_relat_1 @ B ) ) =
% 1.61/1.78             ( k7_relat_1 @
% 1.61/1.78               A @ ( k1_relat_1 @ ( k7_relat_1 @ B @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ))).
% 1.61/1.78  thf('42', plain,
% 1.61/1.78      (![X42 : $i, X43 : $i]:
% 1.61/1.78         (~ (v1_relat_1 @ X42)
% 1.61/1.78          | ((k7_relat_1 @ X43 @ (k1_relat_1 @ X42))
% 1.61/1.78              = (k7_relat_1 @ X43 @ 
% 1.61/1.78                 (k1_relat_1 @ (k7_relat_1 @ X42 @ (k1_relat_1 @ X43)))))
% 1.61/1.78          | ~ (v1_relat_1 @ X43))),
% 1.61/1.78      inference('cnf', [status(esa)], [t189_relat_1])).
% 1.61/1.78  thf('43', plain,
% 1.61/1.78      (![X46 : $i, X47 : $i]:
% 1.61/1.78         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X46 @ X47)) @ X47)
% 1.61/1.78          | ~ (v1_relat_1 @ X46))),
% 1.61/1.78      inference('cnf', [status(esa)], [t87_relat_1])).
% 1.61/1.78  thf('44', plain,
% 1.61/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.61/1.78         (~ (v1_relat_1 @ X1)
% 1.61/1.78          | (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X2)
% 1.61/1.78          | ~ (r1_tarski @ X0 @ X2))),
% 1.61/1.78      inference('sup-', [status(thm)], ['37', '38'])).
% 1.61/1.78  thf('45', plain,
% 1.61/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.61/1.78         (~ (v1_relat_1 @ X1)
% 1.61/1.78          | (r1_tarski @ 
% 1.61/1.78             (k1_relat_1 @ 
% 1.61/1.78              (k7_relat_1 @ X2 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))) @ 
% 1.61/1.78             X0)
% 1.61/1.78          | ~ (v1_relat_1 @ X2))),
% 1.61/1.78      inference('sup-', [status(thm)], ['43', '44'])).
% 1.61/1.78  thf('46', plain,
% 1.61/1.78      (![X0 : $i, X1 : $i]:
% 1.61/1.78         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X1 @ (k1_relat_1 @ X0))) @ 
% 1.61/1.78           (k1_relat_1 @ X1))
% 1.61/1.78          | ~ (v1_relat_1 @ X1)
% 1.61/1.78          | ~ (v1_relat_1 @ X0)
% 1.61/1.78          | ~ (v1_relat_1 @ X1)
% 1.61/1.78          | ~ (v1_relat_1 @ X0))),
% 1.61/1.78      inference('sup+', [status(thm)], ['42', '45'])).
% 1.61/1.78  thf('47', plain,
% 1.61/1.78      (![X0 : $i, X1 : $i]:
% 1.61/1.78         (~ (v1_relat_1 @ X0)
% 1.61/1.78          | ~ (v1_relat_1 @ X1)
% 1.61/1.78          | (r1_tarski @ 
% 1.61/1.78             (k1_relat_1 @ (k7_relat_1 @ X1 @ (k1_relat_1 @ X0))) @ 
% 1.61/1.78             (k1_relat_1 @ X1)))),
% 1.61/1.78      inference('simplify', [status(thm)], ['46'])).
% 1.61/1.78  thf('48', plain,
% 1.61/1.78      (![X0 : $i, X1 : $i]:
% 1.61/1.78         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ 
% 1.61/1.78           (k1_relat_1 @ X1))
% 1.61/1.78          | ~ (v1_relat_1 @ X1)
% 1.61/1.78          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 1.61/1.78      inference('sup+', [status(thm)], ['41', '47'])).
% 1.61/1.78  thf('49', plain, (![X49 : $i]: (v1_relat_1 @ (k6_relat_1 @ X49))),
% 1.61/1.78      inference('cnf', [status(esa)], [fc4_funct_1])).
% 1.61/1.78  thf('50', plain,
% 1.61/1.78      (![X0 : $i, X1 : $i]:
% 1.61/1.78         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ 
% 1.61/1.78           (k1_relat_1 @ X1))
% 1.61/1.78          | ~ (v1_relat_1 @ X1))),
% 1.61/1.78      inference('demod', [status(thm)], ['48', '49'])).
% 1.61/1.78  thf('51', plain,
% 1.61/1.78      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.61/1.78         (~ (r1_tarski @ X8 @ X9)
% 1.61/1.78          | ~ (r1_tarski @ X9 @ X10)
% 1.61/1.78          | (r1_tarski @ X8 @ X10))),
% 1.61/1.78      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.61/1.78  thf('52', plain,
% 1.61/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.61/1.78         (~ (v1_relat_1 @ X0)
% 1.61/1.78          | (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X0 @ X1)) @ X2)
% 1.61/1.78          | ~ (r1_tarski @ (k1_relat_1 @ X0) @ X2))),
% 1.61/1.78      inference('sup-', [status(thm)], ['50', '51'])).
% 1.61/1.78  thf('53', plain,
% 1.61/1.78      (![X0 : $i, X1 : $i]:
% 1.61/1.78         (~ (v1_relat_1 @ X0)
% 1.61/1.78          | (r1_tarski @ 
% 1.61/1.78             (k1_relat_1 @ (k7_relat_1 @ (k7_relat_1 @ X0 @ sk_A) @ X1)) @ 
% 1.61/1.78             (k1_relat_1 @ sk_B))
% 1.61/1.78          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ sk_A)))),
% 1.61/1.78      inference('sup-', [status(thm)], ['40', '52'])).
% 1.61/1.78  thf('54', plain,
% 1.61/1.78      (![X35 : $i, X36 : $i]:
% 1.61/1.78         (~ (v1_relat_1 @ X35) | (v1_relat_1 @ (k7_relat_1 @ X35 @ X36)))),
% 1.61/1.78      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 1.61/1.78  thf('55', plain,
% 1.61/1.78      (![X0 : $i, X1 : $i]:
% 1.61/1.78         ((r1_tarski @ 
% 1.61/1.78           (k1_relat_1 @ (k7_relat_1 @ (k7_relat_1 @ X0 @ sk_A) @ X1)) @ 
% 1.61/1.78           (k1_relat_1 @ sk_B))
% 1.61/1.78          | ~ (v1_relat_1 @ X0))),
% 1.61/1.78      inference('clc', [status(thm)], ['53', '54'])).
% 1.61/1.78  thf('56', plain,
% 1.61/1.78      (![X0 : $i]:
% 1.61/1.78         ((r1_tarski @ 
% 1.61/1.78           (k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ sk_A) @ X0)) @ 
% 1.61/1.78           (k1_relat_1 @ sk_B))
% 1.61/1.78          | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A)))),
% 1.61/1.78      inference('sup+', [status(thm)], ['35', '55'])).
% 1.61/1.78  thf('57', plain, (![X49 : $i]: (v1_relat_1 @ (k6_relat_1 @ X49))),
% 1.61/1.78      inference('cnf', [status(esa)], [fc4_funct_1])).
% 1.61/1.78  thf('58', plain,
% 1.61/1.78      (![X0 : $i]:
% 1.61/1.78         (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ sk_A) @ X0)) @ 
% 1.61/1.78          (k1_relat_1 @ sk_B))),
% 1.61/1.78      inference('demod', [status(thm)], ['56', '57'])).
% 1.61/1.78  thf('59', plain,
% 1.61/1.78      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.61/1.78         (~ (r1_tarski @ X8 @ X9)
% 1.61/1.78          | ~ (r1_tarski @ X9 @ X10)
% 1.61/1.78          | (r1_tarski @ X8 @ X10))),
% 1.61/1.78      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.61/1.78  thf('60', plain,
% 1.61/1.78      (![X0 : $i, X1 : $i]:
% 1.61/1.78         ((r1_tarski @ 
% 1.61/1.78           (k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ sk_A) @ X0)) @ X1)
% 1.61/1.78          | ~ (r1_tarski @ (k1_relat_1 @ sk_B) @ X1))),
% 1.61/1.78      inference('sup-', [status(thm)], ['58', '59'])).
% 1.61/1.78  thf('61', plain,
% 1.61/1.78      (![X0 : $i]:
% 1.61/1.78         (~ (v1_relat_1 @ sk_B)
% 1.61/1.78          | (r1_tarski @ 
% 1.61/1.78             (k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ sk_A) @ X0)) @ 
% 1.61/1.78             (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B))))),
% 1.61/1.78      inference('sup-', [status(thm)], ['30', '60'])).
% 1.61/1.78  thf('62', plain, ((v1_relat_1 @ sk_B)),
% 1.61/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.78  thf('63', plain,
% 1.61/1.78      (![X0 : $i]:
% 1.61/1.78         (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ sk_A) @ X0)) @ 
% 1.61/1.78          (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B)))),
% 1.61/1.78      inference('demod', [status(thm)], ['61', '62'])).
% 1.61/1.78  thf('64', plain,
% 1.61/1.78      (![X11 : $i, X12 : $i]:
% 1.61/1.78         (((k3_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_tarski @ X11 @ X12))),
% 1.61/1.78      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.61/1.78  thf('65', plain,
% 1.61/1.78      (![X0 : $i]:
% 1.61/1.78         ((k3_xboole_0 @ 
% 1.61/1.78           (k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ sk_A) @ X0)) @ 
% 1.61/1.78           (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B)))
% 1.61/1.78           = (k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ sk_A) @ X0)))),
% 1.61/1.78      inference('sup-', [status(thm)], ['63', '64'])).
% 1.61/1.78  thf('66', plain,
% 1.61/1.78      (![X42 : $i, X43 : $i]:
% 1.61/1.78         (~ (v1_relat_1 @ X42)
% 1.61/1.78          | ((k7_relat_1 @ X43 @ (k1_relat_1 @ X42))
% 1.61/1.78              = (k7_relat_1 @ X43 @ 
% 1.61/1.78                 (k1_relat_1 @ (k7_relat_1 @ X42 @ (k1_relat_1 @ X43)))))
% 1.61/1.78          | ~ (v1_relat_1 @ X43))),
% 1.61/1.78      inference('cnf', [status(esa)], [t189_relat_1])).
% 1.61/1.78  thf('67', plain,
% 1.61/1.78      (![X51 : $i, X52 : $i, X53 : $i]:
% 1.61/1.78         (((k10_relat_1 @ (k7_relat_1 @ X52 @ X51) @ X53)
% 1.61/1.78            = (k3_xboole_0 @ X51 @ (k10_relat_1 @ X52 @ X53)))
% 1.61/1.78          | ~ (v1_relat_1 @ X52))),
% 1.61/1.78      inference('cnf', [status(esa)], [t139_funct_1])).
% 1.61/1.78  thf('68', plain,
% 1.61/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.61/1.78         (((k10_relat_1 @ (k7_relat_1 @ X1 @ (k1_relat_1 @ X0)) @ X2)
% 1.61/1.78            = (k3_xboole_0 @ 
% 1.61/1.78               (k1_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X1))) @ 
% 1.61/1.78               (k10_relat_1 @ X1 @ X2)))
% 1.61/1.78          | ~ (v1_relat_1 @ X1)
% 1.61/1.78          | ~ (v1_relat_1 @ X0)
% 1.61/1.78          | ~ (v1_relat_1 @ X1))),
% 1.61/1.78      inference('sup+', [status(thm)], ['66', '67'])).
% 1.61/1.78  thf('69', plain,
% 1.61/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.61/1.78         (~ (v1_relat_1 @ X0)
% 1.61/1.78          | ~ (v1_relat_1 @ X1)
% 1.61/1.78          | ((k10_relat_1 @ (k7_relat_1 @ X1 @ (k1_relat_1 @ X0)) @ X2)
% 1.61/1.78              = (k3_xboole_0 @ 
% 1.61/1.78                 (k1_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X1))) @ 
% 1.61/1.78                 (k10_relat_1 @ X1 @ X2))))),
% 1.61/1.78      inference('simplify', [status(thm)], ['68'])).
% 1.61/1.78  thf('70', plain,
% 1.61/1.78      ((((k10_relat_1 @ 
% 1.61/1.78          (k7_relat_1 @ sk_B @ (k1_relat_1 @ (k6_relat_1 @ sk_A))) @ 
% 1.61/1.78          (k2_relat_1 @ sk_B))
% 1.61/1.78          = (k1_relat_1 @ 
% 1.61/1.78             (k7_relat_1 @ (k6_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))))
% 1.61/1.78        | ~ (v1_relat_1 @ sk_B)
% 1.61/1.78        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A)))),
% 1.61/1.78      inference('sup+', [status(thm)], ['65', '69'])).
% 1.61/1.78  thf('71', plain, (![X44 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X44)) = (X44))),
% 1.61/1.78      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.61/1.78  thf('72', plain, ((v1_relat_1 @ sk_B)),
% 1.61/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.78  thf('73', plain, (![X49 : $i]: (v1_relat_1 @ (k6_relat_1 @ X49))),
% 1.61/1.78      inference('cnf', [status(esa)], [fc4_funct_1])).
% 1.61/1.78  thf('74', plain,
% 1.61/1.78      (((k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ (k2_relat_1 @ sk_B))
% 1.61/1.78         = (k1_relat_1 @ 
% 1.61/1.78            (k7_relat_1 @ (k6_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))))),
% 1.61/1.78      inference('demod', [status(thm)], ['70', '71', '72', '73'])).
% 1.61/1.78  thf('75', plain,
% 1.61/1.78      (![X51 : $i, X52 : $i, X53 : $i]:
% 1.61/1.78         (((k10_relat_1 @ (k7_relat_1 @ X52 @ X51) @ X53)
% 1.61/1.78            = (k3_xboole_0 @ X51 @ (k10_relat_1 @ X52 @ X53)))
% 1.61/1.78          | ~ (v1_relat_1 @ X52))),
% 1.61/1.78      inference('cnf', [status(esa)], [t139_funct_1])).
% 1.61/1.78  thf('76', plain,
% 1.61/1.78      (((k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ (k2_relat_1 @ sk_B))
% 1.61/1.78         = (k1_relat_1 @ 
% 1.61/1.78            (k7_relat_1 @ (k6_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))))),
% 1.61/1.78      inference('demod', [status(thm)], ['70', '71', '72', '73'])).
% 1.61/1.78  thf('77', plain,
% 1.61/1.78      (![X0 : $i, X1 : $i]:
% 1.61/1.78         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ 
% 1.61/1.78           (k1_relat_1 @ X1))
% 1.61/1.78          | ~ (v1_relat_1 @ X1))),
% 1.61/1.78      inference('demod', [status(thm)], ['48', '49'])).
% 1.61/1.78  thf('78', plain,
% 1.61/1.78      (![X0 : $i, X2 : $i]:
% 1.61/1.78         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.61/1.78      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.61/1.78  thf('79', plain,
% 1.61/1.78      (![X0 : $i, X1 : $i]:
% 1.61/1.78         (~ (v1_relat_1 @ X0)
% 1.61/1.78          | ~ (r1_tarski @ (k1_relat_1 @ X0) @ 
% 1.61/1.78               (k1_relat_1 @ (k7_relat_1 @ X0 @ X1)))
% 1.61/1.78          | ((k1_relat_1 @ X0) = (k1_relat_1 @ (k7_relat_1 @ X0 @ X1))))),
% 1.61/1.78      inference('sup-', [status(thm)], ['77', '78'])).
% 1.61/1.78  thf('80', plain,
% 1.61/1.78      ((~ (r1_tarski @ (k1_relat_1 @ (k6_relat_1 @ sk_A)) @ 
% 1.61/1.78           (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ (k2_relat_1 @ sk_B)))
% 1.61/1.78        | ((k1_relat_1 @ (k6_relat_1 @ sk_A))
% 1.61/1.78            = (k1_relat_1 @ 
% 1.61/1.78               (k7_relat_1 @ (k6_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))))
% 1.61/1.78        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A)))),
% 1.61/1.78      inference('sup-', [status(thm)], ['76', '79'])).
% 1.61/1.78  thf('81', plain, (![X44 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X44)) = (X44))),
% 1.61/1.78      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.61/1.78  thf('82', plain, (![X44 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X44)) = (X44))),
% 1.61/1.78      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.61/1.78  thf('83', plain,
% 1.61/1.78      (((k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ (k2_relat_1 @ sk_B))
% 1.61/1.78         = (k1_relat_1 @ 
% 1.61/1.78            (k7_relat_1 @ (k6_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))))),
% 1.61/1.78      inference('demod', [status(thm)], ['70', '71', '72', '73'])).
% 1.61/1.78  thf('84', plain, (![X49 : $i]: (v1_relat_1 @ (k6_relat_1 @ X49))),
% 1.61/1.78      inference('cnf', [status(esa)], [fc4_funct_1])).
% 1.61/1.78  thf('85', plain,
% 1.61/1.78      ((~ (r1_tarski @ sk_A @ 
% 1.61/1.78           (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ (k2_relat_1 @ sk_B)))
% 1.61/1.78        | ((sk_A)
% 1.61/1.78            = (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ (k2_relat_1 @ sk_B))))),
% 1.61/1.78      inference('demod', [status(thm)], ['80', '81', '82', '83', '84'])).
% 1.61/1.78  thf('86', plain,
% 1.61/1.78      ((~ (r1_tarski @ sk_A @ 
% 1.61/1.78           (k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B))))
% 1.61/1.78        | ~ (v1_relat_1 @ sk_B)
% 1.61/1.78        | ((sk_A)
% 1.61/1.78            = (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ (k2_relat_1 @ sk_B))))),
% 1.61/1.78      inference('sup-', [status(thm)], ['75', '85'])).
% 1.61/1.78  thf('87', plain,
% 1.61/1.78      (![X0 : $i]:
% 1.61/1.78         ((r1_tarski @ (k1_relat_1 @ X0) @ 
% 1.61/1.78           (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 1.61/1.78          | ~ (v1_relat_1 @ X0))),
% 1.61/1.78      inference('simplify', [status(thm)], ['29'])).
% 1.61/1.78  thf('88', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 1.61/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.78  thf('89', plain,
% 1.61/1.78      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.61/1.78         (~ (r1_tarski @ X8 @ X9)
% 1.61/1.78          | ~ (r1_tarski @ X9 @ X10)
% 1.61/1.78          | (r1_tarski @ X8 @ X10))),
% 1.61/1.78      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.61/1.78  thf('90', plain,
% 1.61/1.78      (![X0 : $i]:
% 1.61/1.78         ((r1_tarski @ sk_A @ X0) | ~ (r1_tarski @ (k1_relat_1 @ sk_B) @ X0))),
% 1.61/1.78      inference('sup-', [status(thm)], ['88', '89'])).
% 1.61/1.78  thf('91', plain,
% 1.61/1.78      ((~ (v1_relat_1 @ sk_B)
% 1.61/1.78        | (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B))))),
% 1.61/1.78      inference('sup-', [status(thm)], ['87', '90'])).
% 1.61/1.78  thf('92', plain, ((v1_relat_1 @ sk_B)),
% 1.61/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.78  thf('93', plain,
% 1.61/1.78      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B)))),
% 1.61/1.78      inference('demod', [status(thm)], ['91', '92'])).
% 1.61/1.78  thf('94', plain,
% 1.61/1.78      (![X11 : $i, X12 : $i]:
% 1.61/1.78         (((k3_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_tarski @ X11 @ X12))),
% 1.61/1.78      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.61/1.78  thf('95', plain,
% 1.61/1.78      (((k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B)))
% 1.61/1.78         = (sk_A))),
% 1.61/1.78      inference('sup-', [status(thm)], ['93', '94'])).
% 1.61/1.78  thf('96', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.61/1.78      inference('simplify', [status(thm)], ['1'])).
% 1.61/1.78  thf('97', plain, ((v1_relat_1 @ sk_B)),
% 1.61/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.78  thf('98', plain,
% 1.61/1.78      (((sk_A)
% 1.61/1.78         = (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ (k2_relat_1 @ sk_B)))),
% 1.61/1.78      inference('demod', [status(thm)], ['86', '95', '96', '97'])).
% 1.61/1.78  thf('99', plain,
% 1.61/1.78      (((sk_A)
% 1.61/1.78         = (k1_relat_1 @ 
% 1.61/1.78            (k7_relat_1 @ (k6_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))))),
% 1.61/1.78      inference('demod', [status(thm)], ['74', '98'])).
% 1.61/1.78  thf('100', plain,
% 1.61/1.78      (![X42 : $i, X43 : $i]:
% 1.61/1.78         (~ (v1_relat_1 @ X42)
% 1.61/1.78          | ((k7_relat_1 @ X43 @ (k1_relat_1 @ X42))
% 1.61/1.78              = (k7_relat_1 @ X43 @ 
% 1.61/1.78                 (k1_relat_1 @ (k7_relat_1 @ X42 @ (k1_relat_1 @ X43)))))
% 1.61/1.78          | ~ (v1_relat_1 @ X43))),
% 1.61/1.78      inference('cnf', [status(esa)], [t189_relat_1])).
% 1.61/1.78  thf('101', plain,
% 1.61/1.78      (![X46 : $i, X47 : $i]:
% 1.61/1.78         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X46 @ X47)) @ X47)
% 1.61/1.78          | ~ (v1_relat_1 @ X46))),
% 1.61/1.78      inference('cnf', [status(esa)], [t87_relat_1])).
% 1.61/1.78  thf('102', plain,
% 1.61/1.78      (![X0 : $i, X1 : $i]:
% 1.61/1.78         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X1 @ (k1_relat_1 @ X0))) @ 
% 1.61/1.78           (k1_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X1))))
% 1.61/1.78          | ~ (v1_relat_1 @ X1)
% 1.61/1.78          | ~ (v1_relat_1 @ X0)
% 1.61/1.78          | ~ (v1_relat_1 @ X1))),
% 1.61/1.78      inference('sup+', [status(thm)], ['100', '101'])).
% 1.61/1.78  thf('103', plain,
% 1.61/1.78      (![X0 : $i, X1 : $i]:
% 1.61/1.78         (~ (v1_relat_1 @ X0)
% 1.61/1.78          | ~ (v1_relat_1 @ X1)
% 1.61/1.78          | (r1_tarski @ 
% 1.61/1.78             (k1_relat_1 @ (k7_relat_1 @ X1 @ (k1_relat_1 @ X0))) @ 
% 1.61/1.78             (k1_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X1)))))),
% 1.61/1.78      inference('simplify', [status(thm)], ['102'])).
% 1.61/1.78  thf('104', plain,
% 1.61/1.78      (((r1_tarski @ sk_A @ 
% 1.61/1.78         (k1_relat_1 @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ (k6_relat_1 @ sk_A)))))
% 1.61/1.78        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A))
% 1.61/1.78        | ~ (v1_relat_1 @ sk_B))),
% 1.61/1.78      inference('sup+', [status(thm)], ['99', '103'])).
% 1.61/1.78  thf('105', plain, (![X44 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X44)) = (X44))),
% 1.61/1.78      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.61/1.78  thf('106', plain, (![X49 : $i]: (v1_relat_1 @ (k6_relat_1 @ X49))),
% 1.61/1.78      inference('cnf', [status(esa)], [fc4_funct_1])).
% 1.61/1.78  thf('107', plain, ((v1_relat_1 @ sk_B)),
% 1.61/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.78  thf('108', plain,
% 1.61/1.78      ((r1_tarski @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 1.61/1.78      inference('demod', [status(thm)], ['104', '105', '106', '107'])).
% 1.61/1.78  thf('109', plain,
% 1.61/1.78      (![X46 : $i, X47 : $i]:
% 1.61/1.78         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X46 @ X47)) @ X47)
% 1.61/1.78          | ~ (v1_relat_1 @ X46))),
% 1.61/1.78      inference('cnf', [status(esa)], [t87_relat_1])).
% 1.61/1.78  thf('110', plain,
% 1.61/1.78      (![X0 : $i, X2 : $i]:
% 1.61/1.78         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.61/1.78      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.61/1.78  thf('111', plain,
% 1.61/1.78      (![X0 : $i, X1 : $i]:
% 1.61/1.78         (~ (v1_relat_1 @ X1)
% 1.61/1.78          | ~ (r1_tarski @ X0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 1.61/1.78          | ((X0) = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 1.61/1.78      inference('sup-', [status(thm)], ['109', '110'])).
% 1.61/1.78  thf('112', plain,
% 1.61/1.78      ((((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 1.61/1.78        | ~ (v1_relat_1 @ sk_B))),
% 1.61/1.78      inference('sup-', [status(thm)], ['108', '111'])).
% 1.61/1.78  thf('113', plain, ((v1_relat_1 @ sk_B)),
% 1.61/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.78  thf('114', plain, (((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 1.61/1.78      inference('demod', [status(thm)], ['112', '113'])).
% 1.61/1.78  thf(t146_relat_1, axiom,
% 1.61/1.78    (![A:$i]:
% 1.61/1.78     ( ( v1_relat_1 @ A ) =>
% 1.61/1.78       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 1.61/1.78  thf('115', plain,
% 1.61/1.78      (![X37 : $i]:
% 1.61/1.78         (((k9_relat_1 @ X37 @ (k1_relat_1 @ X37)) = (k2_relat_1 @ X37))
% 1.61/1.78          | ~ (v1_relat_1 @ X37))),
% 1.61/1.78      inference('cnf', [status(esa)], [t146_relat_1])).
% 1.61/1.78  thf('116', plain,
% 1.61/1.78      ((((k9_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ sk_A)
% 1.61/1.78          = (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 1.61/1.78        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 1.61/1.78      inference('sup+', [status(thm)], ['114', '115'])).
% 1.61/1.78  thf('117', plain,
% 1.61/1.78      ((~ (v1_relat_1 @ sk_B)
% 1.61/1.78        | ((k9_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ sk_A)
% 1.61/1.78            = (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))))),
% 1.61/1.78      inference('sup-', [status(thm)], ['5', '116'])).
% 1.61/1.78  thf('118', plain, ((v1_relat_1 @ sk_B)),
% 1.61/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.78  thf('119', plain,
% 1.61/1.78      (((k9_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ sk_A)
% 1.61/1.78         = (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 1.61/1.78      inference('demod', [status(thm)], ['117', '118'])).
% 1.61/1.78  thf('120', plain,
% 1.61/1.78      ((((k9_relat_1 @ sk_B @ sk_A) = (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 1.61/1.78        | ~ (v1_relat_1 @ sk_B))),
% 1.61/1.78      inference('sup+', [status(thm)], ['4', '119'])).
% 1.61/1.78  thf('121', plain, ((v1_relat_1 @ sk_B)),
% 1.61/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.78  thf('122', plain,
% 1.61/1.78      (((k9_relat_1 @ sk_B @ sk_A) = (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 1.61/1.78      inference('demod', [status(thm)], ['120', '121'])).
% 1.61/1.78  thf('123', plain,
% 1.61/1.78      (![X51 : $i, X52 : $i, X53 : $i]:
% 1.61/1.78         (((k10_relat_1 @ (k7_relat_1 @ X52 @ X51) @ X53)
% 1.61/1.78            = (k3_xboole_0 @ X51 @ (k10_relat_1 @ X52 @ X53)))
% 1.61/1.78          | ~ (v1_relat_1 @ X52))),
% 1.61/1.78      inference('cnf', [status(esa)], [t139_funct_1])).
% 1.61/1.78  thf('124', plain,
% 1.61/1.78      (![X41 : $i]:
% 1.61/1.78         (((k10_relat_1 @ X41 @ (k2_relat_1 @ X41)) = (k1_relat_1 @ X41))
% 1.61/1.78          | ~ (v1_relat_1 @ X41))),
% 1.61/1.78      inference('cnf', [status(esa)], [t169_relat_1])).
% 1.61/1.78  thf('125', plain,
% 1.61/1.78      (![X0 : $i, X1 : $i]:
% 1.61/1.78         (((k3_xboole_0 @ X0 @ 
% 1.61/1.78            (k10_relat_1 @ X1 @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X0))))
% 1.61/1.78            = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 1.61/1.78          | ~ (v1_relat_1 @ X1)
% 1.61/1.78          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 1.61/1.78      inference('sup+', [status(thm)], ['123', '124'])).
% 1.61/1.78  thf('126', plain,
% 1.61/1.78      (![X35 : $i, X36 : $i]:
% 1.61/1.78         (~ (v1_relat_1 @ X35) | (v1_relat_1 @ (k7_relat_1 @ X35 @ X36)))),
% 1.61/1.78      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 1.61/1.78  thf('127', plain,
% 1.61/1.78      (![X0 : $i, X1 : $i]:
% 1.61/1.78         (~ (v1_relat_1 @ X1)
% 1.61/1.78          | ((k3_xboole_0 @ X0 @ 
% 1.61/1.78              (k10_relat_1 @ X1 @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X0))))
% 1.61/1.78              = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 1.61/1.78      inference('clc', [status(thm)], ['125', '126'])).
% 1.61/1.78  thf('128', plain,
% 1.61/1.78      ((((k3_xboole_0 @ sk_A @ 
% 1.61/1.78          (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 1.61/1.78          = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 1.61/1.78        | ~ (v1_relat_1 @ sk_B))),
% 1.61/1.78      inference('sup+', [status(thm)], ['122', '127'])).
% 1.61/1.78  thf('129', plain, (((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 1.61/1.78      inference('demod', [status(thm)], ['112', '113'])).
% 1.61/1.78  thf('130', plain, ((v1_relat_1 @ sk_B)),
% 1.61/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.78  thf('131', plain,
% 1.61/1.78      (((k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 1.61/1.78         = (sk_A))),
% 1.61/1.78      inference('demod', [status(thm)], ['128', '129', '130'])).
% 1.61/1.78  thf('132', plain,
% 1.61/1.78      (![X6 : $i, X7 : $i]:
% 1.61/1.78         ((k4_xboole_0 @ X6 @ X7)
% 1.61/1.78           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 1.61/1.78      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.61/1.78  thf('133', plain,
% 1.61/1.78      (((k4_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 1.61/1.78         = (k5_xboole_0 @ sk_A @ sk_A))),
% 1.61/1.78      inference('sup+', [status(thm)], ['131', '132'])).
% 1.61/1.78  thf('134', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.61/1.78      inference('sup+', [status(thm)], ['19', '22'])).
% 1.61/1.78  thf('135', plain,
% 1.61/1.78      (((k4_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 1.61/1.78         = (k1_xboole_0))),
% 1.61/1.78      inference('demod', [status(thm)], ['133', '134'])).
% 1.61/1.78  thf('136', plain,
% 1.61/1.78      (![X3 : $i, X4 : $i]:
% 1.61/1.78         ((r1_tarski @ X3 @ X4) | ((k4_xboole_0 @ X3 @ X4) != (k1_xboole_0)))),
% 1.61/1.78      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.61/1.78  thf('137', plain,
% 1.61/1.78      ((((k1_xboole_0) != (k1_xboole_0))
% 1.61/1.78        | (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A))))),
% 1.61/1.78      inference('sup-', [status(thm)], ['135', '136'])).
% 1.61/1.78  thf('138', plain,
% 1.61/1.78      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 1.61/1.78      inference('simplify', [status(thm)], ['137'])).
% 1.61/1.78  thf('139', plain, ($false), inference('demod', [status(thm)], ['0', '138'])).
% 1.61/1.78  
% 1.61/1.78  % SZS output end Refutation
% 1.61/1.78  
% 1.61/1.79  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
