%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mmdL5kLAXC

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:55 EST 2020

% Result     : Theorem 0.62s
% Output     : Refutation 0.62s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 185 expanded)
%              Number of leaves         :   27 (  74 expanded)
%              Depth                    :   10
%              Number of atoms          :  713 (1403 expanded)
%              Number of equality atoms :   58 ( 117 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('0',plain,(
    ! [X60: $i,X61: $i] :
      ( ( ( k7_relat_1 @ X61 @ X60 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X60 ) @ X61 ) )
      | ~ ( v1_relat_1 @ X61 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

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
    ( ( ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
     != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('3',plain,(
    ! [X40: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('4',plain,(
    ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('6',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['5'])).

thf(t77_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B )
          = B ) ) ) )).

thf('7',plain,(
    ! [X53: $i,X54: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X53 ) @ X54 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X54 ) @ X53 )
        = X53 )
      | ~ ( v1_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t77_relat_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t123_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ B )
        = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ) )).

thf('9',plain,(
    ! [X41: $i,X42: $i] :
      ( ( ( k8_relat_1 @ X42 @ X41 )
        = ( k5_relat_1 @ X41 @ ( k6_relat_1 @ X42 ) ) )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t139_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( k8_relat_1 @ A @ ( k5_relat_1 @ B @ C ) )
            = ( k5_relat_1 @ B @ ( k8_relat_1 @ A @ C ) ) ) ) ) )).

thf('10',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( v1_relat_1 @ X43 )
      | ( ( k8_relat_1 @ X45 @ ( k5_relat_1 @ X44 @ X43 ) )
        = ( k5_relat_1 @ X44 @ ( k8_relat_1 @ X45 @ X43 ) ) )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t139_relat_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ X0 @ ( k8_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X40: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ X0 @ ( k8_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ X0 @ ( k8_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X41: $i,X42: $i] :
      ( ( ( k8_relat_1 @ X42 @ X41 )
        = ( k5_relat_1 @ X41 @ ( k6_relat_1 @ X42 ) ) )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('16',plain,(
    ! [X60: $i,X61: $i] :
      ( ( ( k7_relat_1 @ X61 @ X60 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X60 ) @ X61 ) )
      | ~ ( v1_relat_1 @ X61 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X40: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('19',plain,(
    ! [X40: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ X0 @ ( k7_relat_1 @ ( k6_relat_1 @ X2 ) @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['14','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ X1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ) )
        = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['8','21'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('23',plain,(
    ! [X49: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X49 ) )
      = X49 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('24',plain,(
    ! [X58: $i,X59: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X58 @ X59 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X58 ) @ X59 ) )
      | ~ ( v1_relat_1 @ X58 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( k3_xboole_0 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X40: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('29',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_tarski @ X8 @ X7 )
      = ( k2_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('30',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X36 @ X37 ) )
      = ( k3_xboole_0 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X36 @ X37 ) )
      = ( k3_xboole_0 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X41: $i,X42: $i] :
      ( ( ( k8_relat_1 @ X42 @ X41 )
        = ( k5_relat_1 @ X41 @ ( k6_relat_1 @ X42 ) ) )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('35',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('36',plain,(
    ! [X50: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X50 ) )
      = X50 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('37',plain,(
    ! [X55: $i,X56: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X55 ) @ X56 )
      | ( ( k5_relat_1 @ X55 @ ( k6_relat_1 @ X56 ) )
        = X55 )
      | ~ ( v1_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X40: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['35','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
        = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['34','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('44',plain,(
    ! [X40: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['33','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['33','45'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('50',plain,(
    ! [X41: $i,X42: $i] :
      ( ( ( k8_relat_1 @ X42 @ X41 )
        = ( k5_relat_1 @ X41 @ ( k6_relat_1 @ X42 ) ) )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('51',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( v1_relat_1 @ X38 )
      | ~ ( v1_relat_1 @ X39 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X38 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X40: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['49','55'])).

thf('57',plain,(
    ! [X40: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('60',plain,(
    ! [X40: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['22','27','28','46','47','48','58','59','60'])).

thf('62',plain,(
    ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
 != ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['4','61'])).

thf('63',plain,(
    $false ),
    inference(simplify,[status(thm)],['62'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mmdL5kLAXC
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:59:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.62/0.80  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.62/0.80  % Solved by: fo/fo7.sh
% 0.62/0.80  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.62/0.80  % done 596 iterations in 0.347s
% 0.62/0.80  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.62/0.80  % SZS output start Refutation
% 0.62/0.80  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.62/0.80  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.62/0.80  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.62/0.80  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.62/0.80  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.62/0.80  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.62/0.80  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.62/0.80  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.62/0.80  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.62/0.80  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.62/0.80  thf(sk_A_type, type, sk_A: $i).
% 0.62/0.80  thf(sk_B_type, type, sk_B: $i).
% 0.62/0.80  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.62/0.80  thf(t94_relat_1, axiom,
% 0.62/0.80    (![A:$i,B:$i]:
% 0.62/0.80     ( ( v1_relat_1 @ B ) =>
% 0.62/0.80       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.62/0.80  thf('0', plain,
% 0.62/0.80      (![X60 : $i, X61 : $i]:
% 0.62/0.80         (((k7_relat_1 @ X61 @ X60) = (k5_relat_1 @ (k6_relat_1 @ X60) @ X61))
% 0.62/0.80          | ~ (v1_relat_1 @ X61))),
% 0.62/0.80      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.62/0.80  thf(t43_funct_1, conjecture,
% 0.62/0.80    (![A:$i,B:$i]:
% 0.62/0.80     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.62/0.80       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.62/0.80  thf(zf_stmt_0, negated_conjecture,
% 0.62/0.80    (~( ![A:$i,B:$i]:
% 0.62/0.80        ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.62/0.80          ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 0.62/0.80    inference('cnf.neg', [status(esa)], [t43_funct_1])).
% 0.62/0.80  thf('1', plain,
% 0.62/0.80      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A))
% 0.62/0.80         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.62/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.80  thf('2', plain,
% 0.62/0.80      ((((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 0.62/0.80          != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))
% 0.62/0.80        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A)))),
% 0.62/0.80      inference('sup-', [status(thm)], ['0', '1'])).
% 0.62/0.80  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.62/0.80  thf('3', plain, (![X40 : $i]: (v1_relat_1 @ (k6_relat_1 @ X40))),
% 0.62/0.80      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.62/0.80  thf('4', plain,
% 0.62/0.80      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 0.62/0.80         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.62/0.80      inference('demod', [status(thm)], ['2', '3'])).
% 0.62/0.80  thf(d10_xboole_0, axiom,
% 0.62/0.80    (![A:$i,B:$i]:
% 0.62/0.80     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.62/0.80  thf('5', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.62/0.80      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.62/0.80  thf('6', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.62/0.80      inference('simplify', [status(thm)], ['5'])).
% 0.62/0.80  thf(t77_relat_1, axiom,
% 0.62/0.80    (![A:$i,B:$i]:
% 0.62/0.80     ( ( v1_relat_1 @ B ) =>
% 0.62/0.80       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.62/0.80         ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ) ))).
% 0.62/0.80  thf('7', plain,
% 0.62/0.80      (![X53 : $i, X54 : $i]:
% 0.62/0.80         (~ (r1_tarski @ (k1_relat_1 @ X53) @ X54)
% 0.62/0.80          | ((k5_relat_1 @ (k6_relat_1 @ X54) @ X53) = (X53))
% 0.62/0.80          | ~ (v1_relat_1 @ X53))),
% 0.62/0.80      inference('cnf', [status(esa)], [t77_relat_1])).
% 0.62/0.80  thf('8', plain,
% 0.62/0.80      (![X0 : $i]:
% 0.62/0.80         (~ (v1_relat_1 @ X0)
% 0.62/0.80          | ((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X0) = (X0)))),
% 0.62/0.80      inference('sup-', [status(thm)], ['6', '7'])).
% 0.62/0.80  thf(t123_relat_1, axiom,
% 0.62/0.80    (![A:$i,B:$i]:
% 0.62/0.80     ( ( v1_relat_1 @ B ) =>
% 0.62/0.80       ( ( k8_relat_1 @ A @ B ) = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ))).
% 0.62/0.80  thf('9', plain,
% 0.62/0.80      (![X41 : $i, X42 : $i]:
% 0.62/0.80         (((k8_relat_1 @ X42 @ X41) = (k5_relat_1 @ X41 @ (k6_relat_1 @ X42)))
% 0.62/0.80          | ~ (v1_relat_1 @ X41))),
% 0.62/0.80      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.62/0.80  thf(t139_relat_1, axiom,
% 0.62/0.80    (![A:$i,B:$i]:
% 0.62/0.80     ( ( v1_relat_1 @ B ) =>
% 0.62/0.80       ( ![C:$i]:
% 0.62/0.80         ( ( v1_relat_1 @ C ) =>
% 0.62/0.80           ( ( k8_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) =
% 0.62/0.80             ( k5_relat_1 @ B @ ( k8_relat_1 @ A @ C ) ) ) ) ) ))).
% 0.62/0.80  thf('10', plain,
% 0.62/0.80      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.62/0.80         (~ (v1_relat_1 @ X43)
% 0.62/0.80          | ((k8_relat_1 @ X45 @ (k5_relat_1 @ X44 @ X43))
% 0.62/0.80              = (k5_relat_1 @ X44 @ (k8_relat_1 @ X45 @ X43)))
% 0.62/0.80          | ~ (v1_relat_1 @ X44))),
% 0.62/0.80      inference('cnf', [status(esa)], [t139_relat_1])).
% 0.62/0.80  thf('11', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.62/0.80         (((k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ X0))
% 0.62/0.80            = (k5_relat_1 @ X0 @ (k8_relat_1 @ X2 @ (k6_relat_1 @ X1))))
% 0.62/0.80          | ~ (v1_relat_1 @ X0)
% 0.62/0.80          | ~ (v1_relat_1 @ X0)
% 0.62/0.80          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.62/0.80      inference('sup+', [status(thm)], ['9', '10'])).
% 0.62/0.80  thf('12', plain, (![X40 : $i]: (v1_relat_1 @ (k6_relat_1 @ X40))),
% 0.62/0.80      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.62/0.80  thf('13', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.62/0.80         (((k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ X0))
% 0.62/0.80            = (k5_relat_1 @ X0 @ (k8_relat_1 @ X2 @ (k6_relat_1 @ X1))))
% 0.62/0.80          | ~ (v1_relat_1 @ X0)
% 0.62/0.80          | ~ (v1_relat_1 @ X0))),
% 0.62/0.80      inference('demod', [status(thm)], ['11', '12'])).
% 0.62/0.80  thf('14', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.62/0.80         (~ (v1_relat_1 @ X0)
% 0.62/0.80          | ((k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ X0))
% 0.62/0.80              = (k5_relat_1 @ X0 @ (k8_relat_1 @ X2 @ (k6_relat_1 @ X1)))))),
% 0.62/0.80      inference('simplify', [status(thm)], ['13'])).
% 0.62/0.80  thf('15', plain,
% 0.62/0.80      (![X41 : $i, X42 : $i]:
% 0.62/0.80         (((k8_relat_1 @ X42 @ X41) = (k5_relat_1 @ X41 @ (k6_relat_1 @ X42)))
% 0.62/0.80          | ~ (v1_relat_1 @ X41))),
% 0.62/0.80      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.62/0.80  thf('16', plain,
% 0.62/0.80      (![X60 : $i, X61 : $i]:
% 0.62/0.80         (((k7_relat_1 @ X61 @ X60) = (k5_relat_1 @ (k6_relat_1 @ X60) @ X61))
% 0.62/0.80          | ~ (v1_relat_1 @ X61))),
% 0.62/0.80      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.62/0.80  thf('17', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i]:
% 0.62/0.80         (((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.62/0.80            = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.62/0.80          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.62/0.80          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.62/0.80      inference('sup+', [status(thm)], ['15', '16'])).
% 0.62/0.80  thf('18', plain, (![X40 : $i]: (v1_relat_1 @ (k6_relat_1 @ X40))),
% 0.62/0.80      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.62/0.80  thf('19', plain, (![X40 : $i]: (v1_relat_1 @ (k6_relat_1 @ X40))),
% 0.62/0.80      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.62/0.80  thf('20', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i]:
% 0.62/0.80         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.62/0.80           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.62/0.80      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.62/0.80  thf('21', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.62/0.80         (~ (v1_relat_1 @ X0)
% 0.62/0.80          | ((k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ X0))
% 0.62/0.80              = (k5_relat_1 @ X0 @ (k7_relat_1 @ (k6_relat_1 @ X2) @ X1))))),
% 0.62/0.80      inference('demod', [status(thm)], ['14', '20'])).
% 0.62/0.80  thf('22', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i]:
% 0.62/0.80         (((k8_relat_1 @ X1 @ 
% 0.62/0.80            (k8_relat_1 @ X0 @ 
% 0.62/0.80             (k6_relat_1 @ (k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))))
% 0.62/0.80            = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.62/0.80          | ~ (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.62/0.80          | ~ (v1_relat_1 @ 
% 0.62/0.80               (k6_relat_1 @ 
% 0.62/0.80                (k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))))),
% 0.62/0.80      inference('sup+', [status(thm)], ['8', '21'])).
% 0.62/0.80  thf(t71_relat_1, axiom,
% 0.62/0.80    (![A:$i]:
% 0.62/0.80     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.62/0.80       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.62/0.80  thf('23', plain, (![X49 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X49)) = (X49))),
% 0.62/0.80      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.62/0.80  thf(t90_relat_1, axiom,
% 0.62/0.80    (![A:$i,B:$i]:
% 0.62/0.80     ( ( v1_relat_1 @ B ) =>
% 0.62/0.80       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 0.62/0.80         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.62/0.80  thf('24', plain,
% 0.62/0.80      (![X58 : $i, X59 : $i]:
% 0.62/0.80         (((k1_relat_1 @ (k7_relat_1 @ X58 @ X59))
% 0.62/0.80            = (k3_xboole_0 @ (k1_relat_1 @ X58) @ X59))
% 0.62/0.80          | ~ (v1_relat_1 @ X58))),
% 0.62/0.80      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.62/0.80  thf('25', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i]:
% 0.62/0.80         (((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.62/0.80            = (k3_xboole_0 @ X0 @ X1))
% 0.62/0.80          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.62/0.80      inference('sup+', [status(thm)], ['23', '24'])).
% 0.62/0.80  thf('26', plain, (![X40 : $i]: (v1_relat_1 @ (k6_relat_1 @ X40))),
% 0.62/0.80      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.62/0.80  thf('27', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i]:
% 0.62/0.80         ((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.62/0.80           = (k3_xboole_0 @ X0 @ X1))),
% 0.62/0.80      inference('demod', [status(thm)], ['25', '26'])).
% 0.62/0.80  thf('28', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i]:
% 0.62/0.80         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.62/0.80           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.62/0.80      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.62/0.80  thf(commutativity_k2_tarski, axiom,
% 0.62/0.80    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.62/0.80  thf('29', plain,
% 0.62/0.80      (![X7 : $i, X8 : $i]: ((k2_tarski @ X8 @ X7) = (k2_tarski @ X7 @ X8))),
% 0.62/0.80      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.62/0.80  thf(t12_setfam_1, axiom,
% 0.62/0.80    (![A:$i,B:$i]:
% 0.62/0.80     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.62/0.80  thf('30', plain,
% 0.62/0.80      (![X36 : $i, X37 : $i]:
% 0.62/0.80         ((k1_setfam_1 @ (k2_tarski @ X36 @ X37)) = (k3_xboole_0 @ X36 @ X37))),
% 0.62/0.80      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.62/0.80  thf('31', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i]:
% 0.62/0.80         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.62/0.80      inference('sup+', [status(thm)], ['29', '30'])).
% 0.62/0.80  thf('32', plain,
% 0.62/0.80      (![X36 : $i, X37 : $i]:
% 0.62/0.80         ((k1_setfam_1 @ (k2_tarski @ X36 @ X37)) = (k3_xboole_0 @ X36 @ X37))),
% 0.62/0.80      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.62/0.80  thf('33', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.62/0.80      inference('sup+', [status(thm)], ['31', '32'])).
% 0.62/0.80  thf('34', plain,
% 0.62/0.80      (![X41 : $i, X42 : $i]:
% 0.62/0.80         (((k8_relat_1 @ X42 @ X41) = (k5_relat_1 @ X41 @ (k6_relat_1 @ X42)))
% 0.62/0.80          | ~ (v1_relat_1 @ X41))),
% 0.62/0.80      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.62/0.80  thf(t17_xboole_1, axiom,
% 0.62/0.80    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.62/0.80  thf('35', plain,
% 0.62/0.80      (![X3 : $i, X4 : $i]: (r1_tarski @ (k3_xboole_0 @ X3 @ X4) @ X3)),
% 0.62/0.80      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.62/0.80  thf('36', plain, (![X50 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X50)) = (X50))),
% 0.62/0.80      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.62/0.80  thf(t79_relat_1, axiom,
% 0.62/0.80    (![A:$i,B:$i]:
% 0.62/0.80     ( ( v1_relat_1 @ B ) =>
% 0.62/0.80       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.62/0.80         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 0.62/0.80  thf('37', plain,
% 0.62/0.80      (![X55 : $i, X56 : $i]:
% 0.62/0.80         (~ (r1_tarski @ (k2_relat_1 @ X55) @ X56)
% 0.62/0.80          | ((k5_relat_1 @ X55 @ (k6_relat_1 @ X56)) = (X55))
% 0.62/0.80          | ~ (v1_relat_1 @ X55))),
% 0.62/0.80      inference('cnf', [status(esa)], [t79_relat_1])).
% 0.62/0.80  thf('38', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i]:
% 0.62/0.80         (~ (r1_tarski @ X0 @ X1)
% 0.62/0.80          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.62/0.80          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 0.62/0.80              = (k6_relat_1 @ X0)))),
% 0.62/0.80      inference('sup-', [status(thm)], ['36', '37'])).
% 0.62/0.80  thf('39', plain, (![X40 : $i]: (v1_relat_1 @ (k6_relat_1 @ X40))),
% 0.62/0.80      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.62/0.80  thf('40', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i]:
% 0.62/0.80         (~ (r1_tarski @ X0 @ X1)
% 0.62/0.80          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 0.62/0.80              = (k6_relat_1 @ X0)))),
% 0.62/0.80      inference('demod', [status(thm)], ['38', '39'])).
% 0.62/0.80  thf('41', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i]:
% 0.62/0.80         ((k5_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 0.62/0.80           (k6_relat_1 @ X0)) = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.62/0.80      inference('sup-', [status(thm)], ['35', '40'])).
% 0.62/0.80  thf('42', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i]:
% 0.62/0.80         (((k8_relat_1 @ X1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.62/0.80            = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.62/0.80          | ~ (v1_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.62/0.80      inference('sup+', [status(thm)], ['34', '41'])).
% 0.62/0.80  thf('43', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i]:
% 0.62/0.80         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.62/0.80           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.62/0.80      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.62/0.80  thf('44', plain, (![X40 : $i]: (v1_relat_1 @ (k6_relat_1 @ X40))),
% 0.62/0.80      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.62/0.80  thf('45', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i]:
% 0.62/0.80         ((k7_relat_1 @ (k6_relat_1 @ X1) @ (k3_xboole_0 @ X1 @ X0))
% 0.62/0.80           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.62/0.80      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.62/0.80  thf('46', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i]:
% 0.62/0.80         ((k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 0.62/0.80           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.62/0.80      inference('sup+', [status(thm)], ['33', '45'])).
% 0.62/0.80  thf('47', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i]:
% 0.62/0.80         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.62/0.80           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.62/0.80      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.62/0.80  thf('48', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i]:
% 0.62/0.80         ((k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 0.62/0.80           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.62/0.80      inference('sup+', [status(thm)], ['33', '45'])).
% 0.62/0.80  thf('49', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i]:
% 0.62/0.80         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.62/0.80           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.62/0.80      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.62/0.80  thf('50', plain,
% 0.62/0.80      (![X41 : $i, X42 : $i]:
% 0.62/0.80         (((k8_relat_1 @ X42 @ X41) = (k5_relat_1 @ X41 @ (k6_relat_1 @ X42)))
% 0.62/0.80          | ~ (v1_relat_1 @ X41))),
% 0.62/0.80      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.62/0.80  thf(dt_k5_relat_1, axiom,
% 0.62/0.80    (![A:$i,B:$i]:
% 0.62/0.80     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.62/0.80       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.62/0.80  thf('51', plain,
% 0.62/0.80      (![X38 : $i, X39 : $i]:
% 0.62/0.80         (~ (v1_relat_1 @ X38)
% 0.62/0.80          | ~ (v1_relat_1 @ X39)
% 0.62/0.80          | (v1_relat_1 @ (k5_relat_1 @ X38 @ X39)))),
% 0.62/0.80      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.62/0.80  thf('52', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i]:
% 0.62/0.80         ((v1_relat_1 @ (k8_relat_1 @ X1 @ X0))
% 0.62/0.80          | ~ (v1_relat_1 @ X0)
% 0.62/0.80          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.62/0.80          | ~ (v1_relat_1 @ X0))),
% 0.62/0.80      inference('sup+', [status(thm)], ['50', '51'])).
% 0.62/0.80  thf('53', plain, (![X40 : $i]: (v1_relat_1 @ (k6_relat_1 @ X40))),
% 0.62/0.80      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.62/0.80  thf('54', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i]:
% 0.62/0.80         ((v1_relat_1 @ (k8_relat_1 @ X1 @ X0))
% 0.62/0.80          | ~ (v1_relat_1 @ X0)
% 0.62/0.80          | ~ (v1_relat_1 @ X0))),
% 0.62/0.80      inference('demod', [status(thm)], ['52', '53'])).
% 0.62/0.80  thf('55', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i]:
% 0.62/0.80         (~ (v1_relat_1 @ X0) | (v1_relat_1 @ (k8_relat_1 @ X1 @ X0)))),
% 0.62/0.80      inference('simplify', [status(thm)], ['54'])).
% 0.62/0.80  thf('56', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i]:
% 0.62/0.80         ((v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.62/0.80          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.62/0.80      inference('sup+', [status(thm)], ['49', '55'])).
% 0.62/0.80  thf('57', plain, (![X40 : $i]: (v1_relat_1 @ (k6_relat_1 @ X40))),
% 0.62/0.80      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.62/0.80  thf('58', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i]:
% 0.62/0.80         (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 0.62/0.80      inference('demod', [status(thm)], ['56', '57'])).
% 0.62/0.80  thf('59', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i]:
% 0.62/0.80         ((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.62/0.80           = (k3_xboole_0 @ X0 @ X1))),
% 0.62/0.80      inference('demod', [status(thm)], ['25', '26'])).
% 0.62/0.80  thf('60', plain, (![X40 : $i]: (v1_relat_1 @ (k6_relat_1 @ X40))),
% 0.62/0.80      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.62/0.80  thf('61', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i]:
% 0.62/0.80         ((k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))
% 0.62/0.80           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 0.62/0.80      inference('demod', [status(thm)],
% 0.62/0.80                ['22', '27', '28', '46', '47', '48', '58', '59', '60'])).
% 0.62/0.80  thf('62', plain,
% 0.62/0.80      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 0.62/0.80         != (k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))),
% 0.62/0.80      inference('demod', [status(thm)], ['4', '61'])).
% 0.62/0.80  thf('63', plain, ($false), inference('simplify', [status(thm)], ['62'])).
% 0.62/0.80  
% 0.62/0.80  % SZS output end Refutation
% 0.62/0.80  
% 0.62/0.81  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
