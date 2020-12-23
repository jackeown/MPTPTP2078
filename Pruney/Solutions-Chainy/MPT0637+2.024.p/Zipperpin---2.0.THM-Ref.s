%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cQsMCNWsDp

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:58 EST 2020

% Result     : Theorem 1.38s
% Output     : Refutation 1.38s
% Verified   : 
% Statistics : Number of formulae       :  163 ( 466 expanded)
%              Number of leaves         :   32 ( 180 expanded)
%              Depth                    :   16
%              Number of atoms          : 1361 (3686 expanded)
%              Number of equality atoms :  111 ( 312 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t123_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ B )
        = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k8_relat_1 @ X21 @ X20 )
        = ( k5_relat_1 @ X20 @ ( k6_relat_1 @ X21 ) ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
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

thf('5',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k8_relat_1 @ X21 @ X20 )
        = ( k5_relat_1 @ X20 @ ( k6_relat_1 @ X21 ) ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('6',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k7_relat_1 @ X38 @ X37 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X37 ) @ X38 ) )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('9',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf(t140_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ ( k8_relat_1 @ A @ C ) @ B )
        = ( k8_relat_1 @ A @ ( k7_relat_1 @ C @ B ) ) ) ) )).

thf('11',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k7_relat_1 @ ( k8_relat_1 @ X22 @ X23 ) @ X24 )
        = ( k8_relat_1 @ X22 @ ( k7_relat_1 @ X23 @ X24 ) ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t140_relat_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k8_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) @ X0 )
        = ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k8_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) @ X0 )
      = ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf(t100_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('16',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X14 @ X15 ) @ X16 )
        = ( k7_relat_1 @ X14 @ ( k3_xboole_0 @ X15 @ X16 ) ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X2 )
        = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k3_xboole_0 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('19',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X2 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X2 ) ) ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k8_relat_1 @ X2 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['14','20'])).

thf('22',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k8_relat_1 @ X21 @ X20 )
        = ( k5_relat_1 @ X20 @ ( k6_relat_1 @ X21 ) ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('23',plain,(
    ! [X30: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X30 ) )
      = X30 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('24',plain,(
    ! [X36: $i] :
      ( ( ( k5_relat_1 @ X36 @ ( k6_relat_1 @ ( k2_relat_1 @ X36 ) ) )
        = X36 )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','27'])).

thf('29',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','30'])).

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
    ! [X36: $i] :
      ( ( ( k5_relat_1 @ X36 @ ( k6_relat_1 @ ( k2_relat_1 @ X36 ) ) )
        = X36 )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('38',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k7_relat_1 @ X38 @ X37 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X37 ) @ X38 ) )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) ) @ X0 )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X30: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X30 ) )
      = X30 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('41',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('42',plain,(
    ! [X30: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X30 ) )
      = X30 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('43',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['39','40','41','42','43'])).

thf('45',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X14 @ X15 ) @ X16 )
        = ( k7_relat_1 @ X14 @ ( k3_xboole_0 @ X15 @ X16 ) ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['36','51'])).

thf('53',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k8_relat_1 @ X21 @ X20 )
        = ( k5_relat_1 @ X20 @ ( k6_relat_1 @ X21 ) ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('54',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k7_relat_1 @ X38 @ X37 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X37 ) @ X38 ) )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t72_relat_1,axiom,(
    ! [A: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ A ) ) )).

thf('55',plain,(
    ! [X31: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ X31 ) )
      = ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t72_relat_1])).

thf(t54_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('56',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v1_relat_1 @ X27 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X28 @ X27 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X27 ) @ ( k4_relat_1 @ X28 ) ) )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k4_relat_1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['54','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('62',plain,(
    ! [X31: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ X31 ) )
      = ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t72_relat_1])).

thf('63',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('64',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['60','61','62','63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
        = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['53','65'])).

thf('67',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k8_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['52','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X36: $i] :
      ( ( ( k5_relat_1 @ X36 @ ( k6_relat_1 @ ( k2_relat_1 @ X36 ) ) )
        = X36 )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf(t76_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B )
        & ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ) )).

thf('73',plain,(
    ! [X32: $i,X33: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ X33 ) @ X32 ) @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t76_relat_1])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X30: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X30 ) )
      = X30 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('76',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('77',plain,(
    ! [X30: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X30 ) )
      = X30 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('78',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('79',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['74','75','76','77','78'])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('80',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v1_relat_1 @ X25 )
      | ( r1_tarski @ ( k2_relat_1 @ X26 ) @ ( k2_relat_1 @ X25 ) )
      | ~ ( r1_tarski @ X26 @ X25 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('83',plain,(
    ! [X30: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X30 ) )
      = X30 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('84',plain,(
    ! [X30: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X30 ) )
      = X30 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('85',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('86',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(demod,[status(thm)],['81','82','83','84','85'])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('87',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X39 ) @ X40 )
      | ( ( k7_relat_1 @ X39 @ X40 )
        = X39 )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('88',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k7_relat_1 @ X38 @ X37 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X37 ) @ X38 ) )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('90',plain,(
    ! [X32: $i,X33: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ X33 ) @ X32 ) @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t76_relat_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k3_xboole_0 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X0 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k3_xboole_0 @ X0 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['89','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k3_xboole_0 @ X1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X0 )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['88','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(demod,[status(thm)],['81','82','83','84','85'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['97','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k8_relat_1 @ X21 @ X20 )
        = ( k5_relat_1 @ X20 @ ( k6_relat_1 @ X21 ) ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t112_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( k7_relat_1 @ ( k5_relat_1 @ B @ C ) @ A )
            = ( k5_relat_1 @ ( k7_relat_1 @ B @ A ) @ C ) ) ) ) )).

thf('104',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ( ( k7_relat_1 @ ( k5_relat_1 @ X18 @ X17 ) @ X19 )
        = ( k5_relat_1 @ ( k7_relat_1 @ X18 @ X19 ) @ X17 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t112_relat_1])).

thf('105',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X2 ) ) @ X0 )
        = ( k8_relat_1 @ X2 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('107',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X2 ) ) @ X0 )
        = ( k8_relat_1 @ X2 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k7_relat_1 @ X38 @ X37 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X37 ) @ X38 ) )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k3_xboole_0 @ X0 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf(fc1_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('110',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[fc1_relat_1])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['108','112'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k7_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X2 ) ) @ X0 )
        = ( k8_relat_1 @ X2 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['107','114'])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k8_relat_1 @ X0 @ ( k7_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['102','115'])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('118',plain,(
    ! [X29: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X29 ) )
      = X29 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('120',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('121',plain,(
    ! [X29: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X29 ) )
      = X29 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('122',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ X0 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['116','117','118','119','120','121','122'])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k8_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['71','123'])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k8_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['31','126'])).

thf('128',plain,(
    ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ sk_B ) )
 != ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','127'])).

thf('129',plain,(
    $false ),
    inference(simplify,[status(thm)],['128'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cQsMCNWsDp
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:56:21 EST 2020
% 0.21/0.35  % CPUTime    : 
% 0.21/0.35  % Running portfolio for 600 s
% 0.21/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.21/0.35  % Number of cores: 8
% 0.21/0.35  % Python version: Python 3.6.8
% 0.21/0.36  % Running in FO mode
% 1.38/1.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.38/1.59  % Solved by: fo/fo7.sh
% 1.38/1.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.38/1.59  % done 1587 iterations in 1.122s
% 1.38/1.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.38/1.59  % SZS output start Refutation
% 1.38/1.59  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.38/1.59  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.38/1.59  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 1.38/1.59  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.38/1.59  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.38/1.59  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.38/1.59  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 1.38/1.59  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.38/1.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.38/1.59  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 1.38/1.59  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 1.38/1.59  thf(sk_B_type, type, sk_B: $i).
% 1.38/1.59  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.38/1.59  thf(sk_A_type, type, sk_A: $i).
% 1.38/1.59  thf(t123_relat_1, axiom,
% 1.38/1.59    (![A:$i,B:$i]:
% 1.38/1.59     ( ( v1_relat_1 @ B ) =>
% 1.38/1.59       ( ( k8_relat_1 @ A @ B ) = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ))).
% 1.38/1.59  thf('0', plain,
% 1.38/1.59      (![X20 : $i, X21 : $i]:
% 1.38/1.59         (((k8_relat_1 @ X21 @ X20) = (k5_relat_1 @ X20 @ (k6_relat_1 @ X21)))
% 1.38/1.59          | ~ (v1_relat_1 @ X20))),
% 1.38/1.59      inference('cnf', [status(esa)], [t123_relat_1])).
% 1.38/1.59  thf(t43_funct_1, conjecture,
% 1.38/1.59    (![A:$i,B:$i]:
% 1.38/1.59     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 1.38/1.59       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.38/1.59  thf(zf_stmt_0, negated_conjecture,
% 1.38/1.59    (~( ![A:$i,B:$i]:
% 1.38/1.59        ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 1.38/1.59          ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 1.38/1.59    inference('cnf.neg', [status(esa)], [t43_funct_1])).
% 1.38/1.59  thf('1', plain,
% 1.38/1.59      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A))
% 1.38/1.59         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 1.38/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.59  thf('2', plain,
% 1.38/1.59      ((((k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B))
% 1.38/1.59          != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))
% 1.38/1.59        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_B)))),
% 1.38/1.59      inference('sup-', [status(thm)], ['0', '1'])).
% 1.38/1.59  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 1.38/1.59  thf('3', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 1.38/1.59      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.38/1.59  thf('4', plain,
% 1.38/1.59      (((k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B))
% 1.38/1.59         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 1.38/1.59      inference('demod', [status(thm)], ['2', '3'])).
% 1.38/1.59  thf('5', plain,
% 1.38/1.59      (![X20 : $i, X21 : $i]:
% 1.38/1.59         (((k8_relat_1 @ X21 @ X20) = (k5_relat_1 @ X20 @ (k6_relat_1 @ X21)))
% 1.38/1.59          | ~ (v1_relat_1 @ X20))),
% 1.38/1.59      inference('cnf', [status(esa)], [t123_relat_1])).
% 1.38/1.59  thf(t94_relat_1, axiom,
% 1.38/1.59    (![A:$i,B:$i]:
% 1.38/1.59     ( ( v1_relat_1 @ B ) =>
% 1.38/1.59       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 1.38/1.59  thf('6', plain,
% 1.38/1.59      (![X37 : $i, X38 : $i]:
% 1.38/1.59         (((k7_relat_1 @ X38 @ X37) = (k5_relat_1 @ (k6_relat_1 @ X37) @ X38))
% 1.38/1.59          | ~ (v1_relat_1 @ X38))),
% 1.38/1.59      inference('cnf', [status(esa)], [t94_relat_1])).
% 1.38/1.59  thf('7', plain,
% 1.38/1.59      (![X0 : $i, X1 : $i]:
% 1.38/1.59         (((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 1.38/1.59            = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 1.38/1.59          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 1.38/1.59          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 1.38/1.59      inference('sup+', [status(thm)], ['5', '6'])).
% 1.38/1.59  thf('8', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 1.38/1.59      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.38/1.59  thf('9', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 1.38/1.59      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.38/1.59  thf('10', plain,
% 1.38/1.59      (![X0 : $i, X1 : $i]:
% 1.38/1.59         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 1.38/1.59           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 1.38/1.59      inference('demod', [status(thm)], ['7', '8', '9'])).
% 1.38/1.59  thf(t140_relat_1, axiom,
% 1.38/1.59    (![A:$i,B:$i,C:$i]:
% 1.38/1.59     ( ( v1_relat_1 @ C ) =>
% 1.38/1.59       ( ( k7_relat_1 @ ( k8_relat_1 @ A @ C ) @ B ) =
% 1.38/1.59         ( k8_relat_1 @ A @ ( k7_relat_1 @ C @ B ) ) ) ))).
% 1.38/1.59  thf('11', plain,
% 1.38/1.59      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.38/1.59         (((k7_relat_1 @ (k8_relat_1 @ X22 @ X23) @ X24)
% 1.38/1.59            = (k8_relat_1 @ X22 @ (k7_relat_1 @ X23 @ X24)))
% 1.38/1.59          | ~ (v1_relat_1 @ X23))),
% 1.38/1.59      inference('cnf', [status(esa)], [t140_relat_1])).
% 1.38/1.59  thf('12', plain,
% 1.38/1.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.38/1.59         (((k7_relat_1 @ (k8_relat_1 @ X2 @ (k6_relat_1 @ X1)) @ X0)
% 1.38/1.59            = (k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))
% 1.38/1.59          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 1.38/1.59      inference('sup+', [status(thm)], ['10', '11'])).
% 1.38/1.59  thf('13', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 1.38/1.59      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.38/1.59  thf('14', plain,
% 1.38/1.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.38/1.59         ((k7_relat_1 @ (k8_relat_1 @ X2 @ (k6_relat_1 @ X1)) @ X0)
% 1.38/1.59           = (k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 1.38/1.59      inference('demod', [status(thm)], ['12', '13'])).
% 1.38/1.59  thf('15', plain,
% 1.38/1.59      (![X0 : $i, X1 : $i]:
% 1.38/1.59         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 1.38/1.59           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 1.38/1.59      inference('demod', [status(thm)], ['7', '8', '9'])).
% 1.38/1.59  thf(t100_relat_1, axiom,
% 1.38/1.59    (![A:$i,B:$i,C:$i]:
% 1.38/1.59     ( ( v1_relat_1 @ C ) =>
% 1.38/1.59       ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 1.38/1.59         ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 1.38/1.59  thf('16', plain,
% 1.38/1.59      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.38/1.59         (((k7_relat_1 @ (k7_relat_1 @ X14 @ X15) @ X16)
% 1.38/1.59            = (k7_relat_1 @ X14 @ (k3_xboole_0 @ X15 @ X16)))
% 1.38/1.59          | ~ (v1_relat_1 @ X14))),
% 1.38/1.59      inference('cnf', [status(esa)], [t100_relat_1])).
% 1.38/1.59  thf('17', plain,
% 1.38/1.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.38/1.59         (((k7_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ X2)
% 1.38/1.59            = (k7_relat_1 @ (k6_relat_1 @ X1) @ (k3_xboole_0 @ X0 @ X2)))
% 1.38/1.59          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 1.38/1.59      inference('sup+', [status(thm)], ['15', '16'])).
% 1.38/1.59  thf('18', plain,
% 1.38/1.59      (![X0 : $i, X1 : $i]:
% 1.38/1.59         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 1.38/1.59           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 1.38/1.59      inference('demod', [status(thm)], ['7', '8', '9'])).
% 1.38/1.59  thf('19', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 1.38/1.59      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.38/1.59  thf('20', plain,
% 1.38/1.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.38/1.59         ((k7_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ X2)
% 1.38/1.59           = (k8_relat_1 @ X1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X2))))),
% 1.38/1.59      inference('demod', [status(thm)], ['17', '18', '19'])).
% 1.38/1.59  thf('21', plain,
% 1.38/1.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.38/1.59         ((k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 1.38/1.59           = (k8_relat_1 @ X2 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))),
% 1.38/1.59      inference('sup+', [status(thm)], ['14', '20'])).
% 1.38/1.59  thf('22', plain,
% 1.38/1.59      (![X20 : $i, X21 : $i]:
% 1.38/1.59         (((k8_relat_1 @ X21 @ X20) = (k5_relat_1 @ X20 @ (k6_relat_1 @ X21)))
% 1.38/1.59          | ~ (v1_relat_1 @ X20))),
% 1.38/1.59      inference('cnf', [status(esa)], [t123_relat_1])).
% 1.38/1.59  thf(t71_relat_1, axiom,
% 1.38/1.59    (![A:$i]:
% 1.38/1.59     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 1.38/1.59       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 1.38/1.59  thf('23', plain, (![X30 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X30)) = (X30))),
% 1.38/1.59      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.38/1.59  thf(t80_relat_1, axiom,
% 1.38/1.59    (![A:$i]:
% 1.38/1.59     ( ( v1_relat_1 @ A ) =>
% 1.38/1.59       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 1.38/1.59  thf('24', plain,
% 1.38/1.59      (![X36 : $i]:
% 1.38/1.59         (((k5_relat_1 @ X36 @ (k6_relat_1 @ (k2_relat_1 @ X36))) = (X36))
% 1.38/1.59          | ~ (v1_relat_1 @ X36))),
% 1.38/1.59      inference('cnf', [status(esa)], [t80_relat_1])).
% 1.38/1.59  thf('25', plain,
% 1.38/1.59      (![X0 : $i]:
% 1.38/1.59         (((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 1.38/1.59            = (k6_relat_1 @ X0))
% 1.38/1.59          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 1.38/1.59      inference('sup+', [status(thm)], ['23', '24'])).
% 1.38/1.59  thf('26', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 1.38/1.59      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.38/1.59  thf('27', plain,
% 1.38/1.59      (![X0 : $i]:
% 1.38/1.59         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 1.38/1.59           = (k6_relat_1 @ X0))),
% 1.38/1.59      inference('demod', [status(thm)], ['25', '26'])).
% 1.38/1.59  thf('28', plain,
% 1.38/1.59      (![X0 : $i]:
% 1.38/1.59         (((k8_relat_1 @ X0 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0))
% 1.38/1.59          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 1.38/1.59      inference('sup+', [status(thm)], ['22', '27'])).
% 1.38/1.59  thf('29', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 1.38/1.59      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.38/1.59  thf('30', plain,
% 1.38/1.59      (![X0 : $i]: ((k8_relat_1 @ X0 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0))),
% 1.38/1.59      inference('demod', [status(thm)], ['28', '29'])).
% 1.38/1.59  thf('31', plain,
% 1.38/1.59      (![X0 : $i, X1 : $i]:
% 1.38/1.59         ((k8_relat_1 @ (k3_xboole_0 @ X1 @ X0) @ 
% 1.38/1.59           (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 1.38/1.59           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.38/1.59      inference('sup+', [status(thm)], ['21', '30'])).
% 1.38/1.59  thf(commutativity_k2_tarski, axiom,
% 1.38/1.59    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 1.38/1.59  thf('32', plain,
% 1.38/1.59      (![X2 : $i, X3 : $i]: ((k2_tarski @ X3 @ X2) = (k2_tarski @ X2 @ X3))),
% 1.38/1.59      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.38/1.59  thf(t12_setfam_1, axiom,
% 1.38/1.59    (![A:$i,B:$i]:
% 1.38/1.59     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.38/1.59  thf('33', plain,
% 1.38/1.59      (![X9 : $i, X10 : $i]:
% 1.38/1.59         ((k1_setfam_1 @ (k2_tarski @ X9 @ X10)) = (k3_xboole_0 @ X9 @ X10))),
% 1.38/1.59      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.38/1.59  thf('34', plain,
% 1.38/1.59      (![X0 : $i, X1 : $i]:
% 1.38/1.59         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 1.38/1.59      inference('sup+', [status(thm)], ['32', '33'])).
% 1.38/1.59  thf('35', plain,
% 1.38/1.59      (![X9 : $i, X10 : $i]:
% 1.38/1.59         ((k1_setfam_1 @ (k2_tarski @ X9 @ X10)) = (k3_xboole_0 @ X9 @ X10))),
% 1.38/1.59      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.38/1.59  thf('36', plain,
% 1.38/1.59      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.38/1.59      inference('sup+', [status(thm)], ['34', '35'])).
% 1.38/1.59  thf('37', plain,
% 1.38/1.59      (![X36 : $i]:
% 1.38/1.59         (((k5_relat_1 @ X36 @ (k6_relat_1 @ (k2_relat_1 @ X36))) = (X36))
% 1.38/1.59          | ~ (v1_relat_1 @ X36))),
% 1.38/1.59      inference('cnf', [status(esa)], [t80_relat_1])).
% 1.38/1.59  thf('38', plain,
% 1.38/1.59      (![X37 : $i, X38 : $i]:
% 1.38/1.59         (((k7_relat_1 @ X38 @ X37) = (k5_relat_1 @ (k6_relat_1 @ X37) @ X38))
% 1.38/1.59          | ~ (v1_relat_1 @ X38))),
% 1.38/1.59      inference('cnf', [status(esa)], [t94_relat_1])).
% 1.38/1.59  thf('39', plain,
% 1.38/1.59      (![X0 : $i]:
% 1.38/1.59         (((k7_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ (k6_relat_1 @ X0))) @ X0)
% 1.38/1.59            = (k6_relat_1 @ X0))
% 1.38/1.59          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 1.38/1.59          | ~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ (k6_relat_1 @ X0)))))),
% 1.38/1.59      inference('sup+', [status(thm)], ['37', '38'])).
% 1.38/1.59  thf('40', plain, (![X30 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X30)) = (X30))),
% 1.38/1.59      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.38/1.59  thf('41', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 1.38/1.59      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.38/1.59  thf('42', plain, (![X30 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X30)) = (X30))),
% 1.38/1.59      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.38/1.59  thf('43', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 1.38/1.59      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.38/1.59  thf('44', plain,
% 1.38/1.59      (![X0 : $i]: ((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 1.38/1.59      inference('demod', [status(thm)], ['39', '40', '41', '42', '43'])).
% 1.38/1.59  thf('45', plain,
% 1.38/1.59      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.38/1.59         (((k7_relat_1 @ (k7_relat_1 @ X14 @ X15) @ X16)
% 1.38/1.59            = (k7_relat_1 @ X14 @ (k3_xboole_0 @ X15 @ X16)))
% 1.38/1.59          | ~ (v1_relat_1 @ X14))),
% 1.38/1.59      inference('cnf', [status(esa)], [t100_relat_1])).
% 1.38/1.59  thf('46', plain,
% 1.38/1.59      (![X0 : $i, X1 : $i]:
% 1.38/1.59         (((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 1.38/1.59            = (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))
% 1.38/1.59          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 1.38/1.59      inference('sup+', [status(thm)], ['44', '45'])).
% 1.38/1.59  thf('47', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 1.38/1.59      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.38/1.59  thf('48', plain,
% 1.38/1.59      (![X0 : $i, X1 : $i]:
% 1.38/1.59         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 1.38/1.59           = (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 1.38/1.59      inference('demod', [status(thm)], ['46', '47'])).
% 1.38/1.59  thf('49', plain,
% 1.38/1.59      (![X0 : $i, X1 : $i]:
% 1.38/1.59         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 1.38/1.59           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 1.38/1.59      inference('demod', [status(thm)], ['7', '8', '9'])).
% 1.38/1.59  thf('50', plain,
% 1.38/1.59      (![X0 : $i, X1 : $i]:
% 1.38/1.59         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 1.38/1.59           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 1.38/1.59      inference('demod', [status(thm)], ['7', '8', '9'])).
% 1.38/1.59  thf('51', plain,
% 1.38/1.59      (![X0 : $i, X1 : $i]:
% 1.38/1.59         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 1.38/1.59           = (k8_relat_1 @ X0 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1))))),
% 1.38/1.59      inference('demod', [status(thm)], ['48', '49', '50'])).
% 1.38/1.59  thf('52', plain,
% 1.38/1.59      (![X0 : $i, X1 : $i]:
% 1.38/1.59         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 1.38/1.59           = (k8_relat_1 @ X0 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))),
% 1.38/1.59      inference('sup+', [status(thm)], ['36', '51'])).
% 1.38/1.59  thf('53', plain,
% 1.38/1.59      (![X20 : $i, X21 : $i]:
% 1.38/1.59         (((k8_relat_1 @ X21 @ X20) = (k5_relat_1 @ X20 @ (k6_relat_1 @ X21)))
% 1.38/1.59          | ~ (v1_relat_1 @ X20))),
% 1.38/1.59      inference('cnf', [status(esa)], [t123_relat_1])).
% 1.38/1.59  thf('54', plain,
% 1.38/1.59      (![X37 : $i, X38 : $i]:
% 1.38/1.59         (((k7_relat_1 @ X38 @ X37) = (k5_relat_1 @ (k6_relat_1 @ X37) @ X38))
% 1.38/1.59          | ~ (v1_relat_1 @ X38))),
% 1.38/1.59      inference('cnf', [status(esa)], [t94_relat_1])).
% 1.38/1.59  thf(t72_relat_1, axiom,
% 1.38/1.59    (![A:$i]: ( ( k4_relat_1 @ ( k6_relat_1 @ A ) ) = ( k6_relat_1 @ A ) ))).
% 1.38/1.59  thf('55', plain,
% 1.38/1.59      (![X31 : $i]: ((k4_relat_1 @ (k6_relat_1 @ X31)) = (k6_relat_1 @ X31))),
% 1.38/1.59      inference('cnf', [status(esa)], [t72_relat_1])).
% 1.38/1.59  thf(t54_relat_1, axiom,
% 1.38/1.59    (![A:$i]:
% 1.38/1.59     ( ( v1_relat_1 @ A ) =>
% 1.38/1.59       ( ![B:$i]:
% 1.38/1.59         ( ( v1_relat_1 @ B ) =>
% 1.38/1.59           ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 1.38/1.59             ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) ))).
% 1.38/1.59  thf('56', plain,
% 1.38/1.59      (![X27 : $i, X28 : $i]:
% 1.38/1.59         (~ (v1_relat_1 @ X27)
% 1.38/1.59          | ((k4_relat_1 @ (k5_relat_1 @ X28 @ X27))
% 1.38/1.59              = (k5_relat_1 @ (k4_relat_1 @ X27) @ (k4_relat_1 @ X28)))
% 1.38/1.59          | ~ (v1_relat_1 @ X28))),
% 1.38/1.59      inference('cnf', [status(esa)], [t54_relat_1])).
% 1.38/1.59  thf('57', plain,
% 1.38/1.59      (![X0 : $i, X1 : $i]:
% 1.38/1.59         (((k4_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 1.38/1.59            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k4_relat_1 @ X1)))
% 1.38/1.59          | ~ (v1_relat_1 @ X1)
% 1.38/1.59          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 1.38/1.59      inference('sup+', [status(thm)], ['55', '56'])).
% 1.38/1.59  thf('58', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 1.38/1.59      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.38/1.59  thf('59', plain,
% 1.38/1.59      (![X0 : $i, X1 : $i]:
% 1.38/1.59         (((k4_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 1.38/1.59            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k4_relat_1 @ X1)))
% 1.38/1.59          | ~ (v1_relat_1 @ X1))),
% 1.38/1.59      inference('demod', [status(thm)], ['57', '58'])).
% 1.38/1.59  thf('60', plain,
% 1.38/1.59      (![X0 : $i, X1 : $i]:
% 1.38/1.59         (((k4_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 1.38/1.59            = (k5_relat_1 @ (k6_relat_1 @ X1) @ 
% 1.38/1.59               (k4_relat_1 @ (k6_relat_1 @ X0))))
% 1.38/1.59          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 1.38/1.59          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 1.38/1.59      inference('sup+', [status(thm)], ['54', '59'])).
% 1.38/1.59  thf('61', plain,
% 1.38/1.59      (![X0 : $i, X1 : $i]:
% 1.38/1.59         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 1.38/1.59           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 1.38/1.59      inference('demod', [status(thm)], ['7', '8', '9'])).
% 1.38/1.59  thf('62', plain,
% 1.38/1.59      (![X31 : $i]: ((k4_relat_1 @ (k6_relat_1 @ X31)) = (k6_relat_1 @ X31))),
% 1.38/1.59      inference('cnf', [status(esa)], [t72_relat_1])).
% 1.38/1.59  thf('63', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 1.38/1.59      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.38/1.59  thf('64', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 1.38/1.59      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.38/1.59  thf('65', plain,
% 1.38/1.59      (![X0 : $i, X1 : $i]:
% 1.38/1.59         ((k4_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 1.38/1.59           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 1.38/1.59      inference('demod', [status(thm)], ['60', '61', '62', '63', '64'])).
% 1.38/1.59  thf('66', plain,
% 1.38/1.59      (![X0 : $i, X1 : $i]:
% 1.38/1.59         (((k4_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 1.38/1.59            = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 1.38/1.59          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 1.38/1.59      inference('sup+', [status(thm)], ['53', '65'])).
% 1.38/1.59  thf('67', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 1.38/1.59      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.38/1.59  thf('68', plain,
% 1.38/1.59      (![X0 : $i, X1 : $i]:
% 1.38/1.59         ((k4_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 1.38/1.59           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 1.38/1.59      inference('demod', [status(thm)], ['66', '67'])).
% 1.38/1.59  thf('69', plain,
% 1.38/1.59      (![X0 : $i, X1 : $i]:
% 1.38/1.59         ((k4_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 1.38/1.59           = (k8_relat_1 @ (k3_xboole_0 @ X0 @ X1) @ (k6_relat_1 @ X1)))),
% 1.38/1.59      inference('sup+', [status(thm)], ['52', '68'])).
% 1.38/1.59  thf('70', plain,
% 1.38/1.59      (![X0 : $i, X1 : $i]:
% 1.38/1.59         ((k4_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 1.38/1.59           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 1.38/1.59      inference('demod', [status(thm)], ['66', '67'])).
% 1.38/1.59  thf('71', plain,
% 1.38/1.59      (![X0 : $i, X1 : $i]:
% 1.38/1.59         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 1.38/1.59           = (k8_relat_1 @ (k3_xboole_0 @ X0 @ X1) @ (k6_relat_1 @ X1)))),
% 1.38/1.59      inference('demod', [status(thm)], ['69', '70'])).
% 1.38/1.59  thf('72', plain,
% 1.38/1.59      (![X36 : $i]:
% 1.38/1.59         (((k5_relat_1 @ X36 @ (k6_relat_1 @ (k2_relat_1 @ X36))) = (X36))
% 1.38/1.59          | ~ (v1_relat_1 @ X36))),
% 1.38/1.59      inference('cnf', [status(esa)], [t80_relat_1])).
% 1.38/1.59  thf(t76_relat_1, axiom,
% 1.38/1.59    (![A:$i,B:$i]:
% 1.38/1.59     ( ( v1_relat_1 @ B ) =>
% 1.38/1.59       ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B ) & 
% 1.38/1.59         ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ))).
% 1.38/1.59  thf('73', plain,
% 1.38/1.59      (![X32 : $i, X33 : $i]:
% 1.38/1.59         ((r1_tarski @ (k5_relat_1 @ (k6_relat_1 @ X33) @ X32) @ X32)
% 1.38/1.59          | ~ (v1_relat_1 @ X32))),
% 1.38/1.59      inference('cnf', [status(esa)], [t76_relat_1])).
% 1.38/1.59  thf('74', plain,
% 1.38/1.59      (![X0 : $i]:
% 1.38/1.59         ((r1_tarski @ (k6_relat_1 @ X0) @ 
% 1.38/1.59           (k6_relat_1 @ (k2_relat_1 @ (k6_relat_1 @ X0))))
% 1.38/1.59          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 1.38/1.59          | ~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ (k6_relat_1 @ X0)))))),
% 1.38/1.59      inference('sup+', [status(thm)], ['72', '73'])).
% 1.38/1.59  thf('75', plain, (![X30 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X30)) = (X30))),
% 1.38/1.59      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.38/1.59  thf('76', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 1.38/1.59      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.38/1.59  thf('77', plain, (![X30 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X30)) = (X30))),
% 1.38/1.59      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.38/1.59  thf('78', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 1.38/1.59      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.38/1.59  thf('79', plain,
% 1.38/1.59      (![X0 : $i]: (r1_tarski @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 1.38/1.59      inference('demod', [status(thm)], ['74', '75', '76', '77', '78'])).
% 1.38/1.59  thf(t25_relat_1, axiom,
% 1.38/1.59    (![A:$i]:
% 1.38/1.59     ( ( v1_relat_1 @ A ) =>
% 1.38/1.59       ( ![B:$i]:
% 1.38/1.59         ( ( v1_relat_1 @ B ) =>
% 1.38/1.59           ( ( r1_tarski @ A @ B ) =>
% 1.38/1.59             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 1.38/1.59               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 1.38/1.59  thf('80', plain,
% 1.38/1.59      (![X25 : $i, X26 : $i]:
% 1.38/1.59         (~ (v1_relat_1 @ X25)
% 1.38/1.59          | (r1_tarski @ (k2_relat_1 @ X26) @ (k2_relat_1 @ X25))
% 1.38/1.59          | ~ (r1_tarski @ X26 @ X25)
% 1.38/1.59          | ~ (v1_relat_1 @ X26))),
% 1.38/1.59      inference('cnf', [status(esa)], [t25_relat_1])).
% 1.38/1.59  thf('81', plain,
% 1.38/1.59      (![X0 : $i]:
% 1.38/1.59         (~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 1.38/1.59          | (r1_tarski @ (k2_relat_1 @ (k6_relat_1 @ X0)) @ 
% 1.38/1.59             (k2_relat_1 @ (k6_relat_1 @ X0)))
% 1.38/1.59          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 1.38/1.59      inference('sup-', [status(thm)], ['79', '80'])).
% 1.38/1.59  thf('82', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 1.38/1.59      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.38/1.59  thf('83', plain, (![X30 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X30)) = (X30))),
% 1.38/1.59      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.38/1.59  thf('84', plain, (![X30 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X30)) = (X30))),
% 1.38/1.59      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.38/1.59  thf('85', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 1.38/1.59      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.38/1.59  thf('86', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 1.38/1.59      inference('demod', [status(thm)], ['81', '82', '83', '84', '85'])).
% 1.38/1.59  thf(t97_relat_1, axiom,
% 1.38/1.59    (![A:$i,B:$i]:
% 1.38/1.59     ( ( v1_relat_1 @ B ) =>
% 1.38/1.59       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 1.38/1.59         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 1.38/1.59  thf('87', plain,
% 1.38/1.59      (![X39 : $i, X40 : $i]:
% 1.38/1.59         (~ (r1_tarski @ (k1_relat_1 @ X39) @ X40)
% 1.38/1.59          | ((k7_relat_1 @ X39 @ X40) = (X39))
% 1.38/1.59          | ~ (v1_relat_1 @ X39))),
% 1.38/1.59      inference('cnf', [status(esa)], [t97_relat_1])).
% 1.38/1.59  thf('88', plain,
% 1.38/1.59      (![X0 : $i]:
% 1.38/1.59         (~ (v1_relat_1 @ X0) | ((k7_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (X0)))),
% 1.38/1.59      inference('sup-', [status(thm)], ['86', '87'])).
% 1.38/1.59  thf('89', plain,
% 1.38/1.59      (![X37 : $i, X38 : $i]:
% 1.38/1.59         (((k7_relat_1 @ X38 @ X37) = (k5_relat_1 @ (k6_relat_1 @ X37) @ X38))
% 1.38/1.59          | ~ (v1_relat_1 @ X38))),
% 1.38/1.59      inference('cnf', [status(esa)], [t94_relat_1])).
% 1.38/1.59  thf('90', plain,
% 1.38/1.59      (![X32 : $i, X33 : $i]:
% 1.38/1.59         ((r1_tarski @ (k5_relat_1 @ (k6_relat_1 @ X33) @ X32) @ X32)
% 1.38/1.59          | ~ (v1_relat_1 @ X32))),
% 1.38/1.59      inference('cnf', [status(esa)], [t76_relat_1])).
% 1.38/1.59  thf(t28_xboole_1, axiom,
% 1.38/1.59    (![A:$i,B:$i]:
% 1.38/1.59     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.38/1.59  thf('91', plain,
% 1.38/1.59      (![X0 : $i, X1 : $i]:
% 1.38/1.59         (((k3_xboole_0 @ X0 @ X1) = (X0)) | ~ (r1_tarski @ X0 @ X1))),
% 1.38/1.59      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.38/1.59  thf('92', plain,
% 1.38/1.59      (![X0 : $i, X1 : $i]:
% 1.38/1.59         (~ (v1_relat_1 @ X0)
% 1.38/1.59          | ((k3_xboole_0 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X0)
% 1.38/1.59              = (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 1.38/1.59      inference('sup-', [status(thm)], ['90', '91'])).
% 1.38/1.59  thf('93', plain,
% 1.38/1.59      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.38/1.59      inference('sup+', [status(thm)], ['34', '35'])).
% 1.38/1.59  thf('94', plain,
% 1.38/1.59      (![X0 : $i, X1 : $i]:
% 1.38/1.59         (~ (v1_relat_1 @ X0)
% 1.38/1.59          | ((k3_xboole_0 @ X0 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 1.38/1.59              = (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 1.38/1.59      inference('demod', [status(thm)], ['92', '93'])).
% 1.38/1.59  thf('95', plain,
% 1.38/1.59      (![X0 : $i, X1 : $i]:
% 1.38/1.59         (((k3_xboole_0 @ X1 @ (k7_relat_1 @ X1 @ X0))
% 1.38/1.59            = (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 1.38/1.59          | ~ (v1_relat_1 @ X1)
% 1.38/1.59          | ~ (v1_relat_1 @ X1))),
% 1.38/1.59      inference('sup+', [status(thm)], ['89', '94'])).
% 1.38/1.59  thf('96', plain,
% 1.38/1.59      (![X0 : $i, X1 : $i]:
% 1.38/1.59         (~ (v1_relat_1 @ X1)
% 1.38/1.59          | ((k3_xboole_0 @ X1 @ (k7_relat_1 @ X1 @ X0))
% 1.38/1.59              = (k5_relat_1 @ (k6_relat_1 @ X0) @ X1)))),
% 1.38/1.59      inference('simplify', [status(thm)], ['95'])).
% 1.38/1.59  thf('97', plain,
% 1.38/1.59      (![X0 : $i]:
% 1.38/1.59         (((k3_xboole_0 @ X0 @ X0)
% 1.38/1.59            = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X0))
% 1.38/1.59          | ~ (v1_relat_1 @ X0)
% 1.38/1.59          | ~ (v1_relat_1 @ X0))),
% 1.38/1.59      inference('sup+', [status(thm)], ['88', '96'])).
% 1.38/1.59  thf('98', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 1.38/1.59      inference('demod', [status(thm)], ['81', '82', '83', '84', '85'])).
% 1.38/1.59  thf('99', plain,
% 1.38/1.59      (![X0 : $i, X1 : $i]:
% 1.38/1.59         (((k3_xboole_0 @ X0 @ X1) = (X0)) | ~ (r1_tarski @ X0 @ X1))),
% 1.38/1.59      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.38/1.59  thf('100', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 1.38/1.59      inference('sup-', [status(thm)], ['98', '99'])).
% 1.38/1.59  thf('101', plain,
% 1.38/1.59      (![X0 : $i]:
% 1.38/1.59         (((X0) = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X0))
% 1.38/1.59          | ~ (v1_relat_1 @ X0)
% 1.38/1.59          | ~ (v1_relat_1 @ X0))),
% 1.38/1.59      inference('demod', [status(thm)], ['97', '100'])).
% 1.38/1.59  thf('102', plain,
% 1.38/1.59      (![X0 : $i]:
% 1.38/1.59         (~ (v1_relat_1 @ X0)
% 1.38/1.59          | ((X0) = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X0)))),
% 1.38/1.59      inference('simplify', [status(thm)], ['101'])).
% 1.38/1.59  thf('103', plain,
% 1.38/1.59      (![X20 : $i, X21 : $i]:
% 1.38/1.59         (((k8_relat_1 @ X21 @ X20) = (k5_relat_1 @ X20 @ (k6_relat_1 @ X21)))
% 1.38/1.59          | ~ (v1_relat_1 @ X20))),
% 1.38/1.59      inference('cnf', [status(esa)], [t123_relat_1])).
% 1.38/1.59  thf(t112_relat_1, axiom,
% 1.38/1.59    (![A:$i,B:$i]:
% 1.38/1.59     ( ( v1_relat_1 @ B ) =>
% 1.38/1.59       ( ![C:$i]:
% 1.38/1.59         ( ( v1_relat_1 @ C ) =>
% 1.38/1.59           ( ( k7_relat_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 1.38/1.59             ( k5_relat_1 @ ( k7_relat_1 @ B @ A ) @ C ) ) ) ) ))).
% 1.38/1.59  thf('104', plain,
% 1.38/1.59      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.38/1.59         (~ (v1_relat_1 @ X17)
% 1.38/1.59          | ((k7_relat_1 @ (k5_relat_1 @ X18 @ X17) @ X19)
% 1.38/1.59              = (k5_relat_1 @ (k7_relat_1 @ X18 @ X19) @ X17))
% 1.38/1.59          | ~ (v1_relat_1 @ X18))),
% 1.38/1.59      inference('cnf', [status(esa)], [t112_relat_1])).
% 1.38/1.59  thf('105', plain,
% 1.38/1.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.38/1.59         (((k7_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X2)) @ X0)
% 1.38/1.59            = (k8_relat_1 @ X2 @ (k7_relat_1 @ X1 @ X0)))
% 1.38/1.59          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 1.38/1.59          | ~ (v1_relat_1 @ X1)
% 1.38/1.59          | ~ (v1_relat_1 @ (k6_relat_1 @ X2)))),
% 1.38/1.59      inference('sup+', [status(thm)], ['103', '104'])).
% 1.38/1.59  thf('106', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 1.38/1.59      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.38/1.59  thf('107', plain,
% 1.38/1.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.38/1.59         (((k7_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X2)) @ X0)
% 1.38/1.59            = (k8_relat_1 @ X2 @ (k7_relat_1 @ X1 @ X0)))
% 1.38/1.59          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 1.38/1.59          | ~ (v1_relat_1 @ X1))),
% 1.38/1.59      inference('demod', [status(thm)], ['105', '106'])).
% 1.38/1.59  thf('108', plain,
% 1.38/1.59      (![X37 : $i, X38 : $i]:
% 1.38/1.59         (((k7_relat_1 @ X38 @ X37) = (k5_relat_1 @ (k6_relat_1 @ X37) @ X38))
% 1.38/1.59          | ~ (v1_relat_1 @ X38))),
% 1.38/1.59      inference('cnf', [status(esa)], [t94_relat_1])).
% 1.38/1.59  thf('109', plain,
% 1.38/1.59      (![X0 : $i, X1 : $i]:
% 1.38/1.59         (~ (v1_relat_1 @ X0)
% 1.38/1.59          | ((k3_xboole_0 @ X0 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 1.38/1.59              = (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 1.38/1.59      inference('demod', [status(thm)], ['92', '93'])).
% 1.38/1.59  thf(fc1_relat_1, axiom,
% 1.38/1.59    (![A:$i,B:$i]:
% 1.38/1.59     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.38/1.59  thf('110', plain,
% 1.38/1.59      (![X12 : $i, X13 : $i]:
% 1.38/1.59         (~ (v1_relat_1 @ X12) | (v1_relat_1 @ (k3_xboole_0 @ X12 @ X13)))),
% 1.38/1.59      inference('cnf', [status(esa)], [fc1_relat_1])).
% 1.38/1.59  thf('111', plain,
% 1.38/1.59      (![X0 : $i, X1 : $i]:
% 1.38/1.59         ((v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 1.38/1.59          | ~ (v1_relat_1 @ X0)
% 1.38/1.59          | ~ (v1_relat_1 @ X0))),
% 1.38/1.59      inference('sup+', [status(thm)], ['109', '110'])).
% 1.38/1.59  thf('112', plain,
% 1.38/1.59      (![X0 : $i, X1 : $i]:
% 1.38/1.59         (~ (v1_relat_1 @ X0)
% 1.38/1.59          | (v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 1.38/1.59      inference('simplify', [status(thm)], ['111'])).
% 1.38/1.59  thf('113', plain,
% 1.38/1.59      (![X0 : $i, X1 : $i]:
% 1.38/1.59         ((v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 1.38/1.59          | ~ (v1_relat_1 @ X1)
% 1.38/1.59          | ~ (v1_relat_1 @ X1))),
% 1.38/1.59      inference('sup+', [status(thm)], ['108', '112'])).
% 1.38/1.59  thf('114', plain,
% 1.38/1.59      (![X0 : $i, X1 : $i]:
% 1.38/1.59         (~ (v1_relat_1 @ X1) | (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 1.38/1.59      inference('simplify', [status(thm)], ['113'])).
% 1.38/1.59  thf('115', plain,
% 1.38/1.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.38/1.59         (~ (v1_relat_1 @ X1)
% 1.38/1.59          | ((k7_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X2)) @ X0)
% 1.38/1.59              = (k8_relat_1 @ X2 @ (k7_relat_1 @ X1 @ X0))))),
% 1.38/1.59      inference('clc', [status(thm)], ['107', '114'])).
% 1.38/1.59  thf('116', plain,
% 1.38/1.59      (![X0 : $i, X1 : $i]:
% 1.38/1.59         (((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 1.38/1.59            = (k8_relat_1 @ X0 @ 
% 1.38/1.59               (k7_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ (k6_relat_1 @ X0))) @ 
% 1.38/1.59                X1)))
% 1.38/1.59          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 1.38/1.59          | ~ (v1_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ (k6_relat_1 @ X0)))))),
% 1.38/1.59      inference('sup+', [status(thm)], ['102', '115'])).
% 1.38/1.59  thf('117', plain,
% 1.38/1.59      (![X0 : $i, X1 : $i]:
% 1.38/1.59         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 1.38/1.59           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 1.38/1.59      inference('demod', [status(thm)], ['7', '8', '9'])).
% 1.38/1.59  thf('118', plain, (![X29 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X29)) = (X29))),
% 1.38/1.59      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.38/1.59  thf('119', plain,
% 1.38/1.59      (![X0 : $i, X1 : $i]:
% 1.38/1.59         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 1.38/1.59           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 1.38/1.59      inference('demod', [status(thm)], ['7', '8', '9'])).
% 1.38/1.59  thf('120', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 1.38/1.59      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.38/1.59  thf('121', plain, (![X29 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X29)) = (X29))),
% 1.38/1.59      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.38/1.59  thf('122', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 1.38/1.59      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.38/1.59  thf('123', plain,
% 1.38/1.59      (![X0 : $i, X1 : $i]:
% 1.38/1.59         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 1.38/1.59           = (k8_relat_1 @ X0 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1))))),
% 1.38/1.59      inference('demod', [status(thm)],
% 1.38/1.59                ['116', '117', '118', '119', '120', '121', '122'])).
% 1.38/1.59  thf('124', plain,
% 1.38/1.59      (![X0 : $i, X1 : $i]:
% 1.38/1.59         ((k8_relat_1 @ (k3_xboole_0 @ X1 @ X0) @ (k6_relat_1 @ X0))
% 1.38/1.59           = (k8_relat_1 @ (k3_xboole_0 @ X1 @ X0) @ 
% 1.38/1.59              (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 1.38/1.59      inference('sup+', [status(thm)], ['71', '123'])).
% 1.38/1.59  thf('125', plain,
% 1.38/1.59      (![X0 : $i, X1 : $i]:
% 1.38/1.59         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 1.38/1.59           = (k8_relat_1 @ (k3_xboole_0 @ X0 @ X1) @ (k6_relat_1 @ X1)))),
% 1.38/1.59      inference('demod', [status(thm)], ['69', '70'])).
% 1.38/1.59  thf('126', plain,
% 1.38/1.59      (![X0 : $i, X1 : $i]:
% 1.38/1.59         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 1.38/1.59           = (k8_relat_1 @ (k3_xboole_0 @ X1 @ X0) @ 
% 1.38/1.59              (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 1.38/1.59      inference('demod', [status(thm)], ['124', '125'])).
% 1.38/1.59  thf('127', plain,
% 1.38/1.59      (![X0 : $i, X1 : $i]:
% 1.38/1.59         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 1.38/1.59           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.38/1.59      inference('sup+', [status(thm)], ['31', '126'])).
% 1.38/1.59  thf('128', plain,
% 1.38/1.59      (((k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B))
% 1.38/1.59         != (k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B)))),
% 1.38/1.59      inference('demod', [status(thm)], ['4', '127'])).
% 1.38/1.59  thf('129', plain, ($false), inference('simplify', [status(thm)], ['128'])).
% 1.38/1.59  
% 1.38/1.59  % SZS output end Refutation
% 1.38/1.59  
% 1.42/1.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
