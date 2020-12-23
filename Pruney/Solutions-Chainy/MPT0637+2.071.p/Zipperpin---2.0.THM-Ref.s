%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lOSsNd9Tmw

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:06 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 127 expanded)
%              Number of leaves         :   24 (  54 expanded)
%              Depth                    :   12
%              Number of atoms          :  603 (1043 expanded)
%              Number of equality atoms :   40 (  65 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t123_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ B )
        = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k8_relat_1 @ X25 @ X24 )
        = ( k5_relat_1 @ X24 @ ( k6_relat_1 @ X25 ) ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
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

thf(fc24_relat_1,axiom,(
    ! [A: $i] :
      ( ( v5_relat_1 @ ( k6_relat_1 @ A ) @ A )
      & ( v4_relat_1 @ ( k6_relat_1 @ A ) @ A )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('3',plain,(
    ! [X46: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('4',plain,(
    ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ sk_B ) )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k8_relat_1 @ X25 @ X24 )
        = ( k5_relat_1 @ X24 @ ( k6_relat_1 @ X25 ) ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('6',plain,(
    ! [X44: $i,X45: $i] :
      ( ( ( k7_relat_1 @ X45 @ X44 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X44 ) @ X45 ) )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t76_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B )
        & ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ) )).

thf('7',plain,(
    ! [X40: $i,X41: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X40 @ ( k6_relat_1 @ X41 ) ) @ X40 )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t76_relat_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X46: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('10',plain,(
    ! [X46: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k8_relat_1 @ X25 @ X24 )
        = ( k5_relat_1 @ X24 @ ( k6_relat_1 @ X25 ) ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('13',plain,(
    ! [X44: $i,X45: $i] :
      ( ( ( k7_relat_1 @ X45 @ X44 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X44 ) @ X45 ) )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X46: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('16',plain,(
    ! [X46: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['11','17'])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('19',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( v1_relat_1 @ X33 )
      | ( r1_tarski @ ( k2_relat_1 @ X34 ) @ ( k2_relat_1 @ X33 ) )
      | ~ ( r1_tarski @ X34 @ X33 )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('22',plain,(
    ! [X44: $i,X45: $i] :
      ( ( ( k7_relat_1 @ X45 @ X44 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X44 ) @ X45 ) )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('23',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_relat_1 @ X17 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X46: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['21','27'])).

thf('29',plain,(
    ! [X46: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('31',plain,(
    ! [X38: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X38 ) )
      = X38 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t119_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('32',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k2_relat_1 @ ( k8_relat_1 @ X23 @ X22 ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ X22 ) @ X23 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t119_relat_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k3_xboole_0 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X46: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X38: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X38 ) )
      = X38 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('37',plain,(
    ! [X46: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(demod,[status(thm)],['20','30','35','36','37'])).

thf('39',plain,(
    ! [X38: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X38 ) )
      = X38 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('40',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X42 ) @ X43 )
      | ( ( k5_relat_1 @ X42 @ ( k6_relat_1 @ X43 ) )
        = X42 )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X46: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['38','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
        = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['5','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf(t192_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k7_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ) )).

thf('47',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k7_relat_1 @ X29 @ X30 )
        = ( k7_relat_1 @ X29 @ ( k3_xboole_0 @ ( k1_relat_1 @ X29 ) @ X30 ) ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t192_relat_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ ( k3_xboole_0 @ ( k1_relat_1 @ ( k6_relat_1 @ X1 ) ) @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('50',plain,(
    ! [X37: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X37 ) )
      = X37 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('51',plain,(
    ! [X46: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['48','49','50','51'])).

thf('53',plain,(
    ! [X46: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['45','52','53'])).

thf('55',plain,(
    ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ sk_B ) )
 != ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','54'])).

thf('56',plain,(
    $false ),
    inference(simplify,[status(thm)],['55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lOSsNd9Tmw
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:19:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.21/0.34  % Number of cores: 8
% 0.21/0.34  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 0.21/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.52  % Solved by: fo/fo7.sh
% 0.21/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.52  % done 114 iterations in 0.073s
% 0.21/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.52  % SZS output start Refutation
% 0.21/0.52  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.21/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.52  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.21/0.52  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.52  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.21/0.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.52  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.21/0.52  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.21/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.52  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.21/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.52  thf(t123_relat_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( v1_relat_1 @ B ) =>
% 0.21/0.52       ( ( k8_relat_1 @ A @ B ) = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ))).
% 0.21/0.52  thf('0', plain,
% 0.21/0.52      (![X24 : $i, X25 : $i]:
% 0.21/0.52         (((k8_relat_1 @ X25 @ X24) = (k5_relat_1 @ X24 @ (k6_relat_1 @ X25)))
% 0.21/0.52          | ~ (v1_relat_1 @ X24))),
% 0.21/0.52      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.21/0.52  thf(t43_funct_1, conjecture,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.21/0.52       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.21/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.52    (~( ![A:$i,B:$i]:
% 0.21/0.52        ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.21/0.52          ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 0.21/0.52    inference('cnf.neg', [status(esa)], [t43_funct_1])).
% 0.21/0.52  thf('1', plain,
% 0.21/0.52      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A))
% 0.21/0.52         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('2', plain,
% 0.21/0.52      ((((k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B))
% 0.21/0.52          != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))
% 0.21/0.52        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_B)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.52  thf(fc24_relat_1, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( v5_relat_1 @ ( k6_relat_1 @ A ) @ A ) & 
% 0.21/0.52       ( v4_relat_1 @ ( k6_relat_1 @ A ) @ A ) & 
% 0.21/0.52       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.21/0.52  thf('3', plain, (![X46 : $i]: (v1_relat_1 @ (k6_relat_1 @ X46))),
% 0.21/0.52      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.21/0.52  thf('4', plain,
% 0.21/0.52      (((k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B))
% 0.21/0.52         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.21/0.52      inference('demod', [status(thm)], ['2', '3'])).
% 0.21/0.52  thf('5', plain,
% 0.21/0.52      (![X24 : $i, X25 : $i]:
% 0.21/0.52         (((k8_relat_1 @ X25 @ X24) = (k5_relat_1 @ X24 @ (k6_relat_1 @ X25)))
% 0.21/0.52          | ~ (v1_relat_1 @ X24))),
% 0.21/0.52      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.21/0.52  thf(t94_relat_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( v1_relat_1 @ B ) =>
% 0.21/0.52       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.21/0.52  thf('6', plain,
% 0.21/0.52      (![X44 : $i, X45 : $i]:
% 0.21/0.52         (((k7_relat_1 @ X45 @ X44) = (k5_relat_1 @ (k6_relat_1 @ X44) @ X45))
% 0.21/0.52          | ~ (v1_relat_1 @ X45))),
% 0.21/0.52      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.21/0.52  thf(t76_relat_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( v1_relat_1 @ B ) =>
% 0.21/0.52       ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B ) & 
% 0.21/0.52         ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ))).
% 0.21/0.52  thf('7', plain,
% 0.21/0.52      (![X40 : $i, X41 : $i]:
% 0.21/0.52         ((r1_tarski @ (k5_relat_1 @ X40 @ (k6_relat_1 @ X41)) @ X40)
% 0.21/0.52          | ~ (v1_relat_1 @ X40))),
% 0.21/0.52      inference('cnf', [status(esa)], [t76_relat_1])).
% 0.21/0.52  thf('8', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((r1_tarski @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 0.21/0.52           (k6_relat_1 @ X0))
% 0.21/0.52          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.21/0.52          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.21/0.52      inference('sup+', [status(thm)], ['6', '7'])).
% 0.21/0.52  thf('9', plain, (![X46 : $i]: (v1_relat_1 @ (k6_relat_1 @ X46))),
% 0.21/0.52      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.21/0.52  thf('10', plain, (![X46 : $i]: (v1_relat_1 @ (k6_relat_1 @ X46))),
% 0.21/0.52      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.21/0.52  thf('11', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (r1_tarski @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ (k6_relat_1 @ X0))),
% 0.21/0.52      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.21/0.52  thf('12', plain,
% 0.21/0.52      (![X24 : $i, X25 : $i]:
% 0.21/0.52         (((k8_relat_1 @ X25 @ X24) = (k5_relat_1 @ X24 @ (k6_relat_1 @ X25)))
% 0.21/0.52          | ~ (v1_relat_1 @ X24))),
% 0.21/0.52      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.21/0.52  thf('13', plain,
% 0.21/0.52      (![X44 : $i, X45 : $i]:
% 0.21/0.52         (((k7_relat_1 @ X45 @ X44) = (k5_relat_1 @ (k6_relat_1 @ X44) @ X45))
% 0.21/0.52          | ~ (v1_relat_1 @ X45))),
% 0.21/0.52      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.21/0.52  thf('14', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.21/0.52            = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.21/0.52          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.21/0.52          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.21/0.52      inference('sup+', [status(thm)], ['12', '13'])).
% 0.21/0.52  thf('15', plain, (![X46 : $i]: (v1_relat_1 @ (k6_relat_1 @ X46))),
% 0.21/0.52      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.21/0.52  thf('16', plain, (![X46 : $i]: (v1_relat_1 @ (k6_relat_1 @ X46))),
% 0.21/0.52      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.21/0.52  thf('17', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.21/0.52           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.21/0.52      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.21/0.52  thf('18', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (r1_tarski @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ (k6_relat_1 @ X0))),
% 0.21/0.52      inference('demod', [status(thm)], ['11', '17'])).
% 0.21/0.52  thf(t25_relat_1, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( v1_relat_1 @ A ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( v1_relat_1 @ B ) =>
% 0.21/0.52           ( ( r1_tarski @ A @ B ) =>
% 0.21/0.52             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 0.21/0.52               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 0.21/0.52  thf('19', plain,
% 0.21/0.52      (![X33 : $i, X34 : $i]:
% 0.21/0.52         (~ (v1_relat_1 @ X33)
% 0.21/0.52          | (r1_tarski @ (k2_relat_1 @ X34) @ (k2_relat_1 @ X33))
% 0.21/0.52          | ~ (r1_tarski @ X34 @ X33)
% 0.21/0.52          | ~ (v1_relat_1 @ X34))),
% 0.21/0.52      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.21/0.52  thf('20', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (~ (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.21/0.52          | (r1_tarski @ 
% 0.21/0.52             (k2_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ 
% 0.21/0.52             (k2_relat_1 @ (k6_relat_1 @ X0)))
% 0.21/0.52          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.52  thf('21', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.21/0.52           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.21/0.52      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.21/0.52  thf('22', plain,
% 0.21/0.52      (![X44 : $i, X45 : $i]:
% 0.21/0.52         (((k7_relat_1 @ X45 @ X44) = (k5_relat_1 @ (k6_relat_1 @ X44) @ X45))
% 0.21/0.52          | ~ (v1_relat_1 @ X45))),
% 0.21/0.52      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.21/0.52  thf(dt_k5_relat_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.21/0.52       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.21/0.52  thf('23', plain,
% 0.21/0.52      (![X16 : $i, X17 : $i]:
% 0.21/0.52         (~ (v1_relat_1 @ X16)
% 0.21/0.52          | ~ (v1_relat_1 @ X17)
% 0.21/0.52          | (v1_relat_1 @ (k5_relat_1 @ X16 @ X17)))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.21/0.52  thf('24', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.21/0.52          | ~ (v1_relat_1 @ X1)
% 0.21/0.52          | ~ (v1_relat_1 @ X1)
% 0.21/0.52          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.21/0.52      inference('sup+', [status(thm)], ['22', '23'])).
% 0.21/0.52  thf('25', plain, (![X46 : $i]: (v1_relat_1 @ (k6_relat_1 @ X46))),
% 0.21/0.52      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.21/0.52  thf('26', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.21/0.52          | ~ (v1_relat_1 @ X1)
% 0.21/0.52          | ~ (v1_relat_1 @ X1))),
% 0.21/0.52      inference('demod', [status(thm)], ['24', '25'])).
% 0.21/0.52  thf('27', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (~ (v1_relat_1 @ X1) | (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.21/0.52      inference('simplify', [status(thm)], ['26'])).
% 0.21/0.52  thf('28', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.21/0.52          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.21/0.52      inference('sup+', [status(thm)], ['21', '27'])).
% 0.21/0.52  thf('29', plain, (![X46 : $i]: (v1_relat_1 @ (k6_relat_1 @ X46))),
% 0.21/0.52      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.21/0.52  thf('30', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.21/0.52      inference('demod', [status(thm)], ['28', '29'])).
% 0.21/0.52  thf(t71_relat_1, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.21/0.52       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.21/0.52  thf('31', plain, (![X38 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X38)) = (X38))),
% 0.21/0.52      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.52  thf(t119_relat_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( v1_relat_1 @ B ) =>
% 0.21/0.52       ( ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) ) =
% 0.21/0.52         ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.21/0.52  thf('32', plain,
% 0.21/0.52      (![X22 : $i, X23 : $i]:
% 0.21/0.52         (((k2_relat_1 @ (k8_relat_1 @ X23 @ X22))
% 0.21/0.52            = (k3_xboole_0 @ (k2_relat_1 @ X22) @ X23))
% 0.21/0.52          | ~ (v1_relat_1 @ X22))),
% 0.21/0.52      inference('cnf', [status(esa)], [t119_relat_1])).
% 0.21/0.52  thf('33', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (((k2_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.21/0.52            = (k3_xboole_0 @ X0 @ X1))
% 0.21/0.52          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.21/0.52      inference('sup+', [status(thm)], ['31', '32'])).
% 0.21/0.52  thf('34', plain, (![X46 : $i]: (v1_relat_1 @ (k6_relat_1 @ X46))),
% 0.21/0.52      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.21/0.52  thf('35', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((k2_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.21/0.52           = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.52      inference('demod', [status(thm)], ['33', '34'])).
% 0.21/0.52  thf('36', plain, (![X38 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X38)) = (X38))),
% 0.21/0.52      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.52  thf('37', plain, (![X46 : $i]: (v1_relat_1 @ (k6_relat_1 @ X46))),
% 0.21/0.52      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.21/0.52  thf('38', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.21/0.52      inference('demod', [status(thm)], ['20', '30', '35', '36', '37'])).
% 0.21/0.52  thf('39', plain, (![X38 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X38)) = (X38))),
% 0.21/0.52      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.52  thf(t79_relat_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( v1_relat_1 @ B ) =>
% 0.21/0.52       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.21/0.52         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 0.21/0.52  thf('40', plain,
% 0.21/0.52      (![X42 : $i, X43 : $i]:
% 0.21/0.52         (~ (r1_tarski @ (k2_relat_1 @ X42) @ X43)
% 0.21/0.52          | ((k5_relat_1 @ X42 @ (k6_relat_1 @ X43)) = (X42))
% 0.21/0.52          | ~ (v1_relat_1 @ X42))),
% 0.21/0.52      inference('cnf', [status(esa)], [t79_relat_1])).
% 0.21/0.52  thf('41', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (~ (r1_tarski @ X0 @ X1)
% 0.21/0.52          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.21/0.52          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 0.21/0.52              = (k6_relat_1 @ X0)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['39', '40'])).
% 0.21/0.52  thf('42', plain, (![X46 : $i]: (v1_relat_1 @ (k6_relat_1 @ X46))),
% 0.21/0.52      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.21/0.52  thf('43', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (~ (r1_tarski @ X0 @ X1)
% 0.21/0.52          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 0.21/0.52              = (k6_relat_1 @ X0)))),
% 0.21/0.52      inference('demod', [status(thm)], ['41', '42'])).
% 0.21/0.52  thf('44', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((k5_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 0.21/0.52           (k6_relat_1 @ X0)) = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['38', '43'])).
% 0.21/0.52  thf('45', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (((k8_relat_1 @ X1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.21/0.52            = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.21/0.52          | ~ (v1_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.21/0.52      inference('sup+', [status(thm)], ['5', '44'])).
% 0.21/0.52  thf('46', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.21/0.52           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.21/0.52      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.21/0.52  thf(t192_relat_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( v1_relat_1 @ B ) =>
% 0.21/0.52       ( ( k7_relat_1 @ B @ A ) =
% 0.21/0.52         ( k7_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ))).
% 0.21/0.52  thf('47', plain,
% 0.21/0.52      (![X29 : $i, X30 : $i]:
% 0.21/0.52         (((k7_relat_1 @ X29 @ X30)
% 0.21/0.52            = (k7_relat_1 @ X29 @ (k3_xboole_0 @ (k1_relat_1 @ X29) @ X30)))
% 0.21/0.52          | ~ (v1_relat_1 @ X29))),
% 0.21/0.52      inference('cnf', [status(esa)], [t192_relat_1])).
% 0.21/0.52  thf('48', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.21/0.52            = (k8_relat_1 @ X1 @ 
% 0.21/0.52               (k6_relat_1 @ 
% 0.21/0.52                (k3_xboole_0 @ (k1_relat_1 @ (k6_relat_1 @ X1)) @ X0))))
% 0.21/0.52          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.21/0.52      inference('sup+', [status(thm)], ['46', '47'])).
% 0.21/0.52  thf('49', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.21/0.52           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.21/0.52      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.21/0.52  thf('50', plain, (![X37 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X37)) = (X37))),
% 0.21/0.52      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.52  thf('51', plain, (![X46 : $i]: (v1_relat_1 @ (k6_relat_1 @ X46))),
% 0.21/0.52      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.21/0.52  thf('52', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 0.21/0.52           = (k8_relat_1 @ X1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.21/0.52      inference('demod', [status(thm)], ['48', '49', '50', '51'])).
% 0.21/0.52  thf('53', plain, (![X46 : $i]: (v1_relat_1 @ (k6_relat_1 @ X46))),
% 0.21/0.52      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.21/0.52  thf('54', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 0.21/0.52           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.21/0.52      inference('demod', [status(thm)], ['45', '52', '53'])).
% 0.21/0.52  thf('55', plain,
% 0.21/0.52      (((k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B))
% 0.21/0.52         != (k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B)))),
% 0.21/0.52      inference('demod', [status(thm)], ['4', '54'])).
% 0.21/0.52  thf('56', plain, ($false), inference('simplify', [status(thm)], ['55'])).
% 0.21/0.52  
% 0.21/0.52  % SZS output end Refutation
% 0.21/0.52  
% 0.21/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
