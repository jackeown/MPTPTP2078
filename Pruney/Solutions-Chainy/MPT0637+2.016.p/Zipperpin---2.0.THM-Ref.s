%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aJ4PrLI0dF

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:57 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 181 expanded)
%              Number of leaves         :   26 (  73 expanded)
%              Depth                    :   10
%              Number of atoms          :  681 (1372 expanded)
%              Number of equality atoms :   55 ( 114 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('0',plain,(
    ! [X51: $i,X52: $i] :
      ( ( ( k7_relat_1 @ X52 @ X51 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X51 ) @ X52 ) )
      | ~ ( v1_relat_1 @ X52 ) ) ),
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
    ! [X37: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('4',plain,(
    ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t78_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A )
        = A ) ) )).

thf('5',plain,(
    ! [X45: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X45 ) ) @ X45 )
        = X45 )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf(t123_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ B )
        = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ) )).

thf('6',plain,(
    ! [X38: $i,X39: $i] :
      ( ( ( k8_relat_1 @ X39 @ X38 )
        = ( k5_relat_1 @ X38 @ ( k6_relat_1 @ X39 ) ) )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t139_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( k8_relat_1 @ A @ ( k5_relat_1 @ B @ C ) )
            = ( k5_relat_1 @ B @ ( k8_relat_1 @ A @ C ) ) ) ) ) )).

thf('7',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( v1_relat_1 @ X40 )
      | ( ( k8_relat_1 @ X42 @ ( k5_relat_1 @ X41 @ X40 ) )
        = ( k5_relat_1 @ X41 @ ( k8_relat_1 @ X42 @ X40 ) ) )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t139_relat_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ X0 @ ( k8_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X37: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ X0 @ ( k8_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ X0 @ ( k8_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X38: $i,X39: $i] :
      ( ( ( k8_relat_1 @ X39 @ X38 )
        = ( k5_relat_1 @ X38 @ ( k6_relat_1 @ X39 ) ) )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('13',plain,(
    ! [X51: $i,X52: $i] :
      ( ( ( k7_relat_1 @ X52 @ X51 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X51 ) @ X52 ) )
      | ~ ( v1_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X37: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('16',plain,(
    ! [X37: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ X0 @ ( k7_relat_1 @ ( k6_relat_1 @ X2 ) @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['11','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ X1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ) )
        = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['5','18'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('20',plain,(
    ! [X43: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X43 ) )
      = X43 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('21',plain,(
    ! [X49: $i,X50: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X49 @ X50 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X49 ) @ X50 ) )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( k3_xboole_0 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X37: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('26',plain,(
    ! [X38: $i,X39: $i] :
      ( ( ( k8_relat_1 @ X39 @ X38 )
        = ( k5_relat_1 @ X38 @ ( k6_relat_1 @ X39 ) ) )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('27',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_tarski @ X5 @ X4 )
      = ( k2_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('28',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X33 @ X34 ) )
      = ( k3_xboole_0 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X33 @ X34 ) )
      = ( k3_xboole_0 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('33',plain,(
    ! [X44: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X44 ) )
      = X44 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('34',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X46 ) @ X47 )
      | ( ( k5_relat_1 @ X46 @ ( k6_relat_1 @ X47 ) )
        = X46 )
      | ~ ( v1_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X37: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['32','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['31','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
        = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['26','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('42',plain,(
    ! [X37: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('47',plain,(
    ! [X38: $i,X39: $i] :
      ( ( ( k8_relat_1 @ X39 @ X38 )
        = ( k5_relat_1 @ X38 @ ( k6_relat_1 @ X39 ) ) )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('48',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( v1_relat_1 @ X35 )
      | ~ ( v1_relat_1 @ X36 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X35 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X37: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['46','52'])).

thf('54',plain,(
    ! [X37: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('57',plain,(
    ! [X37: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['19','24','25','43','44','45','55','56','57'])).

thf('59',plain,(
    ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
 != ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['4','58'])).

thf('60',plain,(
    $false ),
    inference(simplify,[status(thm)],['59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aJ4PrLI0dF
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:09:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.38/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.56  % Solved by: fo/fo7.sh
% 0.38/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.56  % done 302 iterations in 0.120s
% 0.38/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.56  % SZS output start Refutation
% 0.38/0.56  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.38/0.56  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.38/0.56  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.38/0.56  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.38/0.56  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.38/0.56  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.38/0.56  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.38/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.56  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.38/0.56  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.38/0.56  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.38/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.56  thf(t94_relat_1, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( v1_relat_1 @ B ) =>
% 0.38/0.56       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.38/0.56  thf('0', plain,
% 0.38/0.56      (![X51 : $i, X52 : $i]:
% 0.38/0.56         (((k7_relat_1 @ X52 @ X51) = (k5_relat_1 @ (k6_relat_1 @ X51) @ X52))
% 0.38/0.56          | ~ (v1_relat_1 @ X52))),
% 0.38/0.56      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.38/0.56  thf(t43_funct_1, conjecture,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.38/0.56       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.38/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.56    (~( ![A:$i,B:$i]:
% 0.38/0.56        ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.38/0.56          ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 0.38/0.56    inference('cnf.neg', [status(esa)], [t43_funct_1])).
% 0.38/0.56  thf('1', plain,
% 0.38/0.56      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A))
% 0.38/0.56         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('2', plain,
% 0.38/0.56      ((((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 0.38/0.56          != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))
% 0.38/0.56        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['0', '1'])).
% 0.38/0.56  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.38/0.56  thf('3', plain, (![X37 : $i]: (v1_relat_1 @ (k6_relat_1 @ X37))),
% 0.38/0.56      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.38/0.56  thf('4', plain,
% 0.38/0.56      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 0.38/0.56         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.38/0.56      inference('demod', [status(thm)], ['2', '3'])).
% 0.38/0.56  thf(t78_relat_1, axiom,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ( v1_relat_1 @ A ) =>
% 0.38/0.56       ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A ) = ( A ) ) ))).
% 0.38/0.56  thf('5', plain,
% 0.38/0.56      (![X45 : $i]:
% 0.38/0.56         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X45)) @ X45) = (X45))
% 0.38/0.56          | ~ (v1_relat_1 @ X45))),
% 0.38/0.56      inference('cnf', [status(esa)], [t78_relat_1])).
% 0.38/0.56  thf(t123_relat_1, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( v1_relat_1 @ B ) =>
% 0.38/0.56       ( ( k8_relat_1 @ A @ B ) = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ))).
% 0.38/0.56  thf('6', plain,
% 0.38/0.56      (![X38 : $i, X39 : $i]:
% 0.38/0.56         (((k8_relat_1 @ X39 @ X38) = (k5_relat_1 @ X38 @ (k6_relat_1 @ X39)))
% 0.38/0.56          | ~ (v1_relat_1 @ X38))),
% 0.38/0.56      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.38/0.56  thf(t139_relat_1, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( v1_relat_1 @ B ) =>
% 0.38/0.56       ( ![C:$i]:
% 0.38/0.56         ( ( v1_relat_1 @ C ) =>
% 0.38/0.56           ( ( k8_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) =
% 0.38/0.56             ( k5_relat_1 @ B @ ( k8_relat_1 @ A @ C ) ) ) ) ) ))).
% 0.38/0.56  thf('7', plain,
% 0.38/0.56      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.38/0.56         (~ (v1_relat_1 @ X40)
% 0.38/0.56          | ((k8_relat_1 @ X42 @ (k5_relat_1 @ X41 @ X40))
% 0.38/0.56              = (k5_relat_1 @ X41 @ (k8_relat_1 @ X42 @ X40)))
% 0.38/0.56          | ~ (v1_relat_1 @ X41))),
% 0.38/0.56      inference('cnf', [status(esa)], [t139_relat_1])).
% 0.38/0.56  thf('8', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.56         (((k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ X0))
% 0.38/0.56            = (k5_relat_1 @ X0 @ (k8_relat_1 @ X2 @ (k6_relat_1 @ X1))))
% 0.38/0.56          | ~ (v1_relat_1 @ X0)
% 0.38/0.56          | ~ (v1_relat_1 @ X0)
% 0.38/0.56          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.38/0.56      inference('sup+', [status(thm)], ['6', '7'])).
% 0.38/0.56  thf('9', plain, (![X37 : $i]: (v1_relat_1 @ (k6_relat_1 @ X37))),
% 0.38/0.56      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.38/0.56  thf('10', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.56         (((k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ X0))
% 0.38/0.56            = (k5_relat_1 @ X0 @ (k8_relat_1 @ X2 @ (k6_relat_1 @ X1))))
% 0.38/0.56          | ~ (v1_relat_1 @ X0)
% 0.38/0.56          | ~ (v1_relat_1 @ X0))),
% 0.38/0.56      inference('demod', [status(thm)], ['8', '9'])).
% 0.38/0.56  thf('11', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.56         (~ (v1_relat_1 @ X0)
% 0.38/0.56          | ((k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ X0))
% 0.38/0.56              = (k5_relat_1 @ X0 @ (k8_relat_1 @ X2 @ (k6_relat_1 @ X1)))))),
% 0.38/0.56      inference('simplify', [status(thm)], ['10'])).
% 0.38/0.56  thf('12', plain,
% 0.38/0.56      (![X38 : $i, X39 : $i]:
% 0.38/0.56         (((k8_relat_1 @ X39 @ X38) = (k5_relat_1 @ X38 @ (k6_relat_1 @ X39)))
% 0.38/0.56          | ~ (v1_relat_1 @ X38))),
% 0.38/0.56      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.38/0.56  thf('13', plain,
% 0.38/0.56      (![X51 : $i, X52 : $i]:
% 0.38/0.56         (((k7_relat_1 @ X52 @ X51) = (k5_relat_1 @ (k6_relat_1 @ X51) @ X52))
% 0.38/0.56          | ~ (v1_relat_1 @ X52))),
% 0.38/0.56      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.38/0.56  thf('14', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         (((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.38/0.56            = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.38/0.56          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.38/0.56          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.38/0.56      inference('sup+', [status(thm)], ['12', '13'])).
% 0.38/0.56  thf('15', plain, (![X37 : $i]: (v1_relat_1 @ (k6_relat_1 @ X37))),
% 0.38/0.56      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.38/0.56  thf('16', plain, (![X37 : $i]: (v1_relat_1 @ (k6_relat_1 @ X37))),
% 0.38/0.56      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.38/0.56  thf('17', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.38/0.56           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.38/0.56      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.38/0.56  thf('18', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.56         (~ (v1_relat_1 @ X0)
% 0.38/0.56          | ((k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ X0))
% 0.38/0.56              = (k5_relat_1 @ X0 @ (k7_relat_1 @ (k6_relat_1 @ X2) @ X1))))),
% 0.38/0.56      inference('demod', [status(thm)], ['11', '17'])).
% 0.38/0.56  thf('19', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         (((k8_relat_1 @ X1 @ 
% 0.38/0.56            (k8_relat_1 @ X0 @ 
% 0.38/0.56             (k6_relat_1 @ (k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))))
% 0.38/0.56            = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.38/0.56          | ~ (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.38/0.56          | ~ (v1_relat_1 @ 
% 0.38/0.56               (k6_relat_1 @ 
% 0.38/0.56                (k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))))),
% 0.38/0.56      inference('sup+', [status(thm)], ['5', '18'])).
% 0.38/0.56  thf(t71_relat_1, axiom,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.38/0.56       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.38/0.56  thf('20', plain, (![X43 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X43)) = (X43))),
% 0.38/0.56      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.38/0.56  thf(t90_relat_1, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( v1_relat_1 @ B ) =>
% 0.38/0.56       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 0.38/0.56         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.38/0.56  thf('21', plain,
% 0.38/0.56      (![X49 : $i, X50 : $i]:
% 0.38/0.56         (((k1_relat_1 @ (k7_relat_1 @ X49 @ X50))
% 0.38/0.56            = (k3_xboole_0 @ (k1_relat_1 @ X49) @ X50))
% 0.38/0.56          | ~ (v1_relat_1 @ X49))),
% 0.38/0.56      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.38/0.56  thf('22', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         (((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.38/0.56            = (k3_xboole_0 @ X0 @ X1))
% 0.38/0.56          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.38/0.56      inference('sup+', [status(thm)], ['20', '21'])).
% 0.38/0.56  thf('23', plain, (![X37 : $i]: (v1_relat_1 @ (k6_relat_1 @ X37))),
% 0.38/0.56      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.38/0.56  thf('24', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         ((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.38/0.56           = (k3_xboole_0 @ X0 @ X1))),
% 0.38/0.56      inference('demod', [status(thm)], ['22', '23'])).
% 0.38/0.56  thf('25', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.38/0.56           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.38/0.56      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.38/0.56  thf('26', plain,
% 0.38/0.56      (![X38 : $i, X39 : $i]:
% 0.38/0.56         (((k8_relat_1 @ X39 @ X38) = (k5_relat_1 @ X38 @ (k6_relat_1 @ X39)))
% 0.38/0.56          | ~ (v1_relat_1 @ X38))),
% 0.38/0.56      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.38/0.56  thf(commutativity_k2_tarski, axiom,
% 0.38/0.56    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.38/0.56  thf('27', plain,
% 0.38/0.56      (![X4 : $i, X5 : $i]: ((k2_tarski @ X5 @ X4) = (k2_tarski @ X4 @ X5))),
% 0.38/0.56      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.38/0.56  thf(t12_setfam_1, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.38/0.56  thf('28', plain,
% 0.38/0.56      (![X33 : $i, X34 : $i]:
% 0.38/0.56         ((k1_setfam_1 @ (k2_tarski @ X33 @ X34)) = (k3_xboole_0 @ X33 @ X34))),
% 0.38/0.56      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.38/0.56  thf('29', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.38/0.56      inference('sup+', [status(thm)], ['27', '28'])).
% 0.38/0.56  thf('30', plain,
% 0.38/0.56      (![X33 : $i, X34 : $i]:
% 0.38/0.56         ((k1_setfam_1 @ (k2_tarski @ X33 @ X34)) = (k3_xboole_0 @ X33 @ X34))),
% 0.38/0.56      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.38/0.56  thf('31', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.38/0.56      inference('sup+', [status(thm)], ['29', '30'])).
% 0.38/0.56  thf(t17_xboole_1, axiom,
% 0.38/0.56    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.38/0.56  thf('32', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.38/0.56      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.38/0.56  thf('33', plain, (![X44 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X44)) = (X44))),
% 0.38/0.56      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.38/0.56  thf(t79_relat_1, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( v1_relat_1 @ B ) =>
% 0.38/0.56       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.38/0.56         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 0.38/0.56  thf('34', plain,
% 0.38/0.56      (![X46 : $i, X47 : $i]:
% 0.38/0.56         (~ (r1_tarski @ (k2_relat_1 @ X46) @ X47)
% 0.38/0.56          | ((k5_relat_1 @ X46 @ (k6_relat_1 @ X47)) = (X46))
% 0.38/0.56          | ~ (v1_relat_1 @ X46))),
% 0.38/0.56      inference('cnf', [status(esa)], [t79_relat_1])).
% 0.38/0.56  thf('35', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         (~ (r1_tarski @ X0 @ X1)
% 0.38/0.56          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.38/0.56          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 0.38/0.56              = (k6_relat_1 @ X0)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['33', '34'])).
% 0.38/0.56  thf('36', plain, (![X37 : $i]: (v1_relat_1 @ (k6_relat_1 @ X37))),
% 0.38/0.56      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.38/0.56  thf('37', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         (~ (r1_tarski @ X0 @ X1)
% 0.38/0.56          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 0.38/0.56              = (k6_relat_1 @ X0)))),
% 0.38/0.56      inference('demod', [status(thm)], ['35', '36'])).
% 0.38/0.56  thf('38', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         ((k5_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 0.38/0.56           (k6_relat_1 @ X0)) = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['32', '37'])).
% 0.38/0.56  thf('39', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         ((k5_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.38/0.56           (k6_relat_1 @ X0)) = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.38/0.56      inference('sup+', [status(thm)], ['31', '38'])).
% 0.38/0.56  thf('40', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         (((k8_relat_1 @ X0 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.38/0.56            = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))
% 0.38/0.56          | ~ (v1_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.38/0.56      inference('sup+', [status(thm)], ['26', '39'])).
% 0.38/0.56  thf('41', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.38/0.56           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.38/0.56      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.38/0.56  thf('42', plain, (![X37 : $i]: (v1_relat_1 @ (k6_relat_1 @ X37))),
% 0.38/0.56      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.38/0.56  thf('43', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         ((k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 0.38/0.56           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.38/0.56      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.38/0.56  thf('44', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.38/0.56           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.38/0.56      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.38/0.56  thf('45', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         ((k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 0.38/0.56           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.38/0.56      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.38/0.56  thf('46', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.38/0.56           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.38/0.56      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.38/0.56  thf('47', plain,
% 0.38/0.56      (![X38 : $i, X39 : $i]:
% 0.38/0.56         (((k8_relat_1 @ X39 @ X38) = (k5_relat_1 @ X38 @ (k6_relat_1 @ X39)))
% 0.38/0.56          | ~ (v1_relat_1 @ X38))),
% 0.38/0.56      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.38/0.56  thf(dt_k5_relat_1, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.38/0.56       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.38/0.56  thf('48', plain,
% 0.38/0.56      (![X35 : $i, X36 : $i]:
% 0.38/0.56         (~ (v1_relat_1 @ X35)
% 0.38/0.56          | ~ (v1_relat_1 @ X36)
% 0.38/0.56          | (v1_relat_1 @ (k5_relat_1 @ X35 @ X36)))),
% 0.38/0.56      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.38/0.56  thf('49', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         ((v1_relat_1 @ (k8_relat_1 @ X1 @ X0))
% 0.38/0.56          | ~ (v1_relat_1 @ X0)
% 0.38/0.56          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.38/0.56          | ~ (v1_relat_1 @ X0))),
% 0.38/0.56      inference('sup+', [status(thm)], ['47', '48'])).
% 0.38/0.56  thf('50', plain, (![X37 : $i]: (v1_relat_1 @ (k6_relat_1 @ X37))),
% 0.38/0.56      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.38/0.56  thf('51', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         ((v1_relat_1 @ (k8_relat_1 @ X1 @ X0))
% 0.38/0.56          | ~ (v1_relat_1 @ X0)
% 0.38/0.56          | ~ (v1_relat_1 @ X0))),
% 0.38/0.56      inference('demod', [status(thm)], ['49', '50'])).
% 0.38/0.56  thf('52', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         (~ (v1_relat_1 @ X0) | (v1_relat_1 @ (k8_relat_1 @ X1 @ X0)))),
% 0.38/0.56      inference('simplify', [status(thm)], ['51'])).
% 0.38/0.56  thf('53', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         ((v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.38/0.56          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.38/0.56      inference('sup+', [status(thm)], ['46', '52'])).
% 0.38/0.56  thf('54', plain, (![X37 : $i]: (v1_relat_1 @ (k6_relat_1 @ X37))),
% 0.38/0.56      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.38/0.56  thf('55', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 0.38/0.56      inference('demod', [status(thm)], ['53', '54'])).
% 0.38/0.56  thf('56', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         ((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.38/0.56           = (k3_xboole_0 @ X0 @ X1))),
% 0.38/0.56      inference('demod', [status(thm)], ['22', '23'])).
% 0.38/0.56  thf('57', plain, (![X37 : $i]: (v1_relat_1 @ (k6_relat_1 @ X37))),
% 0.38/0.56      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.38/0.56  thf('58', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         ((k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))
% 0.38/0.56           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 0.38/0.56      inference('demod', [status(thm)],
% 0.38/0.56                ['19', '24', '25', '43', '44', '45', '55', '56', '57'])).
% 0.38/0.56  thf('59', plain,
% 0.38/0.56      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 0.38/0.56         != (k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))),
% 0.38/0.56      inference('demod', [status(thm)], ['4', '58'])).
% 0.38/0.56  thf('60', plain, ($false), inference('simplify', [status(thm)], ['59'])).
% 0.38/0.56  
% 0.38/0.56  % SZS output end Refutation
% 0.38/0.56  
% 0.38/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
