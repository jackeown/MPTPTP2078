%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QLJmDB5xfM

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:57 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 184 expanded)
%              Number of leaves         :   26 (  72 expanded)
%              Depth                    :   11
%              Number of atoms          :  735 (1405 expanded)
%              Number of equality atoms :   59 ( 111 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t123_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ B )
        = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X39: $i,X40: $i] :
      ( ( ( k8_relat_1 @ X40 @ X39 )
        = ( k5_relat_1 @ X39 @ ( k6_relat_1 @ X40 ) ) )
      | ~ ( v1_relat_1 @ X39 ) ) ),
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
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('4',plain,(
    ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ sk_B ) )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t78_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A )
        = A ) ) )).

thf('5',plain,(
    ! [X48: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X48 ) ) @ X48 )
        = X48 )
      | ~ ( v1_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('6',plain,(
    ! [X54: $i,X55: $i] :
      ( ( ( k7_relat_1 @ X55 @ X54 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X54 ) @ X55 ) )
      | ~ ( v1_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X39: $i,X40: $i] :
      ( ( ( k8_relat_1 @ X40 @ X39 )
        = ( k5_relat_1 @ X39 @ ( k6_relat_1 @ X40 ) ) )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('10',plain,(
    ! [X54: $i,X55: $i] :
      ( ( ( k7_relat_1 @ X55 @ X54 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X54 ) @ X55 ) )
      | ~ ( v1_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t112_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( k7_relat_1 @ ( k5_relat_1 @ B @ C ) @ A )
            = ( k5_relat_1 @ ( k7_relat_1 @ B @ A ) @ C ) ) ) ) )).

thf('11',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( v1_relat_1 @ X36 )
      | ( ( k7_relat_1 @ ( k5_relat_1 @ X37 @ X36 ) @ X38 )
        = ( k5_relat_1 @ ( k7_relat_1 @ X37 @ X38 ) @ X36 ) )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t112_relat_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X39: $i,X40: $i] :
      ( ( ( k8_relat_1 @ X40 @ X39 )
        = ( k5_relat_1 @ X39 @ ( k6_relat_1 @ X40 ) ) )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('17',plain,(
    ! [X54: $i,X55: $i] :
      ( ( ( k7_relat_1 @ X55 @ X54 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X54 ) @ X55 ) )
      | ~ ( v1_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('20',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X2 ) ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['15','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X2 ) @ X1 ) @ X0 )
        = ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['9','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('26',plain,(
    ! [X54: $i,X55: $i] :
      ( ( ( k7_relat_1 @ X55 @ X54 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X54 ) @ X55 ) )
      | ~ ( v1_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('27',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( v1_relat_1 @ X33 )
      | ~ ( v1_relat_1 @ X34 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X33 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['25','31'])).

thf('33',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k8_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) @ X0 )
      = ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['23','24','34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
        = ( k8_relat_1 @ X1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ) ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['8','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('39',plain,(
    ! [X52: $i,X53: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X52 @ X53 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X52 ) @ X53 ) )
      | ~ ( v1_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ ( k6_relat_1 @ X1 ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('41',plain,(
    ! [X46: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X46 ) )
      = X46 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('42',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,(
    ! [X39: $i,X40: $i] :
      ( ( ( k8_relat_1 @ X40 @ X39 )
        = ( k5_relat_1 @ X39 @ ( k6_relat_1 @ X40 ) ) )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('45',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_tarski @ X3 @ X2 )
      = ( k2_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('46',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X31 @ X32 ) )
      = ( k3_xboole_0 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X31 @ X32 ) )
      = ( k3_xboole_0 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('51',plain,(
    ! [X47: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X47 ) )
      = X47 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('52',plain,(
    ! [X49: $i,X50: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X49 ) @ X50 )
      | ( ( k5_relat_1 @ X49 @ ( k6_relat_1 @ X50 ) )
        = X49 )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['50','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['49','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
        = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['44','57'])).

thf('59',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['37','43','60','61','62'])).

thf('64',plain,(
    ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ sk_B ) )
 != ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','63'])).

thf('65',plain,(
    $false ),
    inference(simplify,[status(thm)],['64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QLJmDB5xfM
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:31:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.42/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.42/0.62  % Solved by: fo/fo7.sh
% 0.42/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.42/0.62  % done 298 iterations in 0.161s
% 0.42/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.42/0.62  % SZS output start Refutation
% 0.42/0.62  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.42/0.62  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.42/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.42/0.62  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.42/0.62  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.42/0.62  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.42/0.62  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.42/0.62  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.42/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.42/0.62  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.42/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.42/0.62  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.42/0.62  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.42/0.62  thf(t123_relat_1, axiom,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( v1_relat_1 @ B ) =>
% 0.42/0.62       ( ( k8_relat_1 @ A @ B ) = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ))).
% 0.42/0.62  thf('0', plain,
% 0.42/0.62      (![X39 : $i, X40 : $i]:
% 0.42/0.62         (((k8_relat_1 @ X40 @ X39) = (k5_relat_1 @ X39 @ (k6_relat_1 @ X40)))
% 0.42/0.62          | ~ (v1_relat_1 @ X39))),
% 0.42/0.62      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.42/0.62  thf(t43_funct_1, conjecture,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.42/0.62       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.42/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.42/0.62    (~( ![A:$i,B:$i]:
% 0.42/0.62        ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.42/0.62          ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 0.42/0.62    inference('cnf.neg', [status(esa)], [t43_funct_1])).
% 0.42/0.62  thf('1', plain,
% 0.42/0.62      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A))
% 0.42/0.62         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('2', plain,
% 0.42/0.62      ((((k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B))
% 0.42/0.62          != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))
% 0.42/0.62        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_B)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['0', '1'])).
% 0.42/0.62  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.42/0.62  thf('3', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 0.42/0.62      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.42/0.62  thf('4', plain,
% 0.42/0.62      (((k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B))
% 0.42/0.62         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.42/0.62      inference('demod', [status(thm)], ['2', '3'])).
% 0.42/0.62  thf(t78_relat_1, axiom,
% 0.42/0.62    (![A:$i]:
% 0.42/0.62     ( ( v1_relat_1 @ A ) =>
% 0.42/0.62       ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A ) = ( A ) ) ))).
% 0.42/0.62  thf('5', plain,
% 0.42/0.62      (![X48 : $i]:
% 0.42/0.62         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X48)) @ X48) = (X48))
% 0.42/0.62          | ~ (v1_relat_1 @ X48))),
% 0.42/0.62      inference('cnf', [status(esa)], [t78_relat_1])).
% 0.42/0.62  thf(t94_relat_1, axiom,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( v1_relat_1 @ B ) =>
% 0.42/0.62       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.42/0.62  thf('6', plain,
% 0.42/0.62      (![X54 : $i, X55 : $i]:
% 0.42/0.62         (((k7_relat_1 @ X55 @ X54) = (k5_relat_1 @ (k6_relat_1 @ X54) @ X55))
% 0.42/0.62          | ~ (v1_relat_1 @ X55))),
% 0.42/0.62      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.42/0.62  thf('7', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         (((k7_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (X0))
% 0.42/0.62          | ~ (v1_relat_1 @ X0)
% 0.42/0.62          | ~ (v1_relat_1 @ X0))),
% 0.42/0.62      inference('sup+', [status(thm)], ['5', '6'])).
% 0.42/0.62  thf('8', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         (~ (v1_relat_1 @ X0) | ((k7_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (X0)))),
% 0.42/0.62      inference('simplify', [status(thm)], ['7'])).
% 0.42/0.62  thf('9', plain,
% 0.42/0.62      (![X39 : $i, X40 : $i]:
% 0.42/0.62         (((k8_relat_1 @ X40 @ X39) = (k5_relat_1 @ X39 @ (k6_relat_1 @ X40)))
% 0.42/0.62          | ~ (v1_relat_1 @ X39))),
% 0.42/0.62      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.42/0.62  thf('10', plain,
% 0.42/0.62      (![X54 : $i, X55 : $i]:
% 0.42/0.62         (((k7_relat_1 @ X55 @ X54) = (k5_relat_1 @ (k6_relat_1 @ X54) @ X55))
% 0.42/0.62          | ~ (v1_relat_1 @ X55))),
% 0.42/0.62      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.42/0.62  thf(t112_relat_1, axiom,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( v1_relat_1 @ B ) =>
% 0.42/0.62       ( ![C:$i]:
% 0.42/0.62         ( ( v1_relat_1 @ C ) =>
% 0.42/0.62           ( ( k7_relat_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 0.42/0.62             ( k5_relat_1 @ ( k7_relat_1 @ B @ A ) @ C ) ) ) ) ))).
% 0.42/0.62  thf('11', plain,
% 0.42/0.62      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.42/0.62         (~ (v1_relat_1 @ X36)
% 0.42/0.62          | ((k7_relat_1 @ (k5_relat_1 @ X37 @ X36) @ X38)
% 0.42/0.62              = (k5_relat_1 @ (k7_relat_1 @ X37 @ X38) @ X36))
% 0.42/0.62          | ~ (v1_relat_1 @ X37))),
% 0.42/0.62      inference('cnf', [status(esa)], [t112_relat_1])).
% 0.42/0.62  thf('12', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.62         (((k7_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 0.42/0.62            = (k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X2) @ X1))
% 0.42/0.62          | ~ (v1_relat_1 @ X1)
% 0.42/0.62          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.42/0.62          | ~ (v1_relat_1 @ X1))),
% 0.42/0.62      inference('sup+', [status(thm)], ['10', '11'])).
% 0.42/0.62  thf('13', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 0.42/0.62      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.42/0.62  thf('14', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.62         (((k7_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 0.42/0.62            = (k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X2) @ X1))
% 0.42/0.62          | ~ (v1_relat_1 @ X1)
% 0.42/0.62          | ~ (v1_relat_1 @ X1))),
% 0.42/0.62      inference('demod', [status(thm)], ['12', '13'])).
% 0.42/0.62  thf('15', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.62         (~ (v1_relat_1 @ X1)
% 0.42/0.62          | ((k7_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 0.42/0.62              = (k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X2) @ X1)))),
% 0.42/0.62      inference('simplify', [status(thm)], ['14'])).
% 0.42/0.62  thf('16', plain,
% 0.42/0.62      (![X39 : $i, X40 : $i]:
% 0.42/0.62         (((k8_relat_1 @ X40 @ X39) = (k5_relat_1 @ X39 @ (k6_relat_1 @ X40)))
% 0.42/0.62          | ~ (v1_relat_1 @ X39))),
% 0.42/0.62      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.42/0.62  thf('17', plain,
% 0.42/0.62      (![X54 : $i, X55 : $i]:
% 0.42/0.62         (((k7_relat_1 @ X55 @ X54) = (k5_relat_1 @ (k6_relat_1 @ X54) @ X55))
% 0.42/0.62          | ~ (v1_relat_1 @ X55))),
% 0.42/0.62      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.42/0.62  thf('18', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         (((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.42/0.62            = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.42/0.62          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.42/0.62          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.42/0.62      inference('sup+', [status(thm)], ['16', '17'])).
% 0.42/0.62  thf('19', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 0.42/0.62      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.42/0.62  thf('20', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 0.42/0.62      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.42/0.62  thf('21', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.42/0.62           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.42/0.62      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.42/0.62  thf('22', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.62         (~ (v1_relat_1 @ X1)
% 0.42/0.62          | ((k7_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 0.42/0.62              = (k5_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X2)) @ X1)))),
% 0.42/0.62      inference('demod', [status(thm)], ['15', '21'])).
% 0.42/0.62  thf('23', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.62         (((k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X2) @ X1) @ X0)
% 0.42/0.62            = (k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))
% 0.42/0.62          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.42/0.62          | ~ (v1_relat_1 @ (k6_relat_1 @ X2)))),
% 0.42/0.62      inference('sup+', [status(thm)], ['9', '22'])).
% 0.42/0.62  thf('24', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.42/0.62           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.42/0.62      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.42/0.62  thf('25', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.42/0.62           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.42/0.62      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.42/0.62  thf('26', plain,
% 0.42/0.62      (![X54 : $i, X55 : $i]:
% 0.42/0.62         (((k7_relat_1 @ X55 @ X54) = (k5_relat_1 @ (k6_relat_1 @ X54) @ X55))
% 0.42/0.62          | ~ (v1_relat_1 @ X55))),
% 0.42/0.62      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.42/0.62  thf(dt_k5_relat_1, axiom,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.42/0.62       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.42/0.62  thf('27', plain,
% 0.42/0.62      (![X33 : $i, X34 : $i]:
% 0.42/0.62         (~ (v1_relat_1 @ X33)
% 0.42/0.62          | ~ (v1_relat_1 @ X34)
% 0.42/0.62          | (v1_relat_1 @ (k5_relat_1 @ X33 @ X34)))),
% 0.42/0.62      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.42/0.62  thf('28', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         ((v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.42/0.62          | ~ (v1_relat_1 @ X1)
% 0.42/0.62          | ~ (v1_relat_1 @ X1)
% 0.42/0.62          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.42/0.62      inference('sup+', [status(thm)], ['26', '27'])).
% 0.42/0.62  thf('29', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 0.42/0.62      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.42/0.62  thf('30', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         ((v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.42/0.62          | ~ (v1_relat_1 @ X1)
% 0.42/0.62          | ~ (v1_relat_1 @ X1))),
% 0.42/0.62      inference('demod', [status(thm)], ['28', '29'])).
% 0.42/0.62  thf('31', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         (~ (v1_relat_1 @ X1) | (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.42/0.62      inference('simplify', [status(thm)], ['30'])).
% 0.42/0.62  thf('32', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         ((v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.42/0.62          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.42/0.62      inference('sup+', [status(thm)], ['25', '31'])).
% 0.42/0.62  thf('33', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 0.42/0.62      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.42/0.62  thf('34', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.42/0.62      inference('demod', [status(thm)], ['32', '33'])).
% 0.42/0.62  thf('35', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 0.42/0.62      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.42/0.62  thf('36', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.62         ((k7_relat_1 @ (k8_relat_1 @ X2 @ (k6_relat_1 @ X1)) @ X0)
% 0.42/0.62           = (k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 0.42/0.62      inference('demod', [status(thm)], ['23', '24', '34', '35'])).
% 0.42/0.62  thf('37', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         (((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 0.42/0.62            = (k8_relat_1 @ X1 @ 
% 0.42/0.62               (k8_relat_1 @ X0 @ 
% 0.42/0.62                (k6_relat_1 @ 
% 0.42/0.62                 (k1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))))))
% 0.42/0.62          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 0.42/0.62      inference('sup+', [status(thm)], ['8', '36'])).
% 0.42/0.62  thf('38', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.63         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.42/0.63           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.42/0.63      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.42/0.63  thf(t90_relat_1, axiom,
% 0.42/0.63    (![A:$i,B:$i]:
% 0.42/0.63     ( ( v1_relat_1 @ B ) =>
% 0.42/0.63       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 0.42/0.63         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.42/0.63  thf('39', plain,
% 0.42/0.63      (![X52 : $i, X53 : $i]:
% 0.42/0.63         (((k1_relat_1 @ (k7_relat_1 @ X52 @ X53))
% 0.42/0.63            = (k3_xboole_0 @ (k1_relat_1 @ X52) @ X53))
% 0.42/0.63          | ~ (v1_relat_1 @ X52))),
% 0.42/0.63      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.42/0.63  thf('40', plain,
% 0.42/0.63      (![X0 : $i, X1 : $i]:
% 0.42/0.63         (((k1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.42/0.63            = (k3_xboole_0 @ (k1_relat_1 @ (k6_relat_1 @ X1)) @ X0))
% 0.42/0.63          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.42/0.63      inference('sup+', [status(thm)], ['38', '39'])).
% 0.42/0.63  thf(t71_relat_1, axiom,
% 0.42/0.63    (![A:$i]:
% 0.42/0.63     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.42/0.63       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.42/0.63  thf('41', plain, (![X46 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X46)) = (X46))),
% 0.42/0.63      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.42/0.63  thf('42', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 0.42/0.63      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.42/0.63  thf('43', plain,
% 0.42/0.63      (![X0 : $i, X1 : $i]:
% 0.42/0.63         ((k1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.42/0.63           = (k3_xboole_0 @ X1 @ X0))),
% 0.42/0.63      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.42/0.63  thf('44', plain,
% 0.42/0.63      (![X39 : $i, X40 : $i]:
% 0.42/0.63         (((k8_relat_1 @ X40 @ X39) = (k5_relat_1 @ X39 @ (k6_relat_1 @ X40)))
% 0.42/0.63          | ~ (v1_relat_1 @ X39))),
% 0.42/0.63      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.42/0.63  thf(commutativity_k2_tarski, axiom,
% 0.42/0.63    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.42/0.63  thf('45', plain,
% 0.42/0.63      (![X2 : $i, X3 : $i]: ((k2_tarski @ X3 @ X2) = (k2_tarski @ X2 @ X3))),
% 0.42/0.63      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.42/0.63  thf(t12_setfam_1, axiom,
% 0.42/0.63    (![A:$i,B:$i]:
% 0.42/0.63     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.42/0.63  thf('46', plain,
% 0.42/0.63      (![X31 : $i, X32 : $i]:
% 0.42/0.63         ((k1_setfam_1 @ (k2_tarski @ X31 @ X32)) = (k3_xboole_0 @ X31 @ X32))),
% 0.42/0.63      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.42/0.63  thf('47', plain,
% 0.42/0.63      (![X0 : $i, X1 : $i]:
% 0.42/0.63         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.42/0.63      inference('sup+', [status(thm)], ['45', '46'])).
% 0.42/0.63  thf('48', plain,
% 0.42/0.63      (![X31 : $i, X32 : $i]:
% 0.42/0.63         ((k1_setfam_1 @ (k2_tarski @ X31 @ X32)) = (k3_xboole_0 @ X31 @ X32))),
% 0.42/0.63      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.42/0.63  thf('49', plain,
% 0.42/0.63      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.42/0.63      inference('sup+', [status(thm)], ['47', '48'])).
% 0.42/0.63  thf(t17_xboole_1, axiom,
% 0.42/0.63    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.42/0.63  thf('50', plain,
% 0.42/0.63      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.42/0.63      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.42/0.63  thf('51', plain, (![X47 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X47)) = (X47))),
% 0.42/0.63      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.42/0.63  thf(t79_relat_1, axiom,
% 0.42/0.63    (![A:$i,B:$i]:
% 0.42/0.63     ( ( v1_relat_1 @ B ) =>
% 0.42/0.63       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.42/0.63         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 0.42/0.63  thf('52', plain,
% 0.42/0.63      (![X49 : $i, X50 : $i]:
% 0.42/0.63         (~ (r1_tarski @ (k2_relat_1 @ X49) @ X50)
% 0.42/0.63          | ((k5_relat_1 @ X49 @ (k6_relat_1 @ X50)) = (X49))
% 0.42/0.63          | ~ (v1_relat_1 @ X49))),
% 0.42/0.63      inference('cnf', [status(esa)], [t79_relat_1])).
% 0.42/0.63  thf('53', plain,
% 0.42/0.63      (![X0 : $i, X1 : $i]:
% 0.42/0.63         (~ (r1_tarski @ X0 @ X1)
% 0.42/0.63          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.42/0.63          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 0.42/0.63              = (k6_relat_1 @ X0)))),
% 0.42/0.63      inference('sup-', [status(thm)], ['51', '52'])).
% 0.42/0.63  thf('54', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 0.42/0.63      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.42/0.63  thf('55', plain,
% 0.42/0.63      (![X0 : $i, X1 : $i]:
% 0.42/0.63         (~ (r1_tarski @ X0 @ X1)
% 0.42/0.63          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 0.42/0.63              = (k6_relat_1 @ X0)))),
% 0.42/0.63      inference('demod', [status(thm)], ['53', '54'])).
% 0.42/0.63  thf('56', plain,
% 0.42/0.63      (![X0 : $i, X1 : $i]:
% 0.42/0.63         ((k5_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 0.42/0.63           (k6_relat_1 @ X0)) = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.42/0.63      inference('sup-', [status(thm)], ['50', '55'])).
% 0.42/0.63  thf('57', plain,
% 0.42/0.63      (![X0 : $i, X1 : $i]:
% 0.42/0.63         ((k5_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.42/0.63           (k6_relat_1 @ X0)) = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.42/0.63      inference('sup+', [status(thm)], ['49', '56'])).
% 0.42/0.63  thf('58', plain,
% 0.42/0.63      (![X0 : $i, X1 : $i]:
% 0.42/0.63         (((k8_relat_1 @ X0 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.42/0.63            = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))
% 0.42/0.63          | ~ (v1_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.42/0.63      inference('sup+', [status(thm)], ['44', '57'])).
% 0.42/0.63  thf('59', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 0.42/0.63      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.42/0.63  thf('60', plain,
% 0.42/0.63      (![X0 : $i, X1 : $i]:
% 0.42/0.63         ((k8_relat_1 @ X0 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.42/0.63           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.42/0.63      inference('demod', [status(thm)], ['58', '59'])).
% 0.42/0.63  thf('61', plain,
% 0.42/0.63      (![X0 : $i, X1 : $i]:
% 0.42/0.63         ((k8_relat_1 @ X0 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.42/0.63           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.42/0.63      inference('demod', [status(thm)], ['58', '59'])).
% 0.42/0.63  thf('62', plain,
% 0.42/0.63      (![X0 : $i, X1 : $i]:
% 0.42/0.63         (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.42/0.63      inference('demod', [status(thm)], ['32', '33'])).
% 0.42/0.63  thf('63', plain,
% 0.42/0.63      (![X0 : $i, X1 : $i]:
% 0.42/0.63         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 0.42/0.63           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.42/0.63      inference('demod', [status(thm)], ['37', '43', '60', '61', '62'])).
% 0.42/0.63  thf('64', plain,
% 0.42/0.63      (((k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B))
% 0.42/0.63         != (k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B)))),
% 0.42/0.63      inference('demod', [status(thm)], ['4', '63'])).
% 0.42/0.63  thf('65', plain, ($false), inference('simplify', [status(thm)], ['64'])).
% 0.42/0.63  
% 0.42/0.63  % SZS output end Refutation
% 0.42/0.63  
% 0.47/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
