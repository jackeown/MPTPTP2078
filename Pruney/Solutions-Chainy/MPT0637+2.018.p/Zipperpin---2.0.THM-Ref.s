%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1kA1HIP5wo

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:57 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 241 expanded)
%              Number of leaves         :   26 (  93 expanded)
%              Depth                    :   14
%              Number of atoms          :  781 (1842 expanded)
%              Number of equality atoms :   59 ( 154 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
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
    ! [X36: $i,X37: $i] :
      ( ( ( k8_relat_1 @ X37 @ X36 )
        = ( k5_relat_1 @ X36 @ ( k6_relat_1 @ X37 ) ) )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t139_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( k8_relat_1 @ A @ ( k5_relat_1 @ B @ C ) )
            = ( k5_relat_1 @ B @ ( k8_relat_1 @ A @ C ) ) ) ) ) )).

thf('7',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( v1_relat_1 @ X38 )
      | ( ( k8_relat_1 @ X40 @ ( k5_relat_1 @ X39 @ X38 ) )
        = ( k5_relat_1 @ X39 @ ( k8_relat_1 @ X40 @ X38 ) ) )
      | ~ ( v1_relat_1 @ X39 ) ) ),
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
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
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
    ! [X36: $i,X37: $i] :
      ( ( ( k8_relat_1 @ X37 @ X36 )
        = ( k5_relat_1 @ X36 @ ( k6_relat_1 @ X37 ) ) )
      | ~ ( v1_relat_1 @ X36 ) ) ),
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
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('16',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
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
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
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
    ! [X36: $i,X37: $i] :
      ( ( ( k8_relat_1 @ X37 @ X36 )
        = ( k5_relat_1 @ X36 @ ( k6_relat_1 @ X37 ) ) )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('27',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_tarski @ X3 @ X2 )
      = ( k2_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('28',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X31 @ X32 ) )
      = ( k3_xboole_0 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X31 @ X32 ) )
      = ( k3_xboole_0 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('34',plain,(
    ! [X51: $i,X52: $i] :
      ( ( ( k7_relat_1 @ X52 @ X51 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X51 ) @ X52 ) )
      | ~ ( v1_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t44_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) )).

thf('35',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( v1_relat_1 @ X41 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X42 @ X41 ) ) @ ( k1_relat_1 @ X42 ) )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t44_relat_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X43: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X43 ) )
      = X43 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('38',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['33','40'])).

thf('42',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['32','43'])).

thf('45',plain,(
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

thf('46',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X46 ) @ X47 )
      | ( ( k5_relat_1 @ X46 @ ( k6_relat_1 @ X47 ) )
        = X46 )
      | ~ ( v1_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['44','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['31','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
        = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['26','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('54',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('59',plain,(
    ! [X36: $i,X37: $i] :
      ( ( ( k8_relat_1 @ X37 @ X36 )
        = ( k5_relat_1 @ X36 @ ( k6_relat_1 @ X37 ) ) )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('60',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( v1_relat_1 @ X33 )
      | ~ ( v1_relat_1 @ X34 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X33 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['58','64'])).

thf('66',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('69',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['19','24','25','55','56','57','67','68','69'])).

thf('71',plain,(
    ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
 != ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['4','70'])).

thf('72',plain,(
    $false ),
    inference(simplify,[status(thm)],['71'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1kA1HIP5wo
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:06:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.39/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.39/0.61  % Solved by: fo/fo7.sh
% 0.39/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.61  % done 367 iterations in 0.158s
% 0.39/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.39/0.61  % SZS output start Refutation
% 0.39/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.61  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.39/0.61  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.39/0.61  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.39/0.61  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.39/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.61  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.39/0.61  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.39/0.61  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.39/0.61  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.39/0.61  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.39/0.61  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.39/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.61  thf(t94_relat_1, axiom,
% 0.39/0.61    (![A:$i,B:$i]:
% 0.39/0.61     ( ( v1_relat_1 @ B ) =>
% 0.39/0.61       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.39/0.61  thf('0', plain,
% 0.39/0.61      (![X51 : $i, X52 : $i]:
% 0.39/0.61         (((k7_relat_1 @ X52 @ X51) = (k5_relat_1 @ (k6_relat_1 @ X51) @ X52))
% 0.39/0.61          | ~ (v1_relat_1 @ X52))),
% 0.39/0.61      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.39/0.61  thf(t43_funct_1, conjecture,
% 0.39/0.61    (![A:$i,B:$i]:
% 0.39/0.61     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.39/0.61       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.39/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.61    (~( ![A:$i,B:$i]:
% 0.39/0.61        ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.39/0.61          ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 0.39/0.61    inference('cnf.neg', [status(esa)], [t43_funct_1])).
% 0.39/0.61  thf('1', plain,
% 0.39/0.61      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A))
% 0.39/0.61         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('2', plain,
% 0.39/0.61      ((((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 0.39/0.61          != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))
% 0.39/0.61        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A)))),
% 0.39/0.61      inference('sup-', [status(thm)], ['0', '1'])).
% 0.39/0.61  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.39/0.61  thf('3', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 0.39/0.61      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.39/0.61  thf('4', plain,
% 0.39/0.61      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 0.39/0.61         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.39/0.61      inference('demod', [status(thm)], ['2', '3'])).
% 0.39/0.61  thf(t78_relat_1, axiom,
% 0.39/0.61    (![A:$i]:
% 0.39/0.61     ( ( v1_relat_1 @ A ) =>
% 0.39/0.61       ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A ) = ( A ) ) ))).
% 0.39/0.61  thf('5', plain,
% 0.39/0.61      (![X45 : $i]:
% 0.39/0.61         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X45)) @ X45) = (X45))
% 0.39/0.61          | ~ (v1_relat_1 @ X45))),
% 0.39/0.61      inference('cnf', [status(esa)], [t78_relat_1])).
% 0.39/0.61  thf(t123_relat_1, axiom,
% 0.39/0.61    (![A:$i,B:$i]:
% 0.39/0.61     ( ( v1_relat_1 @ B ) =>
% 0.39/0.61       ( ( k8_relat_1 @ A @ B ) = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ))).
% 0.39/0.61  thf('6', plain,
% 0.39/0.61      (![X36 : $i, X37 : $i]:
% 0.39/0.61         (((k8_relat_1 @ X37 @ X36) = (k5_relat_1 @ X36 @ (k6_relat_1 @ X37)))
% 0.39/0.61          | ~ (v1_relat_1 @ X36))),
% 0.39/0.61      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.39/0.61  thf(t139_relat_1, axiom,
% 0.39/0.61    (![A:$i,B:$i]:
% 0.39/0.61     ( ( v1_relat_1 @ B ) =>
% 0.39/0.61       ( ![C:$i]:
% 0.39/0.61         ( ( v1_relat_1 @ C ) =>
% 0.39/0.61           ( ( k8_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) =
% 0.39/0.61             ( k5_relat_1 @ B @ ( k8_relat_1 @ A @ C ) ) ) ) ) ))).
% 0.39/0.61  thf('7', plain,
% 0.39/0.61      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.39/0.61         (~ (v1_relat_1 @ X38)
% 0.39/0.61          | ((k8_relat_1 @ X40 @ (k5_relat_1 @ X39 @ X38))
% 0.39/0.61              = (k5_relat_1 @ X39 @ (k8_relat_1 @ X40 @ X38)))
% 0.39/0.61          | ~ (v1_relat_1 @ X39))),
% 0.39/0.61      inference('cnf', [status(esa)], [t139_relat_1])).
% 0.39/0.61  thf('8', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.61         (((k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ X0))
% 0.39/0.61            = (k5_relat_1 @ X0 @ (k8_relat_1 @ X2 @ (k6_relat_1 @ X1))))
% 0.39/0.61          | ~ (v1_relat_1 @ X0)
% 0.39/0.61          | ~ (v1_relat_1 @ X0)
% 0.39/0.61          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.39/0.61      inference('sup+', [status(thm)], ['6', '7'])).
% 0.39/0.61  thf('9', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 0.39/0.61      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.39/0.61  thf('10', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.61         (((k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ X0))
% 0.39/0.61            = (k5_relat_1 @ X0 @ (k8_relat_1 @ X2 @ (k6_relat_1 @ X1))))
% 0.39/0.61          | ~ (v1_relat_1 @ X0)
% 0.39/0.61          | ~ (v1_relat_1 @ X0))),
% 0.39/0.61      inference('demod', [status(thm)], ['8', '9'])).
% 0.39/0.61  thf('11', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.61         (~ (v1_relat_1 @ X0)
% 0.39/0.61          | ((k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ X0))
% 0.39/0.61              = (k5_relat_1 @ X0 @ (k8_relat_1 @ X2 @ (k6_relat_1 @ X1)))))),
% 0.39/0.61      inference('simplify', [status(thm)], ['10'])).
% 0.39/0.61  thf('12', plain,
% 0.39/0.61      (![X36 : $i, X37 : $i]:
% 0.39/0.61         (((k8_relat_1 @ X37 @ X36) = (k5_relat_1 @ X36 @ (k6_relat_1 @ X37)))
% 0.39/0.61          | ~ (v1_relat_1 @ X36))),
% 0.39/0.61      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.39/0.61  thf('13', plain,
% 0.39/0.61      (![X51 : $i, X52 : $i]:
% 0.39/0.61         (((k7_relat_1 @ X52 @ X51) = (k5_relat_1 @ (k6_relat_1 @ X51) @ X52))
% 0.39/0.61          | ~ (v1_relat_1 @ X52))),
% 0.39/0.61      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.39/0.61  thf('14', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         (((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.39/0.61            = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.39/0.61          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.39/0.61          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.39/0.61      inference('sup+', [status(thm)], ['12', '13'])).
% 0.39/0.61  thf('15', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 0.39/0.61      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.39/0.61  thf('16', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 0.39/0.61      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.39/0.61  thf('17', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.39/0.61           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.39/0.61      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.39/0.61  thf('18', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.61         (~ (v1_relat_1 @ X0)
% 0.39/0.61          | ((k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ X0))
% 0.39/0.61              = (k5_relat_1 @ X0 @ (k7_relat_1 @ (k6_relat_1 @ X2) @ X1))))),
% 0.39/0.61      inference('demod', [status(thm)], ['11', '17'])).
% 0.39/0.61  thf('19', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         (((k8_relat_1 @ X1 @ 
% 0.39/0.61            (k8_relat_1 @ X0 @ 
% 0.39/0.61             (k6_relat_1 @ (k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))))
% 0.39/0.61            = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.39/0.61          | ~ (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.39/0.61          | ~ (v1_relat_1 @ 
% 0.39/0.61               (k6_relat_1 @ 
% 0.39/0.61                (k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))))),
% 0.39/0.61      inference('sup+', [status(thm)], ['5', '18'])).
% 0.39/0.61  thf(t71_relat_1, axiom,
% 0.39/0.61    (![A:$i]:
% 0.39/0.61     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.39/0.61       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.39/0.61  thf('20', plain, (![X43 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X43)) = (X43))),
% 0.39/0.61      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.39/0.61  thf(t90_relat_1, axiom,
% 0.39/0.61    (![A:$i,B:$i]:
% 0.39/0.61     ( ( v1_relat_1 @ B ) =>
% 0.39/0.61       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 0.39/0.61         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.39/0.61  thf('21', plain,
% 0.39/0.61      (![X49 : $i, X50 : $i]:
% 0.39/0.61         (((k1_relat_1 @ (k7_relat_1 @ X49 @ X50))
% 0.39/0.61            = (k3_xboole_0 @ (k1_relat_1 @ X49) @ X50))
% 0.39/0.61          | ~ (v1_relat_1 @ X49))),
% 0.39/0.61      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.39/0.61  thf('22', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         (((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.39/0.61            = (k3_xboole_0 @ X0 @ X1))
% 0.39/0.61          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.39/0.61      inference('sup+', [status(thm)], ['20', '21'])).
% 0.39/0.61  thf('23', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 0.39/0.61      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.39/0.61  thf('24', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         ((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.39/0.61           = (k3_xboole_0 @ X0 @ X1))),
% 0.39/0.61      inference('demod', [status(thm)], ['22', '23'])).
% 0.39/0.61  thf('25', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.39/0.61           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.39/0.61      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.39/0.61  thf('26', plain,
% 0.39/0.61      (![X36 : $i, X37 : $i]:
% 0.39/0.61         (((k8_relat_1 @ X37 @ X36) = (k5_relat_1 @ X36 @ (k6_relat_1 @ X37)))
% 0.39/0.61          | ~ (v1_relat_1 @ X36))),
% 0.39/0.61      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.39/0.61  thf(commutativity_k2_tarski, axiom,
% 0.39/0.61    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.39/0.61  thf('27', plain,
% 0.39/0.61      (![X2 : $i, X3 : $i]: ((k2_tarski @ X3 @ X2) = (k2_tarski @ X2 @ X3))),
% 0.39/0.61      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.39/0.61  thf(t12_setfam_1, axiom,
% 0.39/0.61    (![A:$i,B:$i]:
% 0.39/0.61     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.39/0.61  thf('28', plain,
% 0.39/0.61      (![X31 : $i, X32 : $i]:
% 0.39/0.61         ((k1_setfam_1 @ (k2_tarski @ X31 @ X32)) = (k3_xboole_0 @ X31 @ X32))),
% 0.39/0.61      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.39/0.61  thf('29', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.39/0.61      inference('sup+', [status(thm)], ['27', '28'])).
% 0.39/0.61  thf('30', plain,
% 0.39/0.61      (![X31 : $i, X32 : $i]:
% 0.39/0.61         ((k1_setfam_1 @ (k2_tarski @ X31 @ X32)) = (k3_xboole_0 @ X31 @ X32))),
% 0.39/0.61      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.39/0.61  thf('31', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.39/0.61      inference('sup+', [status(thm)], ['29', '30'])).
% 0.39/0.61  thf('32', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.39/0.61      inference('sup+', [status(thm)], ['29', '30'])).
% 0.39/0.61  thf('33', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         ((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.39/0.61           = (k3_xboole_0 @ X0 @ X1))),
% 0.39/0.61      inference('demod', [status(thm)], ['22', '23'])).
% 0.39/0.61  thf('34', plain,
% 0.39/0.61      (![X51 : $i, X52 : $i]:
% 0.39/0.61         (((k7_relat_1 @ X52 @ X51) = (k5_relat_1 @ (k6_relat_1 @ X51) @ X52))
% 0.39/0.61          | ~ (v1_relat_1 @ X52))),
% 0.39/0.61      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.39/0.61  thf(t44_relat_1, axiom,
% 0.39/0.61    (![A:$i]:
% 0.39/0.61     ( ( v1_relat_1 @ A ) =>
% 0.39/0.61       ( ![B:$i]:
% 0.39/0.61         ( ( v1_relat_1 @ B ) =>
% 0.39/0.61           ( r1_tarski @
% 0.39/0.61             ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) ))).
% 0.39/0.61  thf('35', plain,
% 0.39/0.61      (![X41 : $i, X42 : $i]:
% 0.39/0.61         (~ (v1_relat_1 @ X41)
% 0.39/0.61          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X42 @ X41)) @ 
% 0.39/0.61             (k1_relat_1 @ X42))
% 0.39/0.61          | ~ (v1_relat_1 @ X42))),
% 0.39/0.61      inference('cnf', [status(esa)], [t44_relat_1])).
% 0.39/0.61  thf('36', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ 
% 0.39/0.61           (k1_relat_1 @ (k6_relat_1 @ X0)))
% 0.39/0.61          | ~ (v1_relat_1 @ X1)
% 0.39/0.61          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.39/0.61          | ~ (v1_relat_1 @ X1))),
% 0.39/0.61      inference('sup+', [status(thm)], ['34', '35'])).
% 0.39/0.61  thf('37', plain, (![X43 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X43)) = (X43))),
% 0.39/0.61      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.39/0.61  thf('38', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 0.39/0.61      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.39/0.61  thf('39', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X0)
% 0.39/0.61          | ~ (v1_relat_1 @ X1)
% 0.39/0.61          | ~ (v1_relat_1 @ X1))),
% 0.39/0.61      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.39/0.61  thf('40', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         (~ (v1_relat_1 @ X1)
% 0.39/0.61          | (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X0))),
% 0.39/0.61      inference('simplify', [status(thm)], ['39'])).
% 0.39/0.61  thf('41', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 0.39/0.61          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.39/0.61      inference('sup+', [status(thm)], ['33', '40'])).
% 0.39/0.61  thf('42', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 0.39/0.61      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.39/0.61  thf('43', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.39/0.61      inference('demod', [status(thm)], ['41', '42'])).
% 0.39/0.61  thf('44', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.39/0.61      inference('sup+', [status(thm)], ['32', '43'])).
% 0.39/0.61  thf('45', plain, (![X44 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X44)) = (X44))),
% 0.39/0.61      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.39/0.61  thf(t79_relat_1, axiom,
% 0.39/0.61    (![A:$i,B:$i]:
% 0.39/0.61     ( ( v1_relat_1 @ B ) =>
% 0.39/0.61       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.39/0.61         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 0.39/0.61  thf('46', plain,
% 0.39/0.61      (![X46 : $i, X47 : $i]:
% 0.39/0.61         (~ (r1_tarski @ (k2_relat_1 @ X46) @ X47)
% 0.39/0.61          | ((k5_relat_1 @ X46 @ (k6_relat_1 @ X47)) = (X46))
% 0.39/0.61          | ~ (v1_relat_1 @ X46))),
% 0.39/0.61      inference('cnf', [status(esa)], [t79_relat_1])).
% 0.39/0.61  thf('47', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         (~ (r1_tarski @ X0 @ X1)
% 0.39/0.61          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.39/0.61          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 0.39/0.61              = (k6_relat_1 @ X0)))),
% 0.39/0.61      inference('sup-', [status(thm)], ['45', '46'])).
% 0.39/0.61  thf('48', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 0.39/0.61      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.39/0.61  thf('49', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         (~ (r1_tarski @ X0 @ X1)
% 0.39/0.61          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 0.39/0.61              = (k6_relat_1 @ X0)))),
% 0.39/0.61      inference('demod', [status(thm)], ['47', '48'])).
% 0.39/0.61  thf('50', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         ((k5_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 0.39/0.61           (k6_relat_1 @ X0)) = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.39/0.61      inference('sup-', [status(thm)], ['44', '49'])).
% 0.39/0.61  thf('51', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         ((k5_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.39/0.61           (k6_relat_1 @ X0)) = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.39/0.61      inference('sup+', [status(thm)], ['31', '50'])).
% 0.39/0.61  thf('52', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         (((k8_relat_1 @ X0 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.39/0.61            = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))
% 0.39/0.61          | ~ (v1_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.39/0.61      inference('sup+', [status(thm)], ['26', '51'])).
% 0.39/0.61  thf('53', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.39/0.61           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.39/0.61      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.39/0.61  thf('54', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 0.39/0.61      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.39/0.61  thf('55', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         ((k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 0.39/0.61           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.39/0.61      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.39/0.61  thf('56', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.39/0.61           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.39/0.61      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.39/0.61  thf('57', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         ((k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 0.39/0.61           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.39/0.61      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.39/0.61  thf('58', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.39/0.61           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.39/0.61      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.39/0.61  thf('59', plain,
% 0.39/0.61      (![X36 : $i, X37 : $i]:
% 0.39/0.61         (((k8_relat_1 @ X37 @ X36) = (k5_relat_1 @ X36 @ (k6_relat_1 @ X37)))
% 0.39/0.61          | ~ (v1_relat_1 @ X36))),
% 0.39/0.61      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.39/0.61  thf(dt_k5_relat_1, axiom,
% 0.39/0.61    (![A:$i,B:$i]:
% 0.39/0.61     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.39/0.61       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.39/0.61  thf('60', plain,
% 0.39/0.61      (![X33 : $i, X34 : $i]:
% 0.39/0.61         (~ (v1_relat_1 @ X33)
% 0.39/0.61          | ~ (v1_relat_1 @ X34)
% 0.39/0.61          | (v1_relat_1 @ (k5_relat_1 @ X33 @ X34)))),
% 0.39/0.61      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.39/0.61  thf('61', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         ((v1_relat_1 @ (k8_relat_1 @ X1 @ X0))
% 0.39/0.61          | ~ (v1_relat_1 @ X0)
% 0.39/0.61          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.39/0.61          | ~ (v1_relat_1 @ X0))),
% 0.39/0.61      inference('sup+', [status(thm)], ['59', '60'])).
% 0.39/0.61  thf('62', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 0.39/0.61      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.39/0.61  thf('63', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         ((v1_relat_1 @ (k8_relat_1 @ X1 @ X0))
% 0.39/0.61          | ~ (v1_relat_1 @ X0)
% 0.39/0.61          | ~ (v1_relat_1 @ X0))),
% 0.39/0.61      inference('demod', [status(thm)], ['61', '62'])).
% 0.39/0.61  thf('64', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         (~ (v1_relat_1 @ X0) | (v1_relat_1 @ (k8_relat_1 @ X1 @ X0)))),
% 0.39/0.61      inference('simplify', [status(thm)], ['63'])).
% 0.39/0.61  thf('65', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         ((v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.39/0.61          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.39/0.61      inference('sup+', [status(thm)], ['58', '64'])).
% 0.39/0.61  thf('66', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 0.39/0.61      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.39/0.61  thf('67', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 0.39/0.61      inference('demod', [status(thm)], ['65', '66'])).
% 0.39/0.61  thf('68', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         ((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.39/0.61           = (k3_xboole_0 @ X0 @ X1))),
% 0.39/0.61      inference('demod', [status(thm)], ['22', '23'])).
% 0.39/0.61  thf('69', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 0.39/0.61      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.39/0.61  thf('70', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         ((k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))
% 0.39/0.61           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 0.39/0.61      inference('demod', [status(thm)],
% 0.39/0.61                ['19', '24', '25', '55', '56', '57', '67', '68', '69'])).
% 0.39/0.61  thf('71', plain,
% 0.39/0.61      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 0.39/0.61         != (k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))),
% 0.39/0.61      inference('demod', [status(thm)], ['4', '70'])).
% 0.39/0.61  thf('72', plain, ($false), inference('simplify', [status(thm)], ['71'])).
% 0.39/0.61  
% 0.39/0.61  % SZS output end Refutation
% 0.39/0.61  
% 0.39/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
