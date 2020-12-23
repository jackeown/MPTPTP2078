%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gt500u2epS

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:04 EST 2020

% Result     : Theorem 0.68s
% Output     : Refutation 0.68s
% Verified   : 
% Statistics : Number of formulae       :  156 (1008 expanded)
%              Number of leaves         :   26 ( 377 expanded)
%              Depth                    :   17
%              Number of atoms          : 1333 (8092 expanded)
%              Number of equality atoms :   88 ( 592 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(t123_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ B )
        = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k8_relat_1 @ X36 @ X35 )
        = ( k5_relat_1 @ X35 @ ( k6_relat_1 @ X36 ) ) )
      | ~ ( v1_relat_1 @ X35 ) ) ),
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
    ! [X31: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('4',plain,(
    ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ sk_B ) )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k8_relat_1 @ X36 @ X35 )
        = ( k5_relat_1 @ X35 @ ( k6_relat_1 @ X36 ) ) )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('6',plain,(
    ! [X50: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X50 ) )
      = X50 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('7',plain,(
    ! [X57: $i] :
      ( ( ( k5_relat_1 @ X57 @ ( k6_relat_1 @ ( k2_relat_1 @ X57 ) ) )
        = X57 )
      | ~ ( v1_relat_1 @ X57 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X31: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('11',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ~ ( v1_relat_1 @ X46 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X47 @ X46 ) @ X48 )
        = ( k5_relat_1 @ X47 @ ( k5_relat_1 @ X46 @ X48 ) ) )
      | ~ ( v1_relat_1 @ X48 )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X31: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('14',plain,(
    ! [X31: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['5','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(t139_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( k8_relat_1 @ A @ ( k5_relat_1 @ B @ C ) )
            = ( k5_relat_1 @ B @ ( k8_relat_1 @ A @ C ) ) ) ) ) )).

thf('18',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( v1_relat_1 @ X37 )
      | ( ( k8_relat_1 @ X39 @ ( k5_relat_1 @ X38 @ X37 ) )
        = ( k5_relat_1 @ X38 @ ( k8_relat_1 @ X39 @ X37 ) ) )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t139_relat_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X31: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('21',plain,(
    ! [X31: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,(
    ! [X31: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('24',plain,(
    ! [X31: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['16','22','23','24'])).

thf('26',plain,(
    ! [X57: $i] :
      ( ( ( k5_relat_1 @ X57 @ ( k6_relat_1 @ ( k2_relat_1 @ X57 ) ) )
        = X57 )
      | ~ ( v1_relat_1 @ X57 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('27',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ~ ( v1_relat_1 @ X46 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X47 @ X46 ) @ X48 )
        = ( k5_relat_1 @ X47 @ ( k5_relat_1 @ X46 @ X48 ) ) )
      | ~ ( v1_relat_1 @ X48 )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X1 @ X0 )
        = ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X31: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X1 @ X0 )
        = ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ ( k2_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['25','30'])).

thf('32',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k8_relat_1 @ X36 @ X35 )
        = ( k5_relat_1 @ X35 @ ( k6_relat_1 @ X36 ) ) )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('33',plain,(
    ! [X60: $i,X61: $i] :
      ( ( ( k7_relat_1 @ X61 @ X60 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X60 ) @ X61 ) )
      | ~ ( v1_relat_1 @ X61 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X31: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('36',plain,(
    ! [X31: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,(
    ! [X60: $i,X61: $i] :
      ( ( ( k7_relat_1 @ X61 @ X60 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X60 ) @ X61 ) )
      | ~ ( v1_relat_1 @ X61 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('39',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( v1_relat_1 @ X29 )
      | ~ ( v1_relat_1 @ X30 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X29 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X31: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['37','43'])).

thf('45',plain,(
    ! [X31: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X31: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('48',plain,(
    ! [X31: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['16','22','23','24'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['16','22','23','24'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('52',plain,(
    ! [X40: $i,X41: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X40 @ X41 ) )
        = ( k9_relat_1 @ X40 @ X41 ) )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X31: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['16','22','23','24'])).

thf('57',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k8_relat_1 @ X36 @ X35 )
        = ( k5_relat_1 @ X35 @ ( k6_relat_1 @ X36 ) ) )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t76_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B )
        & ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ) )).

thf('58',plain,(
    ! [X51: $i,X52: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ X52 ) @ X51 ) @ X51 )
      | ~ ( v1_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t76_relat_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X31: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('61',plain,(
    ! [X31: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ ( k6_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('63',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( v1_relat_1 @ X42 )
      | ( r1_tarski @ ( k2_relat_1 @ X43 ) @ ( k2_relat_1 @ X42 ) )
      | ~ ( r1_tarski @ X43 @ X42 )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('67',plain,(
    ! [X50: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X50 ) )
      = X50 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('68',plain,(
    ! [X31: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 ) ),
    inference(demod,[status(thm)],['64','65','66','67','68'])).

thf('70',plain,(
    ! [X49: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X49 ) )
      = X49 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t77_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B )
          = B ) ) ) )).

thf('71',plain,(
    ! [X53: $i,X54: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X53 ) @ X54 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X54 ) @ X53 )
        = X53 )
      | ~ ( v1_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t77_relat_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X31: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['16','22','23','24'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['69','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['16','22','23','24'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k8_relat_1 @ ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['31','46','47','48','49','50','55','56','77','78'])).

thf('80',plain,(
    ! [X60: $i,X61: $i] :
      ( ( ( k7_relat_1 @ X61 @ X60 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X60 ) @ X61 ) )
      | ~ ( v1_relat_1 @ X61 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('81',plain,(
    ! [X51: $i,X52: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X51 @ ( k6_relat_1 @ X52 ) ) @ X51 )
      | ~ ( v1_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t76_relat_1])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X31: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('84',plain,(
    ! [X31: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( v1_relat_1 @ X42 )
      | ( r1_tarski @ ( k2_relat_1 @ X43 ) @ ( k2_relat_1 @ X42 ) )
      | ~ ( r1_tarski @ X43 @ X42 )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('92',plain,(
    ! [X50: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X50 ) )
      = X50 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('93',plain,(
    ! [X31: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['89','90','91','92','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('98',plain,(
    ! [X58: $i,X59: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X58 @ X59 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X58 ) @ X59 ) )
      | ~ ( v1_relat_1 @ X58 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ ( k6_relat_1 @ X1 ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X49: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X49 ) )
      = X49 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('101',plain,(
    ! [X31: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['99','100','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) )
      = ( k3_xboole_0 @ ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['96','102'])).

thf('104',plain,(
    ! [X49: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X49 ) )
      = X49 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k8_relat_1 @ ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['31','46','47','48','49','50','55','56','77','78'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['99','100','101'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k3_xboole_0 @ ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['99','100','101'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['103','104','109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k8_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['79','110'])).

thf('112',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k8_relat_1 @ X36 @ X35 )
        = ( k5_relat_1 @ X35 @ ( k6_relat_1 @ X36 ) ) )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('114',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( v1_relat_1 @ X42 )
      | ( r1_tarski @ ( k1_relat_1 @ X43 ) @ ( k1_relat_1 @ X42 ) )
      | ~ ( r1_tarski @ X43 @ X42 )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['99','100','101'])).

thf('118',plain,(
    ! [X49: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X49 ) )
      = X49 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('119',plain,(
    ! [X31: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['115','116','117','118','119'])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['112','122'])).

thf('124',plain,(
    ! [X31: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['111','125'])).

thf('127',plain,(
    ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','126'])).

thf('128',plain,(
    $false ),
    inference(simplify,[status(thm)],['127'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gt500u2epS
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:09:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.68/0.92  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.68/0.92  % Solved by: fo/fo7.sh
% 0.68/0.92  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.68/0.92  % done 585 iterations in 0.440s
% 0.68/0.92  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.68/0.92  % SZS output start Refutation
% 0.68/0.92  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.68/0.92  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.68/0.92  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.68/0.92  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.68/0.92  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.68/0.92  thf(sk_A_type, type, sk_A: $i).
% 0.68/0.92  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.68/0.92  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.68/0.92  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.68/0.92  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.68/0.92  thf(sk_B_type, type, sk_B: $i).
% 0.68/0.92  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.68/0.92  thf(t123_relat_1, axiom,
% 0.68/0.92    (![A:$i,B:$i]:
% 0.68/0.92     ( ( v1_relat_1 @ B ) =>
% 0.68/0.92       ( ( k8_relat_1 @ A @ B ) = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ))).
% 0.68/0.92  thf('0', plain,
% 0.68/0.92      (![X35 : $i, X36 : $i]:
% 0.68/0.92         (((k8_relat_1 @ X36 @ X35) = (k5_relat_1 @ X35 @ (k6_relat_1 @ X36)))
% 0.68/0.92          | ~ (v1_relat_1 @ X35))),
% 0.68/0.92      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.68/0.92  thf(t43_funct_1, conjecture,
% 0.68/0.92    (![A:$i,B:$i]:
% 0.68/0.92     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.68/0.92       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.68/0.92  thf(zf_stmt_0, negated_conjecture,
% 0.68/0.92    (~( ![A:$i,B:$i]:
% 0.68/0.92        ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.68/0.92          ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 0.68/0.92    inference('cnf.neg', [status(esa)], [t43_funct_1])).
% 0.68/0.92  thf('1', plain,
% 0.68/0.92      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A))
% 0.68/0.92         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.68/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.92  thf('2', plain,
% 0.68/0.92      ((((k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B))
% 0.68/0.92          != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))
% 0.68/0.92        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_B)))),
% 0.68/0.92      inference('sup-', [status(thm)], ['0', '1'])).
% 0.68/0.92  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.68/0.92  thf('3', plain, (![X31 : $i]: (v1_relat_1 @ (k6_relat_1 @ X31))),
% 0.68/0.92      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.68/0.92  thf('4', plain,
% 0.68/0.92      (((k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B))
% 0.68/0.92         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.68/0.92      inference('demod', [status(thm)], ['2', '3'])).
% 0.68/0.92  thf('5', plain,
% 0.68/0.92      (![X35 : $i, X36 : $i]:
% 0.68/0.92         (((k8_relat_1 @ X36 @ X35) = (k5_relat_1 @ X35 @ (k6_relat_1 @ X36)))
% 0.68/0.92          | ~ (v1_relat_1 @ X35))),
% 0.68/0.92      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.68/0.92  thf(t71_relat_1, axiom,
% 0.68/0.92    (![A:$i]:
% 0.68/0.92     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.68/0.92       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.68/0.92  thf('6', plain, (![X50 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X50)) = (X50))),
% 0.68/0.92      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.68/0.92  thf(t80_relat_1, axiom,
% 0.68/0.92    (![A:$i]:
% 0.68/0.92     ( ( v1_relat_1 @ A ) =>
% 0.68/0.92       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 0.68/0.92  thf('7', plain,
% 0.68/0.92      (![X57 : $i]:
% 0.68/0.92         (((k5_relat_1 @ X57 @ (k6_relat_1 @ (k2_relat_1 @ X57))) = (X57))
% 0.68/0.92          | ~ (v1_relat_1 @ X57))),
% 0.68/0.92      inference('cnf', [status(esa)], [t80_relat_1])).
% 0.68/0.92  thf('8', plain,
% 0.68/0.92      (![X0 : $i]:
% 0.68/0.92         (((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 0.68/0.92            = (k6_relat_1 @ X0))
% 0.68/0.92          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.68/0.92      inference('sup+', [status(thm)], ['6', '7'])).
% 0.68/0.92  thf('9', plain, (![X31 : $i]: (v1_relat_1 @ (k6_relat_1 @ X31))),
% 0.68/0.92      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.68/0.92  thf('10', plain,
% 0.68/0.92      (![X0 : $i]:
% 0.68/0.92         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 0.68/0.92           = (k6_relat_1 @ X0))),
% 0.68/0.92      inference('demod', [status(thm)], ['8', '9'])).
% 0.68/0.92  thf(t55_relat_1, axiom,
% 0.68/0.92    (![A:$i]:
% 0.68/0.92     ( ( v1_relat_1 @ A ) =>
% 0.68/0.92       ( ![B:$i]:
% 0.68/0.92         ( ( v1_relat_1 @ B ) =>
% 0.68/0.92           ( ![C:$i]:
% 0.68/0.92             ( ( v1_relat_1 @ C ) =>
% 0.68/0.92               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 0.68/0.92                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 0.68/0.92  thf('11', plain,
% 0.68/0.92      (![X46 : $i, X47 : $i, X48 : $i]:
% 0.68/0.92         (~ (v1_relat_1 @ X46)
% 0.68/0.92          | ((k5_relat_1 @ (k5_relat_1 @ X47 @ X46) @ X48)
% 0.68/0.92              = (k5_relat_1 @ X47 @ (k5_relat_1 @ X46 @ X48)))
% 0.68/0.92          | ~ (v1_relat_1 @ X48)
% 0.68/0.92          | ~ (v1_relat_1 @ X47))),
% 0.68/0.92      inference('cnf', [status(esa)], [t55_relat_1])).
% 0.68/0.92  thf('12', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         (((k5_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.68/0.92            = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.68/0.92               (k5_relat_1 @ (k6_relat_1 @ X0) @ X1)))
% 0.68/0.92          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.68/0.92          | ~ (v1_relat_1 @ X1)
% 0.68/0.92          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.68/0.92      inference('sup+', [status(thm)], ['10', '11'])).
% 0.68/0.92  thf('13', plain, (![X31 : $i]: (v1_relat_1 @ (k6_relat_1 @ X31))),
% 0.68/0.92      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.68/0.92  thf('14', plain, (![X31 : $i]: (v1_relat_1 @ (k6_relat_1 @ X31))),
% 0.68/0.92      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.68/0.92  thf('15', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         (((k5_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.68/0.92            = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.68/0.92               (k5_relat_1 @ (k6_relat_1 @ X0) @ X1)))
% 0.68/0.92          | ~ (v1_relat_1 @ X1))),
% 0.68/0.92      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.68/0.92  thf('16', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         (((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 0.68/0.92            = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.68/0.92               (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))
% 0.68/0.92          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.68/0.92          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.68/0.92      inference('sup+', [status(thm)], ['5', '15'])).
% 0.68/0.92  thf('17', plain,
% 0.68/0.92      (![X0 : $i]:
% 0.68/0.92         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 0.68/0.92           = (k6_relat_1 @ X0))),
% 0.68/0.92      inference('demod', [status(thm)], ['8', '9'])).
% 0.68/0.92  thf(t139_relat_1, axiom,
% 0.68/0.92    (![A:$i,B:$i]:
% 0.68/0.92     ( ( v1_relat_1 @ B ) =>
% 0.68/0.92       ( ![C:$i]:
% 0.68/0.92         ( ( v1_relat_1 @ C ) =>
% 0.68/0.92           ( ( k8_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) =
% 0.68/0.92             ( k5_relat_1 @ B @ ( k8_relat_1 @ A @ C ) ) ) ) ) ))).
% 0.68/0.92  thf('18', plain,
% 0.68/0.92      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.68/0.92         (~ (v1_relat_1 @ X37)
% 0.68/0.92          | ((k8_relat_1 @ X39 @ (k5_relat_1 @ X38 @ X37))
% 0.68/0.92              = (k5_relat_1 @ X38 @ (k8_relat_1 @ X39 @ X37)))
% 0.68/0.92          | ~ (v1_relat_1 @ X38))),
% 0.68/0.92      inference('cnf', [status(esa)], [t139_relat_1])).
% 0.68/0.92  thf('19', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         (((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 0.68/0.92            = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.68/0.92               (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))
% 0.68/0.92          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.68/0.92          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.68/0.92      inference('sup+', [status(thm)], ['17', '18'])).
% 0.68/0.92  thf('20', plain, (![X31 : $i]: (v1_relat_1 @ (k6_relat_1 @ X31))),
% 0.68/0.92      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.68/0.92  thf('21', plain, (![X31 : $i]: (v1_relat_1 @ (k6_relat_1 @ X31))),
% 0.68/0.92      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.68/0.92  thf('22', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 0.68/0.92           = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.68/0.92              (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 0.68/0.92      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.68/0.92  thf('23', plain, (![X31 : $i]: (v1_relat_1 @ (k6_relat_1 @ X31))),
% 0.68/0.92      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.68/0.92  thf('24', plain, (![X31 : $i]: (v1_relat_1 @ (k6_relat_1 @ X31))),
% 0.68/0.92      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.68/0.92  thf('25', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 0.68/0.92           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.68/0.92      inference('demod', [status(thm)], ['16', '22', '23', '24'])).
% 0.68/0.92  thf('26', plain,
% 0.68/0.92      (![X57 : $i]:
% 0.68/0.92         (((k5_relat_1 @ X57 @ (k6_relat_1 @ (k2_relat_1 @ X57))) = (X57))
% 0.68/0.92          | ~ (v1_relat_1 @ X57))),
% 0.68/0.92      inference('cnf', [status(esa)], [t80_relat_1])).
% 0.68/0.92  thf('27', plain,
% 0.68/0.92      (![X46 : $i, X47 : $i, X48 : $i]:
% 0.68/0.92         (~ (v1_relat_1 @ X46)
% 0.68/0.92          | ((k5_relat_1 @ (k5_relat_1 @ X47 @ X46) @ X48)
% 0.68/0.92              = (k5_relat_1 @ X47 @ (k5_relat_1 @ X46 @ X48)))
% 0.68/0.92          | ~ (v1_relat_1 @ X48)
% 0.68/0.92          | ~ (v1_relat_1 @ X47))),
% 0.68/0.92      inference('cnf', [status(esa)], [t55_relat_1])).
% 0.68/0.92  thf('28', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         (((k5_relat_1 @ X1 @ X0)
% 0.68/0.92            = (k5_relat_1 @ X1 @ 
% 0.68/0.92               (k5_relat_1 @ X0 @ 
% 0.68/0.92                (k6_relat_1 @ (k2_relat_1 @ (k5_relat_1 @ X1 @ X0))))))
% 0.68/0.92          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 0.68/0.92          | ~ (v1_relat_1 @ X1)
% 0.68/0.92          | ~ (v1_relat_1 @ 
% 0.68/0.92               (k6_relat_1 @ (k2_relat_1 @ (k5_relat_1 @ X1 @ X0))))
% 0.68/0.92          | ~ (v1_relat_1 @ X0))),
% 0.68/0.92      inference('sup+', [status(thm)], ['26', '27'])).
% 0.68/0.92  thf('29', plain, (![X31 : $i]: (v1_relat_1 @ (k6_relat_1 @ X31))),
% 0.68/0.92      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.68/0.92  thf('30', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         (((k5_relat_1 @ X1 @ X0)
% 0.68/0.92            = (k5_relat_1 @ X1 @ 
% 0.68/0.92               (k5_relat_1 @ X0 @ 
% 0.68/0.92                (k6_relat_1 @ (k2_relat_1 @ (k5_relat_1 @ X1 @ X0))))))
% 0.68/0.92          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 0.68/0.92          | ~ (v1_relat_1 @ X1)
% 0.68/0.92          | ~ (v1_relat_1 @ X0))),
% 0.68/0.92      inference('demod', [status(thm)], ['28', '29'])).
% 0.68/0.92  thf('31', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         (~ (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.68/0.92          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.68/0.92          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.68/0.92          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 0.68/0.92              = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.68/0.92                 (k5_relat_1 @ (k6_relat_1 @ X1) @ 
% 0.68/0.92                  (k6_relat_1 @ 
% 0.68/0.92                   (k2_relat_1 @ 
% 0.68/0.92                    (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))))))))),
% 0.68/0.92      inference('sup-', [status(thm)], ['25', '30'])).
% 0.68/0.92  thf('32', plain,
% 0.68/0.92      (![X35 : $i, X36 : $i]:
% 0.68/0.92         (((k8_relat_1 @ X36 @ X35) = (k5_relat_1 @ X35 @ (k6_relat_1 @ X36)))
% 0.68/0.92          | ~ (v1_relat_1 @ X35))),
% 0.68/0.92      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.68/0.92  thf(t94_relat_1, axiom,
% 0.68/0.92    (![A:$i,B:$i]:
% 0.68/0.92     ( ( v1_relat_1 @ B ) =>
% 0.68/0.92       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.68/0.92  thf('33', plain,
% 0.68/0.92      (![X60 : $i, X61 : $i]:
% 0.68/0.92         (((k7_relat_1 @ X61 @ X60) = (k5_relat_1 @ (k6_relat_1 @ X60) @ X61))
% 0.68/0.92          | ~ (v1_relat_1 @ X61))),
% 0.68/0.92      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.68/0.92  thf('34', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         (((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.68/0.92            = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.68/0.92          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.68/0.92          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.68/0.92      inference('sup+', [status(thm)], ['32', '33'])).
% 0.68/0.92  thf('35', plain, (![X31 : $i]: (v1_relat_1 @ (k6_relat_1 @ X31))),
% 0.68/0.92      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.68/0.92  thf('36', plain, (![X31 : $i]: (v1_relat_1 @ (k6_relat_1 @ X31))),
% 0.68/0.92      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.68/0.92  thf('37', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.68/0.92           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.68/0.92      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.68/0.92  thf('38', plain,
% 0.68/0.92      (![X60 : $i, X61 : $i]:
% 0.68/0.92         (((k7_relat_1 @ X61 @ X60) = (k5_relat_1 @ (k6_relat_1 @ X60) @ X61))
% 0.68/0.92          | ~ (v1_relat_1 @ X61))),
% 0.68/0.92      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.68/0.92  thf(dt_k5_relat_1, axiom,
% 0.68/0.92    (![A:$i,B:$i]:
% 0.68/0.92     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.68/0.92       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.68/0.92  thf('39', plain,
% 0.68/0.92      (![X29 : $i, X30 : $i]:
% 0.68/0.92         (~ (v1_relat_1 @ X29)
% 0.68/0.92          | ~ (v1_relat_1 @ X30)
% 0.68/0.92          | (v1_relat_1 @ (k5_relat_1 @ X29 @ X30)))),
% 0.68/0.92      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.68/0.92  thf('40', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         ((v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.68/0.92          | ~ (v1_relat_1 @ X1)
% 0.68/0.92          | ~ (v1_relat_1 @ X1)
% 0.68/0.92          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.68/0.92      inference('sup+', [status(thm)], ['38', '39'])).
% 0.68/0.92  thf('41', plain, (![X31 : $i]: (v1_relat_1 @ (k6_relat_1 @ X31))),
% 0.68/0.92      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.68/0.92  thf('42', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         ((v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.68/0.92          | ~ (v1_relat_1 @ X1)
% 0.68/0.92          | ~ (v1_relat_1 @ X1))),
% 0.68/0.92      inference('demod', [status(thm)], ['40', '41'])).
% 0.68/0.92  thf('43', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         (~ (v1_relat_1 @ X1) | (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.68/0.92      inference('simplify', [status(thm)], ['42'])).
% 0.68/0.92  thf('44', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         ((v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.68/0.92          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.68/0.92      inference('sup+', [status(thm)], ['37', '43'])).
% 0.68/0.92  thf('45', plain, (![X31 : $i]: (v1_relat_1 @ (k6_relat_1 @ X31))),
% 0.68/0.92      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.68/0.92  thf('46', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.68/0.92      inference('demod', [status(thm)], ['44', '45'])).
% 0.68/0.92  thf('47', plain, (![X31 : $i]: (v1_relat_1 @ (k6_relat_1 @ X31))),
% 0.68/0.92      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.68/0.92  thf('48', plain, (![X31 : $i]: (v1_relat_1 @ (k6_relat_1 @ X31))),
% 0.68/0.92      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.68/0.92  thf('49', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 0.68/0.92           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.68/0.92      inference('demod', [status(thm)], ['16', '22', '23', '24'])).
% 0.68/0.92  thf('50', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 0.68/0.92           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.68/0.92      inference('demod', [status(thm)], ['16', '22', '23', '24'])).
% 0.68/0.92  thf('51', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.68/0.92           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.68/0.92      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.68/0.92  thf(t148_relat_1, axiom,
% 0.68/0.92    (![A:$i,B:$i]:
% 0.68/0.92     ( ( v1_relat_1 @ B ) =>
% 0.68/0.92       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.68/0.92  thf('52', plain,
% 0.68/0.92      (![X40 : $i, X41 : $i]:
% 0.68/0.92         (((k2_relat_1 @ (k7_relat_1 @ X40 @ X41)) = (k9_relat_1 @ X40 @ X41))
% 0.68/0.92          | ~ (v1_relat_1 @ X40))),
% 0.68/0.92      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.68/0.92  thf('53', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         (((k2_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.68/0.92            = (k9_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.68/0.92          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.68/0.92      inference('sup+', [status(thm)], ['51', '52'])).
% 0.68/0.92  thf('54', plain, (![X31 : $i]: (v1_relat_1 @ (k6_relat_1 @ X31))),
% 0.68/0.92      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.68/0.92  thf('55', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         ((k2_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.68/0.92           = (k9_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 0.68/0.92      inference('demod', [status(thm)], ['53', '54'])).
% 0.68/0.92  thf('56', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 0.68/0.92           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.68/0.92      inference('demod', [status(thm)], ['16', '22', '23', '24'])).
% 0.68/0.92  thf('57', plain,
% 0.68/0.92      (![X35 : $i, X36 : $i]:
% 0.68/0.92         (((k8_relat_1 @ X36 @ X35) = (k5_relat_1 @ X35 @ (k6_relat_1 @ X36)))
% 0.68/0.92          | ~ (v1_relat_1 @ X35))),
% 0.68/0.92      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.68/0.92  thf(t76_relat_1, axiom,
% 0.68/0.92    (![A:$i,B:$i]:
% 0.68/0.92     ( ( v1_relat_1 @ B ) =>
% 0.68/0.92       ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B ) & 
% 0.68/0.92         ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ))).
% 0.68/0.92  thf('58', plain,
% 0.68/0.92      (![X51 : $i, X52 : $i]:
% 0.68/0.92         ((r1_tarski @ (k5_relat_1 @ (k6_relat_1 @ X52) @ X51) @ X51)
% 0.68/0.92          | ~ (v1_relat_1 @ X51))),
% 0.68/0.92      inference('cnf', [status(esa)], [t76_relat_1])).
% 0.68/0.92  thf('59', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         ((r1_tarski @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ 
% 0.68/0.92           (k6_relat_1 @ X1))
% 0.68/0.92          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.68/0.92          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.68/0.92      inference('sup+', [status(thm)], ['57', '58'])).
% 0.68/0.92  thf('60', plain, (![X31 : $i]: (v1_relat_1 @ (k6_relat_1 @ X31))),
% 0.68/0.92      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.68/0.92  thf('61', plain, (![X31 : $i]: (v1_relat_1 @ (k6_relat_1 @ X31))),
% 0.68/0.92      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.68/0.92  thf('62', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         (r1_tarski @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ (k6_relat_1 @ X1))),
% 0.68/0.92      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.68/0.92  thf(t25_relat_1, axiom,
% 0.68/0.92    (![A:$i]:
% 0.68/0.92     ( ( v1_relat_1 @ A ) =>
% 0.68/0.92       ( ![B:$i]:
% 0.68/0.92         ( ( v1_relat_1 @ B ) =>
% 0.68/0.92           ( ( r1_tarski @ A @ B ) =>
% 0.68/0.92             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 0.68/0.92               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 0.68/0.92  thf('63', plain,
% 0.68/0.92      (![X42 : $i, X43 : $i]:
% 0.68/0.92         (~ (v1_relat_1 @ X42)
% 0.68/0.92          | (r1_tarski @ (k2_relat_1 @ X43) @ (k2_relat_1 @ X42))
% 0.68/0.92          | ~ (r1_tarski @ X43 @ X42)
% 0.68/0.92          | ~ (v1_relat_1 @ X43))),
% 0.68/0.92      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.68/0.92  thf('64', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         (~ (v1_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 0.68/0.92          | (r1_tarski @ 
% 0.68/0.92             (k2_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1))) @ 
% 0.68/0.92             (k2_relat_1 @ (k6_relat_1 @ X0)))
% 0.68/0.92          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.68/0.92      inference('sup-', [status(thm)], ['62', '63'])).
% 0.68/0.92  thf('65', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.68/0.92      inference('demod', [status(thm)], ['44', '45'])).
% 0.68/0.92  thf('66', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         ((k2_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.68/0.92           = (k9_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 0.68/0.92      inference('demod', [status(thm)], ['53', '54'])).
% 0.68/0.92  thf('67', plain, (![X50 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X50)) = (X50))),
% 0.68/0.92      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.68/0.92  thf('68', plain, (![X31 : $i]: (v1_relat_1 @ (k6_relat_1 @ X31))),
% 0.68/0.92      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.68/0.92  thf('69', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         (r1_tarski @ (k9_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X0)),
% 0.68/0.92      inference('demod', [status(thm)], ['64', '65', '66', '67', '68'])).
% 0.68/0.92  thf('70', plain, (![X49 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X49)) = (X49))),
% 0.68/0.92      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.68/0.92  thf(t77_relat_1, axiom,
% 0.68/0.92    (![A:$i,B:$i]:
% 0.68/0.92     ( ( v1_relat_1 @ B ) =>
% 0.68/0.92       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.68/0.92         ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ) ))).
% 0.68/0.92  thf('71', plain,
% 0.68/0.92      (![X53 : $i, X54 : $i]:
% 0.68/0.92         (~ (r1_tarski @ (k1_relat_1 @ X53) @ X54)
% 0.68/0.92          | ((k5_relat_1 @ (k6_relat_1 @ X54) @ X53) = (X53))
% 0.68/0.92          | ~ (v1_relat_1 @ X53))),
% 0.68/0.92      inference('cnf', [status(esa)], [t77_relat_1])).
% 0.68/0.92  thf('72', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         (~ (r1_tarski @ X0 @ X1)
% 0.68/0.92          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.68/0.92          | ((k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 0.68/0.92              = (k6_relat_1 @ X0)))),
% 0.68/0.92      inference('sup-', [status(thm)], ['70', '71'])).
% 0.68/0.92  thf('73', plain, (![X31 : $i]: (v1_relat_1 @ (k6_relat_1 @ X31))),
% 0.68/0.92      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.68/0.92  thf('74', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         (~ (r1_tarski @ X0 @ X1)
% 0.68/0.92          | ((k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 0.68/0.92              = (k6_relat_1 @ X0)))),
% 0.68/0.92      inference('demod', [status(thm)], ['72', '73'])).
% 0.68/0.92  thf('75', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 0.68/0.92           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.68/0.92      inference('demod', [status(thm)], ['16', '22', '23', '24'])).
% 0.68/0.92  thf('76', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         (~ (r1_tarski @ X0 @ X1)
% 0.68/0.92          | ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1)) = (k6_relat_1 @ X0)))),
% 0.68/0.92      inference('demod', [status(thm)], ['74', '75'])).
% 0.68/0.92  thf('77', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         ((k8_relat_1 @ (k9_relat_1 @ (k6_relat_1 @ X0) @ X1) @ 
% 0.68/0.92           (k6_relat_1 @ X0))
% 0.68/0.92           = (k6_relat_1 @ (k9_relat_1 @ (k6_relat_1 @ X0) @ X1)))),
% 0.68/0.92      inference('sup-', [status(thm)], ['69', '76'])).
% 0.68/0.92  thf('78', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 0.68/0.92           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.68/0.92      inference('demod', [status(thm)], ['16', '22', '23', '24'])).
% 0.68/0.92  thf('79', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 0.68/0.92           = (k8_relat_1 @ (k9_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 0.68/0.92              (k6_relat_1 @ X0)))),
% 0.68/0.92      inference('demod', [status(thm)],
% 0.68/0.92                ['31', '46', '47', '48', '49', '50', '55', '56', '77', '78'])).
% 0.68/0.92  thf('80', plain,
% 0.68/0.92      (![X60 : $i, X61 : $i]:
% 0.68/0.92         (((k7_relat_1 @ X61 @ X60) = (k5_relat_1 @ (k6_relat_1 @ X60) @ X61))
% 0.68/0.92          | ~ (v1_relat_1 @ X61))),
% 0.68/0.92      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.68/0.92  thf('81', plain,
% 0.68/0.92      (![X51 : $i, X52 : $i]:
% 0.68/0.92         ((r1_tarski @ (k5_relat_1 @ X51 @ (k6_relat_1 @ X52)) @ X51)
% 0.68/0.92          | ~ (v1_relat_1 @ X51))),
% 0.68/0.92      inference('cnf', [status(esa)], [t76_relat_1])).
% 0.68/0.92  thf('82', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         ((r1_tarski @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 0.68/0.92           (k6_relat_1 @ X0))
% 0.68/0.92          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.68/0.92          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.68/0.92      inference('sup+', [status(thm)], ['80', '81'])).
% 0.68/0.92  thf('83', plain, (![X31 : $i]: (v1_relat_1 @ (k6_relat_1 @ X31))),
% 0.68/0.92      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.68/0.92  thf('84', plain, (![X31 : $i]: (v1_relat_1 @ (k6_relat_1 @ X31))),
% 0.68/0.92      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.68/0.92  thf('85', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         (r1_tarski @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ (k6_relat_1 @ X0))),
% 0.68/0.92      inference('demod', [status(thm)], ['82', '83', '84'])).
% 0.68/0.92  thf('86', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.68/0.92           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.68/0.92      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.68/0.92  thf('87', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         (r1_tarski @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ (k6_relat_1 @ X0))),
% 0.68/0.92      inference('demod', [status(thm)], ['85', '86'])).
% 0.68/0.92  thf('88', plain,
% 0.68/0.92      (![X42 : $i, X43 : $i]:
% 0.68/0.92         (~ (v1_relat_1 @ X42)
% 0.68/0.92          | (r1_tarski @ (k2_relat_1 @ X43) @ (k2_relat_1 @ X42))
% 0.68/0.92          | ~ (r1_tarski @ X43 @ X42)
% 0.68/0.92          | ~ (v1_relat_1 @ X43))),
% 0.68/0.92      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.68/0.92  thf('89', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         (~ (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.68/0.92          | (r1_tarski @ 
% 0.68/0.92             (k2_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ 
% 0.68/0.92             (k2_relat_1 @ (k6_relat_1 @ X0)))
% 0.68/0.92          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.68/0.92      inference('sup-', [status(thm)], ['87', '88'])).
% 0.68/0.92  thf('90', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.68/0.92      inference('demod', [status(thm)], ['44', '45'])).
% 0.68/0.92  thf('91', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         ((k2_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.68/0.92           = (k9_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 0.68/0.92      inference('demod', [status(thm)], ['53', '54'])).
% 0.68/0.92  thf('92', plain, (![X50 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X50)) = (X50))),
% 0.68/0.92      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.68/0.92  thf('93', plain, (![X31 : $i]: (v1_relat_1 @ (k6_relat_1 @ X31))),
% 0.68/0.92      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.68/0.92  thf('94', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         (r1_tarski @ (k9_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X0)),
% 0.68/0.92      inference('demod', [status(thm)], ['89', '90', '91', '92', '93'])).
% 0.68/0.92  thf('95', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         (~ (r1_tarski @ X0 @ X1)
% 0.68/0.92          | ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1)) = (k6_relat_1 @ X0)))),
% 0.68/0.92      inference('demod', [status(thm)], ['74', '75'])).
% 0.68/0.92  thf('96', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         ((k8_relat_1 @ (k9_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 0.68/0.92           (k6_relat_1 @ X0))
% 0.68/0.92           = (k6_relat_1 @ (k9_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 0.68/0.92      inference('sup-', [status(thm)], ['94', '95'])).
% 0.68/0.92  thf('97', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.68/0.92           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.68/0.92      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.68/0.92  thf(t90_relat_1, axiom,
% 0.68/0.92    (![A:$i,B:$i]:
% 0.68/0.92     ( ( v1_relat_1 @ B ) =>
% 0.68/0.92       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 0.68/0.92         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.68/0.92  thf('98', plain,
% 0.68/0.92      (![X58 : $i, X59 : $i]:
% 0.68/0.92         (((k1_relat_1 @ (k7_relat_1 @ X58 @ X59))
% 0.68/0.92            = (k3_xboole_0 @ (k1_relat_1 @ X58) @ X59))
% 0.68/0.92          | ~ (v1_relat_1 @ X58))),
% 0.68/0.92      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.68/0.92  thf('99', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         (((k1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.68/0.92            = (k3_xboole_0 @ (k1_relat_1 @ (k6_relat_1 @ X1)) @ X0))
% 0.68/0.92          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.68/0.92      inference('sup+', [status(thm)], ['97', '98'])).
% 0.68/0.92  thf('100', plain, (![X49 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X49)) = (X49))),
% 0.68/0.92      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.68/0.92  thf('101', plain, (![X31 : $i]: (v1_relat_1 @ (k6_relat_1 @ X31))),
% 0.68/0.92      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.68/0.92  thf('102', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         ((k1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.68/0.92           = (k3_xboole_0 @ X1 @ X0))),
% 0.68/0.92      inference('demod', [status(thm)], ['99', '100', '101'])).
% 0.68/0.92  thf('103', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         ((k1_relat_1 @ (k6_relat_1 @ (k9_relat_1 @ (k6_relat_1 @ X1) @ X0)))
% 0.68/0.92           = (k3_xboole_0 @ (k9_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X0))),
% 0.68/0.92      inference('sup+', [status(thm)], ['96', '102'])).
% 0.68/0.92  thf('104', plain, (![X49 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X49)) = (X49))),
% 0.68/0.92      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.68/0.92  thf('105', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 0.68/0.92           = (k8_relat_1 @ (k9_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 0.68/0.92              (k6_relat_1 @ X0)))),
% 0.68/0.92      inference('demod', [status(thm)],
% 0.68/0.92                ['31', '46', '47', '48', '49', '50', '55', '56', '77', '78'])).
% 0.68/0.92  thf('106', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         ((k1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.68/0.92           = (k3_xboole_0 @ X1 @ X0))),
% 0.68/0.92      inference('demod', [status(thm)], ['99', '100', '101'])).
% 0.68/0.92  thf('107', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         ((k1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.68/0.92           = (k3_xboole_0 @ (k9_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X0))),
% 0.68/0.92      inference('sup+', [status(thm)], ['105', '106'])).
% 0.68/0.92  thf('108', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         ((k1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.68/0.92           = (k3_xboole_0 @ X1 @ X0))),
% 0.68/0.92      inference('demod', [status(thm)], ['99', '100', '101'])).
% 0.68/0.92  thf('109', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         ((k3_xboole_0 @ X1 @ X0)
% 0.68/0.92           = (k3_xboole_0 @ (k9_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X0))),
% 0.68/0.92      inference('demod', [status(thm)], ['107', '108'])).
% 0.68/0.92  thf('110', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         ((k9_relat_1 @ (k6_relat_1 @ X1) @ X0) = (k3_xboole_0 @ X1 @ X0))),
% 0.68/0.92      inference('demod', [status(thm)], ['103', '104', '109'])).
% 0.68/0.92  thf('111', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 0.68/0.92           = (k8_relat_1 @ (k3_xboole_0 @ X1 @ X0) @ (k6_relat_1 @ X0)))),
% 0.68/0.92      inference('demod', [status(thm)], ['79', '110'])).
% 0.68/0.92  thf('112', plain,
% 0.68/0.92      (![X35 : $i, X36 : $i]:
% 0.68/0.92         (((k8_relat_1 @ X36 @ X35) = (k5_relat_1 @ X35 @ (k6_relat_1 @ X36)))
% 0.68/0.92          | ~ (v1_relat_1 @ X35))),
% 0.68/0.92      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.68/0.92  thf('113', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         (r1_tarski @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ (k6_relat_1 @ X0))),
% 0.68/0.92      inference('demod', [status(thm)], ['85', '86'])).
% 0.68/0.92  thf('114', plain,
% 0.68/0.92      (![X42 : $i, X43 : $i]:
% 0.68/0.92         (~ (v1_relat_1 @ X42)
% 0.68/0.92          | (r1_tarski @ (k1_relat_1 @ X43) @ (k1_relat_1 @ X42))
% 0.68/0.92          | ~ (r1_tarski @ X43 @ X42)
% 0.68/0.92          | ~ (v1_relat_1 @ X43))),
% 0.68/0.92      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.68/0.92  thf('115', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         (~ (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.68/0.92          | (r1_tarski @ 
% 0.68/0.92             (k1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ 
% 0.68/0.92             (k1_relat_1 @ (k6_relat_1 @ X0)))
% 0.68/0.92          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.68/0.92      inference('sup-', [status(thm)], ['113', '114'])).
% 0.68/0.92  thf('116', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.68/0.92      inference('demod', [status(thm)], ['44', '45'])).
% 0.68/0.92  thf('117', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         ((k1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.68/0.92           = (k3_xboole_0 @ X1 @ X0))),
% 0.68/0.92      inference('demod', [status(thm)], ['99', '100', '101'])).
% 0.68/0.92  thf('118', plain, (![X49 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X49)) = (X49))),
% 0.68/0.92      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.68/0.92  thf('119', plain, (![X31 : $i]: (v1_relat_1 @ (k6_relat_1 @ X31))),
% 0.68/0.92      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.68/0.92  thf('120', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.68/0.92      inference('demod', [status(thm)], ['115', '116', '117', '118', '119'])).
% 0.68/0.92  thf('121', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         (~ (r1_tarski @ X0 @ X1)
% 0.68/0.92          | ((k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 0.68/0.92              = (k6_relat_1 @ X0)))),
% 0.68/0.92      inference('demod', [status(thm)], ['72', '73'])).
% 0.68/0.92  thf('122', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         ((k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.68/0.92           (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.68/0.92           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.68/0.92      inference('sup-', [status(thm)], ['120', '121'])).
% 0.68/0.92  thf('123', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         (((k8_relat_1 @ (k3_xboole_0 @ X1 @ X0) @ (k6_relat_1 @ X0))
% 0.68/0.92            = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.68/0.92          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.68/0.92      inference('sup+', [status(thm)], ['112', '122'])).
% 0.68/0.92  thf('124', plain, (![X31 : $i]: (v1_relat_1 @ (k6_relat_1 @ X31))),
% 0.68/0.92      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.68/0.92  thf('125', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         ((k8_relat_1 @ (k3_xboole_0 @ X1 @ X0) @ (k6_relat_1 @ X0))
% 0.68/0.92           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.68/0.92      inference('demod', [status(thm)], ['123', '124'])).
% 0.68/0.92  thf('126', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 0.68/0.92           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.68/0.92      inference('sup+', [status(thm)], ['111', '125'])).
% 0.68/0.92  thf('127', plain,
% 0.68/0.92      (((k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B))
% 0.68/0.92         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.68/0.92      inference('demod', [status(thm)], ['4', '126'])).
% 0.68/0.92  thf('128', plain, ($false), inference('simplify', [status(thm)], ['127'])).
% 0.68/0.92  
% 0.68/0.92  % SZS output end Refutation
% 0.68/0.92  
% 0.68/0.92  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
