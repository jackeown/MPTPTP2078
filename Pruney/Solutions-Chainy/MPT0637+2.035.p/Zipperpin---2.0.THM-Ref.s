%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qZJ0ABhUn2

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:00 EST 2020

% Result     : Theorem 1.34s
% Output     : Refutation 1.44s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 335 expanded)
%              Number of leaves         :   26 ( 124 expanded)
%              Depth                    :   15
%              Number of atoms          : 1107 (2799 expanded)
%              Number of equality atoms :   80 ( 226 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t123_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ B )
        = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k8_relat_1 @ X20 @ X19 )
        = ( k5_relat_1 @ X19 @ ( k6_relat_1 @ X20 ) ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
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
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('4',plain,(
    ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ sk_B ) )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('6',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['5'])).

thf(t77_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B )
          = B ) ) ) )).

thf('7',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X30 ) @ X31 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X31 ) @ X30 )
        = X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t77_relat_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k8_relat_1 @ X20 @ X19 )
        = ( k5_relat_1 @ X19 @ ( k6_relat_1 @ X20 ) ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('10',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k8_relat_1 @ X20 @ X19 )
        = ( k5_relat_1 @ X19 @ ( k6_relat_1 @ X20 ) ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

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
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X24 @ X23 ) @ X25 )
        = ( k5_relat_1 @ X24 @ ( k5_relat_1 @ X23 @ X25 ) ) )
      | ~ ( v1_relat_1 @ X25 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k8_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X2 ) ) ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k8_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X2 ) ) ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k8_relat_1 @ X2 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X2 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf('16',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k8_relat_1 @ X2 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X2 ) ) ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k8_relat_1 @ X2 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X2 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k8_relat_1 @ X20 @ X19 )
        = ( k5_relat_1 @ X19 @ ( k6_relat_1 @ X20 ) ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('20',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X24 @ X23 ) @ X25 )
        = ( k5_relat_1 @ X24 @ ( k5_relat_1 @ X23 @ X25 ) ) )
      | ~ ( v1_relat_1 @ X25 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X2 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X2 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('25',plain,(
    ! [X27: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('26',plain,(
    ! [X32: $i] :
      ( ( ( k5_relat_1 @ X32 @ ( k6_relat_1 @ ( k2_relat_1 @ X32 ) ) )
        = X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k8_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X2 ) ) ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k8_relat_1 @ X1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('33',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('34',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['31','32','33','34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
        = ( k5_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X1 ) ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['24','36'])).

thf('38',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k8_relat_1 @ X20 @ X19 )
        = ( k5_relat_1 @ X19 @ ( k6_relat_1 @ X20 ) ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('44',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['37','42','43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k8_relat_1 @ X2 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
        = ( k5_relat_1 @ X0 @ ( k8_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['18','45'])).

thf('47',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k8_relat_1 @ X20 @ X19 )
        = ( k5_relat_1 @ X19 @ ( k6_relat_1 @ X20 ) ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t76_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B )
        & ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ) )).

thf('48',plain,(
    ! [X28: $i,X29: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X28 @ ( k6_relat_1 @ X29 ) ) @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t76_relat_1])).

thf('49',plain,(
    ! [X27: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t125_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k8_relat_1 @ A @ B )
          = B ) ) ) )).

thf('50',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X21 ) @ X22 )
      | ( ( k8_relat_1 @ X22 @ X21 )
        = X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t125_relat_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) )
        = ( k6_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['48','53'])).

thf('55',plain,(
    ! [X26: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('56',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X33 @ X34 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X33 ) @ X34 ) )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( k3_xboole_0 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k8_relat_1 @ X20 @ X19 )
        = ( k5_relat_1 @ X19 @ ( k6_relat_1 @ X20 ) ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('61',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k7_relat_1 @ X36 @ X35 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X35 ) @ X36 ) )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('64',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['59','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k6_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) )
        = ( k3_xboole_0 @ X1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['54','66'])).

thf('68',plain,(
    ! [X26: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
        = ( k3_xboole_0 @ X1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf(fc1_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('70',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[fc1_relat_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['47','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k8_relat_1 @ X2 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
        = ( k5_relat_1 @ X0 @ ( k8_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) ) ) ) ),
    inference(clc,[status(thm)],['46','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ X1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) @ ( k6_relat_1 @ X0 ) ) )
        = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ) ) ),
    inference('sup+',[status(thm)],['8','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['59','65'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['37','42','43','44'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('80',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['79','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['79','82'])).

thf('85',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k7_relat_1 @ X36 @ X35 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X35 ) @ X36 ) )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('89',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('90',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['87','88','89','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['59','65'])).

thf('93',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['76','77','78','83','84','91','92','93'])).

thf('95',plain,(
    ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ sk_B ) )
 != ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','94'])).

thf('96',plain,(
    $false ),
    inference(simplify,[status(thm)],['95'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qZJ0ABhUn2
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:56:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.34/1.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.34/1.62  % Solved by: fo/fo7.sh
% 1.34/1.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.34/1.62  % done 1874 iterations in 1.166s
% 1.34/1.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.34/1.62  % SZS output start Refutation
% 1.34/1.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.34/1.62  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.34/1.62  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.34/1.62  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.34/1.62  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.34/1.62  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.34/1.62  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 1.34/1.62  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.34/1.62  thf(sk_A_type, type, sk_A: $i).
% 1.34/1.62  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 1.34/1.62  thf(sk_B_type, type, sk_B: $i).
% 1.34/1.62  thf(t123_relat_1, axiom,
% 1.34/1.62    (![A:$i,B:$i]:
% 1.34/1.62     ( ( v1_relat_1 @ B ) =>
% 1.34/1.62       ( ( k8_relat_1 @ A @ B ) = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ))).
% 1.34/1.62  thf('0', plain,
% 1.34/1.62      (![X19 : $i, X20 : $i]:
% 1.34/1.62         (((k8_relat_1 @ X20 @ X19) = (k5_relat_1 @ X19 @ (k6_relat_1 @ X20)))
% 1.34/1.62          | ~ (v1_relat_1 @ X19))),
% 1.34/1.62      inference('cnf', [status(esa)], [t123_relat_1])).
% 1.34/1.62  thf(t43_funct_1, conjecture,
% 1.34/1.62    (![A:$i,B:$i]:
% 1.34/1.62     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 1.34/1.62       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.34/1.62  thf(zf_stmt_0, negated_conjecture,
% 1.34/1.62    (~( ![A:$i,B:$i]:
% 1.34/1.62        ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 1.34/1.62          ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 1.34/1.62    inference('cnf.neg', [status(esa)], [t43_funct_1])).
% 1.34/1.62  thf('1', plain,
% 1.34/1.62      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A))
% 1.34/1.62         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 1.34/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.34/1.62  thf('2', plain,
% 1.34/1.62      ((((k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B))
% 1.34/1.62          != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))
% 1.34/1.62        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_B)))),
% 1.34/1.62      inference('sup-', [status(thm)], ['0', '1'])).
% 1.34/1.62  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 1.34/1.62  thf('3', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 1.34/1.62      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.34/1.62  thf('4', plain,
% 1.34/1.62      (((k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B))
% 1.34/1.62         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 1.34/1.62      inference('demod', [status(thm)], ['2', '3'])).
% 1.34/1.62  thf(d10_xboole_0, axiom,
% 1.34/1.62    (![A:$i,B:$i]:
% 1.34/1.62     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.34/1.62  thf('5', plain,
% 1.34/1.62      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 1.34/1.62      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.34/1.62  thf('6', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 1.34/1.62      inference('simplify', [status(thm)], ['5'])).
% 1.34/1.62  thf(t77_relat_1, axiom,
% 1.34/1.62    (![A:$i,B:$i]:
% 1.34/1.62     ( ( v1_relat_1 @ B ) =>
% 1.34/1.62       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 1.34/1.62         ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ) ))).
% 1.34/1.62  thf('7', plain,
% 1.34/1.62      (![X30 : $i, X31 : $i]:
% 1.34/1.62         (~ (r1_tarski @ (k1_relat_1 @ X30) @ X31)
% 1.34/1.62          | ((k5_relat_1 @ (k6_relat_1 @ X31) @ X30) = (X30))
% 1.34/1.62          | ~ (v1_relat_1 @ X30))),
% 1.34/1.62      inference('cnf', [status(esa)], [t77_relat_1])).
% 1.34/1.62  thf('8', plain,
% 1.34/1.62      (![X0 : $i]:
% 1.34/1.62         (~ (v1_relat_1 @ X0)
% 1.34/1.62          | ((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X0) = (X0)))),
% 1.34/1.62      inference('sup-', [status(thm)], ['6', '7'])).
% 1.34/1.62  thf('9', plain,
% 1.34/1.62      (![X19 : $i, X20 : $i]:
% 1.34/1.62         (((k8_relat_1 @ X20 @ X19) = (k5_relat_1 @ X19 @ (k6_relat_1 @ X20)))
% 1.34/1.62          | ~ (v1_relat_1 @ X19))),
% 1.34/1.62      inference('cnf', [status(esa)], [t123_relat_1])).
% 1.34/1.62  thf('10', plain,
% 1.34/1.62      (![X19 : $i, X20 : $i]:
% 1.34/1.62         (((k8_relat_1 @ X20 @ X19) = (k5_relat_1 @ X19 @ (k6_relat_1 @ X20)))
% 1.34/1.62          | ~ (v1_relat_1 @ X19))),
% 1.34/1.62      inference('cnf', [status(esa)], [t123_relat_1])).
% 1.34/1.62  thf(t55_relat_1, axiom,
% 1.34/1.62    (![A:$i]:
% 1.34/1.62     ( ( v1_relat_1 @ A ) =>
% 1.34/1.62       ( ![B:$i]:
% 1.34/1.62         ( ( v1_relat_1 @ B ) =>
% 1.34/1.62           ( ![C:$i]:
% 1.34/1.62             ( ( v1_relat_1 @ C ) =>
% 1.34/1.62               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 1.34/1.62                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 1.34/1.62  thf('11', plain,
% 1.34/1.62      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.34/1.62         (~ (v1_relat_1 @ X23)
% 1.34/1.62          | ((k5_relat_1 @ (k5_relat_1 @ X24 @ X23) @ X25)
% 1.34/1.62              = (k5_relat_1 @ X24 @ (k5_relat_1 @ X23 @ X25)))
% 1.34/1.62          | ~ (v1_relat_1 @ X25)
% 1.34/1.62          | ~ (v1_relat_1 @ X24))),
% 1.34/1.62      inference('cnf', [status(esa)], [t55_relat_1])).
% 1.34/1.62  thf('12', plain,
% 1.34/1.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.34/1.62         (((k8_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0))
% 1.34/1.62            = (k5_relat_1 @ X1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X2))))
% 1.34/1.62          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 1.34/1.62          | ~ (v1_relat_1 @ X1)
% 1.34/1.62          | ~ (v1_relat_1 @ (k6_relat_1 @ X2))
% 1.34/1.62          | ~ (v1_relat_1 @ X0))),
% 1.34/1.62      inference('sup+', [status(thm)], ['10', '11'])).
% 1.34/1.62  thf('13', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 1.34/1.62      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.34/1.62  thf('14', plain,
% 1.34/1.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.34/1.62         (((k8_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0))
% 1.34/1.62            = (k5_relat_1 @ X1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X2))))
% 1.34/1.62          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 1.34/1.62          | ~ (v1_relat_1 @ X1)
% 1.34/1.62          | ~ (v1_relat_1 @ X0))),
% 1.34/1.62      inference('demod', [status(thm)], ['12', '13'])).
% 1.34/1.62  thf('15', plain,
% 1.34/1.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.34/1.62         (~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X0))
% 1.34/1.62          | ~ (v1_relat_1 @ X0)
% 1.34/1.62          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 1.34/1.62          | ~ (v1_relat_1 @ X0)
% 1.34/1.62          | ((k8_relat_1 @ X2 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 1.34/1.62              = (k5_relat_1 @ X0 @ 
% 1.34/1.62                 (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X2)))))),
% 1.34/1.62      inference('sup-', [status(thm)], ['9', '14'])).
% 1.34/1.62  thf('16', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 1.34/1.62      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.34/1.62  thf('17', plain,
% 1.34/1.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.34/1.62         (~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X0))
% 1.34/1.62          | ~ (v1_relat_1 @ X0)
% 1.34/1.62          | ~ (v1_relat_1 @ X0)
% 1.34/1.62          | ((k8_relat_1 @ X2 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 1.34/1.62              = (k5_relat_1 @ X0 @ 
% 1.34/1.62                 (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X2)))))),
% 1.34/1.62      inference('demod', [status(thm)], ['15', '16'])).
% 1.34/1.62  thf('18', plain,
% 1.34/1.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.34/1.62         (((k8_relat_1 @ X2 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 1.34/1.62            = (k5_relat_1 @ X0 @ 
% 1.34/1.62               (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X2))))
% 1.34/1.62          | ~ (v1_relat_1 @ X0)
% 1.34/1.62          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X0)))),
% 1.34/1.62      inference('simplify', [status(thm)], ['17'])).
% 1.34/1.62  thf('19', plain,
% 1.34/1.62      (![X19 : $i, X20 : $i]:
% 1.34/1.62         (((k8_relat_1 @ X20 @ X19) = (k5_relat_1 @ X19 @ (k6_relat_1 @ X20)))
% 1.34/1.62          | ~ (v1_relat_1 @ X19))),
% 1.34/1.62      inference('cnf', [status(esa)], [t123_relat_1])).
% 1.34/1.62  thf('20', plain,
% 1.34/1.62      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.34/1.62         (~ (v1_relat_1 @ X23)
% 1.34/1.62          | ((k5_relat_1 @ (k5_relat_1 @ X24 @ X23) @ X25)
% 1.34/1.62              = (k5_relat_1 @ X24 @ (k5_relat_1 @ X23 @ X25)))
% 1.34/1.62          | ~ (v1_relat_1 @ X25)
% 1.34/1.62          | ~ (v1_relat_1 @ X24))),
% 1.34/1.62      inference('cnf', [status(esa)], [t55_relat_1])).
% 1.34/1.62  thf('21', plain,
% 1.34/1.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.34/1.62         (((k5_relat_1 @ (k8_relat_1 @ X1 @ X0) @ X2)
% 1.34/1.62            = (k5_relat_1 @ X0 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X2)))
% 1.34/1.62          | ~ (v1_relat_1 @ X0)
% 1.34/1.62          | ~ (v1_relat_1 @ X0)
% 1.34/1.62          | ~ (v1_relat_1 @ X2)
% 1.34/1.62          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 1.34/1.62      inference('sup+', [status(thm)], ['19', '20'])).
% 1.34/1.62  thf('22', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 1.34/1.62      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.34/1.62  thf('23', plain,
% 1.34/1.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.34/1.62         (((k5_relat_1 @ (k8_relat_1 @ X1 @ X0) @ X2)
% 1.34/1.62            = (k5_relat_1 @ X0 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X2)))
% 1.34/1.62          | ~ (v1_relat_1 @ X0)
% 1.34/1.62          | ~ (v1_relat_1 @ X0)
% 1.34/1.62          | ~ (v1_relat_1 @ X2))),
% 1.34/1.62      inference('demod', [status(thm)], ['21', '22'])).
% 1.34/1.62  thf('24', plain,
% 1.34/1.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.34/1.62         (~ (v1_relat_1 @ X2)
% 1.34/1.62          | ~ (v1_relat_1 @ X0)
% 1.34/1.62          | ((k5_relat_1 @ (k8_relat_1 @ X1 @ X0) @ X2)
% 1.34/1.62              = (k5_relat_1 @ X0 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X2))))),
% 1.34/1.62      inference('simplify', [status(thm)], ['23'])).
% 1.34/1.62  thf(t71_relat_1, axiom,
% 1.34/1.62    (![A:$i]:
% 1.34/1.62     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 1.34/1.62       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 1.34/1.62  thf('25', plain, (![X27 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X27)) = (X27))),
% 1.34/1.62      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.34/1.62  thf(t80_relat_1, axiom,
% 1.34/1.62    (![A:$i]:
% 1.34/1.62     ( ( v1_relat_1 @ A ) =>
% 1.34/1.62       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 1.34/1.62  thf('26', plain,
% 1.34/1.62      (![X32 : $i]:
% 1.34/1.62         (((k5_relat_1 @ X32 @ (k6_relat_1 @ (k2_relat_1 @ X32))) = (X32))
% 1.34/1.62          | ~ (v1_relat_1 @ X32))),
% 1.34/1.62      inference('cnf', [status(esa)], [t80_relat_1])).
% 1.34/1.62  thf('27', plain,
% 1.34/1.62      (![X0 : $i]:
% 1.34/1.62         (((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 1.34/1.62            = (k6_relat_1 @ X0))
% 1.34/1.62          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 1.34/1.62      inference('sup+', [status(thm)], ['25', '26'])).
% 1.34/1.62  thf('28', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 1.34/1.62      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.34/1.62  thf('29', plain,
% 1.34/1.62      (![X0 : $i]:
% 1.34/1.62         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 1.34/1.62           = (k6_relat_1 @ X0))),
% 1.34/1.62      inference('demod', [status(thm)], ['27', '28'])).
% 1.34/1.62  thf('30', plain,
% 1.34/1.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.34/1.62         (((k8_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0))
% 1.34/1.62            = (k5_relat_1 @ X1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X2))))
% 1.34/1.62          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 1.34/1.62          | ~ (v1_relat_1 @ X1)
% 1.34/1.62          | ~ (v1_relat_1 @ X0))),
% 1.34/1.62      inference('demod', [status(thm)], ['12', '13'])).
% 1.34/1.62  thf('31', plain,
% 1.34/1.62      (![X0 : $i, X1 : $i]:
% 1.34/1.62         (~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 1.34/1.62          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 1.34/1.62          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 1.34/1.62          | ((k8_relat_1 @ X1 @ 
% 1.34/1.62              (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0)))
% 1.34/1.62              = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 1.34/1.62                 (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1)))))),
% 1.34/1.62      inference('sup-', [status(thm)], ['29', '30'])).
% 1.34/1.62  thf('32', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 1.34/1.62      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.34/1.62  thf('33', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 1.34/1.62      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.34/1.62  thf('34', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 1.34/1.62      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.34/1.62  thf('35', plain,
% 1.34/1.62      (![X0 : $i]:
% 1.34/1.62         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 1.34/1.62           = (k6_relat_1 @ X0))),
% 1.34/1.62      inference('demod', [status(thm)], ['27', '28'])).
% 1.34/1.62  thf('36', plain,
% 1.34/1.62      (![X0 : $i, X1 : $i]:
% 1.34/1.62         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 1.34/1.62           = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 1.34/1.62              (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))))),
% 1.34/1.62      inference('demod', [status(thm)], ['31', '32', '33', '34', '35'])).
% 1.34/1.62  thf('37', plain,
% 1.34/1.62      (![X0 : $i, X1 : $i]:
% 1.34/1.62         (((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 1.34/1.62            = (k5_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X1)) @ 
% 1.34/1.62               (k6_relat_1 @ X0)))
% 1.34/1.62          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 1.34/1.62          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 1.34/1.62      inference('sup+', [status(thm)], ['24', '36'])).
% 1.34/1.62  thf('38', plain,
% 1.34/1.62      (![X19 : $i, X20 : $i]:
% 1.34/1.62         (((k8_relat_1 @ X20 @ X19) = (k5_relat_1 @ X19 @ (k6_relat_1 @ X20)))
% 1.34/1.62          | ~ (v1_relat_1 @ X19))),
% 1.34/1.62      inference('cnf', [status(esa)], [t123_relat_1])).
% 1.34/1.62  thf('39', plain,
% 1.34/1.62      (![X0 : $i]:
% 1.34/1.62         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 1.34/1.62           = (k6_relat_1 @ X0))),
% 1.34/1.62      inference('demod', [status(thm)], ['27', '28'])).
% 1.34/1.62  thf('40', plain,
% 1.34/1.62      (![X0 : $i]:
% 1.34/1.62         (((k8_relat_1 @ X0 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0))
% 1.34/1.62          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 1.34/1.62      inference('sup+', [status(thm)], ['38', '39'])).
% 1.34/1.62  thf('41', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 1.34/1.62      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.34/1.62  thf('42', plain,
% 1.34/1.62      (![X0 : $i]: ((k8_relat_1 @ X0 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0))),
% 1.34/1.62      inference('demod', [status(thm)], ['40', '41'])).
% 1.34/1.62  thf('43', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 1.34/1.62      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.34/1.62  thf('44', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 1.34/1.62      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.34/1.62  thf('45', plain,
% 1.34/1.62      (![X0 : $i, X1 : $i]:
% 1.34/1.62         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 1.34/1.62           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 1.34/1.62      inference('demod', [status(thm)], ['37', '42', '43', '44'])).
% 1.34/1.62  thf('46', plain,
% 1.34/1.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.34/1.62         (((k8_relat_1 @ X2 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 1.34/1.62            = (k5_relat_1 @ X0 @ (k8_relat_1 @ X2 @ (k6_relat_1 @ X1))))
% 1.34/1.62          | ~ (v1_relat_1 @ X0)
% 1.34/1.62          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X0)))),
% 1.34/1.62      inference('demod', [status(thm)], ['18', '45'])).
% 1.34/1.62  thf('47', plain,
% 1.34/1.62      (![X19 : $i, X20 : $i]:
% 1.34/1.62         (((k8_relat_1 @ X20 @ X19) = (k5_relat_1 @ X19 @ (k6_relat_1 @ X20)))
% 1.34/1.62          | ~ (v1_relat_1 @ X19))),
% 1.34/1.62      inference('cnf', [status(esa)], [t123_relat_1])).
% 1.34/1.62  thf(t76_relat_1, axiom,
% 1.34/1.62    (![A:$i,B:$i]:
% 1.34/1.62     ( ( v1_relat_1 @ B ) =>
% 1.34/1.62       ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B ) & 
% 1.34/1.62         ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ))).
% 1.34/1.62  thf('48', plain,
% 1.34/1.62      (![X28 : $i, X29 : $i]:
% 1.34/1.62         ((r1_tarski @ (k5_relat_1 @ X28 @ (k6_relat_1 @ X29)) @ X28)
% 1.34/1.62          | ~ (v1_relat_1 @ X28))),
% 1.34/1.62      inference('cnf', [status(esa)], [t76_relat_1])).
% 1.34/1.62  thf('49', plain, (![X27 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X27)) = (X27))),
% 1.34/1.62      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.34/1.62  thf(t125_relat_1, axiom,
% 1.34/1.62    (![A:$i,B:$i]:
% 1.34/1.62     ( ( v1_relat_1 @ B ) =>
% 1.34/1.62       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 1.34/1.62         ( ( k8_relat_1 @ A @ B ) = ( B ) ) ) ))).
% 1.34/1.62  thf('50', plain,
% 1.34/1.62      (![X21 : $i, X22 : $i]:
% 1.34/1.62         (~ (r1_tarski @ (k2_relat_1 @ X21) @ X22)
% 1.34/1.62          | ((k8_relat_1 @ X22 @ X21) = (X21))
% 1.34/1.62          | ~ (v1_relat_1 @ X21))),
% 1.34/1.62      inference('cnf', [status(esa)], [t125_relat_1])).
% 1.34/1.62  thf('51', plain,
% 1.34/1.62      (![X0 : $i, X1 : $i]:
% 1.34/1.62         (~ (r1_tarski @ X0 @ X1)
% 1.34/1.62          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 1.34/1.62          | ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0)))),
% 1.34/1.62      inference('sup-', [status(thm)], ['49', '50'])).
% 1.34/1.62  thf('52', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 1.34/1.62      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.34/1.62  thf('53', plain,
% 1.34/1.62      (![X0 : $i, X1 : $i]:
% 1.34/1.62         (~ (r1_tarski @ X0 @ X1)
% 1.34/1.62          | ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0)))),
% 1.34/1.62      inference('demod', [status(thm)], ['51', '52'])).
% 1.34/1.62  thf('54', plain,
% 1.34/1.62      (![X0 : $i, X1 : $i]:
% 1.34/1.62         (~ (v1_relat_1 @ X0)
% 1.34/1.62          | ((k8_relat_1 @ X0 @ 
% 1.34/1.62              (k6_relat_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1))))
% 1.34/1.62              = (k6_relat_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)))))),
% 1.34/1.62      inference('sup-', [status(thm)], ['48', '53'])).
% 1.34/1.62  thf('55', plain, (![X26 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X26)) = (X26))),
% 1.34/1.62      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.34/1.62  thf(t90_relat_1, axiom,
% 1.34/1.62    (![A:$i,B:$i]:
% 1.34/1.62     ( ( v1_relat_1 @ B ) =>
% 1.34/1.62       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 1.34/1.62         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 1.34/1.62  thf('56', plain,
% 1.34/1.62      (![X33 : $i, X34 : $i]:
% 1.34/1.62         (((k1_relat_1 @ (k7_relat_1 @ X33 @ X34))
% 1.34/1.62            = (k3_xboole_0 @ (k1_relat_1 @ X33) @ X34))
% 1.34/1.62          | ~ (v1_relat_1 @ X33))),
% 1.34/1.62      inference('cnf', [status(esa)], [t90_relat_1])).
% 1.34/1.62  thf('57', plain,
% 1.34/1.62      (![X0 : $i, X1 : $i]:
% 1.34/1.62         (((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 1.34/1.62            = (k3_xboole_0 @ X0 @ X1))
% 1.34/1.62          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 1.34/1.62      inference('sup+', [status(thm)], ['55', '56'])).
% 1.34/1.62  thf('58', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 1.34/1.62      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.34/1.62  thf('59', plain,
% 1.34/1.62      (![X0 : $i, X1 : $i]:
% 1.34/1.62         ((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 1.34/1.62           = (k3_xboole_0 @ X0 @ X1))),
% 1.34/1.62      inference('demod', [status(thm)], ['57', '58'])).
% 1.34/1.62  thf('60', plain,
% 1.34/1.62      (![X19 : $i, X20 : $i]:
% 1.34/1.62         (((k8_relat_1 @ X20 @ X19) = (k5_relat_1 @ X19 @ (k6_relat_1 @ X20)))
% 1.34/1.62          | ~ (v1_relat_1 @ X19))),
% 1.34/1.62      inference('cnf', [status(esa)], [t123_relat_1])).
% 1.34/1.62  thf(t94_relat_1, axiom,
% 1.34/1.62    (![A:$i,B:$i]:
% 1.34/1.62     ( ( v1_relat_1 @ B ) =>
% 1.34/1.62       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 1.34/1.62  thf('61', plain,
% 1.34/1.62      (![X35 : $i, X36 : $i]:
% 1.34/1.62         (((k7_relat_1 @ X36 @ X35) = (k5_relat_1 @ (k6_relat_1 @ X35) @ X36))
% 1.34/1.62          | ~ (v1_relat_1 @ X36))),
% 1.34/1.62      inference('cnf', [status(esa)], [t94_relat_1])).
% 1.34/1.62  thf('62', plain,
% 1.34/1.62      (![X0 : $i, X1 : $i]:
% 1.34/1.62         (((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 1.34/1.62            = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 1.34/1.62          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 1.34/1.62          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 1.34/1.62      inference('sup+', [status(thm)], ['60', '61'])).
% 1.34/1.62  thf('63', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 1.34/1.62      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.34/1.62  thf('64', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 1.34/1.62      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.34/1.62  thf('65', plain,
% 1.34/1.62      (![X0 : $i, X1 : $i]:
% 1.34/1.62         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 1.34/1.62           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 1.34/1.62      inference('demod', [status(thm)], ['62', '63', '64'])).
% 1.34/1.62  thf('66', plain,
% 1.34/1.62      (![X0 : $i, X1 : $i]:
% 1.34/1.62         ((k1_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 1.34/1.62           = (k3_xboole_0 @ X0 @ X1))),
% 1.34/1.62      inference('demod', [status(thm)], ['59', '65'])).
% 1.34/1.62  thf('67', plain,
% 1.34/1.62      (![X0 : $i, X1 : $i]:
% 1.34/1.62         (((k1_relat_1 @ (k6_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))))
% 1.34/1.62            = (k3_xboole_0 @ X1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))))
% 1.34/1.62          | ~ (v1_relat_1 @ X1))),
% 1.34/1.62      inference('sup+', [status(thm)], ['54', '66'])).
% 1.34/1.62  thf('68', plain, (![X26 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X26)) = (X26))),
% 1.34/1.62      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.34/1.62  thf('69', plain,
% 1.34/1.62      (![X0 : $i, X1 : $i]:
% 1.34/1.62         (((k5_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 1.34/1.62            = (k3_xboole_0 @ X1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))))
% 1.34/1.62          | ~ (v1_relat_1 @ X1))),
% 1.34/1.62      inference('demod', [status(thm)], ['67', '68'])).
% 1.34/1.62  thf(fc1_relat_1, axiom,
% 1.34/1.62    (![A:$i,B:$i]:
% 1.34/1.62     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.34/1.62  thf('70', plain,
% 1.34/1.62      (![X17 : $i, X18 : $i]:
% 1.34/1.62         (~ (v1_relat_1 @ X17) | (v1_relat_1 @ (k3_xboole_0 @ X17 @ X18)))),
% 1.34/1.62      inference('cnf', [status(esa)], [fc1_relat_1])).
% 1.34/1.62  thf('71', plain,
% 1.34/1.62      (![X0 : $i, X1 : $i]:
% 1.34/1.62         ((v1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 1.34/1.62          | ~ (v1_relat_1 @ X1)
% 1.34/1.62          | ~ (v1_relat_1 @ X1))),
% 1.34/1.62      inference('sup+', [status(thm)], ['69', '70'])).
% 1.34/1.62  thf('72', plain,
% 1.34/1.62      (![X0 : $i, X1 : $i]:
% 1.34/1.62         (~ (v1_relat_1 @ X1)
% 1.34/1.62          | (v1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 1.34/1.62      inference('simplify', [status(thm)], ['71'])).
% 1.34/1.62  thf('73', plain,
% 1.34/1.62      (![X0 : $i, X1 : $i]:
% 1.34/1.62         ((v1_relat_1 @ (k8_relat_1 @ X1 @ X0))
% 1.34/1.62          | ~ (v1_relat_1 @ X0)
% 1.34/1.62          | ~ (v1_relat_1 @ X0))),
% 1.34/1.62      inference('sup+', [status(thm)], ['47', '72'])).
% 1.34/1.62  thf('74', plain,
% 1.34/1.62      (![X0 : $i, X1 : $i]:
% 1.34/1.62         (~ (v1_relat_1 @ X0) | (v1_relat_1 @ (k8_relat_1 @ X1 @ X0)))),
% 1.34/1.62      inference('simplify', [status(thm)], ['73'])).
% 1.34/1.62  thf('75', plain,
% 1.34/1.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.34/1.62         (~ (v1_relat_1 @ X0)
% 1.34/1.62          | ((k8_relat_1 @ X2 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 1.34/1.62              = (k5_relat_1 @ X0 @ (k8_relat_1 @ X2 @ (k6_relat_1 @ X1)))))),
% 1.34/1.62      inference('clc', [status(thm)], ['46', '74'])).
% 1.34/1.62  thf('76', plain,
% 1.34/1.62      (![X0 : $i, X1 : $i]:
% 1.34/1.62         (((k8_relat_1 @ X1 @ 
% 1.34/1.62            (k5_relat_1 @ 
% 1.34/1.62             (k6_relat_1 @ (k1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))) @ 
% 1.34/1.62             (k6_relat_1 @ X0)))
% 1.34/1.62            = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 1.34/1.62          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 1.34/1.62          | ~ (v1_relat_1 @ 
% 1.34/1.62               (k6_relat_1 @ 
% 1.34/1.62                (k1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))))),
% 1.34/1.62      inference('sup+', [status(thm)], ['8', '75'])).
% 1.34/1.62  thf('77', plain,
% 1.34/1.62      (![X0 : $i, X1 : $i]:
% 1.34/1.62         ((k1_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 1.34/1.62           = (k3_xboole_0 @ X0 @ X1))),
% 1.34/1.62      inference('demod', [status(thm)], ['59', '65'])).
% 1.34/1.62  thf('78', plain,
% 1.34/1.62      (![X0 : $i, X1 : $i]:
% 1.34/1.62         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 1.34/1.62           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 1.34/1.62      inference('demod', [status(thm)], ['37', '42', '43', '44'])).
% 1.34/1.62  thf(commutativity_k3_xboole_0, axiom,
% 1.34/1.62    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.34/1.62  thf('79', plain,
% 1.34/1.62      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.34/1.62      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.34/1.62  thf(t17_xboole_1, axiom,
% 1.34/1.62    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 1.34/1.62  thf('80', plain,
% 1.34/1.62      (![X5 : $i, X6 : $i]: (r1_tarski @ (k3_xboole_0 @ X5 @ X6) @ X5)),
% 1.34/1.62      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.34/1.62  thf('81', plain,
% 1.34/1.62      (![X0 : $i, X1 : $i]:
% 1.34/1.62         (~ (r1_tarski @ X0 @ X1)
% 1.34/1.62          | ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0)))),
% 1.34/1.62      inference('demod', [status(thm)], ['51', '52'])).
% 1.34/1.62  thf('82', plain,
% 1.34/1.62      (![X0 : $i, X1 : $i]:
% 1.34/1.62         ((k8_relat_1 @ X0 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))
% 1.34/1.62           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 1.34/1.62      inference('sup-', [status(thm)], ['80', '81'])).
% 1.34/1.62  thf('83', plain,
% 1.34/1.62      (![X0 : $i, X1 : $i]:
% 1.34/1.62         ((k8_relat_1 @ X0 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 1.34/1.62           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 1.34/1.62      inference('sup+', [status(thm)], ['79', '82'])).
% 1.34/1.62  thf('84', plain,
% 1.34/1.62      (![X0 : $i, X1 : $i]:
% 1.34/1.62         ((k8_relat_1 @ X0 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 1.34/1.62           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 1.34/1.62      inference('sup+', [status(thm)], ['79', '82'])).
% 1.34/1.62  thf('85', plain,
% 1.34/1.62      (![X35 : $i, X36 : $i]:
% 1.34/1.62         (((k7_relat_1 @ X36 @ X35) = (k5_relat_1 @ (k6_relat_1 @ X35) @ X36))
% 1.34/1.62          | ~ (v1_relat_1 @ X36))),
% 1.34/1.62      inference('cnf', [status(esa)], [t94_relat_1])).
% 1.34/1.62  thf('86', plain,
% 1.34/1.62      (![X0 : $i, X1 : $i]:
% 1.34/1.62         (~ (v1_relat_1 @ X1)
% 1.34/1.62          | (v1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 1.34/1.62      inference('simplify', [status(thm)], ['71'])).
% 1.34/1.62  thf('87', plain,
% 1.34/1.62      (![X0 : $i, X1 : $i]:
% 1.34/1.62         ((v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 1.34/1.62          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 1.34/1.62          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 1.34/1.62      inference('sup+', [status(thm)], ['85', '86'])).
% 1.34/1.62  thf('88', plain,
% 1.34/1.62      (![X0 : $i, X1 : $i]:
% 1.34/1.62         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 1.34/1.62           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 1.34/1.62      inference('demod', [status(thm)], ['62', '63', '64'])).
% 1.34/1.62  thf('89', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 1.34/1.62      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.34/1.62  thf('90', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 1.34/1.62      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.34/1.62  thf('91', plain,
% 1.34/1.62      (![X0 : $i, X1 : $i]:
% 1.34/1.62         (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 1.34/1.62      inference('demod', [status(thm)], ['87', '88', '89', '90'])).
% 1.34/1.62  thf('92', plain,
% 1.34/1.62      (![X0 : $i, X1 : $i]:
% 1.34/1.62         ((k1_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 1.34/1.62           = (k3_xboole_0 @ X0 @ X1))),
% 1.34/1.62      inference('demod', [status(thm)], ['59', '65'])).
% 1.34/1.62  thf('93', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 1.34/1.62      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.34/1.62  thf('94', plain,
% 1.34/1.62      (![X0 : $i, X1 : $i]:
% 1.34/1.62         ((k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))
% 1.34/1.62           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 1.34/1.62      inference('demod', [status(thm)],
% 1.44/1.62                ['76', '77', '78', '83', '84', '91', '92', '93'])).
% 1.44/1.62  thf('95', plain,
% 1.44/1.62      (((k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B))
% 1.44/1.62         != (k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B)))),
% 1.44/1.62      inference('demod', [status(thm)], ['4', '94'])).
% 1.44/1.62  thf('96', plain, ($false), inference('simplify', [status(thm)], ['95'])).
% 1.44/1.62  
% 1.44/1.62  % SZS output end Refutation
% 1.44/1.62  
% 1.44/1.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
