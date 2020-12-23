%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wPT9QWOod7

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:04 EST 2020

% Result     : Theorem 0.48s
% Output     : Refutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 283 expanded)
%              Number of leaves         :   28 ( 108 expanded)
%              Depth                    :   16
%              Number of atoms          : 1087 (2227 expanded)
%              Number of equality atoms :   77 ( 169 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(t123_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ B )
        = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k8_relat_1 @ X38 @ X37 )
        = ( k5_relat_1 @ X37 @ ( k6_relat_1 @ X38 ) ) )
      | ~ ( v1_relat_1 @ X37 ) ) ),
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

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X29 @ X30 ) )
      = ( k3_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('3',plain,(
    ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k6_relat_1 @ sk_A ) )
 != ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,
    ( ( ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ sk_B ) )
     != ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) ) ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('5',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('6',plain,(
    ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ sk_B ) )
 != ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t78_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A )
        = A ) ) )).

thf('7',plain,(
    ! [X49: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X49 ) ) @ X49 )
        = X49 )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('8',plain,(
    ! [X55: $i,X56: $i] :
      ( ( ( k7_relat_1 @ X56 @ X55 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X55 ) @ X56 ) )
      | ~ ( v1_relat_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k8_relat_1 @ X38 @ X37 )
        = ( k5_relat_1 @ X37 @ ( k6_relat_1 @ X38 ) ) )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('12',plain,(
    ! [X47: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X47 ) )
      = X47 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('13',plain,(
    ! [X49: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X49 ) ) @ X49 )
        = X49 )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(t139_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( k8_relat_1 @ A @ ( k5_relat_1 @ B @ C ) )
            = ( k5_relat_1 @ B @ ( k8_relat_1 @ A @ C ) ) ) ) ) )).

thf('17',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( v1_relat_1 @ X39 )
      | ( ( k8_relat_1 @ X41 @ ( k5_relat_1 @ X40 @ X39 ) )
        = ( k5_relat_1 @ X40 @ ( k8_relat_1 @ X41 @ X39 ) ) )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t139_relat_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('20',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k8_relat_1 @ X38 @ X37 )
        = ( k5_relat_1 @ X37 @ ( k6_relat_1 @ X38 ) ) )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('24',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( v1_relat_1 @ X44 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X45 @ X44 ) @ X46 )
        = ( k5_relat_1 @ X45 @ ( k5_relat_1 @ X44 @ X46 ) ) )
      | ~ ( v1_relat_1 @ X46 )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('27',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['22','28'])).

thf('30',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('31',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','32'])).

thf(t112_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( k7_relat_1 @ ( k5_relat_1 @ B @ C ) @ A )
            = ( k5_relat_1 @ ( k7_relat_1 @ B @ A ) @ C ) ) ) ) )).

thf('34',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( v1_relat_1 @ X34 )
      | ( ( k7_relat_1 @ ( k5_relat_1 @ X35 @ X34 ) @ X36 )
        = ( k5_relat_1 @ ( k7_relat_1 @ X35 @ X36 ) @ X34 ) )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t112_relat_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X2 )
        = ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ ( k6_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k8_relat_1 @ X38 @ X37 )
        = ( k5_relat_1 @ X37 @ ( k6_relat_1 @ X38 ) ) )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('37',plain,(
    ! [X55: $i,X56: $i] :
      ( ( ( k7_relat_1 @ X56 @ X55 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X55 ) @ X56 ) )
      | ~ ( v1_relat_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('40',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('43',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X2 )
      = ( k5_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X2 ) ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['35','41','42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k8_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) @ X0 )
        = ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['11','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('47',plain,(
    ! [X55: $i,X56: $i] :
      ( ( ( k7_relat_1 @ X56 @ X55 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X55 ) @ X56 ) )
      | ~ ( v1_relat_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('48',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( v1_relat_1 @ X31 )
      | ~ ( v1_relat_1 @ X32 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X31 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['46','52'])).

thf('54',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k8_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) @ X0 )
      = ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['45','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
        = ( k8_relat_1 @ X1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ) ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['10','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('59',plain,(
    ! [X53: $i,X54: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X53 @ X54 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X53 ) @ X54 ) )
      | ~ ( v1_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('60',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X29 @ X30 ) )
      = ( k3_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('61',plain,(
    ! [X53: $i,X54: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X53 @ X54 ) )
        = ( k1_setfam_1 @ ( k2_tarski @ ( k1_relat_1 @ X53 ) @ X54 ) ) )
      | ~ ( v1_relat_1 @ X53 ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k1_setfam_1 @ ( k2_tarski @ ( k1_relat_1 @ ( k6_relat_1 @ X1 ) ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['58','61'])).

thf('63',plain,(
    ! [X47: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X47 ) )
      = X47 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('64',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('67',plain,(
    ! [X55: $i,X56: $i] :
      ( ( ( k7_relat_1 @ X56 @ X55 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X55 ) @ X56 ) )
      | ~ ( v1_relat_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t44_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) )).

thf('68',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( v1_relat_1 @ X42 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X43 @ X42 ) ) @ ( k1_relat_1 @ X43 ) )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t44_relat_1])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X47: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X47 ) )
      = X47 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('71',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['66','73'])).

thf('75',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ X0 ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X48: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X48 ) )
      = X48 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('80',plain,(
    ! [X50: $i,X51: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X50 ) @ X51 )
      | ( ( k5_relat_1 @ X50 @ ( k6_relat_1 @ X51 ) )
        = X50 )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','32'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) )
      = ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['78','85'])).

thf('87',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k8_relat_1 @ X38 @ X37 )
        = ( k5_relat_1 @ X37 @ ( k6_relat_1 @ X38 ) ) )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('89',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X29 @ X30 ) )
      = ( k3_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) )
        = ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['87','92'])).

thf('94',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) )
      = ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['57','65','86','95','96'])).

thf('98',plain,(
    ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) ) )
 != ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['6','97'])).

thf('99',plain,(
    $false ),
    inference(simplify,[status(thm)],['98'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wPT9QWOod7
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:15:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.48/0.66  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.48/0.66  % Solved by: fo/fo7.sh
% 0.48/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.48/0.66  % done 256 iterations in 0.211s
% 0.48/0.66  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.48/0.66  % SZS output start Refutation
% 0.48/0.66  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.48/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.48/0.66  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.48/0.66  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.48/0.66  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.48/0.66  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.48/0.66  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.48/0.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.48/0.66  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.48/0.66  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.48/0.66  thf(sk_B_type, type, sk_B: $i).
% 0.48/0.66  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.48/0.66  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.48/0.66  thf(t123_relat_1, axiom,
% 0.48/0.66    (![A:$i,B:$i]:
% 0.48/0.66     ( ( v1_relat_1 @ B ) =>
% 0.48/0.66       ( ( k8_relat_1 @ A @ B ) = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ))).
% 0.48/0.66  thf('0', plain,
% 0.48/0.66      (![X37 : $i, X38 : $i]:
% 0.48/0.66         (((k8_relat_1 @ X38 @ X37) = (k5_relat_1 @ X37 @ (k6_relat_1 @ X38)))
% 0.48/0.66          | ~ (v1_relat_1 @ X37))),
% 0.48/0.66      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.48/0.66  thf(t43_funct_1, conjecture,
% 0.48/0.66    (![A:$i,B:$i]:
% 0.48/0.66     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.48/0.66       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.48/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.48/0.66    (~( ![A:$i,B:$i]:
% 0.48/0.66        ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.48/0.66          ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 0.48/0.66    inference('cnf.neg', [status(esa)], [t43_funct_1])).
% 0.48/0.66  thf('1', plain,
% 0.48/0.66      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A))
% 0.48/0.66         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.48/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.66  thf(t12_setfam_1, axiom,
% 0.48/0.66    (![A:$i,B:$i]:
% 0.48/0.66     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.48/0.66  thf('2', plain,
% 0.48/0.66      (![X29 : $i, X30 : $i]:
% 0.48/0.66         ((k1_setfam_1 @ (k2_tarski @ X29 @ X30)) = (k3_xboole_0 @ X29 @ X30))),
% 0.48/0.66      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.48/0.66  thf('3', plain,
% 0.48/0.66      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A))
% 0.48/0.66         != (k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B))))),
% 0.48/0.66      inference('demod', [status(thm)], ['1', '2'])).
% 0.48/0.66  thf('4', plain,
% 0.48/0.66      ((((k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B))
% 0.48/0.66          != (k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B))))
% 0.48/0.66        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_B)))),
% 0.48/0.66      inference('sup-', [status(thm)], ['0', '3'])).
% 0.48/0.66  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.48/0.66  thf('5', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 0.48/0.66      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.48/0.66  thf('6', plain,
% 0.48/0.66      (((k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B))
% 0.48/0.66         != (k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B))))),
% 0.48/0.66      inference('demod', [status(thm)], ['4', '5'])).
% 0.48/0.66  thf(t78_relat_1, axiom,
% 0.48/0.66    (![A:$i]:
% 0.48/0.66     ( ( v1_relat_1 @ A ) =>
% 0.48/0.66       ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A ) = ( A ) ) ))).
% 0.48/0.66  thf('7', plain,
% 0.48/0.66      (![X49 : $i]:
% 0.48/0.66         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X49)) @ X49) = (X49))
% 0.48/0.66          | ~ (v1_relat_1 @ X49))),
% 0.48/0.66      inference('cnf', [status(esa)], [t78_relat_1])).
% 0.48/0.66  thf(t94_relat_1, axiom,
% 0.48/0.66    (![A:$i,B:$i]:
% 0.48/0.66     ( ( v1_relat_1 @ B ) =>
% 0.48/0.66       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.48/0.66  thf('8', plain,
% 0.48/0.66      (![X55 : $i, X56 : $i]:
% 0.48/0.66         (((k7_relat_1 @ X56 @ X55) = (k5_relat_1 @ (k6_relat_1 @ X55) @ X56))
% 0.48/0.66          | ~ (v1_relat_1 @ X56))),
% 0.48/0.66      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.48/0.66  thf('9', plain,
% 0.48/0.66      (![X0 : $i]:
% 0.48/0.66         (((k7_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (X0))
% 0.48/0.66          | ~ (v1_relat_1 @ X0)
% 0.48/0.66          | ~ (v1_relat_1 @ X0))),
% 0.48/0.66      inference('sup+', [status(thm)], ['7', '8'])).
% 0.48/0.66  thf('10', plain,
% 0.48/0.66      (![X0 : $i]:
% 0.48/0.66         (~ (v1_relat_1 @ X0) | ((k7_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (X0)))),
% 0.48/0.66      inference('simplify', [status(thm)], ['9'])).
% 0.48/0.66  thf('11', plain,
% 0.48/0.66      (![X37 : $i, X38 : $i]:
% 0.48/0.66         (((k8_relat_1 @ X38 @ X37) = (k5_relat_1 @ X37 @ (k6_relat_1 @ X38)))
% 0.48/0.66          | ~ (v1_relat_1 @ X37))),
% 0.48/0.66      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.48/0.66  thf(t71_relat_1, axiom,
% 0.48/0.66    (![A:$i]:
% 0.48/0.66     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.48/0.66       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.48/0.66  thf('12', plain, (![X47 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X47)) = (X47))),
% 0.48/0.66      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.48/0.66  thf('13', plain,
% 0.48/0.66      (![X49 : $i]:
% 0.48/0.66         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X49)) @ X49) = (X49))
% 0.48/0.66          | ~ (v1_relat_1 @ X49))),
% 0.48/0.66      inference('cnf', [status(esa)], [t78_relat_1])).
% 0.48/0.66  thf('14', plain,
% 0.48/0.66      (![X0 : $i]:
% 0.48/0.66         (((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 0.48/0.66            = (k6_relat_1 @ X0))
% 0.48/0.66          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.48/0.66      inference('sup+', [status(thm)], ['12', '13'])).
% 0.48/0.66  thf('15', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 0.48/0.66      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.48/0.66  thf('16', plain,
% 0.48/0.66      (![X0 : $i]:
% 0.48/0.66         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 0.48/0.66           = (k6_relat_1 @ X0))),
% 0.48/0.66      inference('demod', [status(thm)], ['14', '15'])).
% 0.48/0.66  thf(t139_relat_1, axiom,
% 0.48/0.66    (![A:$i,B:$i]:
% 0.48/0.66     ( ( v1_relat_1 @ B ) =>
% 0.48/0.66       ( ![C:$i]:
% 0.48/0.66         ( ( v1_relat_1 @ C ) =>
% 0.48/0.66           ( ( k8_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) =
% 0.48/0.66             ( k5_relat_1 @ B @ ( k8_relat_1 @ A @ C ) ) ) ) ) ))).
% 0.48/0.66  thf('17', plain,
% 0.48/0.66      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.48/0.66         (~ (v1_relat_1 @ X39)
% 0.48/0.66          | ((k8_relat_1 @ X41 @ (k5_relat_1 @ X40 @ X39))
% 0.48/0.66              = (k5_relat_1 @ X40 @ (k8_relat_1 @ X41 @ X39)))
% 0.48/0.66          | ~ (v1_relat_1 @ X40))),
% 0.48/0.66      inference('cnf', [status(esa)], [t139_relat_1])).
% 0.48/0.66  thf('18', plain,
% 0.48/0.66      (![X0 : $i, X1 : $i]:
% 0.48/0.66         (((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 0.48/0.66            = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.48/0.66               (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))
% 0.48/0.66          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.48/0.66          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.48/0.66      inference('sup+', [status(thm)], ['16', '17'])).
% 0.48/0.66  thf('19', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 0.48/0.66      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.48/0.66  thf('20', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 0.48/0.66      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.48/0.66  thf('21', plain,
% 0.48/0.66      (![X0 : $i, X1 : $i]:
% 0.48/0.66         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 0.48/0.66           = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.48/0.66              (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 0.48/0.66      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.48/0.66  thf('22', plain,
% 0.48/0.66      (![X37 : $i, X38 : $i]:
% 0.48/0.66         (((k8_relat_1 @ X38 @ X37) = (k5_relat_1 @ X37 @ (k6_relat_1 @ X38)))
% 0.48/0.66          | ~ (v1_relat_1 @ X37))),
% 0.48/0.66      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.48/0.66  thf('23', plain,
% 0.48/0.66      (![X0 : $i]:
% 0.48/0.66         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 0.48/0.66           = (k6_relat_1 @ X0))),
% 0.48/0.66      inference('demod', [status(thm)], ['14', '15'])).
% 0.48/0.66  thf(t55_relat_1, axiom,
% 0.48/0.66    (![A:$i]:
% 0.48/0.66     ( ( v1_relat_1 @ A ) =>
% 0.48/0.66       ( ![B:$i]:
% 0.48/0.66         ( ( v1_relat_1 @ B ) =>
% 0.48/0.66           ( ![C:$i]:
% 0.48/0.66             ( ( v1_relat_1 @ C ) =>
% 0.48/0.66               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 0.48/0.66                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 0.48/0.66  thf('24', plain,
% 0.48/0.66      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.48/0.66         (~ (v1_relat_1 @ X44)
% 0.48/0.66          | ((k5_relat_1 @ (k5_relat_1 @ X45 @ X44) @ X46)
% 0.48/0.66              = (k5_relat_1 @ X45 @ (k5_relat_1 @ X44 @ X46)))
% 0.48/0.66          | ~ (v1_relat_1 @ X46)
% 0.48/0.66          | ~ (v1_relat_1 @ X45))),
% 0.48/0.66      inference('cnf', [status(esa)], [t55_relat_1])).
% 0.48/0.66  thf('25', plain,
% 0.48/0.66      (![X0 : $i, X1 : $i]:
% 0.48/0.66         (((k5_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.48/0.66            = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.48/0.66               (k5_relat_1 @ (k6_relat_1 @ X0) @ X1)))
% 0.48/0.66          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.48/0.66          | ~ (v1_relat_1 @ X1)
% 0.48/0.66          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.48/0.66      inference('sup+', [status(thm)], ['23', '24'])).
% 0.48/0.66  thf('26', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 0.48/0.66      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.48/0.66  thf('27', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 0.48/0.66      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.48/0.66  thf('28', plain,
% 0.48/0.66      (![X0 : $i, X1 : $i]:
% 0.48/0.66         (((k5_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.48/0.66            = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.48/0.66               (k5_relat_1 @ (k6_relat_1 @ X0) @ X1)))
% 0.48/0.66          | ~ (v1_relat_1 @ X1))),
% 0.48/0.66      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.48/0.66  thf('29', plain,
% 0.48/0.66      (![X0 : $i, X1 : $i]:
% 0.48/0.66         (((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 0.48/0.66            = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.48/0.66               (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))
% 0.48/0.66          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.48/0.66          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.48/0.66      inference('sup+', [status(thm)], ['22', '28'])).
% 0.48/0.66  thf('30', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 0.48/0.66      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.48/0.66  thf('31', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 0.48/0.66      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.48/0.66  thf('32', plain,
% 0.48/0.66      (![X0 : $i, X1 : $i]:
% 0.48/0.66         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 0.48/0.66           = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.48/0.66              (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 0.48/0.66      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.48/0.66  thf('33', plain,
% 0.48/0.66      (![X0 : $i, X1 : $i]:
% 0.48/0.66         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 0.48/0.66           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.48/0.66      inference('sup+', [status(thm)], ['21', '32'])).
% 0.48/0.66  thf(t112_relat_1, axiom,
% 0.48/0.66    (![A:$i,B:$i]:
% 0.48/0.66     ( ( v1_relat_1 @ B ) =>
% 0.48/0.66       ( ![C:$i]:
% 0.48/0.66         ( ( v1_relat_1 @ C ) =>
% 0.48/0.66           ( ( k7_relat_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 0.48/0.66             ( k5_relat_1 @ ( k7_relat_1 @ B @ A ) @ C ) ) ) ) ))).
% 0.48/0.66  thf('34', plain,
% 0.48/0.66      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.48/0.66         (~ (v1_relat_1 @ X34)
% 0.48/0.66          | ((k7_relat_1 @ (k5_relat_1 @ X35 @ X34) @ X36)
% 0.48/0.66              = (k5_relat_1 @ (k7_relat_1 @ X35 @ X36) @ X34))
% 0.48/0.66          | ~ (v1_relat_1 @ X35))),
% 0.48/0.66      inference('cnf', [status(esa)], [t112_relat_1])).
% 0.48/0.66  thf('35', plain,
% 0.48/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.66         (((k7_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ X2)
% 0.48/0.66            = (k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X2) @ 
% 0.48/0.66               (k6_relat_1 @ X1)))
% 0.48/0.66          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.48/0.66          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.48/0.66      inference('sup+', [status(thm)], ['33', '34'])).
% 0.48/0.66  thf('36', plain,
% 0.48/0.66      (![X37 : $i, X38 : $i]:
% 0.48/0.66         (((k8_relat_1 @ X38 @ X37) = (k5_relat_1 @ X37 @ (k6_relat_1 @ X38)))
% 0.48/0.66          | ~ (v1_relat_1 @ X37))),
% 0.48/0.66      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.48/0.66  thf('37', plain,
% 0.48/0.66      (![X55 : $i, X56 : $i]:
% 0.48/0.66         (((k7_relat_1 @ X56 @ X55) = (k5_relat_1 @ (k6_relat_1 @ X55) @ X56))
% 0.48/0.66          | ~ (v1_relat_1 @ X56))),
% 0.48/0.66      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.48/0.66  thf('38', plain,
% 0.48/0.66      (![X0 : $i, X1 : $i]:
% 0.48/0.66         (((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.48/0.66            = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.48/0.66          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.48/0.66          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.48/0.66      inference('sup+', [status(thm)], ['36', '37'])).
% 0.48/0.66  thf('39', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 0.48/0.66      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.48/0.66  thf('40', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 0.48/0.66      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.48/0.66  thf('41', plain,
% 0.48/0.66      (![X0 : $i, X1 : $i]:
% 0.48/0.66         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.48/0.66           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.48/0.66      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.48/0.66  thf('42', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 0.48/0.66      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.48/0.66  thf('43', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 0.48/0.66      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.48/0.66  thf('44', plain,
% 0.48/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.66         ((k7_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ X2)
% 0.48/0.66           = (k5_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X2)) @ 
% 0.48/0.66              (k6_relat_1 @ X1)))),
% 0.48/0.66      inference('demod', [status(thm)], ['35', '41', '42', '43'])).
% 0.48/0.66  thf('45', plain,
% 0.48/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.66         (((k7_relat_1 @ (k8_relat_1 @ X2 @ (k6_relat_1 @ X1)) @ X0)
% 0.48/0.66            = (k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))
% 0.48/0.66          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 0.48/0.66      inference('sup+', [status(thm)], ['11', '44'])).
% 0.48/0.66  thf('46', plain,
% 0.48/0.66      (![X0 : $i, X1 : $i]:
% 0.48/0.66         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.48/0.66           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.48/0.66      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.48/0.66  thf('47', plain,
% 0.48/0.66      (![X55 : $i, X56 : $i]:
% 0.48/0.66         (((k7_relat_1 @ X56 @ X55) = (k5_relat_1 @ (k6_relat_1 @ X55) @ X56))
% 0.48/0.66          | ~ (v1_relat_1 @ X56))),
% 0.48/0.66      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.48/0.66  thf(dt_k5_relat_1, axiom,
% 0.48/0.66    (![A:$i,B:$i]:
% 0.48/0.66     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.48/0.66       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.48/0.66  thf('48', plain,
% 0.48/0.66      (![X31 : $i, X32 : $i]:
% 0.48/0.66         (~ (v1_relat_1 @ X31)
% 0.48/0.66          | ~ (v1_relat_1 @ X32)
% 0.48/0.66          | (v1_relat_1 @ (k5_relat_1 @ X31 @ X32)))),
% 0.48/0.66      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.48/0.66  thf('49', plain,
% 0.48/0.66      (![X0 : $i, X1 : $i]:
% 0.48/0.66         ((v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.48/0.66          | ~ (v1_relat_1 @ X1)
% 0.48/0.66          | ~ (v1_relat_1 @ X1)
% 0.48/0.66          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.48/0.66      inference('sup+', [status(thm)], ['47', '48'])).
% 0.48/0.66  thf('50', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 0.48/0.66      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.48/0.66  thf('51', plain,
% 0.48/0.66      (![X0 : $i, X1 : $i]:
% 0.48/0.66         ((v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.48/0.66          | ~ (v1_relat_1 @ X1)
% 0.48/0.66          | ~ (v1_relat_1 @ X1))),
% 0.48/0.66      inference('demod', [status(thm)], ['49', '50'])).
% 0.48/0.66  thf('52', plain,
% 0.48/0.66      (![X0 : $i, X1 : $i]:
% 0.48/0.66         (~ (v1_relat_1 @ X1) | (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.48/0.66      inference('simplify', [status(thm)], ['51'])).
% 0.48/0.66  thf('53', plain,
% 0.48/0.66      (![X0 : $i, X1 : $i]:
% 0.48/0.66         ((v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.48/0.66          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.48/0.66      inference('sup+', [status(thm)], ['46', '52'])).
% 0.48/0.66  thf('54', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 0.48/0.66      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.48/0.66  thf('55', plain,
% 0.48/0.66      (![X0 : $i, X1 : $i]:
% 0.48/0.66         (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.48/0.66      inference('demod', [status(thm)], ['53', '54'])).
% 0.48/0.66  thf('56', plain,
% 0.48/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.66         ((k7_relat_1 @ (k8_relat_1 @ X2 @ (k6_relat_1 @ X1)) @ X0)
% 0.48/0.66           = (k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 0.48/0.66      inference('demod', [status(thm)], ['45', '55'])).
% 0.48/0.66  thf('57', plain,
% 0.48/0.66      (![X0 : $i, X1 : $i]:
% 0.48/0.66         (((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 0.48/0.66            = (k8_relat_1 @ X1 @ 
% 0.48/0.66               (k8_relat_1 @ X0 @ 
% 0.48/0.66                (k6_relat_1 @ 
% 0.48/0.66                 (k1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))))))
% 0.48/0.66          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 0.48/0.66      inference('sup+', [status(thm)], ['10', '56'])).
% 0.48/0.66  thf('58', plain,
% 0.48/0.66      (![X0 : $i, X1 : $i]:
% 0.48/0.66         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.48/0.66           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.48/0.66      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.48/0.66  thf(t90_relat_1, axiom,
% 0.48/0.66    (![A:$i,B:$i]:
% 0.48/0.66     ( ( v1_relat_1 @ B ) =>
% 0.48/0.66       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 0.48/0.66         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.48/0.66  thf('59', plain,
% 0.48/0.66      (![X53 : $i, X54 : $i]:
% 0.48/0.66         (((k1_relat_1 @ (k7_relat_1 @ X53 @ X54))
% 0.48/0.66            = (k3_xboole_0 @ (k1_relat_1 @ X53) @ X54))
% 0.48/0.66          | ~ (v1_relat_1 @ X53))),
% 0.48/0.66      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.48/0.66  thf('60', plain,
% 0.48/0.66      (![X29 : $i, X30 : $i]:
% 0.48/0.66         ((k1_setfam_1 @ (k2_tarski @ X29 @ X30)) = (k3_xboole_0 @ X29 @ X30))),
% 0.48/0.66      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.48/0.66  thf('61', plain,
% 0.48/0.66      (![X53 : $i, X54 : $i]:
% 0.48/0.66         (((k1_relat_1 @ (k7_relat_1 @ X53 @ X54))
% 0.48/0.66            = (k1_setfam_1 @ (k2_tarski @ (k1_relat_1 @ X53) @ X54)))
% 0.48/0.66          | ~ (v1_relat_1 @ X53))),
% 0.48/0.66      inference('demod', [status(thm)], ['59', '60'])).
% 0.48/0.66  thf('62', plain,
% 0.48/0.66      (![X0 : $i, X1 : $i]:
% 0.48/0.66         (((k1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.48/0.66            = (k1_setfam_1 @ 
% 0.48/0.66               (k2_tarski @ (k1_relat_1 @ (k6_relat_1 @ X1)) @ X0)))
% 0.48/0.66          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.48/0.66      inference('sup+', [status(thm)], ['58', '61'])).
% 0.48/0.66  thf('63', plain, (![X47 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X47)) = (X47))),
% 0.48/0.66      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.48/0.66  thf('64', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 0.48/0.66      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.48/0.66  thf('65', plain,
% 0.48/0.66      (![X0 : $i, X1 : $i]:
% 0.48/0.66         ((k1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.48/0.66           = (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))),
% 0.48/0.66      inference('demod', [status(thm)], ['62', '63', '64'])).
% 0.48/0.66  thf('66', plain,
% 0.48/0.66      (![X0 : $i, X1 : $i]:
% 0.48/0.66         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.48/0.66           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.48/0.66      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.48/0.66  thf('67', plain,
% 0.48/0.66      (![X55 : $i, X56 : $i]:
% 0.48/0.66         (((k7_relat_1 @ X56 @ X55) = (k5_relat_1 @ (k6_relat_1 @ X55) @ X56))
% 0.48/0.66          | ~ (v1_relat_1 @ X56))),
% 0.48/0.66      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.48/0.66  thf(t44_relat_1, axiom,
% 0.48/0.66    (![A:$i]:
% 0.48/0.66     ( ( v1_relat_1 @ A ) =>
% 0.48/0.66       ( ![B:$i]:
% 0.48/0.66         ( ( v1_relat_1 @ B ) =>
% 0.48/0.66           ( r1_tarski @
% 0.48/0.66             ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) ))).
% 0.48/0.66  thf('68', plain,
% 0.48/0.66      (![X42 : $i, X43 : $i]:
% 0.48/0.66         (~ (v1_relat_1 @ X42)
% 0.48/0.66          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X43 @ X42)) @ 
% 0.48/0.66             (k1_relat_1 @ X43))
% 0.48/0.66          | ~ (v1_relat_1 @ X43))),
% 0.48/0.66      inference('cnf', [status(esa)], [t44_relat_1])).
% 0.48/0.66  thf('69', plain,
% 0.48/0.66      (![X0 : $i, X1 : $i]:
% 0.48/0.66         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ 
% 0.48/0.66           (k1_relat_1 @ (k6_relat_1 @ X0)))
% 0.48/0.66          | ~ (v1_relat_1 @ X1)
% 0.48/0.66          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.48/0.66          | ~ (v1_relat_1 @ X1))),
% 0.48/0.66      inference('sup+', [status(thm)], ['67', '68'])).
% 0.48/0.66  thf('70', plain, (![X47 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X47)) = (X47))),
% 0.48/0.66      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.48/0.66  thf('71', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 0.48/0.66      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.48/0.66  thf('72', plain,
% 0.48/0.66      (![X0 : $i, X1 : $i]:
% 0.48/0.66         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X0)
% 0.48/0.66          | ~ (v1_relat_1 @ X1)
% 0.48/0.66          | ~ (v1_relat_1 @ X1))),
% 0.48/0.66      inference('demod', [status(thm)], ['69', '70', '71'])).
% 0.48/0.66  thf('73', plain,
% 0.48/0.66      (![X0 : $i, X1 : $i]:
% 0.48/0.66         (~ (v1_relat_1 @ X1)
% 0.48/0.66          | (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X0))),
% 0.48/0.66      inference('simplify', [status(thm)], ['72'])).
% 0.48/0.66  thf('74', plain,
% 0.48/0.66      (![X0 : $i, X1 : $i]:
% 0.48/0.66         ((r1_tarski @ (k1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ 
% 0.48/0.66           X0)
% 0.48/0.66          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.48/0.66      inference('sup+', [status(thm)], ['66', '73'])).
% 0.48/0.66  thf('75', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 0.48/0.66      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.48/0.66  thf('76', plain,
% 0.48/0.66      (![X0 : $i, X1 : $i]:
% 0.48/0.66         (r1_tarski @ (k1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ X0)),
% 0.48/0.66      inference('demod', [status(thm)], ['74', '75'])).
% 0.48/0.66  thf('77', plain,
% 0.48/0.66      (![X0 : $i, X1 : $i]:
% 0.48/0.66         ((k1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.48/0.66           = (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))),
% 0.48/0.66      inference('demod', [status(thm)], ['62', '63', '64'])).
% 0.48/0.66  thf('78', plain,
% 0.48/0.66      (![X0 : $i, X1 : $i]:
% 0.48/0.66         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X0)),
% 0.48/0.66      inference('demod', [status(thm)], ['76', '77'])).
% 0.48/0.66  thf('79', plain, (![X48 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X48)) = (X48))),
% 0.48/0.66      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.48/0.66  thf(t79_relat_1, axiom,
% 0.48/0.66    (![A:$i,B:$i]:
% 0.48/0.66     ( ( v1_relat_1 @ B ) =>
% 0.48/0.66       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.48/0.66         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 0.48/0.66  thf('80', plain,
% 0.48/0.66      (![X50 : $i, X51 : $i]:
% 0.48/0.66         (~ (r1_tarski @ (k2_relat_1 @ X50) @ X51)
% 0.48/0.66          | ((k5_relat_1 @ X50 @ (k6_relat_1 @ X51)) = (X50))
% 0.48/0.66          | ~ (v1_relat_1 @ X50))),
% 0.48/0.66      inference('cnf', [status(esa)], [t79_relat_1])).
% 0.48/0.66  thf('81', plain,
% 0.48/0.66      (![X0 : $i, X1 : $i]:
% 0.48/0.66         (~ (r1_tarski @ X0 @ X1)
% 0.48/0.66          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.48/0.66          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 0.48/0.66              = (k6_relat_1 @ X0)))),
% 0.48/0.66      inference('sup-', [status(thm)], ['79', '80'])).
% 0.48/0.66  thf('82', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 0.48/0.66      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.48/0.66  thf('83', plain,
% 0.48/0.66      (![X0 : $i, X1 : $i]:
% 0.48/0.66         (~ (r1_tarski @ X0 @ X1)
% 0.48/0.66          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 0.48/0.66              = (k6_relat_1 @ X0)))),
% 0.48/0.66      inference('demod', [status(thm)], ['81', '82'])).
% 0.48/0.66  thf('84', plain,
% 0.48/0.66      (![X0 : $i, X1 : $i]:
% 0.48/0.66         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 0.48/0.66           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.48/0.66      inference('sup+', [status(thm)], ['21', '32'])).
% 0.48/0.66  thf('85', plain,
% 0.48/0.66      (![X0 : $i, X1 : $i]:
% 0.48/0.66         (~ (r1_tarski @ X0 @ X1)
% 0.48/0.66          | ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0)))),
% 0.48/0.66      inference('demod', [status(thm)], ['83', '84'])).
% 0.48/0.66  thf('86', plain,
% 0.48/0.66      (![X0 : $i, X1 : $i]:
% 0.48/0.66         ((k8_relat_1 @ X0 @ 
% 0.48/0.66           (k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))
% 0.48/0.66           = (k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 0.48/0.66      inference('sup-', [status(thm)], ['78', '85'])).
% 0.48/0.66  thf('87', plain,
% 0.48/0.66      (![X37 : $i, X38 : $i]:
% 0.48/0.66         (((k8_relat_1 @ X38 @ X37) = (k5_relat_1 @ X37 @ (k6_relat_1 @ X38)))
% 0.48/0.66          | ~ (v1_relat_1 @ X37))),
% 0.48/0.66      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.48/0.66  thf(t17_xboole_1, axiom,
% 0.48/0.66    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.48/0.66  thf('88', plain,
% 0.48/0.66      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.48/0.66      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.48/0.66  thf('89', plain,
% 0.48/0.66      (![X29 : $i, X30 : $i]:
% 0.48/0.66         ((k1_setfam_1 @ (k2_tarski @ X29 @ X30)) = (k3_xboole_0 @ X29 @ X30))),
% 0.48/0.66      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.48/0.66  thf('90', plain,
% 0.48/0.66      (![X0 : $i, X1 : $i]:
% 0.48/0.66         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)) @ X0)),
% 0.48/0.66      inference('demod', [status(thm)], ['88', '89'])).
% 0.48/0.66  thf('91', plain,
% 0.48/0.66      (![X0 : $i, X1 : $i]:
% 0.48/0.66         (~ (r1_tarski @ X0 @ X1)
% 0.48/0.66          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 0.48/0.66              = (k6_relat_1 @ X0)))),
% 0.48/0.66      inference('demod', [status(thm)], ['81', '82'])).
% 0.48/0.66  thf('92', plain,
% 0.48/0.66      (![X0 : $i, X1 : $i]:
% 0.48/0.66         ((k5_relat_1 @ (k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))) @ 
% 0.48/0.66           (k6_relat_1 @ X0))
% 0.48/0.66           = (k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))))),
% 0.48/0.66      inference('sup-', [status(thm)], ['90', '91'])).
% 0.48/0.66  thf('93', plain,
% 0.48/0.66      (![X0 : $i, X1 : $i]:
% 0.48/0.66         (((k8_relat_1 @ X1 @ 
% 0.48/0.66            (k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))
% 0.48/0.66            = (k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))
% 0.48/0.66          | ~ (v1_relat_1 @ 
% 0.48/0.66               (k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))))),
% 0.48/0.66      inference('sup+', [status(thm)], ['87', '92'])).
% 0.48/0.66  thf('94', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 0.48/0.66      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.48/0.66  thf('95', plain,
% 0.48/0.66      (![X0 : $i, X1 : $i]:
% 0.48/0.66         ((k8_relat_1 @ X1 @ 
% 0.48/0.66           (k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))
% 0.48/0.66           = (k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 0.48/0.66      inference('demod', [status(thm)], ['93', '94'])).
% 0.48/0.66  thf('96', plain,
% 0.48/0.66      (![X0 : $i, X1 : $i]:
% 0.48/0.66         (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.48/0.66      inference('demod', [status(thm)], ['53', '54'])).
% 0.48/0.66  thf('97', plain,
% 0.48/0.66      (![X0 : $i, X1 : $i]:
% 0.48/0.66         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 0.48/0.66           = (k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 0.48/0.66      inference('demod', [status(thm)], ['57', '65', '86', '95', '96'])).
% 0.48/0.66  thf('98', plain,
% 0.48/0.66      (((k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B)))
% 0.48/0.66         != (k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B))))),
% 0.48/0.66      inference('demod', [status(thm)], ['6', '97'])).
% 0.48/0.66  thf('99', plain, ($false), inference('simplify', [status(thm)], ['98'])).
% 0.48/0.66  
% 0.48/0.66  % SZS output end Refutation
% 0.48/0.66  
% 0.48/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
