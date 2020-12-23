%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JFCcOOvb1t

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:04 EST 2020

% Result     : Theorem 3.59s
% Output     : Refutation 3.59s
% Verified   : 
% Statistics : Number of formulae       :  236 (4530 expanded)
%              Number of leaves         :   27 (1635 expanded)
%              Depth                    :   23
%              Number of atoms          : 2312 (37500 expanded)
%              Number of equality atoms :  169 (2724 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

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

thf('2',plain,
    ( ( ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ sk_B ) )
     != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('3',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('4',plain,(
    ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ sk_B ) )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('6',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k8_relat_1 @ X38 @ X37 )
        = ( k5_relat_1 @ X37 @ ( k6_relat_1 @ X38 ) ) )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('7',plain,(
    ! [X58: $i,X59: $i] :
      ( ( ( k7_relat_1 @ X59 @ X58 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X58 ) @ X59 ) )
      | ~ ( v1_relat_1 @ X59 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('10',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('12',plain,(
    ! [X56: $i,X57: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X56 @ X57 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X56 ) @ X57 ) )
      | ~ ( v1_relat_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ ( k6_relat_1 @ X1 ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('14',plain,(
    ! [X47: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X47 ) )
      = X47 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('15',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf(t77_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B )
          = B ) ) ) )).

thf('17',plain,(
    ! [X51: $i,X52: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X51 ) @ X52 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X52 ) @ X51 )
        = X51 )
      | ~ ( v1_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t77_relat_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('20',plain,(
    ! [X58: $i,X59: $i] :
      ( ( ( k7_relat_1 @ X59 @ X58 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X58 ) @ X59 ) )
      | ~ ( v1_relat_1 @ X59 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('21',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( v1_relat_1 @ X31 )
      | ~ ( v1_relat_1 @ X32 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X31 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['19','25'])).

thf('27',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['18','28'])).

thf('30',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k8_relat_1 @ X38 @ X37 )
        = ( k5_relat_1 @ X37 @ ( k6_relat_1 @ X38 ) ) )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('31',plain,(
    ! [X48: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X48 ) )
      = X48 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('32',plain,(
    ! [X55: $i] :
      ( ( ( k5_relat_1 @ X55 @ ( k6_relat_1 @ ( k2_relat_1 @ X55 ) ) )
        = X55 )
      | ~ ( v1_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('36',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( v1_relat_1 @ X44 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X45 @ X44 ) @ X46 )
        = ( k5_relat_1 @ X45 @ ( k5_relat_1 @ X44 @ X46 ) ) )
      | ~ ( v1_relat_1 @ X46 )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('39',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['30','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf(t139_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( k8_relat_1 @ A @ ( k5_relat_1 @ B @ C ) )
            = ( k5_relat_1 @ B @ ( k8_relat_1 @ A @ C ) ) ) ) ) )).

thf('43',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( v1_relat_1 @ X39 )
      | ( ( k8_relat_1 @ X41 @ ( k5_relat_1 @ X40 @ X39 ) )
        = ( k5_relat_1 @ X40 @ ( k8_relat_1 @ X41 @ X39 ) ) )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t139_relat_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('46',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('49',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['41','47','48','49'])).

thf('51',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( v1_relat_1 @ X39 )
      | ( ( k8_relat_1 @ X41 @ ( k5_relat_1 @ X40 @ X39 ) )
        = ( k5_relat_1 @ X40 @ ( k8_relat_1 @ X41 @ X39 ) ) )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t139_relat_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k8_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('54',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k8_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( ( k8_relat_1 @ X1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X2 ) ) )
        = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['29','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['5','56'])).

thf('58',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k8_relat_1 @ X38 @ X37 )
        = ( k5_relat_1 @ X37 @ ( k6_relat_1 @ X38 ) ) )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t76_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B )
        & ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ) )).

thf('59',plain,(
    ! [X49: $i,X50: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X49 @ ( k6_relat_1 @ X50 ) ) @ X49 )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t76_relat_1])).

thf('60',plain,(
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

thf('61',plain,(
    ! [X53: $i,X54: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X53 ) @ X54 )
      | ( ( k5_relat_1 @ X53 @ ( k6_relat_1 @ X54 ) )
        = X53 )
      | ~ ( v1_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['41','47','48','49'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) )
        = ( k6_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['59','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k6_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) )
        = ( k3_xboole_0 @ X1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X47: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X47 ) )
      = X47 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
        = ( k3_xboole_0 @ X1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
        = ( k3_xboole_0 @ X0 @ ( k8_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['58','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
        = ( k3_xboole_0 @ X0 @ ( k8_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) @ ( k6_relat_1 @ X1 ) )
        = ( k3_xboole_0 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['57','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['41','47','48','49'])).

thf(t112_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( k7_relat_1 @ ( k5_relat_1 @ B @ C ) @ A )
            = ( k5_relat_1 @ ( k7_relat_1 @ B @ A ) @ C ) ) ) ) )).

thf('76',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( v1_relat_1 @ X34 )
      | ( ( k7_relat_1 @ ( k5_relat_1 @ X35 @ X34 ) @ X36 )
        = ( k5_relat_1 @ ( k7_relat_1 @ X35 @ X36 ) @ X34 ) )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t112_relat_1])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X2 )
        = ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ ( k6_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('79',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('80',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X2 )
      = ( k5_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X2 ) ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['77','78','79','80'])).

thf('82',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k8_relat_1 @ X38 @ X37 )
        = ( k5_relat_1 @ X37 @ ( k6_relat_1 @ X38 ) ) )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X2 )
      = ( k5_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X2 ) ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['77','78','79','80'])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k8_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) @ X0 )
        = ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k8_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) @ X0 )
      = ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k8_relat_1 @ X1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X2 ) ) )
      = ( k5_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X2 ) ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['81','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['5','56'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['5','56'])).

thf('90',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k8_relat_1 @ X38 @ X37 )
        = ( k5_relat_1 @ X37 @ ( k6_relat_1 @ X38 ) ) )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('91',plain,(
    ! [X49: $i,X50: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X49 @ ( k6_relat_1 @ X50 ) ) @ X49 )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t76_relat_1])).

thf('92',plain,(
    ! [X47: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X47 ) )
      = X47 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('93',plain,(
    ! [X51: $i,X52: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X51 ) @ X52 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X52 ) @ X51 )
        = X51 )
      | ~ ( v1_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t77_relat_1])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) )
        = ( k6_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['91','96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) )
        = ( k6_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['90','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) )
        = ( k6_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['41','47','48','49'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k8_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X47: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X47 ) )
      = X47 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k8_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k8_relat_1 @ X1 @ X0 ) @ X0 )
        = ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
        = ( k5_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) @ ( k6_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['89','105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k8_relat_1 @ X1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X2 ) ) )
      = ( k5_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X2 ) ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['81','86'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['5','56'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['106','107','108','109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['74','87','88','110','111'])).

thf('113',plain,(
    ! [X55: $i] :
      ( ( ( k5_relat_1 @ X55 @ ( k6_relat_1 @ ( k2_relat_1 @ X55 ) ) )
        = X55 )
      | ~ ( v1_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('114',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k8_relat_1 @ X38 @ X37 )
        = ( k5_relat_1 @ X37 @ ( k6_relat_1 @ X38 ) ) )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( ( k8_relat_1 @ ( k2_relat_1 @ X0 ) @ X0 )
        = X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k8_relat_1 @ ( k2_relat_1 @ X0 ) @ X0 )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['115'])).

thf('117',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k8_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) @ X0 )
      = ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('118',plain,(
    ! [X56: $i,X57: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X56 @ X57 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X56 ) @ X57 ) )
      | ~ ( v1_relat_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('119',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_relat_1 @ ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ ( k8_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('122',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_relat_1 @ ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['119','120','121'])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k3_xboole_0 @ ( k3_xboole_0 @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['116','122'])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['123','124','125'])).

thf('127',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k8_relat_1 @ X38 @ X37 )
        = ( k5_relat_1 @ X37 @ ( k6_relat_1 @ X38 ) ) )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
        = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['127','130'])).

thf('132',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('135',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['133','134'])).

thf('136',plain,(
    ! [X47: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X47 ) )
      = X47 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ X1 ) @ X0 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['126','137'])).

thf('139',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['123','124','125'])).

thf('140',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('141',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_relat_1 @ ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['119','120','121'])).

thf('142',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_relat_1 @ ( k8_relat_1 @ X2 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['140','141'])).

thf('143',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('144',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['142','143'])).

thf('145',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['138','139','144'])).

thf('146',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['112','145'])).

thf('147',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['123','124','125'])).

thf('148',plain,(
    ! [X58: $i,X59: $i] :
      ( ( ( k7_relat_1 @ X59 @ X58 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X58 ) @ X59 ) )
      | ~ ( v1_relat_1 @ X59 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('149',plain,(
    ! [X48: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X48 ) )
      = X48 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('150',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( v1_relat_1 @ X42 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X43 @ X42 ) ) @ ( k2_relat_1 @ X42 ) )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf('151',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['149','150'])).

thf('152',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('153',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['151','152'])).

thf('154',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['148','153'])).

thf('155',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('156',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('157',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('158',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ X1 ) ),
    inference(demod,[status(thm)],['154','155','156','157'])).

thf('159',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('160',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['41','47','48','49'])).

thf('161',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['159','160'])).

thf('162',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ ( k2_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k2_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['158','161'])).

thf('163',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('164',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) )
      = ( k3_xboole_0 @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['162','163'])).

thf('165',plain,(
    ! [X47: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X47 ) )
      = X47 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('166',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k3_xboole_0 @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ X1 ) ) ),
    inference(demod,[status(thm)],['164','165'])).

thf('167',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['147','166'])).

thf('168',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['142','143'])).

thf('169',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ ( k3_xboole_0 @ X0 @ X2 ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['167','168'])).

thf('170',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['142','143'])).

thf('171',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ ( k3_xboole_0 @ X0 @ X2 ) )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['169','170'])).

thf('172',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['146','171'])).

thf('173',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['5','56'])).

thf('174',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('175',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( v1_relat_1 @ X42 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X43 @ X42 ) ) @ ( k2_relat_1 @ X42 ) )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf('176',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['174','175'])).

thf('177',plain,(
    ! [X48: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X48 ) )
      = X48 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('178',plain,(
    ! [X48: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X48 ) )
      = X48 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('179',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('180',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('181',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(demod,[status(thm)],['176','177','178','179','180'])).

thf('182',plain,(
    ! [X51: $i,X52: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X51 ) @ X52 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X52 ) @ X51 )
        = X51 )
      | ~ ( v1_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t77_relat_1])).

thf('183',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['181','182'])).

thf('184',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( v1_relat_1 @ X39 )
      | ( ( k8_relat_1 @ X41 @ ( k5_relat_1 @ X40 @ X39 ) )
        = ( k5_relat_1 @ X40 @ ( k8_relat_1 @ X41 @ X39 ) ) )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t139_relat_1])).

thf('185',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ X1 @ X0 )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ ( k8_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['183','184'])).

thf('186',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('187',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ X1 @ X0 )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ ( k8_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['185','186'])).

thf('188',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k8_relat_1 @ X1 @ X0 )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ ( k8_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['187'])).

thf('189',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ X1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ) @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['173','188'])).

thf('190',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['5','56'])).

thf('191',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('192',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k8_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('193',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('194',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('195',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['189','190','191','192','193','194'])).

thf('196',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k8_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['172','195'])).

thf('197',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['74','87','88','110','111'])).

thf('198',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['189','190','191','192','193','194'])).

thf('199',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('200',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k8_relat_1 @ X38 @ X37 )
        = ( k5_relat_1 @ X37 @ ( k6_relat_1 @ X38 ) ) )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('201',plain,(
    ! [X0: $i] :
      ( ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['199','200'])).

thf('202',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('203',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['201','202'])).

thf('204',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['196','197','198','203'])).

thf('205',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['74','87','88','110','111'])).

thf('206',plain,(
    ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ sk_B ) )
 != ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','204','205'])).

thf('207',plain,(
    $false ),
    inference(simplify,[status(thm)],['206'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JFCcOOvb1t
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:03:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 3.59/3.81  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.59/3.81  % Solved by: fo/fo7.sh
% 3.59/3.81  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.59/3.81  % done 3256 iterations in 3.354s
% 3.59/3.81  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.59/3.81  % SZS output start Refutation
% 3.59/3.81  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.59/3.81  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.59/3.81  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 3.59/3.81  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 3.59/3.81  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 3.59/3.81  thf(sk_B_type, type, sk_B: $i).
% 3.59/3.81  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 3.59/3.81  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.59/3.81  thf(sk_A_type, type, sk_A: $i).
% 3.59/3.81  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 3.59/3.81  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.59/3.81  thf(t123_relat_1, axiom,
% 3.59/3.81    (![A:$i,B:$i]:
% 3.59/3.81     ( ( v1_relat_1 @ B ) =>
% 3.59/3.81       ( ( k8_relat_1 @ A @ B ) = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ))).
% 3.59/3.81  thf('0', plain,
% 3.59/3.81      (![X37 : $i, X38 : $i]:
% 3.59/3.81         (((k8_relat_1 @ X38 @ X37) = (k5_relat_1 @ X37 @ (k6_relat_1 @ X38)))
% 3.59/3.81          | ~ (v1_relat_1 @ X37))),
% 3.59/3.81      inference('cnf', [status(esa)], [t123_relat_1])).
% 3.59/3.81  thf(t43_funct_1, conjecture,
% 3.59/3.81    (![A:$i,B:$i]:
% 3.59/3.81     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 3.59/3.81       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 3.59/3.81  thf(zf_stmt_0, negated_conjecture,
% 3.59/3.81    (~( ![A:$i,B:$i]:
% 3.59/3.81        ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 3.59/3.81          ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 3.59/3.81    inference('cnf.neg', [status(esa)], [t43_funct_1])).
% 3.59/3.81  thf('1', plain,
% 3.59/3.81      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A))
% 3.59/3.81         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 3.59/3.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.59/3.81  thf('2', plain,
% 3.59/3.81      ((((k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B))
% 3.59/3.81          != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))
% 3.59/3.81        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_B)))),
% 3.59/3.81      inference('sup-', [status(thm)], ['0', '1'])).
% 3.59/3.81  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 3.59/3.81  thf('3', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 3.59/3.81      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 3.59/3.81  thf('4', plain,
% 3.59/3.81      (((k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B))
% 3.59/3.81         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 3.59/3.81      inference('demod', [status(thm)], ['2', '3'])).
% 3.59/3.81  thf(t17_xboole_1, axiom,
% 3.59/3.81    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 3.59/3.81  thf('5', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 3.59/3.81      inference('cnf', [status(esa)], [t17_xboole_1])).
% 3.59/3.81  thf('6', plain,
% 3.59/3.81      (![X37 : $i, X38 : $i]:
% 3.59/3.81         (((k8_relat_1 @ X38 @ X37) = (k5_relat_1 @ X37 @ (k6_relat_1 @ X38)))
% 3.59/3.81          | ~ (v1_relat_1 @ X37))),
% 3.59/3.81      inference('cnf', [status(esa)], [t123_relat_1])).
% 3.59/3.81  thf(t94_relat_1, axiom,
% 3.59/3.81    (![A:$i,B:$i]:
% 3.59/3.81     ( ( v1_relat_1 @ B ) =>
% 3.59/3.81       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 3.59/3.81  thf('7', plain,
% 3.59/3.81      (![X58 : $i, X59 : $i]:
% 3.59/3.81         (((k7_relat_1 @ X59 @ X58) = (k5_relat_1 @ (k6_relat_1 @ X58) @ X59))
% 3.59/3.81          | ~ (v1_relat_1 @ X59))),
% 3.59/3.81      inference('cnf', [status(esa)], [t94_relat_1])).
% 3.59/3.81  thf('8', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         (((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 3.59/3.81            = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 3.59/3.81          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 3.59/3.81          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 3.59/3.81      inference('sup+', [status(thm)], ['6', '7'])).
% 3.59/3.81  thf('9', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 3.59/3.81      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 3.59/3.81  thf('10', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 3.59/3.81      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 3.59/3.81  thf('11', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 3.59/3.81           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 3.59/3.81      inference('demod', [status(thm)], ['8', '9', '10'])).
% 3.59/3.81  thf(t90_relat_1, axiom,
% 3.59/3.81    (![A:$i,B:$i]:
% 3.59/3.81     ( ( v1_relat_1 @ B ) =>
% 3.59/3.81       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 3.59/3.81         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 3.59/3.81  thf('12', plain,
% 3.59/3.81      (![X56 : $i, X57 : $i]:
% 3.59/3.81         (((k1_relat_1 @ (k7_relat_1 @ X56 @ X57))
% 3.59/3.81            = (k3_xboole_0 @ (k1_relat_1 @ X56) @ X57))
% 3.59/3.81          | ~ (v1_relat_1 @ X56))),
% 3.59/3.81      inference('cnf', [status(esa)], [t90_relat_1])).
% 3.59/3.81  thf('13', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         (((k1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 3.59/3.81            = (k3_xboole_0 @ (k1_relat_1 @ (k6_relat_1 @ X1)) @ X0))
% 3.59/3.81          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 3.59/3.81      inference('sup+', [status(thm)], ['11', '12'])).
% 3.59/3.81  thf(t71_relat_1, axiom,
% 3.59/3.81    (![A:$i]:
% 3.59/3.81     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 3.59/3.81       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 3.59/3.81  thf('14', plain, (![X47 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X47)) = (X47))),
% 3.59/3.81      inference('cnf', [status(esa)], [t71_relat_1])).
% 3.59/3.81  thf('15', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 3.59/3.81      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 3.59/3.81  thf('16', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         ((k1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 3.59/3.81           = (k3_xboole_0 @ X1 @ X0))),
% 3.59/3.81      inference('demod', [status(thm)], ['13', '14', '15'])).
% 3.59/3.81  thf(t77_relat_1, axiom,
% 3.59/3.81    (![A:$i,B:$i]:
% 3.59/3.81     ( ( v1_relat_1 @ B ) =>
% 3.59/3.81       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 3.59/3.81         ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ) ))).
% 3.59/3.81  thf('17', plain,
% 3.59/3.81      (![X51 : $i, X52 : $i]:
% 3.59/3.81         (~ (r1_tarski @ (k1_relat_1 @ X51) @ X52)
% 3.59/3.81          | ((k5_relat_1 @ (k6_relat_1 @ X52) @ X51) = (X51))
% 3.59/3.81          | ~ (v1_relat_1 @ X51))),
% 3.59/3.81      inference('cnf', [status(esa)], [t77_relat_1])).
% 3.59/3.81  thf('18', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.59/3.81         (~ (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 3.59/3.81          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 3.59/3.81          | ((k5_relat_1 @ (k6_relat_1 @ X2) @ 
% 3.59/3.81              (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 3.59/3.81              = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 3.59/3.81      inference('sup-', [status(thm)], ['16', '17'])).
% 3.59/3.81  thf('19', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 3.59/3.81           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 3.59/3.81      inference('demod', [status(thm)], ['8', '9', '10'])).
% 3.59/3.81  thf('20', plain,
% 3.59/3.81      (![X58 : $i, X59 : $i]:
% 3.59/3.81         (((k7_relat_1 @ X59 @ X58) = (k5_relat_1 @ (k6_relat_1 @ X58) @ X59))
% 3.59/3.81          | ~ (v1_relat_1 @ X59))),
% 3.59/3.81      inference('cnf', [status(esa)], [t94_relat_1])).
% 3.59/3.81  thf(dt_k5_relat_1, axiom,
% 3.59/3.81    (![A:$i,B:$i]:
% 3.59/3.81     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 3.59/3.81       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 3.59/3.81  thf('21', plain,
% 3.59/3.81      (![X31 : $i, X32 : $i]:
% 3.59/3.81         (~ (v1_relat_1 @ X31)
% 3.59/3.81          | ~ (v1_relat_1 @ X32)
% 3.59/3.81          | (v1_relat_1 @ (k5_relat_1 @ X31 @ X32)))),
% 3.59/3.81      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 3.59/3.81  thf('22', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         ((v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 3.59/3.81          | ~ (v1_relat_1 @ X1)
% 3.59/3.81          | ~ (v1_relat_1 @ X1)
% 3.59/3.81          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 3.59/3.81      inference('sup+', [status(thm)], ['20', '21'])).
% 3.59/3.81  thf('23', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 3.59/3.81      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 3.59/3.81  thf('24', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         ((v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 3.59/3.81          | ~ (v1_relat_1 @ X1)
% 3.59/3.81          | ~ (v1_relat_1 @ X1))),
% 3.59/3.81      inference('demod', [status(thm)], ['22', '23'])).
% 3.59/3.81  thf('25', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         (~ (v1_relat_1 @ X1) | (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 3.59/3.81      inference('simplify', [status(thm)], ['24'])).
% 3.59/3.81  thf('26', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         ((v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 3.59/3.81          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 3.59/3.81      inference('sup+', [status(thm)], ['19', '25'])).
% 3.59/3.81  thf('27', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 3.59/3.81      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 3.59/3.81  thf('28', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 3.59/3.81      inference('demod', [status(thm)], ['26', '27'])).
% 3.59/3.81  thf('29', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.59/3.81         (~ (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 3.59/3.81          | ((k5_relat_1 @ (k6_relat_1 @ X2) @ 
% 3.59/3.81              (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 3.59/3.81              = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 3.59/3.81      inference('demod', [status(thm)], ['18', '28'])).
% 3.59/3.81  thf('30', plain,
% 3.59/3.81      (![X37 : $i, X38 : $i]:
% 3.59/3.81         (((k8_relat_1 @ X38 @ X37) = (k5_relat_1 @ X37 @ (k6_relat_1 @ X38)))
% 3.59/3.81          | ~ (v1_relat_1 @ X37))),
% 3.59/3.81      inference('cnf', [status(esa)], [t123_relat_1])).
% 3.59/3.81  thf('31', plain, (![X48 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X48)) = (X48))),
% 3.59/3.81      inference('cnf', [status(esa)], [t71_relat_1])).
% 3.59/3.81  thf(t80_relat_1, axiom,
% 3.59/3.81    (![A:$i]:
% 3.59/3.81     ( ( v1_relat_1 @ A ) =>
% 3.59/3.81       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 3.59/3.81  thf('32', plain,
% 3.59/3.81      (![X55 : $i]:
% 3.59/3.81         (((k5_relat_1 @ X55 @ (k6_relat_1 @ (k2_relat_1 @ X55))) = (X55))
% 3.59/3.81          | ~ (v1_relat_1 @ X55))),
% 3.59/3.81      inference('cnf', [status(esa)], [t80_relat_1])).
% 3.59/3.81  thf('33', plain,
% 3.59/3.81      (![X0 : $i]:
% 3.59/3.81         (((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 3.59/3.81            = (k6_relat_1 @ X0))
% 3.59/3.81          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 3.59/3.81      inference('sup+', [status(thm)], ['31', '32'])).
% 3.59/3.81  thf('34', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 3.59/3.81      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 3.59/3.81  thf('35', plain,
% 3.59/3.81      (![X0 : $i]:
% 3.59/3.81         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 3.59/3.81           = (k6_relat_1 @ X0))),
% 3.59/3.81      inference('demod', [status(thm)], ['33', '34'])).
% 3.59/3.81  thf(t55_relat_1, axiom,
% 3.59/3.81    (![A:$i]:
% 3.59/3.81     ( ( v1_relat_1 @ A ) =>
% 3.59/3.81       ( ![B:$i]:
% 3.59/3.81         ( ( v1_relat_1 @ B ) =>
% 3.59/3.81           ( ![C:$i]:
% 3.59/3.81             ( ( v1_relat_1 @ C ) =>
% 3.59/3.81               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 3.59/3.81                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 3.59/3.81  thf('36', plain,
% 3.59/3.81      (![X44 : $i, X45 : $i, X46 : $i]:
% 3.59/3.81         (~ (v1_relat_1 @ X44)
% 3.59/3.81          | ((k5_relat_1 @ (k5_relat_1 @ X45 @ X44) @ X46)
% 3.59/3.81              = (k5_relat_1 @ X45 @ (k5_relat_1 @ X44 @ X46)))
% 3.59/3.81          | ~ (v1_relat_1 @ X46)
% 3.59/3.81          | ~ (v1_relat_1 @ X45))),
% 3.59/3.81      inference('cnf', [status(esa)], [t55_relat_1])).
% 3.59/3.81  thf('37', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         (((k5_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 3.59/3.81            = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 3.59/3.81               (k5_relat_1 @ (k6_relat_1 @ X0) @ X1)))
% 3.59/3.81          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 3.59/3.81          | ~ (v1_relat_1 @ X1)
% 3.59/3.81          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 3.59/3.81      inference('sup+', [status(thm)], ['35', '36'])).
% 3.59/3.81  thf('38', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 3.59/3.81      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 3.59/3.81  thf('39', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 3.59/3.81      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 3.59/3.81  thf('40', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         (((k5_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 3.59/3.81            = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 3.59/3.81               (k5_relat_1 @ (k6_relat_1 @ X0) @ X1)))
% 3.59/3.81          | ~ (v1_relat_1 @ X1))),
% 3.59/3.81      inference('demod', [status(thm)], ['37', '38', '39'])).
% 3.59/3.81  thf('41', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         (((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 3.59/3.81            = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 3.59/3.81               (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))
% 3.59/3.81          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 3.59/3.81          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 3.59/3.81      inference('sup+', [status(thm)], ['30', '40'])).
% 3.59/3.81  thf('42', plain,
% 3.59/3.81      (![X0 : $i]:
% 3.59/3.81         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 3.59/3.81           = (k6_relat_1 @ X0))),
% 3.59/3.81      inference('demod', [status(thm)], ['33', '34'])).
% 3.59/3.81  thf(t139_relat_1, axiom,
% 3.59/3.81    (![A:$i,B:$i]:
% 3.59/3.81     ( ( v1_relat_1 @ B ) =>
% 3.59/3.81       ( ![C:$i]:
% 3.59/3.81         ( ( v1_relat_1 @ C ) =>
% 3.59/3.81           ( ( k8_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) =
% 3.59/3.81             ( k5_relat_1 @ B @ ( k8_relat_1 @ A @ C ) ) ) ) ) ))).
% 3.59/3.81  thf('43', plain,
% 3.59/3.81      (![X39 : $i, X40 : $i, X41 : $i]:
% 3.59/3.81         (~ (v1_relat_1 @ X39)
% 3.59/3.81          | ((k8_relat_1 @ X41 @ (k5_relat_1 @ X40 @ X39))
% 3.59/3.81              = (k5_relat_1 @ X40 @ (k8_relat_1 @ X41 @ X39)))
% 3.59/3.81          | ~ (v1_relat_1 @ X40))),
% 3.59/3.81      inference('cnf', [status(esa)], [t139_relat_1])).
% 3.59/3.81  thf('44', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         (((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 3.59/3.81            = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 3.59/3.81               (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))
% 3.59/3.81          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 3.59/3.81          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 3.59/3.81      inference('sup+', [status(thm)], ['42', '43'])).
% 3.59/3.81  thf('45', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 3.59/3.81      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 3.59/3.81  thf('46', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 3.59/3.81      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 3.59/3.81  thf('47', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 3.59/3.81           = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 3.59/3.81              (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 3.59/3.81      inference('demod', [status(thm)], ['44', '45', '46'])).
% 3.59/3.81  thf('48', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 3.59/3.81      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 3.59/3.81  thf('49', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 3.59/3.81      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 3.59/3.81  thf('50', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 3.59/3.81           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 3.59/3.81      inference('demod', [status(thm)], ['41', '47', '48', '49'])).
% 3.59/3.81  thf('51', plain,
% 3.59/3.81      (![X39 : $i, X40 : $i, X41 : $i]:
% 3.59/3.81         (~ (v1_relat_1 @ X39)
% 3.59/3.81          | ((k8_relat_1 @ X41 @ (k5_relat_1 @ X40 @ X39))
% 3.59/3.81              = (k5_relat_1 @ X40 @ (k8_relat_1 @ X41 @ X39)))
% 3.59/3.81          | ~ (v1_relat_1 @ X40))),
% 3.59/3.81      inference('cnf', [status(esa)], [t139_relat_1])).
% 3.59/3.81  thf('52', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.59/3.81         (((k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 3.59/3.81            = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 3.59/3.81               (k8_relat_1 @ X2 @ (k6_relat_1 @ X1))))
% 3.59/3.81          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 3.59/3.81          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 3.59/3.81      inference('sup+', [status(thm)], ['50', '51'])).
% 3.59/3.81  thf('53', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 3.59/3.81      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 3.59/3.81  thf('54', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 3.59/3.81      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 3.59/3.81  thf('55', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.59/3.81         ((k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 3.59/3.81           = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 3.59/3.81              (k8_relat_1 @ X2 @ (k6_relat_1 @ X1))))),
% 3.59/3.81      inference('demod', [status(thm)], ['52', '53', '54'])).
% 3.59/3.81  thf('56', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.59/3.81         (~ (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 3.59/3.81          | ((k8_relat_1 @ X1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X2)))
% 3.59/3.81              = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 3.59/3.81      inference('demod', [status(thm)], ['29', '55'])).
% 3.59/3.81  thf('57', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         ((k8_relat_1 @ X0 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 3.59/3.81           = (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))),
% 3.59/3.81      inference('sup-', [status(thm)], ['5', '56'])).
% 3.59/3.81  thf('58', plain,
% 3.59/3.81      (![X37 : $i, X38 : $i]:
% 3.59/3.81         (((k8_relat_1 @ X38 @ X37) = (k5_relat_1 @ X37 @ (k6_relat_1 @ X38)))
% 3.59/3.81          | ~ (v1_relat_1 @ X37))),
% 3.59/3.81      inference('cnf', [status(esa)], [t123_relat_1])).
% 3.59/3.81  thf(t76_relat_1, axiom,
% 3.59/3.81    (![A:$i,B:$i]:
% 3.59/3.81     ( ( v1_relat_1 @ B ) =>
% 3.59/3.81       ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B ) & 
% 3.59/3.81         ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ))).
% 3.59/3.81  thf('59', plain,
% 3.59/3.81      (![X49 : $i, X50 : $i]:
% 3.59/3.81         ((r1_tarski @ (k5_relat_1 @ X49 @ (k6_relat_1 @ X50)) @ X49)
% 3.59/3.81          | ~ (v1_relat_1 @ X49))),
% 3.59/3.81      inference('cnf', [status(esa)], [t76_relat_1])).
% 3.59/3.81  thf('60', plain, (![X48 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X48)) = (X48))),
% 3.59/3.81      inference('cnf', [status(esa)], [t71_relat_1])).
% 3.59/3.81  thf(t79_relat_1, axiom,
% 3.59/3.81    (![A:$i,B:$i]:
% 3.59/3.81     ( ( v1_relat_1 @ B ) =>
% 3.59/3.81       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 3.59/3.81         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 3.59/3.81  thf('61', plain,
% 3.59/3.81      (![X53 : $i, X54 : $i]:
% 3.59/3.81         (~ (r1_tarski @ (k2_relat_1 @ X53) @ X54)
% 3.59/3.81          | ((k5_relat_1 @ X53 @ (k6_relat_1 @ X54)) = (X53))
% 3.59/3.81          | ~ (v1_relat_1 @ X53))),
% 3.59/3.81      inference('cnf', [status(esa)], [t79_relat_1])).
% 3.59/3.81  thf('62', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         (~ (r1_tarski @ X0 @ X1)
% 3.59/3.81          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 3.59/3.81          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 3.59/3.81              = (k6_relat_1 @ X0)))),
% 3.59/3.81      inference('sup-', [status(thm)], ['60', '61'])).
% 3.59/3.81  thf('63', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 3.59/3.81      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 3.59/3.81  thf('64', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         (~ (r1_tarski @ X0 @ X1)
% 3.59/3.81          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 3.59/3.81              = (k6_relat_1 @ X0)))),
% 3.59/3.81      inference('demod', [status(thm)], ['62', '63'])).
% 3.59/3.81  thf('65', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 3.59/3.81           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 3.59/3.81      inference('demod', [status(thm)], ['41', '47', '48', '49'])).
% 3.59/3.81  thf('66', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         (~ (r1_tarski @ X0 @ X1)
% 3.59/3.81          | ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0)))),
% 3.59/3.81      inference('demod', [status(thm)], ['64', '65'])).
% 3.59/3.81  thf('67', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         (~ (v1_relat_1 @ X0)
% 3.59/3.81          | ((k8_relat_1 @ X0 @ 
% 3.59/3.81              (k6_relat_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1))))
% 3.59/3.81              = (k6_relat_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)))))),
% 3.59/3.81      inference('sup-', [status(thm)], ['59', '66'])).
% 3.59/3.81  thf('68', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         ((k1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 3.59/3.81           = (k3_xboole_0 @ X1 @ X0))),
% 3.59/3.81      inference('demod', [status(thm)], ['13', '14', '15'])).
% 3.59/3.81  thf('69', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         (((k1_relat_1 @ (k6_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))))
% 3.59/3.81            = (k3_xboole_0 @ X1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))))
% 3.59/3.81          | ~ (v1_relat_1 @ X1))),
% 3.59/3.81      inference('sup+', [status(thm)], ['67', '68'])).
% 3.59/3.81  thf('70', plain, (![X47 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X47)) = (X47))),
% 3.59/3.81      inference('cnf', [status(esa)], [t71_relat_1])).
% 3.59/3.81  thf('71', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         (((k5_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 3.59/3.81            = (k3_xboole_0 @ X1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))))
% 3.59/3.81          | ~ (v1_relat_1 @ X1))),
% 3.59/3.81      inference('demod', [status(thm)], ['69', '70'])).
% 3.59/3.81  thf('72', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         (((k5_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 3.59/3.81            = (k3_xboole_0 @ X0 @ (k8_relat_1 @ X1 @ X0)))
% 3.59/3.81          | ~ (v1_relat_1 @ X0)
% 3.59/3.81          | ~ (v1_relat_1 @ X0))),
% 3.59/3.81      inference('sup+', [status(thm)], ['58', '71'])).
% 3.59/3.81  thf('73', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         (~ (v1_relat_1 @ X0)
% 3.59/3.81          | ((k5_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 3.59/3.81              = (k3_xboole_0 @ X0 @ (k8_relat_1 @ X1 @ X0))))),
% 3.59/3.81      inference('simplify', [status(thm)], ['72'])).
% 3.59/3.81  thf('74', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         (((k5_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)) @ 
% 3.59/3.81            (k6_relat_1 @ X1))
% 3.59/3.81            = (k3_xboole_0 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)) @ 
% 3.59/3.81               (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))
% 3.59/3.81          | ~ (v1_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1))))),
% 3.59/3.81      inference('sup+', [status(thm)], ['57', '73'])).
% 3.59/3.81  thf('75', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 3.59/3.81           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 3.59/3.81      inference('demod', [status(thm)], ['41', '47', '48', '49'])).
% 3.59/3.81  thf(t112_relat_1, axiom,
% 3.59/3.81    (![A:$i,B:$i]:
% 3.59/3.81     ( ( v1_relat_1 @ B ) =>
% 3.59/3.81       ( ![C:$i]:
% 3.59/3.81         ( ( v1_relat_1 @ C ) =>
% 3.59/3.81           ( ( k7_relat_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 3.59/3.81             ( k5_relat_1 @ ( k7_relat_1 @ B @ A ) @ C ) ) ) ) ))).
% 3.59/3.81  thf('76', plain,
% 3.59/3.81      (![X34 : $i, X35 : $i, X36 : $i]:
% 3.59/3.81         (~ (v1_relat_1 @ X34)
% 3.59/3.81          | ((k7_relat_1 @ (k5_relat_1 @ X35 @ X34) @ X36)
% 3.59/3.81              = (k5_relat_1 @ (k7_relat_1 @ X35 @ X36) @ X34))
% 3.59/3.81          | ~ (v1_relat_1 @ X35))),
% 3.59/3.81      inference('cnf', [status(esa)], [t112_relat_1])).
% 3.59/3.81  thf('77', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.59/3.81         (((k7_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ X2)
% 3.59/3.81            = (k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X2) @ 
% 3.59/3.81               (k6_relat_1 @ X1)))
% 3.59/3.81          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 3.59/3.81          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 3.59/3.81      inference('sup+', [status(thm)], ['75', '76'])).
% 3.59/3.81  thf('78', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 3.59/3.81           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 3.59/3.81      inference('demod', [status(thm)], ['8', '9', '10'])).
% 3.59/3.81  thf('79', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 3.59/3.81      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 3.59/3.81  thf('80', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 3.59/3.81      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 3.59/3.81  thf('81', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.59/3.81         ((k7_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ X2)
% 3.59/3.81           = (k5_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X2)) @ 
% 3.59/3.81              (k6_relat_1 @ X1)))),
% 3.59/3.81      inference('demod', [status(thm)], ['77', '78', '79', '80'])).
% 3.59/3.81  thf('82', plain,
% 3.59/3.81      (![X37 : $i, X38 : $i]:
% 3.59/3.81         (((k8_relat_1 @ X38 @ X37) = (k5_relat_1 @ X37 @ (k6_relat_1 @ X38)))
% 3.59/3.81          | ~ (v1_relat_1 @ X37))),
% 3.59/3.81      inference('cnf', [status(esa)], [t123_relat_1])).
% 3.59/3.81  thf('83', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.59/3.81         ((k7_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ X2)
% 3.59/3.81           = (k5_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X2)) @ 
% 3.59/3.81              (k6_relat_1 @ X1)))),
% 3.59/3.81      inference('demod', [status(thm)], ['77', '78', '79', '80'])).
% 3.59/3.81  thf('84', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.59/3.81         (((k7_relat_1 @ (k8_relat_1 @ X2 @ (k6_relat_1 @ X1)) @ X0)
% 3.59/3.81            = (k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))
% 3.59/3.81          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 3.59/3.81      inference('sup+', [status(thm)], ['82', '83'])).
% 3.59/3.81  thf('85', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 3.59/3.81      inference('demod', [status(thm)], ['26', '27'])).
% 3.59/3.81  thf('86', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.59/3.81         ((k7_relat_1 @ (k8_relat_1 @ X2 @ (k6_relat_1 @ X1)) @ X0)
% 3.59/3.81           = (k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 3.59/3.81      inference('demod', [status(thm)], ['84', '85'])).
% 3.59/3.81  thf('87', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.59/3.81         ((k8_relat_1 @ X1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X2)))
% 3.59/3.81           = (k5_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X2)) @ 
% 3.59/3.81              (k6_relat_1 @ X1)))),
% 3.59/3.81      inference('demod', [status(thm)], ['81', '86'])).
% 3.59/3.81  thf('88', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         ((k8_relat_1 @ X0 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 3.59/3.81           = (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))),
% 3.59/3.81      inference('sup-', [status(thm)], ['5', '56'])).
% 3.59/3.81  thf('89', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         ((k8_relat_1 @ X0 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 3.59/3.81           = (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))),
% 3.59/3.81      inference('sup-', [status(thm)], ['5', '56'])).
% 3.59/3.81  thf('90', plain,
% 3.59/3.81      (![X37 : $i, X38 : $i]:
% 3.59/3.81         (((k8_relat_1 @ X38 @ X37) = (k5_relat_1 @ X37 @ (k6_relat_1 @ X38)))
% 3.59/3.81          | ~ (v1_relat_1 @ X37))),
% 3.59/3.81      inference('cnf', [status(esa)], [t123_relat_1])).
% 3.59/3.81  thf('91', plain,
% 3.59/3.81      (![X49 : $i, X50 : $i]:
% 3.59/3.81         ((r1_tarski @ (k5_relat_1 @ X49 @ (k6_relat_1 @ X50)) @ X49)
% 3.59/3.81          | ~ (v1_relat_1 @ X49))),
% 3.59/3.81      inference('cnf', [status(esa)], [t76_relat_1])).
% 3.59/3.81  thf('92', plain, (![X47 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X47)) = (X47))),
% 3.59/3.81      inference('cnf', [status(esa)], [t71_relat_1])).
% 3.59/3.81  thf('93', plain,
% 3.59/3.81      (![X51 : $i, X52 : $i]:
% 3.59/3.81         (~ (r1_tarski @ (k1_relat_1 @ X51) @ X52)
% 3.59/3.81          | ((k5_relat_1 @ (k6_relat_1 @ X52) @ X51) = (X51))
% 3.59/3.81          | ~ (v1_relat_1 @ X51))),
% 3.59/3.81      inference('cnf', [status(esa)], [t77_relat_1])).
% 3.59/3.81  thf('94', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         (~ (r1_tarski @ X0 @ X1)
% 3.59/3.81          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 3.59/3.81          | ((k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 3.59/3.81              = (k6_relat_1 @ X0)))),
% 3.59/3.81      inference('sup-', [status(thm)], ['92', '93'])).
% 3.59/3.81  thf('95', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 3.59/3.81      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 3.59/3.81  thf('96', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         (~ (r1_tarski @ X0 @ X1)
% 3.59/3.81          | ((k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 3.59/3.81              = (k6_relat_1 @ X0)))),
% 3.59/3.81      inference('demod', [status(thm)], ['94', '95'])).
% 3.59/3.81  thf('97', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         (~ (v1_relat_1 @ X0)
% 3.59/3.81          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 3.59/3.81              (k6_relat_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1))))
% 3.59/3.81              = (k6_relat_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)))))),
% 3.59/3.81      inference('sup-', [status(thm)], ['91', '96'])).
% 3.59/3.81  thf('98', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         (((k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 3.59/3.81            (k6_relat_1 @ (k8_relat_1 @ X1 @ X0)))
% 3.59/3.81            = (k6_relat_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1))))
% 3.59/3.81          | ~ (v1_relat_1 @ X0)
% 3.59/3.81          | ~ (v1_relat_1 @ X0))),
% 3.59/3.81      inference('sup+', [status(thm)], ['90', '97'])).
% 3.59/3.81  thf('99', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         (~ (v1_relat_1 @ X0)
% 3.59/3.81          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 3.59/3.81              (k6_relat_1 @ (k8_relat_1 @ X1 @ X0)))
% 3.59/3.81              = (k6_relat_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)))))),
% 3.59/3.81      inference('simplify', [status(thm)], ['98'])).
% 3.59/3.81  thf('100', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 3.59/3.81           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 3.59/3.81      inference('demod', [status(thm)], ['41', '47', '48', '49'])).
% 3.59/3.81  thf('101', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         (~ (v1_relat_1 @ X0)
% 3.59/3.81          | ((k8_relat_1 @ (k8_relat_1 @ X1 @ X0) @ (k6_relat_1 @ X0))
% 3.59/3.81              = (k6_relat_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)))))),
% 3.59/3.81      inference('demod', [status(thm)], ['99', '100'])).
% 3.59/3.81  thf('102', plain, (![X47 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X47)) = (X47))),
% 3.59/3.81      inference('cnf', [status(esa)], [t71_relat_1])).
% 3.59/3.81  thf('103', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         (((k1_relat_1 @ 
% 3.59/3.81            (k8_relat_1 @ (k8_relat_1 @ X1 @ X0) @ (k6_relat_1 @ X0)))
% 3.59/3.81            = (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 3.59/3.81          | ~ (v1_relat_1 @ X0))),
% 3.59/3.81      inference('sup+', [status(thm)], ['101', '102'])).
% 3.59/3.81  thf('104', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         ((k1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 3.59/3.81           = (k3_xboole_0 @ X1 @ X0))),
% 3.59/3.81      inference('demod', [status(thm)], ['13', '14', '15'])).
% 3.59/3.81  thf('105', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         (((k3_xboole_0 @ (k8_relat_1 @ X1 @ X0) @ X0)
% 3.59/3.81            = (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 3.59/3.81          | ~ (v1_relat_1 @ X0))),
% 3.59/3.81      inference('demod', [status(thm)], ['103', '104'])).
% 3.59/3.81  thf('106', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         (((k3_xboole_0 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ 
% 3.59/3.81            (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 3.59/3.81            = (k5_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)) @ 
% 3.59/3.81               (k6_relat_1 @ X1)))
% 3.59/3.81          | ~ (v1_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1))))),
% 3.59/3.81      inference('sup+', [status(thm)], ['89', '105'])).
% 3.59/3.81  thf('107', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.59/3.81         ((k8_relat_1 @ X1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X2)))
% 3.59/3.81           = (k5_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X2)) @ 
% 3.59/3.81              (k6_relat_1 @ X1)))),
% 3.59/3.81      inference('demod', [status(thm)], ['81', '86'])).
% 3.59/3.81  thf('108', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         ((k8_relat_1 @ X0 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 3.59/3.81           = (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))),
% 3.59/3.81      inference('sup-', [status(thm)], ['5', '56'])).
% 3.59/3.81  thf('109', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 3.59/3.81      inference('demod', [status(thm)], ['26', '27'])).
% 3.59/3.81  thf('110', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         ((k3_xboole_0 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ 
% 3.59/3.81           (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 3.59/3.81           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 3.59/3.81      inference('demod', [status(thm)], ['106', '107', '108', '109'])).
% 3.59/3.81  thf('111', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 3.59/3.81      inference('demod', [status(thm)], ['26', '27'])).
% 3.59/3.81  thf('112', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 3.59/3.81           = (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))),
% 3.59/3.81      inference('demod', [status(thm)], ['74', '87', '88', '110', '111'])).
% 3.59/3.81  thf('113', plain,
% 3.59/3.81      (![X55 : $i]:
% 3.59/3.81         (((k5_relat_1 @ X55 @ (k6_relat_1 @ (k2_relat_1 @ X55))) = (X55))
% 3.59/3.81          | ~ (v1_relat_1 @ X55))),
% 3.59/3.81      inference('cnf', [status(esa)], [t80_relat_1])).
% 3.59/3.81  thf('114', plain,
% 3.59/3.81      (![X37 : $i, X38 : $i]:
% 3.59/3.81         (((k8_relat_1 @ X38 @ X37) = (k5_relat_1 @ X37 @ (k6_relat_1 @ X38)))
% 3.59/3.81          | ~ (v1_relat_1 @ X37))),
% 3.59/3.81      inference('cnf', [status(esa)], [t123_relat_1])).
% 3.59/3.81  thf('115', plain,
% 3.59/3.81      (![X0 : $i]:
% 3.59/3.81         (((k8_relat_1 @ (k2_relat_1 @ X0) @ X0) = (X0))
% 3.59/3.81          | ~ (v1_relat_1 @ X0)
% 3.59/3.81          | ~ (v1_relat_1 @ X0))),
% 3.59/3.81      inference('sup+', [status(thm)], ['113', '114'])).
% 3.59/3.81  thf('116', plain,
% 3.59/3.81      (![X0 : $i]:
% 3.59/3.81         (~ (v1_relat_1 @ X0) | ((k8_relat_1 @ (k2_relat_1 @ X0) @ X0) = (X0)))),
% 3.59/3.81      inference('simplify', [status(thm)], ['115'])).
% 3.59/3.81  thf('117', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.59/3.81         ((k7_relat_1 @ (k8_relat_1 @ X2 @ (k6_relat_1 @ X1)) @ X0)
% 3.59/3.81           = (k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 3.59/3.81      inference('demod', [status(thm)], ['84', '85'])).
% 3.59/3.81  thf('118', plain,
% 3.59/3.81      (![X56 : $i, X57 : $i]:
% 3.59/3.81         (((k1_relat_1 @ (k7_relat_1 @ X56 @ X57))
% 3.59/3.81            = (k3_xboole_0 @ (k1_relat_1 @ X56) @ X57))
% 3.59/3.81          | ~ (v1_relat_1 @ X56))),
% 3.59/3.81      inference('cnf', [status(esa)], [t90_relat_1])).
% 3.59/3.81  thf('119', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.59/3.81         (((k1_relat_1 @ 
% 3.59/3.81            (k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))
% 3.59/3.81            = (k3_xboole_0 @ 
% 3.59/3.81               (k1_relat_1 @ (k8_relat_1 @ X2 @ (k6_relat_1 @ X1))) @ X0))
% 3.59/3.81          | ~ (v1_relat_1 @ (k8_relat_1 @ X2 @ (k6_relat_1 @ X1))))),
% 3.59/3.81      inference('sup+', [status(thm)], ['117', '118'])).
% 3.59/3.81  thf('120', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         ((k1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 3.59/3.81           = (k3_xboole_0 @ X1 @ X0))),
% 3.59/3.81      inference('demod', [status(thm)], ['13', '14', '15'])).
% 3.59/3.81  thf('121', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 3.59/3.81      inference('demod', [status(thm)], ['26', '27'])).
% 3.59/3.81  thf('122', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.59/3.81         ((k1_relat_1 @ 
% 3.59/3.81           (k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))
% 3.59/3.81           = (k3_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0))),
% 3.59/3.81      inference('demod', [status(thm)], ['119', '120', '121'])).
% 3.59/3.81  thf('123', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         (((k1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 3.59/3.81            = (k3_xboole_0 @ 
% 3.59/3.81               (k3_xboole_0 @ 
% 3.59/3.81                (k2_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ X1) @ 
% 3.59/3.81               X0))
% 3.59/3.81          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 3.59/3.81      inference('sup+', [status(thm)], ['116', '122'])).
% 3.59/3.81  thf('124', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         ((k1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 3.59/3.81           = (k3_xboole_0 @ X1 @ X0))),
% 3.59/3.81      inference('demod', [status(thm)], ['13', '14', '15'])).
% 3.59/3.81  thf('125', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 3.59/3.81      inference('demod', [status(thm)], ['26', '27'])).
% 3.59/3.81  thf('126', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         ((k3_xboole_0 @ X1 @ X0)
% 3.59/3.81           = (k3_xboole_0 @ 
% 3.59/3.81              (k3_xboole_0 @ 
% 3.59/3.81               (k2_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ X1) @ 
% 3.59/3.81              X0))),
% 3.59/3.81      inference('demod', [status(thm)], ['123', '124', '125'])).
% 3.59/3.81  thf('127', plain,
% 3.59/3.81      (![X37 : $i, X38 : $i]:
% 3.59/3.81         (((k8_relat_1 @ X38 @ X37) = (k5_relat_1 @ X37 @ (k6_relat_1 @ X38)))
% 3.59/3.81          | ~ (v1_relat_1 @ X37))),
% 3.59/3.81      inference('cnf', [status(esa)], [t123_relat_1])).
% 3.59/3.81  thf('128', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 3.59/3.81      inference('cnf', [status(esa)], [t17_xboole_1])).
% 3.59/3.81  thf('129', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         (~ (r1_tarski @ X0 @ X1)
% 3.59/3.81          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 3.59/3.81              = (k6_relat_1 @ X0)))),
% 3.59/3.81      inference('demod', [status(thm)], ['62', '63'])).
% 3.59/3.81  thf('130', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         ((k5_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 3.59/3.81           (k6_relat_1 @ X0)) = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 3.59/3.81      inference('sup-', [status(thm)], ['128', '129'])).
% 3.59/3.81  thf('131', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         (((k8_relat_1 @ X1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 3.59/3.81            = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 3.59/3.81          | ~ (v1_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))),
% 3.59/3.81      inference('sup+', [status(thm)], ['127', '130'])).
% 3.59/3.81  thf('132', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 3.59/3.81      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 3.59/3.81  thf('133', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         ((k8_relat_1 @ X1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 3.59/3.81           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 3.59/3.81      inference('demod', [status(thm)], ['131', '132'])).
% 3.59/3.81  thf('134', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         ((k1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 3.59/3.81           = (k3_xboole_0 @ X1 @ X0))),
% 3.59/3.81      inference('demod', [status(thm)], ['13', '14', '15'])).
% 3.59/3.81  thf('135', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         ((k1_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 3.59/3.81           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 3.59/3.81      inference('sup+', [status(thm)], ['133', '134'])).
% 3.59/3.81  thf('136', plain, (![X47 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X47)) = (X47))),
% 3.59/3.81      inference('cnf', [status(esa)], [t71_relat_1])).
% 3.59/3.81  thf('137', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         ((k3_xboole_0 @ X1 @ X0)
% 3.59/3.81           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 3.59/3.81      inference('demod', [status(thm)], ['135', '136'])).
% 3.59/3.81  thf('138', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         ((k3_xboole_0 @ 
% 3.59/3.81           (k3_xboole_0 @ 
% 3.59/3.81            (k2_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ X1) @ 
% 3.59/3.81           X0)
% 3.59/3.81           = (k3_xboole_0 @ 
% 3.59/3.81              (k3_xboole_0 @ 
% 3.59/3.81               (k2_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ X1) @ 
% 3.59/3.81              (k3_xboole_0 @ X1 @ X0)))),
% 3.59/3.81      inference('sup+', [status(thm)], ['126', '137'])).
% 3.59/3.81  thf('139', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         ((k3_xboole_0 @ X1 @ X0)
% 3.59/3.81           = (k3_xboole_0 @ 
% 3.59/3.81              (k3_xboole_0 @ 
% 3.59/3.81               (k2_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ X1) @ 
% 3.59/3.81              X0))),
% 3.59/3.81      inference('demod', [status(thm)], ['123', '124', '125'])).
% 3.59/3.81  thf('140', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         ((k8_relat_1 @ X1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 3.59/3.81           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 3.59/3.81      inference('demod', [status(thm)], ['131', '132'])).
% 3.59/3.81  thf('141', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.59/3.81         ((k1_relat_1 @ 
% 3.59/3.81           (k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))
% 3.59/3.81           = (k3_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0))),
% 3.59/3.81      inference('demod', [status(thm)], ['119', '120', '121'])).
% 3.59/3.81  thf('142', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.59/3.81         ((k1_relat_1 @ 
% 3.59/3.81           (k8_relat_1 @ X2 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))
% 3.59/3.81           = (k3_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ (k3_xboole_0 @ X1 @ X0)))),
% 3.59/3.81      inference('sup+', [status(thm)], ['140', '141'])).
% 3.59/3.81  thf('143', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         ((k1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 3.59/3.81           = (k3_xboole_0 @ X1 @ X0))),
% 3.59/3.81      inference('demod', [status(thm)], ['13', '14', '15'])).
% 3.59/3.81  thf('144', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.59/3.81         ((k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 3.59/3.81           = (k3_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ (k3_xboole_0 @ X1 @ X0)))),
% 3.59/3.81      inference('demod', [status(thm)], ['142', '143'])).
% 3.59/3.81  thf('145', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         ((k3_xboole_0 @ X1 @ X0)
% 3.59/3.81           = (k3_xboole_0 @ 
% 3.59/3.81              (k2_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ 
% 3.59/3.81              (k3_xboole_0 @ X1 @ X0)))),
% 3.59/3.81      inference('demod', [status(thm)], ['138', '139', '144'])).
% 3.59/3.81  thf('146', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         ((k3_xboole_0 @ X0 @ X1)
% 3.59/3.81           = (k3_xboole_0 @ 
% 3.59/3.81              (k2_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ 
% 3.59/3.81              (k3_xboole_0 @ X0 @ X1)))),
% 3.59/3.81      inference('sup+', [status(thm)], ['112', '145'])).
% 3.59/3.81  thf('147', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         ((k3_xboole_0 @ X1 @ X0)
% 3.59/3.81           = (k3_xboole_0 @ 
% 3.59/3.81              (k3_xboole_0 @ 
% 3.59/3.81               (k2_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ X1) @ 
% 3.59/3.81              X0))),
% 3.59/3.81      inference('demod', [status(thm)], ['123', '124', '125'])).
% 3.59/3.81  thf('148', plain,
% 3.59/3.81      (![X58 : $i, X59 : $i]:
% 3.59/3.81         (((k7_relat_1 @ X59 @ X58) = (k5_relat_1 @ (k6_relat_1 @ X58) @ X59))
% 3.59/3.81          | ~ (v1_relat_1 @ X59))),
% 3.59/3.81      inference('cnf', [status(esa)], [t94_relat_1])).
% 3.59/3.81  thf('149', plain, (![X48 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X48)) = (X48))),
% 3.59/3.81      inference('cnf', [status(esa)], [t71_relat_1])).
% 3.59/3.81  thf(t45_relat_1, axiom,
% 3.59/3.81    (![A:$i]:
% 3.59/3.81     ( ( v1_relat_1 @ A ) =>
% 3.59/3.81       ( ![B:$i]:
% 3.59/3.81         ( ( v1_relat_1 @ B ) =>
% 3.59/3.81           ( r1_tarski @
% 3.59/3.81             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 3.59/3.81  thf('150', plain,
% 3.59/3.81      (![X42 : $i, X43 : $i]:
% 3.59/3.81         (~ (v1_relat_1 @ X42)
% 3.59/3.81          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X43 @ X42)) @ 
% 3.59/3.81             (k2_relat_1 @ X42))
% 3.59/3.81          | ~ (v1_relat_1 @ X43))),
% 3.59/3.81      inference('cnf', [status(esa)], [t45_relat_1])).
% 3.59/3.81  thf('151', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ 
% 3.59/3.81           X0)
% 3.59/3.81          | ~ (v1_relat_1 @ X1)
% 3.59/3.81          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 3.59/3.81      inference('sup+', [status(thm)], ['149', '150'])).
% 3.59/3.81  thf('152', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 3.59/3.81      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 3.59/3.81  thf('153', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ 
% 3.59/3.81           X0)
% 3.59/3.81          | ~ (v1_relat_1 @ X1))),
% 3.59/3.81      inference('demod', [status(thm)], ['151', '152'])).
% 3.59/3.81  thf('154', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         ((r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)) @ 
% 3.59/3.81           X1)
% 3.59/3.81          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 3.59/3.81          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 3.59/3.81      inference('sup+', [status(thm)], ['148', '153'])).
% 3.59/3.81  thf('155', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 3.59/3.81           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 3.59/3.81      inference('demod', [status(thm)], ['8', '9', '10'])).
% 3.59/3.81  thf('156', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 3.59/3.81      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 3.59/3.81  thf('157', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 3.59/3.81      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 3.59/3.81  thf('158', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         (r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ X1)),
% 3.59/3.81      inference('demod', [status(thm)], ['154', '155', '156', '157'])).
% 3.59/3.81  thf('159', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         (~ (r1_tarski @ X0 @ X1)
% 3.59/3.81          | ((k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 3.59/3.81              = (k6_relat_1 @ X0)))),
% 3.59/3.81      inference('demod', [status(thm)], ['94', '95'])).
% 3.59/3.81  thf('160', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 3.59/3.81           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 3.59/3.81      inference('demod', [status(thm)], ['41', '47', '48', '49'])).
% 3.59/3.81  thf('161', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         (~ (r1_tarski @ X0 @ X1)
% 3.59/3.81          | ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1)) = (k6_relat_1 @ X0)))),
% 3.59/3.81      inference('demod', [status(thm)], ['159', '160'])).
% 3.59/3.81  thf('162', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         ((k8_relat_1 @ (k2_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1))) @ 
% 3.59/3.81           (k6_relat_1 @ X0))
% 3.59/3.81           = (k6_relat_1 @ (k2_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))))),
% 3.59/3.81      inference('sup-', [status(thm)], ['158', '161'])).
% 3.59/3.81  thf('163', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         ((k1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 3.59/3.81           = (k3_xboole_0 @ X1 @ X0))),
% 3.59/3.81      inference('demod', [status(thm)], ['13', '14', '15'])).
% 3.59/3.81  thf('164', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         ((k1_relat_1 @ 
% 3.59/3.81           (k6_relat_1 @ (k2_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))))
% 3.59/3.81           = (k3_xboole_0 @ 
% 3.59/3.81              (k2_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ X1))),
% 3.59/3.81      inference('sup+', [status(thm)], ['162', '163'])).
% 3.59/3.81  thf('165', plain, (![X47 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X47)) = (X47))),
% 3.59/3.81      inference('cnf', [status(esa)], [t71_relat_1])).
% 3.59/3.81  thf('166', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         ((k2_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 3.59/3.81           = (k3_xboole_0 @ 
% 3.59/3.81              (k2_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ X1))),
% 3.59/3.81      inference('demod', [status(thm)], ['164', '165'])).
% 3.59/3.81  thf('167', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         ((k3_xboole_0 @ X1 @ X0)
% 3.59/3.81           = (k3_xboole_0 @ 
% 3.59/3.81              (k2_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ X0))),
% 3.59/3.81      inference('demod', [status(thm)], ['147', '166'])).
% 3.59/3.81  thf('168', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.59/3.81         ((k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 3.59/3.81           = (k3_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ (k3_xboole_0 @ X1 @ X0)))),
% 3.59/3.81      inference('demod', [status(thm)], ['142', '143'])).
% 3.59/3.81  thf('169', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.59/3.81         ((k3_xboole_0 @ 
% 3.59/3.81           (k2_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ 
% 3.59/3.81           (k3_xboole_0 @ X0 @ X2))
% 3.59/3.81           = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X2)))),
% 3.59/3.81      inference('sup+', [status(thm)], ['167', '168'])).
% 3.59/3.81  thf('170', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.59/3.81         ((k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 3.59/3.81           = (k3_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ (k3_xboole_0 @ X1 @ X0)))),
% 3.59/3.81      inference('demod', [status(thm)], ['142', '143'])).
% 3.59/3.81  thf('171', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.59/3.81         ((k3_xboole_0 @ 
% 3.59/3.81           (k2_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ 
% 3.59/3.81           (k3_xboole_0 @ X0 @ X2))
% 3.59/3.81           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X2)))),
% 3.59/3.81      inference('demod', [status(thm)], ['169', '170'])).
% 3.59/3.81  thf('172', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         ((k3_xboole_0 @ X0 @ X1)
% 3.59/3.81           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1)))),
% 3.59/3.81      inference('demod', [status(thm)], ['146', '171'])).
% 3.59/3.81  thf('173', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         ((k8_relat_1 @ X0 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 3.59/3.81           = (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))),
% 3.59/3.81      inference('sup-', [status(thm)], ['5', '56'])).
% 3.59/3.81  thf('174', plain,
% 3.59/3.81      (![X0 : $i]:
% 3.59/3.81         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 3.59/3.81           = (k6_relat_1 @ X0))),
% 3.59/3.81      inference('demod', [status(thm)], ['33', '34'])).
% 3.59/3.81  thf('175', plain,
% 3.59/3.81      (![X42 : $i, X43 : $i]:
% 3.59/3.81         (~ (v1_relat_1 @ X42)
% 3.59/3.81          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X43 @ X42)) @ 
% 3.59/3.81             (k2_relat_1 @ X42))
% 3.59/3.81          | ~ (v1_relat_1 @ X43))),
% 3.59/3.81      inference('cnf', [status(esa)], [t45_relat_1])).
% 3.59/3.81  thf('176', plain,
% 3.59/3.81      (![X0 : $i]:
% 3.59/3.81         ((r1_tarski @ (k2_relat_1 @ (k6_relat_1 @ X0)) @ 
% 3.59/3.81           (k2_relat_1 @ (k6_relat_1 @ X0)))
% 3.59/3.81          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 3.59/3.81          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 3.59/3.81      inference('sup+', [status(thm)], ['174', '175'])).
% 3.59/3.81  thf('177', plain, (![X48 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X48)) = (X48))),
% 3.59/3.81      inference('cnf', [status(esa)], [t71_relat_1])).
% 3.59/3.81  thf('178', plain, (![X48 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X48)) = (X48))),
% 3.59/3.81      inference('cnf', [status(esa)], [t71_relat_1])).
% 3.59/3.81  thf('179', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 3.59/3.81      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 3.59/3.81  thf('180', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 3.59/3.81      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 3.59/3.81  thf('181', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 3.59/3.81      inference('demod', [status(thm)], ['176', '177', '178', '179', '180'])).
% 3.59/3.81  thf('182', plain,
% 3.59/3.81      (![X51 : $i, X52 : $i]:
% 3.59/3.81         (~ (r1_tarski @ (k1_relat_1 @ X51) @ X52)
% 3.59/3.81          | ((k5_relat_1 @ (k6_relat_1 @ X52) @ X51) = (X51))
% 3.59/3.81          | ~ (v1_relat_1 @ X51))),
% 3.59/3.81      inference('cnf', [status(esa)], [t77_relat_1])).
% 3.59/3.81  thf('183', plain,
% 3.59/3.81      (![X0 : $i]:
% 3.59/3.81         (~ (v1_relat_1 @ X0)
% 3.59/3.81          | ((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X0) = (X0)))),
% 3.59/3.81      inference('sup-', [status(thm)], ['181', '182'])).
% 3.59/3.81  thf('184', plain,
% 3.59/3.81      (![X39 : $i, X40 : $i, X41 : $i]:
% 3.59/3.81         (~ (v1_relat_1 @ X39)
% 3.59/3.81          | ((k8_relat_1 @ X41 @ (k5_relat_1 @ X40 @ X39))
% 3.59/3.81              = (k5_relat_1 @ X40 @ (k8_relat_1 @ X41 @ X39)))
% 3.59/3.81          | ~ (v1_relat_1 @ X40))),
% 3.59/3.81      inference('cnf', [status(esa)], [t139_relat_1])).
% 3.59/3.81  thf('185', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         (((k8_relat_1 @ X1 @ X0)
% 3.59/3.81            = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ 
% 3.59/3.81               (k8_relat_1 @ X1 @ X0)))
% 3.59/3.81          | ~ (v1_relat_1 @ X0)
% 3.59/3.81          | ~ (v1_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 3.59/3.81          | ~ (v1_relat_1 @ X0))),
% 3.59/3.81      inference('sup+', [status(thm)], ['183', '184'])).
% 3.59/3.81  thf('186', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 3.59/3.81      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 3.59/3.81  thf('187', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         (((k8_relat_1 @ X1 @ X0)
% 3.59/3.81            = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ 
% 3.59/3.81               (k8_relat_1 @ X1 @ X0)))
% 3.59/3.81          | ~ (v1_relat_1 @ X0)
% 3.59/3.81          | ~ (v1_relat_1 @ X0))),
% 3.59/3.81      inference('demod', [status(thm)], ['185', '186'])).
% 3.59/3.81  thf('188', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         (~ (v1_relat_1 @ X0)
% 3.59/3.81          | ((k8_relat_1 @ X1 @ X0)
% 3.59/3.81              = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ 
% 3.59/3.81                 (k8_relat_1 @ X1 @ X0))))),
% 3.59/3.81      inference('simplify', [status(thm)], ['187'])).
% 3.59/3.81  thf('189', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         (((k8_relat_1 @ X1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 3.59/3.81            = (k5_relat_1 @ 
% 3.59/3.81               (k6_relat_1 @ 
% 3.59/3.81                (k1_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))) @ 
% 3.59/3.81               (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))
% 3.59/3.81          | ~ (v1_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1))))),
% 3.59/3.81      inference('sup+', [status(thm)], ['173', '188'])).
% 3.59/3.81  thf('190', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         ((k8_relat_1 @ X0 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 3.59/3.81           = (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))),
% 3.59/3.81      inference('sup-', [status(thm)], ['5', '56'])).
% 3.59/3.81  thf('191', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         ((k1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 3.59/3.81           = (k3_xboole_0 @ X1 @ X0))),
% 3.59/3.81      inference('demod', [status(thm)], ['13', '14', '15'])).
% 3.59/3.81  thf('192', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.59/3.81         ((k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 3.59/3.81           = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 3.59/3.81              (k8_relat_1 @ X2 @ (k6_relat_1 @ X1))))),
% 3.59/3.81      inference('demod', [status(thm)], ['52', '53', '54'])).
% 3.59/3.81  thf('193', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         ((k8_relat_1 @ X1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 3.59/3.81           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 3.59/3.81      inference('demod', [status(thm)], ['131', '132'])).
% 3.59/3.81  thf('194', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 3.59/3.81      inference('demod', [status(thm)], ['26', '27'])).
% 3.59/3.81  thf('195', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 3.59/3.81           = (k8_relat_1 @ X1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1))))),
% 3.59/3.81      inference('demod', [status(thm)],
% 3.59/3.81                ['189', '190', '191', '192', '193', '194'])).
% 3.59/3.81  thf('196', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         ((k8_relat_1 @ (k3_xboole_0 @ X1 @ X0) @ (k6_relat_1 @ X0))
% 3.59/3.81           = (k8_relat_1 @ (k3_xboole_0 @ X1 @ X0) @ 
% 3.59/3.81              (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))),
% 3.59/3.81      inference('sup+', [status(thm)], ['172', '195'])).
% 3.59/3.81  thf('197', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 3.59/3.81           = (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))),
% 3.59/3.81      inference('demod', [status(thm)], ['74', '87', '88', '110', '111'])).
% 3.59/3.81  thf('198', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 3.59/3.81           = (k8_relat_1 @ X1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1))))),
% 3.59/3.81      inference('demod', [status(thm)],
% 3.59/3.81                ['189', '190', '191', '192', '193', '194'])).
% 3.59/3.81  thf('199', plain,
% 3.59/3.81      (![X0 : $i]:
% 3.59/3.81         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 3.59/3.81           = (k6_relat_1 @ X0))),
% 3.59/3.81      inference('demod', [status(thm)], ['33', '34'])).
% 3.59/3.81  thf('200', plain,
% 3.59/3.81      (![X37 : $i, X38 : $i]:
% 3.59/3.81         (((k8_relat_1 @ X38 @ X37) = (k5_relat_1 @ X37 @ (k6_relat_1 @ X38)))
% 3.59/3.81          | ~ (v1_relat_1 @ X37))),
% 3.59/3.81      inference('cnf', [status(esa)], [t123_relat_1])).
% 3.59/3.81  thf('201', plain,
% 3.59/3.81      (![X0 : $i]:
% 3.59/3.81         (((k8_relat_1 @ X0 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0))
% 3.59/3.81          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 3.59/3.81      inference('sup+', [status(thm)], ['199', '200'])).
% 3.59/3.81  thf('202', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 3.59/3.81      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 3.59/3.81  thf('203', plain,
% 3.59/3.81      (![X0 : $i]: ((k8_relat_1 @ X0 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0))),
% 3.59/3.81      inference('demod', [status(thm)], ['201', '202'])).
% 3.59/3.81  thf('204', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 3.59/3.81           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 3.59/3.81      inference('demod', [status(thm)], ['196', '197', '198', '203'])).
% 3.59/3.81  thf('205', plain,
% 3.59/3.81      (![X0 : $i, X1 : $i]:
% 3.59/3.81         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 3.59/3.81           = (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))),
% 3.59/3.81      inference('demod', [status(thm)], ['74', '87', '88', '110', '111'])).
% 3.59/3.81  thf('206', plain,
% 3.59/3.81      (((k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B))
% 3.59/3.81         != (k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B)))),
% 3.59/3.81      inference('demod', [status(thm)], ['4', '204', '205'])).
% 3.59/3.81  thf('207', plain, ($false), inference('simplify', [status(thm)], ['206'])).
% 3.59/3.81  
% 3.59/3.81  % SZS output end Refutation
% 3.59/3.81  
% 3.59/3.82  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
