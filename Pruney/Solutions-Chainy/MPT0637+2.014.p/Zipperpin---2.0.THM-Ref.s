%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HzmW4PZvCF

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:57 EST 2020

% Result     : Theorem 43.23s
% Output     : Refutation 43.23s
% Verified   : 
% Statistics : Number of formulae       :  252 (2213 expanded)
%              Number of leaves         :   31 ( 783 expanded)
%              Depth                    :   22
%              Number of atoms          : 2291 (18420 expanded)
%              Number of equality atoms :  182 (1407 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t123_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ B )
        = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X41: $i,X42: $i] :
      ( ( ( k8_relat_1 @ X42 @ X41 )
        = ( k5_relat_1 @ X41 @ ( k6_relat_1 @ X42 ) ) )
      | ~ ( v1_relat_1 @ X41 ) ) ),
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
    ! [X37: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('4',plain,(
    ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ sk_B ) )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X41: $i,X42: $i] :
      ( ( ( k8_relat_1 @ X42 @ X41 )
        = ( k5_relat_1 @ X41 @ ( k6_relat_1 @ X42 ) ) )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('6',plain,(
    ! [X62: $i,X63: $i] :
      ( ( ( k7_relat_1 @ X63 @ X62 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X62 ) @ X63 ) )
      | ~ ( v1_relat_1 @ X63 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X37: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('9',plain,(
    ! [X37: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('11',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_tarski @ X5 @ X4 )
      = ( k2_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('12',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X33 @ X34 ) )
      = ( k3_xboole_0 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X33 @ X34 ) )
      = ( k3_xboole_0 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('16',plain,(
    ! [X60: $i,X61: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X60 @ X61 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X60 ) @ X61 ) )
      | ~ ( v1_relat_1 @ X60 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('17',plain,(
    ! [X62: $i,X63: $i] :
      ( ( ( k7_relat_1 @ X63 @ X62 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X62 ) @ X63 ) )
      | ~ ( v1_relat_1 @ X63 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('18',plain,(
    ! [X54: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X54 ) )
      = X54 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('19',plain,(
    ! [X59: $i] :
      ( ( ( k5_relat_1 @ X59 @ ( k6_relat_1 @ ( k2_relat_1 @ X59 ) ) )
        = X59 )
      | ~ ( v1_relat_1 @ X59 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X37: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('23',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( v1_relat_1 @ X48 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X49 @ X48 ) ) @ ( k2_relat_1 @ X48 ) )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X54: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X54 ) )
      = X54 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('26',plain,(
    ! [X54: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X54 ) )
      = X54 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('27',plain,(
    ! [X37: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('28',plain,(
    ! [X37: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(demod,[status(thm)],['24','25','26','27','28'])).

thf(t77_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B )
          = B ) ) ) )).

thf('30',plain,(
    ! [X57: $i,X58: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X57 ) @ X58 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X58 ) @ X57 )
        = X57 )
      | ~ ( v1_relat_1 @ X57 ) ) ),
    inference(cnf,[status(esa)],[t77_relat_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) )
        = ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','33'])).

thf('35',plain,(
    ! [X62: $i,X63: $i] :
      ( ( ( k7_relat_1 @ X63 @ X62 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X62 ) @ X63 ) )
      | ~ ( v1_relat_1 @ X63 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('36',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( v1_relat_1 @ X35 )
      | ~ ( v1_relat_1 @ X36 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X35 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X37: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) )
        = ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['34','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ ( k3_xboole_0 @ X0 @ ( k1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) )
        = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['10','42'])).

thf('44',plain,(
    ! [X53: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X53 ) )
      = X53 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('45',plain,(
    ! [X41: $i,X42: $i] :
      ( ( ( k8_relat_1 @ X42 @ X41 )
        = ( k5_relat_1 @ X41 @ ( k6_relat_1 @ X42 ) ) )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('46',plain,(
    ! [X62: $i,X63: $i] :
      ( ( ( k7_relat_1 @ X63 @ X62 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X62 ) @ X63 ) )
      | ~ ( v1_relat_1 @ X63 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t112_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( k7_relat_1 @ ( k5_relat_1 @ B @ C ) @ A )
            = ( k5_relat_1 @ ( k7_relat_1 @ B @ A ) @ C ) ) ) ) )).

thf('47',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( v1_relat_1 @ X38 )
      | ( ( k7_relat_1 @ ( k5_relat_1 @ X39 @ X38 ) @ X40 )
        = ( k5_relat_1 @ ( k7_relat_1 @ X39 @ X40 ) @ X38 ) )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t112_relat_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X37: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X2 ) ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X2 ) @ X1 ) @ X0 )
        = ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['45','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X37: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X37: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k8_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) @ X0 )
      = ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['54','55','60','61'])).

thf('63',plain,(
    ! [X41: $i,X42: $i] :
      ( ( ( k8_relat_1 @ X42 @ X41 )
        = ( k5_relat_1 @ X41 @ ( k6_relat_1 @ X42 ) ) )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('65',plain,(
    ! [X53: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X53 ) )
      = X53 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('66',plain,(
    ! [X57: $i,X58: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X57 ) @ X58 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X58 ) @ X57 )
        = X57 )
      | ~ ( v1_relat_1 @ X57 ) ) ),
    inference(cnf,[status(esa)],[t77_relat_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X37: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['64','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['63','70'])).

thf('72',plain,(
    ! [X37: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
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

thf('75',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( v1_relat_1 @ X43 )
      | ( ( k8_relat_1 @ X45 @ ( k5_relat_1 @ X44 @ X43 ) )
        = ( k5_relat_1 @ X44 @ ( k8_relat_1 @ X45 @ X43 ) ) )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t139_relat_1])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ X0 @ ( k8_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X37: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ X0 @ ( k8_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ X0 @ ( k8_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('82',plain,(
    ! [X60: $i,X61: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X60 @ X61 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X60 ) @ X61 ) )
      | ~ ( v1_relat_1 @ X60 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ ( k6_relat_1 @ X1 ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X53: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X53 ) )
      = X53 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('85',plain,(
    ! [X37: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('87',plain,(
    ! [X57: $i,X58: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X57 ) @ X58 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X58 ) @ X57 )
        = X57 )
      | ~ ( v1_relat_1 @ X57 ) ) ),
    inference(cnf,[status(esa)],[t77_relat_1])).

thf('88',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('90',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['80','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ X0 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['79','91'])).

thf('93',plain,(
    ! [X37: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X41: $i,X42: $i] :
      ( ( ( k8_relat_1 @ X42 @ X41 )
        = ( k5_relat_1 @ X41 @ ( k6_relat_1 @ X42 ) ) )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t76_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B )
        & ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ) )).

thf('96',plain,(
    ! [X55: $i,X56: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X55 @ ( k6_relat_1 @ X56 ) ) @ X55 )
      | ~ ( v1_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t76_relat_1])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('99',plain,(
    ! [X41: $i,X42: $i] :
      ( ( ( k8_relat_1 @ X42 @ X41 )
        = ( k5_relat_1 @ X41 @ ( k6_relat_1 @ X42 ) ) )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X37: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X62: $i,X63: $i] :
      ( ( ( k7_relat_1 @ X63 @ X62 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X62 ) @ X63 ) )
      | ~ ( v1_relat_1 @ X63 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('104',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( v1_relat_1 @ X43 )
      | ( ( k8_relat_1 @ X45 @ ( k5_relat_1 @ X44 @ X43 ) )
        = ( k5_relat_1 @ X44 @ ( k8_relat_1 @ X45 @ X43 ) ) )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t139_relat_1])).

thf('105',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k8_relat_1 @ X2 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k8_relat_1 @ X2 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X37: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('107',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k8_relat_1 @ X2 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k8_relat_1 @ X2 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k8_relat_1 @ X2 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k8_relat_1 @ X2 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['107'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ X0 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['102','108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('111',plain,(
    ! [X41: $i,X42: $i] :
      ( ( ( k8_relat_1 @ X42 @ X41 )
        = ( k5_relat_1 @ X41 @ ( k6_relat_1 @ X42 ) ) )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('113',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( v1_relat_1 @ X38 )
      | ( ( k7_relat_1 @ ( k5_relat_1 @ X39 @ X38 ) @ X40 )
        = ( k5_relat_1 @ ( k7_relat_1 @ X39 @ X40 ) @ X38 ) )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t112_relat_1])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X37: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('116',plain,(
    ! [X37: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['114','115','116'])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k5_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['117','118','119'])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
        = ( k8_relat_1 @ X1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['111','120'])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k8_relat_1 @ X1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X37: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['109','110','123','124'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['97','125'])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k8_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['96','126'])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k6_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) )
        = ( k3_xboole_0 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X53: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X53 ) )
      = X53 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
        = ( k3_xboole_0 @ X1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['129','130','131'])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
        = ( k3_xboole_0 @ X0 @ ( k8_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['95','132'])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
        = ( k3_xboole_0 @ X0 @ ( k8_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['133'])).

thf('135',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) @ ( k6_relat_1 @ X1 ) )
        = ( k3_xboole_0 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['94','134'])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('137',plain,(
    ! [X41: $i,X42: $i] :
      ( ( ( k8_relat_1 @ X42 @ X41 )
        = ( k5_relat_1 @ X41 @ ( k6_relat_1 @ X42 ) ) )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('138',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( v1_relat_1 @ X38 )
      | ( ( k7_relat_1 @ ( k5_relat_1 @ X39 @ X38 ) @ X40 )
        = ( k5_relat_1 @ ( k7_relat_1 @ X39 @ X40 ) @ X38 ) )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t112_relat_1])).

thf('139',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k7_relat_1 @ X0 @ X2 ) @ ( k6_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X37: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('141',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k7_relat_1 @ X0 @ X2 ) @ ( k6_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k7_relat_1 @ X0 @ X2 ) @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['141'])).

thf('143',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k8_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) @ X0 )
        = ( k5_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ ( k6_relat_1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['136','142'])).

thf('144',plain,(
    ! [X37: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('145',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k8_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) @ X0 )
      = ( k5_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ ( k6_relat_1 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['143','144'])).

thf('146',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k8_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) @ X0 )
      = ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['54','55','60','61'])).

thf('147',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k5_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ ( k6_relat_1 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['145','146'])).

thf('148',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('149',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('150',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k3_xboole_0 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['135','147','148','149'])).

thf('151',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k3_xboole_0 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['73','150'])).

thf('152',plain,(
    ! [X41: $i,X42: $i] :
      ( ( ( k8_relat_1 @ X42 @ X41 )
        = ( k5_relat_1 @ X41 @ ( k6_relat_1 @ X42 ) ) )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('153',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('154',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('155',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('156',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['154','155'])).

thf('157',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('158',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['156','157'])).

thf('159',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['153','158'])).

thf('160',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['152','159'])).

thf('161',plain,(
    ! [X37: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('162',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['160','161'])).

thf('163',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('164',plain,(
    ! [X62: $i,X63: $i] :
      ( ( ( k7_relat_1 @ X63 @ X62 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X62 ) @ X63 ) )
      | ~ ( v1_relat_1 @ X63 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('165',plain,(
    ! [X55: $i,X56: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X55 @ ( k6_relat_1 @ X56 ) ) @ X55 )
      | ~ ( v1_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t76_relat_1])).

thf('166',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['164','165'])).

thf('167',plain,(
    ! [X37: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('168',plain,(
    ! [X37: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('169',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['166','167','168'])).

thf('170',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('171',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['169','170'])).

thf('172',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['97','125'])).

thf('173',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ ( k6_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k6_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['171','172'])).

thf('174',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('175',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) )
      = ( k3_xboole_0 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['173','174'])).

thf('176',plain,(
    ! [X53: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X53 ) )
      = X53 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('177',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('178',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k3_xboole_0 @ ( k6_relat_1 @ X0 ) @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['175','176','177'])).

thf('179',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['151','162','163','178'])).

thf('180',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['151','162','163','178'])).

thf('181',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('182',plain,(
    ! [X37: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('183',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['43','44','62','179','180','181','182'])).

thf('184',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k3_xboole_0 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['135','147','148','149'])).

thf('185',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('186',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('187',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('188',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['186','187'])).

thf('189',plain,(
    ! [X53: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X53 ) )
      = X53 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('190',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('191',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['188','189','190'])).

thf('192',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['185','191'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('193',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k1_enumset1 @ X6 @ X6 @ X7 )
      = ( k2_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('194',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X33 @ X34 ) )
      = ( k3_xboole_0 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('195',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['193','194'])).

thf('196',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k1_enumset1 @ X1 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['192','195'])).

thf('197',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k1_enumset1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) )
      = ( k3_xboole_0 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['184','196'])).

thf('198',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k1_enumset1 @ X6 @ X6 @ X7 )
      = ( k2_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('199',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_tarski @ X5 @ X4 )
      = ( k2_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('200',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['198','199'])).

thf('201',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('202',plain,(
    ! [X59: $i] :
      ( ( ( k5_relat_1 @ X59 @ ( k6_relat_1 @ ( k2_relat_1 @ X59 ) ) )
        = X59 )
      | ~ ( v1_relat_1 @ X59 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('203',plain,(
    ! [X62: $i,X63: $i] :
      ( ( ( k7_relat_1 @ X63 @ X62 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X62 ) @ X63 ) )
      | ~ ( v1_relat_1 @ X63 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('204',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) ) @ X0 )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['202','203'])).

thf('205',plain,(
    ! [X54: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X54 ) )
      = X54 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('206',plain,(
    ! [X37: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('207',plain,(
    ! [X54: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X54 ) )
      = X54 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('208',plain,(
    ! [X37: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('209',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['204','205','206','207','208'])).

thf('210',plain,(
    ! [X60: $i,X61: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X60 @ X61 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X60 ) @ X61 ) )
      | ~ ( v1_relat_1 @ X60 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('211',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k6_relat_1 @ X0 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['209','210'])).

thf('212',plain,(
    ! [X53: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X53 ) )
      = X53 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('213',plain,(
    ! [X53: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X53 ) )
      = X53 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('214',plain,(
    ! [X37: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('215',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['211','212','213','214'])).

thf('216',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k3_xboole_0 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['135','147','148','149'])).

thf('217',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['197','200','201','215','216'])).

thf('218',plain,(
    ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ sk_B ) )
 != ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','183','217'])).

thf('219',plain,(
    $false ),
    inference(simplify,[status(thm)],['218'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HzmW4PZvCF
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:12:50 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 43.23/43.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 43.23/43.48  % Solved by: fo/fo7.sh
% 43.23/43.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 43.23/43.48  % done 25334 iterations in 43.022s
% 43.23/43.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 43.23/43.48  % SZS output start Refutation
% 43.23/43.48  thf(sk_A_type, type, sk_A: $i).
% 43.23/43.48  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 43.23/43.48  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 43.23/43.48  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 43.23/43.48  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 43.23/43.48  thf(sk_B_type, type, sk_B: $i).
% 43.23/43.48  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 43.23/43.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 43.23/43.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 43.23/43.48  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 43.23/43.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 43.23/43.48  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 43.23/43.48  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 43.23/43.48  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 43.23/43.48  thf(t123_relat_1, axiom,
% 43.23/43.48    (![A:$i,B:$i]:
% 43.23/43.48     ( ( v1_relat_1 @ B ) =>
% 43.23/43.48       ( ( k8_relat_1 @ A @ B ) = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ))).
% 43.23/43.48  thf('0', plain,
% 43.23/43.48      (![X41 : $i, X42 : $i]:
% 43.23/43.48         (((k8_relat_1 @ X42 @ X41) = (k5_relat_1 @ X41 @ (k6_relat_1 @ X42)))
% 43.23/43.48          | ~ (v1_relat_1 @ X41))),
% 43.23/43.48      inference('cnf', [status(esa)], [t123_relat_1])).
% 43.23/43.48  thf(t43_funct_1, conjecture,
% 43.23/43.48    (![A:$i,B:$i]:
% 43.23/43.48     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 43.23/43.48       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 43.23/43.48  thf(zf_stmt_0, negated_conjecture,
% 43.23/43.48    (~( ![A:$i,B:$i]:
% 43.23/43.48        ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 43.23/43.48          ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 43.23/43.48    inference('cnf.neg', [status(esa)], [t43_funct_1])).
% 43.23/43.48  thf('1', plain,
% 43.23/43.48      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A))
% 43.23/43.48         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 43.23/43.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.23/43.48  thf('2', plain,
% 43.23/43.48      ((((k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B))
% 43.23/43.48          != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))
% 43.23/43.48        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_B)))),
% 43.23/43.48      inference('sup-', [status(thm)], ['0', '1'])).
% 43.23/43.48  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 43.23/43.48  thf('3', plain, (![X37 : $i]: (v1_relat_1 @ (k6_relat_1 @ X37))),
% 43.23/43.48      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 43.23/43.48  thf('4', plain,
% 43.23/43.48      (((k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B))
% 43.23/43.48         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 43.23/43.48      inference('demod', [status(thm)], ['2', '3'])).
% 43.23/43.48  thf('5', plain,
% 43.23/43.48      (![X41 : $i, X42 : $i]:
% 43.23/43.48         (((k8_relat_1 @ X42 @ X41) = (k5_relat_1 @ X41 @ (k6_relat_1 @ X42)))
% 43.23/43.48          | ~ (v1_relat_1 @ X41))),
% 43.23/43.48      inference('cnf', [status(esa)], [t123_relat_1])).
% 43.23/43.48  thf(t94_relat_1, axiom,
% 43.23/43.48    (![A:$i,B:$i]:
% 43.23/43.48     ( ( v1_relat_1 @ B ) =>
% 43.23/43.48       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 43.23/43.48  thf('6', plain,
% 43.23/43.48      (![X62 : $i, X63 : $i]:
% 43.23/43.48         (((k7_relat_1 @ X63 @ X62) = (k5_relat_1 @ (k6_relat_1 @ X62) @ X63))
% 43.23/43.48          | ~ (v1_relat_1 @ X63))),
% 43.23/43.48      inference('cnf', [status(esa)], [t94_relat_1])).
% 43.23/43.48  thf('7', plain,
% 43.23/43.48      (![X0 : $i, X1 : $i]:
% 43.23/43.48         (((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 43.23/43.48            = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 43.23/43.48          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 43.23/43.48          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 43.23/43.48      inference('sup+', [status(thm)], ['5', '6'])).
% 43.23/43.48  thf('8', plain, (![X37 : $i]: (v1_relat_1 @ (k6_relat_1 @ X37))),
% 43.23/43.48      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 43.23/43.48  thf('9', plain, (![X37 : $i]: (v1_relat_1 @ (k6_relat_1 @ X37))),
% 43.23/43.48      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 43.23/43.48  thf('10', plain,
% 43.23/43.48      (![X0 : $i, X1 : $i]:
% 43.23/43.48         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 43.23/43.48           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 43.23/43.48      inference('demod', [status(thm)], ['7', '8', '9'])).
% 43.23/43.48  thf(commutativity_k2_tarski, axiom,
% 43.23/43.48    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 43.23/43.48  thf('11', plain,
% 43.23/43.48      (![X4 : $i, X5 : $i]: ((k2_tarski @ X5 @ X4) = (k2_tarski @ X4 @ X5))),
% 43.23/43.48      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 43.23/43.48  thf(t12_setfam_1, axiom,
% 43.23/43.48    (![A:$i,B:$i]:
% 43.23/43.48     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 43.23/43.48  thf('12', plain,
% 43.23/43.48      (![X33 : $i, X34 : $i]:
% 43.23/43.48         ((k1_setfam_1 @ (k2_tarski @ X33 @ X34)) = (k3_xboole_0 @ X33 @ X34))),
% 43.23/43.48      inference('cnf', [status(esa)], [t12_setfam_1])).
% 43.23/43.48  thf('13', plain,
% 43.23/43.48      (![X0 : $i, X1 : $i]:
% 43.23/43.48         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 43.23/43.48      inference('sup+', [status(thm)], ['11', '12'])).
% 43.23/43.48  thf('14', plain,
% 43.23/43.48      (![X33 : $i, X34 : $i]:
% 43.23/43.48         ((k1_setfam_1 @ (k2_tarski @ X33 @ X34)) = (k3_xboole_0 @ X33 @ X34))),
% 43.23/43.48      inference('cnf', [status(esa)], [t12_setfam_1])).
% 43.23/43.48  thf('15', plain,
% 43.23/43.48      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 43.23/43.48      inference('sup+', [status(thm)], ['13', '14'])).
% 43.23/43.48  thf(t90_relat_1, axiom,
% 43.23/43.48    (![A:$i,B:$i]:
% 43.23/43.48     ( ( v1_relat_1 @ B ) =>
% 43.23/43.48       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 43.23/43.48         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 43.23/43.48  thf('16', plain,
% 43.23/43.48      (![X60 : $i, X61 : $i]:
% 43.23/43.48         (((k1_relat_1 @ (k7_relat_1 @ X60 @ X61))
% 43.23/43.48            = (k3_xboole_0 @ (k1_relat_1 @ X60) @ X61))
% 43.23/43.48          | ~ (v1_relat_1 @ X60))),
% 43.23/43.48      inference('cnf', [status(esa)], [t90_relat_1])).
% 43.23/43.48  thf('17', plain,
% 43.23/43.48      (![X62 : $i, X63 : $i]:
% 43.23/43.48         (((k7_relat_1 @ X63 @ X62) = (k5_relat_1 @ (k6_relat_1 @ X62) @ X63))
% 43.23/43.48          | ~ (v1_relat_1 @ X63))),
% 43.23/43.48      inference('cnf', [status(esa)], [t94_relat_1])).
% 43.23/43.48  thf(t71_relat_1, axiom,
% 43.23/43.48    (![A:$i]:
% 43.23/43.48     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 43.23/43.48       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 43.23/43.48  thf('18', plain, (![X54 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X54)) = (X54))),
% 43.23/43.48      inference('cnf', [status(esa)], [t71_relat_1])).
% 43.23/43.48  thf(t80_relat_1, axiom,
% 43.23/43.48    (![A:$i]:
% 43.23/43.48     ( ( v1_relat_1 @ A ) =>
% 43.23/43.48       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 43.23/43.48  thf('19', plain,
% 43.23/43.48      (![X59 : $i]:
% 43.23/43.48         (((k5_relat_1 @ X59 @ (k6_relat_1 @ (k2_relat_1 @ X59))) = (X59))
% 43.23/43.48          | ~ (v1_relat_1 @ X59))),
% 43.23/43.48      inference('cnf', [status(esa)], [t80_relat_1])).
% 43.23/43.48  thf('20', plain,
% 43.23/43.48      (![X0 : $i]:
% 43.23/43.48         (((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 43.23/43.48            = (k6_relat_1 @ X0))
% 43.23/43.48          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 43.23/43.48      inference('sup+', [status(thm)], ['18', '19'])).
% 43.23/43.48  thf('21', plain, (![X37 : $i]: (v1_relat_1 @ (k6_relat_1 @ X37))),
% 43.23/43.48      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 43.23/43.48  thf('22', plain,
% 43.23/43.48      (![X0 : $i]:
% 43.23/43.48         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 43.23/43.48           = (k6_relat_1 @ X0))),
% 43.23/43.48      inference('demod', [status(thm)], ['20', '21'])).
% 43.23/43.48  thf(t45_relat_1, axiom,
% 43.23/43.48    (![A:$i]:
% 43.23/43.48     ( ( v1_relat_1 @ A ) =>
% 43.23/43.48       ( ![B:$i]:
% 43.23/43.48         ( ( v1_relat_1 @ B ) =>
% 43.23/43.48           ( r1_tarski @
% 43.23/43.48             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 43.23/43.48  thf('23', plain,
% 43.23/43.48      (![X48 : $i, X49 : $i]:
% 43.23/43.48         (~ (v1_relat_1 @ X48)
% 43.23/43.48          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X49 @ X48)) @ 
% 43.23/43.48             (k2_relat_1 @ X48))
% 43.23/43.48          | ~ (v1_relat_1 @ X49))),
% 43.23/43.48      inference('cnf', [status(esa)], [t45_relat_1])).
% 43.23/43.48  thf('24', plain,
% 43.23/43.48      (![X0 : $i]:
% 43.23/43.48         ((r1_tarski @ (k2_relat_1 @ (k6_relat_1 @ X0)) @ 
% 43.23/43.48           (k2_relat_1 @ (k6_relat_1 @ X0)))
% 43.23/43.48          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 43.23/43.48          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 43.23/43.48      inference('sup+', [status(thm)], ['22', '23'])).
% 43.23/43.48  thf('25', plain, (![X54 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X54)) = (X54))),
% 43.23/43.48      inference('cnf', [status(esa)], [t71_relat_1])).
% 43.23/43.48  thf('26', plain, (![X54 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X54)) = (X54))),
% 43.23/43.48      inference('cnf', [status(esa)], [t71_relat_1])).
% 43.23/43.48  thf('27', plain, (![X37 : $i]: (v1_relat_1 @ (k6_relat_1 @ X37))),
% 43.23/43.48      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 43.23/43.48  thf('28', plain, (![X37 : $i]: (v1_relat_1 @ (k6_relat_1 @ X37))),
% 43.23/43.48      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 43.23/43.48  thf('29', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 43.23/43.48      inference('demod', [status(thm)], ['24', '25', '26', '27', '28'])).
% 43.23/43.48  thf(t77_relat_1, axiom,
% 43.23/43.48    (![A:$i,B:$i]:
% 43.23/43.48     ( ( v1_relat_1 @ B ) =>
% 43.23/43.48       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 43.23/43.48         ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ) ))).
% 43.23/43.49  thf('30', plain,
% 43.23/43.49      (![X57 : $i, X58 : $i]:
% 43.23/43.49         (~ (r1_tarski @ (k1_relat_1 @ X57) @ X58)
% 43.23/43.49          | ((k5_relat_1 @ (k6_relat_1 @ X58) @ X57) = (X57))
% 43.23/43.49          | ~ (v1_relat_1 @ X57))),
% 43.23/43.49      inference('cnf', [status(esa)], [t77_relat_1])).
% 43.23/43.49  thf('31', plain,
% 43.23/43.49      (![X0 : $i]:
% 43.23/43.49         (~ (v1_relat_1 @ X0)
% 43.23/43.49          | ((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X0) = (X0)))),
% 43.23/43.49      inference('sup-', [status(thm)], ['29', '30'])).
% 43.23/43.49  thf('32', plain,
% 43.23/43.49      (![X0 : $i]:
% 43.23/43.49         (((k7_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (X0))
% 43.23/43.49          | ~ (v1_relat_1 @ X0)
% 43.23/43.49          | ~ (v1_relat_1 @ X0))),
% 43.23/43.49      inference('sup+', [status(thm)], ['17', '31'])).
% 43.23/43.49  thf('33', plain,
% 43.23/43.49      (![X0 : $i]:
% 43.23/43.49         (~ (v1_relat_1 @ X0) | ((k7_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (X0)))),
% 43.23/43.49      inference('simplify', [status(thm)], ['32'])).
% 43.23/43.49  thf('34', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i]:
% 43.23/43.49         (((k7_relat_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 43.23/43.49            (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0)) = (k7_relat_1 @ X1 @ X0))
% 43.23/43.49          | ~ (v1_relat_1 @ X1)
% 43.23/43.49          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 43.23/43.49      inference('sup+', [status(thm)], ['16', '33'])).
% 43.23/43.49  thf('35', plain,
% 43.23/43.49      (![X62 : $i, X63 : $i]:
% 43.23/43.49         (((k7_relat_1 @ X63 @ X62) = (k5_relat_1 @ (k6_relat_1 @ X62) @ X63))
% 43.23/43.49          | ~ (v1_relat_1 @ X63))),
% 43.23/43.49      inference('cnf', [status(esa)], [t94_relat_1])).
% 43.23/43.49  thf(dt_k5_relat_1, axiom,
% 43.23/43.49    (![A:$i,B:$i]:
% 43.23/43.49     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 43.23/43.49       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 43.23/43.49  thf('36', plain,
% 43.23/43.49      (![X35 : $i, X36 : $i]:
% 43.23/43.49         (~ (v1_relat_1 @ X35)
% 43.23/43.49          | ~ (v1_relat_1 @ X36)
% 43.23/43.49          | (v1_relat_1 @ (k5_relat_1 @ X35 @ X36)))),
% 43.23/43.49      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 43.23/43.49  thf('37', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i]:
% 43.23/43.49         ((v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 43.23/43.49          | ~ (v1_relat_1 @ X1)
% 43.23/43.49          | ~ (v1_relat_1 @ X1)
% 43.23/43.49          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 43.23/43.49      inference('sup+', [status(thm)], ['35', '36'])).
% 43.23/43.49  thf('38', plain, (![X37 : $i]: (v1_relat_1 @ (k6_relat_1 @ X37))),
% 43.23/43.49      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 43.23/43.49  thf('39', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i]:
% 43.23/43.49         ((v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 43.23/43.49          | ~ (v1_relat_1 @ X1)
% 43.23/43.49          | ~ (v1_relat_1 @ X1))),
% 43.23/43.49      inference('demod', [status(thm)], ['37', '38'])).
% 43.23/43.49  thf('40', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i]:
% 43.23/43.49         (~ (v1_relat_1 @ X1) | (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 43.23/43.49      inference('simplify', [status(thm)], ['39'])).
% 43.23/43.49  thf('41', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i]:
% 43.23/43.49         (~ (v1_relat_1 @ X1)
% 43.23/43.49          | ((k7_relat_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 43.23/43.49              (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0)) = (k7_relat_1 @ X1 @ X0)))),
% 43.23/43.49      inference('clc', [status(thm)], ['34', '40'])).
% 43.23/43.49  thf('42', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i]:
% 43.23/43.49         (((k7_relat_1 @ (k7_relat_1 @ X0 @ X1) @ 
% 43.23/43.49            (k3_xboole_0 @ X1 @ (k1_relat_1 @ X0))) = (k7_relat_1 @ X0 @ X1))
% 43.23/43.49          | ~ (v1_relat_1 @ X0))),
% 43.23/43.49      inference('sup+', [status(thm)], ['15', '41'])).
% 43.23/43.49  thf('43', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i]:
% 43.23/43.49         (((k7_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ 
% 43.23/43.49            (k3_xboole_0 @ X0 @ (k1_relat_1 @ (k6_relat_1 @ X1))))
% 43.23/43.49            = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 43.23/43.49          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 43.23/43.49      inference('sup+', [status(thm)], ['10', '42'])).
% 43.23/43.49  thf('44', plain, (![X53 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X53)) = (X53))),
% 43.23/43.49      inference('cnf', [status(esa)], [t71_relat_1])).
% 43.23/43.49  thf('45', plain,
% 43.23/43.49      (![X41 : $i, X42 : $i]:
% 43.23/43.49         (((k8_relat_1 @ X42 @ X41) = (k5_relat_1 @ X41 @ (k6_relat_1 @ X42)))
% 43.23/43.49          | ~ (v1_relat_1 @ X41))),
% 43.23/43.49      inference('cnf', [status(esa)], [t123_relat_1])).
% 43.23/43.49  thf('46', plain,
% 43.23/43.49      (![X62 : $i, X63 : $i]:
% 43.23/43.49         (((k7_relat_1 @ X63 @ X62) = (k5_relat_1 @ (k6_relat_1 @ X62) @ X63))
% 43.23/43.49          | ~ (v1_relat_1 @ X63))),
% 43.23/43.49      inference('cnf', [status(esa)], [t94_relat_1])).
% 43.23/43.49  thf(t112_relat_1, axiom,
% 43.23/43.49    (![A:$i,B:$i]:
% 43.23/43.49     ( ( v1_relat_1 @ B ) =>
% 43.23/43.49       ( ![C:$i]:
% 43.23/43.49         ( ( v1_relat_1 @ C ) =>
% 43.23/43.49           ( ( k7_relat_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 43.23/43.49             ( k5_relat_1 @ ( k7_relat_1 @ B @ A ) @ C ) ) ) ) ))).
% 43.23/43.49  thf('47', plain,
% 43.23/43.49      (![X38 : $i, X39 : $i, X40 : $i]:
% 43.23/43.49         (~ (v1_relat_1 @ X38)
% 43.23/43.49          | ((k7_relat_1 @ (k5_relat_1 @ X39 @ X38) @ X40)
% 43.23/43.49              = (k5_relat_1 @ (k7_relat_1 @ X39 @ X40) @ X38))
% 43.23/43.49          | ~ (v1_relat_1 @ X39))),
% 43.23/43.49      inference('cnf', [status(esa)], [t112_relat_1])).
% 43.23/43.49  thf('48', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 43.23/43.49         (((k7_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 43.23/43.49            = (k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X2) @ X1))
% 43.23/43.49          | ~ (v1_relat_1 @ X1)
% 43.23/43.49          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 43.23/43.49          | ~ (v1_relat_1 @ X1))),
% 43.23/43.49      inference('sup+', [status(thm)], ['46', '47'])).
% 43.23/43.49  thf('49', plain, (![X37 : $i]: (v1_relat_1 @ (k6_relat_1 @ X37))),
% 43.23/43.49      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 43.23/43.49  thf('50', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 43.23/43.49         (((k7_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 43.23/43.49            = (k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X2) @ X1))
% 43.23/43.49          | ~ (v1_relat_1 @ X1)
% 43.23/43.49          | ~ (v1_relat_1 @ X1))),
% 43.23/43.49      inference('demod', [status(thm)], ['48', '49'])).
% 43.23/43.49  thf('51', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 43.23/43.49         (~ (v1_relat_1 @ X1)
% 43.23/43.49          | ((k7_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 43.23/43.49              = (k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X2) @ X1)))),
% 43.23/43.49      inference('simplify', [status(thm)], ['50'])).
% 43.23/43.49  thf('52', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i]:
% 43.23/43.49         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 43.23/43.49           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 43.23/43.49      inference('demod', [status(thm)], ['7', '8', '9'])).
% 43.23/43.49  thf('53', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 43.23/43.49         (~ (v1_relat_1 @ X1)
% 43.23/43.49          | ((k7_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 43.23/43.49              = (k5_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X2)) @ X1)))),
% 43.23/43.49      inference('demod', [status(thm)], ['51', '52'])).
% 43.23/43.49  thf('54', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 43.23/43.49         (((k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X2) @ X1) @ X0)
% 43.23/43.49            = (k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))
% 43.23/43.49          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 43.23/43.49          | ~ (v1_relat_1 @ (k6_relat_1 @ X2)))),
% 43.23/43.49      inference('sup+', [status(thm)], ['45', '53'])).
% 43.23/43.49  thf('55', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i]:
% 43.23/43.49         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 43.23/43.49           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 43.23/43.49      inference('demod', [status(thm)], ['7', '8', '9'])).
% 43.23/43.49  thf('56', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i]:
% 43.23/43.49         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 43.23/43.49           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 43.23/43.49      inference('demod', [status(thm)], ['7', '8', '9'])).
% 43.23/43.49  thf('57', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i]:
% 43.23/43.49         (~ (v1_relat_1 @ X1) | (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 43.23/43.49      inference('simplify', [status(thm)], ['39'])).
% 43.23/43.49  thf('58', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i]:
% 43.23/43.49         ((v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 43.23/43.49          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 43.23/43.49      inference('sup+', [status(thm)], ['56', '57'])).
% 43.23/43.49  thf('59', plain, (![X37 : $i]: (v1_relat_1 @ (k6_relat_1 @ X37))),
% 43.23/43.49      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 43.23/43.49  thf('60', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i]:
% 43.23/43.49         (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 43.23/43.49      inference('demod', [status(thm)], ['58', '59'])).
% 43.23/43.49  thf('61', plain, (![X37 : $i]: (v1_relat_1 @ (k6_relat_1 @ X37))),
% 43.23/43.49      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 43.23/43.49  thf('62', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 43.23/43.49         ((k7_relat_1 @ (k8_relat_1 @ X2 @ (k6_relat_1 @ X1)) @ X0)
% 43.23/43.49           = (k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 43.23/43.49      inference('demod', [status(thm)], ['54', '55', '60', '61'])).
% 43.23/43.49  thf('63', plain,
% 43.23/43.49      (![X41 : $i, X42 : $i]:
% 43.23/43.49         (((k8_relat_1 @ X42 @ X41) = (k5_relat_1 @ X41 @ (k6_relat_1 @ X42)))
% 43.23/43.49          | ~ (v1_relat_1 @ X41))),
% 43.23/43.49      inference('cnf', [status(esa)], [t123_relat_1])).
% 43.23/43.49  thf(t17_xboole_1, axiom,
% 43.23/43.49    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 43.23/43.49  thf('64', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 43.23/43.49      inference('cnf', [status(esa)], [t17_xboole_1])).
% 43.23/43.49  thf('65', plain, (![X53 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X53)) = (X53))),
% 43.23/43.49      inference('cnf', [status(esa)], [t71_relat_1])).
% 43.23/43.49  thf('66', plain,
% 43.23/43.49      (![X57 : $i, X58 : $i]:
% 43.23/43.49         (~ (r1_tarski @ (k1_relat_1 @ X57) @ X58)
% 43.23/43.49          | ((k5_relat_1 @ (k6_relat_1 @ X58) @ X57) = (X57))
% 43.23/43.49          | ~ (v1_relat_1 @ X57))),
% 43.23/43.49      inference('cnf', [status(esa)], [t77_relat_1])).
% 43.23/43.49  thf('67', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i]:
% 43.23/43.49         (~ (r1_tarski @ X0 @ X1)
% 43.23/43.49          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 43.23/43.49          | ((k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 43.23/43.49              = (k6_relat_1 @ X0)))),
% 43.23/43.49      inference('sup-', [status(thm)], ['65', '66'])).
% 43.23/43.49  thf('68', plain, (![X37 : $i]: (v1_relat_1 @ (k6_relat_1 @ X37))),
% 43.23/43.49      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 43.23/43.49  thf('69', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i]:
% 43.23/43.49         (~ (r1_tarski @ X0 @ X1)
% 43.23/43.49          | ((k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 43.23/43.49              = (k6_relat_1 @ X0)))),
% 43.23/43.49      inference('demod', [status(thm)], ['67', '68'])).
% 43.23/43.49  thf('70', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i]:
% 43.23/43.49         ((k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 43.23/43.49           (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))
% 43.23/43.49           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 43.23/43.49      inference('sup-', [status(thm)], ['64', '69'])).
% 43.23/43.49  thf('71', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i]:
% 43.23/43.49         (((k8_relat_1 @ (k3_xboole_0 @ X0 @ X1) @ (k6_relat_1 @ X0))
% 43.23/43.49            = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))
% 43.23/43.49          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 43.23/43.49      inference('sup+', [status(thm)], ['63', '70'])).
% 43.23/43.49  thf('72', plain, (![X37 : $i]: (v1_relat_1 @ (k6_relat_1 @ X37))),
% 43.23/43.49      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 43.23/43.49  thf('73', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i]:
% 43.23/43.49         ((k8_relat_1 @ (k3_xboole_0 @ X0 @ X1) @ (k6_relat_1 @ X0))
% 43.23/43.49           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 43.23/43.49      inference('demod', [status(thm)], ['71', '72'])).
% 43.23/43.49  thf('74', plain,
% 43.23/43.49      (![X41 : $i, X42 : $i]:
% 43.23/43.49         (((k8_relat_1 @ X42 @ X41) = (k5_relat_1 @ X41 @ (k6_relat_1 @ X42)))
% 43.23/43.49          | ~ (v1_relat_1 @ X41))),
% 43.23/43.49      inference('cnf', [status(esa)], [t123_relat_1])).
% 43.23/43.49  thf(t139_relat_1, axiom,
% 43.23/43.49    (![A:$i,B:$i]:
% 43.23/43.49     ( ( v1_relat_1 @ B ) =>
% 43.23/43.49       ( ![C:$i]:
% 43.23/43.49         ( ( v1_relat_1 @ C ) =>
% 43.23/43.49           ( ( k8_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) =
% 43.23/43.49             ( k5_relat_1 @ B @ ( k8_relat_1 @ A @ C ) ) ) ) ) ))).
% 43.23/43.49  thf('75', plain,
% 43.23/43.49      (![X43 : $i, X44 : $i, X45 : $i]:
% 43.23/43.49         (~ (v1_relat_1 @ X43)
% 43.23/43.49          | ((k8_relat_1 @ X45 @ (k5_relat_1 @ X44 @ X43))
% 43.23/43.49              = (k5_relat_1 @ X44 @ (k8_relat_1 @ X45 @ X43)))
% 43.23/43.49          | ~ (v1_relat_1 @ X44))),
% 43.23/43.49      inference('cnf', [status(esa)], [t139_relat_1])).
% 43.23/43.49  thf('76', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 43.23/43.49         (((k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ X0))
% 43.23/43.49            = (k5_relat_1 @ X0 @ (k8_relat_1 @ X2 @ (k6_relat_1 @ X1))))
% 43.23/43.49          | ~ (v1_relat_1 @ X0)
% 43.23/43.49          | ~ (v1_relat_1 @ X0)
% 43.23/43.49          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 43.23/43.49      inference('sup+', [status(thm)], ['74', '75'])).
% 43.23/43.49  thf('77', plain, (![X37 : $i]: (v1_relat_1 @ (k6_relat_1 @ X37))),
% 43.23/43.49      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 43.23/43.49  thf('78', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 43.23/43.49         (((k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ X0))
% 43.23/43.49            = (k5_relat_1 @ X0 @ (k8_relat_1 @ X2 @ (k6_relat_1 @ X1))))
% 43.23/43.49          | ~ (v1_relat_1 @ X0)
% 43.23/43.49          | ~ (v1_relat_1 @ X0))),
% 43.23/43.49      inference('demod', [status(thm)], ['76', '77'])).
% 43.23/43.49  thf('79', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 43.23/43.49         (~ (v1_relat_1 @ X0)
% 43.23/43.49          | ((k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ X0))
% 43.23/43.49              = (k5_relat_1 @ X0 @ (k8_relat_1 @ X2 @ (k6_relat_1 @ X1)))))),
% 43.23/43.49      inference('simplify', [status(thm)], ['78'])).
% 43.23/43.49  thf('80', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 43.23/43.49      inference('cnf', [status(esa)], [t17_xboole_1])).
% 43.23/43.49  thf('81', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i]:
% 43.23/43.49         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 43.23/43.49           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 43.23/43.49      inference('demod', [status(thm)], ['7', '8', '9'])).
% 43.23/43.49  thf('82', plain,
% 43.23/43.49      (![X60 : $i, X61 : $i]:
% 43.23/43.49         (((k1_relat_1 @ (k7_relat_1 @ X60 @ X61))
% 43.23/43.49            = (k3_xboole_0 @ (k1_relat_1 @ X60) @ X61))
% 43.23/43.49          | ~ (v1_relat_1 @ X60))),
% 43.23/43.49      inference('cnf', [status(esa)], [t90_relat_1])).
% 43.23/43.49  thf('83', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i]:
% 43.23/43.49         (((k1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 43.23/43.49            = (k3_xboole_0 @ (k1_relat_1 @ (k6_relat_1 @ X1)) @ X0))
% 43.23/43.49          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 43.23/43.49      inference('sup+', [status(thm)], ['81', '82'])).
% 43.23/43.49  thf('84', plain, (![X53 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X53)) = (X53))),
% 43.23/43.49      inference('cnf', [status(esa)], [t71_relat_1])).
% 43.23/43.49  thf('85', plain, (![X37 : $i]: (v1_relat_1 @ (k6_relat_1 @ X37))),
% 43.23/43.49      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 43.23/43.49  thf('86', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i]:
% 43.23/43.49         ((k1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 43.23/43.49           = (k3_xboole_0 @ X1 @ X0))),
% 43.23/43.49      inference('demod', [status(thm)], ['83', '84', '85'])).
% 43.23/43.49  thf('87', plain,
% 43.23/43.49      (![X57 : $i, X58 : $i]:
% 43.23/43.49         (~ (r1_tarski @ (k1_relat_1 @ X57) @ X58)
% 43.23/43.49          | ((k5_relat_1 @ (k6_relat_1 @ X58) @ X57) = (X57))
% 43.23/43.49          | ~ (v1_relat_1 @ X57))),
% 43.23/43.49      inference('cnf', [status(esa)], [t77_relat_1])).
% 43.23/43.49  thf('88', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 43.23/43.49         (~ (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 43.23/43.49          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 43.23/43.49          | ((k5_relat_1 @ (k6_relat_1 @ X2) @ 
% 43.23/43.49              (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 43.23/43.49              = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 43.23/43.49      inference('sup-', [status(thm)], ['86', '87'])).
% 43.23/43.49  thf('89', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i]:
% 43.23/43.49         (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 43.23/43.49      inference('demod', [status(thm)], ['58', '59'])).
% 43.23/43.49  thf('90', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 43.23/43.49         (~ (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 43.23/43.49          | ((k5_relat_1 @ (k6_relat_1 @ X2) @ 
% 43.23/43.49              (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 43.23/43.49              = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 43.23/43.49      inference('demod', [status(thm)], ['88', '89'])).
% 43.23/43.49  thf('91', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i]:
% 43.23/43.49         ((k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 43.23/43.49           (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 43.23/43.49           = (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))),
% 43.23/43.49      inference('sup-', [status(thm)], ['80', '90'])).
% 43.23/43.49  thf('92', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i]:
% 43.23/43.49         (((k8_relat_1 @ X0 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 43.23/43.49            = (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 43.23/43.49          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 43.23/43.49      inference('sup+', [status(thm)], ['79', '91'])).
% 43.23/43.49  thf('93', plain, (![X37 : $i]: (v1_relat_1 @ (k6_relat_1 @ X37))),
% 43.23/43.49      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 43.23/43.49  thf('94', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i]:
% 43.23/43.49         ((k8_relat_1 @ X0 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 43.23/43.49           = (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))),
% 43.23/43.49      inference('demod', [status(thm)], ['92', '93'])).
% 43.23/43.49  thf('95', plain,
% 43.23/43.49      (![X41 : $i, X42 : $i]:
% 43.23/43.49         (((k8_relat_1 @ X42 @ X41) = (k5_relat_1 @ X41 @ (k6_relat_1 @ X42)))
% 43.23/43.49          | ~ (v1_relat_1 @ X41))),
% 43.23/43.49      inference('cnf', [status(esa)], [t123_relat_1])).
% 43.23/43.49  thf(t76_relat_1, axiom,
% 43.23/43.49    (![A:$i,B:$i]:
% 43.23/43.49     ( ( v1_relat_1 @ B ) =>
% 43.23/43.49       ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B ) & 
% 43.23/43.49         ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ))).
% 43.23/43.49  thf('96', plain,
% 43.23/43.49      (![X55 : $i, X56 : $i]:
% 43.23/43.49         ((r1_tarski @ (k5_relat_1 @ X55 @ (k6_relat_1 @ X56)) @ X55)
% 43.23/43.49          | ~ (v1_relat_1 @ X55))),
% 43.23/43.49      inference('cnf', [status(esa)], [t76_relat_1])).
% 43.23/43.49  thf('97', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i]:
% 43.23/43.49         (~ (r1_tarski @ X0 @ X1)
% 43.23/43.49          | ((k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 43.23/43.49              = (k6_relat_1 @ X0)))),
% 43.23/43.49      inference('demod', [status(thm)], ['67', '68'])).
% 43.23/43.49  thf('98', plain,
% 43.23/43.49      (![X0 : $i]:
% 43.23/43.49         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 43.23/43.49           = (k6_relat_1 @ X0))),
% 43.23/43.49      inference('demod', [status(thm)], ['20', '21'])).
% 43.23/43.49  thf('99', plain,
% 43.23/43.49      (![X41 : $i, X42 : $i]:
% 43.23/43.49         (((k8_relat_1 @ X42 @ X41) = (k5_relat_1 @ X41 @ (k6_relat_1 @ X42)))
% 43.23/43.49          | ~ (v1_relat_1 @ X41))),
% 43.23/43.49      inference('cnf', [status(esa)], [t123_relat_1])).
% 43.23/43.49  thf('100', plain,
% 43.23/43.49      (![X0 : $i]:
% 43.23/43.49         (((k8_relat_1 @ X0 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0))
% 43.23/43.49          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 43.23/43.49      inference('sup+', [status(thm)], ['98', '99'])).
% 43.23/43.49  thf('101', plain, (![X37 : $i]: (v1_relat_1 @ (k6_relat_1 @ X37))),
% 43.23/43.49      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 43.23/43.49  thf('102', plain,
% 43.23/43.49      (![X0 : $i]: ((k8_relat_1 @ X0 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0))),
% 43.23/43.49      inference('demod', [status(thm)], ['100', '101'])).
% 43.23/43.49  thf('103', plain,
% 43.23/43.49      (![X62 : $i, X63 : $i]:
% 43.23/43.49         (((k7_relat_1 @ X63 @ X62) = (k5_relat_1 @ (k6_relat_1 @ X62) @ X63))
% 43.23/43.49          | ~ (v1_relat_1 @ X63))),
% 43.23/43.49      inference('cnf', [status(esa)], [t94_relat_1])).
% 43.23/43.49  thf('104', plain,
% 43.23/43.49      (![X43 : $i, X44 : $i, X45 : $i]:
% 43.23/43.49         (~ (v1_relat_1 @ X43)
% 43.23/43.49          | ((k8_relat_1 @ X45 @ (k5_relat_1 @ X44 @ X43))
% 43.23/43.49              = (k5_relat_1 @ X44 @ (k8_relat_1 @ X45 @ X43)))
% 43.23/43.49          | ~ (v1_relat_1 @ X44))),
% 43.23/43.49      inference('cnf', [status(esa)], [t139_relat_1])).
% 43.23/43.49  thf('105', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 43.23/43.49         (((k8_relat_1 @ X2 @ (k7_relat_1 @ X1 @ X0))
% 43.23/43.49            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k8_relat_1 @ X2 @ X1)))
% 43.23/43.49          | ~ (v1_relat_1 @ X1)
% 43.23/43.49          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 43.23/43.49          | ~ (v1_relat_1 @ X1))),
% 43.23/43.49      inference('sup+', [status(thm)], ['103', '104'])).
% 43.23/43.49  thf('106', plain, (![X37 : $i]: (v1_relat_1 @ (k6_relat_1 @ X37))),
% 43.23/43.49      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 43.23/43.49  thf('107', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 43.23/43.49         (((k8_relat_1 @ X2 @ (k7_relat_1 @ X1 @ X0))
% 43.23/43.49            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k8_relat_1 @ X2 @ X1)))
% 43.23/43.49          | ~ (v1_relat_1 @ X1)
% 43.23/43.49          | ~ (v1_relat_1 @ X1))),
% 43.23/43.49      inference('demod', [status(thm)], ['105', '106'])).
% 43.23/43.49  thf('108', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 43.23/43.49         (~ (v1_relat_1 @ X1)
% 43.23/43.49          | ((k8_relat_1 @ X2 @ (k7_relat_1 @ X1 @ X0))
% 43.23/43.49              = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k8_relat_1 @ X2 @ X1))))),
% 43.23/43.49      inference('simplify', [status(thm)], ['107'])).
% 43.23/43.49  thf('109', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i]:
% 43.23/43.49         (((k8_relat_1 @ X0 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 43.23/43.49            = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))
% 43.23/43.49          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 43.23/43.49      inference('sup+', [status(thm)], ['102', '108'])).
% 43.23/43.49  thf('110', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i]:
% 43.23/43.49         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 43.23/43.49           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 43.23/43.49      inference('demod', [status(thm)], ['7', '8', '9'])).
% 43.23/43.49  thf('111', plain,
% 43.23/43.49      (![X41 : $i, X42 : $i]:
% 43.23/43.49         (((k8_relat_1 @ X42 @ X41) = (k5_relat_1 @ X41 @ (k6_relat_1 @ X42)))
% 43.23/43.49          | ~ (v1_relat_1 @ X41))),
% 43.23/43.49      inference('cnf', [status(esa)], [t123_relat_1])).
% 43.23/43.49  thf('112', plain,
% 43.23/43.49      (![X0 : $i]:
% 43.23/43.49         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 43.23/43.49           = (k6_relat_1 @ X0))),
% 43.23/43.49      inference('demod', [status(thm)], ['20', '21'])).
% 43.23/43.49  thf('113', plain,
% 43.23/43.49      (![X38 : $i, X39 : $i, X40 : $i]:
% 43.23/43.49         (~ (v1_relat_1 @ X38)
% 43.23/43.49          | ((k7_relat_1 @ (k5_relat_1 @ X39 @ X38) @ X40)
% 43.23/43.49              = (k5_relat_1 @ (k7_relat_1 @ X39 @ X40) @ X38))
% 43.23/43.49          | ~ (v1_relat_1 @ X39))),
% 43.23/43.49      inference('cnf', [status(esa)], [t112_relat_1])).
% 43.23/43.49  thf('114', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i]:
% 43.23/43.49         (((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 43.23/43.49            = (k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1) @ 
% 43.23/43.49               (k6_relat_1 @ X0)))
% 43.23/43.49          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 43.23/43.49          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 43.23/43.49      inference('sup+', [status(thm)], ['112', '113'])).
% 43.23/43.49  thf('115', plain, (![X37 : $i]: (v1_relat_1 @ (k6_relat_1 @ X37))),
% 43.23/43.49      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 43.23/43.49  thf('116', plain, (![X37 : $i]: (v1_relat_1 @ (k6_relat_1 @ X37))),
% 43.23/43.49      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 43.23/43.49  thf('117', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i]:
% 43.23/43.49         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 43.23/43.49           = (k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1) @ 
% 43.23/43.49              (k6_relat_1 @ X0)))),
% 43.23/43.49      inference('demod', [status(thm)], ['114', '115', '116'])).
% 43.23/43.49  thf('118', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i]:
% 43.23/43.49         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 43.23/43.49           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 43.23/43.49      inference('demod', [status(thm)], ['7', '8', '9'])).
% 43.23/43.49  thf('119', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i]:
% 43.23/43.49         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 43.23/43.49           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 43.23/43.49      inference('demod', [status(thm)], ['7', '8', '9'])).
% 43.23/43.49  thf('120', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i]:
% 43.23/43.49         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 43.23/43.49           = (k5_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)) @ 
% 43.23/43.49              (k6_relat_1 @ X0)))),
% 43.23/43.49      inference('demod', [status(thm)], ['117', '118', '119'])).
% 43.23/43.49  thf('121', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i]:
% 43.23/43.49         (((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 43.23/43.49            = (k8_relat_1 @ X1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))
% 43.23/43.49          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 43.23/43.49      inference('sup+', [status(thm)], ['111', '120'])).
% 43.23/43.49  thf('122', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i]:
% 43.23/43.49         (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 43.23/43.49      inference('demod', [status(thm)], ['58', '59'])).
% 43.23/43.49  thf('123', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i]:
% 43.23/43.49         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 43.23/43.49           = (k8_relat_1 @ X1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 43.23/43.49      inference('demod', [status(thm)], ['121', '122'])).
% 43.23/43.49  thf('124', plain, (![X37 : $i]: (v1_relat_1 @ (k6_relat_1 @ X37))),
% 43.23/43.49      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 43.23/43.49  thf('125', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i]:
% 43.23/43.49         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 43.23/43.49           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 43.23/43.49      inference('demod', [status(thm)], ['109', '110', '123', '124'])).
% 43.23/43.49  thf('126', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i]:
% 43.23/43.49         (~ (r1_tarski @ X0 @ X1)
% 43.23/43.49          | ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1)) = (k6_relat_1 @ X0)))),
% 43.23/43.49      inference('demod', [status(thm)], ['97', '125'])).
% 43.23/43.49  thf('127', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i]:
% 43.23/43.49         (~ (v1_relat_1 @ X0)
% 43.23/43.49          | ((k8_relat_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)) @ 
% 43.23/43.49              (k6_relat_1 @ X0))
% 43.23/43.49              = (k6_relat_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)))))),
% 43.23/43.49      inference('sup-', [status(thm)], ['96', '126'])).
% 43.23/43.49  thf('128', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i]:
% 43.23/43.49         ((k1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 43.23/43.49           = (k3_xboole_0 @ X1 @ X0))),
% 43.23/43.49      inference('demod', [status(thm)], ['83', '84', '85'])).
% 43.23/43.49  thf('129', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i]:
% 43.23/43.49         (((k1_relat_1 @ (k6_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))))
% 43.23/43.49            = (k3_xboole_0 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ X1))
% 43.23/43.49          | ~ (v1_relat_1 @ X1))),
% 43.23/43.49      inference('sup+', [status(thm)], ['127', '128'])).
% 43.23/43.49  thf('130', plain, (![X53 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X53)) = (X53))),
% 43.23/43.49      inference('cnf', [status(esa)], [t71_relat_1])).
% 43.23/43.49  thf('131', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 43.23/43.49      inference('sup+', [status(thm)], ['13', '14'])).
% 43.23/43.49  thf('132', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i]:
% 43.23/43.49         (((k5_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 43.23/43.49            = (k3_xboole_0 @ X1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))))
% 43.23/43.49          | ~ (v1_relat_1 @ X1))),
% 43.23/43.49      inference('demod', [status(thm)], ['129', '130', '131'])).
% 43.23/43.49  thf('133', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i]:
% 43.23/43.49         (((k5_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 43.23/43.49            = (k3_xboole_0 @ X0 @ (k8_relat_1 @ X1 @ X0)))
% 43.23/43.49          | ~ (v1_relat_1 @ X0)
% 43.23/43.49          | ~ (v1_relat_1 @ X0))),
% 43.23/43.49      inference('sup+', [status(thm)], ['95', '132'])).
% 43.23/43.49  thf('134', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i]:
% 43.23/43.49         (~ (v1_relat_1 @ X0)
% 43.23/43.49          | ((k5_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 43.23/43.49              = (k3_xboole_0 @ X0 @ (k8_relat_1 @ X1 @ X0))))),
% 43.23/43.49      inference('simplify', [status(thm)], ['133'])).
% 43.23/43.49  thf('135', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i]:
% 43.23/43.49         (((k5_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)) @ 
% 43.23/43.49            (k6_relat_1 @ X1))
% 43.23/43.49            = (k3_xboole_0 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)) @ 
% 43.23/43.49               (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))
% 43.23/43.49          | ~ (v1_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1))))),
% 43.23/43.49      inference('sup+', [status(thm)], ['94', '134'])).
% 43.23/43.49  thf('136', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i]:
% 43.23/43.49         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 43.23/43.49           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 43.23/43.49      inference('demod', [status(thm)], ['7', '8', '9'])).
% 43.23/43.49  thf('137', plain,
% 43.23/43.49      (![X41 : $i, X42 : $i]:
% 43.23/43.49         (((k8_relat_1 @ X42 @ X41) = (k5_relat_1 @ X41 @ (k6_relat_1 @ X42)))
% 43.23/43.49          | ~ (v1_relat_1 @ X41))),
% 43.23/43.49      inference('cnf', [status(esa)], [t123_relat_1])).
% 43.23/43.49  thf('138', plain,
% 43.23/43.49      (![X38 : $i, X39 : $i, X40 : $i]:
% 43.23/43.49         (~ (v1_relat_1 @ X38)
% 43.23/43.49          | ((k7_relat_1 @ (k5_relat_1 @ X39 @ X38) @ X40)
% 43.23/43.49              = (k5_relat_1 @ (k7_relat_1 @ X39 @ X40) @ X38))
% 43.23/43.49          | ~ (v1_relat_1 @ X39))),
% 43.23/43.49      inference('cnf', [status(esa)], [t112_relat_1])).
% 43.23/43.49  thf('139', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 43.23/43.49         (((k7_relat_1 @ (k8_relat_1 @ X1 @ X0) @ X2)
% 43.23/43.49            = (k5_relat_1 @ (k7_relat_1 @ X0 @ X2) @ (k6_relat_1 @ X1)))
% 43.23/43.49          | ~ (v1_relat_1 @ X0)
% 43.23/43.49          | ~ (v1_relat_1 @ X0)
% 43.23/43.49          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 43.23/43.49      inference('sup+', [status(thm)], ['137', '138'])).
% 43.23/43.49  thf('140', plain, (![X37 : $i]: (v1_relat_1 @ (k6_relat_1 @ X37))),
% 43.23/43.49      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 43.23/43.49  thf('141', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 43.23/43.49         (((k7_relat_1 @ (k8_relat_1 @ X1 @ X0) @ X2)
% 43.23/43.49            = (k5_relat_1 @ (k7_relat_1 @ X0 @ X2) @ (k6_relat_1 @ X1)))
% 43.23/43.49          | ~ (v1_relat_1 @ X0)
% 43.23/43.49          | ~ (v1_relat_1 @ X0))),
% 43.23/43.49      inference('demod', [status(thm)], ['139', '140'])).
% 43.23/43.49  thf('142', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 43.23/43.49         (~ (v1_relat_1 @ X0)
% 43.23/43.49          | ((k7_relat_1 @ (k8_relat_1 @ X1 @ X0) @ X2)
% 43.23/43.49              = (k5_relat_1 @ (k7_relat_1 @ X0 @ X2) @ (k6_relat_1 @ X1))))),
% 43.23/43.49      inference('simplify', [status(thm)], ['141'])).
% 43.23/43.49  thf('143', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 43.23/43.49         (((k7_relat_1 @ (k8_relat_1 @ X2 @ (k6_relat_1 @ X1)) @ X0)
% 43.23/43.49            = (k5_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ 
% 43.23/43.49               (k6_relat_1 @ X2)))
% 43.23/43.49          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 43.23/43.49      inference('sup+', [status(thm)], ['136', '142'])).
% 43.23/43.49  thf('144', plain, (![X37 : $i]: (v1_relat_1 @ (k6_relat_1 @ X37))),
% 43.23/43.49      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 43.23/43.49  thf('145', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 43.23/43.49         ((k7_relat_1 @ (k8_relat_1 @ X2 @ (k6_relat_1 @ X1)) @ X0)
% 43.23/43.49           = (k5_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ 
% 43.23/43.49              (k6_relat_1 @ X2)))),
% 43.23/43.49      inference('demod', [status(thm)], ['143', '144'])).
% 43.23/43.49  thf('146', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 43.23/43.49         ((k7_relat_1 @ (k8_relat_1 @ X2 @ (k6_relat_1 @ X1)) @ X0)
% 43.23/43.49           = (k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 43.23/43.49      inference('demod', [status(thm)], ['54', '55', '60', '61'])).
% 43.23/43.49  thf('147', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 43.23/43.49         ((k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 43.23/43.49           = (k5_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ 
% 43.23/43.49              (k6_relat_1 @ X2)))),
% 43.23/43.49      inference('demod', [status(thm)], ['145', '146'])).
% 43.23/43.49  thf('148', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i]:
% 43.23/43.49         ((k8_relat_1 @ X0 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 43.23/43.49           = (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))),
% 43.23/43.49      inference('demod', [status(thm)], ['92', '93'])).
% 43.23/43.49  thf('149', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i]:
% 43.23/43.49         (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 43.23/43.49      inference('demod', [status(thm)], ['58', '59'])).
% 43.23/43.49  thf('150', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i]:
% 43.23/43.49         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 43.23/43.49           = (k3_xboole_0 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)) @ 
% 43.23/43.49              (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 43.23/43.49      inference('demod', [status(thm)], ['135', '147', '148', '149'])).
% 43.23/43.49  thf('151', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i]:
% 43.23/43.49         ((k8_relat_1 @ (k3_xboole_0 @ X1 @ X0) @ (k6_relat_1 @ X1))
% 43.23/43.49           = (k3_xboole_0 @ 
% 43.23/43.49              (k8_relat_1 @ X1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))) @ 
% 43.23/43.49              (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))),
% 43.23/43.49      inference('sup+', [status(thm)], ['73', '150'])).
% 43.23/43.49  thf('152', plain,
% 43.23/43.49      (![X41 : $i, X42 : $i]:
% 43.23/43.49         (((k8_relat_1 @ X42 @ X41) = (k5_relat_1 @ X41 @ (k6_relat_1 @ X42)))
% 43.23/43.49          | ~ (v1_relat_1 @ X41))),
% 43.23/43.49      inference('cnf', [status(esa)], [t123_relat_1])).
% 43.23/43.49  thf('153', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 43.23/43.49      inference('sup+', [status(thm)], ['13', '14'])).
% 43.23/43.49  thf('154', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 43.23/43.49      inference('sup+', [status(thm)], ['13', '14'])).
% 43.23/43.49  thf('155', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 43.23/43.49      inference('cnf', [status(esa)], [t17_xboole_1])).
% 43.23/43.49  thf('156', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 43.23/43.49      inference('sup+', [status(thm)], ['154', '155'])).
% 43.23/43.49  thf('157', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i]:
% 43.23/43.49         (~ (r1_tarski @ X0 @ X1)
% 43.23/43.49          | ((k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 43.23/43.49              = (k6_relat_1 @ X0)))),
% 43.23/43.49      inference('demod', [status(thm)], ['67', '68'])).
% 43.23/43.49  thf('158', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i]:
% 43.23/43.49         ((k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 43.23/43.49           (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 43.23/43.49           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 43.23/43.49      inference('sup-', [status(thm)], ['156', '157'])).
% 43.23/43.49  thf('159', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i]:
% 43.23/43.49         ((k5_relat_1 @ (k6_relat_1 @ X1) @ 
% 43.23/43.49           (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 43.23/43.49           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 43.23/43.49      inference('sup+', [status(thm)], ['153', '158'])).
% 43.23/43.49  thf('160', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i]:
% 43.23/43.49         (((k8_relat_1 @ (k3_xboole_0 @ X0 @ X1) @ (k6_relat_1 @ X0))
% 43.23/43.49            = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 43.23/43.49          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 43.23/43.49      inference('sup+', [status(thm)], ['152', '159'])).
% 43.23/43.49  thf('161', plain, (![X37 : $i]: (v1_relat_1 @ (k6_relat_1 @ X37))),
% 43.23/43.49      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 43.23/43.49  thf('162', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i]:
% 43.23/43.49         ((k8_relat_1 @ (k3_xboole_0 @ X0 @ X1) @ (k6_relat_1 @ X0))
% 43.23/43.49           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 43.23/43.49      inference('demod', [status(thm)], ['160', '161'])).
% 43.23/43.49  thf('163', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 43.23/43.49      inference('sup+', [status(thm)], ['13', '14'])).
% 43.23/43.49  thf('164', plain,
% 43.23/43.49      (![X62 : $i, X63 : $i]:
% 43.23/43.49         (((k7_relat_1 @ X63 @ X62) = (k5_relat_1 @ (k6_relat_1 @ X62) @ X63))
% 43.23/43.49          | ~ (v1_relat_1 @ X63))),
% 43.23/43.49      inference('cnf', [status(esa)], [t94_relat_1])).
% 43.23/43.49  thf('165', plain,
% 43.23/43.49      (![X55 : $i, X56 : $i]:
% 43.23/43.49         ((r1_tarski @ (k5_relat_1 @ X55 @ (k6_relat_1 @ X56)) @ X55)
% 43.23/43.49          | ~ (v1_relat_1 @ X55))),
% 43.23/43.49      inference('cnf', [status(esa)], [t76_relat_1])).
% 43.23/43.49  thf('166', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i]:
% 43.23/43.49         ((r1_tarski @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 43.23/43.49           (k6_relat_1 @ X0))
% 43.23/43.49          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 43.23/43.49          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 43.23/43.49      inference('sup+', [status(thm)], ['164', '165'])).
% 43.23/43.49  thf('167', plain, (![X37 : $i]: (v1_relat_1 @ (k6_relat_1 @ X37))),
% 43.23/43.49      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 43.23/43.49  thf('168', plain, (![X37 : $i]: (v1_relat_1 @ (k6_relat_1 @ X37))),
% 43.23/43.49      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 43.23/43.49  thf('169', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i]:
% 43.23/43.49         (r1_tarski @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ (k6_relat_1 @ X0))),
% 43.23/43.49      inference('demod', [status(thm)], ['166', '167', '168'])).
% 43.23/43.49  thf('170', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i]:
% 43.23/43.49         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 43.23/43.49           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 43.23/43.49      inference('demod', [status(thm)], ['7', '8', '9'])).
% 43.23/43.49  thf('171', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i]:
% 43.23/43.49         (r1_tarski @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ (k6_relat_1 @ X0))),
% 43.23/43.49      inference('demod', [status(thm)], ['169', '170'])).
% 43.23/43.49  thf('172', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i]:
% 43.23/43.49         (~ (r1_tarski @ X0 @ X1)
% 43.23/43.49          | ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1)) = (k6_relat_1 @ X0)))),
% 43.23/43.49      inference('demod', [status(thm)], ['97', '125'])).
% 43.23/43.49  thf('173', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i]:
% 43.23/43.49         ((k8_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ 
% 43.23/43.49           (k6_relat_1 @ (k6_relat_1 @ X0)))
% 43.23/43.49           = (k6_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 43.23/43.49      inference('sup-', [status(thm)], ['171', '172'])).
% 43.23/43.49  thf('174', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i]:
% 43.23/43.49         ((k1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 43.23/43.49           = (k3_xboole_0 @ X1 @ X0))),
% 43.23/43.49      inference('demod', [status(thm)], ['83', '84', '85'])).
% 43.23/43.49  thf('175', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i]:
% 43.23/43.49         ((k1_relat_1 @ (k6_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))
% 43.23/43.49           = (k3_xboole_0 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ 
% 43.23/43.49              (k6_relat_1 @ X0)))),
% 43.23/43.49      inference('sup+', [status(thm)], ['173', '174'])).
% 43.23/43.49  thf('176', plain, (![X53 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X53)) = (X53))),
% 43.23/43.49      inference('cnf', [status(esa)], [t71_relat_1])).
% 43.23/43.49  thf('177', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 43.23/43.49      inference('sup+', [status(thm)], ['13', '14'])).
% 43.23/43.49  thf('178', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i]:
% 43.23/43.49         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 43.23/43.49           = (k3_xboole_0 @ (k6_relat_1 @ X0) @ 
% 43.23/43.49              (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 43.23/43.49      inference('demod', [status(thm)], ['175', '176', '177'])).
% 43.23/43.49  thf('179', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i]:
% 43.23/43.49         ((k6_relat_1 @ (k3_xboole_0 @ X0 @ X1))
% 43.23/43.49           = (k8_relat_1 @ X1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))),
% 43.23/43.49      inference('demod', [status(thm)], ['151', '162', '163', '178'])).
% 43.23/43.49  thf('180', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i]:
% 43.23/43.49         ((k6_relat_1 @ (k3_xboole_0 @ X0 @ X1))
% 43.23/43.49           = (k8_relat_1 @ X1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))),
% 43.23/43.49      inference('demod', [status(thm)], ['151', '162', '163', '178'])).
% 43.23/43.49  thf('181', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i]:
% 43.23/43.49         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 43.23/43.49           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 43.23/43.49      inference('demod', [status(thm)], ['7', '8', '9'])).
% 43.23/43.49  thf('182', plain, (![X37 : $i]: (v1_relat_1 @ (k6_relat_1 @ X37))),
% 43.23/43.49      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 43.23/43.49  thf('183', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i]:
% 43.23/43.49         ((k6_relat_1 @ (k3_xboole_0 @ X0 @ X1))
% 43.23/43.49           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 43.23/43.49      inference('demod', [status(thm)],
% 43.23/43.49                ['43', '44', '62', '179', '180', '181', '182'])).
% 43.23/43.49  thf('184', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i]:
% 43.23/43.49         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 43.23/43.49           = (k3_xboole_0 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)) @ 
% 43.23/43.49              (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 43.23/43.49      inference('demod', [status(thm)], ['135', '147', '148', '149'])).
% 43.23/43.49  thf('185', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 43.23/43.49      inference('sup+', [status(thm)], ['13', '14'])).
% 43.23/43.49  thf('186', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i]:
% 43.23/43.49         ((k8_relat_1 @ (k3_xboole_0 @ X0 @ X1) @ (k6_relat_1 @ X0))
% 43.23/43.49           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 43.23/43.49      inference('demod', [status(thm)], ['71', '72'])).
% 43.23/43.49  thf('187', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i]:
% 43.23/43.49         ((k1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 43.23/43.49           = (k3_xboole_0 @ X1 @ X0))),
% 43.23/43.49      inference('demod', [status(thm)], ['83', '84', '85'])).
% 43.23/43.49  thf('188', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i]:
% 43.23/43.49         ((k1_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 43.23/43.49           = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))),
% 43.23/43.49      inference('sup+', [status(thm)], ['186', '187'])).
% 43.23/43.49  thf('189', plain, (![X53 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X53)) = (X53))),
% 43.23/43.49      inference('cnf', [status(esa)], [t71_relat_1])).
% 43.23/43.49  thf('190', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 43.23/43.49      inference('sup+', [status(thm)], ['13', '14'])).
% 43.23/43.49  thf('191', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i]:
% 43.23/43.49         ((k3_xboole_0 @ X1 @ X0)
% 43.23/43.49           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 43.23/43.49      inference('demod', [status(thm)], ['188', '189', '190'])).
% 43.23/43.49  thf('192', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i]:
% 43.23/43.49         ((k3_xboole_0 @ X0 @ X1)
% 43.23/43.49           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 43.23/43.49      inference('sup+', [status(thm)], ['185', '191'])).
% 43.23/43.49  thf(t70_enumset1, axiom,
% 43.23/43.49    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 43.23/43.49  thf('193', plain,
% 43.23/43.49      (![X6 : $i, X7 : $i]:
% 43.23/43.49         ((k1_enumset1 @ X6 @ X6 @ X7) = (k2_tarski @ X6 @ X7))),
% 43.23/43.49      inference('cnf', [status(esa)], [t70_enumset1])).
% 43.23/43.49  thf('194', plain,
% 43.23/43.49      (![X33 : $i, X34 : $i]:
% 43.23/43.49         ((k1_setfam_1 @ (k2_tarski @ X33 @ X34)) = (k3_xboole_0 @ X33 @ X34))),
% 43.23/43.49      inference('cnf', [status(esa)], [t12_setfam_1])).
% 43.23/43.49  thf('195', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i]:
% 43.23/43.49         ((k1_setfam_1 @ (k1_enumset1 @ X1 @ X1 @ X0))
% 43.23/43.49           = (k3_xboole_0 @ X1 @ X0))),
% 43.23/43.49      inference('sup+', [status(thm)], ['193', '194'])).
% 43.23/43.49  thf('196', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i]:
% 43.23/43.49         ((k1_setfam_1 @ (k1_enumset1 @ X1 @ X1 @ (k3_xboole_0 @ X0 @ X1)))
% 43.23/43.49           = (k3_xboole_0 @ X1 @ X0))),
% 43.23/43.49      inference('sup+', [status(thm)], ['192', '195'])).
% 43.23/43.49  thf('197', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i]:
% 43.23/43.49         ((k1_setfam_1 @ 
% 43.23/43.49           (k1_enumset1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ 
% 43.23/43.49            (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ 
% 43.23/43.49            (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))
% 43.23/43.49           = (k3_xboole_0 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ 
% 43.23/43.49              (k8_relat_1 @ X0 @ (k6_relat_1 @ X1))))),
% 43.23/43.49      inference('sup+', [status(thm)], ['184', '196'])).
% 43.23/43.49  thf('198', plain,
% 43.23/43.49      (![X6 : $i, X7 : $i]:
% 43.23/43.49         ((k1_enumset1 @ X6 @ X6 @ X7) = (k2_tarski @ X6 @ X7))),
% 43.23/43.49      inference('cnf', [status(esa)], [t70_enumset1])).
% 43.23/43.49  thf('199', plain,
% 43.23/43.49      (![X4 : $i, X5 : $i]: ((k2_tarski @ X5 @ X4) = (k2_tarski @ X4 @ X5))),
% 43.23/43.49      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 43.23/43.49  thf('200', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i]:
% 43.23/43.49         ((k2_tarski @ X0 @ X1) = (k1_enumset1 @ X1 @ X1 @ X0))),
% 43.23/43.49      inference('sup+', [status(thm)], ['198', '199'])).
% 43.23/43.49  thf('201', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i]:
% 43.23/43.49         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 43.23/43.49      inference('sup+', [status(thm)], ['11', '12'])).
% 43.23/43.49  thf('202', plain,
% 43.23/43.49      (![X59 : $i]:
% 43.23/43.49         (((k5_relat_1 @ X59 @ (k6_relat_1 @ (k2_relat_1 @ X59))) = (X59))
% 43.23/43.49          | ~ (v1_relat_1 @ X59))),
% 43.23/43.49      inference('cnf', [status(esa)], [t80_relat_1])).
% 43.23/43.49  thf('203', plain,
% 43.23/43.49      (![X62 : $i, X63 : $i]:
% 43.23/43.49         (((k7_relat_1 @ X63 @ X62) = (k5_relat_1 @ (k6_relat_1 @ X62) @ X63))
% 43.23/43.49          | ~ (v1_relat_1 @ X63))),
% 43.23/43.49      inference('cnf', [status(esa)], [t94_relat_1])).
% 43.23/43.49  thf('204', plain,
% 43.23/43.49      (![X0 : $i]:
% 43.23/43.49         (((k7_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ (k6_relat_1 @ X0))) @ X0)
% 43.23/43.49            = (k6_relat_1 @ X0))
% 43.23/43.49          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 43.23/43.49          | ~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ (k6_relat_1 @ X0)))))),
% 43.23/43.49      inference('sup+', [status(thm)], ['202', '203'])).
% 43.23/43.49  thf('205', plain, (![X54 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X54)) = (X54))),
% 43.23/43.49      inference('cnf', [status(esa)], [t71_relat_1])).
% 43.23/43.49  thf('206', plain, (![X37 : $i]: (v1_relat_1 @ (k6_relat_1 @ X37))),
% 43.23/43.49      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 43.23/43.49  thf('207', plain, (![X54 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X54)) = (X54))),
% 43.23/43.49      inference('cnf', [status(esa)], [t71_relat_1])).
% 43.23/43.49  thf('208', plain, (![X37 : $i]: (v1_relat_1 @ (k6_relat_1 @ X37))),
% 43.23/43.49      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 43.23/43.49  thf('209', plain,
% 43.23/43.49      (![X0 : $i]: ((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 43.23/43.49      inference('demod', [status(thm)], ['204', '205', '206', '207', '208'])).
% 43.23/43.49  thf('210', plain,
% 43.23/43.49      (![X60 : $i, X61 : $i]:
% 43.23/43.49         (((k1_relat_1 @ (k7_relat_1 @ X60 @ X61))
% 43.23/43.49            = (k3_xboole_0 @ (k1_relat_1 @ X60) @ X61))
% 43.23/43.49          | ~ (v1_relat_1 @ X60))),
% 43.23/43.49      inference('cnf', [status(esa)], [t90_relat_1])).
% 43.23/43.49  thf('211', plain,
% 43.23/43.49      (![X0 : $i]:
% 43.23/43.49         (((k1_relat_1 @ (k6_relat_1 @ X0))
% 43.23/43.49            = (k3_xboole_0 @ (k1_relat_1 @ (k6_relat_1 @ X0)) @ X0))
% 43.23/43.49          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 43.23/43.49      inference('sup+', [status(thm)], ['209', '210'])).
% 43.23/43.49  thf('212', plain, (![X53 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X53)) = (X53))),
% 43.23/43.49      inference('cnf', [status(esa)], [t71_relat_1])).
% 43.23/43.49  thf('213', plain, (![X53 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X53)) = (X53))),
% 43.23/43.49      inference('cnf', [status(esa)], [t71_relat_1])).
% 43.23/43.49  thf('214', plain, (![X37 : $i]: (v1_relat_1 @ (k6_relat_1 @ X37))),
% 43.23/43.49      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 43.23/43.49  thf('215', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 43.23/43.49      inference('demod', [status(thm)], ['211', '212', '213', '214'])).
% 43.23/43.49  thf('216', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i]:
% 43.23/43.49         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 43.23/43.49           = (k3_xboole_0 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)) @ 
% 43.23/43.49              (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 43.23/43.49      inference('demod', [status(thm)], ['135', '147', '148', '149'])).
% 43.23/43.49  thf('217', plain,
% 43.23/43.49      (![X0 : $i, X1 : $i]:
% 43.23/43.49         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 43.23/43.49           = (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))),
% 43.23/43.49      inference('demod', [status(thm)], ['197', '200', '201', '215', '216'])).
% 43.23/43.49  thf('218', plain,
% 43.23/43.49      (((k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B))
% 43.23/43.49         != (k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B)))),
% 43.23/43.49      inference('demod', [status(thm)], ['4', '183', '217'])).
% 43.23/43.49  thf('219', plain, ($false), inference('simplify', [status(thm)], ['218'])).
% 43.23/43.49  
% 43.23/43.49  % SZS output end Refutation
% 43.23/43.49  
% 43.23/43.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
