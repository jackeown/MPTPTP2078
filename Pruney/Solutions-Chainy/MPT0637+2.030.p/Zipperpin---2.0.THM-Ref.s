%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.djZ92TSFNB

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:59 EST 2020

% Result     : Theorem 2.16s
% Output     : Refutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 408 expanded)
%              Number of leaves         :   23 ( 149 expanded)
%              Depth                    :   18
%              Number of atoms          : 1089 (3580 expanded)
%              Number of equality atoms :   71 ( 267 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('0',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k7_relat_1 @ X36 @ X35 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X35 ) @ X36 ) )
      | ~ ( v1_relat_1 @ X36 ) ) ),
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
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('4',plain,(
    ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('5',plain,(
    ! [X25: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X25 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('6',plain,(
    ! [X32: $i] :
      ( ( ( k5_relat_1 @ X32 @ ( k6_relat_1 @ ( k2_relat_1 @ X32 ) ) )
        = X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k7_relat_1 @ X36 @ X35 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X35 ) @ X36 ) )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

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
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X22 @ X21 ) @ X23 )
        = ( k5_relat_1 @ X22 @ ( k5_relat_1 @ X21 @ X23 ) ) )
      | ~ ( v1_relat_1 @ X23 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k7_relat_1 @ X36 @ X35 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X35 ) @ X36 ) )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k5_relat_1 @ X2 @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k7_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['9','17'])).

thf('19',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('20',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('21',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ ( k6_relat_1 @ X0 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('27',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ ( k6_relat_1 @ X0 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['18','19','20','21','22','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('31',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('32',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['31'])).

thf(t77_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B )
          = B ) ) ) )).

thf('33',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X28 ) @ X29 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X29 ) @ X28 )
        = X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t77_relat_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X0 )
        = ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['30','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) ) ) @ ( k6_relat_1 @ X1 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['29','35'])).

thf('37',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k7_relat_1 @ X36 @ X35 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X35 ) @ X36 ) )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('41',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X22 @ X21 ) @ X23 )
        = ( k5_relat_1 @ X22 @ ( k5_relat_1 @ X21 @ X23 ) ) )
      | ~ ( v1_relat_1 @ X23 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('42',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_relat_1 @ X17 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['40','44'])).

thf('46',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('47',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('48',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['45','46','47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['39','49'])).

thf('51',plain,(
    ! [X32: $i] :
      ( ( ( k5_relat_1 @ X32 @ ( k6_relat_1 @ ( k2_relat_1 @ X32 ) ) )
        = X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('52',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k7_relat_1 @ X36 @ X35 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X35 ) @ X36 ) )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) ) @ X0 )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X25: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X25 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('55',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('56',plain,(
    ! [X25: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X25 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('57',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['53','54','55','56','57'])).

thf('59',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['50','58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['38','66'])).

thf('68',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('69',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['37','70'])).

thf('72',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('75',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['18','19','20','21','22','28'])).

thf('77',plain,(
    ! [X24: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X24 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('78',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X33 @ X34 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X33 ) @ X34 ) )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( k3_xboole_0 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('83',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k7_relat_1 @ X36 @ X35 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X35 ) @ X36 ) )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('84',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('85',plain,(
    ! [X25: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X25 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('86',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X30 ) @ X31 )
      | ( ( k5_relat_1 @ X30 @ ( k6_relat_1 @ X31 ) )
        = X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['84','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
        = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['83','90'])).

thf('92',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['82','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['18','19','20','21','22','28'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['82','93'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['18','19','20','21','22','28'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['36','73','74','75','76','81','94','95','96','97'])).

thf('99',plain,(
    ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
 != ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['4','98'])).

thf('100',plain,(
    $false ),
    inference(simplify,[status(thm)],['99'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.djZ92TSFNB
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:45:03 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.16/2.37  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.16/2.37  % Solved by: fo/fo7.sh
% 2.16/2.37  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.16/2.37  % done 2743 iterations in 1.917s
% 2.16/2.37  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.16/2.37  % SZS output start Refutation
% 2.16/2.37  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.16/2.37  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.16/2.37  thf(sk_A_type, type, sk_A: $i).
% 2.16/2.37  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.16/2.37  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 2.16/2.37  thf(sk_B_type, type, sk_B: $i).
% 2.16/2.37  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.16/2.37  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.16/2.37  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 2.16/2.37  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 2.16/2.37  thf(t94_relat_1, axiom,
% 2.16/2.37    (![A:$i,B:$i]:
% 2.16/2.37     ( ( v1_relat_1 @ B ) =>
% 2.16/2.37       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 2.16/2.37  thf('0', plain,
% 2.16/2.37      (![X35 : $i, X36 : $i]:
% 2.16/2.37         (((k7_relat_1 @ X36 @ X35) = (k5_relat_1 @ (k6_relat_1 @ X35) @ X36))
% 2.16/2.37          | ~ (v1_relat_1 @ X36))),
% 2.16/2.37      inference('cnf', [status(esa)], [t94_relat_1])).
% 2.16/2.37  thf(t43_funct_1, conjecture,
% 2.16/2.37    (![A:$i,B:$i]:
% 2.16/2.37     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 2.16/2.37       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 2.16/2.37  thf(zf_stmt_0, negated_conjecture,
% 2.16/2.37    (~( ![A:$i,B:$i]:
% 2.16/2.37        ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 2.16/2.37          ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 2.16/2.37    inference('cnf.neg', [status(esa)], [t43_funct_1])).
% 2.16/2.37  thf('1', plain,
% 2.16/2.37      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A))
% 2.16/2.37         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 2.16/2.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.16/2.37  thf('2', plain,
% 2.16/2.37      ((((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 2.16/2.37          != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))
% 2.16/2.37        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A)))),
% 2.16/2.37      inference('sup-', [status(thm)], ['0', '1'])).
% 2.16/2.37  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 2.16/2.37  thf('3', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 2.16/2.37      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.16/2.37  thf('4', plain,
% 2.16/2.37      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 2.16/2.37         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 2.16/2.37      inference('demod', [status(thm)], ['2', '3'])).
% 2.16/2.37  thf(t71_relat_1, axiom,
% 2.16/2.37    (![A:$i]:
% 2.16/2.37     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 2.16/2.37       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 2.16/2.37  thf('5', plain, (![X25 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X25)) = (X25))),
% 2.16/2.37      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.16/2.37  thf(t80_relat_1, axiom,
% 2.16/2.37    (![A:$i]:
% 2.16/2.37     ( ( v1_relat_1 @ A ) =>
% 2.16/2.37       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 2.16/2.37  thf('6', plain,
% 2.16/2.37      (![X32 : $i]:
% 2.16/2.37         (((k5_relat_1 @ X32 @ (k6_relat_1 @ (k2_relat_1 @ X32))) = (X32))
% 2.16/2.37          | ~ (v1_relat_1 @ X32))),
% 2.16/2.37      inference('cnf', [status(esa)], [t80_relat_1])).
% 2.16/2.37  thf('7', plain,
% 2.16/2.37      (![X0 : $i]:
% 2.16/2.37         (((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 2.16/2.37            = (k6_relat_1 @ X0))
% 2.16/2.37          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 2.16/2.37      inference('sup+', [status(thm)], ['5', '6'])).
% 2.16/2.37  thf('8', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 2.16/2.37      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.16/2.37  thf('9', plain,
% 2.16/2.37      (![X0 : $i]:
% 2.16/2.37         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 2.16/2.37           = (k6_relat_1 @ X0))),
% 2.16/2.37      inference('demod', [status(thm)], ['7', '8'])).
% 2.16/2.37  thf('10', plain,
% 2.16/2.37      (![X35 : $i, X36 : $i]:
% 2.16/2.37         (((k7_relat_1 @ X36 @ X35) = (k5_relat_1 @ (k6_relat_1 @ X35) @ X36))
% 2.16/2.37          | ~ (v1_relat_1 @ X36))),
% 2.16/2.37      inference('cnf', [status(esa)], [t94_relat_1])).
% 2.16/2.37  thf(t55_relat_1, axiom,
% 2.16/2.37    (![A:$i]:
% 2.16/2.37     ( ( v1_relat_1 @ A ) =>
% 2.16/2.37       ( ![B:$i]:
% 2.16/2.37         ( ( v1_relat_1 @ B ) =>
% 2.16/2.37           ( ![C:$i]:
% 2.16/2.37             ( ( v1_relat_1 @ C ) =>
% 2.16/2.37               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 2.16/2.37                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 2.16/2.37  thf('11', plain,
% 2.16/2.37      (![X21 : $i, X22 : $i, X23 : $i]:
% 2.16/2.37         (~ (v1_relat_1 @ X21)
% 2.16/2.37          | ((k5_relat_1 @ (k5_relat_1 @ X22 @ X21) @ X23)
% 2.16/2.37              = (k5_relat_1 @ X22 @ (k5_relat_1 @ X21 @ X23)))
% 2.16/2.37          | ~ (v1_relat_1 @ X23)
% 2.16/2.37          | ~ (v1_relat_1 @ X22))),
% 2.16/2.37      inference('cnf', [status(esa)], [t55_relat_1])).
% 2.16/2.37  thf('12', plain,
% 2.16/2.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.16/2.37         (((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 2.16/2.37            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2)))
% 2.16/2.37          | ~ (v1_relat_1 @ X1)
% 2.16/2.37          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 2.16/2.37          | ~ (v1_relat_1 @ X2)
% 2.16/2.37          | ~ (v1_relat_1 @ X1))),
% 2.16/2.37      inference('sup+', [status(thm)], ['10', '11'])).
% 2.16/2.37  thf('13', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 2.16/2.37      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.16/2.37  thf('14', plain,
% 2.16/2.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.16/2.37         (((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 2.16/2.37            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2)))
% 2.16/2.37          | ~ (v1_relat_1 @ X1)
% 2.16/2.37          | ~ (v1_relat_1 @ X2)
% 2.16/2.37          | ~ (v1_relat_1 @ X1))),
% 2.16/2.37      inference('demod', [status(thm)], ['12', '13'])).
% 2.16/2.37  thf('15', plain,
% 2.16/2.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.16/2.37         (~ (v1_relat_1 @ X2)
% 2.16/2.37          | ~ (v1_relat_1 @ X1)
% 2.16/2.37          | ((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 2.16/2.37              = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2))))),
% 2.16/2.37      inference('simplify', [status(thm)], ['14'])).
% 2.16/2.37  thf('16', plain,
% 2.16/2.37      (![X35 : $i, X36 : $i]:
% 2.16/2.37         (((k7_relat_1 @ X36 @ X35) = (k5_relat_1 @ (k6_relat_1 @ X35) @ X36))
% 2.16/2.37          | ~ (v1_relat_1 @ X36))),
% 2.16/2.37      inference('cnf', [status(esa)], [t94_relat_1])).
% 2.16/2.37  thf('17', plain,
% 2.16/2.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.16/2.37         (((k7_relat_1 @ (k5_relat_1 @ X2 @ X0) @ X1)
% 2.16/2.37            = (k5_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0))
% 2.16/2.37          | ~ (v1_relat_1 @ X2)
% 2.16/2.37          | ~ (v1_relat_1 @ X0)
% 2.16/2.37          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X0)))),
% 2.16/2.37      inference('sup+', [status(thm)], ['15', '16'])).
% 2.16/2.37  thf('18', plain,
% 2.16/2.37      (![X0 : $i, X1 : $i]:
% 2.16/2.37         (~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 2.16/2.37          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 2.16/2.37          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 2.16/2.37          | ((k7_relat_1 @ 
% 2.16/2.37              (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0)) @ X1)
% 2.16/2.37              = (k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1) @ 
% 2.16/2.37                 (k6_relat_1 @ X0))))),
% 2.16/2.37      inference('sup-', [status(thm)], ['9', '17'])).
% 2.16/2.37  thf('19', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 2.16/2.37      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.16/2.37  thf('20', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 2.16/2.37      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.16/2.37  thf('21', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 2.16/2.37      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.16/2.37  thf('22', plain,
% 2.16/2.37      (![X0 : $i]:
% 2.16/2.37         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 2.16/2.37           = (k6_relat_1 @ X0))),
% 2.16/2.37      inference('demod', [status(thm)], ['7', '8'])).
% 2.16/2.37  thf('23', plain,
% 2.16/2.37      (![X0 : $i]:
% 2.16/2.37         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 2.16/2.37           = (k6_relat_1 @ X0))),
% 2.16/2.37      inference('demod', [status(thm)], ['7', '8'])).
% 2.16/2.37  thf('24', plain,
% 2.16/2.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.16/2.37         (~ (v1_relat_1 @ X2)
% 2.16/2.37          | ~ (v1_relat_1 @ X1)
% 2.16/2.37          | ((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 2.16/2.37              = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2))))),
% 2.16/2.37      inference('simplify', [status(thm)], ['14'])).
% 2.16/2.37  thf('25', plain,
% 2.16/2.37      (![X0 : $i, X1 : $i]:
% 2.16/2.37         (((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1) @ 
% 2.16/2.37            (k6_relat_1 @ X0))
% 2.16/2.37            = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))
% 2.16/2.37          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 2.16/2.37          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 2.16/2.37      inference('sup+', [status(thm)], ['23', '24'])).
% 2.16/2.37  thf('26', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 2.16/2.37      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.16/2.37  thf('27', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 2.16/2.37      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.16/2.37  thf('28', plain,
% 2.16/2.37      (![X0 : $i, X1 : $i]:
% 2.16/2.37         ((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1) @ 
% 2.16/2.37           (k6_relat_1 @ X0))
% 2.16/2.37           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 2.16/2.37      inference('demod', [status(thm)], ['25', '26', '27'])).
% 2.16/2.37  thf('29', plain,
% 2.16/2.37      (![X0 : $i, X1 : $i]:
% 2.16/2.37         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 2.16/2.37           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 2.16/2.37      inference('demod', [status(thm)], ['18', '19', '20', '21', '22', '28'])).
% 2.16/2.37  thf('30', plain,
% 2.16/2.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.16/2.37         (~ (v1_relat_1 @ X2)
% 2.16/2.37          | ~ (v1_relat_1 @ X1)
% 2.16/2.37          | ((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 2.16/2.37              = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2))))),
% 2.16/2.37      inference('simplify', [status(thm)], ['14'])).
% 2.16/2.37  thf(d10_xboole_0, axiom,
% 2.16/2.37    (![A:$i,B:$i]:
% 2.16/2.37     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.16/2.37  thf('31', plain,
% 2.16/2.37      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 2.16/2.37      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.16/2.37  thf('32', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 2.16/2.37      inference('simplify', [status(thm)], ['31'])).
% 2.16/2.37  thf(t77_relat_1, axiom,
% 2.16/2.37    (![A:$i,B:$i]:
% 2.16/2.37     ( ( v1_relat_1 @ B ) =>
% 2.16/2.37       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 2.16/2.37         ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ) ))).
% 2.16/2.37  thf('33', plain,
% 2.16/2.37      (![X28 : $i, X29 : $i]:
% 2.16/2.37         (~ (r1_tarski @ (k1_relat_1 @ X28) @ X29)
% 2.16/2.37          | ((k5_relat_1 @ (k6_relat_1 @ X29) @ X28) = (X28))
% 2.16/2.37          | ~ (v1_relat_1 @ X28))),
% 2.16/2.37      inference('cnf', [status(esa)], [t77_relat_1])).
% 2.16/2.37  thf('34', plain,
% 2.16/2.37      (![X0 : $i]:
% 2.16/2.37         (~ (v1_relat_1 @ X0)
% 2.16/2.37          | ((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X0) = (X0)))),
% 2.16/2.37      inference('sup-', [status(thm)], ['32', '33'])).
% 2.16/2.37  thf('35', plain,
% 2.16/2.37      (![X0 : $i, X1 : $i]:
% 2.16/2.37         (((k5_relat_1 @ 
% 2.16/2.37            (k7_relat_1 @ X1 @ (k1_relat_1 @ (k5_relat_1 @ X1 @ X0))) @ X0)
% 2.16/2.37            = (k5_relat_1 @ X1 @ X0))
% 2.16/2.37          | ~ (v1_relat_1 @ X1)
% 2.16/2.37          | ~ (v1_relat_1 @ X0)
% 2.16/2.37          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0)))),
% 2.16/2.37      inference('sup+', [status(thm)], ['30', '34'])).
% 2.16/2.37  thf('36', plain,
% 2.16/2.37      (![X0 : $i, X1 : $i]:
% 2.16/2.37         (~ (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 2.16/2.37          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 2.16/2.37          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 2.16/2.37          | ((k5_relat_1 @ 
% 2.16/2.37              (k7_relat_1 @ (k6_relat_1 @ X0) @ 
% 2.16/2.37               (k1_relat_1 @ 
% 2.16/2.37                (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1)))) @ 
% 2.16/2.37              (k6_relat_1 @ X1))
% 2.16/2.37              = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))))),
% 2.16/2.37      inference('sup-', [status(thm)], ['29', '35'])).
% 2.16/2.37  thf('37', plain,
% 2.16/2.37      (![X35 : $i, X36 : $i]:
% 2.16/2.37         (((k7_relat_1 @ X36 @ X35) = (k5_relat_1 @ (k6_relat_1 @ X35) @ X36))
% 2.16/2.37          | ~ (v1_relat_1 @ X36))),
% 2.16/2.37      inference('cnf', [status(esa)], [t94_relat_1])).
% 2.16/2.37  thf('38', plain,
% 2.16/2.37      (![X0 : $i]:
% 2.16/2.37         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 2.16/2.37           = (k6_relat_1 @ X0))),
% 2.16/2.37      inference('demod', [status(thm)], ['7', '8'])).
% 2.16/2.37  thf('39', plain,
% 2.16/2.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.16/2.37         (~ (v1_relat_1 @ X2)
% 2.16/2.37          | ~ (v1_relat_1 @ X1)
% 2.16/2.37          | ((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 2.16/2.37              = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2))))),
% 2.16/2.37      inference('simplify', [status(thm)], ['14'])).
% 2.16/2.37  thf('40', plain,
% 2.16/2.37      (![X0 : $i]:
% 2.16/2.37         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 2.16/2.37           = (k6_relat_1 @ X0))),
% 2.16/2.37      inference('demod', [status(thm)], ['7', '8'])).
% 2.16/2.37  thf('41', plain,
% 2.16/2.37      (![X21 : $i, X22 : $i, X23 : $i]:
% 2.16/2.37         (~ (v1_relat_1 @ X21)
% 2.16/2.37          | ((k5_relat_1 @ (k5_relat_1 @ X22 @ X21) @ X23)
% 2.16/2.37              = (k5_relat_1 @ X22 @ (k5_relat_1 @ X21 @ X23)))
% 2.16/2.37          | ~ (v1_relat_1 @ X23)
% 2.16/2.37          | ~ (v1_relat_1 @ X22))),
% 2.16/2.37      inference('cnf', [status(esa)], [t55_relat_1])).
% 2.16/2.37  thf(dt_k5_relat_1, axiom,
% 2.16/2.37    (![A:$i,B:$i]:
% 2.16/2.37     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 2.16/2.37       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 2.16/2.37  thf('42', plain,
% 2.16/2.37      (![X16 : $i, X17 : $i]:
% 2.16/2.37         (~ (v1_relat_1 @ X16)
% 2.16/2.37          | ~ (v1_relat_1 @ X17)
% 2.16/2.37          | (v1_relat_1 @ (k5_relat_1 @ X16 @ X17)))),
% 2.16/2.37      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 2.16/2.37  thf('43', plain,
% 2.16/2.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.16/2.37         ((v1_relat_1 @ (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0)))
% 2.16/2.37          | ~ (v1_relat_1 @ X2)
% 2.16/2.37          | ~ (v1_relat_1 @ X0)
% 2.16/2.37          | ~ (v1_relat_1 @ X1)
% 2.16/2.37          | ~ (v1_relat_1 @ X0)
% 2.16/2.37          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1)))),
% 2.16/2.37      inference('sup+', [status(thm)], ['41', '42'])).
% 2.16/2.37  thf('44', plain,
% 2.16/2.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.16/2.37         (~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1))
% 2.16/2.37          | ~ (v1_relat_1 @ X1)
% 2.16/2.37          | ~ (v1_relat_1 @ X0)
% 2.16/2.37          | ~ (v1_relat_1 @ X2)
% 2.16/2.37          | (v1_relat_1 @ (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0))))),
% 2.16/2.37      inference('simplify', [status(thm)], ['43'])).
% 2.16/2.37  thf('45', plain,
% 2.16/2.37      (![X0 : $i, X1 : $i]:
% 2.16/2.37         (~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 2.16/2.37          | (v1_relat_1 @ 
% 2.16/2.37             (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 2.16/2.37              (k5_relat_1 @ (k6_relat_1 @ X0) @ X1)))
% 2.16/2.37          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 2.16/2.37          | ~ (v1_relat_1 @ X1)
% 2.16/2.37          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 2.16/2.37      inference('sup-', [status(thm)], ['40', '44'])).
% 2.16/2.37  thf('46', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 2.16/2.37      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.16/2.37  thf('47', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 2.16/2.37      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.16/2.37  thf('48', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 2.16/2.37      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.16/2.37  thf('49', plain,
% 2.16/2.37      (![X0 : $i, X1 : $i]:
% 2.16/2.37         ((v1_relat_1 @ 
% 2.16/2.37           (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 2.16/2.37            (k5_relat_1 @ (k6_relat_1 @ X0) @ X1)))
% 2.16/2.37          | ~ (v1_relat_1 @ X1))),
% 2.16/2.37      inference('demod', [status(thm)], ['45', '46', '47', '48'])).
% 2.16/2.37  thf('50', plain,
% 2.16/2.37      (![X0 : $i, X1 : $i]:
% 2.16/2.37         ((v1_relat_1 @ 
% 2.16/2.37           (k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X1) @ X0))
% 2.16/2.37          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 2.16/2.37          | ~ (v1_relat_1 @ X0)
% 2.16/2.37          | ~ (v1_relat_1 @ X0))),
% 2.16/2.37      inference('sup+', [status(thm)], ['39', '49'])).
% 2.16/2.37  thf('51', plain,
% 2.16/2.37      (![X32 : $i]:
% 2.16/2.37         (((k5_relat_1 @ X32 @ (k6_relat_1 @ (k2_relat_1 @ X32))) = (X32))
% 2.16/2.37          | ~ (v1_relat_1 @ X32))),
% 2.16/2.37      inference('cnf', [status(esa)], [t80_relat_1])).
% 2.16/2.37  thf('52', plain,
% 2.16/2.37      (![X35 : $i, X36 : $i]:
% 2.16/2.37         (((k7_relat_1 @ X36 @ X35) = (k5_relat_1 @ (k6_relat_1 @ X35) @ X36))
% 2.16/2.37          | ~ (v1_relat_1 @ X36))),
% 2.16/2.37      inference('cnf', [status(esa)], [t94_relat_1])).
% 2.16/2.37  thf('53', plain,
% 2.16/2.37      (![X0 : $i]:
% 2.16/2.37         (((k7_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ (k6_relat_1 @ X0))) @ X0)
% 2.16/2.37            = (k6_relat_1 @ X0))
% 2.16/2.37          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 2.16/2.37          | ~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ (k6_relat_1 @ X0)))))),
% 2.16/2.37      inference('sup+', [status(thm)], ['51', '52'])).
% 2.16/2.37  thf('54', plain, (![X25 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X25)) = (X25))),
% 2.16/2.37      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.16/2.37  thf('55', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 2.16/2.37      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.16/2.37  thf('56', plain, (![X25 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X25)) = (X25))),
% 2.16/2.37      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.16/2.37  thf('57', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 2.16/2.37      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.16/2.37  thf('58', plain,
% 2.16/2.37      (![X0 : $i]: ((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 2.16/2.37      inference('demod', [status(thm)], ['53', '54', '55', '56', '57'])).
% 2.16/2.37  thf('59', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 2.16/2.37      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.16/2.37  thf('60', plain,
% 2.16/2.37      (![X0 : $i, X1 : $i]:
% 2.16/2.37         ((v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 2.16/2.37          | ~ (v1_relat_1 @ X0)
% 2.16/2.37          | ~ (v1_relat_1 @ X0))),
% 2.16/2.37      inference('demod', [status(thm)], ['50', '58', '59'])).
% 2.16/2.37  thf('61', plain,
% 2.16/2.37      (![X0 : $i, X1 : $i]:
% 2.16/2.37         (~ (v1_relat_1 @ X0)
% 2.16/2.37          | (v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 2.16/2.37      inference('simplify', [status(thm)], ['60'])).
% 2.16/2.37  thf('62', plain,
% 2.16/2.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.16/2.37         (~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1))
% 2.16/2.37          | ~ (v1_relat_1 @ X1)
% 2.16/2.37          | ~ (v1_relat_1 @ X0)
% 2.16/2.37          | ~ (v1_relat_1 @ X2)
% 2.16/2.37          | (v1_relat_1 @ (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0))))),
% 2.16/2.37      inference('simplify', [status(thm)], ['43'])).
% 2.16/2.37  thf('63', plain,
% 2.16/2.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.16/2.37         (~ (v1_relat_1 @ X0)
% 2.16/2.37          | (v1_relat_1 @ 
% 2.16/2.37             (k5_relat_1 @ (k6_relat_1 @ X1) @ (k5_relat_1 @ X0 @ X2)))
% 2.16/2.37          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 2.16/2.37          | ~ (v1_relat_1 @ X2)
% 2.16/2.37          | ~ (v1_relat_1 @ X0))),
% 2.16/2.37      inference('sup-', [status(thm)], ['61', '62'])).
% 2.16/2.37  thf('64', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 2.16/2.37      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.16/2.37  thf('65', plain,
% 2.16/2.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.16/2.37         (~ (v1_relat_1 @ X0)
% 2.16/2.37          | (v1_relat_1 @ 
% 2.16/2.37             (k5_relat_1 @ (k6_relat_1 @ X1) @ (k5_relat_1 @ X0 @ X2)))
% 2.16/2.37          | ~ (v1_relat_1 @ X2)
% 2.16/2.37          | ~ (v1_relat_1 @ X0))),
% 2.16/2.37      inference('demod', [status(thm)], ['63', '64'])).
% 2.16/2.37  thf('66', plain,
% 2.16/2.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.16/2.37         (~ (v1_relat_1 @ X2)
% 2.16/2.37          | (v1_relat_1 @ 
% 2.16/2.37             (k5_relat_1 @ (k6_relat_1 @ X1) @ (k5_relat_1 @ X0 @ X2)))
% 2.16/2.37          | ~ (v1_relat_1 @ X0))),
% 2.16/2.37      inference('simplify', [status(thm)], ['65'])).
% 2.16/2.37  thf('67', plain,
% 2.16/2.37      (![X0 : $i, X1 : $i]:
% 2.16/2.37         ((v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))
% 2.16/2.37          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 2.16/2.37          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 2.16/2.37      inference('sup+', [status(thm)], ['38', '66'])).
% 2.16/2.37  thf('68', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 2.16/2.37      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.16/2.37  thf('69', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 2.16/2.37      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.16/2.37  thf('70', plain,
% 2.16/2.37      (![X0 : $i, X1 : $i]:
% 2.16/2.37         (v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 2.16/2.37      inference('demod', [status(thm)], ['67', '68', '69'])).
% 2.16/2.37  thf('71', plain,
% 2.16/2.37      (![X0 : $i, X1 : $i]:
% 2.16/2.37         ((v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 2.16/2.37          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 2.16/2.37      inference('sup+', [status(thm)], ['37', '70'])).
% 2.16/2.37  thf('72', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 2.16/2.37      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.16/2.37  thf('73', plain,
% 2.16/2.37      (![X0 : $i, X1 : $i]:
% 2.16/2.37         (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 2.16/2.37      inference('demod', [status(thm)], ['71', '72'])).
% 2.16/2.37  thf('74', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 2.16/2.37      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.16/2.37  thf('75', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 2.16/2.37      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.16/2.37  thf('76', plain,
% 2.16/2.37      (![X0 : $i, X1 : $i]:
% 2.16/2.37         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 2.16/2.37           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 2.16/2.37      inference('demod', [status(thm)], ['18', '19', '20', '21', '22', '28'])).
% 2.16/2.37  thf('77', plain, (![X24 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X24)) = (X24))),
% 2.16/2.37      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.16/2.37  thf(t90_relat_1, axiom,
% 2.16/2.37    (![A:$i,B:$i]:
% 2.16/2.37     ( ( v1_relat_1 @ B ) =>
% 2.16/2.37       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 2.16/2.37         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 2.16/2.37  thf('78', plain,
% 2.16/2.37      (![X33 : $i, X34 : $i]:
% 2.16/2.37         (((k1_relat_1 @ (k7_relat_1 @ X33 @ X34))
% 2.16/2.37            = (k3_xboole_0 @ (k1_relat_1 @ X33) @ X34))
% 2.16/2.37          | ~ (v1_relat_1 @ X33))),
% 2.16/2.37      inference('cnf', [status(esa)], [t90_relat_1])).
% 2.16/2.37  thf('79', plain,
% 2.16/2.37      (![X0 : $i, X1 : $i]:
% 2.16/2.37         (((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 2.16/2.37            = (k3_xboole_0 @ X0 @ X1))
% 2.16/2.37          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 2.16/2.37      inference('sup+', [status(thm)], ['77', '78'])).
% 2.16/2.37  thf('80', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 2.16/2.37      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.16/2.37  thf('81', plain,
% 2.16/2.37      (![X0 : $i, X1 : $i]:
% 2.16/2.37         ((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 2.16/2.37           = (k3_xboole_0 @ X0 @ X1))),
% 2.16/2.37      inference('demod', [status(thm)], ['79', '80'])).
% 2.16/2.37  thf(commutativity_k3_xboole_0, axiom,
% 2.16/2.37    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 2.16/2.37  thf('82', plain,
% 2.16/2.37      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.16/2.37      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.16/2.37  thf('83', plain,
% 2.16/2.37      (![X35 : $i, X36 : $i]:
% 2.16/2.37         (((k7_relat_1 @ X36 @ X35) = (k5_relat_1 @ (k6_relat_1 @ X35) @ X36))
% 2.16/2.37          | ~ (v1_relat_1 @ X36))),
% 2.16/2.37      inference('cnf', [status(esa)], [t94_relat_1])).
% 2.16/2.37  thf(t17_xboole_1, axiom,
% 2.16/2.37    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 2.16/2.37  thf('84', plain,
% 2.16/2.37      (![X5 : $i, X6 : $i]: (r1_tarski @ (k3_xboole_0 @ X5 @ X6) @ X5)),
% 2.16/2.37      inference('cnf', [status(esa)], [t17_xboole_1])).
% 2.16/2.37  thf('85', plain, (![X25 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X25)) = (X25))),
% 2.16/2.37      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.16/2.37  thf(t79_relat_1, axiom,
% 2.16/2.37    (![A:$i,B:$i]:
% 2.16/2.37     ( ( v1_relat_1 @ B ) =>
% 2.16/2.37       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 2.16/2.37         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 2.16/2.37  thf('86', plain,
% 2.16/2.37      (![X30 : $i, X31 : $i]:
% 2.16/2.37         (~ (r1_tarski @ (k2_relat_1 @ X30) @ X31)
% 2.16/2.37          | ((k5_relat_1 @ X30 @ (k6_relat_1 @ X31)) = (X30))
% 2.16/2.37          | ~ (v1_relat_1 @ X30))),
% 2.16/2.37      inference('cnf', [status(esa)], [t79_relat_1])).
% 2.16/2.37  thf('87', plain,
% 2.16/2.37      (![X0 : $i, X1 : $i]:
% 2.16/2.37         (~ (r1_tarski @ X0 @ X1)
% 2.16/2.37          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 2.16/2.37          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 2.16/2.37              = (k6_relat_1 @ X0)))),
% 2.16/2.37      inference('sup-', [status(thm)], ['85', '86'])).
% 2.16/2.37  thf('88', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 2.16/2.37      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.16/2.37  thf('89', plain,
% 2.16/2.37      (![X0 : $i, X1 : $i]:
% 2.16/2.37         (~ (r1_tarski @ X0 @ X1)
% 2.16/2.37          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 2.16/2.37              = (k6_relat_1 @ X0)))),
% 2.16/2.37      inference('demod', [status(thm)], ['87', '88'])).
% 2.16/2.37  thf('90', plain,
% 2.16/2.37      (![X0 : $i, X1 : $i]:
% 2.16/2.37         ((k5_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 2.16/2.37           (k6_relat_1 @ X0)) = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 2.16/2.37      inference('sup-', [status(thm)], ['84', '89'])).
% 2.16/2.37  thf('91', plain,
% 2.16/2.37      (![X0 : $i, X1 : $i]:
% 2.16/2.37         (((k7_relat_1 @ (k6_relat_1 @ X1) @ (k3_xboole_0 @ X1 @ X0))
% 2.16/2.37            = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 2.16/2.37          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 2.16/2.37      inference('sup+', [status(thm)], ['83', '90'])).
% 2.16/2.37  thf('92', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 2.16/2.37      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.16/2.37  thf('93', plain,
% 2.16/2.37      (![X0 : $i, X1 : $i]:
% 2.16/2.37         ((k7_relat_1 @ (k6_relat_1 @ X1) @ (k3_xboole_0 @ X1 @ X0))
% 2.16/2.37           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 2.16/2.37      inference('demod', [status(thm)], ['91', '92'])).
% 2.16/2.37  thf('94', plain,
% 2.16/2.37      (![X0 : $i, X1 : $i]:
% 2.16/2.37         ((k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 2.16/2.37           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 2.16/2.37      inference('sup+', [status(thm)], ['82', '93'])).
% 2.16/2.37  thf('95', plain,
% 2.16/2.37      (![X0 : $i, X1 : $i]:
% 2.16/2.37         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 2.16/2.37           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 2.16/2.37      inference('demod', [status(thm)], ['18', '19', '20', '21', '22', '28'])).
% 2.16/2.37  thf('96', plain,
% 2.16/2.37      (![X0 : $i, X1 : $i]:
% 2.16/2.37         ((k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 2.16/2.37           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 2.16/2.37      inference('sup+', [status(thm)], ['82', '93'])).
% 2.16/2.37  thf('97', plain,
% 2.16/2.37      (![X0 : $i, X1 : $i]:
% 2.16/2.37         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 2.16/2.37           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 2.16/2.37      inference('demod', [status(thm)], ['18', '19', '20', '21', '22', '28'])).
% 2.16/2.37  thf('98', plain,
% 2.16/2.37      (![X0 : $i, X1 : $i]:
% 2.16/2.37         ((k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))
% 2.16/2.37           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 2.16/2.37      inference('demod', [status(thm)],
% 2.16/2.37                ['36', '73', '74', '75', '76', '81', '94', '95', '96', '97'])).
% 2.16/2.37  thf('99', plain,
% 2.16/2.37      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 2.16/2.37         != (k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))),
% 2.16/2.37      inference('demod', [status(thm)], ['4', '98'])).
% 2.16/2.37  thf('100', plain, ($false), inference('simplify', [status(thm)], ['99'])).
% 2.16/2.37  
% 2.16/2.37  % SZS output end Refutation
% 2.16/2.37  
% 2.16/2.38  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
