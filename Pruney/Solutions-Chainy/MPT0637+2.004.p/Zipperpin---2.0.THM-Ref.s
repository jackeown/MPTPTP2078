%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mgbxeBMHGE

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:55 EST 2020

% Result     : Theorem 7.90s
% Output     : Refutation 7.90s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 868 expanded)
%              Number of leaves         :   21 ( 297 expanded)
%              Depth                    :   22
%              Number of atoms          : 1392 (7868 expanded)
%              Number of equality atoms :   78 ( 591 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('0',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k7_relat_1 @ X29 @ X28 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X28 ) @ X29 ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
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
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('4',plain,(
    ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t192_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k7_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ) )).

thf('5',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k7_relat_1 @ X17 @ X18 )
        = ( k7_relat_1 @ X17 @ ( k3_xboole_0 @ ( k1_relat_1 @ X17 ) @ X18 ) ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t192_relat_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('6',plain,(
    ! [X22: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X22 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('8',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['7'])).

thf(t77_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B )
          = B ) ) ) )).

thf('9',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X26 ) @ X27 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X27 ) @ X26 )
        = X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t77_relat_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','10'])).

thf('12',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k7_relat_1 @ X29 @ X28 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X28 ) @ X29 ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
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

thf('15',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X20 @ X19 ) @ X21 )
        = ( k5_relat_1 @ X20 @ ( k5_relat_1 @ X19 @ X21 ) ) )
      | ~ ( v1_relat_1 @ X21 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ ( k6_relat_1 @ X0 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','19'])).

thf('21',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('22',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ ( k6_relat_1 @ X0 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ ( k1_relat_1 @ ( k6_relat_1 @ X1 ) ) @ X0 ) ) @ ( k6_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['5','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ ( k6_relat_1 @ X0 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('26',plain,(
    ! [X22: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X22 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('27',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['24','25','26','27'])).

thf(t76_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B )
        & ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ) )).

thf('29',plain,(
    ! [X24: $i,X25: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X24 @ ( k6_relat_1 @ X25 ) ) @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t76_relat_1])).

thf('30',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      | ( X0
        = ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      | ( ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['24','25','26','27'])).

thf('34',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      | ( ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k7_relat_1 @ X29 @ X28 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X28 ) @ X29 ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['24','25','26','27'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X22: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X22 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('40',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k7_relat_1 @ X17 @ X18 )
        = ( k7_relat_1 @ X17 @ ( k3_xboole_0 @ ( k1_relat_1 @ X17 ) @ X18 ) ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t192_relat_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['38','43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['38','43','44'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ( ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) )
        = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['35','45','46'])).

thf('48',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k7_relat_1 @ X29 @ X28 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X28 ) @ X29 ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('56',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X20 @ X19 ) @ X21 )
        = ( k5_relat_1 @ X20 @ ( k5_relat_1 @ X19 @ X21 ) ) )
      | ~ ( v1_relat_1 @ X21 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('57',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_relat_1 @ X12 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['55','59'])).

thf('61',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('62',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('63',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['60','61','62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['54','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('67',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['53','74'])).

thf('76',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('77',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('79',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X20 @ X19 ) @ X21 )
        = ( k5_relat_1 @ X20 @ ( k5_relat_1 @ X19 @ X21 ) ) )
      | ~ ( v1_relat_1 @ X21 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('80',plain,(
    ! [X24: $i,X25: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X24 @ ( k6_relat_1 @ X25 ) ) @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t76_relat_1])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X2 ) ) ) @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['78','83'])).

thf('85',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('86',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('87',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X2 ) ) ) @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['84','85','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['38','43','44'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ ( k6_relat_1 @ X0 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['38','43','44'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ ( k6_relat_1 @ X0 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X2 ) @ ( k6_relat_1 @ X1 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf(t100_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('95',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X14 @ X15 ) @ X16 )
        = ( k7_relat_1 @ X14 @ ( k3_xboole_0 @ X15 @ X16 ) ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('96',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X14 @ X15 ) @ X16 )
        = ( k7_relat_1 @ X14 @ ( k3_xboole_0 @ X15 @ X16 ) ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('97',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X3 )
        = ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ ( k3_xboole_0 @ X0 @ X3 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k7_relat_1 @ X29 @ X28 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X28 ) @ X29 ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('99',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_relat_1 @ X12 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X3 )
        = ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ ( k3_xboole_0 @ X0 @ X3 ) ) ) ) ),
    inference(clc,[status(thm)],['97','103'])).

thf('105',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X2 )
        = ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X1 ) @ ( k3_xboole_0 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['94','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('107',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('108',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X2 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k3_xboole_0 @ X0 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['105','106','107'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ ( k6_relat_1 @ X0 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('116',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k3_xboole_0 @ X0 @ X2 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['93','108','109','114','115'])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['38','43','44'])).

thf('118',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k7_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['87','88','116','117'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['52','118'])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['47','119'])).

thf('121',plain,(
    ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','120'])).

thf('122',plain,(
    $false ),
    inference(simplify,[status(thm)],['121'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mgbxeBMHGE
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:32:00 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 7.90/8.13  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 7.90/8.13  % Solved by: fo/fo7.sh
% 7.90/8.13  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 7.90/8.13  % done 4449 iterations in 7.680s
% 7.90/8.13  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 7.90/8.13  % SZS output start Refutation
% 7.90/8.13  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 7.90/8.13  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 7.90/8.13  thf(sk_B_type, type, sk_B: $i).
% 7.90/8.13  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 7.90/8.13  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 7.90/8.13  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 7.90/8.13  thf(sk_A_type, type, sk_A: $i).
% 7.90/8.13  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 7.90/8.13  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 7.90/8.13  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 7.90/8.13  thf(t94_relat_1, axiom,
% 7.90/8.13    (![A:$i,B:$i]:
% 7.90/8.13     ( ( v1_relat_1 @ B ) =>
% 7.90/8.13       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 7.90/8.13  thf('0', plain,
% 7.90/8.13      (![X28 : $i, X29 : $i]:
% 7.90/8.13         (((k7_relat_1 @ X29 @ X28) = (k5_relat_1 @ (k6_relat_1 @ X28) @ X29))
% 7.90/8.13          | ~ (v1_relat_1 @ X29))),
% 7.90/8.13      inference('cnf', [status(esa)], [t94_relat_1])).
% 7.90/8.13  thf(t43_funct_1, conjecture,
% 7.90/8.13    (![A:$i,B:$i]:
% 7.90/8.13     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 7.90/8.13       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 7.90/8.13  thf(zf_stmt_0, negated_conjecture,
% 7.90/8.13    (~( ![A:$i,B:$i]:
% 7.90/8.13        ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 7.90/8.13          ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 7.90/8.13    inference('cnf.neg', [status(esa)], [t43_funct_1])).
% 7.90/8.13  thf('1', plain,
% 7.90/8.13      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A))
% 7.90/8.13         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 7.90/8.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.90/8.13  thf('2', plain,
% 7.90/8.13      ((((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 7.90/8.13          != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))
% 7.90/8.13        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A)))),
% 7.90/8.13      inference('sup-', [status(thm)], ['0', '1'])).
% 7.90/8.13  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 7.90/8.13  thf('3', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 7.90/8.13      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 7.90/8.13  thf('4', plain,
% 7.90/8.13      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 7.90/8.13         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 7.90/8.13      inference('demod', [status(thm)], ['2', '3'])).
% 7.90/8.13  thf(t192_relat_1, axiom,
% 7.90/8.13    (![A:$i,B:$i]:
% 7.90/8.13     ( ( v1_relat_1 @ B ) =>
% 7.90/8.13       ( ( k7_relat_1 @ B @ A ) =
% 7.90/8.13         ( k7_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ))).
% 7.90/8.13  thf('5', plain,
% 7.90/8.13      (![X17 : $i, X18 : $i]:
% 7.90/8.13         (((k7_relat_1 @ X17 @ X18)
% 7.90/8.13            = (k7_relat_1 @ X17 @ (k3_xboole_0 @ (k1_relat_1 @ X17) @ X18)))
% 7.90/8.13          | ~ (v1_relat_1 @ X17))),
% 7.90/8.13      inference('cnf', [status(esa)], [t192_relat_1])).
% 7.90/8.13  thf(t71_relat_1, axiom,
% 7.90/8.13    (![A:$i]:
% 7.90/8.13     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 7.90/8.13       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 7.90/8.13  thf('6', plain, (![X22 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X22)) = (X22))),
% 7.90/8.13      inference('cnf', [status(esa)], [t71_relat_1])).
% 7.90/8.13  thf(d10_xboole_0, axiom,
% 7.90/8.13    (![A:$i,B:$i]:
% 7.90/8.13     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 7.90/8.13  thf('7', plain,
% 7.90/8.13      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 7.90/8.13      inference('cnf', [status(esa)], [d10_xboole_0])).
% 7.90/8.13  thf('8', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 7.90/8.13      inference('simplify', [status(thm)], ['7'])).
% 7.90/8.13  thf(t77_relat_1, axiom,
% 7.90/8.13    (![A:$i,B:$i]:
% 7.90/8.13     ( ( v1_relat_1 @ B ) =>
% 7.90/8.13       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 7.90/8.13         ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ) ))).
% 7.90/8.13  thf('9', plain,
% 7.90/8.13      (![X26 : $i, X27 : $i]:
% 7.90/8.13         (~ (r1_tarski @ (k1_relat_1 @ X26) @ X27)
% 7.90/8.13          | ((k5_relat_1 @ (k6_relat_1 @ X27) @ X26) = (X26))
% 7.90/8.13          | ~ (v1_relat_1 @ X26))),
% 7.90/8.13      inference('cnf', [status(esa)], [t77_relat_1])).
% 7.90/8.13  thf('10', plain,
% 7.90/8.13      (![X0 : $i]:
% 7.90/8.13         (~ (v1_relat_1 @ X0)
% 7.90/8.13          | ((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X0) = (X0)))),
% 7.90/8.13      inference('sup-', [status(thm)], ['8', '9'])).
% 7.90/8.13  thf('11', plain,
% 7.90/8.13      (![X0 : $i]:
% 7.90/8.13         (((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 7.90/8.13            = (k6_relat_1 @ X0))
% 7.90/8.13          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 7.90/8.13      inference('sup+', [status(thm)], ['6', '10'])).
% 7.90/8.13  thf('12', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 7.90/8.13      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 7.90/8.13  thf('13', plain,
% 7.90/8.13      (![X0 : $i]:
% 7.90/8.13         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 7.90/8.13           = (k6_relat_1 @ X0))),
% 7.90/8.13      inference('demod', [status(thm)], ['11', '12'])).
% 7.90/8.13  thf('14', plain,
% 7.90/8.13      (![X28 : $i, X29 : $i]:
% 7.90/8.13         (((k7_relat_1 @ X29 @ X28) = (k5_relat_1 @ (k6_relat_1 @ X28) @ X29))
% 7.90/8.13          | ~ (v1_relat_1 @ X29))),
% 7.90/8.13      inference('cnf', [status(esa)], [t94_relat_1])).
% 7.90/8.13  thf(t55_relat_1, axiom,
% 7.90/8.13    (![A:$i]:
% 7.90/8.13     ( ( v1_relat_1 @ A ) =>
% 7.90/8.13       ( ![B:$i]:
% 7.90/8.13         ( ( v1_relat_1 @ B ) =>
% 7.90/8.13           ( ![C:$i]:
% 7.90/8.13             ( ( v1_relat_1 @ C ) =>
% 7.90/8.13               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 7.90/8.13                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 7.90/8.13  thf('15', plain,
% 7.90/8.13      (![X19 : $i, X20 : $i, X21 : $i]:
% 7.90/8.13         (~ (v1_relat_1 @ X19)
% 7.90/8.13          | ((k5_relat_1 @ (k5_relat_1 @ X20 @ X19) @ X21)
% 7.90/8.13              = (k5_relat_1 @ X20 @ (k5_relat_1 @ X19 @ X21)))
% 7.90/8.13          | ~ (v1_relat_1 @ X21)
% 7.90/8.13          | ~ (v1_relat_1 @ X20))),
% 7.90/8.13      inference('cnf', [status(esa)], [t55_relat_1])).
% 7.90/8.13  thf('16', plain,
% 7.90/8.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.90/8.13         (((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 7.90/8.13            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2)))
% 7.90/8.13          | ~ (v1_relat_1 @ X1)
% 7.90/8.13          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 7.90/8.13          | ~ (v1_relat_1 @ X2)
% 7.90/8.13          | ~ (v1_relat_1 @ X1))),
% 7.90/8.13      inference('sup+', [status(thm)], ['14', '15'])).
% 7.90/8.13  thf('17', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 7.90/8.13      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 7.90/8.13  thf('18', plain,
% 7.90/8.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.90/8.13         (((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 7.90/8.13            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2)))
% 7.90/8.13          | ~ (v1_relat_1 @ X1)
% 7.90/8.13          | ~ (v1_relat_1 @ X2)
% 7.90/8.13          | ~ (v1_relat_1 @ X1))),
% 7.90/8.13      inference('demod', [status(thm)], ['16', '17'])).
% 7.90/8.13  thf('19', plain,
% 7.90/8.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.90/8.13         (~ (v1_relat_1 @ X2)
% 7.90/8.13          | ~ (v1_relat_1 @ X1)
% 7.90/8.13          | ((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 7.90/8.13              = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2))))),
% 7.90/8.13      inference('simplify', [status(thm)], ['18'])).
% 7.90/8.13  thf('20', plain,
% 7.90/8.13      (![X0 : $i, X1 : $i]:
% 7.90/8.13         (((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1) @ 
% 7.90/8.13            (k6_relat_1 @ X0))
% 7.90/8.13            = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))
% 7.90/8.13          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 7.90/8.13          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 7.90/8.13      inference('sup+', [status(thm)], ['13', '19'])).
% 7.90/8.13  thf('21', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 7.90/8.13      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 7.90/8.13  thf('22', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 7.90/8.13      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 7.90/8.13  thf('23', plain,
% 7.90/8.13      (![X0 : $i, X1 : $i]:
% 7.90/8.13         ((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1) @ 
% 7.90/8.13           (k6_relat_1 @ X0))
% 7.90/8.13           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 7.90/8.13      inference('demod', [status(thm)], ['20', '21', '22'])).
% 7.90/8.13  thf('24', plain,
% 7.90/8.13      (![X0 : $i, X1 : $i]:
% 7.90/8.13         (((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 7.90/8.13            (k6_relat_1 @ X1))
% 7.90/8.13            = (k5_relat_1 @ 
% 7.90/8.13               (k6_relat_1 @ 
% 7.90/8.13                (k3_xboole_0 @ (k1_relat_1 @ (k6_relat_1 @ X1)) @ X0)) @ 
% 7.90/8.13               (k6_relat_1 @ X1)))
% 7.90/8.13          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 7.90/8.13      inference('sup+', [status(thm)], ['5', '23'])).
% 7.90/8.13  thf('25', plain,
% 7.90/8.13      (![X0 : $i, X1 : $i]:
% 7.90/8.13         ((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1) @ 
% 7.90/8.13           (k6_relat_1 @ X0))
% 7.90/8.13           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 7.90/8.13      inference('demod', [status(thm)], ['20', '21', '22'])).
% 7.90/8.13  thf('26', plain, (![X22 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X22)) = (X22))),
% 7.90/8.13      inference('cnf', [status(esa)], [t71_relat_1])).
% 7.90/8.13  thf('27', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 7.90/8.13      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 7.90/8.13  thf('28', plain,
% 7.90/8.13      (![X0 : $i, X1 : $i]:
% 7.90/8.13         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 7.90/8.13           = (k5_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 7.90/8.13              (k6_relat_1 @ X1)))),
% 7.90/8.13      inference('demod', [status(thm)], ['24', '25', '26', '27'])).
% 7.90/8.13  thf(t76_relat_1, axiom,
% 7.90/8.13    (![A:$i,B:$i]:
% 7.90/8.13     ( ( v1_relat_1 @ B ) =>
% 7.90/8.13       ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B ) & 
% 7.90/8.13         ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ))).
% 7.90/8.13  thf('29', plain,
% 7.90/8.13      (![X24 : $i, X25 : $i]:
% 7.90/8.13         ((r1_tarski @ (k5_relat_1 @ X24 @ (k6_relat_1 @ X25)) @ X24)
% 7.90/8.13          | ~ (v1_relat_1 @ X24))),
% 7.90/8.13      inference('cnf', [status(esa)], [t76_relat_1])).
% 7.90/8.13  thf('30', plain,
% 7.90/8.13      (![X0 : $i, X2 : $i]:
% 7.90/8.13         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 7.90/8.13      inference('cnf', [status(esa)], [d10_xboole_0])).
% 7.90/8.13  thf('31', plain,
% 7.90/8.13      (![X0 : $i, X1 : $i]:
% 7.90/8.13         (~ (v1_relat_1 @ X0)
% 7.90/8.13          | ~ (r1_tarski @ X0 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 7.90/8.13          | ((X0) = (k5_relat_1 @ X0 @ (k6_relat_1 @ X1))))),
% 7.90/8.13      inference('sup-', [status(thm)], ['29', '30'])).
% 7.90/8.13  thf('32', plain,
% 7.90/8.13      (![X0 : $i, X1 : $i]:
% 7.90/8.13         (~ (r1_tarski @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 7.90/8.13             (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))
% 7.90/8.13          | ((k6_relat_1 @ (k3_xboole_0 @ X0 @ X1))
% 7.90/8.13              = (k5_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 7.90/8.13                 (k6_relat_1 @ X0)))
% 7.90/8.13          | ~ (v1_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1))))),
% 7.90/8.13      inference('sup-', [status(thm)], ['28', '31'])).
% 7.90/8.13  thf('33', plain,
% 7.90/8.13      (![X0 : $i, X1 : $i]:
% 7.90/8.13         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 7.90/8.13           = (k5_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 7.90/8.13              (k6_relat_1 @ X1)))),
% 7.90/8.13      inference('demod', [status(thm)], ['24', '25', '26', '27'])).
% 7.90/8.13  thf('34', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 7.90/8.13      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 7.90/8.13  thf('35', plain,
% 7.90/8.13      (![X0 : $i, X1 : $i]:
% 7.90/8.13         (~ (r1_tarski @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 7.90/8.13             (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))
% 7.90/8.13          | ((k6_relat_1 @ (k3_xboole_0 @ X0 @ X1))
% 7.90/8.13              = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))))),
% 7.90/8.13      inference('demod', [status(thm)], ['32', '33', '34'])).
% 7.90/8.13  thf('36', plain,
% 7.90/8.13      (![X28 : $i, X29 : $i]:
% 7.90/8.13         (((k7_relat_1 @ X29 @ X28) = (k5_relat_1 @ (k6_relat_1 @ X28) @ X29))
% 7.90/8.13          | ~ (v1_relat_1 @ X29))),
% 7.90/8.13      inference('cnf', [status(esa)], [t94_relat_1])).
% 7.90/8.13  thf('37', plain,
% 7.90/8.13      (![X0 : $i, X1 : $i]:
% 7.90/8.13         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 7.90/8.13           = (k5_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 7.90/8.13              (k6_relat_1 @ X1)))),
% 7.90/8.13      inference('demod', [status(thm)], ['24', '25', '26', '27'])).
% 7.90/8.13  thf('38', plain,
% 7.90/8.13      (![X0 : $i, X1 : $i]:
% 7.90/8.13         (((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 7.90/8.13            = (k7_relat_1 @ (k6_relat_1 @ X1) @ (k3_xboole_0 @ X1 @ X0)))
% 7.90/8.13          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 7.90/8.13      inference('sup+', [status(thm)], ['36', '37'])).
% 7.90/8.13  thf('39', plain, (![X22 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X22)) = (X22))),
% 7.90/8.13      inference('cnf', [status(esa)], [t71_relat_1])).
% 7.90/8.13  thf('40', plain,
% 7.90/8.13      (![X17 : $i, X18 : $i]:
% 7.90/8.13         (((k7_relat_1 @ X17 @ X18)
% 7.90/8.13            = (k7_relat_1 @ X17 @ (k3_xboole_0 @ (k1_relat_1 @ X17) @ X18)))
% 7.90/8.13          | ~ (v1_relat_1 @ X17))),
% 7.90/8.13      inference('cnf', [status(esa)], [t192_relat_1])).
% 7.90/8.13  thf('41', plain,
% 7.90/8.13      (![X0 : $i, X1 : $i]:
% 7.90/8.13         (((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 7.90/8.13            = (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))
% 7.90/8.13          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 7.90/8.13      inference('sup+', [status(thm)], ['39', '40'])).
% 7.90/8.13  thf('42', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 7.90/8.13      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 7.90/8.13  thf('43', plain,
% 7.90/8.13      (![X0 : $i, X1 : $i]:
% 7.90/8.13         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 7.90/8.13           = (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 7.90/8.13      inference('demod', [status(thm)], ['41', '42'])).
% 7.90/8.13  thf('44', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 7.90/8.13      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 7.90/8.13  thf('45', plain,
% 7.90/8.13      (![X0 : $i, X1 : $i]:
% 7.90/8.13         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 7.90/8.13           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 7.90/8.13      inference('demod', [status(thm)], ['38', '43', '44'])).
% 7.90/8.13  thf('46', plain,
% 7.90/8.13      (![X0 : $i, X1 : $i]:
% 7.90/8.13         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 7.90/8.13           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 7.90/8.13      inference('demod', [status(thm)], ['38', '43', '44'])).
% 7.90/8.13  thf('47', plain,
% 7.90/8.13      (![X0 : $i, X1 : $i]:
% 7.90/8.13         (~ (r1_tarski @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 7.90/8.13             (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 7.90/8.13          | ((k6_relat_1 @ (k3_xboole_0 @ X0 @ X1))
% 7.90/8.13              = (k7_relat_1 @ (k6_relat_1 @ X0) @ X1)))),
% 7.90/8.13      inference('demod', [status(thm)], ['35', '45', '46'])).
% 7.90/8.13  thf('48', plain,
% 7.90/8.13      (![X28 : $i, X29 : $i]:
% 7.90/8.13         (((k7_relat_1 @ X29 @ X28) = (k5_relat_1 @ (k6_relat_1 @ X28) @ X29))
% 7.90/8.13          | ~ (v1_relat_1 @ X29))),
% 7.90/8.13      inference('cnf', [status(esa)], [t94_relat_1])).
% 7.90/8.13  thf('49', plain,
% 7.90/8.13      (![X0 : $i]:
% 7.90/8.13         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 7.90/8.13           = (k6_relat_1 @ X0))),
% 7.90/8.13      inference('demod', [status(thm)], ['11', '12'])).
% 7.90/8.13  thf('50', plain,
% 7.90/8.13      (![X0 : $i]:
% 7.90/8.13         (((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))
% 7.90/8.13          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 7.90/8.13      inference('sup+', [status(thm)], ['48', '49'])).
% 7.90/8.13  thf('51', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 7.90/8.13      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 7.90/8.13  thf('52', plain,
% 7.90/8.13      (![X0 : $i]: ((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 7.90/8.13      inference('demod', [status(thm)], ['50', '51'])).
% 7.90/8.13  thf('53', plain,
% 7.90/8.13      (![X0 : $i]:
% 7.90/8.13         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 7.90/8.13           = (k6_relat_1 @ X0))),
% 7.90/8.13      inference('demod', [status(thm)], ['11', '12'])).
% 7.90/8.13  thf('54', plain,
% 7.90/8.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.90/8.13         (~ (v1_relat_1 @ X2)
% 7.90/8.13          | ~ (v1_relat_1 @ X1)
% 7.90/8.13          | ((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 7.90/8.13              = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2))))),
% 7.90/8.13      inference('simplify', [status(thm)], ['18'])).
% 7.90/8.13  thf('55', plain,
% 7.90/8.13      (![X0 : $i]:
% 7.90/8.13         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 7.90/8.13           = (k6_relat_1 @ X0))),
% 7.90/8.13      inference('demod', [status(thm)], ['11', '12'])).
% 7.90/8.13  thf('56', plain,
% 7.90/8.13      (![X19 : $i, X20 : $i, X21 : $i]:
% 7.90/8.13         (~ (v1_relat_1 @ X19)
% 7.90/8.13          | ((k5_relat_1 @ (k5_relat_1 @ X20 @ X19) @ X21)
% 7.90/8.13              = (k5_relat_1 @ X20 @ (k5_relat_1 @ X19 @ X21)))
% 7.90/8.13          | ~ (v1_relat_1 @ X21)
% 7.90/8.13          | ~ (v1_relat_1 @ X20))),
% 7.90/8.13      inference('cnf', [status(esa)], [t55_relat_1])).
% 7.90/8.13  thf(dt_k5_relat_1, axiom,
% 7.90/8.13    (![A:$i,B:$i]:
% 7.90/8.13     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 7.90/8.13       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 7.90/8.13  thf('57', plain,
% 7.90/8.13      (![X11 : $i, X12 : $i]:
% 7.90/8.13         (~ (v1_relat_1 @ X11)
% 7.90/8.13          | ~ (v1_relat_1 @ X12)
% 7.90/8.13          | (v1_relat_1 @ (k5_relat_1 @ X11 @ X12)))),
% 7.90/8.13      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 7.90/8.13  thf('58', plain,
% 7.90/8.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.90/8.13         ((v1_relat_1 @ (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0)))
% 7.90/8.13          | ~ (v1_relat_1 @ X2)
% 7.90/8.13          | ~ (v1_relat_1 @ X0)
% 7.90/8.13          | ~ (v1_relat_1 @ X1)
% 7.90/8.13          | ~ (v1_relat_1 @ X0)
% 7.90/8.13          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1)))),
% 7.90/8.13      inference('sup+', [status(thm)], ['56', '57'])).
% 7.90/8.13  thf('59', plain,
% 7.90/8.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.90/8.13         (~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1))
% 7.90/8.13          | ~ (v1_relat_1 @ X1)
% 7.90/8.13          | ~ (v1_relat_1 @ X0)
% 7.90/8.13          | ~ (v1_relat_1 @ X2)
% 7.90/8.13          | (v1_relat_1 @ (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0))))),
% 7.90/8.13      inference('simplify', [status(thm)], ['58'])).
% 7.90/8.13  thf('60', plain,
% 7.90/8.13      (![X0 : $i, X1 : $i]:
% 7.90/8.13         (~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 7.90/8.13          | (v1_relat_1 @ 
% 7.90/8.13             (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 7.90/8.13              (k5_relat_1 @ (k6_relat_1 @ X0) @ X1)))
% 7.90/8.13          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 7.90/8.13          | ~ (v1_relat_1 @ X1)
% 7.90/8.13          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 7.90/8.13      inference('sup-', [status(thm)], ['55', '59'])).
% 7.90/8.13  thf('61', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 7.90/8.13      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 7.90/8.13  thf('62', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 7.90/8.13      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 7.90/8.13  thf('63', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 7.90/8.13      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 7.90/8.13  thf('64', plain,
% 7.90/8.13      (![X0 : $i, X1 : $i]:
% 7.90/8.13         ((v1_relat_1 @ 
% 7.90/8.13           (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 7.90/8.13            (k5_relat_1 @ (k6_relat_1 @ X0) @ X1)))
% 7.90/8.13          | ~ (v1_relat_1 @ X1))),
% 7.90/8.13      inference('demod', [status(thm)], ['60', '61', '62', '63'])).
% 7.90/8.13  thf('65', plain,
% 7.90/8.13      (![X0 : $i, X1 : $i]:
% 7.90/8.13         ((v1_relat_1 @ 
% 7.90/8.13           (k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X1) @ X0))
% 7.90/8.13          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 7.90/8.13          | ~ (v1_relat_1 @ X0)
% 7.90/8.13          | ~ (v1_relat_1 @ X0))),
% 7.90/8.13      inference('sup+', [status(thm)], ['54', '64'])).
% 7.90/8.13  thf('66', plain,
% 7.90/8.13      (![X0 : $i]: ((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 7.90/8.13      inference('demod', [status(thm)], ['50', '51'])).
% 7.90/8.13  thf('67', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 7.90/8.13      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 7.90/8.13  thf('68', plain,
% 7.90/8.13      (![X0 : $i, X1 : $i]:
% 7.90/8.13         ((v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 7.90/8.13          | ~ (v1_relat_1 @ X0)
% 7.90/8.13          | ~ (v1_relat_1 @ X0))),
% 7.90/8.13      inference('demod', [status(thm)], ['65', '66', '67'])).
% 7.90/8.13  thf('69', plain,
% 7.90/8.13      (![X0 : $i, X1 : $i]:
% 7.90/8.13         (~ (v1_relat_1 @ X0)
% 7.90/8.13          | (v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 7.90/8.13      inference('simplify', [status(thm)], ['68'])).
% 7.90/8.13  thf('70', plain,
% 7.90/8.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.90/8.13         (~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1))
% 7.90/8.13          | ~ (v1_relat_1 @ X1)
% 7.90/8.13          | ~ (v1_relat_1 @ X0)
% 7.90/8.13          | ~ (v1_relat_1 @ X2)
% 7.90/8.13          | (v1_relat_1 @ (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0))))),
% 7.90/8.13      inference('simplify', [status(thm)], ['58'])).
% 7.90/8.13  thf('71', plain,
% 7.90/8.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.90/8.13         (~ (v1_relat_1 @ X0)
% 7.90/8.13          | (v1_relat_1 @ 
% 7.90/8.13             (k5_relat_1 @ (k6_relat_1 @ X1) @ (k5_relat_1 @ X0 @ X2)))
% 7.90/8.13          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 7.90/8.13          | ~ (v1_relat_1 @ X2)
% 7.90/8.13          | ~ (v1_relat_1 @ X0))),
% 7.90/8.13      inference('sup-', [status(thm)], ['69', '70'])).
% 7.90/8.13  thf('72', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 7.90/8.13      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 7.90/8.13  thf('73', plain,
% 7.90/8.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.90/8.13         (~ (v1_relat_1 @ X0)
% 7.90/8.13          | (v1_relat_1 @ 
% 7.90/8.13             (k5_relat_1 @ (k6_relat_1 @ X1) @ (k5_relat_1 @ X0 @ X2)))
% 7.90/8.13          | ~ (v1_relat_1 @ X2)
% 7.90/8.13          | ~ (v1_relat_1 @ X0))),
% 7.90/8.13      inference('demod', [status(thm)], ['71', '72'])).
% 7.90/8.13  thf('74', plain,
% 7.90/8.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.90/8.13         (~ (v1_relat_1 @ X2)
% 7.90/8.13          | (v1_relat_1 @ 
% 7.90/8.13             (k5_relat_1 @ (k6_relat_1 @ X1) @ (k5_relat_1 @ X0 @ X2)))
% 7.90/8.13          | ~ (v1_relat_1 @ X0))),
% 7.90/8.13      inference('simplify', [status(thm)], ['73'])).
% 7.90/8.13  thf('75', plain,
% 7.90/8.13      (![X0 : $i, X1 : $i]:
% 7.90/8.13         ((v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))
% 7.90/8.13          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 7.90/8.13          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 7.90/8.13      inference('sup+', [status(thm)], ['53', '74'])).
% 7.90/8.13  thf('76', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 7.90/8.13      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 7.90/8.13  thf('77', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 7.90/8.13      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 7.90/8.13  thf('78', plain,
% 7.90/8.13      (![X0 : $i, X1 : $i]:
% 7.90/8.13         (v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 7.90/8.13      inference('demod', [status(thm)], ['75', '76', '77'])).
% 7.90/8.13  thf('79', plain,
% 7.90/8.13      (![X19 : $i, X20 : $i, X21 : $i]:
% 7.90/8.13         (~ (v1_relat_1 @ X19)
% 7.90/8.13          | ((k5_relat_1 @ (k5_relat_1 @ X20 @ X19) @ X21)
% 7.90/8.13              = (k5_relat_1 @ X20 @ (k5_relat_1 @ X19 @ X21)))
% 7.90/8.13          | ~ (v1_relat_1 @ X21)
% 7.90/8.13          | ~ (v1_relat_1 @ X20))),
% 7.90/8.13      inference('cnf', [status(esa)], [t55_relat_1])).
% 7.90/8.13  thf('80', plain,
% 7.90/8.13      (![X24 : $i, X25 : $i]:
% 7.90/8.13         ((r1_tarski @ (k5_relat_1 @ X24 @ (k6_relat_1 @ X25)) @ X24)
% 7.90/8.13          | ~ (v1_relat_1 @ X24))),
% 7.90/8.13      inference('cnf', [status(esa)], [t76_relat_1])).
% 7.90/8.13  thf('81', plain,
% 7.90/8.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.90/8.13         ((r1_tarski @ 
% 7.90/8.13           (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ 
% 7.90/8.13           (k5_relat_1 @ X2 @ X1))
% 7.90/8.13          | ~ (v1_relat_1 @ X2)
% 7.90/8.13          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 7.90/8.13          | ~ (v1_relat_1 @ X1)
% 7.90/8.13          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1)))),
% 7.90/8.13      inference('sup+', [status(thm)], ['79', '80'])).
% 7.90/8.13  thf('82', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 7.90/8.13      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 7.90/8.13  thf('83', plain,
% 7.90/8.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.90/8.13         ((r1_tarski @ 
% 7.90/8.13           (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ 
% 7.90/8.13           (k5_relat_1 @ X2 @ X1))
% 7.90/8.13          | ~ (v1_relat_1 @ X2)
% 7.90/8.13          | ~ (v1_relat_1 @ X1)
% 7.90/8.13          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1)))),
% 7.90/8.13      inference('demod', [status(thm)], ['81', '82'])).
% 7.90/8.13  thf('84', plain,
% 7.90/8.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.90/8.13         (~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 7.90/8.13          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 7.90/8.13          | (r1_tarski @ 
% 7.90/8.13             (k5_relat_1 @ (k6_relat_1 @ X1) @ 
% 7.90/8.13              (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X2))) @ 
% 7.90/8.13             (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))))),
% 7.90/8.13      inference('sup-', [status(thm)], ['78', '83'])).
% 7.90/8.13  thf('85', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 7.90/8.13      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 7.90/8.13  thf('86', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 7.90/8.13      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 7.90/8.13  thf('87', plain,
% 7.90/8.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.90/8.13         (r1_tarski @ 
% 7.90/8.13          (k5_relat_1 @ (k6_relat_1 @ X1) @ 
% 7.90/8.13           (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X2))) @ 
% 7.90/8.13          (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 7.90/8.13      inference('demod', [status(thm)], ['84', '85', '86'])).
% 7.90/8.13  thf('88', plain,
% 7.90/8.13      (![X0 : $i, X1 : $i]:
% 7.90/8.13         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 7.90/8.13           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 7.90/8.13      inference('demod', [status(thm)], ['38', '43', '44'])).
% 7.90/8.13  thf('89', plain,
% 7.90/8.13      (![X0 : $i, X1 : $i]:
% 7.90/8.13         ((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1) @ 
% 7.90/8.13           (k6_relat_1 @ X0))
% 7.90/8.13           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 7.90/8.13      inference('demod', [status(thm)], ['20', '21', '22'])).
% 7.90/8.13  thf('90', plain,
% 7.90/8.13      (![X0 : $i, X1 : $i]:
% 7.90/8.13         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 7.90/8.13           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 7.90/8.13      inference('demod', [status(thm)], ['38', '43', '44'])).
% 7.90/8.13  thf('91', plain,
% 7.90/8.13      (![X0 : $i, X1 : $i]:
% 7.90/8.13         ((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1) @ 
% 7.90/8.13           (k6_relat_1 @ X0)) = (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 7.90/8.13      inference('demod', [status(thm)], ['89', '90'])).
% 7.90/8.13  thf('92', plain,
% 7.90/8.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.90/8.13         (~ (v1_relat_1 @ X2)
% 7.90/8.13          | ~ (v1_relat_1 @ X1)
% 7.90/8.13          | ((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 7.90/8.13              = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2))))),
% 7.90/8.13      inference('simplify', [status(thm)], ['18'])).
% 7.90/8.13  thf('93', plain,
% 7.90/8.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.90/8.13         (((k5_relat_1 @ 
% 7.90/8.13            (k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X2) @ 
% 7.90/8.13            (k6_relat_1 @ X1))
% 7.90/8.13            = (k5_relat_1 @ (k6_relat_1 @ X2) @ 
% 7.90/8.13               (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))
% 7.90/8.13          | ~ (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 7.90/8.13          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 7.90/8.13      inference('sup+', [status(thm)], ['91', '92'])).
% 7.90/8.13  thf('94', plain,
% 7.90/8.13      (![X0 : $i, X1 : $i]:
% 7.90/8.13         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 7.90/8.13           = (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 7.90/8.13      inference('demod', [status(thm)], ['41', '42'])).
% 7.90/8.13  thf(t100_relat_1, axiom,
% 7.90/8.13    (![A:$i,B:$i,C:$i]:
% 7.90/8.13     ( ( v1_relat_1 @ C ) =>
% 7.90/8.13       ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 7.90/8.13         ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 7.90/8.13  thf('95', plain,
% 7.90/8.13      (![X14 : $i, X15 : $i, X16 : $i]:
% 7.90/8.13         (((k7_relat_1 @ (k7_relat_1 @ X14 @ X15) @ X16)
% 7.90/8.13            = (k7_relat_1 @ X14 @ (k3_xboole_0 @ X15 @ X16)))
% 7.90/8.13          | ~ (v1_relat_1 @ X14))),
% 7.90/8.13      inference('cnf', [status(esa)], [t100_relat_1])).
% 7.90/8.13  thf('96', plain,
% 7.90/8.13      (![X14 : $i, X15 : $i, X16 : $i]:
% 7.90/8.13         (((k7_relat_1 @ (k7_relat_1 @ X14 @ X15) @ X16)
% 7.90/8.13            = (k7_relat_1 @ X14 @ (k3_xboole_0 @ X15 @ X16)))
% 7.90/8.13          | ~ (v1_relat_1 @ X14))),
% 7.90/8.13      inference('cnf', [status(esa)], [t100_relat_1])).
% 7.90/8.13  thf('97', plain,
% 7.90/8.13      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 7.90/8.13         (((k7_relat_1 @ (k7_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X3)
% 7.90/8.13            = (k7_relat_1 @ (k7_relat_1 @ X2 @ X1) @ (k3_xboole_0 @ X0 @ X3)))
% 7.90/8.13          | ~ (v1_relat_1 @ X2)
% 7.90/8.13          | ~ (v1_relat_1 @ (k7_relat_1 @ X2 @ X1)))),
% 7.90/8.13      inference('sup+', [status(thm)], ['95', '96'])).
% 7.90/8.13  thf('98', plain,
% 7.90/8.13      (![X28 : $i, X29 : $i]:
% 7.90/8.13         (((k7_relat_1 @ X29 @ X28) = (k5_relat_1 @ (k6_relat_1 @ X28) @ X29))
% 7.90/8.13          | ~ (v1_relat_1 @ X29))),
% 7.90/8.13      inference('cnf', [status(esa)], [t94_relat_1])).
% 7.90/8.13  thf('99', plain,
% 7.90/8.13      (![X11 : $i, X12 : $i]:
% 7.90/8.13         (~ (v1_relat_1 @ X11)
% 7.90/8.13          | ~ (v1_relat_1 @ X12)
% 7.90/8.13          | (v1_relat_1 @ (k5_relat_1 @ X11 @ X12)))),
% 7.90/8.13      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 7.90/8.13  thf('100', plain,
% 7.90/8.13      (![X0 : $i, X1 : $i]:
% 7.90/8.13         ((v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 7.90/8.13          | ~ (v1_relat_1 @ X1)
% 7.90/8.13          | ~ (v1_relat_1 @ X1)
% 7.90/8.13          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 7.90/8.13      inference('sup+', [status(thm)], ['98', '99'])).
% 7.90/8.13  thf('101', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 7.90/8.13      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 7.90/8.13  thf('102', plain,
% 7.90/8.13      (![X0 : $i, X1 : $i]:
% 7.90/8.13         ((v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 7.90/8.13          | ~ (v1_relat_1 @ X1)
% 7.90/8.13          | ~ (v1_relat_1 @ X1))),
% 7.90/8.13      inference('demod', [status(thm)], ['100', '101'])).
% 7.90/8.13  thf('103', plain,
% 7.90/8.13      (![X0 : $i, X1 : $i]:
% 7.90/8.13         (~ (v1_relat_1 @ X1) | (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 7.90/8.13      inference('simplify', [status(thm)], ['102'])).
% 7.90/8.13  thf('104', plain,
% 7.90/8.13      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 7.90/8.13         (~ (v1_relat_1 @ X2)
% 7.90/8.13          | ((k7_relat_1 @ (k7_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X3)
% 7.90/8.13              = (k7_relat_1 @ (k7_relat_1 @ X2 @ X1) @ (k3_xboole_0 @ X0 @ X3))))),
% 7.90/8.13      inference('clc', [status(thm)], ['97', '103'])).
% 7.90/8.13  thf('105', plain,
% 7.90/8.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.90/8.13         (((k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X2)
% 7.90/8.13            = (k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X1) @ 
% 7.90/8.13               (k3_xboole_0 @ X0 @ X2)))
% 7.90/8.13          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 7.90/8.13      inference('sup+', [status(thm)], ['94', '104'])).
% 7.90/8.13  thf('106', plain,
% 7.90/8.13      (![X0 : $i]: ((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 7.90/8.13      inference('demod', [status(thm)], ['50', '51'])).
% 7.90/8.13  thf('107', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 7.90/8.13      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 7.90/8.13  thf('108', plain,
% 7.90/8.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.90/8.13         ((k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X2)
% 7.90/8.13           = (k7_relat_1 @ (k6_relat_1 @ X1) @ (k3_xboole_0 @ X0 @ X2)))),
% 7.90/8.13      inference('demod', [status(thm)], ['105', '106', '107'])).
% 7.90/8.13  thf('109', plain,
% 7.90/8.13      (![X0 : $i, X1 : $i]:
% 7.90/8.13         ((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1) @ 
% 7.90/8.13           (k6_relat_1 @ X0)) = (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 7.90/8.13      inference('demod', [status(thm)], ['89', '90'])).
% 7.90/8.13  thf('110', plain,
% 7.90/8.13      (![X0 : $i, X1 : $i]:
% 7.90/8.13         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 7.90/8.13           = (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 7.90/8.13      inference('demod', [status(thm)], ['41', '42'])).
% 7.90/8.13  thf('111', plain,
% 7.90/8.13      (![X0 : $i, X1 : $i]:
% 7.90/8.13         (~ (v1_relat_1 @ X1) | (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 7.90/8.13      inference('simplify', [status(thm)], ['102'])).
% 7.90/8.13  thf('112', plain,
% 7.90/8.13      (![X0 : $i, X1 : $i]:
% 7.90/8.13         ((v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 7.90/8.13          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 7.90/8.13      inference('sup+', [status(thm)], ['110', '111'])).
% 7.90/8.13  thf('113', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 7.90/8.13      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 7.90/8.13  thf('114', plain,
% 7.90/8.13      (![X0 : $i, X1 : $i]:
% 7.90/8.13         (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 7.90/8.13      inference('demod', [status(thm)], ['112', '113'])).
% 7.90/8.13  thf('115', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 7.90/8.13      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 7.90/8.13  thf('116', plain,
% 7.90/8.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.90/8.13         ((k7_relat_1 @ (k6_relat_1 @ X1) @ (k3_xboole_0 @ X0 @ X2))
% 7.90/8.13           = (k5_relat_1 @ (k6_relat_1 @ X2) @ 
% 7.90/8.13              (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 7.90/8.13      inference('demod', [status(thm)], ['93', '108', '109', '114', '115'])).
% 7.90/8.13  thf('117', plain,
% 7.90/8.13      (![X0 : $i, X1 : $i]:
% 7.90/8.13         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 7.90/8.13           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 7.90/8.13      inference('demod', [status(thm)], ['38', '43', '44'])).
% 7.90/8.13  thf('118', plain,
% 7.90/8.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.90/8.13         (r1_tarski @ 
% 7.90/8.13          (k7_relat_1 @ (k6_relat_1 @ X2) @ (k3_xboole_0 @ X0 @ X1)) @ 
% 7.90/8.13          (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 7.90/8.13      inference('demod', [status(thm)], ['87', '88', '116', '117'])).
% 7.90/8.13  thf('119', plain,
% 7.90/8.13      (![X0 : $i, X1 : $i]:
% 7.90/8.13         (r1_tarski @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 7.90/8.13          (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 7.90/8.13      inference('sup+', [status(thm)], ['52', '118'])).
% 7.90/8.13  thf('120', plain,
% 7.90/8.13      (![X0 : $i, X1 : $i]:
% 7.90/8.13         ((k6_relat_1 @ (k3_xboole_0 @ X0 @ X1))
% 7.90/8.13           = (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 7.90/8.13      inference('demod', [status(thm)], ['47', '119'])).
% 7.90/8.13  thf('121', plain,
% 7.90/8.13      (((k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B))
% 7.90/8.13         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 7.90/8.13      inference('demod', [status(thm)], ['4', '120'])).
% 7.90/8.13  thf('122', plain, ($false), inference('simplify', [status(thm)], ['121'])).
% 7.90/8.13  
% 7.90/8.13  % SZS output end Refutation
% 7.90/8.13  
% 7.90/8.14  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
