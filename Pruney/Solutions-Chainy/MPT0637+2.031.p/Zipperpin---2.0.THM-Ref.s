%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.XiQwZUqxki

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:00 EST 2020

% Result     : Theorem 2.17s
% Output     : Refutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :  153 ( 520 expanded)
%              Number of leaves         :   25 ( 200 expanded)
%              Depth                    :   18
%              Number of atoms          : 1337 (4439 expanded)
%              Number of equality atoms :   90 ( 376 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('0',plain,(
    ! [X34: $i,X35: $i] :
      ( ( ( k7_relat_1 @ X35 @ X34 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X34 ) @ X35 ) )
      | ~ ( v1_relat_1 @ X35 ) ) ),
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

thf('5',plain,(
    ! [X34: $i,X35: $i] :
      ( ( ( k7_relat_1 @ X35 @ X34 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X34 ) @ X35 ) )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t76_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B )
        & ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ) )).

thf('6',plain,(
    ! [X26: $i,X27: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X26 @ ( k6_relat_1 @ X27 ) ) @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t76_relat_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('7',plain,(
    ! [X24: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X24 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('8',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X36 ) @ X37 )
      | ( ( k7_relat_1 @ X36 @ X37 )
        = X36 )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) @ X0 )
        = ( k6_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('13',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X32 @ X33 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X32 ) @ X33 ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('14',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('15',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X1 ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k1_relat_1 @ X1 )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ ( k6_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) @ ( k1_relat_1 @ ( k6_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k1_relat_1 @ ( k6_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ ( k6_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf('19',plain,(
    ! [X24: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X24 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('20',plain,(
    ! [X24: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X24 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('21',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('22',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X24: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X24 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('24',plain,(
    ! [X24: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X24 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('26',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
        = ( k3_xboole_0 @ X1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['18','19','20','22','23','24','25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k3_xboole_0 @ ( k6_relat_1 @ X0 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','27'])).

thf('29',plain,(
    ! [X34: $i,X35: $i] :
      ( ( ( k7_relat_1 @ X35 @ X34 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X34 ) @ X35 ) )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('30',plain,(
    ! [X26: $i,X27: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X26 @ ( k6_relat_1 @ X27 ) ) @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t76_relat_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('33',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X1 ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k1_relat_1 @ X1 )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ ( k6_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) @ ( k1_relat_1 @ ( k6_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) )
      | ( ( k1_relat_1 @ ( k6_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ ( k6_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X24: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X24 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('40',plain,(
    ! [X24: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X24 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('41',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['21'])).

thf('42',plain,(
    ! [X24: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X24 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('43',plain,(
    ! [X24: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X24 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('45',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ ( k6_relat_1 @ X0 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['38','39','40','41','42','43','44','45'])).

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
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['28','46','47','48'])).

thf('50',plain,(
    ! [X34: $i,X35: $i] :
      ( ( ( k7_relat_1 @ X35 @ X34 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X34 ) @ X35 ) )
      | ~ ( v1_relat_1 @ X35 ) ) ),
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

thf('51',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X22 @ X21 ) @ X23 )
        = ( k5_relat_1 @ X22 @ ( k5_relat_1 @ X21 @ X23 ) ) )
      | ~ ( v1_relat_1 @ X23 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf(t78_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A )
        = A ) ) )).

thf('56',plain,(
    ! [X28: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X28 ) ) @ X28 )
        = X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X0 )
        = ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) ) ) @ ( k6_relat_1 @ X1 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['49','57'])).

thf('59',plain,(
    ! [X34: $i,X35: $i] :
      ( ( ( k7_relat_1 @ X35 @ X34 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X34 ) @ X35 ) )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('60',plain,(
    ! [X24: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X24 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('61',plain,(
    ! [X28: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X28 ) ) @ X28 )
        = X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('67',plain,(
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

thf('68',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_relat_1 @ X17 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['66','70'])).

thf('72',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('73',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('74',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['71','72','73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['65','75'])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('77',plain,(
    ! [X31: $i] :
      ( ( ( k5_relat_1 @ X31 @ ( k6_relat_1 @ ( k2_relat_1 @ X31 ) ) )
        = X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('78',plain,(
    ! [X34: $i,X35: $i] :
      ( ( ( k7_relat_1 @ X35 @ X34 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X34 ) @ X35 ) )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) ) @ X0 )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X25: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X25 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('81',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('82',plain,(
    ! [X25: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X25 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('83',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['79','80','81','82','83'])).

thf('85',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['76','84','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('89',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('91',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['64','92'])).

thf('94',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('95',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['93','94','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['59','96'])).

thf('98',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('101',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['28','46','47','48'])).

thf('103',plain,(
    ! [X24: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X24 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('104',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X32 @ X33 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X32 ) @ X33 ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( k3_xboole_0 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('109',plain,(
    ! [X34: $i,X35: $i] :
      ( ( ( k7_relat_1 @ X35 @ X34 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X34 ) @ X35 ) )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('110',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('111',plain,(
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

thf('112',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X29 ) @ X30 )
      | ( ( k5_relat_1 @ X29 @ ( k6_relat_1 @ X30 ) )
        = X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['110','115'])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
        = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['109','116'])).

thf('118',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['108','119'])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['28','46','47','48'])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['108','119'])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['28','46','47','48'])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['58','99','100','101','102','107','120','121','122','123'])).

thf('125',plain,(
    ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
 != ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['4','124'])).

thf('126',plain,(
    $false ),
    inference(simplify,[status(thm)],['125'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.XiQwZUqxki
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:37:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.17/2.38  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.17/2.38  % Solved by: fo/fo7.sh
% 2.17/2.38  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.17/2.38  % done 3033 iterations in 1.934s
% 2.17/2.38  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.17/2.38  % SZS output start Refutation
% 2.17/2.38  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.17/2.38  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.17/2.38  thf(sk_A_type, type, sk_A: $i).
% 2.17/2.38  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 2.17/2.38  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.17/2.38  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 2.17/2.38  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.17/2.38  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.17/2.38  thf(sk_B_type, type, sk_B: $i).
% 2.17/2.38  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 2.17/2.38  thf(t94_relat_1, axiom,
% 2.17/2.38    (![A:$i,B:$i]:
% 2.17/2.38     ( ( v1_relat_1 @ B ) =>
% 2.17/2.38       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 2.17/2.38  thf('0', plain,
% 2.17/2.38      (![X34 : $i, X35 : $i]:
% 2.17/2.38         (((k7_relat_1 @ X35 @ X34) = (k5_relat_1 @ (k6_relat_1 @ X34) @ X35))
% 2.17/2.38          | ~ (v1_relat_1 @ X35))),
% 2.17/2.38      inference('cnf', [status(esa)], [t94_relat_1])).
% 2.17/2.38  thf(t43_funct_1, conjecture,
% 2.17/2.38    (![A:$i,B:$i]:
% 2.17/2.38     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 2.17/2.38       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 2.17/2.38  thf(zf_stmt_0, negated_conjecture,
% 2.17/2.38    (~( ![A:$i,B:$i]:
% 2.17/2.38        ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 2.17/2.38          ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 2.17/2.38    inference('cnf.neg', [status(esa)], [t43_funct_1])).
% 2.17/2.38  thf('1', plain,
% 2.17/2.38      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A))
% 2.17/2.38         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 2.17/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.17/2.38  thf('2', plain,
% 2.17/2.38      ((((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 2.17/2.38          != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))
% 2.17/2.38        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A)))),
% 2.17/2.38      inference('sup-', [status(thm)], ['0', '1'])).
% 2.17/2.38  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 2.17/2.38  thf('3', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 2.17/2.38      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.17/2.38  thf('4', plain,
% 2.17/2.38      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 2.17/2.38         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 2.17/2.38      inference('demod', [status(thm)], ['2', '3'])).
% 2.17/2.38  thf('5', plain,
% 2.17/2.38      (![X34 : $i, X35 : $i]:
% 2.17/2.38         (((k7_relat_1 @ X35 @ X34) = (k5_relat_1 @ (k6_relat_1 @ X34) @ X35))
% 2.17/2.38          | ~ (v1_relat_1 @ X35))),
% 2.17/2.38      inference('cnf', [status(esa)], [t94_relat_1])).
% 2.17/2.38  thf(t76_relat_1, axiom,
% 2.17/2.38    (![A:$i,B:$i]:
% 2.17/2.38     ( ( v1_relat_1 @ B ) =>
% 2.17/2.38       ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B ) & 
% 2.17/2.38         ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ))).
% 2.17/2.38  thf('6', plain,
% 2.17/2.38      (![X26 : $i, X27 : $i]:
% 2.17/2.38         ((r1_tarski @ (k5_relat_1 @ X26 @ (k6_relat_1 @ X27)) @ X26)
% 2.17/2.38          | ~ (v1_relat_1 @ X26))),
% 2.17/2.38      inference('cnf', [status(esa)], [t76_relat_1])).
% 2.17/2.38  thf(t71_relat_1, axiom,
% 2.17/2.38    (![A:$i]:
% 2.17/2.38     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 2.17/2.38       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 2.17/2.38  thf('7', plain, (![X24 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X24)) = (X24))),
% 2.17/2.38      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.17/2.38  thf(t97_relat_1, axiom,
% 2.17/2.38    (![A:$i,B:$i]:
% 2.17/2.38     ( ( v1_relat_1 @ B ) =>
% 2.17/2.38       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 2.17/2.38         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 2.17/2.38  thf('8', plain,
% 2.17/2.38      (![X36 : $i, X37 : $i]:
% 2.17/2.38         (~ (r1_tarski @ (k1_relat_1 @ X36) @ X37)
% 2.17/2.38          | ((k7_relat_1 @ X36 @ X37) = (X36))
% 2.17/2.38          | ~ (v1_relat_1 @ X36))),
% 2.17/2.38      inference('cnf', [status(esa)], [t97_relat_1])).
% 2.17/2.38  thf('9', plain,
% 2.17/2.38      (![X0 : $i, X1 : $i]:
% 2.17/2.38         (~ (r1_tarski @ X0 @ X1)
% 2.17/2.38          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 2.17/2.38          | ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1) = (k6_relat_1 @ X0)))),
% 2.17/2.38      inference('sup-', [status(thm)], ['7', '8'])).
% 2.17/2.38  thf('10', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 2.17/2.38      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.17/2.38  thf('11', plain,
% 2.17/2.38      (![X0 : $i, X1 : $i]:
% 2.17/2.38         (~ (r1_tarski @ X0 @ X1)
% 2.17/2.38          | ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1) = (k6_relat_1 @ X0)))),
% 2.17/2.38      inference('demod', [status(thm)], ['9', '10'])).
% 2.17/2.38  thf('12', plain,
% 2.17/2.38      (![X0 : $i, X1 : $i]:
% 2.17/2.38         (~ (v1_relat_1 @ X0)
% 2.17/2.38          | ((k7_relat_1 @ 
% 2.17/2.38              (k6_relat_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1))) @ X0)
% 2.17/2.38              = (k6_relat_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)))))),
% 2.17/2.38      inference('sup-', [status(thm)], ['6', '11'])).
% 2.17/2.38  thf(t90_relat_1, axiom,
% 2.17/2.38    (![A:$i,B:$i]:
% 2.17/2.38     ( ( v1_relat_1 @ B ) =>
% 2.17/2.38       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 2.17/2.38         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 2.17/2.38  thf('13', plain,
% 2.17/2.38      (![X32 : $i, X33 : $i]:
% 2.17/2.38         (((k1_relat_1 @ (k7_relat_1 @ X32 @ X33))
% 2.17/2.38            = (k3_xboole_0 @ (k1_relat_1 @ X32) @ X33))
% 2.17/2.38          | ~ (v1_relat_1 @ X32))),
% 2.17/2.38      inference('cnf', [status(esa)], [t90_relat_1])).
% 2.17/2.38  thf(t17_xboole_1, axiom,
% 2.17/2.38    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 2.17/2.38  thf('14', plain,
% 2.17/2.38      (![X5 : $i, X6 : $i]: (r1_tarski @ (k3_xboole_0 @ X5 @ X6) @ X5)),
% 2.17/2.38      inference('cnf', [status(esa)], [t17_xboole_1])).
% 2.17/2.38  thf(d10_xboole_0, axiom,
% 2.17/2.38    (![A:$i,B:$i]:
% 2.17/2.38     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.17/2.38  thf('15', plain,
% 2.17/2.38      (![X2 : $i, X4 : $i]:
% 2.17/2.38         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 2.17/2.38      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.17/2.38  thf('16', plain,
% 2.17/2.38      (![X0 : $i, X1 : $i]:
% 2.17/2.38         (~ (r1_tarski @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 2.17/2.38          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 2.17/2.38      inference('sup-', [status(thm)], ['14', '15'])).
% 2.17/2.38  thf('17', plain,
% 2.17/2.38      (![X0 : $i, X1 : $i]:
% 2.17/2.38         (~ (r1_tarski @ (k1_relat_1 @ X1) @ 
% 2.17/2.38             (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 2.17/2.38          | ~ (v1_relat_1 @ X1)
% 2.17/2.38          | ((k1_relat_1 @ X1) = (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0)))),
% 2.17/2.38      inference('sup-', [status(thm)], ['13', '16'])).
% 2.17/2.38  thf('18', plain,
% 2.17/2.38      (![X0 : $i, X1 : $i]:
% 2.17/2.38         (~ (r1_tarski @ 
% 2.17/2.38             (k1_relat_1 @ (k6_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))) @ 
% 2.17/2.38             (k1_relat_1 @ (k6_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))))
% 2.17/2.38          | ~ (v1_relat_1 @ X1)
% 2.17/2.38          | ((k1_relat_1 @ (k6_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))))
% 2.17/2.38              = (k3_xboole_0 @ 
% 2.17/2.38                 (k1_relat_1 @ 
% 2.17/2.38                  (k6_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))) @ 
% 2.17/2.38                 X1))
% 2.17/2.38          | ~ (v1_relat_1 @ 
% 2.17/2.38               (k6_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))))),
% 2.17/2.38      inference('sup-', [status(thm)], ['12', '17'])).
% 2.17/2.38  thf('19', plain, (![X24 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X24)) = (X24))),
% 2.17/2.38      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.17/2.38  thf('20', plain, (![X24 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X24)) = (X24))),
% 2.17/2.38      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.17/2.38  thf('21', plain,
% 2.17/2.38      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 2.17/2.38      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.17/2.38  thf('22', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 2.17/2.38      inference('simplify', [status(thm)], ['21'])).
% 2.17/2.38  thf('23', plain, (![X24 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X24)) = (X24))),
% 2.17/2.38      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.17/2.38  thf('24', plain, (![X24 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X24)) = (X24))),
% 2.17/2.38      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.17/2.38  thf(commutativity_k3_xboole_0, axiom,
% 2.17/2.38    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 2.17/2.38  thf('25', plain,
% 2.17/2.38      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.17/2.38      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.17/2.38  thf('26', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 2.17/2.38      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.17/2.38  thf('27', plain,
% 2.17/2.38      (![X0 : $i, X1 : $i]:
% 2.17/2.38         (~ (v1_relat_1 @ X1)
% 2.17/2.38          | ((k5_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 2.17/2.38              = (k3_xboole_0 @ X1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))))),
% 2.17/2.38      inference('demod', [status(thm)],
% 2.17/2.38                ['18', '19', '20', '22', '23', '24', '25', '26'])).
% 2.17/2.38  thf('28', plain,
% 2.17/2.38      (![X0 : $i, X1 : $i]:
% 2.17/2.38         (((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 2.17/2.38            = (k3_xboole_0 @ (k6_relat_1 @ X0) @ 
% 2.17/2.38               (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))
% 2.17/2.38          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 2.17/2.38          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 2.17/2.38      inference('sup+', [status(thm)], ['5', '27'])).
% 2.17/2.38  thf('29', plain,
% 2.17/2.38      (![X34 : $i, X35 : $i]:
% 2.17/2.38         (((k7_relat_1 @ X35 @ X34) = (k5_relat_1 @ (k6_relat_1 @ X34) @ X35))
% 2.17/2.38          | ~ (v1_relat_1 @ X35))),
% 2.17/2.38      inference('cnf', [status(esa)], [t94_relat_1])).
% 2.17/2.38  thf('30', plain,
% 2.17/2.38      (![X26 : $i, X27 : $i]:
% 2.17/2.38         ((r1_tarski @ (k5_relat_1 @ X26 @ (k6_relat_1 @ X27)) @ X26)
% 2.17/2.38          | ~ (v1_relat_1 @ X26))),
% 2.17/2.38      inference('cnf', [status(esa)], [t76_relat_1])).
% 2.17/2.38  thf('31', plain,
% 2.17/2.38      (![X0 : $i, X1 : $i]:
% 2.17/2.38         ((r1_tarski @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 2.17/2.38           (k6_relat_1 @ X0))
% 2.17/2.38          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 2.17/2.38          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 2.17/2.38      inference('sup+', [status(thm)], ['29', '30'])).
% 2.17/2.38  thf('32', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 2.17/2.38      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.17/2.38  thf('33', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 2.17/2.38      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.17/2.38  thf('34', plain,
% 2.17/2.38      (![X0 : $i, X1 : $i]:
% 2.17/2.38         (r1_tarski @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ (k6_relat_1 @ X0))),
% 2.17/2.38      inference('demod', [status(thm)], ['31', '32', '33'])).
% 2.17/2.38  thf('35', plain,
% 2.17/2.38      (![X0 : $i, X1 : $i]:
% 2.17/2.38         (~ (r1_tarski @ X0 @ X1)
% 2.17/2.38          | ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1) = (k6_relat_1 @ X0)))),
% 2.17/2.38      inference('demod', [status(thm)], ['9', '10'])).
% 2.17/2.38  thf('36', plain,
% 2.17/2.38      (![X0 : $i, X1 : $i]:
% 2.17/2.38         ((k7_relat_1 @ (k6_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)) @ 
% 2.17/2.38           (k6_relat_1 @ X0))
% 2.17/2.38           = (k6_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 2.17/2.38      inference('sup-', [status(thm)], ['34', '35'])).
% 2.17/2.38  thf('37', plain,
% 2.17/2.38      (![X0 : $i, X1 : $i]:
% 2.17/2.38         (~ (r1_tarski @ (k1_relat_1 @ X1) @ 
% 2.17/2.38             (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 2.17/2.38          | ~ (v1_relat_1 @ X1)
% 2.17/2.38          | ((k1_relat_1 @ X1) = (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0)))),
% 2.17/2.38      inference('sup-', [status(thm)], ['13', '16'])).
% 2.17/2.38  thf('38', plain,
% 2.17/2.38      (![X0 : $i, X1 : $i]:
% 2.17/2.39         (~ (r1_tarski @ 
% 2.17/2.39             (k1_relat_1 @ (k6_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))) @ 
% 2.17/2.39             (k1_relat_1 @ (k6_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))))
% 2.17/2.39          | ((k1_relat_1 @ (k6_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))
% 2.17/2.39              = (k3_xboole_0 @ 
% 2.17/2.39                 (k1_relat_1 @ 
% 2.17/2.39                  (k6_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))) @ 
% 2.17/2.39                 (k6_relat_1 @ X0)))
% 2.17/2.39          | ~ (v1_relat_1 @ 
% 2.17/2.39               (k6_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))))),
% 2.17/2.39      inference('sup-', [status(thm)], ['36', '37'])).
% 2.17/2.39  thf('39', plain, (![X24 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X24)) = (X24))),
% 2.17/2.39      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.17/2.39  thf('40', plain, (![X24 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X24)) = (X24))),
% 2.17/2.39      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.17/2.39  thf('41', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 2.17/2.39      inference('simplify', [status(thm)], ['21'])).
% 2.17/2.39  thf('42', plain, (![X24 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X24)) = (X24))),
% 2.17/2.39      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.17/2.39  thf('43', plain, (![X24 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X24)) = (X24))),
% 2.17/2.39      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.17/2.39  thf('44', plain,
% 2.17/2.39      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.17/2.39      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.17/2.39  thf('45', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 2.17/2.39      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.17/2.39  thf('46', plain,
% 2.17/2.39      (![X0 : $i, X1 : $i]:
% 2.17/2.39         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 2.17/2.39           = (k3_xboole_0 @ (k6_relat_1 @ X0) @ 
% 2.17/2.39              (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 2.17/2.39      inference('demod', [status(thm)],
% 2.17/2.39                ['38', '39', '40', '41', '42', '43', '44', '45'])).
% 2.17/2.39  thf('47', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 2.17/2.39      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.17/2.39  thf('48', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 2.17/2.39      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.17/2.39  thf('49', plain,
% 2.17/2.39      (![X0 : $i, X1 : $i]:
% 2.17/2.39         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 2.17/2.39           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 2.17/2.39      inference('demod', [status(thm)], ['28', '46', '47', '48'])).
% 2.17/2.39  thf('50', plain,
% 2.17/2.39      (![X34 : $i, X35 : $i]:
% 2.17/2.39         (((k7_relat_1 @ X35 @ X34) = (k5_relat_1 @ (k6_relat_1 @ X34) @ X35))
% 2.17/2.39          | ~ (v1_relat_1 @ X35))),
% 2.17/2.39      inference('cnf', [status(esa)], [t94_relat_1])).
% 2.17/2.39  thf(t55_relat_1, axiom,
% 2.17/2.39    (![A:$i]:
% 2.17/2.39     ( ( v1_relat_1 @ A ) =>
% 2.17/2.39       ( ![B:$i]:
% 2.17/2.39         ( ( v1_relat_1 @ B ) =>
% 2.17/2.39           ( ![C:$i]:
% 2.17/2.39             ( ( v1_relat_1 @ C ) =>
% 2.17/2.39               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 2.17/2.39                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 2.17/2.39  thf('51', plain,
% 2.17/2.39      (![X21 : $i, X22 : $i, X23 : $i]:
% 2.17/2.39         (~ (v1_relat_1 @ X21)
% 2.17/2.39          | ((k5_relat_1 @ (k5_relat_1 @ X22 @ X21) @ X23)
% 2.17/2.39              = (k5_relat_1 @ X22 @ (k5_relat_1 @ X21 @ X23)))
% 2.17/2.39          | ~ (v1_relat_1 @ X23)
% 2.17/2.39          | ~ (v1_relat_1 @ X22))),
% 2.17/2.39      inference('cnf', [status(esa)], [t55_relat_1])).
% 2.17/2.39  thf('52', plain,
% 2.17/2.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.17/2.39         (((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 2.17/2.39            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2)))
% 2.17/2.39          | ~ (v1_relat_1 @ X1)
% 2.17/2.39          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 2.17/2.39          | ~ (v1_relat_1 @ X2)
% 2.17/2.39          | ~ (v1_relat_1 @ X1))),
% 2.17/2.39      inference('sup+', [status(thm)], ['50', '51'])).
% 2.17/2.39  thf('53', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 2.17/2.39      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.17/2.39  thf('54', plain,
% 2.17/2.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.17/2.39         (((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 2.17/2.39            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2)))
% 2.17/2.39          | ~ (v1_relat_1 @ X1)
% 2.17/2.39          | ~ (v1_relat_1 @ X2)
% 2.17/2.39          | ~ (v1_relat_1 @ X1))),
% 2.17/2.39      inference('demod', [status(thm)], ['52', '53'])).
% 2.17/2.39  thf('55', plain,
% 2.17/2.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.17/2.39         (~ (v1_relat_1 @ X2)
% 2.17/2.39          | ~ (v1_relat_1 @ X1)
% 2.17/2.39          | ((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 2.17/2.39              = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2))))),
% 2.17/2.39      inference('simplify', [status(thm)], ['54'])).
% 2.17/2.39  thf(t78_relat_1, axiom,
% 2.17/2.39    (![A:$i]:
% 2.17/2.39     ( ( v1_relat_1 @ A ) =>
% 2.17/2.39       ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A ) = ( A ) ) ))).
% 2.17/2.39  thf('56', plain,
% 2.17/2.39      (![X28 : $i]:
% 2.17/2.39         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X28)) @ X28) = (X28))
% 2.17/2.39          | ~ (v1_relat_1 @ X28))),
% 2.17/2.39      inference('cnf', [status(esa)], [t78_relat_1])).
% 2.17/2.39  thf('57', plain,
% 2.17/2.39      (![X0 : $i, X1 : $i]:
% 2.17/2.39         (((k5_relat_1 @ 
% 2.17/2.39            (k7_relat_1 @ X1 @ (k1_relat_1 @ (k5_relat_1 @ X1 @ X0))) @ X0)
% 2.17/2.39            = (k5_relat_1 @ X1 @ X0))
% 2.17/2.39          | ~ (v1_relat_1 @ X1)
% 2.17/2.39          | ~ (v1_relat_1 @ X0)
% 2.17/2.39          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0)))),
% 2.17/2.39      inference('sup+', [status(thm)], ['55', '56'])).
% 2.17/2.39  thf('58', plain,
% 2.17/2.39      (![X0 : $i, X1 : $i]:
% 2.17/2.39         (~ (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 2.17/2.39          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 2.17/2.39          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 2.17/2.39          | ((k5_relat_1 @ 
% 2.17/2.39              (k7_relat_1 @ (k6_relat_1 @ X0) @ 
% 2.17/2.39               (k1_relat_1 @ 
% 2.17/2.39                (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1)))) @ 
% 2.17/2.39              (k6_relat_1 @ X1))
% 2.17/2.39              = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))))),
% 2.17/2.39      inference('sup-', [status(thm)], ['49', '57'])).
% 2.17/2.39  thf('59', plain,
% 2.17/2.39      (![X34 : $i, X35 : $i]:
% 2.17/2.39         (((k7_relat_1 @ X35 @ X34) = (k5_relat_1 @ (k6_relat_1 @ X34) @ X35))
% 2.17/2.39          | ~ (v1_relat_1 @ X35))),
% 2.17/2.39      inference('cnf', [status(esa)], [t94_relat_1])).
% 2.17/2.39  thf('60', plain, (![X24 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X24)) = (X24))),
% 2.17/2.39      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.17/2.39  thf('61', plain,
% 2.17/2.39      (![X28 : $i]:
% 2.17/2.39         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X28)) @ X28) = (X28))
% 2.17/2.39          | ~ (v1_relat_1 @ X28))),
% 2.17/2.39      inference('cnf', [status(esa)], [t78_relat_1])).
% 2.17/2.39  thf('62', plain,
% 2.17/2.39      (![X0 : $i]:
% 2.17/2.39         (((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 2.17/2.39            = (k6_relat_1 @ X0))
% 2.17/2.39          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 2.17/2.39      inference('sup+', [status(thm)], ['60', '61'])).
% 2.17/2.39  thf('63', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 2.17/2.39      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.17/2.39  thf('64', plain,
% 2.17/2.39      (![X0 : $i]:
% 2.17/2.39         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 2.17/2.39           = (k6_relat_1 @ X0))),
% 2.17/2.39      inference('demod', [status(thm)], ['62', '63'])).
% 2.17/2.39  thf('65', plain,
% 2.17/2.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.17/2.39         (~ (v1_relat_1 @ X2)
% 2.17/2.39          | ~ (v1_relat_1 @ X1)
% 2.17/2.39          | ((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 2.17/2.39              = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2))))),
% 2.17/2.39      inference('simplify', [status(thm)], ['54'])).
% 2.17/2.39  thf('66', plain,
% 2.17/2.39      (![X0 : $i]:
% 2.17/2.39         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 2.17/2.39           = (k6_relat_1 @ X0))),
% 2.17/2.39      inference('demod', [status(thm)], ['62', '63'])).
% 2.17/2.39  thf('67', plain,
% 2.17/2.39      (![X21 : $i, X22 : $i, X23 : $i]:
% 2.17/2.39         (~ (v1_relat_1 @ X21)
% 2.17/2.39          | ((k5_relat_1 @ (k5_relat_1 @ X22 @ X21) @ X23)
% 2.17/2.39              = (k5_relat_1 @ X22 @ (k5_relat_1 @ X21 @ X23)))
% 2.17/2.39          | ~ (v1_relat_1 @ X23)
% 2.17/2.39          | ~ (v1_relat_1 @ X22))),
% 2.17/2.39      inference('cnf', [status(esa)], [t55_relat_1])).
% 2.17/2.39  thf(dt_k5_relat_1, axiom,
% 2.17/2.39    (![A:$i,B:$i]:
% 2.17/2.39     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 2.17/2.39       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 2.17/2.39  thf('68', plain,
% 2.17/2.39      (![X16 : $i, X17 : $i]:
% 2.17/2.39         (~ (v1_relat_1 @ X16)
% 2.17/2.39          | ~ (v1_relat_1 @ X17)
% 2.17/2.39          | (v1_relat_1 @ (k5_relat_1 @ X16 @ X17)))),
% 2.17/2.39      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 2.17/2.39  thf('69', plain,
% 2.17/2.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.17/2.39         ((v1_relat_1 @ (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0)))
% 2.17/2.39          | ~ (v1_relat_1 @ X2)
% 2.17/2.39          | ~ (v1_relat_1 @ X0)
% 2.17/2.39          | ~ (v1_relat_1 @ X1)
% 2.17/2.39          | ~ (v1_relat_1 @ X0)
% 2.17/2.39          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1)))),
% 2.17/2.39      inference('sup+', [status(thm)], ['67', '68'])).
% 2.17/2.39  thf('70', plain,
% 2.17/2.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.17/2.39         (~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1))
% 2.17/2.39          | ~ (v1_relat_1 @ X1)
% 2.17/2.39          | ~ (v1_relat_1 @ X0)
% 2.17/2.39          | ~ (v1_relat_1 @ X2)
% 2.17/2.39          | (v1_relat_1 @ (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0))))),
% 2.17/2.39      inference('simplify', [status(thm)], ['69'])).
% 2.17/2.39  thf('71', plain,
% 2.17/2.39      (![X0 : $i, X1 : $i]:
% 2.17/2.39         (~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 2.17/2.39          | (v1_relat_1 @ 
% 2.17/2.39             (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 2.17/2.39              (k5_relat_1 @ (k6_relat_1 @ X0) @ X1)))
% 2.17/2.39          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 2.17/2.39          | ~ (v1_relat_1 @ X1)
% 2.17/2.39          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 2.17/2.39      inference('sup-', [status(thm)], ['66', '70'])).
% 2.17/2.39  thf('72', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 2.17/2.39      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.17/2.39  thf('73', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 2.17/2.39      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.17/2.39  thf('74', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 2.17/2.39      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.17/2.39  thf('75', plain,
% 2.17/2.39      (![X0 : $i, X1 : $i]:
% 2.17/2.39         ((v1_relat_1 @ 
% 2.17/2.39           (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 2.17/2.39            (k5_relat_1 @ (k6_relat_1 @ X0) @ X1)))
% 2.17/2.39          | ~ (v1_relat_1 @ X1))),
% 2.17/2.39      inference('demod', [status(thm)], ['71', '72', '73', '74'])).
% 2.17/2.39  thf('76', plain,
% 2.17/2.39      (![X0 : $i, X1 : $i]:
% 2.17/2.39         ((v1_relat_1 @ 
% 2.17/2.39           (k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X1) @ X0))
% 2.17/2.39          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 2.17/2.39          | ~ (v1_relat_1 @ X0)
% 2.17/2.39          | ~ (v1_relat_1 @ X0))),
% 2.17/2.39      inference('sup+', [status(thm)], ['65', '75'])).
% 2.17/2.39  thf(t80_relat_1, axiom,
% 2.17/2.39    (![A:$i]:
% 2.17/2.39     ( ( v1_relat_1 @ A ) =>
% 2.17/2.39       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 2.17/2.39  thf('77', plain,
% 2.17/2.39      (![X31 : $i]:
% 2.17/2.39         (((k5_relat_1 @ X31 @ (k6_relat_1 @ (k2_relat_1 @ X31))) = (X31))
% 2.17/2.39          | ~ (v1_relat_1 @ X31))),
% 2.17/2.39      inference('cnf', [status(esa)], [t80_relat_1])).
% 2.17/2.39  thf('78', plain,
% 2.17/2.39      (![X34 : $i, X35 : $i]:
% 2.17/2.39         (((k7_relat_1 @ X35 @ X34) = (k5_relat_1 @ (k6_relat_1 @ X34) @ X35))
% 2.17/2.39          | ~ (v1_relat_1 @ X35))),
% 2.17/2.39      inference('cnf', [status(esa)], [t94_relat_1])).
% 2.17/2.39  thf('79', plain,
% 2.17/2.39      (![X0 : $i]:
% 2.17/2.39         (((k7_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ (k6_relat_1 @ X0))) @ X0)
% 2.17/2.39            = (k6_relat_1 @ X0))
% 2.17/2.39          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 2.17/2.39          | ~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ (k6_relat_1 @ X0)))))),
% 2.17/2.39      inference('sup+', [status(thm)], ['77', '78'])).
% 2.17/2.39  thf('80', plain, (![X25 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X25)) = (X25))),
% 2.17/2.39      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.17/2.39  thf('81', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 2.17/2.39      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.17/2.39  thf('82', plain, (![X25 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X25)) = (X25))),
% 2.17/2.39      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.17/2.39  thf('83', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 2.17/2.39      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.17/2.39  thf('84', plain,
% 2.17/2.39      (![X0 : $i]: ((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 2.17/2.39      inference('demod', [status(thm)], ['79', '80', '81', '82', '83'])).
% 2.17/2.39  thf('85', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 2.17/2.39      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.17/2.39  thf('86', plain,
% 2.17/2.39      (![X0 : $i, X1 : $i]:
% 2.17/2.39         ((v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 2.17/2.39          | ~ (v1_relat_1 @ X0)
% 2.17/2.39          | ~ (v1_relat_1 @ X0))),
% 2.17/2.39      inference('demod', [status(thm)], ['76', '84', '85'])).
% 2.17/2.39  thf('87', plain,
% 2.17/2.39      (![X0 : $i, X1 : $i]:
% 2.17/2.39         (~ (v1_relat_1 @ X0)
% 2.17/2.39          | (v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 2.17/2.39      inference('simplify', [status(thm)], ['86'])).
% 2.17/2.39  thf('88', plain,
% 2.17/2.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.17/2.39         (~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1))
% 2.17/2.39          | ~ (v1_relat_1 @ X1)
% 2.17/2.39          | ~ (v1_relat_1 @ X0)
% 2.17/2.39          | ~ (v1_relat_1 @ X2)
% 2.17/2.39          | (v1_relat_1 @ (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0))))),
% 2.17/2.39      inference('simplify', [status(thm)], ['69'])).
% 2.17/2.39  thf('89', plain,
% 2.17/2.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.17/2.39         (~ (v1_relat_1 @ X0)
% 2.17/2.39          | (v1_relat_1 @ 
% 2.17/2.39             (k5_relat_1 @ (k6_relat_1 @ X1) @ (k5_relat_1 @ X0 @ X2)))
% 2.17/2.39          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 2.17/2.39          | ~ (v1_relat_1 @ X2)
% 2.17/2.39          | ~ (v1_relat_1 @ X0))),
% 2.17/2.39      inference('sup-', [status(thm)], ['87', '88'])).
% 2.17/2.39  thf('90', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 2.17/2.39      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.17/2.39  thf('91', plain,
% 2.17/2.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.17/2.39         (~ (v1_relat_1 @ X0)
% 2.17/2.39          | (v1_relat_1 @ 
% 2.17/2.39             (k5_relat_1 @ (k6_relat_1 @ X1) @ (k5_relat_1 @ X0 @ X2)))
% 2.17/2.39          | ~ (v1_relat_1 @ X2)
% 2.17/2.39          | ~ (v1_relat_1 @ X0))),
% 2.17/2.39      inference('demod', [status(thm)], ['89', '90'])).
% 2.17/2.39  thf('92', plain,
% 2.17/2.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.17/2.39         (~ (v1_relat_1 @ X2)
% 2.17/2.39          | (v1_relat_1 @ 
% 2.17/2.39             (k5_relat_1 @ (k6_relat_1 @ X1) @ (k5_relat_1 @ X0 @ X2)))
% 2.17/2.39          | ~ (v1_relat_1 @ X0))),
% 2.17/2.39      inference('simplify', [status(thm)], ['91'])).
% 2.17/2.39  thf('93', plain,
% 2.17/2.39      (![X0 : $i, X1 : $i]:
% 2.17/2.39         ((v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))
% 2.17/2.39          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 2.17/2.39          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 2.17/2.39      inference('sup+', [status(thm)], ['64', '92'])).
% 2.17/2.39  thf('94', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 2.17/2.39      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.17/2.39  thf('95', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 2.17/2.39      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.17/2.39  thf('96', plain,
% 2.17/2.39      (![X0 : $i, X1 : $i]:
% 2.17/2.39         (v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 2.17/2.39      inference('demod', [status(thm)], ['93', '94', '95'])).
% 2.17/2.39  thf('97', plain,
% 2.17/2.39      (![X0 : $i, X1 : $i]:
% 2.17/2.39         ((v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 2.17/2.39          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 2.17/2.39      inference('sup+', [status(thm)], ['59', '96'])).
% 2.17/2.39  thf('98', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 2.17/2.39      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.17/2.39  thf('99', plain,
% 2.17/2.39      (![X0 : $i, X1 : $i]:
% 2.17/2.39         (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 2.17/2.39      inference('demod', [status(thm)], ['97', '98'])).
% 2.17/2.39  thf('100', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 2.17/2.39      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.17/2.39  thf('101', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 2.17/2.39      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.17/2.39  thf('102', plain,
% 2.17/2.39      (![X0 : $i, X1 : $i]:
% 2.17/2.39         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 2.17/2.39           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 2.17/2.39      inference('demod', [status(thm)], ['28', '46', '47', '48'])).
% 2.17/2.39  thf('103', plain, (![X24 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X24)) = (X24))),
% 2.17/2.39      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.17/2.39  thf('104', plain,
% 2.17/2.39      (![X32 : $i, X33 : $i]:
% 2.17/2.39         (((k1_relat_1 @ (k7_relat_1 @ X32 @ X33))
% 2.17/2.39            = (k3_xboole_0 @ (k1_relat_1 @ X32) @ X33))
% 2.17/2.39          | ~ (v1_relat_1 @ X32))),
% 2.17/2.39      inference('cnf', [status(esa)], [t90_relat_1])).
% 2.17/2.39  thf('105', plain,
% 2.17/2.39      (![X0 : $i, X1 : $i]:
% 2.17/2.39         (((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 2.17/2.39            = (k3_xboole_0 @ X0 @ X1))
% 2.17/2.39          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 2.17/2.39      inference('sup+', [status(thm)], ['103', '104'])).
% 2.17/2.39  thf('106', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 2.17/2.39      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.17/2.39  thf('107', plain,
% 2.17/2.39      (![X0 : $i, X1 : $i]:
% 2.17/2.39         ((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 2.17/2.39           = (k3_xboole_0 @ X0 @ X1))),
% 2.17/2.39      inference('demod', [status(thm)], ['105', '106'])).
% 2.17/2.39  thf('108', plain,
% 2.17/2.39      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.17/2.39      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.17/2.39  thf('109', plain,
% 2.17/2.39      (![X34 : $i, X35 : $i]:
% 2.17/2.39         (((k7_relat_1 @ X35 @ X34) = (k5_relat_1 @ (k6_relat_1 @ X34) @ X35))
% 2.17/2.39          | ~ (v1_relat_1 @ X35))),
% 2.17/2.39      inference('cnf', [status(esa)], [t94_relat_1])).
% 2.17/2.39  thf('110', plain,
% 2.17/2.39      (![X5 : $i, X6 : $i]: (r1_tarski @ (k3_xboole_0 @ X5 @ X6) @ X5)),
% 2.17/2.39      inference('cnf', [status(esa)], [t17_xboole_1])).
% 2.17/2.39  thf('111', plain, (![X25 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X25)) = (X25))),
% 2.17/2.39      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.17/2.39  thf(t79_relat_1, axiom,
% 2.17/2.39    (![A:$i,B:$i]:
% 2.17/2.39     ( ( v1_relat_1 @ B ) =>
% 2.17/2.39       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 2.17/2.39         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 2.17/2.39  thf('112', plain,
% 2.17/2.39      (![X29 : $i, X30 : $i]:
% 2.17/2.39         (~ (r1_tarski @ (k2_relat_1 @ X29) @ X30)
% 2.17/2.39          | ((k5_relat_1 @ X29 @ (k6_relat_1 @ X30)) = (X29))
% 2.17/2.39          | ~ (v1_relat_1 @ X29))),
% 2.17/2.39      inference('cnf', [status(esa)], [t79_relat_1])).
% 2.17/2.39  thf('113', plain,
% 2.17/2.39      (![X0 : $i, X1 : $i]:
% 2.17/2.39         (~ (r1_tarski @ X0 @ X1)
% 2.17/2.39          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 2.17/2.39          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 2.17/2.39              = (k6_relat_1 @ X0)))),
% 2.17/2.39      inference('sup-', [status(thm)], ['111', '112'])).
% 2.17/2.39  thf('114', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 2.17/2.39      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.17/2.39  thf('115', plain,
% 2.17/2.39      (![X0 : $i, X1 : $i]:
% 2.17/2.39         (~ (r1_tarski @ X0 @ X1)
% 2.17/2.39          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 2.17/2.39              = (k6_relat_1 @ X0)))),
% 2.17/2.39      inference('demod', [status(thm)], ['113', '114'])).
% 2.17/2.39  thf('116', plain,
% 2.17/2.39      (![X0 : $i, X1 : $i]:
% 2.17/2.39         ((k5_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 2.17/2.39           (k6_relat_1 @ X0)) = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 2.17/2.39      inference('sup-', [status(thm)], ['110', '115'])).
% 2.17/2.39  thf('117', plain,
% 2.17/2.39      (![X0 : $i, X1 : $i]:
% 2.17/2.39         (((k7_relat_1 @ (k6_relat_1 @ X1) @ (k3_xboole_0 @ X1 @ X0))
% 2.17/2.39            = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 2.17/2.39          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 2.17/2.39      inference('sup+', [status(thm)], ['109', '116'])).
% 2.17/2.39  thf('118', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 2.17/2.39      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.17/2.39  thf('119', plain,
% 2.17/2.39      (![X0 : $i, X1 : $i]:
% 2.17/2.39         ((k7_relat_1 @ (k6_relat_1 @ X1) @ (k3_xboole_0 @ X1 @ X0))
% 2.17/2.39           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 2.17/2.39      inference('demod', [status(thm)], ['117', '118'])).
% 2.17/2.39  thf('120', plain,
% 2.17/2.39      (![X0 : $i, X1 : $i]:
% 2.17/2.39         ((k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 2.17/2.39           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 2.17/2.39      inference('sup+', [status(thm)], ['108', '119'])).
% 2.17/2.39  thf('121', plain,
% 2.17/2.39      (![X0 : $i, X1 : $i]:
% 2.17/2.39         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 2.17/2.39           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 2.17/2.39      inference('demod', [status(thm)], ['28', '46', '47', '48'])).
% 2.17/2.39  thf('122', plain,
% 2.17/2.39      (![X0 : $i, X1 : $i]:
% 2.17/2.39         ((k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 2.17/2.39           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 2.17/2.39      inference('sup+', [status(thm)], ['108', '119'])).
% 2.17/2.39  thf('123', plain,
% 2.17/2.39      (![X0 : $i, X1 : $i]:
% 2.17/2.39         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 2.17/2.39           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 2.17/2.39      inference('demod', [status(thm)], ['28', '46', '47', '48'])).
% 2.17/2.39  thf('124', plain,
% 2.17/2.39      (![X0 : $i, X1 : $i]:
% 2.17/2.39         ((k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))
% 2.17/2.39           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 2.17/2.39      inference('demod', [status(thm)],
% 2.17/2.39                ['58', '99', '100', '101', '102', '107', '120', '121', '122', 
% 2.17/2.39                 '123'])).
% 2.17/2.39  thf('125', plain,
% 2.17/2.39      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 2.17/2.39         != (k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))),
% 2.17/2.39      inference('demod', [status(thm)], ['4', '124'])).
% 2.17/2.39  thf('126', plain, ($false), inference('simplify', [status(thm)], ['125'])).
% 2.17/2.39  
% 2.17/2.39  % SZS output end Refutation
% 2.17/2.39  
% 2.17/2.39  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
