%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GW0PNBICRJ

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:59 EST 2020

% Result     : Theorem 2.57s
% Output     : Refutation 2.57s
% Verified   : 
% Statistics : Number of formulae       :  161 (1026 expanded)
%              Number of leaves         :   25 ( 370 expanded)
%              Depth                    :   18
%              Number of atoms          : 1419 (8687 expanded)
%              Number of equality atoms :  111 ( 638 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('0',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k7_relat_1 @ X33 @ X32 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X32 ) @ X33 ) )
      | ~ ( v1_relat_1 @ X33 ) ) ),
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
    ! [X15: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('4',plain,(
    ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k7_relat_1 @ X33 @ X32 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X32 ) @ X33 ) )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t76_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B )
        & ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ) )).

thf('6',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X23 @ ( k6_relat_1 @ X24 ) ) @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t76_relat_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('7',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k3_xboole_0 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) @ X0 )
        = ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k3_xboole_0 @ X0 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
        = ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k6_relat_1 @ X0 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','10'])).

thf('12',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('13',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k6_relat_1 @ X0 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k7_relat_1 @ X33 @ X32 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X32 ) @ X33 ) )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('16',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X23 @ ( k6_relat_1 @ X24 ) ) @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t76_relat_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('19',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k6_relat_1 @ X0 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['14','24'])).

thf('26',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k7_relat_1 @ X33 @ X32 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X32 ) @ X33 ) )
      | ~ ( v1_relat_1 @ X33 ) ) ),
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

thf('27',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X19 @ X18 ) @ X20 )
        = ( k5_relat_1 @ X19 @ ( k5_relat_1 @ X18 @ X20 ) ) )
      | ~ ( v1_relat_1 @ X20 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('32',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('33',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['32'])).

thf(t77_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B )
          = B ) ) ) )).

thf('34',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X25 ) @ X26 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X26 ) @ X25 )
        = X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t77_relat_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X0 )
        = ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['31','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) ) ) @ ( k6_relat_1 @ X1 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['25','36'])).

thf('38',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k7_relat_1 @ X33 @ X32 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X32 ) @ X33 ) )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k3_xboole_0 @ X0 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
        = ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(fc1_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('40',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[fc1_relat_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['38','42'])).

thf('44',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('45',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('48',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['14','24'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('50',plain,(
    ! [X21: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X21 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('51',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X30 @ X31 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X30 ) @ X31 ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( k3_xboole_0 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('56',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X22: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X22 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('59',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X27 ) @ X28 )
      | ( ( k5_relat_1 @ X27 @ ( k6_relat_1 @ X28 ) )
        = X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['57','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['14','24'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['14','24'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['57','62'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k6_relat_1 @ X1 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['14','24'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['14','24'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['37','46','47','48','49','54','65','66','71','72'])).

thf('74',plain,(
    ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
 != ( k7_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['4','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('76',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('77',plain,(
    ! [X21: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X21 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('78',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X25 ) @ X26 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X26 ) @ X25 )
        = X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t77_relat_1])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['76','81'])).

thf('83',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X23 @ ( k6_relat_1 @ X24 ) ) @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t76_relat_1])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k6_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['75','86'])).

thf('88',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k7_relat_1 @ X33 @ X32 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X32 ) @ X33 ) )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['76','81'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X0 )
        = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['91','96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X30 @ X31 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X30 ) @ X31 ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) @ ( k1_relat_1 @ X1 ) )
        = ( k6_relat_1 @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k6_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ) @ ( k1_relat_1 @ ( k6_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) )
        = ( k6_relat_1 @ ( k3_xboole_0 @ ( k1_relat_1 @ ( k6_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['99','102'])).

thf('104',plain,(
    ! [X21: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X21 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('105',plain,(
    ! [X21: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X21 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('106',plain,(
    ! [X29: $i] :
      ( ( ( k5_relat_1 @ X29 @ ( k6_relat_1 @ ( k2_relat_1 @ X29 ) ) )
        = X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('107',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k7_relat_1 @ X33 @ X32 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X32 ) @ X33 ) )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) ) @ X0 )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X22: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X22 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('110',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('111',plain,(
    ! [X22: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X22 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('112',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['108','109','110','111','112'])).

thf('114',plain,(
    ! [X21: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X21 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['76','81'])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k3_xboole_0 @ X0 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
        = ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['76','81'])).

thf('121',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['119','120','121'])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['116','122'])).

thf('124',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k6_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['103','104','105','113','114','115','123','124'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['37','46','47','48','49','54','65','66','71','72'])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['37','46','47','48','49','54','65','66','71','72'])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k6_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['125','126','127'])).

thf('129',plain,(
    ! [X21: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X21 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X21: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X21 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['130','131'])).

thf('133',plain,(
    ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
 != ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['74','132'])).

thf('134',plain,(
    $false ),
    inference(simplify,[status(thm)],['133'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GW0PNBICRJ
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:35:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 2.57/2.82  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.57/2.82  % Solved by: fo/fo7.sh
% 2.57/2.82  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.57/2.82  % done 3671 iterations in 2.369s
% 2.57/2.82  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.57/2.82  % SZS output start Refutation
% 2.57/2.82  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.57/2.82  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.57/2.82  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.57/2.82  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 2.57/2.82  thf(sk_B_type, type, sk_B: $i).
% 2.57/2.82  thf(sk_A_type, type, sk_A: $i).
% 2.57/2.82  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 2.57/2.82  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.57/2.82  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.57/2.82  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 2.57/2.82  thf(t94_relat_1, axiom,
% 2.57/2.82    (![A:$i,B:$i]:
% 2.57/2.82     ( ( v1_relat_1 @ B ) =>
% 2.57/2.82       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 2.57/2.82  thf('0', plain,
% 2.57/2.82      (![X32 : $i, X33 : $i]:
% 2.57/2.82         (((k7_relat_1 @ X33 @ X32) = (k5_relat_1 @ (k6_relat_1 @ X32) @ X33))
% 2.57/2.82          | ~ (v1_relat_1 @ X33))),
% 2.57/2.82      inference('cnf', [status(esa)], [t94_relat_1])).
% 2.57/2.82  thf(t43_funct_1, conjecture,
% 2.57/2.82    (![A:$i,B:$i]:
% 2.57/2.82     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 2.57/2.82       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 2.57/2.82  thf(zf_stmt_0, negated_conjecture,
% 2.57/2.82    (~( ![A:$i,B:$i]:
% 2.57/2.82        ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 2.57/2.82          ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 2.57/2.82    inference('cnf.neg', [status(esa)], [t43_funct_1])).
% 2.57/2.82  thf('1', plain,
% 2.57/2.82      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A))
% 2.57/2.82         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 2.57/2.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.57/2.82  thf('2', plain,
% 2.57/2.82      ((((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 2.57/2.82          != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))
% 2.57/2.82        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A)))),
% 2.57/2.82      inference('sup-', [status(thm)], ['0', '1'])).
% 2.57/2.82  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 2.57/2.82  thf('3', plain, (![X15 : $i]: (v1_relat_1 @ (k6_relat_1 @ X15))),
% 2.57/2.82      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.57/2.82  thf('4', plain,
% 2.57/2.82      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 2.57/2.82         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 2.57/2.82      inference('demod', [status(thm)], ['2', '3'])).
% 2.57/2.82  thf('5', plain,
% 2.57/2.82      (![X32 : $i, X33 : $i]:
% 2.57/2.82         (((k7_relat_1 @ X33 @ X32) = (k5_relat_1 @ (k6_relat_1 @ X32) @ X33))
% 2.57/2.82          | ~ (v1_relat_1 @ X33))),
% 2.57/2.82      inference('cnf', [status(esa)], [t94_relat_1])).
% 2.57/2.82  thf(t76_relat_1, axiom,
% 2.57/2.82    (![A:$i,B:$i]:
% 2.57/2.82     ( ( v1_relat_1 @ B ) =>
% 2.57/2.82       ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B ) & 
% 2.57/2.82         ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ))).
% 2.57/2.82  thf('6', plain,
% 2.57/2.82      (![X23 : $i, X24 : $i]:
% 2.57/2.82         ((r1_tarski @ (k5_relat_1 @ X23 @ (k6_relat_1 @ X24)) @ X23)
% 2.57/2.82          | ~ (v1_relat_1 @ X23))),
% 2.57/2.82      inference('cnf', [status(esa)], [t76_relat_1])).
% 2.57/2.82  thf(t28_xboole_1, axiom,
% 2.57/2.82    (![A:$i,B:$i]:
% 2.57/2.82     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 2.57/2.82  thf('7', plain,
% 2.57/2.82      (![X7 : $i, X8 : $i]:
% 2.57/2.82         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 2.57/2.82      inference('cnf', [status(esa)], [t28_xboole_1])).
% 2.57/2.82  thf('8', plain,
% 2.57/2.82      (![X0 : $i, X1 : $i]:
% 2.57/2.82         (~ (v1_relat_1 @ X0)
% 2.57/2.82          | ((k3_xboole_0 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)) @ X0)
% 2.57/2.82              = (k5_relat_1 @ X0 @ (k6_relat_1 @ X1))))),
% 2.57/2.82      inference('sup-', [status(thm)], ['6', '7'])).
% 2.57/2.82  thf(commutativity_k3_xboole_0, axiom,
% 2.57/2.82    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 2.57/2.82  thf('9', plain,
% 2.57/2.82      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.57/2.82      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.57/2.82  thf('10', plain,
% 2.57/2.82      (![X0 : $i, X1 : $i]:
% 2.57/2.82         (~ (v1_relat_1 @ X0)
% 2.57/2.82          | ((k3_xboole_0 @ X0 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 2.57/2.82              = (k5_relat_1 @ X0 @ (k6_relat_1 @ X1))))),
% 2.57/2.82      inference('demod', [status(thm)], ['8', '9'])).
% 2.57/2.82  thf('11', plain,
% 2.57/2.82      (![X0 : $i, X1 : $i]:
% 2.57/2.82         (((k3_xboole_0 @ (k6_relat_1 @ X0) @ 
% 2.57/2.82            (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 2.57/2.82            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1)))
% 2.57/2.82          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 2.57/2.82          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 2.57/2.82      inference('sup+', [status(thm)], ['5', '10'])).
% 2.57/2.82  thf('12', plain, (![X15 : $i]: (v1_relat_1 @ (k6_relat_1 @ X15))),
% 2.57/2.82      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.57/2.82  thf('13', plain, (![X15 : $i]: (v1_relat_1 @ (k6_relat_1 @ X15))),
% 2.57/2.82      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.57/2.82  thf('14', plain,
% 2.57/2.82      (![X0 : $i, X1 : $i]:
% 2.57/2.82         ((k3_xboole_0 @ (k6_relat_1 @ X0) @ 
% 2.57/2.82           (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 2.57/2.82           = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1)))),
% 2.57/2.82      inference('demod', [status(thm)], ['11', '12', '13'])).
% 2.57/2.82  thf('15', plain,
% 2.57/2.82      (![X32 : $i, X33 : $i]:
% 2.57/2.82         (((k7_relat_1 @ X33 @ X32) = (k5_relat_1 @ (k6_relat_1 @ X32) @ X33))
% 2.57/2.82          | ~ (v1_relat_1 @ X33))),
% 2.57/2.82      inference('cnf', [status(esa)], [t94_relat_1])).
% 2.57/2.82  thf('16', plain,
% 2.57/2.82      (![X23 : $i, X24 : $i]:
% 2.57/2.82         ((r1_tarski @ (k5_relat_1 @ X23 @ (k6_relat_1 @ X24)) @ X23)
% 2.57/2.82          | ~ (v1_relat_1 @ X23))),
% 2.57/2.82      inference('cnf', [status(esa)], [t76_relat_1])).
% 2.57/2.82  thf('17', plain,
% 2.57/2.82      (![X0 : $i, X1 : $i]:
% 2.57/2.82         ((r1_tarski @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 2.57/2.82           (k6_relat_1 @ X0))
% 2.57/2.82          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 2.57/2.82          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 2.57/2.82      inference('sup+', [status(thm)], ['15', '16'])).
% 2.57/2.82  thf('18', plain, (![X15 : $i]: (v1_relat_1 @ (k6_relat_1 @ X15))),
% 2.57/2.82      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.57/2.82  thf('19', plain, (![X15 : $i]: (v1_relat_1 @ (k6_relat_1 @ X15))),
% 2.57/2.82      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.57/2.82  thf('20', plain,
% 2.57/2.82      (![X0 : $i, X1 : $i]:
% 2.57/2.82         (r1_tarski @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ (k6_relat_1 @ X0))),
% 2.57/2.82      inference('demod', [status(thm)], ['17', '18', '19'])).
% 2.57/2.82  thf('21', plain,
% 2.57/2.82      (![X7 : $i, X8 : $i]:
% 2.57/2.82         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 2.57/2.82      inference('cnf', [status(esa)], [t28_xboole_1])).
% 2.57/2.82  thf('22', plain,
% 2.57/2.82      (![X0 : $i, X1 : $i]:
% 2.57/2.82         ((k3_xboole_0 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 2.57/2.82           (k6_relat_1 @ X0)) = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 2.57/2.82      inference('sup-', [status(thm)], ['20', '21'])).
% 2.57/2.82  thf('23', plain,
% 2.57/2.82      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.57/2.82      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.57/2.82  thf('24', plain,
% 2.57/2.82      (![X0 : $i, X1 : $i]:
% 2.57/2.82         ((k3_xboole_0 @ (k6_relat_1 @ X0) @ 
% 2.57/2.82           (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 2.57/2.82           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 2.57/2.82      inference('demod', [status(thm)], ['22', '23'])).
% 2.57/2.82  thf('25', plain,
% 2.57/2.82      (![X0 : $i, X1 : $i]:
% 2.57/2.82         ((k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 2.57/2.82           = (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 2.57/2.82      inference('sup+', [status(thm)], ['14', '24'])).
% 2.57/2.82  thf('26', plain,
% 2.57/2.82      (![X32 : $i, X33 : $i]:
% 2.57/2.82         (((k7_relat_1 @ X33 @ X32) = (k5_relat_1 @ (k6_relat_1 @ X32) @ X33))
% 2.57/2.82          | ~ (v1_relat_1 @ X33))),
% 2.57/2.82      inference('cnf', [status(esa)], [t94_relat_1])).
% 2.57/2.82  thf(t55_relat_1, axiom,
% 2.57/2.82    (![A:$i]:
% 2.57/2.82     ( ( v1_relat_1 @ A ) =>
% 2.57/2.82       ( ![B:$i]:
% 2.57/2.82         ( ( v1_relat_1 @ B ) =>
% 2.57/2.82           ( ![C:$i]:
% 2.57/2.82             ( ( v1_relat_1 @ C ) =>
% 2.57/2.82               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 2.57/2.82                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 2.57/2.82  thf('27', plain,
% 2.57/2.82      (![X18 : $i, X19 : $i, X20 : $i]:
% 2.57/2.82         (~ (v1_relat_1 @ X18)
% 2.57/2.82          | ((k5_relat_1 @ (k5_relat_1 @ X19 @ X18) @ X20)
% 2.57/2.82              = (k5_relat_1 @ X19 @ (k5_relat_1 @ X18 @ X20)))
% 2.57/2.82          | ~ (v1_relat_1 @ X20)
% 2.57/2.82          | ~ (v1_relat_1 @ X19))),
% 2.57/2.82      inference('cnf', [status(esa)], [t55_relat_1])).
% 2.57/2.82  thf('28', plain,
% 2.57/2.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.57/2.82         (((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 2.57/2.82            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2)))
% 2.57/2.82          | ~ (v1_relat_1 @ X1)
% 2.57/2.82          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 2.57/2.82          | ~ (v1_relat_1 @ X2)
% 2.57/2.82          | ~ (v1_relat_1 @ X1))),
% 2.57/2.82      inference('sup+', [status(thm)], ['26', '27'])).
% 2.57/2.82  thf('29', plain, (![X15 : $i]: (v1_relat_1 @ (k6_relat_1 @ X15))),
% 2.57/2.82      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.57/2.82  thf('30', plain,
% 2.57/2.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.57/2.82         (((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 2.57/2.82            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2)))
% 2.57/2.82          | ~ (v1_relat_1 @ X1)
% 2.57/2.82          | ~ (v1_relat_1 @ X2)
% 2.57/2.82          | ~ (v1_relat_1 @ X1))),
% 2.57/2.82      inference('demod', [status(thm)], ['28', '29'])).
% 2.57/2.82  thf('31', plain,
% 2.57/2.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.57/2.82         (~ (v1_relat_1 @ X2)
% 2.57/2.82          | ~ (v1_relat_1 @ X1)
% 2.57/2.82          | ((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 2.57/2.82              = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2))))),
% 2.57/2.82      inference('simplify', [status(thm)], ['30'])).
% 2.57/2.82  thf(d10_xboole_0, axiom,
% 2.57/2.82    (![A:$i,B:$i]:
% 2.57/2.82     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.57/2.82  thf('32', plain,
% 2.57/2.82      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 2.57/2.82      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.57/2.82  thf('33', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 2.57/2.82      inference('simplify', [status(thm)], ['32'])).
% 2.57/2.82  thf(t77_relat_1, axiom,
% 2.57/2.82    (![A:$i,B:$i]:
% 2.57/2.82     ( ( v1_relat_1 @ B ) =>
% 2.57/2.82       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 2.57/2.82         ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ) ))).
% 2.57/2.82  thf('34', plain,
% 2.57/2.82      (![X25 : $i, X26 : $i]:
% 2.57/2.82         (~ (r1_tarski @ (k1_relat_1 @ X25) @ X26)
% 2.57/2.82          | ((k5_relat_1 @ (k6_relat_1 @ X26) @ X25) = (X25))
% 2.57/2.82          | ~ (v1_relat_1 @ X25))),
% 2.57/2.82      inference('cnf', [status(esa)], [t77_relat_1])).
% 2.57/2.82  thf('35', plain,
% 2.57/2.82      (![X0 : $i]:
% 2.57/2.82         (~ (v1_relat_1 @ X0)
% 2.57/2.82          | ((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X0) = (X0)))),
% 2.57/2.82      inference('sup-', [status(thm)], ['33', '34'])).
% 2.57/2.82  thf('36', plain,
% 2.57/2.82      (![X0 : $i, X1 : $i]:
% 2.57/2.82         (((k5_relat_1 @ 
% 2.57/2.82            (k7_relat_1 @ X1 @ (k1_relat_1 @ (k5_relat_1 @ X1 @ X0))) @ X0)
% 2.57/2.82            = (k5_relat_1 @ X1 @ X0))
% 2.57/2.82          | ~ (v1_relat_1 @ X1)
% 2.57/2.82          | ~ (v1_relat_1 @ X0)
% 2.57/2.82          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0)))),
% 2.57/2.82      inference('sup+', [status(thm)], ['31', '35'])).
% 2.57/2.82  thf('37', plain,
% 2.57/2.82      (![X0 : $i, X1 : $i]:
% 2.57/2.82         (~ (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 2.57/2.82          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 2.57/2.82          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 2.57/2.82          | ((k5_relat_1 @ 
% 2.57/2.82              (k7_relat_1 @ (k6_relat_1 @ X0) @ 
% 2.57/2.82               (k1_relat_1 @ 
% 2.57/2.82                (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1)))) @ 
% 2.57/2.82              (k6_relat_1 @ X1))
% 2.57/2.82              = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))))),
% 2.57/2.82      inference('sup-', [status(thm)], ['25', '36'])).
% 2.57/2.82  thf('38', plain,
% 2.57/2.82      (![X32 : $i, X33 : $i]:
% 2.57/2.82         (((k7_relat_1 @ X33 @ X32) = (k5_relat_1 @ (k6_relat_1 @ X32) @ X33))
% 2.57/2.82          | ~ (v1_relat_1 @ X33))),
% 2.57/2.82      inference('cnf', [status(esa)], [t94_relat_1])).
% 2.57/2.82  thf('39', plain,
% 2.57/2.82      (![X0 : $i, X1 : $i]:
% 2.57/2.82         (~ (v1_relat_1 @ X0)
% 2.57/2.82          | ((k3_xboole_0 @ X0 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 2.57/2.82              = (k5_relat_1 @ X0 @ (k6_relat_1 @ X1))))),
% 2.57/2.82      inference('demod', [status(thm)], ['8', '9'])).
% 2.57/2.82  thf(fc1_relat_1, axiom,
% 2.57/2.82    (![A:$i,B:$i]:
% 2.57/2.82     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 2.57/2.82  thf('40', plain,
% 2.57/2.82      (![X16 : $i, X17 : $i]:
% 2.57/2.82         (~ (v1_relat_1 @ X16) | (v1_relat_1 @ (k3_xboole_0 @ X16 @ X17)))),
% 2.57/2.82      inference('cnf', [status(esa)], [fc1_relat_1])).
% 2.57/2.82  thf('41', plain,
% 2.57/2.82      (![X0 : $i, X1 : $i]:
% 2.57/2.82         ((v1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 2.57/2.82          | ~ (v1_relat_1 @ X1)
% 2.57/2.82          | ~ (v1_relat_1 @ X1))),
% 2.57/2.82      inference('sup+', [status(thm)], ['39', '40'])).
% 2.57/2.82  thf('42', plain,
% 2.57/2.82      (![X0 : $i, X1 : $i]:
% 2.57/2.82         (~ (v1_relat_1 @ X1)
% 2.57/2.82          | (v1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 2.57/2.82      inference('simplify', [status(thm)], ['41'])).
% 2.57/2.82  thf('43', plain,
% 2.57/2.82      (![X0 : $i, X1 : $i]:
% 2.57/2.82         ((v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 2.57/2.82          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 2.57/2.82          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 2.57/2.82      inference('sup+', [status(thm)], ['38', '42'])).
% 2.57/2.82  thf('44', plain, (![X15 : $i]: (v1_relat_1 @ (k6_relat_1 @ X15))),
% 2.57/2.82      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.57/2.82  thf('45', plain, (![X15 : $i]: (v1_relat_1 @ (k6_relat_1 @ X15))),
% 2.57/2.82      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.57/2.82  thf('46', plain,
% 2.57/2.82      (![X0 : $i, X1 : $i]:
% 2.57/2.82         (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 2.57/2.82      inference('demod', [status(thm)], ['43', '44', '45'])).
% 2.57/2.82  thf('47', plain, (![X15 : $i]: (v1_relat_1 @ (k6_relat_1 @ X15))),
% 2.57/2.82      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.57/2.82  thf('48', plain, (![X15 : $i]: (v1_relat_1 @ (k6_relat_1 @ X15))),
% 2.57/2.82      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.57/2.82  thf('49', plain,
% 2.57/2.82      (![X0 : $i, X1 : $i]:
% 2.57/2.82         ((k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 2.57/2.82           = (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 2.57/2.82      inference('sup+', [status(thm)], ['14', '24'])).
% 2.57/2.82  thf(t71_relat_1, axiom,
% 2.57/2.82    (![A:$i]:
% 2.57/2.82     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 2.57/2.82       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 2.57/2.82  thf('50', plain, (![X21 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X21)) = (X21))),
% 2.57/2.82      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.57/2.82  thf(t90_relat_1, axiom,
% 2.57/2.82    (![A:$i,B:$i]:
% 2.57/2.82     ( ( v1_relat_1 @ B ) =>
% 2.57/2.82       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 2.57/2.82         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 2.57/2.82  thf('51', plain,
% 2.57/2.82      (![X30 : $i, X31 : $i]:
% 2.57/2.82         (((k1_relat_1 @ (k7_relat_1 @ X30 @ X31))
% 2.57/2.82            = (k3_xboole_0 @ (k1_relat_1 @ X30) @ X31))
% 2.57/2.82          | ~ (v1_relat_1 @ X30))),
% 2.57/2.82      inference('cnf', [status(esa)], [t90_relat_1])).
% 2.57/2.82  thf('52', plain,
% 2.57/2.82      (![X0 : $i, X1 : $i]:
% 2.57/2.82         (((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 2.57/2.82            = (k3_xboole_0 @ X0 @ X1))
% 2.57/2.82          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 2.57/2.82      inference('sup+', [status(thm)], ['50', '51'])).
% 2.57/2.82  thf('53', plain, (![X15 : $i]: (v1_relat_1 @ (k6_relat_1 @ X15))),
% 2.57/2.82      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.57/2.82  thf('54', plain,
% 2.57/2.82      (![X0 : $i, X1 : $i]:
% 2.57/2.82         ((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 2.57/2.82           = (k3_xboole_0 @ X0 @ X1))),
% 2.57/2.82      inference('demod', [status(thm)], ['52', '53'])).
% 2.57/2.82  thf('55', plain,
% 2.57/2.82      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.57/2.82      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.57/2.82  thf(t17_xboole_1, axiom,
% 2.57/2.82    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 2.57/2.82  thf('56', plain,
% 2.57/2.82      (![X5 : $i, X6 : $i]: (r1_tarski @ (k3_xboole_0 @ X5 @ X6) @ X5)),
% 2.57/2.82      inference('cnf', [status(esa)], [t17_xboole_1])).
% 2.57/2.82  thf('57', plain,
% 2.57/2.82      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 2.57/2.82      inference('sup+', [status(thm)], ['55', '56'])).
% 2.57/2.82  thf('58', plain, (![X22 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X22)) = (X22))),
% 2.57/2.82      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.57/2.82  thf(t79_relat_1, axiom,
% 2.57/2.82    (![A:$i,B:$i]:
% 2.57/2.82     ( ( v1_relat_1 @ B ) =>
% 2.57/2.82       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 2.57/2.82         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 2.57/2.82  thf('59', plain,
% 2.57/2.82      (![X27 : $i, X28 : $i]:
% 2.57/2.82         (~ (r1_tarski @ (k2_relat_1 @ X27) @ X28)
% 2.57/2.82          | ((k5_relat_1 @ X27 @ (k6_relat_1 @ X28)) = (X27))
% 2.57/2.82          | ~ (v1_relat_1 @ X27))),
% 2.57/2.82      inference('cnf', [status(esa)], [t79_relat_1])).
% 2.57/2.82  thf('60', plain,
% 2.57/2.82      (![X0 : $i, X1 : $i]:
% 2.57/2.82         (~ (r1_tarski @ X0 @ X1)
% 2.57/2.82          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 2.57/2.82          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 2.57/2.82              = (k6_relat_1 @ X0)))),
% 2.57/2.82      inference('sup-', [status(thm)], ['58', '59'])).
% 2.57/2.82  thf('61', plain, (![X15 : $i]: (v1_relat_1 @ (k6_relat_1 @ X15))),
% 2.57/2.82      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.57/2.82  thf('62', plain,
% 2.57/2.82      (![X0 : $i, X1 : $i]:
% 2.57/2.82         (~ (r1_tarski @ X0 @ X1)
% 2.57/2.82          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 2.57/2.82              = (k6_relat_1 @ X0)))),
% 2.57/2.82      inference('demod', [status(thm)], ['60', '61'])).
% 2.57/2.82  thf('63', plain,
% 2.57/2.82      (![X0 : $i, X1 : $i]:
% 2.57/2.82         ((k5_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 2.57/2.82           (k6_relat_1 @ X0)) = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 2.57/2.82      inference('sup-', [status(thm)], ['57', '62'])).
% 2.57/2.82  thf('64', plain,
% 2.57/2.82      (![X0 : $i, X1 : $i]:
% 2.57/2.82         ((k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 2.57/2.82           = (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 2.57/2.82      inference('sup+', [status(thm)], ['14', '24'])).
% 2.57/2.82  thf('65', plain,
% 2.57/2.82      (![X0 : $i, X1 : $i]:
% 2.57/2.82         ((k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 2.57/2.82           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 2.57/2.82      inference('demod', [status(thm)], ['63', '64'])).
% 2.57/2.82  thf('66', plain,
% 2.57/2.82      (![X0 : $i, X1 : $i]:
% 2.57/2.82         ((k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 2.57/2.82           = (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 2.57/2.82      inference('sup+', [status(thm)], ['14', '24'])).
% 2.57/2.82  thf('67', plain,
% 2.57/2.82      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.57/2.82      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.57/2.82  thf('68', plain,
% 2.57/2.82      (![X0 : $i, X1 : $i]:
% 2.57/2.82         ((k5_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 2.57/2.82           (k6_relat_1 @ X0)) = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 2.57/2.82      inference('sup-', [status(thm)], ['57', '62'])).
% 2.57/2.82  thf('69', plain,
% 2.57/2.82      (![X0 : $i, X1 : $i]:
% 2.57/2.82         ((k5_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 2.57/2.82           (k6_relat_1 @ X1)) = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 2.57/2.82      inference('sup+', [status(thm)], ['67', '68'])).
% 2.57/2.82  thf('70', plain,
% 2.57/2.82      (![X0 : $i, X1 : $i]:
% 2.57/2.82         ((k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 2.57/2.82           = (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 2.57/2.82      inference('sup+', [status(thm)], ['14', '24'])).
% 2.57/2.82  thf('71', plain,
% 2.57/2.82      (![X0 : $i, X1 : $i]:
% 2.57/2.82         ((k7_relat_1 @ (k6_relat_1 @ X1) @ (k3_xboole_0 @ X1 @ X0))
% 2.57/2.82           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 2.57/2.82      inference('demod', [status(thm)], ['69', '70'])).
% 2.57/2.82  thf('72', plain,
% 2.57/2.82      (![X0 : $i, X1 : $i]:
% 2.57/2.82         ((k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 2.57/2.82           = (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 2.57/2.82      inference('sup+', [status(thm)], ['14', '24'])).
% 2.57/2.82  thf('73', plain,
% 2.57/2.82      (![X0 : $i, X1 : $i]:
% 2.57/2.82         ((k6_relat_1 @ (k3_xboole_0 @ X0 @ X1))
% 2.57/2.82           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 2.57/2.82      inference('demod', [status(thm)],
% 2.57/2.82                ['37', '46', '47', '48', '49', '54', '65', '66', '71', '72'])).
% 2.57/2.82  thf('74', plain,
% 2.57/2.82      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 2.57/2.82         != (k7_relat_1 @ (k6_relat_1 @ sk_B) @ sk_A))),
% 2.57/2.82      inference('demod', [status(thm)], ['4', '73'])).
% 2.57/2.82  thf('75', plain,
% 2.57/2.82      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.57/2.82      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.57/2.82  thf('76', plain,
% 2.57/2.82      (![X5 : $i, X6 : $i]: (r1_tarski @ (k3_xboole_0 @ X5 @ X6) @ X5)),
% 2.57/2.82      inference('cnf', [status(esa)], [t17_xboole_1])).
% 2.57/2.82  thf('77', plain, (![X21 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X21)) = (X21))),
% 2.57/2.82      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.57/2.82  thf('78', plain,
% 2.57/2.82      (![X25 : $i, X26 : $i]:
% 2.57/2.82         (~ (r1_tarski @ (k1_relat_1 @ X25) @ X26)
% 2.57/2.82          | ((k5_relat_1 @ (k6_relat_1 @ X26) @ X25) = (X25))
% 2.57/2.82          | ~ (v1_relat_1 @ X25))),
% 2.57/2.82      inference('cnf', [status(esa)], [t77_relat_1])).
% 2.57/2.82  thf('79', plain,
% 2.57/2.82      (![X0 : $i, X1 : $i]:
% 2.57/2.82         (~ (r1_tarski @ X0 @ X1)
% 2.57/2.82          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 2.57/2.82          | ((k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 2.57/2.82              = (k6_relat_1 @ X0)))),
% 2.57/2.82      inference('sup-', [status(thm)], ['77', '78'])).
% 2.57/2.82  thf('80', plain, (![X15 : $i]: (v1_relat_1 @ (k6_relat_1 @ X15))),
% 2.57/2.82      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.57/2.82  thf('81', plain,
% 2.57/2.82      (![X0 : $i, X1 : $i]:
% 2.57/2.82         (~ (r1_tarski @ X0 @ X1)
% 2.57/2.82          | ((k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 2.57/2.82              = (k6_relat_1 @ X0)))),
% 2.57/2.82      inference('demod', [status(thm)], ['79', '80'])).
% 2.57/2.82  thf('82', plain,
% 2.57/2.82      (![X0 : $i, X1 : $i]:
% 2.57/2.82         ((k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 2.57/2.82           (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))
% 2.57/2.82           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 2.57/2.82      inference('sup-', [status(thm)], ['76', '81'])).
% 2.57/2.82  thf('83', plain,
% 2.57/2.82      (![X23 : $i, X24 : $i]:
% 2.57/2.82         ((r1_tarski @ (k5_relat_1 @ X23 @ (k6_relat_1 @ X24)) @ X23)
% 2.57/2.82          | ~ (v1_relat_1 @ X23))),
% 2.57/2.82      inference('cnf', [status(esa)], [t76_relat_1])).
% 2.57/2.82  thf('84', plain,
% 2.57/2.82      (![X0 : $i, X1 : $i]:
% 2.57/2.82         ((r1_tarski @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 2.57/2.82           (k6_relat_1 @ X1))
% 2.57/2.82          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 2.57/2.82      inference('sup+', [status(thm)], ['82', '83'])).
% 2.57/2.82  thf('85', plain, (![X15 : $i]: (v1_relat_1 @ (k6_relat_1 @ X15))),
% 2.57/2.82      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.57/2.82  thf('86', plain,
% 2.57/2.82      (![X0 : $i, X1 : $i]:
% 2.57/2.82         (r1_tarski @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 2.57/2.82          (k6_relat_1 @ X1))),
% 2.57/2.82      inference('demod', [status(thm)], ['84', '85'])).
% 2.57/2.82  thf('87', plain,
% 2.57/2.82      (![X0 : $i, X1 : $i]:
% 2.57/2.82         (r1_tarski @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 2.57/2.82          (k6_relat_1 @ X0))),
% 2.57/2.82      inference('sup+', [status(thm)], ['75', '86'])).
% 2.57/2.82  thf('88', plain,
% 2.57/2.82      (![X7 : $i, X8 : $i]:
% 2.57/2.82         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 2.57/2.82      inference('cnf', [status(esa)], [t28_xboole_1])).
% 2.57/2.82  thf('89', plain,
% 2.57/2.82      (![X0 : $i, X1 : $i]:
% 2.57/2.82         ((k3_xboole_0 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 2.57/2.82           (k6_relat_1 @ X0)) = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 2.57/2.82      inference('sup-', [status(thm)], ['87', '88'])).
% 2.57/2.82  thf('90', plain,
% 2.57/2.82      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.57/2.82      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.57/2.82  thf('91', plain,
% 2.57/2.82      (![X0 : $i, X1 : $i]:
% 2.57/2.82         ((k3_xboole_0 @ (k6_relat_1 @ X0) @ 
% 2.57/2.82           (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 2.57/2.82           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 2.57/2.82      inference('demod', [status(thm)], ['89', '90'])).
% 2.57/2.82  thf('92', plain,
% 2.57/2.82      (![X32 : $i, X33 : $i]:
% 2.57/2.82         (((k7_relat_1 @ X33 @ X32) = (k5_relat_1 @ (k6_relat_1 @ X32) @ X33))
% 2.57/2.82          | ~ (v1_relat_1 @ X33))),
% 2.57/2.82      inference('cnf', [status(esa)], [t94_relat_1])).
% 2.57/2.82  thf('93', plain,
% 2.57/2.82      (![X0 : $i, X1 : $i]:
% 2.57/2.82         ((k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 2.57/2.82           (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))
% 2.57/2.82           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 2.57/2.82      inference('sup-', [status(thm)], ['76', '81'])).
% 2.57/2.82  thf('94', plain,
% 2.57/2.82      (![X0 : $i, X1 : $i]:
% 2.57/2.82         (((k7_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ X0)
% 2.57/2.82            = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))
% 2.57/2.82          | ~ (v1_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1))))),
% 2.57/2.82      inference('sup+', [status(thm)], ['92', '93'])).
% 2.57/2.82  thf('95', plain, (![X15 : $i]: (v1_relat_1 @ (k6_relat_1 @ X15))),
% 2.57/2.82      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.57/2.82  thf('96', plain,
% 2.57/2.82      (![X0 : $i, X1 : $i]:
% 2.57/2.82         ((k7_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ X0)
% 2.57/2.82           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 2.57/2.82      inference('demod', [status(thm)], ['94', '95'])).
% 2.57/2.82  thf('97', plain,
% 2.57/2.82      (![X0 : $i, X1 : $i]:
% 2.57/2.82         ((k7_relat_1 @ 
% 2.57/2.82           (k6_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))) @ 
% 2.57/2.82           (k6_relat_1 @ X0))
% 2.57/2.82           = (k6_relat_1 @ 
% 2.57/2.82              (k3_xboole_0 @ (k6_relat_1 @ X0) @ 
% 2.57/2.82               (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))))),
% 2.57/2.82      inference('sup+', [status(thm)], ['91', '96'])).
% 2.57/2.82  thf('98', plain,
% 2.57/2.82      (![X0 : $i, X1 : $i]:
% 2.57/2.82         ((k3_xboole_0 @ (k6_relat_1 @ X0) @ 
% 2.57/2.82           (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 2.57/2.82           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 2.57/2.82      inference('demod', [status(thm)], ['89', '90'])).
% 2.57/2.82  thf('99', plain,
% 2.57/2.82      (![X0 : $i, X1 : $i]:
% 2.57/2.82         ((k7_relat_1 @ 
% 2.57/2.82           (k6_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))) @ 
% 2.57/2.82           (k6_relat_1 @ X0))
% 2.57/2.82           = (k6_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))),
% 2.57/2.82      inference('demod', [status(thm)], ['97', '98'])).
% 2.57/2.82  thf('100', plain,
% 2.57/2.82      (![X30 : $i, X31 : $i]:
% 2.57/2.82         (((k1_relat_1 @ (k7_relat_1 @ X30 @ X31))
% 2.57/2.82            = (k3_xboole_0 @ (k1_relat_1 @ X30) @ X31))
% 2.57/2.82          | ~ (v1_relat_1 @ X30))),
% 2.57/2.82      inference('cnf', [status(esa)], [t90_relat_1])).
% 2.57/2.82  thf('101', plain,
% 2.57/2.82      (![X0 : $i, X1 : $i]:
% 2.57/2.82         ((k7_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ X0)
% 2.57/2.82           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 2.57/2.82      inference('demod', [status(thm)], ['94', '95'])).
% 2.57/2.82  thf('102', plain,
% 2.57/2.82      (![X0 : $i, X1 : $i]:
% 2.57/2.82         (((k7_relat_1 @ 
% 2.57/2.82            (k6_relat_1 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))) @ 
% 2.57/2.82            (k1_relat_1 @ X1))
% 2.57/2.82            = (k6_relat_1 @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0)))
% 2.57/2.82          | ~ (v1_relat_1 @ X1))),
% 2.57/2.82      inference('sup+', [status(thm)], ['100', '101'])).
% 2.57/2.82  thf('103', plain,
% 2.57/2.82      (![X0 : $i, X1 : $i]:
% 2.57/2.82         (((k7_relat_1 @ 
% 2.57/2.82            (k6_relat_1 @ 
% 2.57/2.82             (k1_relat_1 @ 
% 2.57/2.82              (k6_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))) @ 
% 2.57/2.82            (k1_relat_1 @ (k6_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))))
% 2.57/2.82            = (k6_relat_1 @ 
% 2.57/2.82               (k3_xboole_0 @ 
% 2.57/2.82                (k1_relat_1 @ 
% 2.57/2.82                 (k6_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))) @ 
% 2.57/2.82                (k6_relat_1 @ X0))))
% 2.57/2.82          | ~ (v1_relat_1 @ 
% 2.57/2.82               (k6_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))))),
% 2.57/2.82      inference('sup+', [status(thm)], ['99', '102'])).
% 2.57/2.82  thf('104', plain, (![X21 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X21)) = (X21))),
% 2.57/2.82      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.57/2.82  thf('105', plain, (![X21 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X21)) = (X21))),
% 2.57/2.82      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.57/2.82  thf(t80_relat_1, axiom,
% 2.57/2.82    (![A:$i]:
% 2.57/2.82     ( ( v1_relat_1 @ A ) =>
% 2.57/2.82       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 2.57/2.82  thf('106', plain,
% 2.57/2.82      (![X29 : $i]:
% 2.57/2.82         (((k5_relat_1 @ X29 @ (k6_relat_1 @ (k2_relat_1 @ X29))) = (X29))
% 2.57/2.82          | ~ (v1_relat_1 @ X29))),
% 2.57/2.82      inference('cnf', [status(esa)], [t80_relat_1])).
% 2.57/2.82  thf('107', plain,
% 2.57/2.82      (![X32 : $i, X33 : $i]:
% 2.57/2.82         (((k7_relat_1 @ X33 @ X32) = (k5_relat_1 @ (k6_relat_1 @ X32) @ X33))
% 2.57/2.82          | ~ (v1_relat_1 @ X33))),
% 2.57/2.82      inference('cnf', [status(esa)], [t94_relat_1])).
% 2.57/2.82  thf('108', plain,
% 2.57/2.82      (![X0 : $i]:
% 2.57/2.82         (((k7_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ (k6_relat_1 @ X0))) @ X0)
% 2.57/2.82            = (k6_relat_1 @ X0))
% 2.57/2.82          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 2.57/2.82          | ~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ (k6_relat_1 @ X0)))))),
% 2.57/2.82      inference('sup+', [status(thm)], ['106', '107'])).
% 2.57/2.82  thf('109', plain, (![X22 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X22)) = (X22))),
% 2.57/2.82      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.57/2.82  thf('110', plain, (![X15 : $i]: (v1_relat_1 @ (k6_relat_1 @ X15))),
% 2.57/2.82      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.57/2.82  thf('111', plain, (![X22 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X22)) = (X22))),
% 2.57/2.82      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.57/2.82  thf('112', plain, (![X15 : $i]: (v1_relat_1 @ (k6_relat_1 @ X15))),
% 2.57/2.82      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.57/2.82  thf('113', plain,
% 2.57/2.82      (![X0 : $i]: ((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 2.57/2.82      inference('demod', [status(thm)], ['108', '109', '110', '111', '112'])).
% 2.57/2.82  thf('114', plain, (![X21 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X21)) = (X21))),
% 2.57/2.82      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.57/2.82  thf('115', plain,
% 2.57/2.82      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.57/2.82      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.57/2.82  thf('116', plain,
% 2.57/2.82      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.57/2.82      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.57/2.82  thf('117', plain,
% 2.57/2.82      (![X0 : $i, X1 : $i]:
% 2.57/2.82         ((k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 2.57/2.82           (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))
% 2.57/2.82           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 2.57/2.82      inference('sup-', [status(thm)], ['76', '81'])).
% 2.57/2.82  thf('118', plain,
% 2.57/2.82      (![X0 : $i, X1 : $i]:
% 2.57/2.82         (~ (v1_relat_1 @ X0)
% 2.57/2.82          | ((k3_xboole_0 @ X0 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 2.57/2.82              = (k5_relat_1 @ X0 @ (k6_relat_1 @ X1))))),
% 2.57/2.82      inference('demod', [status(thm)], ['8', '9'])).
% 2.57/2.82  thf('119', plain,
% 2.57/2.82      (![X0 : $i, X1 : $i]:
% 2.57/2.82         (((k3_xboole_0 @ (k6_relat_1 @ X1) @ 
% 2.57/2.82            (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 2.57/2.82            = (k5_relat_1 @ (k6_relat_1 @ X1) @ 
% 2.57/2.82               (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))
% 2.57/2.82          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 2.57/2.82      inference('sup+', [status(thm)], ['117', '118'])).
% 2.57/2.82  thf('120', plain,
% 2.57/2.82      (![X0 : $i, X1 : $i]:
% 2.57/2.82         ((k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 2.57/2.82           (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))
% 2.57/2.82           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 2.57/2.82      inference('sup-', [status(thm)], ['76', '81'])).
% 2.57/2.82  thf('121', plain, (![X15 : $i]: (v1_relat_1 @ (k6_relat_1 @ X15))),
% 2.57/2.82      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.57/2.82  thf('122', plain,
% 2.57/2.82      (![X0 : $i, X1 : $i]:
% 2.57/2.82         ((k3_xboole_0 @ (k6_relat_1 @ X1) @ 
% 2.57/2.82           (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 2.57/2.82           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 2.57/2.82      inference('demod', [status(thm)], ['119', '120', '121'])).
% 2.57/2.82  thf('123', plain,
% 2.57/2.82      (![X0 : $i, X1 : $i]:
% 2.57/2.82         ((k3_xboole_0 @ (k6_relat_1 @ X0) @ 
% 2.57/2.82           (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 2.57/2.82           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 2.57/2.82      inference('sup+', [status(thm)], ['116', '122'])).
% 2.57/2.82  thf('124', plain, (![X15 : $i]: (v1_relat_1 @ (k6_relat_1 @ X15))),
% 2.57/2.82      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.57/2.82  thf('125', plain,
% 2.57/2.82      (![X0 : $i, X1 : $i]:
% 2.57/2.82         ((k6_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 2.57/2.82           = (k6_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1))))),
% 2.57/2.82      inference('demod', [status(thm)],
% 2.57/2.82                ['103', '104', '105', '113', '114', '115', '123', '124'])).
% 2.57/2.82  thf('126', plain,
% 2.57/2.82      (![X0 : $i, X1 : $i]:
% 2.57/2.82         ((k6_relat_1 @ (k3_xboole_0 @ X0 @ X1))
% 2.57/2.82           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 2.57/2.82      inference('demod', [status(thm)],
% 2.57/2.82                ['37', '46', '47', '48', '49', '54', '65', '66', '71', '72'])).
% 2.57/2.82  thf('127', plain,
% 2.57/2.82      (![X0 : $i, X1 : $i]:
% 2.57/2.82         ((k6_relat_1 @ (k3_xboole_0 @ X0 @ X1))
% 2.57/2.82           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 2.57/2.82      inference('demod', [status(thm)],
% 2.57/2.82                ['37', '46', '47', '48', '49', '54', '65', '66', '71', '72'])).
% 2.57/2.82  thf('128', plain,
% 2.57/2.82      (![X0 : $i, X1 : $i]:
% 2.57/2.82         ((k6_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 2.57/2.82           = (k6_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 2.57/2.82      inference('demod', [status(thm)], ['125', '126', '127'])).
% 2.57/2.82  thf('129', plain, (![X21 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X21)) = (X21))),
% 2.57/2.82      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.57/2.82  thf('130', plain,
% 2.57/2.82      (![X0 : $i, X1 : $i]:
% 2.57/2.82         ((k1_relat_1 @ (k6_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))
% 2.57/2.82           = (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 2.57/2.82      inference('sup+', [status(thm)], ['128', '129'])).
% 2.57/2.82  thf('131', plain, (![X21 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X21)) = (X21))),
% 2.57/2.82      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.57/2.82  thf('132', plain,
% 2.57/2.82      (![X0 : $i, X1 : $i]:
% 2.57/2.82         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 2.57/2.82           = (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 2.57/2.82      inference('demod', [status(thm)], ['130', '131'])).
% 2.57/2.82  thf('133', plain,
% 2.57/2.82      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 2.57/2.82         != (k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))),
% 2.57/2.82      inference('demod', [status(thm)], ['74', '132'])).
% 2.57/2.82  thf('134', plain, ($false), inference('simplify', [status(thm)], ['133'])).
% 2.57/2.82  
% 2.57/2.82  % SZS output end Refutation
% 2.57/2.82  
% 2.57/2.83  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
