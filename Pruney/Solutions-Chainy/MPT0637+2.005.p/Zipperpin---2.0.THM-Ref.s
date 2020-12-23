%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UUYoFmWq10

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:55 EST 2020

% Result     : Theorem 8.46s
% Output     : Refutation 8.46s
% Verified   : 
% Statistics : Number of formulae       :  154 (1250 expanded)
%              Number of leaves         :   21 ( 451 expanded)
%              Depth                    :   23
%              Number of atoms          : 1474 (11284 expanded)
%              Number of equality atoms :   84 ( 879 expanded)
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
    ! [X26: $i,X27: $i] :
      ( ( ( k7_relat_1 @ X27 @ X26 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X26 ) @ X27 ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
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

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('7',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('8',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X28 ) @ X29 )
      | ( ( k7_relat_1 @ X28 @ X29 )
        = X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k7_relat_1 @ X27 @ X26 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X26 ) @ X27 ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t76_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B )
        & ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ) )).

thf('11',plain,(
    ! [X24: $i,X25: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X24 @ ( k6_relat_1 @ X25 ) ) @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t76_relat_1])).

thf('12',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      | ( X0
        = ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k6_relat_1 @ X0 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ( ( k6_relat_1 @ X0 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('16',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k6_relat_1 @ X0 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ( ( k6_relat_1 @ X0 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k6_relat_1 @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k6_relat_1 @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['9','17'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('19',plain,(
    ! [X22: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X22 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('20',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['6'])).

thf('21',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('22',plain,(
    ! [X22: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X22 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('23',plain,(
    ! [X22: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X22 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k6_relat_1 @ X0 )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['18','19','20','21','22','23'])).

thf('25',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k7_relat_1 @ X27 @ X26 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X26 ) @ X27 ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
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

thf('26',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X20 @ X19 ) @ X21 )
        = ( k5_relat_1 @ X20 @ ( k5_relat_1 @ X19 @ X21 ) ) )
      | ~ ( v1_relat_1 @ X21 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ ( k6_relat_1 @ X0 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['24','30'])).

thf('32',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('33',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ ( k6_relat_1 @ X0 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ ( k1_relat_1 @ ( k6_relat_1 @ X1 ) ) @ X0 ) ) @ ( k6_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['5','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ ( k6_relat_1 @ X0 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('37',plain,(
    ! [X22: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X22 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('38',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['35','36','37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      | ( X0
        = ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      | ( ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['35','36','37','38'])).

thf('43',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      | ( ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k7_relat_1 @ X27 @ X26 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X26 ) @ X27 ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['35','36','37','38'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X22: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X22 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('49',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k7_relat_1 @ X17 @ X18 )
        = ( k7_relat_1 @ X17 @ ( k3_xboole_0 @ ( k1_relat_1 @ X17 ) @ X18 ) ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t192_relat_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['47','52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['47','52','53'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ( ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) )
        = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['44','54','55'])).

thf('57',plain,(
    ! [X22: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X22 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k6_relat_1 @ X0 )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['18','19','20','21','22','23'])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k6_relat_1 @ X0 )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['18','19','20','21','22','23'])).

thf('65',plain,(
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

thf('66',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_relat_1 @ X12 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['64','68'])).

thf('70',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('71',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('72',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['69','70','71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['63','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('76',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('82',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['62','83'])).

thf('85',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('86',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['84','85','86'])).

thf('88',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X20 @ X19 ) @ X21 )
        = ( k5_relat_1 @ X20 @ ( k5_relat_1 @ X19 @ X21 ) ) )
      | ~ ( v1_relat_1 @ X21 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('89',plain,(
    ! [X24: $i,X25: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X24 @ ( k6_relat_1 @ X25 ) ) @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t76_relat_1])).

thf('90',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('92',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X2 ) ) ) @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['87','92'])).

thf('94',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('95',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('96',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X2 ) ) ) @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['93','94','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['47','52','53'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ ( k6_relat_1 @ X0 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['47','52','53'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ ( k6_relat_1 @ X0 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('102',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X2 ) @ ( k6_relat_1 @ X1 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf(t100_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('104',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X14 @ X15 ) @ X16 )
        = ( k7_relat_1 @ X14 @ ( k3_xboole_0 @ X15 @ X16 ) ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('105',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X14 @ X15 ) @ X16 )
        = ( k7_relat_1 @ X14 @ ( k3_xboole_0 @ X15 @ X16 ) ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('106',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X3 )
        = ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ ( k3_xboole_0 @ X0 @ X3 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k7_relat_1 @ X27 @ X26 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X26 ) @ X27 ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('108',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_relat_1 @ X12 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X3 )
        = ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ ( k3_xboole_0 @ X0 @ X3 ) ) ) ) ),
    inference(clc,[status(thm)],['106','112'])).

thf('114',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X2 )
        = ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X1 ) @ ( k3_xboole_0 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['103','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('116',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('117',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X2 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k3_xboole_0 @ X0 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['114','115','116'])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ ( k6_relat_1 @ X0 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['111'])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('125',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k3_xboole_0 @ X0 @ X2 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['102','117','118','123','124'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['47','52','53'])).

thf('127',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k7_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['96','97','125','126'])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['61','127'])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['56','128'])).

thf('130',plain,(
    ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','129'])).

thf('131',plain,(
    $false ),
    inference(simplify,[status(thm)],['130'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UUYoFmWq10
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:39:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 8.46/8.70  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 8.46/8.70  % Solved by: fo/fo7.sh
% 8.46/8.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 8.46/8.70  % done 4941 iterations in 8.207s
% 8.46/8.70  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 8.46/8.70  % SZS output start Refutation
% 8.46/8.70  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 8.46/8.70  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 8.46/8.70  thf(sk_B_type, type, sk_B: $i).
% 8.46/8.70  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 8.46/8.70  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 8.46/8.70  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 8.46/8.70  thf(sk_A_type, type, sk_A: $i).
% 8.46/8.70  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 8.46/8.70  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 8.46/8.70  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 8.46/8.70  thf(t94_relat_1, axiom,
% 8.46/8.70    (![A:$i,B:$i]:
% 8.46/8.70     ( ( v1_relat_1 @ B ) =>
% 8.46/8.70       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 8.46/8.70  thf('0', plain,
% 8.46/8.70      (![X26 : $i, X27 : $i]:
% 8.46/8.70         (((k7_relat_1 @ X27 @ X26) = (k5_relat_1 @ (k6_relat_1 @ X26) @ X27))
% 8.46/8.70          | ~ (v1_relat_1 @ X27))),
% 8.46/8.70      inference('cnf', [status(esa)], [t94_relat_1])).
% 8.46/8.70  thf(t43_funct_1, conjecture,
% 8.46/8.70    (![A:$i,B:$i]:
% 8.46/8.70     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 8.46/8.70       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 8.46/8.70  thf(zf_stmt_0, negated_conjecture,
% 8.46/8.70    (~( ![A:$i,B:$i]:
% 8.46/8.70        ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 8.46/8.70          ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 8.46/8.70    inference('cnf.neg', [status(esa)], [t43_funct_1])).
% 8.46/8.70  thf('1', plain,
% 8.46/8.70      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A))
% 8.46/8.70         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 8.46/8.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.46/8.70  thf('2', plain,
% 8.46/8.70      ((((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 8.46/8.70          != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))
% 8.46/8.70        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A)))),
% 8.46/8.70      inference('sup-', [status(thm)], ['0', '1'])).
% 8.46/8.70  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 8.46/8.70  thf('3', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 8.46/8.70      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 8.46/8.70  thf('4', plain,
% 8.46/8.70      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 8.46/8.70         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 8.46/8.70      inference('demod', [status(thm)], ['2', '3'])).
% 8.46/8.70  thf(t192_relat_1, axiom,
% 8.46/8.70    (![A:$i,B:$i]:
% 8.46/8.70     ( ( v1_relat_1 @ B ) =>
% 8.46/8.70       ( ( k7_relat_1 @ B @ A ) =
% 8.46/8.70         ( k7_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ))).
% 8.46/8.70  thf('5', plain,
% 8.46/8.70      (![X17 : $i, X18 : $i]:
% 8.46/8.70         (((k7_relat_1 @ X17 @ X18)
% 8.46/8.70            = (k7_relat_1 @ X17 @ (k3_xboole_0 @ (k1_relat_1 @ X17) @ X18)))
% 8.46/8.70          | ~ (v1_relat_1 @ X17))),
% 8.46/8.70      inference('cnf', [status(esa)], [t192_relat_1])).
% 8.46/8.70  thf(d10_xboole_0, axiom,
% 8.46/8.70    (![A:$i,B:$i]:
% 8.46/8.70     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 8.46/8.70  thf('6', plain,
% 8.46/8.70      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 8.46/8.70      inference('cnf', [status(esa)], [d10_xboole_0])).
% 8.46/8.70  thf('7', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 8.46/8.70      inference('simplify', [status(thm)], ['6'])).
% 8.46/8.70  thf(t97_relat_1, axiom,
% 8.46/8.70    (![A:$i,B:$i]:
% 8.46/8.70     ( ( v1_relat_1 @ B ) =>
% 8.46/8.70       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 8.46/8.70         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 8.46/8.70  thf('8', plain,
% 8.46/8.70      (![X28 : $i, X29 : $i]:
% 8.46/8.70         (~ (r1_tarski @ (k1_relat_1 @ X28) @ X29)
% 8.46/8.70          | ((k7_relat_1 @ X28 @ X29) = (X28))
% 8.46/8.70          | ~ (v1_relat_1 @ X28))),
% 8.46/8.70      inference('cnf', [status(esa)], [t97_relat_1])).
% 8.46/8.70  thf('9', plain,
% 8.46/8.70      (![X0 : $i]:
% 8.46/8.70         (~ (v1_relat_1 @ X0) | ((k7_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (X0)))),
% 8.46/8.70      inference('sup-', [status(thm)], ['7', '8'])).
% 8.46/8.70  thf('10', plain,
% 8.46/8.70      (![X26 : $i, X27 : $i]:
% 8.46/8.70         (((k7_relat_1 @ X27 @ X26) = (k5_relat_1 @ (k6_relat_1 @ X26) @ X27))
% 8.46/8.70          | ~ (v1_relat_1 @ X27))),
% 8.46/8.70      inference('cnf', [status(esa)], [t94_relat_1])).
% 8.46/8.70  thf(t76_relat_1, axiom,
% 8.46/8.70    (![A:$i,B:$i]:
% 8.46/8.70     ( ( v1_relat_1 @ B ) =>
% 8.46/8.70       ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B ) & 
% 8.46/8.70         ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ))).
% 8.46/8.70  thf('11', plain,
% 8.46/8.70      (![X24 : $i, X25 : $i]:
% 8.46/8.70         ((r1_tarski @ (k5_relat_1 @ X24 @ (k6_relat_1 @ X25)) @ X24)
% 8.46/8.70          | ~ (v1_relat_1 @ X24))),
% 8.46/8.70      inference('cnf', [status(esa)], [t76_relat_1])).
% 8.46/8.70  thf('12', plain,
% 8.46/8.70      (![X0 : $i, X2 : $i]:
% 8.46/8.70         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 8.46/8.70      inference('cnf', [status(esa)], [d10_xboole_0])).
% 8.46/8.70  thf('13', plain,
% 8.46/8.70      (![X0 : $i, X1 : $i]:
% 8.46/8.70         (~ (v1_relat_1 @ X0)
% 8.46/8.70          | ~ (r1_tarski @ X0 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 8.46/8.70          | ((X0) = (k5_relat_1 @ X0 @ (k6_relat_1 @ X1))))),
% 8.46/8.70      inference('sup-', [status(thm)], ['11', '12'])).
% 8.46/8.70  thf('14', plain,
% 8.46/8.70      (![X0 : $i, X1 : $i]:
% 8.46/8.70         (~ (r1_tarski @ (k6_relat_1 @ X0) @ 
% 8.46/8.70             (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 8.46/8.70          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 8.46/8.70          | ((k6_relat_1 @ X0)
% 8.46/8.70              = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1)))
% 8.46/8.70          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 8.46/8.70      inference('sup-', [status(thm)], ['10', '13'])).
% 8.46/8.70  thf('15', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 8.46/8.70      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 8.46/8.70  thf('16', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 8.46/8.70      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 8.46/8.70  thf('17', plain,
% 8.46/8.70      (![X0 : $i, X1 : $i]:
% 8.46/8.70         (~ (r1_tarski @ (k6_relat_1 @ X0) @ 
% 8.46/8.70             (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 8.46/8.70          | ((k6_relat_1 @ X0)
% 8.46/8.70              = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))))),
% 8.46/8.70      inference('demod', [status(thm)], ['14', '15', '16'])).
% 8.46/8.70  thf('18', plain,
% 8.46/8.70      (![X0 : $i]:
% 8.46/8.70         (~ (r1_tarski @ (k6_relat_1 @ (k1_relat_1 @ (k6_relat_1 @ X0))) @ 
% 8.46/8.70             (k6_relat_1 @ X0))
% 8.46/8.70          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 8.46/8.70          | ((k6_relat_1 @ (k1_relat_1 @ (k6_relat_1 @ X0)))
% 8.46/8.70              = (k5_relat_1 @ 
% 8.46/8.70                 (k6_relat_1 @ (k1_relat_1 @ (k6_relat_1 @ X0))) @ 
% 8.46/8.70                 (k6_relat_1 @ X0))))),
% 8.46/8.70      inference('sup-', [status(thm)], ['9', '17'])).
% 8.46/8.70  thf(t71_relat_1, axiom,
% 8.46/8.70    (![A:$i]:
% 8.46/8.70     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 8.46/8.70       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 8.46/8.70  thf('19', plain, (![X22 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X22)) = (X22))),
% 8.46/8.70      inference('cnf', [status(esa)], [t71_relat_1])).
% 8.46/8.70  thf('20', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 8.46/8.70      inference('simplify', [status(thm)], ['6'])).
% 8.46/8.70  thf('21', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 8.46/8.70      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 8.46/8.70  thf('22', plain, (![X22 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X22)) = (X22))),
% 8.46/8.70      inference('cnf', [status(esa)], [t71_relat_1])).
% 8.46/8.70  thf('23', plain, (![X22 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X22)) = (X22))),
% 8.46/8.70      inference('cnf', [status(esa)], [t71_relat_1])).
% 8.46/8.70  thf('24', plain,
% 8.46/8.70      (![X0 : $i]:
% 8.46/8.70         ((k6_relat_1 @ X0)
% 8.46/8.70           = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0)))),
% 8.46/8.70      inference('demod', [status(thm)], ['18', '19', '20', '21', '22', '23'])).
% 8.46/8.70  thf('25', plain,
% 8.46/8.70      (![X26 : $i, X27 : $i]:
% 8.46/8.70         (((k7_relat_1 @ X27 @ X26) = (k5_relat_1 @ (k6_relat_1 @ X26) @ X27))
% 8.46/8.70          | ~ (v1_relat_1 @ X27))),
% 8.46/8.70      inference('cnf', [status(esa)], [t94_relat_1])).
% 8.46/8.70  thf(t55_relat_1, axiom,
% 8.46/8.70    (![A:$i]:
% 8.46/8.70     ( ( v1_relat_1 @ A ) =>
% 8.46/8.70       ( ![B:$i]:
% 8.46/8.70         ( ( v1_relat_1 @ B ) =>
% 8.46/8.70           ( ![C:$i]:
% 8.46/8.70             ( ( v1_relat_1 @ C ) =>
% 8.46/8.70               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 8.46/8.70                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 8.46/8.70  thf('26', plain,
% 8.46/8.70      (![X19 : $i, X20 : $i, X21 : $i]:
% 8.46/8.70         (~ (v1_relat_1 @ X19)
% 8.46/8.70          | ((k5_relat_1 @ (k5_relat_1 @ X20 @ X19) @ X21)
% 8.46/8.70              = (k5_relat_1 @ X20 @ (k5_relat_1 @ X19 @ X21)))
% 8.46/8.70          | ~ (v1_relat_1 @ X21)
% 8.46/8.70          | ~ (v1_relat_1 @ X20))),
% 8.46/8.70      inference('cnf', [status(esa)], [t55_relat_1])).
% 8.46/8.70  thf('27', plain,
% 8.46/8.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.46/8.70         (((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 8.46/8.70            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2)))
% 8.46/8.70          | ~ (v1_relat_1 @ X1)
% 8.46/8.70          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 8.46/8.70          | ~ (v1_relat_1 @ X2)
% 8.46/8.70          | ~ (v1_relat_1 @ X1))),
% 8.46/8.70      inference('sup+', [status(thm)], ['25', '26'])).
% 8.46/8.70  thf('28', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 8.46/8.70      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 8.46/8.70  thf('29', plain,
% 8.46/8.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.46/8.70         (((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 8.46/8.70            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2)))
% 8.46/8.70          | ~ (v1_relat_1 @ X1)
% 8.46/8.70          | ~ (v1_relat_1 @ X2)
% 8.46/8.70          | ~ (v1_relat_1 @ X1))),
% 8.46/8.70      inference('demod', [status(thm)], ['27', '28'])).
% 8.46/8.70  thf('30', plain,
% 8.46/8.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.46/8.70         (~ (v1_relat_1 @ X2)
% 8.46/8.70          | ~ (v1_relat_1 @ X1)
% 8.46/8.70          | ((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 8.46/8.70              = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2))))),
% 8.46/8.70      inference('simplify', [status(thm)], ['29'])).
% 8.46/8.70  thf('31', plain,
% 8.46/8.70      (![X0 : $i, X1 : $i]:
% 8.46/8.70         (((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1) @ 
% 8.46/8.70            (k6_relat_1 @ X0))
% 8.46/8.70            = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))
% 8.46/8.70          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 8.46/8.70          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 8.46/8.70      inference('sup+', [status(thm)], ['24', '30'])).
% 8.46/8.70  thf('32', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 8.46/8.70      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 8.46/8.70  thf('33', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 8.46/8.70      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 8.46/8.70  thf('34', plain,
% 8.46/8.70      (![X0 : $i, X1 : $i]:
% 8.46/8.70         ((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1) @ 
% 8.46/8.70           (k6_relat_1 @ X0))
% 8.46/8.70           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 8.46/8.70      inference('demod', [status(thm)], ['31', '32', '33'])).
% 8.46/8.70  thf('35', plain,
% 8.46/8.70      (![X0 : $i, X1 : $i]:
% 8.46/8.70         (((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 8.46/8.70            (k6_relat_1 @ X1))
% 8.46/8.70            = (k5_relat_1 @ 
% 8.46/8.70               (k6_relat_1 @ 
% 8.46/8.70                (k3_xboole_0 @ (k1_relat_1 @ (k6_relat_1 @ X1)) @ X0)) @ 
% 8.46/8.70               (k6_relat_1 @ X1)))
% 8.46/8.70          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 8.46/8.70      inference('sup+', [status(thm)], ['5', '34'])).
% 8.46/8.70  thf('36', plain,
% 8.46/8.70      (![X0 : $i, X1 : $i]:
% 8.46/8.70         ((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1) @ 
% 8.46/8.70           (k6_relat_1 @ X0))
% 8.46/8.70           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 8.46/8.70      inference('demod', [status(thm)], ['31', '32', '33'])).
% 8.46/8.70  thf('37', plain, (![X22 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X22)) = (X22))),
% 8.46/8.70      inference('cnf', [status(esa)], [t71_relat_1])).
% 8.46/8.70  thf('38', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 8.46/8.70      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 8.46/8.70  thf('39', plain,
% 8.46/8.70      (![X0 : $i, X1 : $i]:
% 8.46/8.70         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 8.46/8.70           = (k5_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 8.46/8.70              (k6_relat_1 @ X1)))),
% 8.46/8.70      inference('demod', [status(thm)], ['35', '36', '37', '38'])).
% 8.46/8.70  thf('40', plain,
% 8.46/8.70      (![X0 : $i, X1 : $i]:
% 8.46/8.70         (~ (v1_relat_1 @ X0)
% 8.46/8.70          | ~ (r1_tarski @ X0 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 8.46/8.70          | ((X0) = (k5_relat_1 @ X0 @ (k6_relat_1 @ X1))))),
% 8.46/8.70      inference('sup-', [status(thm)], ['11', '12'])).
% 8.46/8.70  thf('41', plain,
% 8.46/8.70      (![X0 : $i, X1 : $i]:
% 8.46/8.70         (~ (r1_tarski @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 8.46/8.70             (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))
% 8.46/8.70          | ((k6_relat_1 @ (k3_xboole_0 @ X0 @ X1))
% 8.46/8.70              = (k5_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 8.46/8.70                 (k6_relat_1 @ X0)))
% 8.46/8.70          | ~ (v1_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1))))),
% 8.46/8.70      inference('sup-', [status(thm)], ['39', '40'])).
% 8.46/8.70  thf('42', plain,
% 8.46/8.70      (![X0 : $i, X1 : $i]:
% 8.46/8.70         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 8.46/8.70           = (k5_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 8.46/8.70              (k6_relat_1 @ X1)))),
% 8.46/8.70      inference('demod', [status(thm)], ['35', '36', '37', '38'])).
% 8.46/8.70  thf('43', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 8.46/8.70      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 8.46/8.70  thf('44', plain,
% 8.46/8.70      (![X0 : $i, X1 : $i]:
% 8.46/8.70         (~ (r1_tarski @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 8.46/8.70             (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))
% 8.46/8.70          | ((k6_relat_1 @ (k3_xboole_0 @ X0 @ X1))
% 8.46/8.70              = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))))),
% 8.46/8.70      inference('demod', [status(thm)], ['41', '42', '43'])).
% 8.46/8.70  thf('45', plain,
% 8.46/8.70      (![X26 : $i, X27 : $i]:
% 8.46/8.70         (((k7_relat_1 @ X27 @ X26) = (k5_relat_1 @ (k6_relat_1 @ X26) @ X27))
% 8.46/8.70          | ~ (v1_relat_1 @ X27))),
% 8.46/8.70      inference('cnf', [status(esa)], [t94_relat_1])).
% 8.46/8.70  thf('46', plain,
% 8.46/8.70      (![X0 : $i, X1 : $i]:
% 8.46/8.70         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 8.46/8.70           = (k5_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 8.46/8.70              (k6_relat_1 @ X1)))),
% 8.46/8.70      inference('demod', [status(thm)], ['35', '36', '37', '38'])).
% 8.46/8.70  thf('47', plain,
% 8.46/8.70      (![X0 : $i, X1 : $i]:
% 8.46/8.70         (((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 8.46/8.70            = (k7_relat_1 @ (k6_relat_1 @ X1) @ (k3_xboole_0 @ X1 @ X0)))
% 8.46/8.70          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 8.46/8.70      inference('sup+', [status(thm)], ['45', '46'])).
% 8.46/8.70  thf('48', plain, (![X22 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X22)) = (X22))),
% 8.46/8.70      inference('cnf', [status(esa)], [t71_relat_1])).
% 8.46/8.70  thf('49', plain,
% 8.46/8.70      (![X17 : $i, X18 : $i]:
% 8.46/8.70         (((k7_relat_1 @ X17 @ X18)
% 8.46/8.70            = (k7_relat_1 @ X17 @ (k3_xboole_0 @ (k1_relat_1 @ X17) @ X18)))
% 8.46/8.70          | ~ (v1_relat_1 @ X17))),
% 8.46/8.70      inference('cnf', [status(esa)], [t192_relat_1])).
% 8.46/8.70  thf('50', plain,
% 8.46/8.70      (![X0 : $i, X1 : $i]:
% 8.46/8.70         (((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 8.46/8.70            = (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))
% 8.46/8.70          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 8.46/8.70      inference('sup+', [status(thm)], ['48', '49'])).
% 8.46/8.70  thf('51', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 8.46/8.70      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 8.46/8.70  thf('52', plain,
% 8.46/8.70      (![X0 : $i, X1 : $i]:
% 8.46/8.70         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 8.46/8.70           = (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 8.46/8.70      inference('demod', [status(thm)], ['50', '51'])).
% 8.46/8.70  thf('53', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 8.46/8.70      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 8.46/8.70  thf('54', plain,
% 8.46/8.70      (![X0 : $i, X1 : $i]:
% 8.46/8.70         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 8.46/8.70           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 8.46/8.70      inference('demod', [status(thm)], ['47', '52', '53'])).
% 8.46/8.70  thf('55', plain,
% 8.46/8.70      (![X0 : $i, X1 : $i]:
% 8.46/8.70         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 8.46/8.70           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 8.46/8.70      inference('demod', [status(thm)], ['47', '52', '53'])).
% 8.46/8.70  thf('56', plain,
% 8.46/8.70      (![X0 : $i, X1 : $i]:
% 8.46/8.70         (~ (r1_tarski @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 8.46/8.70             (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 8.46/8.70          | ((k6_relat_1 @ (k3_xboole_0 @ X0 @ X1))
% 8.46/8.70              = (k7_relat_1 @ (k6_relat_1 @ X0) @ X1)))),
% 8.46/8.70      inference('demod', [status(thm)], ['44', '54', '55'])).
% 8.46/8.70  thf('57', plain, (![X22 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X22)) = (X22))),
% 8.46/8.70      inference('cnf', [status(esa)], [t71_relat_1])).
% 8.46/8.70  thf('58', plain,
% 8.46/8.70      (![X0 : $i]:
% 8.46/8.70         (~ (v1_relat_1 @ X0) | ((k7_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (X0)))),
% 8.46/8.70      inference('sup-', [status(thm)], ['7', '8'])).
% 8.46/8.70  thf('59', plain,
% 8.46/8.70      (![X0 : $i]:
% 8.46/8.70         (((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))
% 8.46/8.70          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 8.46/8.70      inference('sup+', [status(thm)], ['57', '58'])).
% 8.46/8.70  thf('60', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 8.46/8.70      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 8.46/8.70  thf('61', plain,
% 8.46/8.70      (![X0 : $i]: ((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 8.46/8.70      inference('demod', [status(thm)], ['59', '60'])).
% 8.46/8.70  thf('62', plain,
% 8.46/8.70      (![X0 : $i]:
% 8.46/8.70         ((k6_relat_1 @ X0)
% 8.46/8.70           = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0)))),
% 8.46/8.70      inference('demod', [status(thm)], ['18', '19', '20', '21', '22', '23'])).
% 8.46/8.70  thf('63', plain,
% 8.46/8.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.46/8.70         (~ (v1_relat_1 @ X2)
% 8.46/8.70          | ~ (v1_relat_1 @ X1)
% 8.46/8.70          | ((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 8.46/8.70              = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2))))),
% 8.46/8.70      inference('simplify', [status(thm)], ['29'])).
% 8.46/8.70  thf('64', plain,
% 8.46/8.70      (![X0 : $i]:
% 8.46/8.70         ((k6_relat_1 @ X0)
% 8.46/8.70           = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0)))),
% 8.46/8.70      inference('demod', [status(thm)], ['18', '19', '20', '21', '22', '23'])).
% 8.46/8.70  thf('65', plain,
% 8.46/8.70      (![X19 : $i, X20 : $i, X21 : $i]:
% 8.46/8.70         (~ (v1_relat_1 @ X19)
% 8.46/8.70          | ((k5_relat_1 @ (k5_relat_1 @ X20 @ X19) @ X21)
% 8.46/8.70              = (k5_relat_1 @ X20 @ (k5_relat_1 @ X19 @ X21)))
% 8.46/8.70          | ~ (v1_relat_1 @ X21)
% 8.46/8.70          | ~ (v1_relat_1 @ X20))),
% 8.46/8.70      inference('cnf', [status(esa)], [t55_relat_1])).
% 8.46/8.70  thf(dt_k5_relat_1, axiom,
% 8.46/8.70    (![A:$i,B:$i]:
% 8.46/8.70     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 8.46/8.70       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 8.46/8.70  thf('66', plain,
% 8.46/8.70      (![X11 : $i, X12 : $i]:
% 8.46/8.70         (~ (v1_relat_1 @ X11)
% 8.46/8.70          | ~ (v1_relat_1 @ X12)
% 8.46/8.70          | (v1_relat_1 @ (k5_relat_1 @ X11 @ X12)))),
% 8.46/8.70      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 8.46/8.70  thf('67', plain,
% 8.46/8.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.46/8.70         ((v1_relat_1 @ (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0)))
% 8.46/8.70          | ~ (v1_relat_1 @ X2)
% 8.46/8.70          | ~ (v1_relat_1 @ X0)
% 8.46/8.70          | ~ (v1_relat_1 @ X1)
% 8.46/8.70          | ~ (v1_relat_1 @ X0)
% 8.46/8.70          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1)))),
% 8.46/8.70      inference('sup+', [status(thm)], ['65', '66'])).
% 8.46/8.70  thf('68', plain,
% 8.46/8.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.46/8.70         (~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1))
% 8.46/8.70          | ~ (v1_relat_1 @ X1)
% 8.46/8.70          | ~ (v1_relat_1 @ X0)
% 8.46/8.70          | ~ (v1_relat_1 @ X2)
% 8.46/8.70          | (v1_relat_1 @ (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0))))),
% 8.46/8.70      inference('simplify', [status(thm)], ['67'])).
% 8.46/8.70  thf('69', plain,
% 8.46/8.70      (![X0 : $i, X1 : $i]:
% 8.46/8.70         (~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 8.46/8.70          | (v1_relat_1 @ 
% 8.46/8.70             (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 8.46/8.70              (k5_relat_1 @ (k6_relat_1 @ X0) @ X1)))
% 8.46/8.70          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 8.46/8.70          | ~ (v1_relat_1 @ X1)
% 8.46/8.70          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 8.46/8.70      inference('sup-', [status(thm)], ['64', '68'])).
% 8.46/8.70  thf('70', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 8.46/8.70      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 8.46/8.70  thf('71', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 8.46/8.70      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 8.46/8.70  thf('72', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 8.46/8.70      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 8.46/8.70  thf('73', plain,
% 8.46/8.70      (![X0 : $i, X1 : $i]:
% 8.46/8.70         ((v1_relat_1 @ 
% 8.46/8.70           (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 8.46/8.70            (k5_relat_1 @ (k6_relat_1 @ X0) @ X1)))
% 8.46/8.70          | ~ (v1_relat_1 @ X1))),
% 8.46/8.70      inference('demod', [status(thm)], ['69', '70', '71', '72'])).
% 8.46/8.70  thf('74', plain,
% 8.46/8.70      (![X0 : $i, X1 : $i]:
% 8.46/8.70         ((v1_relat_1 @ 
% 8.46/8.70           (k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X1) @ X0))
% 8.46/8.70          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 8.46/8.70          | ~ (v1_relat_1 @ X0)
% 8.46/8.70          | ~ (v1_relat_1 @ X0))),
% 8.46/8.70      inference('sup+', [status(thm)], ['63', '73'])).
% 8.46/8.70  thf('75', plain,
% 8.46/8.70      (![X0 : $i]: ((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 8.46/8.70      inference('demod', [status(thm)], ['59', '60'])).
% 8.46/8.70  thf('76', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 8.46/8.70      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 8.46/8.70  thf('77', plain,
% 8.46/8.70      (![X0 : $i, X1 : $i]:
% 8.46/8.70         ((v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 8.46/8.70          | ~ (v1_relat_1 @ X0)
% 8.46/8.70          | ~ (v1_relat_1 @ X0))),
% 8.46/8.70      inference('demod', [status(thm)], ['74', '75', '76'])).
% 8.46/8.70  thf('78', plain,
% 8.46/8.70      (![X0 : $i, X1 : $i]:
% 8.46/8.70         (~ (v1_relat_1 @ X0)
% 8.46/8.70          | (v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 8.46/8.70      inference('simplify', [status(thm)], ['77'])).
% 8.46/8.70  thf('79', plain,
% 8.46/8.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.46/8.70         (~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1))
% 8.46/8.70          | ~ (v1_relat_1 @ X1)
% 8.46/8.70          | ~ (v1_relat_1 @ X0)
% 8.46/8.70          | ~ (v1_relat_1 @ X2)
% 8.46/8.70          | (v1_relat_1 @ (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0))))),
% 8.46/8.70      inference('simplify', [status(thm)], ['67'])).
% 8.46/8.70  thf('80', plain,
% 8.46/8.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.46/8.70         (~ (v1_relat_1 @ X0)
% 8.46/8.70          | (v1_relat_1 @ 
% 8.46/8.70             (k5_relat_1 @ (k6_relat_1 @ X1) @ (k5_relat_1 @ X0 @ X2)))
% 8.46/8.70          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 8.46/8.70          | ~ (v1_relat_1 @ X2)
% 8.46/8.70          | ~ (v1_relat_1 @ X0))),
% 8.46/8.70      inference('sup-', [status(thm)], ['78', '79'])).
% 8.46/8.70  thf('81', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 8.46/8.70      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 8.46/8.70  thf('82', plain,
% 8.46/8.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.46/8.70         (~ (v1_relat_1 @ X0)
% 8.46/8.70          | (v1_relat_1 @ 
% 8.46/8.70             (k5_relat_1 @ (k6_relat_1 @ X1) @ (k5_relat_1 @ X0 @ X2)))
% 8.46/8.70          | ~ (v1_relat_1 @ X2)
% 8.46/8.70          | ~ (v1_relat_1 @ X0))),
% 8.46/8.70      inference('demod', [status(thm)], ['80', '81'])).
% 8.46/8.70  thf('83', plain,
% 8.46/8.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.46/8.70         (~ (v1_relat_1 @ X2)
% 8.46/8.70          | (v1_relat_1 @ 
% 8.46/8.70             (k5_relat_1 @ (k6_relat_1 @ X1) @ (k5_relat_1 @ X0 @ X2)))
% 8.46/8.70          | ~ (v1_relat_1 @ X0))),
% 8.46/8.70      inference('simplify', [status(thm)], ['82'])).
% 8.46/8.70  thf('84', plain,
% 8.46/8.70      (![X0 : $i, X1 : $i]:
% 8.46/8.70         ((v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))
% 8.46/8.70          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 8.46/8.70          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 8.46/8.70      inference('sup+', [status(thm)], ['62', '83'])).
% 8.46/8.70  thf('85', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 8.46/8.70      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 8.46/8.70  thf('86', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 8.46/8.70      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 8.46/8.70  thf('87', plain,
% 8.46/8.70      (![X0 : $i, X1 : $i]:
% 8.46/8.70         (v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 8.46/8.70      inference('demod', [status(thm)], ['84', '85', '86'])).
% 8.46/8.70  thf('88', plain,
% 8.46/8.70      (![X19 : $i, X20 : $i, X21 : $i]:
% 8.46/8.70         (~ (v1_relat_1 @ X19)
% 8.46/8.70          | ((k5_relat_1 @ (k5_relat_1 @ X20 @ X19) @ X21)
% 8.46/8.70              = (k5_relat_1 @ X20 @ (k5_relat_1 @ X19 @ X21)))
% 8.46/8.70          | ~ (v1_relat_1 @ X21)
% 8.46/8.70          | ~ (v1_relat_1 @ X20))),
% 8.46/8.70      inference('cnf', [status(esa)], [t55_relat_1])).
% 8.46/8.70  thf('89', plain,
% 8.46/8.70      (![X24 : $i, X25 : $i]:
% 8.46/8.70         ((r1_tarski @ (k5_relat_1 @ X24 @ (k6_relat_1 @ X25)) @ X24)
% 8.46/8.70          | ~ (v1_relat_1 @ X24))),
% 8.46/8.70      inference('cnf', [status(esa)], [t76_relat_1])).
% 8.46/8.70  thf('90', plain,
% 8.46/8.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.46/8.70         ((r1_tarski @ 
% 8.46/8.70           (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ 
% 8.46/8.70           (k5_relat_1 @ X2 @ X1))
% 8.46/8.70          | ~ (v1_relat_1 @ X2)
% 8.46/8.70          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 8.46/8.70          | ~ (v1_relat_1 @ X1)
% 8.46/8.70          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1)))),
% 8.46/8.70      inference('sup+', [status(thm)], ['88', '89'])).
% 8.46/8.70  thf('91', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 8.46/8.70      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 8.46/8.70  thf('92', plain,
% 8.46/8.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.46/8.70         ((r1_tarski @ 
% 8.46/8.70           (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ 
% 8.46/8.70           (k5_relat_1 @ X2 @ X1))
% 8.46/8.70          | ~ (v1_relat_1 @ X2)
% 8.46/8.70          | ~ (v1_relat_1 @ X1)
% 8.46/8.70          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1)))),
% 8.46/8.70      inference('demod', [status(thm)], ['90', '91'])).
% 8.46/8.70  thf('93', plain,
% 8.46/8.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.46/8.70         (~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 8.46/8.70          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 8.46/8.70          | (r1_tarski @ 
% 8.46/8.70             (k5_relat_1 @ (k6_relat_1 @ X1) @ 
% 8.46/8.70              (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X2))) @ 
% 8.46/8.70             (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))))),
% 8.46/8.70      inference('sup-', [status(thm)], ['87', '92'])).
% 8.46/8.70  thf('94', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 8.46/8.70      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 8.46/8.70  thf('95', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 8.46/8.70      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 8.46/8.70  thf('96', plain,
% 8.46/8.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.46/8.70         (r1_tarski @ 
% 8.46/8.70          (k5_relat_1 @ (k6_relat_1 @ X1) @ 
% 8.46/8.70           (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X2))) @ 
% 8.46/8.70          (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 8.46/8.70      inference('demod', [status(thm)], ['93', '94', '95'])).
% 8.46/8.70  thf('97', plain,
% 8.46/8.70      (![X0 : $i, X1 : $i]:
% 8.46/8.70         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 8.46/8.70           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 8.46/8.70      inference('demod', [status(thm)], ['47', '52', '53'])).
% 8.46/8.70  thf('98', plain,
% 8.46/8.70      (![X0 : $i, X1 : $i]:
% 8.46/8.70         ((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1) @ 
% 8.46/8.70           (k6_relat_1 @ X0))
% 8.46/8.70           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 8.46/8.70      inference('demod', [status(thm)], ['31', '32', '33'])).
% 8.46/8.70  thf('99', plain,
% 8.46/8.70      (![X0 : $i, X1 : $i]:
% 8.46/8.70         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 8.46/8.70           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 8.46/8.70      inference('demod', [status(thm)], ['47', '52', '53'])).
% 8.46/8.70  thf('100', plain,
% 8.46/8.70      (![X0 : $i, X1 : $i]:
% 8.46/8.70         ((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1) @ 
% 8.46/8.70           (k6_relat_1 @ X0)) = (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 8.46/8.70      inference('demod', [status(thm)], ['98', '99'])).
% 8.46/8.70  thf('101', plain,
% 8.46/8.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.46/8.70         (~ (v1_relat_1 @ X2)
% 8.46/8.70          | ~ (v1_relat_1 @ X1)
% 8.46/8.70          | ((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 8.46/8.70              = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2))))),
% 8.46/8.70      inference('simplify', [status(thm)], ['29'])).
% 8.46/8.70  thf('102', plain,
% 8.46/8.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.46/8.70         (((k5_relat_1 @ 
% 8.46/8.70            (k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X2) @ 
% 8.46/8.70            (k6_relat_1 @ X1))
% 8.46/8.70            = (k5_relat_1 @ (k6_relat_1 @ X2) @ 
% 8.46/8.70               (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))
% 8.46/8.70          | ~ (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 8.46/8.70          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 8.46/8.70      inference('sup+', [status(thm)], ['100', '101'])).
% 8.46/8.70  thf('103', plain,
% 8.46/8.70      (![X0 : $i, X1 : $i]:
% 8.46/8.70         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 8.46/8.70           = (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 8.46/8.70      inference('demod', [status(thm)], ['50', '51'])).
% 8.46/8.70  thf(t100_relat_1, axiom,
% 8.46/8.70    (![A:$i,B:$i,C:$i]:
% 8.46/8.70     ( ( v1_relat_1 @ C ) =>
% 8.46/8.70       ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 8.46/8.70         ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 8.46/8.70  thf('104', plain,
% 8.46/8.70      (![X14 : $i, X15 : $i, X16 : $i]:
% 8.46/8.70         (((k7_relat_1 @ (k7_relat_1 @ X14 @ X15) @ X16)
% 8.46/8.70            = (k7_relat_1 @ X14 @ (k3_xboole_0 @ X15 @ X16)))
% 8.46/8.70          | ~ (v1_relat_1 @ X14))),
% 8.46/8.70      inference('cnf', [status(esa)], [t100_relat_1])).
% 8.46/8.70  thf('105', plain,
% 8.46/8.70      (![X14 : $i, X15 : $i, X16 : $i]:
% 8.46/8.70         (((k7_relat_1 @ (k7_relat_1 @ X14 @ X15) @ X16)
% 8.46/8.70            = (k7_relat_1 @ X14 @ (k3_xboole_0 @ X15 @ X16)))
% 8.46/8.70          | ~ (v1_relat_1 @ X14))),
% 8.46/8.70      inference('cnf', [status(esa)], [t100_relat_1])).
% 8.46/8.70  thf('106', plain,
% 8.46/8.70      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 8.46/8.70         (((k7_relat_1 @ (k7_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X3)
% 8.46/8.70            = (k7_relat_1 @ (k7_relat_1 @ X2 @ X1) @ (k3_xboole_0 @ X0 @ X3)))
% 8.46/8.70          | ~ (v1_relat_1 @ X2)
% 8.46/8.70          | ~ (v1_relat_1 @ (k7_relat_1 @ X2 @ X1)))),
% 8.46/8.70      inference('sup+', [status(thm)], ['104', '105'])).
% 8.46/8.70  thf('107', plain,
% 8.46/8.70      (![X26 : $i, X27 : $i]:
% 8.46/8.70         (((k7_relat_1 @ X27 @ X26) = (k5_relat_1 @ (k6_relat_1 @ X26) @ X27))
% 8.46/8.70          | ~ (v1_relat_1 @ X27))),
% 8.46/8.70      inference('cnf', [status(esa)], [t94_relat_1])).
% 8.46/8.70  thf('108', plain,
% 8.46/8.70      (![X11 : $i, X12 : $i]:
% 8.46/8.70         (~ (v1_relat_1 @ X11)
% 8.46/8.70          | ~ (v1_relat_1 @ X12)
% 8.46/8.70          | (v1_relat_1 @ (k5_relat_1 @ X11 @ X12)))),
% 8.46/8.70      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 8.46/8.70  thf('109', plain,
% 8.46/8.70      (![X0 : $i, X1 : $i]:
% 8.46/8.70         ((v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 8.46/8.70          | ~ (v1_relat_1 @ X1)
% 8.46/8.70          | ~ (v1_relat_1 @ X1)
% 8.46/8.70          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 8.46/8.70      inference('sup+', [status(thm)], ['107', '108'])).
% 8.46/8.70  thf('110', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 8.46/8.70      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 8.46/8.70  thf('111', plain,
% 8.46/8.70      (![X0 : $i, X1 : $i]:
% 8.46/8.70         ((v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 8.46/8.70          | ~ (v1_relat_1 @ X1)
% 8.46/8.70          | ~ (v1_relat_1 @ X1))),
% 8.46/8.70      inference('demod', [status(thm)], ['109', '110'])).
% 8.46/8.70  thf('112', plain,
% 8.46/8.70      (![X0 : $i, X1 : $i]:
% 8.46/8.70         (~ (v1_relat_1 @ X1) | (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 8.46/8.70      inference('simplify', [status(thm)], ['111'])).
% 8.46/8.70  thf('113', plain,
% 8.46/8.70      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 8.46/8.70         (~ (v1_relat_1 @ X2)
% 8.46/8.70          | ((k7_relat_1 @ (k7_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X3)
% 8.46/8.70              = (k7_relat_1 @ (k7_relat_1 @ X2 @ X1) @ (k3_xboole_0 @ X0 @ X3))))),
% 8.46/8.70      inference('clc', [status(thm)], ['106', '112'])).
% 8.46/8.70  thf('114', plain,
% 8.46/8.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.46/8.70         (((k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X2)
% 8.46/8.70            = (k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X1) @ 
% 8.46/8.70               (k3_xboole_0 @ X0 @ X2)))
% 8.46/8.70          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 8.46/8.70      inference('sup+', [status(thm)], ['103', '113'])).
% 8.46/8.70  thf('115', plain,
% 8.46/8.70      (![X0 : $i]: ((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 8.46/8.70      inference('demod', [status(thm)], ['59', '60'])).
% 8.46/8.70  thf('116', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 8.46/8.70      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 8.46/8.70  thf('117', plain,
% 8.46/8.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.46/8.70         ((k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X2)
% 8.46/8.70           = (k7_relat_1 @ (k6_relat_1 @ X1) @ (k3_xboole_0 @ X0 @ X2)))),
% 8.46/8.70      inference('demod', [status(thm)], ['114', '115', '116'])).
% 8.46/8.70  thf('118', plain,
% 8.46/8.70      (![X0 : $i, X1 : $i]:
% 8.46/8.70         ((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1) @ 
% 8.46/8.70           (k6_relat_1 @ X0)) = (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 8.46/8.70      inference('demod', [status(thm)], ['98', '99'])).
% 8.46/8.70  thf('119', plain,
% 8.46/8.70      (![X0 : $i, X1 : $i]:
% 8.46/8.70         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 8.46/8.70           = (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 8.46/8.70      inference('demod', [status(thm)], ['50', '51'])).
% 8.46/8.70  thf('120', plain,
% 8.46/8.70      (![X0 : $i, X1 : $i]:
% 8.46/8.70         (~ (v1_relat_1 @ X1) | (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 8.46/8.70      inference('simplify', [status(thm)], ['111'])).
% 8.46/8.70  thf('121', plain,
% 8.46/8.70      (![X0 : $i, X1 : $i]:
% 8.46/8.70         ((v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 8.46/8.70          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 8.46/8.70      inference('sup+', [status(thm)], ['119', '120'])).
% 8.46/8.70  thf('122', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 8.46/8.70      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 8.46/8.70  thf('123', plain,
% 8.46/8.70      (![X0 : $i, X1 : $i]:
% 8.46/8.70         (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 8.46/8.70      inference('demod', [status(thm)], ['121', '122'])).
% 8.46/8.70  thf('124', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 8.46/8.70      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 8.46/8.70  thf('125', plain,
% 8.46/8.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.46/8.70         ((k7_relat_1 @ (k6_relat_1 @ X1) @ (k3_xboole_0 @ X0 @ X2))
% 8.46/8.70           = (k5_relat_1 @ (k6_relat_1 @ X2) @ 
% 8.46/8.70              (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 8.46/8.70      inference('demod', [status(thm)], ['102', '117', '118', '123', '124'])).
% 8.46/8.70  thf('126', plain,
% 8.46/8.70      (![X0 : $i, X1 : $i]:
% 8.46/8.70         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 8.46/8.70           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 8.46/8.70      inference('demod', [status(thm)], ['47', '52', '53'])).
% 8.46/8.70  thf('127', plain,
% 8.46/8.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.46/8.70         (r1_tarski @ 
% 8.46/8.70          (k7_relat_1 @ (k6_relat_1 @ X2) @ (k3_xboole_0 @ X0 @ X1)) @ 
% 8.46/8.70          (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 8.46/8.70      inference('demod', [status(thm)], ['96', '97', '125', '126'])).
% 8.46/8.70  thf('128', plain,
% 8.46/8.70      (![X0 : $i, X1 : $i]:
% 8.46/8.70         (r1_tarski @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 8.46/8.70          (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 8.46/8.70      inference('sup+', [status(thm)], ['61', '127'])).
% 8.46/8.70  thf('129', plain,
% 8.46/8.70      (![X0 : $i, X1 : $i]:
% 8.46/8.70         ((k6_relat_1 @ (k3_xboole_0 @ X0 @ X1))
% 8.46/8.70           = (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 8.46/8.70      inference('demod', [status(thm)], ['56', '128'])).
% 8.46/8.70  thf('130', plain,
% 8.46/8.70      (((k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B))
% 8.46/8.70         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 8.46/8.70      inference('demod', [status(thm)], ['4', '129'])).
% 8.46/8.70  thf('131', plain, ($false), inference('simplify', [status(thm)], ['130'])).
% 8.46/8.70  
% 8.46/8.70  % SZS output end Refutation
% 8.46/8.70  
% 8.56/8.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
