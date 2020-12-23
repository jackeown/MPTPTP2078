%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NYXAmWlb6Y

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:00 EST 2020

% Result     : Theorem 11.24s
% Output     : Refutation 11.24s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 624 expanded)
%              Number of leaves         :   21 ( 225 expanded)
%              Depth                    :   20
%              Number of atoms          : 1447 (5672 expanded)
%              Number of equality atoms :   83 ( 419 expanded)
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

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('0',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k7_relat_1 @ X31 @ X30 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X30 ) @ X31 ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
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
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
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
    ! [X20: $i,X21: $i] :
      ( ( ( k7_relat_1 @ X20 @ X21 )
        = ( k7_relat_1 @ X20 @ ( k3_xboole_0 @ ( k1_relat_1 @ X20 ) @ X21 ) ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t192_relat_1])).

thf('6',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k7_relat_1 @ X31 @ X30 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X30 ) @ X31 ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t76_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B )
        & ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ) )).

thf('7',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X27 @ ( k6_relat_1 @ X28 ) ) @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t76_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('8',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      | ( X0
        = ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k6_relat_1 @ X0 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ( ( k6_relat_1 @ X0 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('12',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k6_relat_1 @ X0 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ( ( k6_relat_1 @ X0 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k6_relat_1 @ ( k3_xboole_0 @ ( k1_relat_1 @ ( k6_relat_1 @ X1 ) ) @ X0 ) ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ( ( k6_relat_1 @ ( k3_xboole_0 @ ( k1_relat_1 @ ( k6_relat_1 @ X1 ) ) @ X0 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ ( k1_relat_1 @ ( k6_relat_1 @ X1 ) ) @ X0 ) ) @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['5','13'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('15',plain,(
    ! [X25: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X25 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('16',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('17',plain,(
    ! [X25: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X25 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('18',plain,(
    ! [X25: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X25 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ( ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['14','15','16','17','18'])).

thf('20',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k7_relat_1 @ X31 @ X30 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X30 ) @ X31 ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('21',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k7_relat_1 @ X20 @ X21 )
        = ( k7_relat_1 @ X20 @ ( k3_xboole_0 @ ( k1_relat_1 @ X20 ) @ X21 ) ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t192_relat_1])).

thf('22',plain,(
    ! [X26: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('23',plain,(
    ! [X29: $i] :
      ( ( ( k5_relat_1 @ X29 @ ( k6_relat_1 @ ( k2_relat_1 @ X29 ) ) )
        = X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k7_relat_1 @ X31 @ X30 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X30 ) @ X31 ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
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

thf('28',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X22 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X23 @ X22 ) @ X24 )
        = ( k5_relat_1 @ X23 @ ( k5_relat_1 @ X22 @ X24 ) ) )
      | ~ ( v1_relat_1 @ X24 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ ( k6_relat_1 @ X0 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['26','32'])).

thf('34',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('35',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ ( k6_relat_1 @ X0 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ ( k1_relat_1 @ ( k6_relat_1 @ X1 ) ) @ X0 ) ) @ ( k6_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['21','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ ( k6_relat_1 @ X0 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('39',plain,(
    ! [X25: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X25 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('40',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['37','38','39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['20','41'])).

thf('43',plain,(
    ! [X25: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X25 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('44',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k7_relat_1 @ X20 @ X21 )
        = ( k7_relat_1 @ X20 @ ( k3_xboole_0 @ ( k1_relat_1 @ X20 ) @ X21 ) ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t192_relat_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['42','47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ( ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) )
        = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['19','49','50'])).

thf('52',plain,(
    ! [X29: $i] :
      ( ( ( k5_relat_1 @ X29 @ ( k6_relat_1 @ ( k2_relat_1 @ X29 ) ) )
        = X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('53',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k7_relat_1 @ X31 @ X30 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X30 ) @ X31 ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) ) @ X0 )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X26: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('56',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('57',plain,(
    ! [X26: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('58',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['54','55','56','57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('63',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X22 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X23 @ X22 ) @ X24 )
        = ( k5_relat_1 @ X23 @ ( k5_relat_1 @ X22 @ X24 ) ) )
      | ~ ( v1_relat_1 @ X24 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('64',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ~ ( v1_relat_1 @ X15 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['62','66'])).

thf('68',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('69',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('70',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['67','68','69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['61','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['54','55','56','57','58'])).

thf('74',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['60','81'])).

thf('83',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('84',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('86',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X22 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X23 @ X22 ) @ X24 )
        = ( k5_relat_1 @ X23 @ ( k5_relat_1 @ X22 @ X24 ) ) )
      | ~ ( v1_relat_1 @ X24 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('87',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X27 @ ( k6_relat_1 @ X28 ) ) @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t76_relat_1])).

thf('88',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('90',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X2 ) ) ) @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['85','90'])).

thf('92',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('93',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('94',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X2 ) ) ) @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['91','92','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['42','47','48'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ ( k6_relat_1 @ X0 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['42','47','48'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ ( k6_relat_1 @ X0 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('100',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X2 ) @ ( k6_relat_1 @ X1 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf(t100_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('102',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X17 @ X18 ) @ X19 )
        = ( k7_relat_1 @ X17 @ ( k3_xboole_0 @ X18 @ X19 ) ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('103',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X17 @ X18 ) @ X19 )
        = ( k7_relat_1 @ X17 @ ( k3_xboole_0 @ X18 @ X19 ) ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('104',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X3 )
        = ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ ( k3_xboole_0 @ X0 @ X3 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k7_relat_1 @ X31 @ X30 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X30 ) @ X31 ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('106',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ~ ( v1_relat_1 @ X15 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X3 )
        = ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ ( k3_xboole_0 @ X0 @ X3 ) ) ) ) ),
    inference(clc,[status(thm)],['104','110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X2 )
        = ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X1 ) @ ( k3_xboole_0 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['101','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['54','55','56','57','58'])).

thf('114',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('115',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X2 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k3_xboole_0 @ X0 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['112','113','114'])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ ( k6_relat_1 @ X0 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['109'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('123',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k3_xboole_0 @ X0 @ X2 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['100','115','116','121','122'])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['42','47','48'])).

thf('125',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k7_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['94','95','123','124'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['59','125'])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['51','126'])).

thf('128',plain,(
    ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','127'])).

thf('129',plain,(
    $false ),
    inference(simplify,[status(thm)],['128'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NYXAmWlb6Y
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:18:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 11.24/11.42  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 11.24/11.42  % Solved by: fo/fo7.sh
% 11.24/11.42  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 11.24/11.42  % done 6465 iterations in 10.961s
% 11.24/11.42  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 11.24/11.42  % SZS output start Refutation
% 11.24/11.42  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 11.24/11.42  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 11.24/11.42  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 11.24/11.42  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 11.24/11.42  thf(sk_A_type, type, sk_A: $i).
% 11.24/11.42  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 11.24/11.42  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 11.24/11.42  thf(sk_B_type, type, sk_B: $i).
% 11.24/11.42  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 11.24/11.42  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 11.24/11.42  thf(t94_relat_1, axiom,
% 11.24/11.42    (![A:$i,B:$i]:
% 11.24/11.42     ( ( v1_relat_1 @ B ) =>
% 11.24/11.42       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 11.24/11.42  thf('0', plain,
% 11.24/11.42      (![X30 : $i, X31 : $i]:
% 11.24/11.42         (((k7_relat_1 @ X31 @ X30) = (k5_relat_1 @ (k6_relat_1 @ X30) @ X31))
% 11.24/11.42          | ~ (v1_relat_1 @ X31))),
% 11.24/11.42      inference('cnf', [status(esa)], [t94_relat_1])).
% 11.24/11.42  thf(t43_funct_1, conjecture,
% 11.24/11.42    (![A:$i,B:$i]:
% 11.24/11.42     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 11.24/11.42       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 11.24/11.42  thf(zf_stmt_0, negated_conjecture,
% 11.24/11.42    (~( ![A:$i,B:$i]:
% 11.24/11.42        ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 11.24/11.42          ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 11.24/11.42    inference('cnf.neg', [status(esa)], [t43_funct_1])).
% 11.24/11.42  thf('1', plain,
% 11.24/11.42      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A))
% 11.24/11.42         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 11.24/11.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.24/11.42  thf('2', plain,
% 11.24/11.42      ((((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 11.24/11.42          != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))
% 11.24/11.42        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A)))),
% 11.24/11.42      inference('sup-', [status(thm)], ['0', '1'])).
% 11.24/11.42  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 11.24/11.42  thf('3', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 11.24/11.42      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 11.24/11.42  thf('4', plain,
% 11.24/11.42      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 11.24/11.42         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 11.24/11.42      inference('demod', [status(thm)], ['2', '3'])).
% 11.24/11.42  thf(t192_relat_1, axiom,
% 11.24/11.42    (![A:$i,B:$i]:
% 11.24/11.42     ( ( v1_relat_1 @ B ) =>
% 11.24/11.42       ( ( k7_relat_1 @ B @ A ) =
% 11.24/11.42         ( k7_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ))).
% 11.24/11.42  thf('5', plain,
% 11.24/11.42      (![X20 : $i, X21 : $i]:
% 11.24/11.42         (((k7_relat_1 @ X20 @ X21)
% 11.24/11.42            = (k7_relat_1 @ X20 @ (k3_xboole_0 @ (k1_relat_1 @ X20) @ X21)))
% 11.24/11.42          | ~ (v1_relat_1 @ X20))),
% 11.24/11.42      inference('cnf', [status(esa)], [t192_relat_1])).
% 11.24/11.42  thf('6', plain,
% 11.24/11.42      (![X30 : $i, X31 : $i]:
% 11.24/11.42         (((k7_relat_1 @ X31 @ X30) = (k5_relat_1 @ (k6_relat_1 @ X30) @ X31))
% 11.24/11.42          | ~ (v1_relat_1 @ X31))),
% 11.24/11.42      inference('cnf', [status(esa)], [t94_relat_1])).
% 11.24/11.42  thf(t76_relat_1, axiom,
% 11.24/11.42    (![A:$i,B:$i]:
% 11.24/11.42     ( ( v1_relat_1 @ B ) =>
% 11.24/11.42       ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B ) & 
% 11.24/11.42         ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ))).
% 11.24/11.42  thf('7', plain,
% 11.24/11.42      (![X27 : $i, X28 : $i]:
% 11.24/11.42         ((r1_tarski @ (k5_relat_1 @ X27 @ (k6_relat_1 @ X28)) @ X27)
% 11.24/11.42          | ~ (v1_relat_1 @ X27))),
% 11.24/11.42      inference('cnf', [status(esa)], [t76_relat_1])).
% 11.24/11.42  thf(d10_xboole_0, axiom,
% 11.24/11.42    (![A:$i,B:$i]:
% 11.24/11.42     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 11.24/11.42  thf('8', plain,
% 11.24/11.42      (![X2 : $i, X4 : $i]:
% 11.24/11.42         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 11.24/11.42      inference('cnf', [status(esa)], [d10_xboole_0])).
% 11.24/11.42  thf('9', plain,
% 11.24/11.42      (![X0 : $i, X1 : $i]:
% 11.24/11.42         (~ (v1_relat_1 @ X0)
% 11.24/11.42          | ~ (r1_tarski @ X0 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 11.24/11.42          | ((X0) = (k5_relat_1 @ X0 @ (k6_relat_1 @ X1))))),
% 11.24/11.42      inference('sup-', [status(thm)], ['7', '8'])).
% 11.24/11.42  thf('10', plain,
% 11.24/11.42      (![X0 : $i, X1 : $i]:
% 11.24/11.42         (~ (r1_tarski @ (k6_relat_1 @ X0) @ 
% 11.24/11.42             (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 11.24/11.42          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 11.24/11.42          | ((k6_relat_1 @ X0)
% 11.24/11.42              = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1)))
% 11.24/11.42          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 11.24/11.42      inference('sup-', [status(thm)], ['6', '9'])).
% 11.24/11.42  thf('11', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 11.24/11.42      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 11.24/11.42  thf('12', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 11.24/11.42      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 11.24/11.42  thf('13', plain,
% 11.24/11.42      (![X0 : $i, X1 : $i]:
% 11.24/11.42         (~ (r1_tarski @ (k6_relat_1 @ X0) @ 
% 11.24/11.42             (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 11.24/11.42          | ((k6_relat_1 @ X0)
% 11.24/11.42              = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))))),
% 11.24/11.42      inference('demod', [status(thm)], ['10', '11', '12'])).
% 11.24/11.42  thf('14', plain,
% 11.24/11.42      (![X0 : $i, X1 : $i]:
% 11.24/11.42         (~ (r1_tarski @ 
% 11.24/11.42             (k6_relat_1 @ 
% 11.24/11.42              (k3_xboole_0 @ (k1_relat_1 @ (k6_relat_1 @ X1)) @ X0)) @ 
% 11.24/11.42             (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 11.24/11.42          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 11.24/11.42          | ((k6_relat_1 @ 
% 11.24/11.42              (k3_xboole_0 @ (k1_relat_1 @ (k6_relat_1 @ X1)) @ X0))
% 11.24/11.42              = (k5_relat_1 @ 
% 11.24/11.42                 (k6_relat_1 @ 
% 11.24/11.42                  (k3_xboole_0 @ (k1_relat_1 @ (k6_relat_1 @ X1)) @ X0)) @ 
% 11.24/11.42                 (k6_relat_1 @ X1))))),
% 11.24/11.42      inference('sup-', [status(thm)], ['5', '13'])).
% 11.24/11.42  thf(t71_relat_1, axiom,
% 11.24/11.42    (![A:$i]:
% 11.24/11.42     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 11.24/11.42       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 11.24/11.42  thf('15', plain, (![X25 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X25)) = (X25))),
% 11.24/11.42      inference('cnf', [status(esa)], [t71_relat_1])).
% 11.24/11.42  thf('16', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 11.24/11.42      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 11.24/11.42  thf('17', plain, (![X25 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X25)) = (X25))),
% 11.24/11.42      inference('cnf', [status(esa)], [t71_relat_1])).
% 11.24/11.42  thf('18', plain, (![X25 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X25)) = (X25))),
% 11.24/11.42      inference('cnf', [status(esa)], [t71_relat_1])).
% 11.24/11.42  thf('19', plain,
% 11.24/11.42      (![X0 : $i, X1 : $i]:
% 11.24/11.42         (~ (r1_tarski @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 11.24/11.42             (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 11.24/11.42          | ((k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))
% 11.24/11.42              = (k5_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 11.24/11.42                 (k6_relat_1 @ X1))))),
% 11.24/11.42      inference('demod', [status(thm)], ['14', '15', '16', '17', '18'])).
% 11.24/11.42  thf('20', plain,
% 11.24/11.42      (![X30 : $i, X31 : $i]:
% 11.24/11.42         (((k7_relat_1 @ X31 @ X30) = (k5_relat_1 @ (k6_relat_1 @ X30) @ X31))
% 11.24/11.42          | ~ (v1_relat_1 @ X31))),
% 11.24/11.42      inference('cnf', [status(esa)], [t94_relat_1])).
% 11.24/11.42  thf('21', plain,
% 11.24/11.42      (![X20 : $i, X21 : $i]:
% 11.24/11.42         (((k7_relat_1 @ X20 @ X21)
% 11.24/11.42            = (k7_relat_1 @ X20 @ (k3_xboole_0 @ (k1_relat_1 @ X20) @ X21)))
% 11.24/11.42          | ~ (v1_relat_1 @ X20))),
% 11.24/11.42      inference('cnf', [status(esa)], [t192_relat_1])).
% 11.24/11.42  thf('22', plain, (![X26 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X26)) = (X26))),
% 11.24/11.42      inference('cnf', [status(esa)], [t71_relat_1])).
% 11.24/11.42  thf(t80_relat_1, axiom,
% 11.24/11.42    (![A:$i]:
% 11.24/11.42     ( ( v1_relat_1 @ A ) =>
% 11.24/11.42       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 11.24/11.42  thf('23', plain,
% 11.24/11.42      (![X29 : $i]:
% 11.24/11.42         (((k5_relat_1 @ X29 @ (k6_relat_1 @ (k2_relat_1 @ X29))) = (X29))
% 11.24/11.42          | ~ (v1_relat_1 @ X29))),
% 11.24/11.42      inference('cnf', [status(esa)], [t80_relat_1])).
% 11.24/11.42  thf('24', plain,
% 11.24/11.42      (![X0 : $i]:
% 11.24/11.42         (((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 11.24/11.42            = (k6_relat_1 @ X0))
% 11.24/11.42          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 11.24/11.42      inference('sup+', [status(thm)], ['22', '23'])).
% 11.24/11.42  thf('25', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 11.24/11.42      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 11.24/11.42  thf('26', plain,
% 11.24/11.42      (![X0 : $i]:
% 11.24/11.42         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 11.24/11.42           = (k6_relat_1 @ X0))),
% 11.24/11.42      inference('demod', [status(thm)], ['24', '25'])).
% 11.24/11.42  thf('27', plain,
% 11.24/11.42      (![X30 : $i, X31 : $i]:
% 11.24/11.42         (((k7_relat_1 @ X31 @ X30) = (k5_relat_1 @ (k6_relat_1 @ X30) @ X31))
% 11.24/11.42          | ~ (v1_relat_1 @ X31))),
% 11.24/11.42      inference('cnf', [status(esa)], [t94_relat_1])).
% 11.24/11.42  thf(t55_relat_1, axiom,
% 11.24/11.42    (![A:$i]:
% 11.24/11.42     ( ( v1_relat_1 @ A ) =>
% 11.24/11.42       ( ![B:$i]:
% 11.24/11.42         ( ( v1_relat_1 @ B ) =>
% 11.24/11.42           ( ![C:$i]:
% 11.24/11.42             ( ( v1_relat_1 @ C ) =>
% 11.24/11.42               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 11.24/11.42                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 11.24/11.42  thf('28', plain,
% 11.24/11.42      (![X22 : $i, X23 : $i, X24 : $i]:
% 11.24/11.42         (~ (v1_relat_1 @ X22)
% 11.24/11.42          | ((k5_relat_1 @ (k5_relat_1 @ X23 @ X22) @ X24)
% 11.24/11.42              = (k5_relat_1 @ X23 @ (k5_relat_1 @ X22 @ X24)))
% 11.24/11.42          | ~ (v1_relat_1 @ X24)
% 11.24/11.42          | ~ (v1_relat_1 @ X23))),
% 11.24/11.42      inference('cnf', [status(esa)], [t55_relat_1])).
% 11.24/11.42  thf('29', plain,
% 11.24/11.42      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.24/11.42         (((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 11.24/11.42            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2)))
% 11.24/11.42          | ~ (v1_relat_1 @ X1)
% 11.24/11.42          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 11.24/11.42          | ~ (v1_relat_1 @ X2)
% 11.24/11.42          | ~ (v1_relat_1 @ X1))),
% 11.24/11.42      inference('sup+', [status(thm)], ['27', '28'])).
% 11.24/11.42  thf('30', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 11.24/11.42      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 11.24/11.42  thf('31', plain,
% 11.24/11.42      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.24/11.42         (((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 11.24/11.42            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2)))
% 11.24/11.42          | ~ (v1_relat_1 @ X1)
% 11.24/11.42          | ~ (v1_relat_1 @ X2)
% 11.24/11.42          | ~ (v1_relat_1 @ X1))),
% 11.24/11.42      inference('demod', [status(thm)], ['29', '30'])).
% 11.24/11.42  thf('32', plain,
% 11.24/11.42      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.24/11.42         (~ (v1_relat_1 @ X2)
% 11.24/11.42          | ~ (v1_relat_1 @ X1)
% 11.24/11.42          | ((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 11.24/11.42              = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2))))),
% 11.24/11.42      inference('simplify', [status(thm)], ['31'])).
% 11.24/11.42  thf('33', plain,
% 11.24/11.42      (![X0 : $i, X1 : $i]:
% 11.24/11.42         (((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1) @ 
% 11.24/11.42            (k6_relat_1 @ X0))
% 11.24/11.42            = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))
% 11.24/11.42          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 11.24/11.42          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 11.24/11.42      inference('sup+', [status(thm)], ['26', '32'])).
% 11.24/11.42  thf('34', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 11.24/11.42      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 11.24/11.42  thf('35', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 11.24/11.42      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 11.24/11.42  thf('36', plain,
% 11.24/11.42      (![X0 : $i, X1 : $i]:
% 11.24/11.42         ((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1) @ 
% 11.24/11.42           (k6_relat_1 @ X0))
% 11.24/11.42           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 11.24/11.42      inference('demod', [status(thm)], ['33', '34', '35'])).
% 11.24/11.42  thf('37', plain,
% 11.24/11.42      (![X0 : $i, X1 : $i]:
% 11.24/11.42         (((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 11.24/11.42            (k6_relat_1 @ X1))
% 11.24/11.42            = (k5_relat_1 @ 
% 11.24/11.42               (k6_relat_1 @ 
% 11.24/11.42                (k3_xboole_0 @ (k1_relat_1 @ (k6_relat_1 @ X1)) @ X0)) @ 
% 11.24/11.42               (k6_relat_1 @ X1)))
% 11.24/11.42          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 11.24/11.42      inference('sup+', [status(thm)], ['21', '36'])).
% 11.24/11.42  thf('38', plain,
% 11.24/11.42      (![X0 : $i, X1 : $i]:
% 11.24/11.42         ((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1) @ 
% 11.24/11.42           (k6_relat_1 @ X0))
% 11.24/11.42           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 11.24/11.42      inference('demod', [status(thm)], ['33', '34', '35'])).
% 11.24/11.42  thf('39', plain, (![X25 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X25)) = (X25))),
% 11.24/11.42      inference('cnf', [status(esa)], [t71_relat_1])).
% 11.24/11.42  thf('40', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 11.24/11.42      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 11.24/11.42  thf('41', plain,
% 11.24/11.42      (![X0 : $i, X1 : $i]:
% 11.24/11.42         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 11.24/11.42           = (k5_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 11.24/11.42              (k6_relat_1 @ X1)))),
% 11.24/11.42      inference('demod', [status(thm)], ['37', '38', '39', '40'])).
% 11.24/11.42  thf('42', plain,
% 11.24/11.42      (![X0 : $i, X1 : $i]:
% 11.24/11.42         (((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 11.24/11.42            = (k7_relat_1 @ (k6_relat_1 @ X1) @ (k3_xboole_0 @ X1 @ X0)))
% 11.24/11.42          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 11.24/11.42      inference('sup+', [status(thm)], ['20', '41'])).
% 11.24/11.42  thf('43', plain, (![X25 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X25)) = (X25))),
% 11.24/11.42      inference('cnf', [status(esa)], [t71_relat_1])).
% 11.24/11.42  thf('44', plain,
% 11.24/11.42      (![X20 : $i, X21 : $i]:
% 11.24/11.42         (((k7_relat_1 @ X20 @ X21)
% 11.24/11.42            = (k7_relat_1 @ X20 @ (k3_xboole_0 @ (k1_relat_1 @ X20) @ X21)))
% 11.24/11.42          | ~ (v1_relat_1 @ X20))),
% 11.24/11.42      inference('cnf', [status(esa)], [t192_relat_1])).
% 11.24/11.42  thf('45', plain,
% 11.24/11.42      (![X0 : $i, X1 : $i]:
% 11.24/11.42         (((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 11.24/11.42            = (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))
% 11.24/11.42          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 11.24/11.42      inference('sup+', [status(thm)], ['43', '44'])).
% 11.24/11.42  thf('46', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 11.24/11.42      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 11.24/11.42  thf('47', plain,
% 11.24/11.42      (![X0 : $i, X1 : $i]:
% 11.24/11.42         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 11.24/11.42           = (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 11.24/11.42      inference('demod', [status(thm)], ['45', '46'])).
% 11.24/11.42  thf('48', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 11.24/11.42      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 11.24/11.42  thf('49', plain,
% 11.24/11.42      (![X0 : $i, X1 : $i]:
% 11.24/11.42         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 11.24/11.42           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 11.24/11.42      inference('demod', [status(thm)], ['42', '47', '48'])).
% 11.24/11.42  thf('50', plain,
% 11.24/11.42      (![X0 : $i, X1 : $i]:
% 11.24/11.42         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 11.24/11.42           = (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 11.24/11.42      inference('demod', [status(thm)], ['45', '46'])).
% 11.24/11.42  thf('51', plain,
% 11.24/11.42      (![X0 : $i, X1 : $i]:
% 11.24/11.42         (~ (r1_tarski @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 11.24/11.42             (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 11.24/11.42          | ((k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))
% 11.24/11.42              = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 11.24/11.42      inference('demod', [status(thm)], ['19', '49', '50'])).
% 11.24/11.42  thf('52', plain,
% 11.24/11.42      (![X29 : $i]:
% 11.24/11.42         (((k5_relat_1 @ X29 @ (k6_relat_1 @ (k2_relat_1 @ X29))) = (X29))
% 11.24/11.42          | ~ (v1_relat_1 @ X29))),
% 11.24/11.42      inference('cnf', [status(esa)], [t80_relat_1])).
% 11.24/11.42  thf('53', plain,
% 11.24/11.42      (![X30 : $i, X31 : $i]:
% 11.24/11.42         (((k7_relat_1 @ X31 @ X30) = (k5_relat_1 @ (k6_relat_1 @ X30) @ X31))
% 11.24/11.42          | ~ (v1_relat_1 @ X31))),
% 11.24/11.42      inference('cnf', [status(esa)], [t94_relat_1])).
% 11.24/11.42  thf('54', plain,
% 11.24/11.42      (![X0 : $i]:
% 11.24/11.42         (((k7_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ (k6_relat_1 @ X0))) @ X0)
% 11.24/11.42            = (k6_relat_1 @ X0))
% 11.24/11.42          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 11.24/11.42          | ~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ (k6_relat_1 @ X0)))))),
% 11.24/11.42      inference('sup+', [status(thm)], ['52', '53'])).
% 11.24/11.42  thf('55', plain, (![X26 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X26)) = (X26))),
% 11.24/11.42      inference('cnf', [status(esa)], [t71_relat_1])).
% 11.24/11.42  thf('56', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 11.24/11.42      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 11.24/11.42  thf('57', plain, (![X26 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X26)) = (X26))),
% 11.24/11.42      inference('cnf', [status(esa)], [t71_relat_1])).
% 11.24/11.42  thf('58', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 11.24/11.42      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 11.24/11.42  thf('59', plain,
% 11.24/11.42      (![X0 : $i]: ((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 11.24/11.42      inference('demod', [status(thm)], ['54', '55', '56', '57', '58'])).
% 11.24/11.42  thf('60', plain,
% 11.24/11.42      (![X0 : $i]:
% 11.24/11.42         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 11.24/11.42           = (k6_relat_1 @ X0))),
% 11.24/11.42      inference('demod', [status(thm)], ['24', '25'])).
% 11.24/11.42  thf('61', plain,
% 11.24/11.42      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.24/11.42         (~ (v1_relat_1 @ X2)
% 11.24/11.42          | ~ (v1_relat_1 @ X1)
% 11.24/11.42          | ((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 11.24/11.42              = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2))))),
% 11.24/11.42      inference('simplify', [status(thm)], ['31'])).
% 11.24/11.42  thf('62', plain,
% 11.24/11.42      (![X0 : $i]:
% 11.24/11.42         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 11.24/11.42           = (k6_relat_1 @ X0))),
% 11.24/11.42      inference('demod', [status(thm)], ['24', '25'])).
% 11.24/11.42  thf('63', plain,
% 11.24/11.42      (![X22 : $i, X23 : $i, X24 : $i]:
% 11.24/11.42         (~ (v1_relat_1 @ X22)
% 11.24/11.42          | ((k5_relat_1 @ (k5_relat_1 @ X23 @ X22) @ X24)
% 11.24/11.42              = (k5_relat_1 @ X23 @ (k5_relat_1 @ X22 @ X24)))
% 11.24/11.42          | ~ (v1_relat_1 @ X24)
% 11.24/11.42          | ~ (v1_relat_1 @ X23))),
% 11.24/11.42      inference('cnf', [status(esa)], [t55_relat_1])).
% 11.24/11.42  thf(dt_k5_relat_1, axiom,
% 11.24/11.42    (![A:$i,B:$i]:
% 11.24/11.42     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 11.24/11.42       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 11.24/11.42  thf('64', plain,
% 11.24/11.42      (![X14 : $i, X15 : $i]:
% 11.24/11.42         (~ (v1_relat_1 @ X14)
% 11.24/11.42          | ~ (v1_relat_1 @ X15)
% 11.24/11.42          | (v1_relat_1 @ (k5_relat_1 @ X14 @ X15)))),
% 11.24/11.42      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 11.24/11.42  thf('65', plain,
% 11.24/11.42      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.24/11.42         ((v1_relat_1 @ (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0)))
% 11.24/11.42          | ~ (v1_relat_1 @ X2)
% 11.24/11.42          | ~ (v1_relat_1 @ X0)
% 11.24/11.42          | ~ (v1_relat_1 @ X1)
% 11.24/11.42          | ~ (v1_relat_1 @ X0)
% 11.24/11.42          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1)))),
% 11.24/11.42      inference('sup+', [status(thm)], ['63', '64'])).
% 11.24/11.42  thf('66', plain,
% 11.24/11.42      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.24/11.42         (~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1))
% 11.24/11.42          | ~ (v1_relat_1 @ X1)
% 11.24/11.42          | ~ (v1_relat_1 @ X0)
% 11.24/11.42          | ~ (v1_relat_1 @ X2)
% 11.24/11.42          | (v1_relat_1 @ (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0))))),
% 11.24/11.42      inference('simplify', [status(thm)], ['65'])).
% 11.24/11.42  thf('67', plain,
% 11.24/11.42      (![X0 : $i, X1 : $i]:
% 11.24/11.42         (~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 11.24/11.42          | (v1_relat_1 @ 
% 11.24/11.42             (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 11.24/11.42              (k5_relat_1 @ (k6_relat_1 @ X0) @ X1)))
% 11.24/11.42          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 11.24/11.42          | ~ (v1_relat_1 @ X1)
% 11.24/11.42          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 11.24/11.42      inference('sup-', [status(thm)], ['62', '66'])).
% 11.24/11.42  thf('68', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 11.24/11.42      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 11.24/11.42  thf('69', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 11.24/11.42      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 11.24/11.42  thf('70', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 11.24/11.42      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 11.24/11.42  thf('71', plain,
% 11.24/11.42      (![X0 : $i, X1 : $i]:
% 11.24/11.42         ((v1_relat_1 @ 
% 11.24/11.42           (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 11.24/11.42            (k5_relat_1 @ (k6_relat_1 @ X0) @ X1)))
% 11.24/11.42          | ~ (v1_relat_1 @ X1))),
% 11.24/11.42      inference('demod', [status(thm)], ['67', '68', '69', '70'])).
% 11.24/11.42  thf('72', plain,
% 11.24/11.42      (![X0 : $i, X1 : $i]:
% 11.24/11.42         ((v1_relat_1 @ 
% 11.24/11.42           (k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X1) @ X0))
% 11.24/11.42          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 11.24/11.42          | ~ (v1_relat_1 @ X0)
% 11.24/11.42          | ~ (v1_relat_1 @ X0))),
% 11.24/11.42      inference('sup+', [status(thm)], ['61', '71'])).
% 11.24/11.42  thf('73', plain,
% 11.24/11.42      (![X0 : $i]: ((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 11.24/11.42      inference('demod', [status(thm)], ['54', '55', '56', '57', '58'])).
% 11.24/11.42  thf('74', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 11.24/11.42      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 11.24/11.42  thf('75', plain,
% 11.24/11.42      (![X0 : $i, X1 : $i]:
% 11.24/11.42         ((v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 11.24/11.42          | ~ (v1_relat_1 @ X0)
% 11.24/11.42          | ~ (v1_relat_1 @ X0))),
% 11.24/11.42      inference('demod', [status(thm)], ['72', '73', '74'])).
% 11.24/11.42  thf('76', plain,
% 11.24/11.42      (![X0 : $i, X1 : $i]:
% 11.24/11.42         (~ (v1_relat_1 @ X0)
% 11.24/11.42          | (v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 11.24/11.42      inference('simplify', [status(thm)], ['75'])).
% 11.24/11.42  thf('77', plain,
% 11.24/11.42      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.24/11.42         (~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1))
% 11.24/11.42          | ~ (v1_relat_1 @ X1)
% 11.24/11.42          | ~ (v1_relat_1 @ X0)
% 11.24/11.42          | ~ (v1_relat_1 @ X2)
% 11.24/11.42          | (v1_relat_1 @ (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0))))),
% 11.24/11.42      inference('simplify', [status(thm)], ['65'])).
% 11.24/11.42  thf('78', plain,
% 11.24/11.42      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.24/11.42         (~ (v1_relat_1 @ X0)
% 11.24/11.42          | (v1_relat_1 @ 
% 11.24/11.42             (k5_relat_1 @ (k6_relat_1 @ X1) @ (k5_relat_1 @ X0 @ X2)))
% 11.24/11.42          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 11.24/11.42          | ~ (v1_relat_1 @ X2)
% 11.24/11.42          | ~ (v1_relat_1 @ X0))),
% 11.24/11.42      inference('sup-', [status(thm)], ['76', '77'])).
% 11.24/11.42  thf('79', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 11.24/11.42      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 11.24/11.42  thf('80', plain,
% 11.24/11.42      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.24/11.42         (~ (v1_relat_1 @ X0)
% 11.24/11.42          | (v1_relat_1 @ 
% 11.24/11.42             (k5_relat_1 @ (k6_relat_1 @ X1) @ (k5_relat_1 @ X0 @ X2)))
% 11.24/11.42          | ~ (v1_relat_1 @ X2)
% 11.24/11.42          | ~ (v1_relat_1 @ X0))),
% 11.24/11.42      inference('demod', [status(thm)], ['78', '79'])).
% 11.24/11.42  thf('81', plain,
% 11.24/11.42      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.24/11.42         (~ (v1_relat_1 @ X2)
% 11.24/11.42          | (v1_relat_1 @ 
% 11.24/11.42             (k5_relat_1 @ (k6_relat_1 @ X1) @ (k5_relat_1 @ X0 @ X2)))
% 11.24/11.42          | ~ (v1_relat_1 @ X0))),
% 11.24/11.42      inference('simplify', [status(thm)], ['80'])).
% 11.24/11.42  thf('82', plain,
% 11.24/11.42      (![X0 : $i, X1 : $i]:
% 11.24/11.42         ((v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))
% 11.24/11.42          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 11.24/11.42          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 11.24/11.42      inference('sup+', [status(thm)], ['60', '81'])).
% 11.24/11.42  thf('83', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 11.24/11.42      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 11.24/11.42  thf('84', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 11.24/11.42      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 11.24/11.42  thf('85', plain,
% 11.24/11.42      (![X0 : $i, X1 : $i]:
% 11.24/11.42         (v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 11.24/11.42      inference('demod', [status(thm)], ['82', '83', '84'])).
% 11.24/11.42  thf('86', plain,
% 11.24/11.42      (![X22 : $i, X23 : $i, X24 : $i]:
% 11.24/11.42         (~ (v1_relat_1 @ X22)
% 11.24/11.42          | ((k5_relat_1 @ (k5_relat_1 @ X23 @ X22) @ X24)
% 11.24/11.42              = (k5_relat_1 @ X23 @ (k5_relat_1 @ X22 @ X24)))
% 11.24/11.42          | ~ (v1_relat_1 @ X24)
% 11.24/11.42          | ~ (v1_relat_1 @ X23))),
% 11.24/11.42      inference('cnf', [status(esa)], [t55_relat_1])).
% 11.24/11.42  thf('87', plain,
% 11.24/11.42      (![X27 : $i, X28 : $i]:
% 11.24/11.42         ((r1_tarski @ (k5_relat_1 @ X27 @ (k6_relat_1 @ X28)) @ X27)
% 11.24/11.42          | ~ (v1_relat_1 @ X27))),
% 11.24/11.42      inference('cnf', [status(esa)], [t76_relat_1])).
% 11.24/11.42  thf('88', plain,
% 11.24/11.42      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.24/11.42         ((r1_tarski @ 
% 11.24/11.42           (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ 
% 11.24/11.42           (k5_relat_1 @ X2 @ X1))
% 11.24/11.42          | ~ (v1_relat_1 @ X2)
% 11.24/11.42          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 11.24/11.42          | ~ (v1_relat_1 @ X1)
% 11.24/11.42          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1)))),
% 11.24/11.42      inference('sup+', [status(thm)], ['86', '87'])).
% 11.24/11.42  thf('89', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 11.24/11.42      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 11.24/11.42  thf('90', plain,
% 11.24/11.42      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.24/11.42         ((r1_tarski @ 
% 11.24/11.42           (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ 
% 11.24/11.42           (k5_relat_1 @ X2 @ X1))
% 11.24/11.42          | ~ (v1_relat_1 @ X2)
% 11.24/11.42          | ~ (v1_relat_1 @ X1)
% 11.24/11.42          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1)))),
% 11.24/11.42      inference('demod', [status(thm)], ['88', '89'])).
% 11.24/11.42  thf('91', plain,
% 11.24/11.42      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.24/11.42         (~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 11.24/11.42          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 11.24/11.42          | (r1_tarski @ 
% 11.24/11.42             (k5_relat_1 @ (k6_relat_1 @ X1) @ 
% 11.24/11.42              (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X2))) @ 
% 11.24/11.42             (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))))),
% 11.24/11.42      inference('sup-', [status(thm)], ['85', '90'])).
% 11.24/11.42  thf('92', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 11.24/11.42      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 11.24/11.42  thf('93', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 11.24/11.42      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 11.24/11.42  thf('94', plain,
% 11.24/11.42      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.24/11.42         (r1_tarski @ 
% 11.24/11.42          (k5_relat_1 @ (k6_relat_1 @ X1) @ 
% 11.24/11.42           (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X2))) @ 
% 11.24/11.42          (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 11.24/11.42      inference('demod', [status(thm)], ['91', '92', '93'])).
% 11.24/11.42  thf('95', plain,
% 11.24/11.42      (![X0 : $i, X1 : $i]:
% 11.24/11.42         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 11.24/11.42           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 11.24/11.42      inference('demod', [status(thm)], ['42', '47', '48'])).
% 11.24/11.42  thf('96', plain,
% 11.24/11.42      (![X0 : $i, X1 : $i]:
% 11.24/11.42         ((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1) @ 
% 11.24/11.42           (k6_relat_1 @ X0))
% 11.24/11.42           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 11.24/11.42      inference('demod', [status(thm)], ['33', '34', '35'])).
% 11.24/11.42  thf('97', plain,
% 11.24/11.42      (![X0 : $i, X1 : $i]:
% 11.24/11.42         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 11.24/11.42           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 11.24/11.42      inference('demod', [status(thm)], ['42', '47', '48'])).
% 11.24/11.42  thf('98', plain,
% 11.24/11.42      (![X0 : $i, X1 : $i]:
% 11.24/11.42         ((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1) @ 
% 11.24/11.42           (k6_relat_1 @ X0)) = (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 11.24/11.42      inference('demod', [status(thm)], ['96', '97'])).
% 11.24/11.42  thf('99', plain,
% 11.24/11.42      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.24/11.42         (~ (v1_relat_1 @ X2)
% 11.24/11.42          | ~ (v1_relat_1 @ X1)
% 11.24/11.42          | ((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 11.24/11.42              = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2))))),
% 11.24/11.42      inference('simplify', [status(thm)], ['31'])).
% 11.24/11.42  thf('100', plain,
% 11.24/11.42      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.24/11.42         (((k5_relat_1 @ 
% 11.24/11.42            (k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X2) @ 
% 11.24/11.42            (k6_relat_1 @ X1))
% 11.24/11.42            = (k5_relat_1 @ (k6_relat_1 @ X2) @ 
% 11.24/11.42               (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))
% 11.24/11.42          | ~ (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 11.24/11.42          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 11.24/11.42      inference('sup+', [status(thm)], ['98', '99'])).
% 11.24/11.42  thf('101', plain,
% 11.24/11.42      (![X0 : $i, X1 : $i]:
% 11.24/11.42         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 11.24/11.42           = (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 11.24/11.42      inference('demod', [status(thm)], ['45', '46'])).
% 11.24/11.42  thf(t100_relat_1, axiom,
% 11.24/11.42    (![A:$i,B:$i,C:$i]:
% 11.24/11.42     ( ( v1_relat_1 @ C ) =>
% 11.24/11.42       ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 11.24/11.42         ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 11.24/11.42  thf('102', plain,
% 11.24/11.42      (![X17 : $i, X18 : $i, X19 : $i]:
% 11.24/11.42         (((k7_relat_1 @ (k7_relat_1 @ X17 @ X18) @ X19)
% 11.24/11.42            = (k7_relat_1 @ X17 @ (k3_xboole_0 @ X18 @ X19)))
% 11.24/11.42          | ~ (v1_relat_1 @ X17))),
% 11.24/11.42      inference('cnf', [status(esa)], [t100_relat_1])).
% 11.24/11.42  thf('103', plain,
% 11.24/11.42      (![X17 : $i, X18 : $i, X19 : $i]:
% 11.24/11.42         (((k7_relat_1 @ (k7_relat_1 @ X17 @ X18) @ X19)
% 11.24/11.42            = (k7_relat_1 @ X17 @ (k3_xboole_0 @ X18 @ X19)))
% 11.24/11.42          | ~ (v1_relat_1 @ X17))),
% 11.24/11.42      inference('cnf', [status(esa)], [t100_relat_1])).
% 11.24/11.42  thf('104', plain,
% 11.24/11.42      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 11.24/11.42         (((k7_relat_1 @ (k7_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X3)
% 11.24/11.42            = (k7_relat_1 @ (k7_relat_1 @ X2 @ X1) @ (k3_xboole_0 @ X0 @ X3)))
% 11.24/11.42          | ~ (v1_relat_1 @ X2)
% 11.24/11.42          | ~ (v1_relat_1 @ (k7_relat_1 @ X2 @ X1)))),
% 11.24/11.42      inference('sup+', [status(thm)], ['102', '103'])).
% 11.24/11.42  thf('105', plain,
% 11.24/11.42      (![X30 : $i, X31 : $i]:
% 11.24/11.42         (((k7_relat_1 @ X31 @ X30) = (k5_relat_1 @ (k6_relat_1 @ X30) @ X31))
% 11.24/11.42          | ~ (v1_relat_1 @ X31))),
% 11.24/11.42      inference('cnf', [status(esa)], [t94_relat_1])).
% 11.24/11.42  thf('106', plain,
% 11.24/11.42      (![X14 : $i, X15 : $i]:
% 11.24/11.42         (~ (v1_relat_1 @ X14)
% 11.24/11.42          | ~ (v1_relat_1 @ X15)
% 11.24/11.42          | (v1_relat_1 @ (k5_relat_1 @ X14 @ X15)))),
% 11.24/11.42      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 11.24/11.42  thf('107', plain,
% 11.24/11.42      (![X0 : $i, X1 : $i]:
% 11.24/11.42         ((v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 11.24/11.42          | ~ (v1_relat_1 @ X1)
% 11.24/11.42          | ~ (v1_relat_1 @ X1)
% 11.24/11.42          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 11.24/11.42      inference('sup+', [status(thm)], ['105', '106'])).
% 11.24/11.42  thf('108', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 11.24/11.42      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 11.24/11.42  thf('109', plain,
% 11.24/11.42      (![X0 : $i, X1 : $i]:
% 11.24/11.42         ((v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 11.24/11.42          | ~ (v1_relat_1 @ X1)
% 11.24/11.42          | ~ (v1_relat_1 @ X1))),
% 11.24/11.42      inference('demod', [status(thm)], ['107', '108'])).
% 11.24/11.42  thf('110', plain,
% 11.24/11.42      (![X0 : $i, X1 : $i]:
% 11.24/11.42         (~ (v1_relat_1 @ X1) | (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 11.24/11.42      inference('simplify', [status(thm)], ['109'])).
% 11.24/11.42  thf('111', plain,
% 11.24/11.42      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 11.24/11.42         (~ (v1_relat_1 @ X2)
% 11.24/11.42          | ((k7_relat_1 @ (k7_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X3)
% 11.24/11.42              = (k7_relat_1 @ (k7_relat_1 @ X2 @ X1) @ (k3_xboole_0 @ X0 @ X3))))),
% 11.24/11.42      inference('clc', [status(thm)], ['104', '110'])).
% 11.24/11.42  thf('112', plain,
% 11.24/11.42      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.24/11.42         (((k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X2)
% 11.24/11.42            = (k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X1) @ 
% 11.24/11.42               (k3_xboole_0 @ X0 @ X2)))
% 11.24/11.42          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 11.24/11.42      inference('sup+', [status(thm)], ['101', '111'])).
% 11.24/11.42  thf('113', plain,
% 11.24/11.42      (![X0 : $i]: ((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 11.24/11.42      inference('demod', [status(thm)], ['54', '55', '56', '57', '58'])).
% 11.24/11.42  thf('114', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 11.24/11.42      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 11.24/11.42  thf('115', plain,
% 11.24/11.42      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.24/11.42         ((k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X2)
% 11.24/11.42           = (k7_relat_1 @ (k6_relat_1 @ X1) @ (k3_xboole_0 @ X0 @ X2)))),
% 11.24/11.42      inference('demod', [status(thm)], ['112', '113', '114'])).
% 11.24/11.42  thf('116', plain,
% 11.24/11.42      (![X0 : $i, X1 : $i]:
% 11.24/11.42         ((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1) @ 
% 11.24/11.42           (k6_relat_1 @ X0)) = (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 11.24/11.42      inference('demod', [status(thm)], ['96', '97'])).
% 11.24/11.42  thf('117', plain,
% 11.24/11.42      (![X0 : $i, X1 : $i]:
% 11.24/11.42         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 11.24/11.42           = (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 11.24/11.42      inference('demod', [status(thm)], ['45', '46'])).
% 11.24/11.42  thf('118', plain,
% 11.24/11.42      (![X0 : $i, X1 : $i]:
% 11.24/11.42         (~ (v1_relat_1 @ X1) | (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 11.24/11.42      inference('simplify', [status(thm)], ['109'])).
% 11.24/11.42  thf('119', plain,
% 11.24/11.42      (![X0 : $i, X1 : $i]:
% 11.24/11.42         ((v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 11.24/11.42          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 11.24/11.42      inference('sup+', [status(thm)], ['117', '118'])).
% 11.24/11.42  thf('120', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 11.24/11.42      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 11.24/11.42  thf('121', plain,
% 11.24/11.42      (![X0 : $i, X1 : $i]:
% 11.24/11.42         (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 11.24/11.42      inference('demod', [status(thm)], ['119', '120'])).
% 11.24/11.42  thf('122', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 11.24/11.42      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 11.24/11.42  thf('123', plain,
% 11.24/11.42      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.24/11.42         ((k7_relat_1 @ (k6_relat_1 @ X1) @ (k3_xboole_0 @ X0 @ X2))
% 11.24/11.42           = (k5_relat_1 @ (k6_relat_1 @ X2) @ 
% 11.24/11.42              (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 11.24/11.42      inference('demod', [status(thm)], ['100', '115', '116', '121', '122'])).
% 11.24/11.42  thf('124', plain,
% 11.24/11.42      (![X0 : $i, X1 : $i]:
% 11.24/11.42         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 11.24/11.42           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 11.24/11.42      inference('demod', [status(thm)], ['42', '47', '48'])).
% 11.24/11.42  thf('125', plain,
% 11.24/11.42      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.24/11.42         (r1_tarski @ 
% 11.24/11.42          (k7_relat_1 @ (k6_relat_1 @ X2) @ (k3_xboole_0 @ X0 @ X1)) @ 
% 11.24/11.42          (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 11.24/11.42      inference('demod', [status(thm)], ['94', '95', '123', '124'])).
% 11.24/11.42  thf('126', plain,
% 11.24/11.42      (![X0 : $i, X1 : $i]:
% 11.24/11.42         (r1_tarski @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 11.24/11.42          (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 11.24/11.42      inference('sup+', [status(thm)], ['59', '125'])).
% 11.24/11.42  thf('127', plain,
% 11.24/11.42      (![X0 : $i, X1 : $i]:
% 11.24/11.42         ((k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))
% 11.24/11.42           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 11.24/11.42      inference('demod', [status(thm)], ['51', '126'])).
% 11.24/11.42  thf('128', plain,
% 11.24/11.42      (((k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B))
% 11.24/11.42         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 11.24/11.42      inference('demod', [status(thm)], ['4', '127'])).
% 11.24/11.42  thf('129', plain, ($false), inference('simplify', [status(thm)], ['128'])).
% 11.24/11.42  
% 11.24/11.42  % SZS output end Refutation
% 11.24/11.42  
% 11.26/11.43  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
