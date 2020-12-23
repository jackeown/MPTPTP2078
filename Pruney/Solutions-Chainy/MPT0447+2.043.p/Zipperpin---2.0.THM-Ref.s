%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qRjuHnPpFG

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:58 EST 2020

% Result     : Theorem 15.90s
% Output     : Refutation 15.90s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 203 expanded)
%              Number of leaves         :   24 (  70 expanded)
%              Depth                    :   16
%              Number of atoms          :  627 (1504 expanded)
%              Number of equality atoms :   20 (  67 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t31_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( ( r1_tarski @ A @ B )
             => ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t31_relat_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X55: $i] :
      ( ( ( k3_relat_1 @ X55 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X55 ) @ ( k2_relat_1 @ X55 ) ) )
      | ~ ( v1_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ( X5 != X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('3',plain,(
    ! [X6: $i] :
      ( r1_tarski @ X6 @ X6 ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X6: $i] :
      ( r1_tarski @ X6 @ X6 ) ),
    inference(simplify,[status(thm)],['2'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('5',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X11 @ X12 )
      | ~ ( r1_tarski @ X11 @ X13 )
      | ( r1_tarski @ X11 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('8',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k4_xboole_0 @ X25 @ ( k4_xboole_0 @ X25 @ X26 ) )
      = ( k3_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('9',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X18 @ X19 ) @ X18 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X5: $i,X7: $i] :
      ( ( X5 = X7 )
      | ~ ( r1_tarski @ X7 @ X5 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('14',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k4_xboole_0 @ X25 @ ( k4_xboole_0 @ X25 @ X26 ) )
      = ( k3_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t38_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) )
     => ( A = k1_xboole_0 ) ) )).

thf('15',plain,(
    ! [X20: $i,X21: $i] :
      ( ( X20 = k1_xboole_0 )
      | ~ ( r1_tarski @ X20 @ ( k4_xboole_0 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k4_xboole_0 @ X0 @ X0 ) @ X0 )
      | ( ( k4_xboole_0 @ X0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X18 @ X19 ) @ X18 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['17','18'])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('20',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( r1_tarski @ X22 @ ( k2_xboole_0 @ X23 @ X24 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X22 @ X23 ) @ X24 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('22',plain,(
    ! [X17: $i] :
      ( r1_tarski @ k1_xboole_0 @ X17 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X55: $i] :
      ( ( ( k3_relat_1 @ X55 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X55 ) @ ( k2_relat_1 @ X55 ) ) )
      | ~ ( v1_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('25',plain,(
    ! [X6: $i] :
      ( r1_tarski @ X6 @ X6 ) ),
    inference(simplify,[status(thm)],['2'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('26',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ( r1_tarski @ X8 @ ( k2_xboole_0 @ X10 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','27'])).

thf('29',plain,(
    r1_tarski @ sk_A @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('30',plain,(
    ! [X58: $i,X59: $i] :
      ( ~ ( v1_relat_1 @ X58 )
      | ( r1_tarski @ ( k2_relat_1 @ X59 ) @ ( k2_relat_1 @ X58 ) )
      | ~ ( r1_tarski @ X59 @ X58 )
      | ~ ( v1_relat_1 @ X59 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('31',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B_2 ) )
    | ~ ( v1_relat_1 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_relat_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('35',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ X14 @ X15 )
      | ~ ( r1_tarski @ X15 @ X16 )
      | ( r1_tarski @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_B_2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ~ ( v1_relat_1 @ sk_B_2 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['28','36'])).

thf('38',plain,(
    v1_relat_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ X14 @ X15 )
      | ~ ( r1_tarski @ X15 @ X16 )
      | ( r1_tarski @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ X0 )
      | ~ ( r1_tarski @ ( k3_relat_1 @ sk_B_2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k2_xboole_0 @ ( k3_relat_1 @ sk_B_2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('44',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( r1_tarski @ X28 @ X29 )
      | ~ ( r1_tarski @ X30 @ X29 )
      | ( r1_tarski @ ( k2_xboole_0 @ X28 @ X30 ) @ X29 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ X0 @ X2 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_tarski @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ X0 @ ( k2_relat_1 @ sk_A ) ) @ ( k2_xboole_0 @ ( k3_relat_1 @ sk_B_2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf('47',plain,
    ( ( r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k2_xboole_0 @ ( k3_relat_1 @ sk_B_2 ) @ ( k1_relat_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['1','46'])).

thf('48',plain,(
    ! [X55: $i] :
      ( ( ( k3_relat_1 @ X55 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X55 ) @ ( k2_relat_1 @ X55 ) ) )
      | ~ ( v1_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    r1_tarski @ sk_A @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X58: $i,X59: $i] :
      ( ~ ( v1_relat_1 @ X58 )
      | ( r1_tarski @ ( k1_relat_1 @ X59 ) @ ( k1_relat_1 @ X58 ) )
      | ~ ( r1_tarski @ X59 @ X58 )
      | ~ ( v1_relat_1 @ X59 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('53',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B_2 ) )
    | ~ ( v1_relat_1 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v1_relat_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ X14 @ X15 )
      | ~ ( r1_tarski @ X15 @ X16 )
      | ( r1_tarski @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_B_2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ~ ( v1_relat_1 @ sk_B_2 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['50','58'])).

thf('60',plain,(
    v1_relat_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X6: $i] :
      ( r1_tarski @ X6 @ X6 ) ),
    inference(simplify,[status(thm)],['2'])).

thf('63',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( r1_tarski @ X28 @ X29 )
      | ~ ( r1_tarski @ X30 @ X29 )
      | ( r1_tarski @ ( k2_xboole_0 @ X28 @ X30 ) @ X29 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k3_relat_1 @ sk_B_2 ) @ ( k1_relat_1 @ sk_A ) ) @ ( k3_relat_1 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['61','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('67',plain,(
    ! [X5: $i,X7: $i] :
      ( ( X5 = X7 )
      | ~ ( r1_tarski @ X7 @ X5 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( k2_xboole_0 @ ( k3_relat_1 @ sk_B_2 ) @ ( k1_relat_1 @ sk_A ) )
    = ( k3_relat_1 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['65','68'])).

thf('70',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['47','69','70'])).

thf('72',plain,(
    $false ),
    inference(demod,[status(thm)],['0','71'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qRjuHnPpFG
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:18:29 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 15.90/16.10  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 15.90/16.10  % Solved by: fo/fo7.sh
% 15.90/16.10  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 15.90/16.10  % done 24427 iterations in 15.641s
% 15.90/16.10  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 15.90/16.10  % SZS output start Refutation
% 15.90/16.10  thf(sk_A_type, type, sk_A: $i).
% 15.90/16.10  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 15.90/16.10  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 15.90/16.10  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 15.90/16.10  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 15.90/16.10  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 15.90/16.10  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 15.90/16.10  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 15.90/16.10  thf(sk_B_2_type, type, sk_B_2: $i).
% 15.90/16.10  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 15.90/16.10  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 15.90/16.10  thf(t31_relat_1, conjecture,
% 15.90/16.10    (![A:$i]:
% 15.90/16.10     ( ( v1_relat_1 @ A ) =>
% 15.90/16.10       ( ![B:$i]:
% 15.90/16.10         ( ( v1_relat_1 @ B ) =>
% 15.90/16.10           ( ( r1_tarski @ A @ B ) =>
% 15.90/16.10             ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ))).
% 15.90/16.10  thf(zf_stmt_0, negated_conjecture,
% 15.90/16.10    (~( ![A:$i]:
% 15.90/16.10        ( ( v1_relat_1 @ A ) =>
% 15.90/16.10          ( ![B:$i]:
% 15.90/16.10            ( ( v1_relat_1 @ B ) =>
% 15.90/16.10              ( ( r1_tarski @ A @ B ) =>
% 15.90/16.10                ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ) )),
% 15.90/16.10    inference('cnf.neg', [status(esa)], [t31_relat_1])).
% 15.90/16.10  thf('0', plain,
% 15.90/16.10      (~ (r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_2))),
% 15.90/16.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.90/16.10  thf(d6_relat_1, axiom,
% 15.90/16.10    (![A:$i]:
% 15.90/16.10     ( ( v1_relat_1 @ A ) =>
% 15.90/16.10       ( ( k3_relat_1 @ A ) =
% 15.90/16.10         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 15.90/16.10  thf('1', plain,
% 15.90/16.10      (![X55 : $i]:
% 15.90/16.10         (((k3_relat_1 @ X55)
% 15.90/16.10            = (k2_xboole_0 @ (k1_relat_1 @ X55) @ (k2_relat_1 @ X55)))
% 15.90/16.10          | ~ (v1_relat_1 @ X55))),
% 15.90/16.10      inference('cnf', [status(esa)], [d6_relat_1])).
% 15.90/16.10  thf(d10_xboole_0, axiom,
% 15.90/16.10    (![A:$i,B:$i]:
% 15.90/16.10     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 15.90/16.10  thf('2', plain,
% 15.90/16.10      (![X5 : $i, X6 : $i]: ((r1_tarski @ X5 @ X6) | ((X5) != (X6)))),
% 15.90/16.10      inference('cnf', [status(esa)], [d10_xboole_0])).
% 15.90/16.10  thf('3', plain, (![X6 : $i]: (r1_tarski @ X6 @ X6)),
% 15.90/16.10      inference('simplify', [status(thm)], ['2'])).
% 15.90/16.10  thf('4', plain, (![X6 : $i]: (r1_tarski @ X6 @ X6)),
% 15.90/16.10      inference('simplify', [status(thm)], ['2'])).
% 15.90/16.10  thf(t19_xboole_1, axiom,
% 15.90/16.10    (![A:$i,B:$i,C:$i]:
% 15.90/16.10     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 15.90/16.10       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 15.90/16.10  thf('5', plain,
% 15.90/16.10      (![X11 : $i, X12 : $i, X13 : $i]:
% 15.90/16.10         (~ (r1_tarski @ X11 @ X12)
% 15.90/16.10          | ~ (r1_tarski @ X11 @ X13)
% 15.90/16.10          | (r1_tarski @ X11 @ (k3_xboole_0 @ X12 @ X13)))),
% 15.90/16.10      inference('cnf', [status(esa)], [t19_xboole_1])).
% 15.90/16.10  thf('6', plain,
% 15.90/16.10      (![X0 : $i, X1 : $i]:
% 15.90/16.10         ((r1_tarski @ X0 @ (k3_xboole_0 @ X0 @ X1)) | ~ (r1_tarski @ X0 @ X1))),
% 15.90/16.10      inference('sup-', [status(thm)], ['4', '5'])).
% 15.90/16.10  thf('7', plain, (![X0 : $i]: (r1_tarski @ X0 @ (k3_xboole_0 @ X0 @ X0))),
% 15.90/16.10      inference('sup-', [status(thm)], ['3', '6'])).
% 15.90/16.10  thf(t48_xboole_1, axiom,
% 15.90/16.10    (![A:$i,B:$i]:
% 15.90/16.10     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 15.90/16.10  thf('8', plain,
% 15.90/16.10      (![X25 : $i, X26 : $i]:
% 15.90/16.10         ((k4_xboole_0 @ X25 @ (k4_xboole_0 @ X25 @ X26))
% 15.90/16.10           = (k3_xboole_0 @ X25 @ X26))),
% 15.90/16.10      inference('cnf', [status(esa)], [t48_xboole_1])).
% 15.90/16.10  thf(t36_xboole_1, axiom,
% 15.90/16.10    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 15.90/16.10  thf('9', plain,
% 15.90/16.10      (![X18 : $i, X19 : $i]: (r1_tarski @ (k4_xboole_0 @ X18 @ X19) @ X18)),
% 15.90/16.10      inference('cnf', [status(esa)], [t36_xboole_1])).
% 15.90/16.10  thf('10', plain,
% 15.90/16.10      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 15.90/16.10      inference('sup+', [status(thm)], ['8', '9'])).
% 15.90/16.10  thf('11', plain,
% 15.90/16.10      (![X5 : $i, X7 : $i]:
% 15.90/16.10         (((X5) = (X7)) | ~ (r1_tarski @ X7 @ X5) | ~ (r1_tarski @ X5 @ X7))),
% 15.90/16.10      inference('cnf', [status(esa)], [d10_xboole_0])).
% 15.90/16.10  thf('12', plain,
% 15.90/16.10      (![X0 : $i, X1 : $i]:
% 15.90/16.10         (~ (r1_tarski @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 15.90/16.10          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 15.90/16.10      inference('sup-', [status(thm)], ['10', '11'])).
% 15.90/16.10  thf('13', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 15.90/16.10      inference('sup-', [status(thm)], ['7', '12'])).
% 15.90/16.10  thf('14', plain,
% 15.90/16.10      (![X25 : $i, X26 : $i]:
% 15.90/16.10         ((k4_xboole_0 @ X25 @ (k4_xboole_0 @ X25 @ X26))
% 15.90/16.10           = (k3_xboole_0 @ X25 @ X26))),
% 15.90/16.10      inference('cnf', [status(esa)], [t48_xboole_1])).
% 15.90/16.10  thf(t38_xboole_1, axiom,
% 15.90/16.10    (![A:$i,B:$i]:
% 15.90/16.10     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) ) =>
% 15.90/16.10       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 15.90/16.10  thf('15', plain,
% 15.90/16.10      (![X20 : $i, X21 : $i]:
% 15.90/16.10         (((X20) = (k1_xboole_0))
% 15.90/16.10          | ~ (r1_tarski @ X20 @ (k4_xboole_0 @ X21 @ X20)))),
% 15.90/16.10      inference('cnf', [status(esa)], [t38_xboole_1])).
% 15.90/16.10  thf('16', plain,
% 15.90/16.10      (![X0 : $i, X1 : $i]:
% 15.90/16.10         (~ (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 15.90/16.10          | ((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0)))),
% 15.90/16.10      inference('sup-', [status(thm)], ['14', '15'])).
% 15.90/16.10  thf('17', plain,
% 15.90/16.10      (![X0 : $i]:
% 15.90/16.10         (~ (r1_tarski @ (k4_xboole_0 @ X0 @ X0) @ X0)
% 15.90/16.10          | ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0)))),
% 15.90/16.10      inference('sup-', [status(thm)], ['13', '16'])).
% 15.90/16.10  thf('18', plain,
% 15.90/16.10      (![X18 : $i, X19 : $i]: (r1_tarski @ (k4_xboole_0 @ X18 @ X19) @ X18)),
% 15.90/16.10      inference('cnf', [status(esa)], [t36_xboole_1])).
% 15.90/16.10  thf('19', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 15.90/16.10      inference('demod', [status(thm)], ['17', '18'])).
% 15.90/16.10  thf(t44_xboole_1, axiom,
% 15.90/16.10    (![A:$i,B:$i,C:$i]:
% 15.90/16.10     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 15.90/16.10       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 15.90/16.10  thf('20', plain,
% 15.90/16.10      (![X22 : $i, X23 : $i, X24 : $i]:
% 15.90/16.10         ((r1_tarski @ X22 @ (k2_xboole_0 @ X23 @ X24))
% 15.90/16.10          | ~ (r1_tarski @ (k4_xboole_0 @ X22 @ X23) @ X24))),
% 15.90/16.10      inference('cnf', [status(esa)], [t44_xboole_1])).
% 15.90/16.10  thf('21', plain,
% 15.90/16.10      (![X0 : $i, X1 : $i]:
% 15.90/16.10         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 15.90/16.10          | (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 15.90/16.10      inference('sup-', [status(thm)], ['19', '20'])).
% 15.90/16.10  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 15.90/16.10  thf('22', plain, (![X17 : $i]: (r1_tarski @ k1_xboole_0 @ X17)),
% 15.90/16.10      inference('cnf', [status(esa)], [t2_xboole_1])).
% 15.90/16.10  thf('23', plain,
% 15.90/16.10      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 15.90/16.10      inference('demod', [status(thm)], ['21', '22'])).
% 15.90/16.10  thf('24', plain,
% 15.90/16.10      (![X55 : $i]:
% 15.90/16.10         (((k3_relat_1 @ X55)
% 15.90/16.10            = (k2_xboole_0 @ (k1_relat_1 @ X55) @ (k2_relat_1 @ X55)))
% 15.90/16.10          | ~ (v1_relat_1 @ X55))),
% 15.90/16.10      inference('cnf', [status(esa)], [d6_relat_1])).
% 15.90/16.10  thf('25', plain, (![X6 : $i]: (r1_tarski @ X6 @ X6)),
% 15.90/16.10      inference('simplify', [status(thm)], ['2'])).
% 15.90/16.10  thf(t10_xboole_1, axiom,
% 15.90/16.10    (![A:$i,B:$i,C:$i]:
% 15.90/16.10     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 15.90/16.10  thf('26', plain,
% 15.90/16.10      (![X8 : $i, X9 : $i, X10 : $i]:
% 15.90/16.10         (~ (r1_tarski @ X8 @ X9) | (r1_tarski @ X8 @ (k2_xboole_0 @ X10 @ X9)))),
% 15.90/16.10      inference('cnf', [status(esa)], [t10_xboole_1])).
% 15.90/16.10  thf('27', plain,
% 15.90/16.10      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 15.90/16.10      inference('sup-', [status(thm)], ['25', '26'])).
% 15.90/16.10  thf('28', plain,
% 15.90/16.10      (![X0 : $i]:
% 15.90/16.10         ((r1_tarski @ (k2_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 15.90/16.10          | ~ (v1_relat_1 @ X0))),
% 15.90/16.10      inference('sup+', [status(thm)], ['24', '27'])).
% 15.90/16.10  thf('29', plain, ((r1_tarski @ sk_A @ sk_B_2)),
% 15.90/16.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.90/16.10  thf(t25_relat_1, axiom,
% 15.90/16.10    (![A:$i]:
% 15.90/16.10     ( ( v1_relat_1 @ A ) =>
% 15.90/16.10       ( ![B:$i]:
% 15.90/16.10         ( ( v1_relat_1 @ B ) =>
% 15.90/16.10           ( ( r1_tarski @ A @ B ) =>
% 15.90/16.10             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 15.90/16.10               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 15.90/16.10  thf('30', plain,
% 15.90/16.10      (![X58 : $i, X59 : $i]:
% 15.90/16.10         (~ (v1_relat_1 @ X58)
% 15.90/16.10          | (r1_tarski @ (k2_relat_1 @ X59) @ (k2_relat_1 @ X58))
% 15.90/16.10          | ~ (r1_tarski @ X59 @ X58)
% 15.90/16.10          | ~ (v1_relat_1 @ X59))),
% 15.90/16.10      inference('cnf', [status(esa)], [t25_relat_1])).
% 15.90/16.10  thf('31', plain,
% 15.90/16.10      ((~ (v1_relat_1 @ sk_A)
% 15.90/16.10        | (r1_tarski @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B_2))
% 15.90/16.10        | ~ (v1_relat_1 @ sk_B_2))),
% 15.90/16.10      inference('sup-', [status(thm)], ['29', '30'])).
% 15.90/16.10  thf('32', plain, ((v1_relat_1 @ sk_A)),
% 15.90/16.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.90/16.10  thf('33', plain, ((v1_relat_1 @ sk_B_2)),
% 15.90/16.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.90/16.10  thf('34', plain, ((r1_tarski @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B_2))),
% 15.90/16.10      inference('demod', [status(thm)], ['31', '32', '33'])).
% 15.90/16.10  thf(t1_xboole_1, axiom,
% 15.90/16.10    (![A:$i,B:$i,C:$i]:
% 15.90/16.10     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 15.90/16.10       ( r1_tarski @ A @ C ) ))).
% 15.90/16.10  thf('35', plain,
% 15.90/16.10      (![X14 : $i, X15 : $i, X16 : $i]:
% 15.90/16.10         (~ (r1_tarski @ X14 @ X15)
% 15.90/16.10          | ~ (r1_tarski @ X15 @ X16)
% 15.90/16.10          | (r1_tarski @ X14 @ X16))),
% 15.90/16.10      inference('cnf', [status(esa)], [t1_xboole_1])).
% 15.90/16.10  thf('36', plain,
% 15.90/16.10      (![X0 : $i]:
% 15.90/16.10         ((r1_tarski @ (k2_relat_1 @ sk_A) @ X0)
% 15.90/16.10          | ~ (r1_tarski @ (k2_relat_1 @ sk_B_2) @ X0))),
% 15.90/16.10      inference('sup-', [status(thm)], ['34', '35'])).
% 15.90/16.10  thf('37', plain,
% 15.90/16.10      ((~ (v1_relat_1 @ sk_B_2)
% 15.90/16.10        | (r1_tarski @ (k2_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_2)))),
% 15.90/16.10      inference('sup-', [status(thm)], ['28', '36'])).
% 15.90/16.10  thf('38', plain, ((v1_relat_1 @ sk_B_2)),
% 15.90/16.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.90/16.10  thf('39', plain, ((r1_tarski @ (k2_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_2))),
% 15.90/16.10      inference('demod', [status(thm)], ['37', '38'])).
% 15.90/16.10  thf('40', plain,
% 15.90/16.10      (![X14 : $i, X15 : $i, X16 : $i]:
% 15.90/16.10         (~ (r1_tarski @ X14 @ X15)
% 15.90/16.10          | ~ (r1_tarski @ X15 @ X16)
% 15.90/16.10          | (r1_tarski @ X14 @ X16))),
% 15.90/16.10      inference('cnf', [status(esa)], [t1_xboole_1])).
% 15.90/16.10  thf('41', plain,
% 15.90/16.10      (![X0 : $i]:
% 15.90/16.10         ((r1_tarski @ (k2_relat_1 @ sk_A) @ X0)
% 15.90/16.10          | ~ (r1_tarski @ (k3_relat_1 @ sk_B_2) @ X0))),
% 15.90/16.10      inference('sup-', [status(thm)], ['39', '40'])).
% 15.90/16.10  thf('42', plain,
% 15.90/16.10      (![X0 : $i]:
% 15.90/16.10         (r1_tarski @ (k2_relat_1 @ sk_A) @ 
% 15.90/16.10          (k2_xboole_0 @ (k3_relat_1 @ sk_B_2) @ X0))),
% 15.90/16.10      inference('sup-', [status(thm)], ['23', '41'])).
% 15.90/16.10  thf('43', plain,
% 15.90/16.10      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 15.90/16.10      inference('sup-', [status(thm)], ['25', '26'])).
% 15.90/16.10  thf(t8_xboole_1, axiom,
% 15.90/16.10    (![A:$i,B:$i,C:$i]:
% 15.90/16.10     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 15.90/16.10       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 15.90/16.10  thf('44', plain,
% 15.90/16.10      (![X28 : $i, X29 : $i, X30 : $i]:
% 15.90/16.10         (~ (r1_tarski @ X28 @ X29)
% 15.90/16.10          | ~ (r1_tarski @ X30 @ X29)
% 15.90/16.10          | (r1_tarski @ (k2_xboole_0 @ X28 @ X30) @ X29))),
% 15.90/16.10      inference('cnf', [status(esa)], [t8_xboole_1])).
% 15.90/16.10  thf('45', plain,
% 15.90/16.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.90/16.10         ((r1_tarski @ (k2_xboole_0 @ X0 @ X2) @ (k2_xboole_0 @ X1 @ X0))
% 15.90/16.10          | ~ (r1_tarski @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 15.90/16.10      inference('sup-', [status(thm)], ['43', '44'])).
% 15.90/16.10  thf('46', plain,
% 15.90/16.10      (![X0 : $i]:
% 15.90/16.10         (r1_tarski @ (k2_xboole_0 @ X0 @ (k2_relat_1 @ sk_A)) @ 
% 15.90/16.10          (k2_xboole_0 @ (k3_relat_1 @ sk_B_2) @ X0))),
% 15.90/16.10      inference('sup-', [status(thm)], ['42', '45'])).
% 15.90/16.10  thf('47', plain,
% 15.90/16.10      (((r1_tarski @ (k3_relat_1 @ sk_A) @ 
% 15.90/16.10         (k2_xboole_0 @ (k3_relat_1 @ sk_B_2) @ (k1_relat_1 @ sk_A)))
% 15.90/16.10        | ~ (v1_relat_1 @ sk_A))),
% 15.90/16.10      inference('sup+', [status(thm)], ['1', '46'])).
% 15.90/16.10  thf('48', plain,
% 15.90/16.10      (![X55 : $i]:
% 15.90/16.10         (((k3_relat_1 @ X55)
% 15.90/16.10            = (k2_xboole_0 @ (k1_relat_1 @ X55) @ (k2_relat_1 @ X55)))
% 15.90/16.10          | ~ (v1_relat_1 @ X55))),
% 15.90/16.10      inference('cnf', [status(esa)], [d6_relat_1])).
% 15.90/16.10  thf('49', plain,
% 15.90/16.10      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 15.90/16.10      inference('demod', [status(thm)], ['21', '22'])).
% 15.90/16.10  thf('50', plain,
% 15.90/16.10      (![X0 : $i]:
% 15.90/16.10         ((r1_tarski @ (k1_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 15.90/16.10          | ~ (v1_relat_1 @ X0))),
% 15.90/16.10      inference('sup+', [status(thm)], ['48', '49'])).
% 15.90/16.10  thf('51', plain, ((r1_tarski @ sk_A @ sk_B_2)),
% 15.90/16.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.90/16.10  thf('52', plain,
% 15.90/16.10      (![X58 : $i, X59 : $i]:
% 15.90/16.10         (~ (v1_relat_1 @ X58)
% 15.90/16.10          | (r1_tarski @ (k1_relat_1 @ X59) @ (k1_relat_1 @ X58))
% 15.90/16.10          | ~ (r1_tarski @ X59 @ X58)
% 15.90/16.10          | ~ (v1_relat_1 @ X59))),
% 15.90/16.10      inference('cnf', [status(esa)], [t25_relat_1])).
% 15.90/16.10  thf('53', plain,
% 15.90/16.10      ((~ (v1_relat_1 @ sk_A)
% 15.90/16.10        | (r1_tarski @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B_2))
% 15.90/16.10        | ~ (v1_relat_1 @ sk_B_2))),
% 15.90/16.10      inference('sup-', [status(thm)], ['51', '52'])).
% 15.90/16.10  thf('54', plain, ((v1_relat_1 @ sk_A)),
% 15.90/16.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.90/16.10  thf('55', plain, ((v1_relat_1 @ sk_B_2)),
% 15.90/16.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.90/16.10  thf('56', plain, ((r1_tarski @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B_2))),
% 15.90/16.10      inference('demod', [status(thm)], ['53', '54', '55'])).
% 15.90/16.10  thf('57', plain,
% 15.90/16.10      (![X14 : $i, X15 : $i, X16 : $i]:
% 15.90/16.10         (~ (r1_tarski @ X14 @ X15)
% 15.90/16.10          | ~ (r1_tarski @ X15 @ X16)
% 15.90/16.10          | (r1_tarski @ X14 @ X16))),
% 15.90/16.10      inference('cnf', [status(esa)], [t1_xboole_1])).
% 15.90/16.10  thf('58', plain,
% 15.90/16.10      (![X0 : $i]:
% 15.90/16.10         ((r1_tarski @ (k1_relat_1 @ sk_A) @ X0)
% 15.90/16.10          | ~ (r1_tarski @ (k1_relat_1 @ sk_B_2) @ X0))),
% 15.90/16.10      inference('sup-', [status(thm)], ['56', '57'])).
% 15.90/16.10  thf('59', plain,
% 15.90/16.10      ((~ (v1_relat_1 @ sk_B_2)
% 15.90/16.10        | (r1_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_2)))),
% 15.90/16.10      inference('sup-', [status(thm)], ['50', '58'])).
% 15.90/16.10  thf('60', plain, ((v1_relat_1 @ sk_B_2)),
% 15.90/16.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.90/16.10  thf('61', plain, ((r1_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_2))),
% 15.90/16.10      inference('demod', [status(thm)], ['59', '60'])).
% 15.90/16.10  thf('62', plain, (![X6 : $i]: (r1_tarski @ X6 @ X6)),
% 15.90/16.10      inference('simplify', [status(thm)], ['2'])).
% 15.90/16.10  thf('63', plain,
% 15.90/16.10      (![X28 : $i, X29 : $i, X30 : $i]:
% 15.90/16.10         (~ (r1_tarski @ X28 @ X29)
% 15.90/16.10          | ~ (r1_tarski @ X30 @ X29)
% 15.90/16.10          | (r1_tarski @ (k2_xboole_0 @ X28 @ X30) @ X29))),
% 15.90/16.10      inference('cnf', [status(esa)], [t8_xboole_1])).
% 15.90/16.10  thf('64', plain,
% 15.90/16.10      (![X0 : $i, X1 : $i]:
% 15.90/16.10         ((r1_tarski @ (k2_xboole_0 @ X0 @ X1) @ X0) | ~ (r1_tarski @ X1 @ X0))),
% 15.90/16.10      inference('sup-', [status(thm)], ['62', '63'])).
% 15.90/16.10  thf('65', plain,
% 15.90/16.10      ((r1_tarski @ 
% 15.90/16.10        (k2_xboole_0 @ (k3_relat_1 @ sk_B_2) @ (k1_relat_1 @ sk_A)) @ 
% 15.90/16.10        (k3_relat_1 @ sk_B_2))),
% 15.90/16.10      inference('sup-', [status(thm)], ['61', '64'])).
% 15.90/16.10  thf('66', plain,
% 15.90/16.10      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 15.90/16.10      inference('demod', [status(thm)], ['21', '22'])).
% 15.90/16.10  thf('67', plain,
% 15.90/16.10      (![X5 : $i, X7 : $i]:
% 15.90/16.10         (((X5) = (X7)) | ~ (r1_tarski @ X7 @ X5) | ~ (r1_tarski @ X5 @ X7))),
% 15.90/16.10      inference('cnf', [status(esa)], [d10_xboole_0])).
% 15.90/16.10  thf('68', plain,
% 15.90/16.10      (![X0 : $i, X1 : $i]:
% 15.90/16.10         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 15.90/16.10          | ((k2_xboole_0 @ X1 @ X0) = (X1)))),
% 15.90/16.10      inference('sup-', [status(thm)], ['66', '67'])).
% 15.90/16.10  thf('69', plain,
% 15.90/16.10      (((k2_xboole_0 @ (k3_relat_1 @ sk_B_2) @ (k1_relat_1 @ sk_A))
% 15.90/16.10         = (k3_relat_1 @ sk_B_2))),
% 15.90/16.10      inference('sup-', [status(thm)], ['65', '68'])).
% 15.90/16.10  thf('70', plain, ((v1_relat_1 @ sk_A)),
% 15.90/16.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.90/16.10  thf('71', plain, ((r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_2))),
% 15.90/16.10      inference('demod', [status(thm)], ['47', '69', '70'])).
% 15.90/16.10  thf('72', plain, ($false), inference('demod', [status(thm)], ['0', '71'])).
% 15.90/16.10  
% 15.90/16.10  % SZS output end Refutation
% 15.90/16.10  
% 15.90/16.11  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
