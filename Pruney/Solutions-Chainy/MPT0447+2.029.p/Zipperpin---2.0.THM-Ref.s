%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.q1RY7xSeUf

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:56 EST 2020

% Result     : Theorem 26.49s
% Output     : Refutation 26.49s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 189 expanded)
%              Number of leaves         :   29 (  66 expanded)
%              Depth                    :   21
%              Number of atoms          :  627 (1429 expanded)
%              Number of equality atoms :   23 (  49 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ~ ( r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X36: $i] :
      ( ( ( k3_relat_1 @ X36 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X36 ) @ ( k2_relat_1 @ X36 ) ) )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('2',plain,(
    ! [X36: $i] :
      ( ( ( k3_relat_1 @ X36 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X36 ) @ ( k2_relat_1 @ X36 ) ) )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_tarski @ X20 @ ( k2_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( X1 != X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('6',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('8',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r1_tarski @ X22 @ X23 )
      | ~ ( r1_tarski @ X24 @ X23 )
      | ( r1_tarski @ ( k2_xboole_0 @ X22 @ X24 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ sk_A @ X0 ) @ sk_B )
      | ~ ( r1_tarski @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_A @ sk_B ) @ sk_B ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['5'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('12',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X4 @ ( k2_xboole_0 @ X6 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['10','15'])).

thf(t13_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k2_xboole_0 @ A @ B ) )
            = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('17',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( v1_relat_1 @ X37 )
      | ( ( k1_relat_1 @ ( k2_xboole_0 @ X38 @ X37 ) )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X38 ) @ ( k1_relat_1 @ X37 ) ) )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t13_relat_1])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('18',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X7 @ X9 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ X0 )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['24','25'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('27',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X13 @ X14 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('28',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ~ ( r1_tarski @ X11 @ X12 )
      | ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) @ ( k3_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('31',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X18 @ X19 ) @ X19 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('32',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r1_xboole_0 @ X16 @ X17 )
      | ~ ( r1_tarski @ X16 @ X17 )
      | ( v1_xboole_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_xboole_0 @ ( k4_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('35',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('36',plain,
    ( ( k4_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['34','35'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('37',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k2_xboole_0 @ X25 @ X26 )
      = ( k5_xboole_0 @ X25 @ ( k4_xboole_0 @ X26 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('38',plain,
    ( ( k2_xboole_0 @ ( k3_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_A ) )
    = ( k5_xboole_0 @ ( k3_relat_1 @ sk_B ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('39',plain,(
    ! [X15: $i] :
      ( ( k5_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('40',plain,
    ( ( k2_xboole_0 @ ( k3_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_A ) )
    = ( k3_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_tarski @ X20 @ ( k2_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('42',plain,(
    ! [X36: $i] :
      ( ( ( k3_relat_1 @ X36 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X36 ) @ ( k2_relat_1 @ X36 ) ) )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('44',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ~ ( r1_tarski @ X11 @ X12 )
      | ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X2 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k3_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X1 ) @ ( k2_xboole_0 @ ( k3_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['41','46'])).

thf('48',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ sk_B ) @ ( k3_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['40','47'])).

thf('49',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_B ) @ ( k3_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['10','15'])).

thf(t26_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k2_relat_1 @ ( k2_xboole_0 @ A @ B ) )
            = ( k2_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) )).

thf('52',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( v1_relat_1 @ X39 )
      | ( ( k2_relat_1 @ ( k2_xboole_0 @ X40 @ X39 ) )
        = ( k2_xboole_0 @ ( k2_relat_1 @ X40 ) @ ( k2_relat_1 @ X39 ) ) )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t26_relat_1])).

thf('53',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X7 @ X9 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_B ) @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ X0 )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_B ) @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['50','58'])).

thf('60',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('61',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r1_tarski @ X22 @ X23 )
      | ~ ( r1_tarski @ X24 @ X23 )
      | ( r1_tarski @ ( k2_xboole_0 @ X22 @ X24 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) @ ( k3_relat_1 @ sk_B ) )
      | ~ ( r1_tarski @ X0 @ ( k3_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) @ ( k3_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['59','62'])).

thf('64',plain,
    ( ( r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['1','63'])).

thf('65',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    $false ),
    inference(demod,[status(thm)],['0','66'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.q1RY7xSeUf
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:42:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 26.49/26.74  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 26.49/26.74  % Solved by: fo/fo7.sh
% 26.49/26.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 26.49/26.74  % done 30564 iterations in 26.280s
% 26.49/26.74  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 26.49/26.74  % SZS output start Refutation
% 26.49/26.74  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 26.49/26.74  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 26.49/26.74  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 26.49/26.74  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 26.49/26.74  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 26.49/26.74  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 26.49/26.74  thf(sk_B_type, type, sk_B: $i).
% 26.49/26.74  thf(sk_A_type, type, sk_A: $i).
% 26.49/26.74  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 26.49/26.74  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 26.49/26.74  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 26.49/26.74  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 26.49/26.74  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 26.49/26.74  thf(t31_relat_1, conjecture,
% 26.49/26.74    (![A:$i]:
% 26.49/26.74     ( ( v1_relat_1 @ A ) =>
% 26.49/26.74       ( ![B:$i]:
% 26.49/26.74         ( ( v1_relat_1 @ B ) =>
% 26.49/26.74           ( ( r1_tarski @ A @ B ) =>
% 26.49/26.74             ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ))).
% 26.49/26.74  thf(zf_stmt_0, negated_conjecture,
% 26.49/26.74    (~( ![A:$i]:
% 26.49/26.74        ( ( v1_relat_1 @ A ) =>
% 26.49/26.74          ( ![B:$i]:
% 26.49/26.74            ( ( v1_relat_1 @ B ) =>
% 26.49/26.74              ( ( r1_tarski @ A @ B ) =>
% 26.49/26.74                ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ) )),
% 26.49/26.74    inference('cnf.neg', [status(esa)], [t31_relat_1])).
% 26.49/26.74  thf('0', plain, (~ (r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 26.49/26.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.49/26.74  thf(d6_relat_1, axiom,
% 26.49/26.74    (![A:$i]:
% 26.49/26.74     ( ( v1_relat_1 @ A ) =>
% 26.49/26.74       ( ( k3_relat_1 @ A ) =
% 26.49/26.74         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 26.49/26.74  thf('1', plain,
% 26.49/26.74      (![X36 : $i]:
% 26.49/26.74         (((k3_relat_1 @ X36)
% 26.49/26.74            = (k2_xboole_0 @ (k1_relat_1 @ X36) @ (k2_relat_1 @ X36)))
% 26.49/26.74          | ~ (v1_relat_1 @ X36))),
% 26.49/26.74      inference('cnf', [status(esa)], [d6_relat_1])).
% 26.49/26.74  thf('2', plain,
% 26.49/26.74      (![X36 : $i]:
% 26.49/26.74         (((k3_relat_1 @ X36)
% 26.49/26.74            = (k2_xboole_0 @ (k1_relat_1 @ X36) @ (k2_relat_1 @ X36)))
% 26.49/26.74          | ~ (v1_relat_1 @ X36))),
% 26.49/26.74      inference('cnf', [status(esa)], [d6_relat_1])).
% 26.49/26.74  thf(t7_xboole_1, axiom,
% 26.49/26.74    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 26.49/26.74  thf('3', plain,
% 26.49/26.74      (![X20 : $i, X21 : $i]: (r1_tarski @ X20 @ (k2_xboole_0 @ X20 @ X21))),
% 26.49/26.74      inference('cnf', [status(esa)], [t7_xboole_1])).
% 26.49/26.74  thf('4', plain,
% 26.49/26.74      (![X0 : $i]:
% 26.49/26.74         ((r1_tarski @ (k1_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 26.49/26.74          | ~ (v1_relat_1 @ X0))),
% 26.49/26.74      inference('sup+', [status(thm)], ['2', '3'])).
% 26.49/26.74  thf(d10_xboole_0, axiom,
% 26.49/26.74    (![A:$i,B:$i]:
% 26.49/26.74     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 26.49/26.74  thf('5', plain,
% 26.49/26.74      (![X1 : $i, X2 : $i]: ((r1_tarski @ X1 @ X2) | ((X1) != (X2)))),
% 26.49/26.74      inference('cnf', [status(esa)], [d10_xboole_0])).
% 26.49/26.74  thf('6', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 26.49/26.74      inference('simplify', [status(thm)], ['5'])).
% 26.49/26.74  thf('7', plain, ((r1_tarski @ sk_A @ sk_B)),
% 26.49/26.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.49/26.74  thf(t8_xboole_1, axiom,
% 26.49/26.74    (![A:$i,B:$i,C:$i]:
% 26.49/26.74     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 26.49/26.74       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 26.49/26.74  thf('8', plain,
% 26.49/26.74      (![X22 : $i, X23 : $i, X24 : $i]:
% 26.49/26.74         (~ (r1_tarski @ X22 @ X23)
% 26.49/26.74          | ~ (r1_tarski @ X24 @ X23)
% 26.49/26.74          | (r1_tarski @ (k2_xboole_0 @ X22 @ X24) @ X23))),
% 26.49/26.74      inference('cnf', [status(esa)], [t8_xboole_1])).
% 26.49/26.74  thf('9', plain,
% 26.49/26.74      (![X0 : $i]:
% 26.49/26.74         ((r1_tarski @ (k2_xboole_0 @ sk_A @ X0) @ sk_B)
% 26.49/26.74          | ~ (r1_tarski @ X0 @ sk_B))),
% 26.49/26.74      inference('sup-', [status(thm)], ['7', '8'])).
% 26.49/26.74  thf('10', plain, ((r1_tarski @ (k2_xboole_0 @ sk_A @ sk_B) @ sk_B)),
% 26.49/26.74      inference('sup-', [status(thm)], ['6', '9'])).
% 26.49/26.74  thf('11', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 26.49/26.74      inference('simplify', [status(thm)], ['5'])).
% 26.49/26.74  thf(t10_xboole_1, axiom,
% 26.49/26.74    (![A:$i,B:$i,C:$i]:
% 26.49/26.74     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 26.49/26.74  thf('12', plain,
% 26.49/26.74      (![X4 : $i, X5 : $i, X6 : $i]:
% 26.49/26.74         (~ (r1_tarski @ X4 @ X5) | (r1_tarski @ X4 @ (k2_xboole_0 @ X6 @ X5)))),
% 26.49/26.74      inference('cnf', [status(esa)], [t10_xboole_1])).
% 26.49/26.74  thf('13', plain,
% 26.49/26.74      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 26.49/26.74      inference('sup-', [status(thm)], ['11', '12'])).
% 26.49/26.74  thf('14', plain,
% 26.49/26.74      (![X1 : $i, X3 : $i]:
% 26.49/26.74         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 26.49/26.74      inference('cnf', [status(esa)], [d10_xboole_0])).
% 26.49/26.74  thf('15', plain,
% 26.49/26.74      (![X0 : $i, X1 : $i]:
% 26.49/26.74         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 26.49/26.74          | ((k2_xboole_0 @ X1 @ X0) = (X0)))),
% 26.49/26.74      inference('sup-', [status(thm)], ['13', '14'])).
% 26.49/26.74  thf('16', plain, (((k2_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 26.49/26.74      inference('sup-', [status(thm)], ['10', '15'])).
% 26.49/26.74  thf(t13_relat_1, axiom,
% 26.49/26.74    (![A:$i]:
% 26.49/26.74     ( ( v1_relat_1 @ A ) =>
% 26.49/26.74       ( ![B:$i]:
% 26.49/26.74         ( ( v1_relat_1 @ B ) =>
% 26.49/26.74           ( ( k1_relat_1 @ ( k2_xboole_0 @ A @ B ) ) =
% 26.49/26.74             ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 26.49/26.74  thf('17', plain,
% 26.49/26.74      (![X37 : $i, X38 : $i]:
% 26.49/26.74         (~ (v1_relat_1 @ X37)
% 26.49/26.74          | ((k1_relat_1 @ (k2_xboole_0 @ X38 @ X37))
% 26.49/26.74              = (k2_xboole_0 @ (k1_relat_1 @ X38) @ (k1_relat_1 @ X37)))
% 26.49/26.74          | ~ (v1_relat_1 @ X38))),
% 26.49/26.74      inference('cnf', [status(esa)], [t13_relat_1])).
% 26.49/26.74  thf(t11_xboole_1, axiom,
% 26.49/26.74    (![A:$i,B:$i,C:$i]:
% 26.49/26.74     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 26.49/26.74  thf('18', plain,
% 26.49/26.74      (![X7 : $i, X8 : $i, X9 : $i]:
% 26.49/26.74         ((r1_tarski @ X7 @ X8) | ~ (r1_tarski @ (k2_xboole_0 @ X7 @ X9) @ X8))),
% 26.49/26.74      inference('cnf', [status(esa)], [t11_xboole_1])).
% 26.49/26.74  thf('19', plain,
% 26.49/26.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 26.49/26.74         (~ (r1_tarski @ (k1_relat_1 @ (k2_xboole_0 @ X1 @ X0)) @ X2)
% 26.49/26.74          | ~ (v1_relat_1 @ X1)
% 26.49/26.74          | ~ (v1_relat_1 @ X0)
% 26.49/26.74          | (r1_tarski @ (k1_relat_1 @ X1) @ X2))),
% 26.49/26.74      inference('sup-', [status(thm)], ['17', '18'])).
% 26.49/26.74  thf('20', plain,
% 26.49/26.74      (![X0 : $i]:
% 26.49/26.74         (~ (r1_tarski @ (k1_relat_1 @ sk_B) @ X0)
% 26.49/26.74          | (r1_tarski @ (k1_relat_1 @ sk_A) @ X0)
% 26.49/26.74          | ~ (v1_relat_1 @ sk_B)
% 26.49/26.74          | ~ (v1_relat_1 @ sk_A))),
% 26.49/26.74      inference('sup-', [status(thm)], ['16', '19'])).
% 26.49/26.74  thf('21', plain, ((v1_relat_1 @ sk_B)),
% 26.49/26.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.49/26.74  thf('22', plain, ((v1_relat_1 @ sk_A)),
% 26.49/26.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.49/26.74  thf('23', plain,
% 26.49/26.74      (![X0 : $i]:
% 26.49/26.74         (~ (r1_tarski @ (k1_relat_1 @ sk_B) @ X0)
% 26.49/26.74          | (r1_tarski @ (k1_relat_1 @ sk_A) @ X0))),
% 26.49/26.74      inference('demod', [status(thm)], ['20', '21', '22'])).
% 26.49/26.74  thf('24', plain,
% 26.49/26.74      ((~ (v1_relat_1 @ sk_B)
% 26.49/26.74        | (r1_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B)))),
% 26.49/26.74      inference('sup-', [status(thm)], ['4', '23'])).
% 26.49/26.74  thf('25', plain, ((v1_relat_1 @ sk_B)),
% 26.49/26.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.49/26.74  thf('26', plain, ((r1_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 26.49/26.74      inference('demod', [status(thm)], ['24', '25'])).
% 26.49/26.74  thf(t36_xboole_1, axiom,
% 26.49/26.74    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 26.49/26.74  thf('27', plain,
% 26.49/26.74      (![X13 : $i, X14 : $i]: (r1_tarski @ (k4_xboole_0 @ X13 @ X14) @ X13)),
% 26.49/26.74      inference('cnf', [status(esa)], [t36_xboole_1])).
% 26.49/26.74  thf(t1_xboole_1, axiom,
% 26.49/26.74    (![A:$i,B:$i,C:$i]:
% 26.49/26.74     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 26.49/26.74       ( r1_tarski @ A @ C ) ))).
% 26.49/26.74  thf('28', plain,
% 26.49/26.74      (![X10 : $i, X11 : $i, X12 : $i]:
% 26.49/26.74         (~ (r1_tarski @ X10 @ X11)
% 26.49/26.74          | ~ (r1_tarski @ X11 @ X12)
% 26.49/26.74          | (r1_tarski @ X10 @ X12))),
% 26.49/26.74      inference('cnf', [status(esa)], [t1_xboole_1])).
% 26.49/26.74  thf('29', plain,
% 26.49/26.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 26.49/26.74         ((r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 26.49/26.74      inference('sup-', [status(thm)], ['27', '28'])).
% 26.49/26.74  thf('30', plain,
% 26.49/26.74      (![X0 : $i]:
% 26.49/26.74         (r1_tarski @ (k4_xboole_0 @ (k1_relat_1 @ sk_A) @ X0) @ 
% 26.49/26.74          (k3_relat_1 @ sk_B))),
% 26.49/26.74      inference('sup-', [status(thm)], ['26', '29'])).
% 26.49/26.74  thf(t79_xboole_1, axiom,
% 26.49/26.74    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 26.49/26.74  thf('31', plain,
% 26.49/26.74      (![X18 : $i, X19 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X18 @ X19) @ X19)),
% 26.49/26.74      inference('cnf', [status(esa)], [t79_xboole_1])).
% 26.49/26.74  thf(t69_xboole_1, axiom,
% 26.49/26.74    (![A:$i,B:$i]:
% 26.49/26.74     ( ( ~( v1_xboole_0 @ B ) ) =>
% 26.49/26.74       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 26.49/26.74  thf('32', plain,
% 26.49/26.74      (![X16 : $i, X17 : $i]:
% 26.49/26.74         (~ (r1_xboole_0 @ X16 @ X17)
% 26.49/26.74          | ~ (r1_tarski @ X16 @ X17)
% 26.49/26.74          | (v1_xboole_0 @ X16))),
% 26.49/26.74      inference('cnf', [status(esa)], [t69_xboole_1])).
% 26.49/26.74  thf('33', plain,
% 26.49/26.74      (![X0 : $i, X1 : $i]:
% 26.49/26.74         ((v1_xboole_0 @ (k4_xboole_0 @ X1 @ X0))
% 26.49/26.74          | ~ (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 26.49/26.74      inference('sup-', [status(thm)], ['31', '32'])).
% 26.49/26.74  thf('34', plain,
% 26.49/26.74      ((v1_xboole_0 @ (k4_xboole_0 @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B)))),
% 26.49/26.74      inference('sup-', [status(thm)], ['30', '33'])).
% 26.49/26.74  thf(l13_xboole_0, axiom,
% 26.49/26.74    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 26.49/26.74  thf('35', plain,
% 26.49/26.74      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 26.49/26.74      inference('cnf', [status(esa)], [l13_xboole_0])).
% 26.49/26.74  thf('36', plain,
% 26.49/26.74      (((k4_xboole_0 @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))
% 26.49/26.74         = (k1_xboole_0))),
% 26.49/26.74      inference('sup-', [status(thm)], ['34', '35'])).
% 26.49/26.74  thf(t98_xboole_1, axiom,
% 26.49/26.74    (![A:$i,B:$i]:
% 26.49/26.74     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 26.49/26.74  thf('37', plain,
% 26.49/26.74      (![X25 : $i, X26 : $i]:
% 26.49/26.74         ((k2_xboole_0 @ X25 @ X26)
% 26.49/26.74           = (k5_xboole_0 @ X25 @ (k4_xboole_0 @ X26 @ X25)))),
% 26.49/26.74      inference('cnf', [status(esa)], [t98_xboole_1])).
% 26.49/26.74  thf('38', plain,
% 26.49/26.74      (((k2_xboole_0 @ (k3_relat_1 @ sk_B) @ (k1_relat_1 @ sk_A))
% 26.49/26.74         = (k5_xboole_0 @ (k3_relat_1 @ sk_B) @ k1_xboole_0))),
% 26.49/26.74      inference('sup+', [status(thm)], ['36', '37'])).
% 26.49/26.74  thf(t5_boole, axiom,
% 26.49/26.74    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 26.49/26.74  thf('39', plain, (![X15 : $i]: ((k5_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 26.49/26.74      inference('cnf', [status(esa)], [t5_boole])).
% 26.49/26.74  thf('40', plain,
% 26.49/26.74      (((k2_xboole_0 @ (k3_relat_1 @ sk_B) @ (k1_relat_1 @ sk_A))
% 26.49/26.74         = (k3_relat_1 @ sk_B))),
% 26.49/26.74      inference('demod', [status(thm)], ['38', '39'])).
% 26.49/26.74  thf('41', plain,
% 26.49/26.74      (![X20 : $i, X21 : $i]: (r1_tarski @ X20 @ (k2_xboole_0 @ X20 @ X21))),
% 26.49/26.74      inference('cnf', [status(esa)], [t7_xboole_1])).
% 26.49/26.74  thf('42', plain,
% 26.49/26.74      (![X36 : $i]:
% 26.49/26.74         (((k3_relat_1 @ X36)
% 26.49/26.74            = (k2_xboole_0 @ (k1_relat_1 @ X36) @ (k2_relat_1 @ X36)))
% 26.49/26.74          | ~ (v1_relat_1 @ X36))),
% 26.49/26.74      inference('cnf', [status(esa)], [d6_relat_1])).
% 26.49/26.74  thf('43', plain,
% 26.49/26.74      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 26.49/26.74      inference('sup-', [status(thm)], ['11', '12'])).
% 26.49/26.74  thf('44', plain,
% 26.49/26.74      (![X10 : $i, X11 : $i, X12 : $i]:
% 26.49/26.74         (~ (r1_tarski @ X10 @ X11)
% 26.49/26.74          | ~ (r1_tarski @ X11 @ X12)
% 26.49/26.74          | (r1_tarski @ X10 @ X12))),
% 26.49/26.74      inference('cnf', [status(esa)], [t1_xboole_1])).
% 26.49/26.74  thf('45', plain,
% 26.49/26.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 26.49/26.74         ((r1_tarski @ X0 @ X2) | ~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 26.49/26.74      inference('sup-', [status(thm)], ['43', '44'])).
% 26.49/26.74  thf('46', plain,
% 26.49/26.74      (![X0 : $i, X1 : $i]:
% 26.49/26.74         (~ (r1_tarski @ (k3_relat_1 @ X0) @ X1)
% 26.49/26.74          | ~ (v1_relat_1 @ X0)
% 26.49/26.74          | (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 26.49/26.74      inference('sup-', [status(thm)], ['42', '45'])).
% 26.49/26.74  thf('47', plain,
% 26.49/26.74      (![X0 : $i, X1 : $i]:
% 26.49/26.74         ((r1_tarski @ (k2_relat_1 @ X1) @ 
% 26.49/26.74           (k2_xboole_0 @ (k3_relat_1 @ X1) @ X0))
% 26.49/26.74          | ~ (v1_relat_1 @ X1))),
% 26.49/26.74      inference('sup-', [status(thm)], ['41', '46'])).
% 26.49/26.74  thf('48', plain,
% 26.49/26.74      (((r1_tarski @ (k2_relat_1 @ sk_B) @ (k3_relat_1 @ sk_B))
% 26.49/26.74        | ~ (v1_relat_1 @ sk_B))),
% 26.49/26.74      inference('sup+', [status(thm)], ['40', '47'])).
% 26.49/26.74  thf('49', plain, ((v1_relat_1 @ sk_B)),
% 26.49/26.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.49/26.74  thf('50', plain, ((r1_tarski @ (k2_relat_1 @ sk_B) @ (k3_relat_1 @ sk_B))),
% 26.49/26.74      inference('demod', [status(thm)], ['48', '49'])).
% 26.49/26.74  thf('51', plain, (((k2_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 26.49/26.74      inference('sup-', [status(thm)], ['10', '15'])).
% 26.49/26.74  thf(t26_relat_1, axiom,
% 26.49/26.74    (![A:$i]:
% 26.49/26.74     ( ( v1_relat_1 @ A ) =>
% 26.49/26.74       ( ![B:$i]:
% 26.49/26.74         ( ( v1_relat_1 @ B ) =>
% 26.49/26.74           ( ( k2_relat_1 @ ( k2_xboole_0 @ A @ B ) ) =
% 26.49/26.74             ( k2_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ))).
% 26.49/26.74  thf('52', plain,
% 26.49/26.74      (![X39 : $i, X40 : $i]:
% 26.49/26.74         (~ (v1_relat_1 @ X39)
% 26.49/26.74          | ((k2_relat_1 @ (k2_xboole_0 @ X40 @ X39))
% 26.49/26.74              = (k2_xboole_0 @ (k2_relat_1 @ X40) @ (k2_relat_1 @ X39)))
% 26.49/26.74          | ~ (v1_relat_1 @ X40))),
% 26.49/26.74      inference('cnf', [status(esa)], [t26_relat_1])).
% 26.49/26.74  thf('53', plain,
% 26.49/26.74      (![X7 : $i, X8 : $i, X9 : $i]:
% 26.49/26.74         ((r1_tarski @ X7 @ X8) | ~ (r1_tarski @ (k2_xboole_0 @ X7 @ X9) @ X8))),
% 26.49/26.74      inference('cnf', [status(esa)], [t11_xboole_1])).
% 26.49/26.74  thf('54', plain,
% 26.49/26.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 26.49/26.74         (~ (r1_tarski @ (k2_relat_1 @ (k2_xboole_0 @ X1 @ X0)) @ X2)
% 26.49/26.74          | ~ (v1_relat_1 @ X1)
% 26.49/26.74          | ~ (v1_relat_1 @ X0)
% 26.49/26.74          | (r1_tarski @ (k2_relat_1 @ X1) @ X2))),
% 26.49/26.74      inference('sup-', [status(thm)], ['52', '53'])).
% 26.49/26.74  thf('55', plain,
% 26.49/26.74      (![X0 : $i]:
% 26.49/26.74         (~ (r1_tarski @ (k2_relat_1 @ sk_B) @ X0)
% 26.49/26.74          | (r1_tarski @ (k2_relat_1 @ sk_A) @ X0)
% 26.49/26.74          | ~ (v1_relat_1 @ sk_B)
% 26.49/26.74          | ~ (v1_relat_1 @ sk_A))),
% 26.49/26.74      inference('sup-', [status(thm)], ['51', '54'])).
% 26.49/26.74  thf('56', plain, ((v1_relat_1 @ sk_B)),
% 26.49/26.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.49/26.74  thf('57', plain, ((v1_relat_1 @ sk_A)),
% 26.49/26.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.49/26.74  thf('58', plain,
% 26.49/26.74      (![X0 : $i]:
% 26.49/26.74         (~ (r1_tarski @ (k2_relat_1 @ sk_B) @ X0)
% 26.49/26.74          | (r1_tarski @ (k2_relat_1 @ sk_A) @ X0))),
% 26.49/26.74      inference('demod', [status(thm)], ['55', '56', '57'])).
% 26.49/26.74  thf('59', plain, ((r1_tarski @ (k2_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 26.49/26.74      inference('sup-', [status(thm)], ['50', '58'])).
% 26.49/26.74  thf('60', plain, ((r1_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 26.49/26.74      inference('demod', [status(thm)], ['24', '25'])).
% 26.49/26.74  thf('61', plain,
% 26.49/26.74      (![X22 : $i, X23 : $i, X24 : $i]:
% 26.49/26.74         (~ (r1_tarski @ X22 @ X23)
% 26.49/26.74          | ~ (r1_tarski @ X24 @ X23)
% 26.49/26.74          | (r1_tarski @ (k2_xboole_0 @ X22 @ X24) @ X23))),
% 26.49/26.74      inference('cnf', [status(esa)], [t8_xboole_1])).
% 26.49/26.74  thf('62', plain,
% 26.49/26.74      (![X0 : $i]:
% 26.49/26.74         ((r1_tarski @ (k2_xboole_0 @ (k1_relat_1 @ sk_A) @ X0) @ 
% 26.49/26.74           (k3_relat_1 @ sk_B))
% 26.49/26.74          | ~ (r1_tarski @ X0 @ (k3_relat_1 @ sk_B)))),
% 26.49/26.74      inference('sup-', [status(thm)], ['60', '61'])).
% 26.49/26.74  thf('63', plain,
% 26.49/26.74      ((r1_tarski @ 
% 26.49/26.74        (k2_xboole_0 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)) @ 
% 26.49/26.74        (k3_relat_1 @ sk_B))),
% 26.49/26.74      inference('sup-', [status(thm)], ['59', '62'])).
% 26.49/26.74  thf('64', plain,
% 26.49/26.74      (((r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))
% 26.49/26.74        | ~ (v1_relat_1 @ sk_A))),
% 26.49/26.74      inference('sup+', [status(thm)], ['1', '63'])).
% 26.49/26.74  thf('65', plain, ((v1_relat_1 @ sk_A)),
% 26.49/26.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.49/26.74  thf('66', plain, ((r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 26.49/26.74      inference('demod', [status(thm)], ['64', '65'])).
% 26.49/26.74  thf('67', plain, ($false), inference('demod', [status(thm)], ['0', '66'])).
% 26.49/26.74  
% 26.49/26.74  % SZS output end Refutation
% 26.49/26.74  
% 26.49/26.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
