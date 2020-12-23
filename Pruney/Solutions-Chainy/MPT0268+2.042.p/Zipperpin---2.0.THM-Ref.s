%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TUdAEIyPkf

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:57 EST 2020

% Result     : Theorem 0.75s
% Output     : Refutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 157 expanded)
%              Number of leaves         :   26 (  55 expanded)
%              Depth                    :   14
%              Number of atoms          :  714 (1210 expanded)
%              Number of equality atoms :   68 ( 123 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t65_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
          = A )
      <=> ~ ( r2_hidden @ B @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t65_zfmisc_1])).

thf('0',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
   <= ( r2_hidden @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k1_enumset1 @ X30 @ X30 @ X31 )
      = ( k2_tarski @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('4',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( zip_tseitin_0 @ X22 @ X23 @ X24 @ X25 )
      | ( r2_hidden @ X22 @ X26 )
      | ( X26
       != ( k1_enumset1 @ X25 @ X24 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('5',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( r2_hidden @ X22 @ ( k1_enumset1 @ X25 @ X24 @ X23 ) )
      | ( zip_tseitin_0 @ X22 @ X23 @ X24 @ X25 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( X18 != X17 )
      | ~ ( zip_tseitin_0 @ X18 @ X19 @ X20 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('8',plain,(
    ! [X17: $i,X19: $i,X20: $i] :
      ~ ( zip_tseitin_0 @ X17 @ X19 @ X20 @ X17 ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('10',plain,(
    ! [X29: $i] :
      ( ( k2_tarski @ X29 @ X29 )
      = ( k1_tarski @ X29 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('11',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ( X6 != X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('12',plain,(
    ! [X7: $i] :
      ( r1_tarski @ X7 @ X7 ) ),
    inference(simplify,[status(thm)],['11'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('13',plain,(
    ! [X9: $i,X11: $i] :
      ( ( ( k4_xboole_0 @ X9 @ X11 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('15',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('17',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('18',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X7: $i] :
      ( r1_tarski @ X7 @ X7 ) ),
    inference(simplify,[status(thm)],['11'])).

thf(l2_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( r2_hidden @ C @ A )
        | ( r1_tarski @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) ) ) )).

thf('20',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( r1_tarski @ X35 @ X36 )
      | ( r2_hidden @ X37 @ X35 )
      | ( r1_tarski @ X35 @ ( k4_xboole_0 @ X36 @ ( k1_tarski @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[l2_zfmisc_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X9: $i,X11: $i] :
      ( ( ( k4_xboole_0 @ X9 @ X11 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('26',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('27',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('29',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('30',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['28','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k5_xboole_0 @ X1 @ k1_xboole_0 ) )
      | ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['25','31'])).

thf('33',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('34',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('37',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['32','41'])).

thf('43',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('44',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('45',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['43','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(clc,[status(thm)],['42','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','49'])).

thf('51',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(split,[status(esa)],['51'])).

thf('53',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('54',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_A )
        | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['50','54'])).

thf('56',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference('sup-',[status(thm)],['2','55'])).

thf('57',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(split,[status(esa)],['51'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('59',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('64',plain,
    ( ( ( sk_A != sk_A )
      | ( r2_hidden @ sk_B @ sk_A ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['51'])).

thf('67',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','56','57','67'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TUdAEIyPkf
% 0.16/0.36  % Computer   : n016.cluster.edu
% 0.16/0.36  % Model      : x86_64 x86_64
% 0.16/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.36  % Memory     : 8042.1875MB
% 0.16/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 12:41:49 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.37  % Python version: Python 3.6.8
% 0.16/0.37  % Running in FO mode
% 0.75/0.96  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.75/0.96  % Solved by: fo/fo7.sh
% 0.75/0.96  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.75/0.96  % done 989 iterations in 0.513s
% 0.75/0.96  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.75/0.96  % SZS output start Refutation
% 0.75/0.96  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.75/0.96  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.75/0.96  thf(sk_A_type, type, sk_A: $i).
% 0.75/0.96  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.75/0.96  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.75/0.96  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.75/0.96  thf(sk_B_type, type, sk_B: $i).
% 0.75/0.96  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.75/0.96  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.75/0.96  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.75/0.96  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.75/0.96  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.75/0.96  thf(t65_zfmisc_1, conjecture,
% 0.75/0.96    (![A:$i,B:$i]:
% 0.75/0.96     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.75/0.96       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.75/0.96  thf(zf_stmt_0, negated_conjecture,
% 0.75/0.96    (~( ![A:$i,B:$i]:
% 0.75/0.96        ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.75/0.96          ( ~( r2_hidden @ B @ A ) ) ) )),
% 0.75/0.96    inference('cnf.neg', [status(esa)], [t65_zfmisc_1])).
% 0.75/0.96  thf('0', plain,
% 0.75/0.96      (((r2_hidden @ sk_B @ sk_A)
% 0.75/0.96        | ((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (sk_A)))),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf('1', plain,
% 0.75/0.96      (((r2_hidden @ sk_B @ sk_A)) | 
% 0.75/0.96       ~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 0.75/0.96      inference('split', [status(esa)], ['0'])).
% 0.75/0.96  thf('2', plain,
% 0.75/0.96      (((r2_hidden @ sk_B @ sk_A)) <= (((r2_hidden @ sk_B @ sk_A)))),
% 0.75/0.96      inference('split', [status(esa)], ['0'])).
% 0.75/0.96  thf(t70_enumset1, axiom,
% 0.75/0.96    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.75/0.96  thf('3', plain,
% 0.75/0.96      (![X30 : $i, X31 : $i]:
% 0.75/0.96         ((k1_enumset1 @ X30 @ X30 @ X31) = (k2_tarski @ X30 @ X31))),
% 0.75/0.96      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.75/0.96  thf(d1_enumset1, axiom,
% 0.75/0.96    (![A:$i,B:$i,C:$i,D:$i]:
% 0.75/0.96     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.75/0.96       ( ![E:$i]:
% 0.75/0.96         ( ( r2_hidden @ E @ D ) <=>
% 0.75/0.96           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.75/0.96  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.75/0.96  thf(zf_stmt_2, axiom,
% 0.75/0.96    (![E:$i,C:$i,B:$i,A:$i]:
% 0.75/0.96     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.75/0.96       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.75/0.96  thf(zf_stmt_3, axiom,
% 0.75/0.96    (![A:$i,B:$i,C:$i,D:$i]:
% 0.75/0.96     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.75/0.96       ( ![E:$i]:
% 0.75/0.96         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.75/0.96  thf('4', plain,
% 0.75/0.96      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.75/0.96         ((zip_tseitin_0 @ X22 @ X23 @ X24 @ X25)
% 0.75/0.96          | (r2_hidden @ X22 @ X26)
% 0.75/0.96          | ((X26) != (k1_enumset1 @ X25 @ X24 @ X23)))),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.75/0.96  thf('5', plain,
% 0.75/0.96      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.75/0.96         ((r2_hidden @ X22 @ (k1_enumset1 @ X25 @ X24 @ X23))
% 0.75/0.96          | (zip_tseitin_0 @ X22 @ X23 @ X24 @ X25))),
% 0.75/0.96      inference('simplify', [status(thm)], ['4'])).
% 0.75/0.96  thf('6', plain,
% 0.75/0.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.96         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.75/0.96          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.75/0.96      inference('sup+', [status(thm)], ['3', '5'])).
% 0.75/0.96  thf('7', plain,
% 0.75/0.96      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.75/0.96         (((X18) != (X17)) | ~ (zip_tseitin_0 @ X18 @ X19 @ X20 @ X17))),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.75/0.96  thf('8', plain,
% 0.75/0.96      (![X17 : $i, X19 : $i, X20 : $i]:
% 0.75/0.96         ~ (zip_tseitin_0 @ X17 @ X19 @ X20 @ X17)),
% 0.75/0.96      inference('simplify', [status(thm)], ['7'])).
% 0.75/0.96  thf('9', plain,
% 0.75/0.96      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.75/0.96      inference('sup-', [status(thm)], ['6', '8'])).
% 0.75/0.96  thf(t69_enumset1, axiom,
% 0.75/0.96    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.75/0.96  thf('10', plain,
% 0.75/0.96      (![X29 : $i]: ((k2_tarski @ X29 @ X29) = (k1_tarski @ X29))),
% 0.75/0.96      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.75/0.96  thf(d10_xboole_0, axiom,
% 0.75/0.96    (![A:$i,B:$i]:
% 0.75/0.96     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.75/0.96  thf('11', plain,
% 0.75/0.96      (![X6 : $i, X7 : $i]: ((r1_tarski @ X6 @ X7) | ((X6) != (X7)))),
% 0.75/0.96      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.75/0.96  thf('12', plain, (![X7 : $i]: (r1_tarski @ X7 @ X7)),
% 0.75/0.96      inference('simplify', [status(thm)], ['11'])).
% 0.75/0.96  thf(l32_xboole_1, axiom,
% 0.75/0.96    (![A:$i,B:$i]:
% 0.75/0.96     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.75/0.96  thf('13', plain,
% 0.75/0.96      (![X9 : $i, X11 : $i]:
% 0.75/0.96         (((k4_xboole_0 @ X9 @ X11) = (k1_xboole_0)) | ~ (r1_tarski @ X9 @ X11))),
% 0.75/0.96      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.75/0.96  thf('14', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.75/0.96      inference('sup-', [status(thm)], ['12', '13'])).
% 0.75/0.96  thf(t48_xboole_1, axiom,
% 0.75/0.96    (![A:$i,B:$i]:
% 0.75/0.96     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.75/0.96  thf('15', plain,
% 0.75/0.96      (![X15 : $i, X16 : $i]:
% 0.75/0.96         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.75/0.96           = (k3_xboole_0 @ X15 @ X16))),
% 0.75/0.96      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.75/0.96  thf('16', plain,
% 0.75/0.96      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.75/0.96      inference('sup+', [status(thm)], ['14', '15'])).
% 0.75/0.96  thf(t3_boole, axiom,
% 0.75/0.96    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.75/0.96  thf('17', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.75/0.96      inference('cnf', [status(esa)], [t3_boole])).
% 0.75/0.96  thf('18', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.75/0.96      inference('demod', [status(thm)], ['16', '17'])).
% 0.75/0.96  thf('19', plain, (![X7 : $i]: (r1_tarski @ X7 @ X7)),
% 0.75/0.96      inference('simplify', [status(thm)], ['11'])).
% 0.75/0.96  thf(l2_zfmisc_1, axiom,
% 0.75/0.96    (![A:$i,B:$i,C:$i]:
% 0.75/0.96     ( ( r1_tarski @ A @ B ) =>
% 0.75/0.96       ( ( r2_hidden @ C @ A ) | 
% 0.75/0.96         ( r1_tarski @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) ) ))).
% 0.75/0.96  thf('20', plain,
% 0.75/0.96      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.75/0.96         (~ (r1_tarski @ X35 @ X36)
% 0.75/0.96          | (r2_hidden @ X37 @ X35)
% 0.75/0.96          | (r1_tarski @ X35 @ (k4_xboole_0 @ X36 @ (k1_tarski @ X37))))),
% 0.75/0.96      inference('cnf', [status(esa)], [l2_zfmisc_1])).
% 0.75/0.96  thf('21', plain,
% 0.75/0.96      (![X0 : $i, X1 : $i]:
% 0.75/0.96         ((r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ (k1_tarski @ X1)))
% 0.75/0.96          | (r2_hidden @ X1 @ X0))),
% 0.75/0.96      inference('sup-', [status(thm)], ['19', '20'])).
% 0.75/0.96  thf('22', plain,
% 0.75/0.96      (![X9 : $i, X11 : $i]:
% 0.75/0.96         (((k4_xboole_0 @ X9 @ X11) = (k1_xboole_0)) | ~ (r1_tarski @ X9 @ X11))),
% 0.75/0.96      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.75/0.96  thf('23', plain,
% 0.75/0.96      (![X0 : $i, X1 : $i]:
% 0.75/0.96         ((r2_hidden @ X0 @ X1)
% 0.75/0.96          | ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 0.75/0.96              = (k1_xboole_0)))),
% 0.75/0.96      inference('sup-', [status(thm)], ['21', '22'])).
% 0.75/0.96  thf('24', plain,
% 0.75/0.96      (![X15 : $i, X16 : $i]:
% 0.75/0.96         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.75/0.96           = (k3_xboole_0 @ X15 @ X16))),
% 0.75/0.96      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.75/0.96  thf('25', plain,
% 0.75/0.96      (![X0 : $i, X1 : $i]:
% 0.75/0.96         ((r2_hidden @ X0 @ X1)
% 0.75/0.96          | ((k3_xboole_0 @ X1 @ (k1_tarski @ X0)) = (k1_xboole_0)))),
% 0.75/0.96      inference('demod', [status(thm)], ['23', '24'])).
% 0.75/0.96  thf(t100_xboole_1, axiom,
% 0.75/0.96    (![A:$i,B:$i]:
% 0.75/0.96     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.75/0.96  thf('26', plain,
% 0.75/0.96      (![X12 : $i, X13 : $i]:
% 0.75/0.96         ((k4_xboole_0 @ X12 @ X13)
% 0.75/0.96           = (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)))),
% 0.75/0.96      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.75/0.96  thf('27', plain,
% 0.75/0.96      (![X15 : $i, X16 : $i]:
% 0.75/0.96         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.75/0.96           = (k3_xboole_0 @ X15 @ X16))),
% 0.75/0.96      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.75/0.96  thf('28', plain,
% 0.75/0.96      (![X0 : $i, X1 : $i]:
% 0.75/0.96         ((k4_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.75/0.96           = (k3_xboole_0 @ X1 @ X0))),
% 0.75/0.96      inference('sup+', [status(thm)], ['26', '27'])).
% 0.75/0.96  thf(d5_xboole_0, axiom,
% 0.75/0.96    (![A:$i,B:$i,C:$i]:
% 0.75/0.96     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.75/0.96       ( ![D:$i]:
% 0.75/0.96         ( ( r2_hidden @ D @ C ) <=>
% 0.75/0.96           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.75/0.96  thf('29', plain,
% 0.75/0.96      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.75/0.96         (~ (r2_hidden @ X4 @ X3)
% 0.75/0.96          | ~ (r2_hidden @ X4 @ X2)
% 0.75/0.96          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.75/0.96      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.75/0.96  thf('30', plain,
% 0.75/0.96      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.75/0.96         (~ (r2_hidden @ X4 @ X2)
% 0.75/0.96          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.75/0.96      inference('simplify', [status(thm)], ['29'])).
% 0.75/0.96  thf('31', plain,
% 0.75/0.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.96         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.75/0.96          | ~ (r2_hidden @ X2 @ (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.75/0.96      inference('sup-', [status(thm)], ['28', '30'])).
% 0.75/0.96  thf('32', plain,
% 0.75/0.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.96         (~ (r2_hidden @ X2 @ (k5_xboole_0 @ X1 @ k1_xboole_0))
% 0.75/0.96          | (r2_hidden @ X0 @ X1)
% 0.75/0.96          | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ (k1_tarski @ X0))))),
% 0.75/0.96      inference('sup-', [status(thm)], ['25', '31'])).
% 0.75/0.96  thf('33', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.75/0.96      inference('cnf', [status(esa)], [t3_boole])).
% 0.75/0.96  thf('34', plain,
% 0.75/0.96      (![X15 : $i, X16 : $i]:
% 0.75/0.96         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.75/0.96           = (k3_xboole_0 @ X15 @ X16))),
% 0.75/0.96      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.75/0.96  thf('35', plain,
% 0.75/0.96      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.75/0.96      inference('sup+', [status(thm)], ['33', '34'])).
% 0.75/0.96  thf('36', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.75/0.96      inference('sup-', [status(thm)], ['12', '13'])).
% 0.75/0.96  thf('37', plain,
% 0.75/0.96      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.75/0.96      inference('demod', [status(thm)], ['35', '36'])).
% 0.75/0.96  thf('38', plain,
% 0.75/0.96      (![X12 : $i, X13 : $i]:
% 0.75/0.96         ((k4_xboole_0 @ X12 @ X13)
% 0.75/0.96           = (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)))),
% 0.75/0.96      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.75/0.96  thf('39', plain,
% 0.75/0.96      (![X0 : $i]:
% 0.75/0.96         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.75/0.96      inference('sup+', [status(thm)], ['37', '38'])).
% 0.75/0.96  thf('40', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.75/0.96      inference('cnf', [status(esa)], [t3_boole])).
% 0.75/0.96  thf('41', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.75/0.96      inference('sup+', [status(thm)], ['39', '40'])).
% 0.75/0.96  thf('42', plain,
% 0.75/0.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.96         (~ (r2_hidden @ X2 @ X1)
% 0.75/0.96          | (r2_hidden @ X0 @ X1)
% 0.75/0.96          | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ (k1_tarski @ X0))))),
% 0.75/0.96      inference('demod', [status(thm)], ['32', '41'])).
% 0.75/0.96  thf('43', plain,
% 0.75/0.96      (![X15 : $i, X16 : $i]:
% 0.75/0.96         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.75/0.96           = (k3_xboole_0 @ X15 @ X16))),
% 0.75/0.96      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.75/0.96  thf('44', plain,
% 0.75/0.96      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.75/0.96         (~ (r2_hidden @ X4 @ X3)
% 0.75/0.96          | (r2_hidden @ X4 @ X1)
% 0.75/0.96          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.75/0.96      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.75/0.96  thf('45', plain,
% 0.75/0.96      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.75/0.96         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.75/0.96      inference('simplify', [status(thm)], ['44'])).
% 0.75/0.96  thf('46', plain,
% 0.75/0.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.96         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r2_hidden @ X2 @ X1))),
% 0.75/0.96      inference('sup-', [status(thm)], ['43', '45'])).
% 0.75/0.96  thf('47', plain,
% 0.75/0.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.96         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 0.75/0.96          | (r2_hidden @ X0 @ X1))),
% 0.75/0.96      inference('clc', [status(thm)], ['42', '46'])).
% 0.75/0.96  thf('48', plain,
% 0.75/0.96      (![X0 : $i, X1 : $i]:
% 0.75/0.96         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.75/0.96          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.75/0.96      inference('sup-', [status(thm)], ['18', '47'])).
% 0.75/0.96  thf('49', plain,
% 0.75/0.96      (![X0 : $i, X1 : $i]:
% 0.75/0.96         (~ (r2_hidden @ X1 @ (k2_tarski @ X0 @ X0))
% 0.75/0.96          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.75/0.96      inference('sup-', [status(thm)], ['10', '48'])).
% 0.75/0.96  thf('50', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.75/0.96      inference('sup-', [status(thm)], ['9', '49'])).
% 0.75/0.96  thf('51', plain,
% 0.75/0.96      ((~ (r2_hidden @ sk_B @ sk_A)
% 0.75/0.96        | ((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf('52', plain,
% 0.75/0.96      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))
% 0.75/0.96         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.75/0.96      inference('split', [status(esa)], ['51'])).
% 0.75/0.96  thf('53', plain,
% 0.75/0.96      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.75/0.96         (~ (r2_hidden @ X4 @ X2)
% 0.75/0.96          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.75/0.96      inference('simplify', [status(thm)], ['29'])).
% 0.75/0.96  thf('54', plain,
% 0.75/0.96      ((![X0 : $i]:
% 0.75/0.96          (~ (r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_B))))
% 0.75/0.96         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.75/0.96      inference('sup-', [status(thm)], ['52', '53'])).
% 0.75/0.96  thf('55', plain,
% 0.75/0.96      ((~ (r2_hidden @ sk_B @ sk_A))
% 0.75/0.96         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.75/0.96      inference('sup-', [status(thm)], ['50', '54'])).
% 0.75/0.96  thf('56', plain,
% 0.75/0.96      (~ ((r2_hidden @ sk_B @ sk_A)) | 
% 0.75/0.96       ~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 0.75/0.96      inference('sup-', [status(thm)], ['2', '55'])).
% 0.75/0.96  thf('57', plain,
% 0.75/0.96      (~ ((r2_hidden @ sk_B @ sk_A)) | 
% 0.75/0.96       (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 0.75/0.96      inference('split', [status(esa)], ['51'])).
% 0.75/0.96  thf('58', plain,
% 0.75/0.96      (![X0 : $i, X1 : $i]:
% 0.75/0.96         ((r2_hidden @ X0 @ X1)
% 0.75/0.96          | ((k3_xboole_0 @ X1 @ (k1_tarski @ X0)) = (k1_xboole_0)))),
% 0.75/0.96      inference('demod', [status(thm)], ['23', '24'])).
% 0.75/0.96  thf('59', plain,
% 0.75/0.96      (![X12 : $i, X13 : $i]:
% 0.75/0.96         ((k4_xboole_0 @ X12 @ X13)
% 0.75/0.96           = (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)))),
% 0.75/0.96      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.75/0.96  thf('60', plain,
% 0.75/0.96      (![X0 : $i, X1 : $i]:
% 0.75/0.96         (((k4_xboole_0 @ X1 @ (k1_tarski @ X0))
% 0.75/0.96            = (k5_xboole_0 @ X1 @ k1_xboole_0))
% 0.75/0.96          | (r2_hidden @ X0 @ X1))),
% 0.75/0.96      inference('sup+', [status(thm)], ['58', '59'])).
% 0.75/0.96  thf('61', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.75/0.96      inference('sup+', [status(thm)], ['39', '40'])).
% 0.75/0.96  thf('62', plain,
% 0.75/0.96      (![X0 : $i, X1 : $i]:
% 0.75/0.96         (((k4_xboole_0 @ X1 @ (k1_tarski @ X0)) = (X1))
% 0.75/0.96          | (r2_hidden @ X0 @ X1))),
% 0.75/0.96      inference('demod', [status(thm)], ['60', '61'])).
% 0.75/0.96  thf('63', plain,
% 0.75/0.96      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (sk_A)))
% 0.75/0.96         <= (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.75/0.96      inference('split', [status(esa)], ['0'])).
% 0.75/0.96  thf('64', plain,
% 0.75/0.96      (((((sk_A) != (sk_A)) | (r2_hidden @ sk_B @ sk_A)))
% 0.75/0.96         <= (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.75/0.96      inference('sup-', [status(thm)], ['62', '63'])).
% 0.75/0.96  thf('65', plain,
% 0.75/0.96      (((r2_hidden @ sk_B @ sk_A))
% 0.75/0.96         <= (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.75/0.96      inference('simplify', [status(thm)], ['64'])).
% 0.75/0.96  thf('66', plain,
% 0.75/0.96      ((~ (r2_hidden @ sk_B @ sk_A)) <= (~ ((r2_hidden @ sk_B @ sk_A)))),
% 0.75/0.96      inference('split', [status(esa)], ['51'])).
% 0.75/0.96  thf('67', plain,
% 0.75/0.96      (((r2_hidden @ sk_B @ sk_A)) | 
% 0.75/0.96       (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 0.75/0.96      inference('sup-', [status(thm)], ['65', '66'])).
% 0.75/0.96  thf('68', plain, ($false),
% 0.75/0.96      inference('sat_resolution*', [status(thm)], ['1', '56', '57', '67'])).
% 0.75/0.96  
% 0.75/0.96  % SZS output end Refutation
% 0.75/0.96  
% 0.75/0.97  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
