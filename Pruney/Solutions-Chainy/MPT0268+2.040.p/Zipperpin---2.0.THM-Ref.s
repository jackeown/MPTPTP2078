%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.C8j9kFns6B

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:57 EST 2020

% Result     : Theorem 0.52s
% Output     : Refutation 0.52s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 491 expanded)
%              Number of leaves         :   21 ( 144 expanded)
%              Depth                    :   19
%              Number of atoms          : 1091 (4300 expanded)
%              Number of equality atoms :   87 ( 359 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('3',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k3_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['3'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('5',plain,(
    ! [X21: $i] :
      ( ( k4_xboole_0 @ X21 @ k1_xboole_0 )
      = X21 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(l33_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
    <=> ~ ( r2_hidden @ A @ B ) ) )).

thf('6',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( r2_hidden @ X40 @ X41 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X40 ) @ X41 )
       != ( k1_tarski @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[l33_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','8'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('10',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ X19 @ ( k3_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('12',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('13',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ X8 @ X6 )
      | ( X7
       != ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('14',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['7'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('19',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['7'])).

thf('20',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('21',plain,(
    ! [X16: $i,X18: $i] :
      ( ( X16 = X18 )
      | ~ ( r1_tarski @ X18 @ X16 )
      | ~ ( r1_tarski @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','22'])).

thf('24',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ X19 @ ( k3_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X21: $i] :
      ( ( k4_xboole_0 @ X21 @ k1_xboole_0 )
      = X21 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['11','27'])).

thf('29',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
   <= ( r2_hidden @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['29'])).

thf('31',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
   <= ( r2_hidden @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['29'])).

thf('32',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( r2_hidden @ X4 @ X6 )
      | ( r2_hidden @ X4 @ X7 )
      | ( X7
       != ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('33',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X4 @ ( k3_xboole_0 @ X5 @ X6 ) )
      | ~ ( r2_hidden @ X4 @ X6 )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ sk_B @ X0 )
        | ( r2_hidden @ sk_B @ ( k3_xboole_0 @ X0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['31','33'])).

thf('35',plain,
    ( ( r2_hidden @ sk_B @ ( k3_xboole_0 @ sk_A @ sk_A ) )
   <= ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['30','34'])).

thf('36',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
   <= ( r2_hidden @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['29'])).

thf('37',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('38',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('39',plain,(
    ! [X34: $i] :
      ( ( k2_tarski @ X34 @ X34 )
      = ( k1_tarski @ X34 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('40',plain,(
    ! [X40: $i,X42: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X40 ) @ X42 )
        = ( k1_tarski @ X40 ) )
      | ( r2_hidden @ X40 @ X42 ) ) ),
    inference(cnf,[status(esa)],[l33_zfmisc_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ X1 )
        = ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('42',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X14 @ X13 )
      | ~ ( r2_hidden @ X14 @ X12 )
      | ( X13
       != ( k4_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('43',plain,(
    ! [X11: $i,X12: $i,X14: $i] :
      ( ~ ( r2_hidden @ X14 @ X12 )
      | ~ ( r2_hidden @ X14 @ ( k4_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['41','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ ( k1_tarski @ X0 ) ) @ X2 )
      | ( r2_hidden @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['38','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['37','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('49',plain,(
    ! [X11: $i,X12: $i,X14: $i] :
      ( ~ ( r2_hidden @ X14 @ X12 )
      | ~ ( r2_hidden @ X14 @ ( k4_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('50',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_A )
        | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k1_tarski @ sk_B ) @ X0 )
        | ~ ( r2_hidden @ sk_B @ sk_A ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k1_tarski @ sk_B ) @ X0 )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
        = sk_A )
      & ( r2_hidden @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('54',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
        = sk_A )
      & ( r2_hidden @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( r2_hidden @ X40 @ X41 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X40 ) @ X41 )
       != ( k1_tarski @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[l33_zfmisc_1])).

thf('56',plain,
    ( ! [X0: $i] :
        ( ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
         != ( k1_tarski @ sk_B ) )
        | ~ ( r2_hidden @ sk_B @ X0 ) )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
        = sk_A )
      & ( r2_hidden @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
        = sk_A )
      & ( r2_hidden @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('58',plain,
    ( ! [X0: $i] :
        ( ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
         != k1_xboole_0 )
        | ~ ( r2_hidden @ sk_B @ X0 ) )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
        = sk_A )
      & ( r2_hidden @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( ( k4_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_A ) )
     != k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
        = sk_A )
      & ( r2_hidden @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','58'])).

thf('60',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
        = sk_A )
      & ( r2_hidden @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','59'])).

thf('61',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A )
    | ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','61'])).

thf('63',plain,(
    ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ X1 )
        = ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('65',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('66',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ X8 @ X5 )
      | ( X7
       != ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('67',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['65','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('70',plain,(
    ! [X11: $i,X12: $i,X14: $i] :
      ( ~ ( r2_hidden @ X14 @ X12 )
      | ~ ( r2_hidden @ X14 @ ( k4_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X2 )
      | ( r1_tarski @ ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['68','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X2 ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k3_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X6 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('75',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['7'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X1 )
      | ( X1
        = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','22'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['3'])).

thf('80',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k3_xboole_0 @ X5 @ X6 ) )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X6 )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X5 )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X0 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k3_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X6 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['82','84'])).

thf('86',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ X19 @ ( k3_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X14 @ X13 )
      | ( r2_hidden @ X14 @ X11 )
      | ( X13
       != ( k4_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('89',plain,(
    ! [X11: $i,X12: $i,X14: $i] :
      ( ( r2_hidden @ X14 @ X11 )
      | ~ ( r2_hidden @ X14 @ ( k4_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['87','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('92',plain,(
    ! [X11: $i,X12: $i,X14: $i] :
      ( ~ ( r2_hidden @ X14 @ X12 )
      | ~ ( r2_hidden @ X14 @ ( k4_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['90','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['78','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ X1 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['73','97'])).

thf('99',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ X19 @ ( k3_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['64','102'])).

thf('104',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference(split,[status(esa)],['29'])).

thf('105',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['29'])).

thf('106',plain,(
    ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
 != sk_A ),
    inference('sat_resolution*',[status(thm)],['2','61','105'])).

thf('107',plain,(
    ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
 != sk_A ),
    inference(simpl_trail,[status(thm)],['104','106'])).

thf('108',plain,
    ( ( sk_A != sk_A )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['103','107'])).

thf('109',plain,(
    r2_hidden @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,(
    $false ),
    inference(demod,[status(thm)],['63','109'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.C8j9kFns6B
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:59:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.52/0.68  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.52/0.68  % Solved by: fo/fo7.sh
% 0.52/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.52/0.68  % done 538 iterations in 0.232s
% 0.52/0.68  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.52/0.68  % SZS output start Refutation
% 0.52/0.68  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.52/0.68  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.52/0.68  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.52/0.68  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.52/0.68  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.52/0.68  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.52/0.68  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.52/0.68  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.52/0.68  thf(sk_B_type, type, sk_B: $i).
% 0.52/0.68  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.52/0.68  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.52/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.52/0.68  thf(t65_zfmisc_1, conjecture,
% 0.52/0.68    (![A:$i,B:$i]:
% 0.52/0.68     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.52/0.68       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.52/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.52/0.68    (~( ![A:$i,B:$i]:
% 0.52/0.68        ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.52/0.68          ( ~( r2_hidden @ B @ A ) ) ) )),
% 0.52/0.68    inference('cnf.neg', [status(esa)], [t65_zfmisc_1])).
% 0.52/0.68  thf('0', plain,
% 0.52/0.68      ((~ (r2_hidden @ sk_B @ sk_A)
% 0.52/0.68        | ((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 0.52/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.68  thf('1', plain,
% 0.52/0.68      ((~ (r2_hidden @ sk_B @ sk_A)) <= (~ ((r2_hidden @ sk_B @ sk_A)))),
% 0.52/0.68      inference('split', [status(esa)], ['0'])).
% 0.52/0.68  thf('2', plain,
% 0.52/0.68      (~ ((r2_hidden @ sk_B @ sk_A)) | 
% 0.52/0.68       (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 0.52/0.68      inference('split', [status(esa)], ['0'])).
% 0.52/0.68  thf(d4_xboole_0, axiom,
% 0.52/0.68    (![A:$i,B:$i,C:$i]:
% 0.52/0.68     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.52/0.68       ( ![D:$i]:
% 0.52/0.68         ( ( r2_hidden @ D @ C ) <=>
% 0.52/0.68           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.52/0.68  thf('3', plain,
% 0.52/0.68      (![X5 : $i, X6 : $i, X9 : $i]:
% 0.52/0.68         (((X9) = (k3_xboole_0 @ X5 @ X6))
% 0.52/0.68          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X5)
% 0.52/0.68          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 0.52/0.68      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.52/0.68  thf('4', plain,
% 0.52/0.68      (![X0 : $i, X1 : $i]:
% 0.52/0.68         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.52/0.68          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 0.52/0.68      inference('eq_fact', [status(thm)], ['3'])).
% 0.52/0.68  thf(t3_boole, axiom,
% 0.52/0.68    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.52/0.68  thf('5', plain, (![X21 : $i]: ((k4_xboole_0 @ X21 @ k1_xboole_0) = (X21))),
% 0.52/0.68      inference('cnf', [status(esa)], [t3_boole])).
% 0.52/0.68  thf(l33_zfmisc_1, axiom,
% 0.52/0.68    (![A:$i,B:$i]:
% 0.52/0.68     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 0.52/0.68       ( ~( r2_hidden @ A @ B ) ) ))).
% 0.52/0.68  thf('6', plain,
% 0.52/0.68      (![X40 : $i, X41 : $i]:
% 0.52/0.68         (~ (r2_hidden @ X40 @ X41)
% 0.52/0.68          | ((k4_xboole_0 @ (k1_tarski @ X40) @ X41) != (k1_tarski @ X40)))),
% 0.52/0.68      inference('cnf', [status(esa)], [l33_zfmisc_1])).
% 0.52/0.68  thf('7', plain,
% 0.52/0.68      (![X0 : $i]:
% 0.52/0.68         (((k1_tarski @ X0) != (k1_tarski @ X0))
% 0.52/0.68          | ~ (r2_hidden @ X0 @ k1_xboole_0))),
% 0.52/0.68      inference('sup-', [status(thm)], ['5', '6'])).
% 0.52/0.68  thf('8', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.52/0.68      inference('simplify', [status(thm)], ['7'])).
% 0.52/0.68  thf('9', plain,
% 0.52/0.68      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.52/0.68      inference('sup-', [status(thm)], ['4', '8'])).
% 0.52/0.68  thf(t100_xboole_1, axiom,
% 0.52/0.68    (![A:$i,B:$i]:
% 0.52/0.68     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.52/0.68  thf('10', plain,
% 0.52/0.68      (![X19 : $i, X20 : $i]:
% 0.52/0.68         ((k4_xboole_0 @ X19 @ X20)
% 0.52/0.68           = (k5_xboole_0 @ X19 @ (k3_xboole_0 @ X19 @ X20)))),
% 0.52/0.68      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.52/0.68  thf('11', plain,
% 0.52/0.68      (![X0 : $i]:
% 0.52/0.68         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.52/0.68           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.52/0.68      inference('sup+', [status(thm)], ['9', '10'])).
% 0.52/0.68  thf(d3_tarski, axiom,
% 0.52/0.68    (![A:$i,B:$i]:
% 0.52/0.68     ( ( r1_tarski @ A @ B ) <=>
% 0.52/0.68       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.52/0.68  thf('12', plain,
% 0.52/0.68      (![X1 : $i, X3 : $i]:
% 0.52/0.68         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.52/0.68      inference('cnf', [status(esa)], [d3_tarski])).
% 0.52/0.68  thf('13', plain,
% 0.52/0.68      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.52/0.68         (~ (r2_hidden @ X8 @ X7)
% 0.52/0.68          | (r2_hidden @ X8 @ X6)
% 0.52/0.68          | ((X7) != (k3_xboole_0 @ X5 @ X6)))),
% 0.52/0.68      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.52/0.68  thf('14', plain,
% 0.52/0.68      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.52/0.68         ((r2_hidden @ X8 @ X6) | ~ (r2_hidden @ X8 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.52/0.68      inference('simplify', [status(thm)], ['13'])).
% 0.52/0.68  thf('15', plain,
% 0.52/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.68         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.52/0.68          | (r2_hidden @ (sk_C @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X0))),
% 0.52/0.68      inference('sup-', [status(thm)], ['12', '14'])).
% 0.52/0.68  thf('16', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.52/0.68      inference('simplify', [status(thm)], ['7'])).
% 0.52/0.68  thf('17', plain,
% 0.52/0.68      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ k1_xboole_0) @ X1)),
% 0.52/0.68      inference('sup-', [status(thm)], ['15', '16'])).
% 0.52/0.68  thf('18', plain,
% 0.52/0.68      (![X1 : $i, X3 : $i]:
% 0.52/0.68         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.52/0.68      inference('cnf', [status(esa)], [d3_tarski])).
% 0.52/0.68  thf('19', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.52/0.68      inference('simplify', [status(thm)], ['7'])).
% 0.52/0.68  thf('20', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.52/0.68      inference('sup-', [status(thm)], ['18', '19'])).
% 0.52/0.68  thf(d10_xboole_0, axiom,
% 0.52/0.68    (![A:$i,B:$i]:
% 0.52/0.68     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.52/0.68  thf('21', plain,
% 0.52/0.68      (![X16 : $i, X18 : $i]:
% 0.52/0.68         (((X16) = (X18))
% 0.52/0.68          | ~ (r1_tarski @ X18 @ X16)
% 0.52/0.68          | ~ (r1_tarski @ X16 @ X18))),
% 0.52/0.68      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.52/0.68  thf('22', plain,
% 0.52/0.68      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.52/0.68      inference('sup-', [status(thm)], ['20', '21'])).
% 0.52/0.68  thf('23', plain,
% 0.52/0.68      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.52/0.68      inference('sup-', [status(thm)], ['17', '22'])).
% 0.52/0.68  thf('24', plain,
% 0.52/0.68      (![X19 : $i, X20 : $i]:
% 0.52/0.68         ((k4_xboole_0 @ X19 @ X20)
% 0.52/0.68           = (k5_xboole_0 @ X19 @ (k3_xboole_0 @ X19 @ X20)))),
% 0.52/0.68      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.52/0.68  thf('25', plain,
% 0.52/0.68      (![X0 : $i]:
% 0.52/0.68         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.52/0.68      inference('sup+', [status(thm)], ['23', '24'])).
% 0.52/0.68  thf('26', plain, (![X21 : $i]: ((k4_xboole_0 @ X21 @ k1_xboole_0) = (X21))),
% 0.52/0.68      inference('cnf', [status(esa)], [t3_boole])).
% 0.52/0.68  thf('27', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.52/0.68      inference('sup+', [status(thm)], ['25', '26'])).
% 0.52/0.68  thf('28', plain,
% 0.52/0.68      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.52/0.68      inference('demod', [status(thm)], ['11', '27'])).
% 0.52/0.68  thf('29', plain,
% 0.52/0.68      (((r2_hidden @ sk_B @ sk_A)
% 0.52/0.68        | ((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (sk_A)))),
% 0.52/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.68  thf('30', plain,
% 0.52/0.68      (((r2_hidden @ sk_B @ sk_A)) <= (((r2_hidden @ sk_B @ sk_A)))),
% 0.52/0.68      inference('split', [status(esa)], ['29'])).
% 0.52/0.68  thf('31', plain,
% 0.52/0.68      (((r2_hidden @ sk_B @ sk_A)) <= (((r2_hidden @ sk_B @ sk_A)))),
% 0.52/0.68      inference('split', [status(esa)], ['29'])).
% 0.52/0.68  thf('32', plain,
% 0.52/0.68      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.52/0.68         (~ (r2_hidden @ X4 @ X5)
% 0.52/0.68          | ~ (r2_hidden @ X4 @ X6)
% 0.52/0.68          | (r2_hidden @ X4 @ X7)
% 0.52/0.68          | ((X7) != (k3_xboole_0 @ X5 @ X6)))),
% 0.52/0.68      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.52/0.68  thf('33', plain,
% 0.52/0.68      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.52/0.68         ((r2_hidden @ X4 @ (k3_xboole_0 @ X5 @ X6))
% 0.52/0.68          | ~ (r2_hidden @ X4 @ X6)
% 0.52/0.68          | ~ (r2_hidden @ X4 @ X5))),
% 0.52/0.68      inference('simplify', [status(thm)], ['32'])).
% 0.52/0.68  thf('34', plain,
% 0.52/0.68      ((![X0 : $i]:
% 0.52/0.68          (~ (r2_hidden @ sk_B @ X0)
% 0.52/0.68           | (r2_hidden @ sk_B @ (k3_xboole_0 @ X0 @ sk_A))))
% 0.52/0.68         <= (((r2_hidden @ sk_B @ sk_A)))),
% 0.52/0.68      inference('sup-', [status(thm)], ['31', '33'])).
% 0.52/0.68  thf('35', plain,
% 0.52/0.68      (((r2_hidden @ sk_B @ (k3_xboole_0 @ sk_A @ sk_A)))
% 0.52/0.68         <= (((r2_hidden @ sk_B @ sk_A)))),
% 0.52/0.68      inference('sup-', [status(thm)], ['30', '34'])).
% 0.52/0.68  thf('36', plain,
% 0.52/0.68      (((r2_hidden @ sk_B @ sk_A)) <= (((r2_hidden @ sk_B @ sk_A)))),
% 0.52/0.68      inference('split', [status(esa)], ['29'])).
% 0.52/0.68  thf('37', plain,
% 0.52/0.68      (![X1 : $i, X3 : $i]:
% 0.52/0.68         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.52/0.68      inference('cnf', [status(esa)], [d3_tarski])).
% 0.52/0.68  thf('38', plain,
% 0.52/0.68      (![X1 : $i, X3 : $i]:
% 0.52/0.68         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.52/0.68      inference('cnf', [status(esa)], [d3_tarski])).
% 0.52/0.68  thf(t69_enumset1, axiom,
% 0.52/0.68    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.52/0.68  thf('39', plain,
% 0.52/0.68      (![X34 : $i]: ((k2_tarski @ X34 @ X34) = (k1_tarski @ X34))),
% 0.52/0.68      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.52/0.68  thf('40', plain,
% 0.52/0.68      (![X40 : $i, X42 : $i]:
% 0.52/0.68         (((k4_xboole_0 @ (k1_tarski @ X40) @ X42) = (k1_tarski @ X40))
% 0.52/0.68          | (r2_hidden @ X40 @ X42))),
% 0.52/0.68      inference('cnf', [status(esa)], [l33_zfmisc_1])).
% 0.52/0.68  thf('41', plain,
% 0.52/0.68      (![X0 : $i, X1 : $i]:
% 0.52/0.68         (((k4_xboole_0 @ (k2_tarski @ X0 @ X0) @ X1) = (k1_tarski @ X0))
% 0.52/0.68          | (r2_hidden @ X0 @ X1))),
% 0.52/0.68      inference('sup+', [status(thm)], ['39', '40'])).
% 0.52/0.68  thf(d5_xboole_0, axiom,
% 0.52/0.68    (![A:$i,B:$i,C:$i]:
% 0.52/0.68     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.52/0.68       ( ![D:$i]:
% 0.52/0.68         ( ( r2_hidden @ D @ C ) <=>
% 0.52/0.68           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.52/0.68  thf('42', plain,
% 0.52/0.68      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.52/0.68         (~ (r2_hidden @ X14 @ X13)
% 0.52/0.68          | ~ (r2_hidden @ X14 @ X12)
% 0.52/0.68          | ((X13) != (k4_xboole_0 @ X11 @ X12)))),
% 0.52/0.68      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.52/0.68  thf('43', plain,
% 0.52/0.68      (![X11 : $i, X12 : $i, X14 : $i]:
% 0.52/0.68         (~ (r2_hidden @ X14 @ X12)
% 0.52/0.68          | ~ (r2_hidden @ X14 @ (k4_xboole_0 @ X11 @ X12)))),
% 0.52/0.68      inference('simplify', [status(thm)], ['42'])).
% 0.52/0.68  thf('44', plain,
% 0.52/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.68         (~ (r2_hidden @ X2 @ (k1_tarski @ X0))
% 0.52/0.68          | (r2_hidden @ X0 @ X1)
% 0.52/0.68          | ~ (r2_hidden @ X2 @ X1))),
% 0.52/0.68      inference('sup-', [status(thm)], ['41', '43'])).
% 0.52/0.68  thf('45', plain,
% 0.52/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.68         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.52/0.68          | ~ (r2_hidden @ (sk_C @ X1 @ (k1_tarski @ X0)) @ X2)
% 0.52/0.68          | (r2_hidden @ X0 @ X2))),
% 0.52/0.68      inference('sup-', [status(thm)], ['38', '44'])).
% 0.52/0.68  thf('46', plain,
% 0.52/0.68      (![X0 : $i, X1 : $i]:
% 0.52/0.68         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.52/0.68          | (r2_hidden @ X0 @ (k1_tarski @ X0))
% 0.52/0.68          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 0.52/0.68      inference('sup-', [status(thm)], ['37', '45'])).
% 0.52/0.68  thf('47', plain,
% 0.52/0.68      (![X0 : $i, X1 : $i]:
% 0.52/0.68         ((r2_hidden @ X0 @ (k1_tarski @ X0))
% 0.52/0.68          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 0.52/0.68      inference('simplify', [status(thm)], ['46'])).
% 0.52/0.68  thf('48', plain,
% 0.52/0.68      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))
% 0.52/0.68         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.52/0.68      inference('split', [status(esa)], ['0'])).
% 0.52/0.68  thf('49', plain,
% 0.52/0.68      (![X11 : $i, X12 : $i, X14 : $i]:
% 0.52/0.68         (~ (r2_hidden @ X14 @ X12)
% 0.52/0.68          | ~ (r2_hidden @ X14 @ (k4_xboole_0 @ X11 @ X12)))),
% 0.52/0.68      inference('simplify', [status(thm)], ['42'])).
% 0.52/0.68  thf('50', plain,
% 0.52/0.68      ((![X0 : $i]:
% 0.52/0.68          (~ (r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_B))))
% 0.52/0.68         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.52/0.68      inference('sup-', [status(thm)], ['48', '49'])).
% 0.52/0.68  thf('51', plain,
% 0.52/0.68      ((![X0 : $i]:
% 0.52/0.68          ((r1_tarski @ (k1_tarski @ sk_B) @ X0) | ~ (r2_hidden @ sk_B @ sk_A)))
% 0.52/0.68         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.52/0.68      inference('sup-', [status(thm)], ['47', '50'])).
% 0.52/0.68  thf('52', plain,
% 0.52/0.68      ((![X0 : $i]: (r1_tarski @ (k1_tarski @ sk_B) @ X0))
% 0.52/0.68         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))) & 
% 0.52/0.68             ((r2_hidden @ sk_B @ sk_A)))),
% 0.52/0.68      inference('sup-', [status(thm)], ['36', '51'])).
% 0.52/0.68  thf('53', plain,
% 0.52/0.68      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.52/0.68      inference('sup-', [status(thm)], ['20', '21'])).
% 0.52/0.68  thf('54', plain,
% 0.52/0.68      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.52/0.68         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))) & 
% 0.52/0.68             ((r2_hidden @ sk_B @ sk_A)))),
% 0.52/0.68      inference('sup-', [status(thm)], ['52', '53'])).
% 0.52/0.68  thf('55', plain,
% 0.52/0.68      (![X40 : $i, X41 : $i]:
% 0.52/0.68         (~ (r2_hidden @ X40 @ X41)
% 0.52/0.68          | ((k4_xboole_0 @ (k1_tarski @ X40) @ X41) != (k1_tarski @ X40)))),
% 0.52/0.68      inference('cnf', [status(esa)], [l33_zfmisc_1])).
% 0.52/0.68  thf('56', plain,
% 0.52/0.68      ((![X0 : $i]:
% 0.52/0.68          (((k4_xboole_0 @ k1_xboole_0 @ X0) != (k1_tarski @ sk_B))
% 0.52/0.68           | ~ (r2_hidden @ sk_B @ X0)))
% 0.52/0.68         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))) & 
% 0.52/0.68             ((r2_hidden @ sk_B @ sk_A)))),
% 0.52/0.68      inference('sup-', [status(thm)], ['54', '55'])).
% 0.52/0.68  thf('57', plain,
% 0.52/0.68      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.52/0.68         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))) & 
% 0.52/0.68             ((r2_hidden @ sk_B @ sk_A)))),
% 0.52/0.68      inference('sup-', [status(thm)], ['52', '53'])).
% 0.52/0.68  thf('58', plain,
% 0.52/0.68      ((![X0 : $i]:
% 0.52/0.68          (((k4_xboole_0 @ k1_xboole_0 @ X0) != (k1_xboole_0))
% 0.52/0.68           | ~ (r2_hidden @ sk_B @ X0)))
% 0.52/0.68         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))) & 
% 0.52/0.68             ((r2_hidden @ sk_B @ sk_A)))),
% 0.52/0.68      inference('demod', [status(thm)], ['56', '57'])).
% 0.52/0.68  thf('59', plain,
% 0.52/0.68      ((((k4_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_A))
% 0.52/0.68          != (k1_xboole_0)))
% 0.52/0.68         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))) & 
% 0.52/0.68             ((r2_hidden @ sk_B @ sk_A)))),
% 0.52/0.68      inference('sup-', [status(thm)], ['35', '58'])).
% 0.52/0.68  thf('60', plain,
% 0.52/0.68      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.52/0.68         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))) & 
% 0.52/0.68             ((r2_hidden @ sk_B @ sk_A)))),
% 0.52/0.68      inference('sup-', [status(thm)], ['28', '59'])).
% 0.52/0.68  thf('61', plain,
% 0.52/0.68      (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))) | 
% 0.52/0.68       ~ ((r2_hidden @ sk_B @ sk_A))),
% 0.52/0.68      inference('simplify', [status(thm)], ['60'])).
% 0.52/0.68  thf('62', plain, (~ ((r2_hidden @ sk_B @ sk_A))),
% 0.52/0.68      inference('sat_resolution*', [status(thm)], ['2', '61'])).
% 0.52/0.68  thf('63', plain, (~ (r2_hidden @ sk_B @ sk_A)),
% 0.52/0.68      inference('simpl_trail', [status(thm)], ['1', '62'])).
% 0.52/0.68  thf('64', plain,
% 0.52/0.68      (![X0 : $i, X1 : $i]:
% 0.52/0.68         (((k4_xboole_0 @ (k2_tarski @ X0 @ X0) @ X1) = (k1_tarski @ X0))
% 0.52/0.68          | (r2_hidden @ X0 @ X1))),
% 0.52/0.68      inference('sup+', [status(thm)], ['39', '40'])).
% 0.52/0.68  thf('65', plain,
% 0.52/0.68      (![X1 : $i, X3 : $i]:
% 0.52/0.68         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.52/0.68      inference('cnf', [status(esa)], [d3_tarski])).
% 0.52/0.68  thf('66', plain,
% 0.52/0.68      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.52/0.68         (~ (r2_hidden @ X8 @ X7)
% 0.52/0.68          | (r2_hidden @ X8 @ X5)
% 0.52/0.68          | ((X7) != (k3_xboole_0 @ X5 @ X6)))),
% 0.52/0.68      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.52/0.68  thf('67', plain,
% 0.52/0.68      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.52/0.68         ((r2_hidden @ X8 @ X5) | ~ (r2_hidden @ X8 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.52/0.68      inference('simplify', [status(thm)], ['66'])).
% 0.52/0.68  thf('68', plain,
% 0.52/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.68         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.52/0.68          | (r2_hidden @ (sk_C @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X1))),
% 0.52/0.68      inference('sup-', [status(thm)], ['65', '67'])).
% 0.52/0.68  thf('69', plain,
% 0.52/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.68         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.52/0.68          | (r2_hidden @ (sk_C @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X0))),
% 0.52/0.68      inference('sup-', [status(thm)], ['12', '14'])).
% 0.52/0.68  thf('70', plain,
% 0.52/0.68      (![X11 : $i, X12 : $i, X14 : $i]:
% 0.52/0.68         (~ (r2_hidden @ X14 @ X12)
% 0.52/0.68          | ~ (r2_hidden @ X14 @ (k4_xboole_0 @ X11 @ X12)))),
% 0.52/0.68      inference('simplify', [status(thm)], ['42'])).
% 0.52/0.68  thf('71', plain,
% 0.52/0.68      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.52/0.68         ((r1_tarski @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X3)
% 0.52/0.68          | ~ (r2_hidden @ 
% 0.52/0.68               (sk_C @ X3 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))) @ X0))),
% 0.52/0.68      inference('sup-', [status(thm)], ['69', '70'])).
% 0.52/0.68  thf('72', plain,
% 0.52/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.68         ((r1_tarski @ (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) @ X2)
% 0.52/0.68          | (r1_tarski @ (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) @ X2))),
% 0.52/0.68      inference('sup-', [status(thm)], ['68', '71'])).
% 0.52/0.68  thf('73', plain,
% 0.52/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.68         (r1_tarski @ (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) @ X2)),
% 0.52/0.68      inference('simplify', [status(thm)], ['72'])).
% 0.52/0.68  thf('74', plain,
% 0.52/0.68      (![X5 : $i, X6 : $i, X9 : $i]:
% 0.52/0.68         (((X9) = (k3_xboole_0 @ X5 @ X6))
% 0.52/0.68          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X6)
% 0.52/0.68          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 0.52/0.68      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.52/0.68  thf('75', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.52/0.68      inference('simplify', [status(thm)], ['7'])).
% 0.52/0.68  thf('76', plain,
% 0.52/0.68      (![X0 : $i, X1 : $i]:
% 0.52/0.68         ((r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X1)
% 0.52/0.68          | ((X1) = (k3_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.52/0.68      inference('sup-', [status(thm)], ['74', '75'])).
% 0.52/0.68  thf('77', plain,
% 0.52/0.68      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.52/0.68      inference('sup-', [status(thm)], ['17', '22'])).
% 0.52/0.68  thf('78', plain,
% 0.52/0.68      (![X0 : $i, X1 : $i]:
% 0.52/0.68         ((r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X1)
% 0.52/0.68          | ((X1) = (k1_xboole_0)))),
% 0.52/0.68      inference('demod', [status(thm)], ['76', '77'])).
% 0.52/0.68  thf('79', plain,
% 0.52/0.68      (![X0 : $i, X1 : $i]:
% 0.52/0.68         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.52/0.68          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 0.52/0.68      inference('eq_fact', [status(thm)], ['3'])).
% 0.52/0.68  thf('80', plain,
% 0.52/0.68      (![X5 : $i, X6 : $i, X9 : $i]:
% 0.52/0.68         (((X9) = (k3_xboole_0 @ X5 @ X6))
% 0.52/0.68          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X6)
% 0.52/0.68          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X5)
% 0.52/0.68          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 0.52/0.68      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.52/0.68  thf('81', plain,
% 0.52/0.68      (![X0 : $i]:
% 0.52/0.68         (((X0) = (k3_xboole_0 @ X0 @ X0))
% 0.52/0.68          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X0) @ X0)
% 0.52/0.68          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X0) @ X0)
% 0.52/0.68          | ((X0) = (k3_xboole_0 @ X0 @ X0)))),
% 0.52/0.68      inference('sup-', [status(thm)], ['79', '80'])).
% 0.52/0.68  thf('82', plain,
% 0.52/0.68      (![X0 : $i]:
% 0.52/0.68         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X0) @ X0)
% 0.52/0.68          | ((X0) = (k3_xboole_0 @ X0 @ X0)))),
% 0.52/0.68      inference('simplify', [status(thm)], ['81'])).
% 0.52/0.68  thf('83', plain,
% 0.52/0.68      (![X5 : $i, X6 : $i, X9 : $i]:
% 0.52/0.68         (((X9) = (k3_xboole_0 @ X5 @ X6))
% 0.52/0.68          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X6)
% 0.52/0.68          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 0.52/0.68      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.52/0.68  thf('84', plain,
% 0.52/0.68      (![X0 : $i, X1 : $i]:
% 0.52/0.68         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.52/0.68          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.52/0.68      inference('eq_fact', [status(thm)], ['83'])).
% 0.52/0.68  thf('85', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.52/0.68      inference('clc', [status(thm)], ['82', '84'])).
% 0.52/0.68  thf('86', plain,
% 0.52/0.68      (![X19 : $i, X20 : $i]:
% 0.52/0.68         ((k4_xboole_0 @ X19 @ X20)
% 0.52/0.68           = (k5_xboole_0 @ X19 @ (k3_xboole_0 @ X19 @ X20)))),
% 0.52/0.68      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.52/0.68  thf('87', plain,
% 0.52/0.68      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.52/0.68      inference('sup+', [status(thm)], ['85', '86'])).
% 0.52/0.68  thf('88', plain,
% 0.52/0.68      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.52/0.68         (~ (r2_hidden @ X14 @ X13)
% 0.52/0.68          | (r2_hidden @ X14 @ X11)
% 0.52/0.68          | ((X13) != (k4_xboole_0 @ X11 @ X12)))),
% 0.52/0.68      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.52/0.68  thf('89', plain,
% 0.52/0.68      (![X11 : $i, X12 : $i, X14 : $i]:
% 0.52/0.68         ((r2_hidden @ X14 @ X11)
% 0.52/0.68          | ~ (r2_hidden @ X14 @ (k4_xboole_0 @ X11 @ X12)))),
% 0.52/0.68      inference('simplify', [status(thm)], ['88'])).
% 0.52/0.68  thf('90', plain,
% 0.52/0.68      (![X0 : $i, X1 : $i]:
% 0.52/0.68         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0)) | (r2_hidden @ X1 @ X0))),
% 0.52/0.68      inference('sup-', [status(thm)], ['87', '89'])).
% 0.52/0.68  thf('91', plain,
% 0.52/0.68      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.52/0.68      inference('sup+', [status(thm)], ['85', '86'])).
% 0.52/0.68  thf('92', plain,
% 0.52/0.68      (![X11 : $i, X12 : $i, X14 : $i]:
% 0.52/0.68         (~ (r2_hidden @ X14 @ X12)
% 0.52/0.68          | ~ (r2_hidden @ X14 @ (k4_xboole_0 @ X11 @ X12)))),
% 0.52/0.68      inference('simplify', [status(thm)], ['42'])).
% 0.52/0.68  thf('93', plain,
% 0.52/0.68      (![X0 : $i, X1 : $i]:
% 0.52/0.68         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 0.52/0.68          | ~ (r2_hidden @ X1 @ X0))),
% 0.52/0.68      inference('sup-', [status(thm)], ['91', '92'])).
% 0.52/0.68  thf('94', plain,
% 0.52/0.68      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))),
% 0.52/0.68      inference('clc', [status(thm)], ['90', '93'])).
% 0.52/0.68  thf('95', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.52/0.68      inference('sup-', [status(thm)], ['78', '94'])).
% 0.52/0.68  thf('96', plain,
% 0.52/0.68      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.52/0.68      inference('sup-', [status(thm)], ['20', '21'])).
% 0.52/0.68  thf('97', plain,
% 0.52/0.68      (![X0 : $i, X1 : $i]:
% 0.52/0.68         (~ (r1_tarski @ X1 @ (k5_xboole_0 @ X0 @ X0)) | ((X1) = (k1_xboole_0)))),
% 0.52/0.68      inference('sup-', [status(thm)], ['95', '96'])).
% 0.52/0.68  thf('98', plain,
% 0.52/0.68      (![X1 : $i, X2 : $i]:
% 0.52/0.68         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ X1)) = (k1_xboole_0))),
% 0.52/0.68      inference('sup-', [status(thm)], ['73', '97'])).
% 0.52/0.68  thf('99', plain,
% 0.52/0.68      (![X19 : $i, X20 : $i]:
% 0.52/0.68         ((k4_xboole_0 @ X19 @ X20)
% 0.52/0.68           = (k5_xboole_0 @ X19 @ (k3_xboole_0 @ X19 @ X20)))),
% 0.52/0.68      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.52/0.68  thf('100', plain,
% 0.52/0.68      (![X0 : $i, X1 : $i]:
% 0.52/0.68         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 0.52/0.68           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.52/0.68      inference('sup+', [status(thm)], ['98', '99'])).
% 0.52/0.68  thf('101', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.52/0.68      inference('sup+', [status(thm)], ['25', '26'])).
% 0.52/0.68  thf('102', plain,
% 0.52/0.68      (![X0 : $i, X1 : $i]:
% 0.52/0.68         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 0.52/0.68      inference('demod', [status(thm)], ['100', '101'])).
% 0.52/0.68  thf('103', plain,
% 0.52/0.68      (![X0 : $i, X1 : $i]:
% 0.52/0.68         (((k4_xboole_0 @ X1 @ (k1_tarski @ X0)) = (X1))
% 0.52/0.68          | (r2_hidden @ X0 @ X1))),
% 0.52/0.68      inference('sup+', [status(thm)], ['64', '102'])).
% 0.52/0.68  thf('104', plain,
% 0.52/0.68      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (sk_A)))
% 0.52/0.68         <= (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.52/0.68      inference('split', [status(esa)], ['29'])).
% 0.52/0.68  thf('105', plain,
% 0.52/0.68      (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))) | 
% 0.52/0.68       ((r2_hidden @ sk_B @ sk_A))),
% 0.52/0.68      inference('split', [status(esa)], ['29'])).
% 0.52/0.68  thf('106', plain, (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 0.52/0.68      inference('sat_resolution*', [status(thm)], ['2', '61', '105'])).
% 0.52/0.68  thf('107', plain, (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (sk_A))),
% 0.52/0.68      inference('simpl_trail', [status(thm)], ['104', '106'])).
% 0.52/0.68  thf('108', plain, ((((sk_A) != (sk_A)) | (r2_hidden @ sk_B @ sk_A))),
% 0.52/0.69      inference('sup-', [status(thm)], ['103', '107'])).
% 0.52/0.69  thf('109', plain, ((r2_hidden @ sk_B @ sk_A)),
% 0.52/0.69      inference('simplify', [status(thm)], ['108'])).
% 0.52/0.69  thf('110', plain, ($false), inference('demod', [status(thm)], ['63', '109'])).
% 0.52/0.69  
% 0.52/0.69  % SZS output end Refutation
% 0.52/0.69  
% 0.52/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
