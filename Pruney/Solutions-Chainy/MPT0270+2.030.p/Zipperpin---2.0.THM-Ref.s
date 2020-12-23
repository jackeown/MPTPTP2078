%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9a0ydM3gCB

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:16 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 217 expanded)
%              Number of leaves         :   20 (  67 expanded)
%              Depth                    :   17
%              Number of atoms          :  844 (1944 expanded)
%              Number of equality atoms :   68 ( 152 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(t67_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
    <=> ~ ( r2_hidden @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
          = ( k1_tarski @ A ) )
      <=> ~ ( r2_hidden @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t67_zfmisc_1])).

thf('0',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B_1 )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B_1 )
   <= ~ ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B_1 )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( r2_hidden @ sk_A @ sk_B_1 )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r2_hidden @ sk_A @ sk_B_1 )
   <= ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,
    ( ( r2_hidden @ sk_A @ sk_B_1 )
   <= ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['3'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('6',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r2_hidden @ X2 @ X4 )
      | ( r2_hidden @ X2 @ X5 )
      | ( X5
       != ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('7',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X2 @ ( k3_xboole_0 @ X3 @ X4 ) )
      | ~ ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ sk_A @ X0 )
        | ( r2_hidden @ sk_A @ ( k3_xboole_0 @ X0 @ sk_B_1 ) ) )
   <= ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,
    ( ( r2_hidden @ sk_A @ ( k3_xboole_0 @ sk_B_1 @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['4','8'])).

thf('10',plain,
    ( ( r2_hidden @ sk_A @ sk_B_1 )
   <= ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['3'])).

thf('11',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('12',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X20 @ X21 ) @ X21 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('13',plain,
    ( ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('14',plain,(
    ! [X45: $i,X46: $i] :
      ( ( ( k4_xboole_0 @ X45 @ ( k1_tarski @ X46 ) )
        = X45 )
      | ( r2_hidden @ X46 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('15',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X20 @ X21 ) @ X21 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('17',plain,(
    ! [X16: $i] :
      ( ( X16 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X16 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('18',plain,(
    ! [X16: $i] :
      ( ( X16 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X16 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('19',plain,(
    ! [X12: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X14 @ X12 )
      | ~ ( r2_hidden @ X14 @ X15 )
      | ~ ( r1_xboole_0 @ X12 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r2_hidden @ ( sk_B @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['16','22'])).

thf('24',plain,(
    ! [X12: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X14 @ X12 )
      | ~ ( r2_hidden @ X14 @ X15 )
      | ~ ( r1_xboole_0 @ X12 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( ~ ( r2_hidden @ sk_A @ sk_B_1 )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','25'])).

thf('27',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['10','26'])).

thf('28',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( r2_hidden @ X44 @ X45 )
      | ( ( k4_xboole_0 @ X45 @ ( k1_tarski @ X44 ) )
       != X45 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('29',plain,
    ( ! [X0: $i] :
        ( ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
         != X0 )
        | ~ ( r2_hidden @ sk_A @ X0 ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('30',plain,(
    ! [X19: $i] :
      ( ( k4_xboole_0 @ X19 @ k1_xboole_0 )
      = X19 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('31',plain,
    ( ! [X0: $i] :
        ( ( X0 != X0 )
        | ~ ( r2_hidden @ sk_A @ X0 ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ sk_A @ X0 )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
     != ( k1_tarski @ sk_A ) )
    | ~ ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['9','32'])).

thf('34',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['2','33'])).

thf('35',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['1','34'])).

thf('36',plain,(
    ! [X45: $i,X46: $i] :
      ( ( ( k4_xboole_0 @ X45 @ ( k1_tarski @ X46 ) )
        = X45 )
      | ( r2_hidden @ X46 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('37',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X20 @ X21 ) @ X21 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('38',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_xboole_0 @ X12 @ X13 )
      | ( r2_hidden @ ( sk_C @ X13 @ X12 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('39',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_xboole_0 @ X12 @ X13 )
      | ( r2_hidden @ ( sk_C @ X13 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('40',plain,(
    ! [X12: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X14 @ X12 )
      | ~ ( r2_hidden @ X14 @ X15 )
      | ~ ( r1_xboole_0 @ X12 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','43'])).

thf('45',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_xboole_0 @ X12 @ X13 )
      | ( r2_hidden @ ( sk_C @ X13 @ X12 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('46',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('47',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r1_xboole_0 @ X2 @ X0 )
      | ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X2 @ X0 )
      | ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['44','51'])).

thf('53',plain,(
    ! [X16: $i] :
      ( ( X16 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X16 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('55',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r2_hidden @ ( sk_B @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      | ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      | ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['52','60'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('62',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X19: $i] :
      ( ( k4_xboole_0 @ X19 @ k1_xboole_0 )
      = X19 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('65',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X20 @ X21 ) @ X21 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X16: $i] :
      ( ( X16 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X16 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('68',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r2_hidden @ ( sk_B @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['66','72'])).

thf('74',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X19: $i] :
      ( ( k4_xboole_0 @ X19 @ k1_xboole_0 )
      = X19 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['63','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = ( k1_tarski @ X1 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['36','78'])).

thf('80',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
     != ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('81',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
     != ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['3'])).

thf('82',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','33','81'])).

thf('83',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['80','82'])).

thf('84',plain,
    ( ( ( k1_tarski @ sk_A )
     != ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['79','83'])).

thf('85',plain,(
    r2_hidden @ sk_A @ sk_B_1 ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    $false ),
    inference(demod,[status(thm)],['35','85'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9a0ydM3gCB
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:51:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.45/0.67  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.67  % Solved by: fo/fo7.sh
% 0.45/0.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.67  % done 475 iterations in 0.214s
% 0.45/0.67  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.67  % SZS output start Refutation
% 0.45/0.67  thf(sk_B_type, type, sk_B: $i > $i).
% 0.45/0.67  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.67  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.45/0.67  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.45/0.67  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.45/0.67  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.45/0.67  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.67  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.45/0.67  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.67  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.45/0.67  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.45/0.67  thf(t67_zfmisc_1, conjecture,
% 0.45/0.67    (![A:$i,B:$i]:
% 0.45/0.67     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 0.45/0.67       ( ~( r2_hidden @ A @ B ) ) ))).
% 0.45/0.67  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.67    (~( ![A:$i,B:$i]:
% 0.45/0.67        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 0.45/0.67          ( ~( r2_hidden @ A @ B ) ) ) )),
% 0.45/0.67    inference('cnf.neg', [status(esa)], [t67_zfmisc_1])).
% 0.45/0.67  thf('0', plain,
% 0.45/0.67      ((~ (r2_hidden @ sk_A @ sk_B_1)
% 0.45/0.67        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A)))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('1', plain,
% 0.45/0.67      ((~ (r2_hidden @ sk_A @ sk_B_1)) <= (~ ((r2_hidden @ sk_A @ sk_B_1)))),
% 0.45/0.67      inference('split', [status(esa)], ['0'])).
% 0.45/0.67  thf('2', plain,
% 0.45/0.67      (~ ((r2_hidden @ sk_A @ sk_B_1)) | 
% 0.45/0.67       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A)))),
% 0.45/0.67      inference('split', [status(esa)], ['0'])).
% 0.45/0.67  thf('3', plain,
% 0.45/0.67      (((r2_hidden @ sk_A @ sk_B_1)
% 0.45/0.67        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) != (k1_tarski @ sk_A)))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('4', plain,
% 0.45/0.67      (((r2_hidden @ sk_A @ sk_B_1)) <= (((r2_hidden @ sk_A @ sk_B_1)))),
% 0.45/0.67      inference('split', [status(esa)], ['3'])).
% 0.45/0.67  thf('5', plain,
% 0.45/0.67      (((r2_hidden @ sk_A @ sk_B_1)) <= (((r2_hidden @ sk_A @ sk_B_1)))),
% 0.45/0.67      inference('split', [status(esa)], ['3'])).
% 0.45/0.67  thf(d4_xboole_0, axiom,
% 0.45/0.67    (![A:$i,B:$i,C:$i]:
% 0.45/0.67     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.45/0.67       ( ![D:$i]:
% 0.45/0.67         ( ( r2_hidden @ D @ C ) <=>
% 0.45/0.67           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.45/0.67  thf('6', plain,
% 0.45/0.67      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.45/0.67         (~ (r2_hidden @ X2 @ X3)
% 0.45/0.67          | ~ (r2_hidden @ X2 @ X4)
% 0.45/0.67          | (r2_hidden @ X2 @ X5)
% 0.45/0.67          | ((X5) != (k3_xboole_0 @ X3 @ X4)))),
% 0.45/0.67      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.45/0.67  thf('7', plain,
% 0.45/0.67      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.45/0.67         ((r2_hidden @ X2 @ (k3_xboole_0 @ X3 @ X4))
% 0.45/0.67          | ~ (r2_hidden @ X2 @ X4)
% 0.45/0.67          | ~ (r2_hidden @ X2 @ X3))),
% 0.45/0.67      inference('simplify', [status(thm)], ['6'])).
% 0.45/0.67  thf('8', plain,
% 0.45/0.67      ((![X0 : $i]:
% 0.45/0.67          (~ (r2_hidden @ sk_A @ X0)
% 0.45/0.67           | (r2_hidden @ sk_A @ (k3_xboole_0 @ X0 @ sk_B_1))))
% 0.45/0.67         <= (((r2_hidden @ sk_A @ sk_B_1)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['5', '7'])).
% 0.45/0.67  thf('9', plain,
% 0.45/0.67      (((r2_hidden @ sk_A @ (k3_xboole_0 @ sk_B_1 @ sk_B_1)))
% 0.45/0.67         <= (((r2_hidden @ sk_A @ sk_B_1)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['4', '8'])).
% 0.45/0.67  thf('10', plain,
% 0.45/0.67      (((r2_hidden @ sk_A @ sk_B_1)) <= (((r2_hidden @ sk_A @ sk_B_1)))),
% 0.45/0.67      inference('split', [status(esa)], ['3'])).
% 0.45/0.67  thf('11', plain,
% 0.45/0.67      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A)))
% 0.45/0.67         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 0.45/0.67      inference('split', [status(esa)], ['0'])).
% 0.45/0.67  thf(t79_xboole_1, axiom,
% 0.45/0.67    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.45/0.67  thf('12', plain,
% 0.45/0.67      (![X20 : $i, X21 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X20 @ X21) @ X21)),
% 0.45/0.67      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.45/0.67  thf('13', plain,
% 0.45/0.67      (((r1_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1))
% 0.45/0.67         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 0.45/0.67      inference('sup+', [status(thm)], ['11', '12'])).
% 0.45/0.67  thf(t65_zfmisc_1, axiom,
% 0.45/0.67    (![A:$i,B:$i]:
% 0.45/0.67     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.45/0.67       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.45/0.67  thf('14', plain,
% 0.45/0.67      (![X45 : $i, X46 : $i]:
% 0.45/0.67         (((k4_xboole_0 @ X45 @ (k1_tarski @ X46)) = (X45))
% 0.45/0.67          | (r2_hidden @ X46 @ X45))),
% 0.45/0.67      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.45/0.67  thf('15', plain,
% 0.45/0.67      (![X20 : $i, X21 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X20 @ X21) @ X21)),
% 0.45/0.67      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.45/0.67  thf('16', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         ((r1_xboole_0 @ X0 @ (k1_tarski @ X1)) | (r2_hidden @ X1 @ X0))),
% 0.45/0.67      inference('sup+', [status(thm)], ['14', '15'])).
% 0.45/0.67  thf(t7_xboole_0, axiom,
% 0.45/0.67    (![A:$i]:
% 0.45/0.67     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.45/0.67          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.45/0.67  thf('17', plain,
% 0.45/0.67      (![X16 : $i]:
% 0.45/0.67         (((X16) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X16) @ X16))),
% 0.45/0.67      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.45/0.67  thf('18', plain,
% 0.45/0.67      (![X16 : $i]:
% 0.45/0.67         (((X16) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X16) @ X16))),
% 0.45/0.67      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.45/0.67  thf(t3_xboole_0, axiom,
% 0.45/0.67    (![A:$i,B:$i]:
% 0.45/0.67     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.45/0.67            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.45/0.67       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.45/0.67            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.45/0.67  thf('19', plain,
% 0.45/0.67      (![X12 : $i, X14 : $i, X15 : $i]:
% 0.45/0.67         (~ (r2_hidden @ X14 @ X12)
% 0.45/0.67          | ~ (r2_hidden @ X14 @ X15)
% 0.45/0.67          | ~ (r1_xboole_0 @ X12 @ X15))),
% 0.45/0.67      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.45/0.67  thf('20', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         (((X0) = (k1_xboole_0))
% 0.45/0.67          | ~ (r1_xboole_0 @ X0 @ X1)
% 0.45/0.67          | ~ (r2_hidden @ (sk_B @ X0) @ X1))),
% 0.45/0.67      inference('sup-', [status(thm)], ['18', '19'])).
% 0.45/0.67  thf('21', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         (((X0) = (k1_xboole_0))
% 0.45/0.67          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.45/0.67          | ((X0) = (k1_xboole_0)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['17', '20'])).
% 0.45/0.67  thf('22', plain,
% 0.45/0.67      (![X0 : $i]: (~ (r1_xboole_0 @ X0 @ X0) | ((X0) = (k1_xboole_0)))),
% 0.45/0.67      inference('simplify', [status(thm)], ['21'])).
% 0.45/0.67  thf('23', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         ((r2_hidden @ X0 @ (k1_tarski @ X0))
% 0.45/0.67          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['16', '22'])).
% 0.45/0.67  thf('24', plain,
% 0.45/0.67      (![X12 : $i, X14 : $i, X15 : $i]:
% 0.45/0.67         (~ (r2_hidden @ X14 @ X12)
% 0.45/0.67          | ~ (r2_hidden @ X14 @ X15)
% 0.45/0.67          | ~ (r1_xboole_0 @ X12 @ X15))),
% 0.45/0.67      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.45/0.67  thf('25', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.45/0.67          | ~ (r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 0.45/0.67          | ~ (r2_hidden @ X0 @ X1))),
% 0.45/0.67      inference('sup-', [status(thm)], ['23', '24'])).
% 0.45/0.67  thf('26', plain,
% 0.45/0.67      (((~ (r2_hidden @ sk_A @ sk_B_1) | ((k1_tarski @ sk_A) = (k1_xboole_0))))
% 0.45/0.67         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 0.45/0.67      inference('sup-', [status(thm)], ['13', '25'])).
% 0.45/0.67  thf('27', plain,
% 0.45/0.67      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 0.45/0.67         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))) & 
% 0.45/0.67             ((r2_hidden @ sk_A @ sk_B_1)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['10', '26'])).
% 0.45/0.67  thf('28', plain,
% 0.45/0.67      (![X44 : $i, X45 : $i]:
% 0.45/0.67         (~ (r2_hidden @ X44 @ X45)
% 0.45/0.67          | ((k4_xboole_0 @ X45 @ (k1_tarski @ X44)) != (X45)))),
% 0.45/0.67      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.45/0.67  thf('29', plain,
% 0.45/0.67      ((![X0 : $i]:
% 0.45/0.67          (((k4_xboole_0 @ X0 @ k1_xboole_0) != (X0))
% 0.45/0.67           | ~ (r2_hidden @ sk_A @ X0)))
% 0.45/0.67         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))) & 
% 0.45/0.67             ((r2_hidden @ sk_A @ sk_B_1)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['27', '28'])).
% 0.45/0.67  thf(t3_boole, axiom,
% 0.45/0.67    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.45/0.67  thf('30', plain, (![X19 : $i]: ((k4_xboole_0 @ X19 @ k1_xboole_0) = (X19))),
% 0.45/0.67      inference('cnf', [status(esa)], [t3_boole])).
% 0.45/0.67  thf('31', plain,
% 0.45/0.67      ((![X0 : $i]: (((X0) != (X0)) | ~ (r2_hidden @ sk_A @ X0)))
% 0.45/0.67         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))) & 
% 0.45/0.67             ((r2_hidden @ sk_A @ sk_B_1)))),
% 0.45/0.67      inference('demod', [status(thm)], ['29', '30'])).
% 0.45/0.67  thf('32', plain,
% 0.45/0.67      ((![X0 : $i]: ~ (r2_hidden @ sk_A @ X0))
% 0.45/0.67         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))) & 
% 0.45/0.67             ((r2_hidden @ sk_A @ sk_B_1)))),
% 0.45/0.67      inference('simplify', [status(thm)], ['31'])).
% 0.45/0.67  thf('33', plain,
% 0.45/0.67      (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))) | 
% 0.45/0.67       ~ ((r2_hidden @ sk_A @ sk_B_1))),
% 0.45/0.67      inference('sup-', [status(thm)], ['9', '32'])).
% 0.45/0.67  thf('34', plain, (~ ((r2_hidden @ sk_A @ sk_B_1))),
% 0.45/0.67      inference('sat_resolution*', [status(thm)], ['2', '33'])).
% 0.45/0.67  thf('35', plain, (~ (r2_hidden @ sk_A @ sk_B_1)),
% 0.45/0.67      inference('simpl_trail', [status(thm)], ['1', '34'])).
% 0.45/0.67  thf('36', plain,
% 0.45/0.67      (![X45 : $i, X46 : $i]:
% 0.45/0.67         (((k4_xboole_0 @ X45 @ (k1_tarski @ X46)) = (X45))
% 0.45/0.67          | (r2_hidden @ X46 @ X45))),
% 0.45/0.67      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.45/0.67  thf('37', plain,
% 0.45/0.67      (![X20 : $i, X21 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X20 @ X21) @ X21)),
% 0.45/0.67      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.45/0.67  thf('38', plain,
% 0.45/0.67      (![X12 : $i, X13 : $i]:
% 0.45/0.67         ((r1_xboole_0 @ X12 @ X13) | (r2_hidden @ (sk_C @ X13 @ X12) @ X12))),
% 0.45/0.67      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.45/0.67  thf('39', plain,
% 0.45/0.67      (![X12 : $i, X13 : $i]:
% 0.45/0.67         ((r1_xboole_0 @ X12 @ X13) | (r2_hidden @ (sk_C @ X13 @ X12) @ X13))),
% 0.45/0.67      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.45/0.67  thf('40', plain,
% 0.45/0.67      (![X12 : $i, X14 : $i, X15 : $i]:
% 0.45/0.67         (~ (r2_hidden @ X14 @ X12)
% 0.45/0.67          | ~ (r2_hidden @ X14 @ X15)
% 0.45/0.67          | ~ (r1_xboole_0 @ X12 @ X15))),
% 0.45/0.67      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.45/0.67  thf('41', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.67         ((r1_xboole_0 @ X1 @ X0)
% 0.45/0.67          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.45/0.67          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.45/0.67      inference('sup-', [status(thm)], ['39', '40'])).
% 0.45/0.67  thf('42', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         ((r1_xboole_0 @ X0 @ X1)
% 0.45/0.67          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.45/0.67          | (r1_xboole_0 @ X0 @ X1))),
% 0.45/0.67      inference('sup-', [status(thm)], ['38', '41'])).
% 0.45/0.67  thf('43', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.45/0.67      inference('simplify', [status(thm)], ['42'])).
% 0.45/0.67  thf('44', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.45/0.67      inference('sup-', [status(thm)], ['37', '43'])).
% 0.45/0.67  thf('45', plain,
% 0.45/0.67      (![X12 : $i, X13 : $i]:
% 0.45/0.67         ((r1_xboole_0 @ X12 @ X13) | (r2_hidden @ (sk_C @ X13 @ X12) @ X12))),
% 0.45/0.67      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.45/0.67  thf('46', plain,
% 0.45/0.67      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.45/0.67         (~ (r2_hidden @ X6 @ X5)
% 0.45/0.67          | (r2_hidden @ X6 @ X4)
% 0.45/0.67          | ((X5) != (k3_xboole_0 @ X3 @ X4)))),
% 0.45/0.67      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.45/0.67  thf('47', plain,
% 0.45/0.67      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.45/0.67         ((r2_hidden @ X6 @ X4) | ~ (r2_hidden @ X6 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.45/0.67      inference('simplify', [status(thm)], ['46'])).
% 0.45/0.67  thf('48', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.67         ((r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.45/0.67          | (r2_hidden @ (sk_C @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X0))),
% 0.45/0.67      inference('sup-', [status(thm)], ['45', '47'])).
% 0.45/0.67  thf('49', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.67         ((r1_xboole_0 @ X1 @ X0)
% 0.45/0.67          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.45/0.67          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.45/0.67      inference('sup-', [status(thm)], ['39', '40'])).
% 0.45/0.67  thf('50', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.67         ((r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.45/0.67          | ~ (r1_xboole_0 @ X2 @ X0)
% 0.45/0.67          | (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 0.45/0.67      inference('sup-', [status(thm)], ['48', '49'])).
% 0.45/0.67  thf('51', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.67         (~ (r1_xboole_0 @ X2 @ X0)
% 0.45/0.67          | (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 0.45/0.67      inference('simplify', [status(thm)], ['50'])).
% 0.45/0.67  thf('52', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.67         (r1_xboole_0 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X0)),
% 0.45/0.67      inference('sup-', [status(thm)], ['44', '51'])).
% 0.45/0.67  thf('53', plain,
% 0.45/0.67      (![X16 : $i]:
% 0.45/0.67         (((X16) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X16) @ X16))),
% 0.45/0.67      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.45/0.67  thf(commutativity_k3_xboole_0, axiom,
% 0.45/0.67    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.45/0.67  thf('54', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.45/0.67      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.45/0.67  thf('55', plain,
% 0.45/0.67      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.45/0.67         ((r2_hidden @ X6 @ X4) | ~ (r2_hidden @ X6 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.45/0.67      inference('simplify', [status(thm)], ['46'])).
% 0.45/0.67  thf('56', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.67         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r2_hidden @ X2 @ X1))),
% 0.45/0.67      inference('sup-', [status(thm)], ['54', '55'])).
% 0.45/0.67  thf('57', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.45/0.67          | (r2_hidden @ (sk_B @ (k3_xboole_0 @ X1 @ X0)) @ X1))),
% 0.45/0.67      inference('sup-', [status(thm)], ['53', '56'])).
% 0.45/0.67  thf('58', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         (((X0) = (k1_xboole_0))
% 0.45/0.67          | ~ (r1_xboole_0 @ X0 @ X1)
% 0.45/0.67          | ~ (r2_hidden @ (sk_B @ X0) @ X1))),
% 0.45/0.67      inference('sup-', [status(thm)], ['18', '19'])).
% 0.45/0.67  thf('59', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0))
% 0.45/0.67          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 0.45/0.67          | ((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['57', '58'])).
% 0.45/0.67  thf('60', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         (~ (r1_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 0.45/0.67          | ((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)))),
% 0.45/0.67      inference('simplify', [status(thm)], ['59'])).
% 0.45/0.67  thf('61', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.45/0.67      inference('sup-', [status(thm)], ['52', '60'])).
% 0.45/0.67  thf(t100_xboole_1, axiom,
% 0.45/0.67    (![A:$i,B:$i]:
% 0.45/0.67     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.45/0.67  thf('62', plain,
% 0.45/0.67      (![X17 : $i, X18 : $i]:
% 0.45/0.67         ((k4_xboole_0 @ X17 @ X18)
% 0.45/0.67           = (k5_xboole_0 @ X17 @ (k3_xboole_0 @ X17 @ X18)))),
% 0.45/0.67      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.45/0.67  thf('63', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 0.45/0.67           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.45/0.67      inference('sup+', [status(thm)], ['61', '62'])).
% 0.45/0.67  thf('64', plain, (![X19 : $i]: ((k4_xboole_0 @ X19 @ k1_xboole_0) = (X19))),
% 0.45/0.67      inference('cnf', [status(esa)], [t3_boole])).
% 0.45/0.67  thf('65', plain,
% 0.45/0.67      (![X20 : $i, X21 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X20 @ X21) @ X21)),
% 0.45/0.67      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.45/0.67  thf('66', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.45/0.67      inference('sup+', [status(thm)], ['64', '65'])).
% 0.45/0.67  thf('67', plain,
% 0.45/0.67      (![X16 : $i]:
% 0.45/0.67         (((X16) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X16) @ X16))),
% 0.45/0.67      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.45/0.67  thf('68', plain,
% 0.45/0.67      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.45/0.67         ((r2_hidden @ X6 @ X4) | ~ (r2_hidden @ X6 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.45/0.67      inference('simplify', [status(thm)], ['46'])).
% 0.45/0.67  thf('69', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.45/0.67          | (r2_hidden @ (sk_B @ (k3_xboole_0 @ X1 @ X0)) @ X0))),
% 0.45/0.67      inference('sup-', [status(thm)], ['67', '68'])).
% 0.45/0.67  thf('70', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         (((X0) = (k1_xboole_0))
% 0.45/0.67          | ~ (r1_xboole_0 @ X0 @ X1)
% 0.45/0.67          | ~ (r2_hidden @ (sk_B @ X0) @ X1))),
% 0.45/0.67      inference('sup-', [status(thm)], ['18', '19'])).
% 0.45/0.67  thf('71', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.45/0.67          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 0.45/0.67          | ((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['69', '70'])).
% 0.45/0.67  thf('72', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         (~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 0.45/0.67          | ((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)))),
% 0.45/0.67      inference('simplify', [status(thm)], ['71'])).
% 0.45/0.67  thf('73', plain,
% 0.45/0.67      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.67      inference('sup-', [status(thm)], ['66', '72'])).
% 0.45/0.67  thf('74', plain,
% 0.45/0.67      (![X17 : $i, X18 : $i]:
% 0.45/0.67         ((k4_xboole_0 @ X17 @ X18)
% 0.45/0.67           = (k5_xboole_0 @ X17 @ (k3_xboole_0 @ X17 @ X18)))),
% 0.45/0.67      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.45/0.67  thf('75', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.45/0.67      inference('sup+', [status(thm)], ['73', '74'])).
% 0.45/0.67  thf('76', plain, (![X19 : $i]: ((k4_xboole_0 @ X19 @ k1_xboole_0) = (X19))),
% 0.45/0.67      inference('cnf', [status(esa)], [t3_boole])).
% 0.45/0.67  thf('77', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.45/0.67      inference('sup+', [status(thm)], ['75', '76'])).
% 0.45/0.67  thf('78', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 0.45/0.67      inference('demod', [status(thm)], ['63', '77'])).
% 0.45/0.67  thf('79', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         (((k4_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_tarski @ X1))
% 0.45/0.67          | (r2_hidden @ X1 @ X0))),
% 0.45/0.67      inference('sup+', [status(thm)], ['36', '78'])).
% 0.45/0.67  thf('80', plain,
% 0.45/0.67      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) != (k1_tarski @ sk_A)))
% 0.45/0.67         <= (~
% 0.45/0.67             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 0.45/0.67      inference('split', [status(esa)], ['3'])).
% 0.45/0.67  thf('81', plain,
% 0.45/0.67      (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))) | 
% 0.45/0.67       ((r2_hidden @ sk_A @ sk_B_1))),
% 0.45/0.67      inference('split', [status(esa)], ['3'])).
% 0.45/0.67  thf('82', plain,
% 0.45/0.67      (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A)))),
% 0.45/0.67      inference('sat_resolution*', [status(thm)], ['2', '33', '81'])).
% 0.45/0.67  thf('83', plain,
% 0.45/0.67      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) != (k1_tarski @ sk_A))),
% 0.45/0.67      inference('simpl_trail', [status(thm)], ['80', '82'])).
% 0.45/0.67  thf('84', plain,
% 0.45/0.67      ((((k1_tarski @ sk_A) != (k1_tarski @ sk_A))
% 0.45/0.67        | (r2_hidden @ sk_A @ sk_B_1))),
% 0.45/0.67      inference('sup-', [status(thm)], ['79', '83'])).
% 0.45/0.67  thf('85', plain, ((r2_hidden @ sk_A @ sk_B_1)),
% 0.45/0.67      inference('simplify', [status(thm)], ['84'])).
% 0.45/0.67  thf('86', plain, ($false), inference('demod', [status(thm)], ['35', '85'])).
% 0.45/0.67  
% 0.45/0.67  % SZS output end Refutation
% 0.45/0.67  
% 0.45/0.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
