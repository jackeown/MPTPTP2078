%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NsoHW1hxGI

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:16 EST 2020

% Result     : Theorem 0.76s
% Output     : Refutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 472 expanded)
%              Number of leaves         :   19 ( 144 expanded)
%              Depth                    :   22
%              Number of atoms          : 1120 (4385 expanded)
%              Number of equality atoms :   96 ( 361 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

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
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('11',plain,(
    ! [X44: $i,X45: $i] :
      ( ( ( k4_xboole_0 @ X44 @ ( k1_tarski @ X45 ) )
        = X44 )
      | ( r2_hidden @ X45 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('12',plain,(
    ! [X18: $i] :
      ( ( X18 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X18 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('13',plain,(
    ! [X18: $i] :
      ( ( X18 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X18 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('14',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X2 @ ( k3_xboole_0 @ X3 @ X4 ) )
      | ~ ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_B @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k3_xboole_0 @ X0 @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_B @ X0 ) @ ( k3_xboole_0 @ X0 @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('18',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ X19 @ ( k3_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('19',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X14 @ X15 )
      | ~ ( r2_hidden @ X14 @ X16 )
      | ~ ( r2_hidden @ X14 @ ( k5_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('22',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('23',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['20','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_B @ X0 ) @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_B @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['11','26'])).

thf('28',plain,(
    ! [X18: $i] :
      ( ( X18 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X18 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('30',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ sk_A @ X0 )
        | ( r2_hidden @ sk_A @ ( k3_xboole_0 @ X0 @ sk_B_1 ) ) )
   <= ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('31',plain,
    ( ( ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ( r2_hidden @ sk_A @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) )
   <= ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('33',plain,
    ( ( ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ( r2_hidden @ sk_A @ ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ) )
   <= ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['20','24'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) )
   <= ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,
    ( ( ~ ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['10','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('40',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( r2_hidden @ X43 @ X44 )
      | ( ( k4_xboole_0 @ X44 @ ( k1_tarski @ X43 ) )
       != X44 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('42',plain,
    ( ! [X0: $i] :
        ( ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
         != X0 )
        | ~ ( r2_hidden @ sk_A @ X0 ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('43',plain,(
    ! [X21: $i] :
      ( ( k4_xboole_0 @ X21 @ k1_xboole_0 )
      = X21 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('44',plain,
    ( ! [X0: $i] :
        ( ( X0 != X0 )
        | ~ ( r2_hidden @ sk_A @ X0 ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ sk_A @ X0 )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
     != ( k1_tarski @ sk_A ) )
    | ~ ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['9','45'])).

thf('47',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['2','46'])).

thf('48',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['1','47'])).

thf('49',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k3_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('50',plain,(
    ! [X21: $i] :
      ( ( k4_xboole_0 @ X21 @ k1_xboole_0 )
      = X21 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('51',plain,(
    ! [X18: $i] :
      ( ( X18 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X18 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['20','24'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_B @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_B @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) @ X0 )
      | ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['50','53'])).

thf('55',plain,(
    ! [X18: $i] :
      ( ( X18 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X18 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['54','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['20','24'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X21: $i] :
      ( ( k4_xboole_0 @ X21 @ k1_xboole_0 )
      = X21 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X1 )
      | ( X1
        = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['49','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['54','57'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X44: $i,X45: $i] :
      ( ( ( k4_xboole_0 @ X44 @ ( k1_tarski @ X45 ) )
        = X44 )
      | ( r2_hidden @ X45 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('69',plain,(
    ! [X18: $i] :
      ( ( X18 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X18 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('70',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['20','24'])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_B @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['68','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['67','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) )
        = k1_xboole_0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ X19 @ ( k3_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
        = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['54','57'])).

thf('85',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ X19 @ ( k3_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X21: $i] :
      ( ( k4_xboole_0 @ X21 @ k1_xboole_0 )
      = X21 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
        = X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['83','88'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('90',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X11 )
      | ~ ( r2_hidden @ X12 @ X10 )
      | ( X11
       != ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('91',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X10 )
      | ~ ( r2_hidden @ X12 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['89','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('94',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference(clc,[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['66','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('97',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ X19 @ ( k3_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['95','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
     != ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('103',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
     != ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['3'])).

thf('104',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','46','103'])).

thf('105',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['102','104'])).

thf('106',plain,
    ( ( ( k1_tarski @ sk_A )
     != ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['101','105'])).

thf('107',plain,(
    r2_hidden @ sk_A @ sk_B_1 ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,(
    $false ),
    inference(demod,[status(thm)],['48','107'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NsoHW1hxGI
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:02:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.76/0.97  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.76/0.97  % Solved by: fo/fo7.sh
% 0.76/0.97  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.76/0.97  % done 722 iterations in 0.513s
% 0.76/0.97  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.76/0.97  % SZS output start Refutation
% 0.76/0.97  thf(sk_B_type, type, sk_B: $i > $i).
% 0.76/0.97  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.76/0.97  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.76/0.97  thf(sk_A_type, type, sk_A: $i).
% 0.76/0.97  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.76/0.97  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.76/0.97  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.76/0.97  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.76/0.97  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.76/0.97  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.76/0.97  thf(t67_zfmisc_1, conjecture,
% 0.76/0.97    (![A:$i,B:$i]:
% 0.76/0.97     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 0.76/0.97       ( ~( r2_hidden @ A @ B ) ) ))).
% 0.76/0.97  thf(zf_stmt_0, negated_conjecture,
% 0.76/0.97    (~( ![A:$i,B:$i]:
% 0.76/0.97        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 0.76/0.97          ( ~( r2_hidden @ A @ B ) ) ) )),
% 0.76/0.97    inference('cnf.neg', [status(esa)], [t67_zfmisc_1])).
% 0.76/0.97  thf('0', plain,
% 0.76/0.97      ((~ (r2_hidden @ sk_A @ sk_B_1)
% 0.76/0.97        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A)))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('1', plain,
% 0.76/0.97      ((~ (r2_hidden @ sk_A @ sk_B_1)) <= (~ ((r2_hidden @ sk_A @ sk_B_1)))),
% 0.76/0.97      inference('split', [status(esa)], ['0'])).
% 0.76/0.97  thf('2', plain,
% 0.76/0.97      (~ ((r2_hidden @ sk_A @ sk_B_1)) | 
% 0.76/0.97       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A)))),
% 0.76/0.97      inference('split', [status(esa)], ['0'])).
% 0.76/0.97  thf('3', plain,
% 0.76/0.97      (((r2_hidden @ sk_A @ sk_B_1)
% 0.76/0.97        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) != (k1_tarski @ sk_A)))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('4', plain,
% 0.76/0.97      (((r2_hidden @ sk_A @ sk_B_1)) <= (((r2_hidden @ sk_A @ sk_B_1)))),
% 0.76/0.97      inference('split', [status(esa)], ['3'])).
% 0.76/0.97  thf('5', plain,
% 0.76/0.97      (((r2_hidden @ sk_A @ sk_B_1)) <= (((r2_hidden @ sk_A @ sk_B_1)))),
% 0.76/0.97      inference('split', [status(esa)], ['3'])).
% 0.76/0.97  thf(d4_xboole_0, axiom,
% 0.76/0.97    (![A:$i,B:$i,C:$i]:
% 0.76/0.97     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.76/0.97       ( ![D:$i]:
% 0.76/0.97         ( ( r2_hidden @ D @ C ) <=>
% 0.76/0.97           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.76/0.97  thf('6', plain,
% 0.76/0.97      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.76/0.97         (~ (r2_hidden @ X2 @ X3)
% 0.76/0.97          | ~ (r2_hidden @ X2 @ X4)
% 0.76/0.97          | (r2_hidden @ X2 @ X5)
% 0.76/0.97          | ((X5) != (k3_xboole_0 @ X3 @ X4)))),
% 0.76/0.97      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.76/0.97  thf('7', plain,
% 0.76/0.97      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.76/0.97         ((r2_hidden @ X2 @ (k3_xboole_0 @ X3 @ X4))
% 0.76/0.97          | ~ (r2_hidden @ X2 @ X4)
% 0.76/0.97          | ~ (r2_hidden @ X2 @ X3))),
% 0.76/0.97      inference('simplify', [status(thm)], ['6'])).
% 0.76/0.97  thf('8', plain,
% 0.76/0.97      ((![X0 : $i]:
% 0.76/0.97          (~ (r2_hidden @ sk_A @ X0)
% 0.76/0.97           | (r2_hidden @ sk_A @ (k3_xboole_0 @ X0 @ sk_B_1))))
% 0.76/0.97         <= (((r2_hidden @ sk_A @ sk_B_1)))),
% 0.76/0.97      inference('sup-', [status(thm)], ['5', '7'])).
% 0.76/0.97  thf('9', plain,
% 0.76/0.97      (((r2_hidden @ sk_A @ (k3_xboole_0 @ sk_B_1 @ sk_B_1)))
% 0.76/0.97         <= (((r2_hidden @ sk_A @ sk_B_1)))),
% 0.76/0.97      inference('sup-', [status(thm)], ['4', '8'])).
% 0.76/0.97  thf('10', plain,
% 0.76/0.97      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A)))
% 0.76/0.97         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 0.76/0.97      inference('split', [status(esa)], ['0'])).
% 0.76/0.97  thf(t65_zfmisc_1, axiom,
% 0.76/0.97    (![A:$i,B:$i]:
% 0.76/0.97     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.76/0.97       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.76/0.97  thf('11', plain,
% 0.76/0.97      (![X44 : $i, X45 : $i]:
% 0.76/0.97         (((k4_xboole_0 @ X44 @ (k1_tarski @ X45)) = (X44))
% 0.76/0.97          | (r2_hidden @ X45 @ X44))),
% 0.76/0.97      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.76/0.97  thf(t7_xboole_0, axiom,
% 0.76/0.97    (![A:$i]:
% 0.76/0.97     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.76/0.97          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.76/0.97  thf('12', plain,
% 0.76/0.97      (![X18 : $i]:
% 0.76/0.97         (((X18) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X18) @ X18))),
% 0.76/0.97      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.76/0.97  thf('13', plain,
% 0.76/0.97      (![X18 : $i]:
% 0.76/0.97         (((X18) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X18) @ X18))),
% 0.76/0.97      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.76/0.97  thf('14', plain,
% 0.76/0.97      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.76/0.97         ((r2_hidden @ X2 @ (k3_xboole_0 @ X3 @ X4))
% 0.76/0.97          | ~ (r2_hidden @ X2 @ X4)
% 0.76/0.97          | ~ (r2_hidden @ X2 @ X3))),
% 0.76/0.97      inference('simplify', [status(thm)], ['6'])).
% 0.76/0.97  thf('15', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]:
% 0.76/0.97         (((X0) = (k1_xboole_0))
% 0.76/0.97          | ~ (r2_hidden @ (sk_B @ X0) @ X1)
% 0.76/0.97          | (r2_hidden @ (sk_B @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 0.76/0.97      inference('sup-', [status(thm)], ['13', '14'])).
% 0.76/0.97  thf('16', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         (((X0) = (k1_xboole_0))
% 0.76/0.97          | (r2_hidden @ (sk_B @ X0) @ (k3_xboole_0 @ X0 @ X0))
% 0.76/0.97          | ((X0) = (k1_xboole_0)))),
% 0.76/0.97      inference('sup-', [status(thm)], ['12', '15'])).
% 0.76/0.97  thf('17', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((r2_hidden @ (sk_B @ X0) @ (k3_xboole_0 @ X0 @ X0))
% 0.76/0.97          | ((X0) = (k1_xboole_0)))),
% 0.76/0.97      inference('simplify', [status(thm)], ['16'])).
% 0.76/0.97  thf(t100_xboole_1, axiom,
% 0.76/0.97    (![A:$i,B:$i]:
% 0.76/0.97     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.76/0.97  thf('18', plain,
% 0.76/0.97      (![X19 : $i, X20 : $i]:
% 0.76/0.97         ((k4_xboole_0 @ X19 @ X20)
% 0.76/0.97           = (k5_xboole_0 @ X19 @ (k3_xboole_0 @ X19 @ X20)))),
% 0.76/0.97      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.76/0.97  thf(t1_xboole_0, axiom,
% 0.76/0.97    (![A:$i,B:$i,C:$i]:
% 0.76/0.97     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.76/0.97       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 0.76/0.97  thf('19', plain,
% 0.76/0.97      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.76/0.97         (~ (r2_hidden @ X14 @ X15)
% 0.76/0.97          | ~ (r2_hidden @ X14 @ X16)
% 0.76/0.97          | ~ (r2_hidden @ X14 @ (k5_xboole_0 @ X15 @ X16)))),
% 0.76/0.97      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.76/0.97  thf('20', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.97         (~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 0.76/0.97          | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.76/0.97          | ~ (r2_hidden @ X2 @ X1))),
% 0.76/0.97      inference('sup-', [status(thm)], ['18', '19'])).
% 0.76/0.97  thf(commutativity_k3_xboole_0, axiom,
% 0.76/0.97    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.76/0.97  thf('21', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.76/0.97      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.76/0.97  thf('22', plain,
% 0.76/0.97      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.76/0.97         (~ (r2_hidden @ X6 @ X5)
% 0.76/0.97          | (r2_hidden @ X6 @ X4)
% 0.76/0.97          | ((X5) != (k3_xboole_0 @ X3 @ X4)))),
% 0.76/0.97      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.76/0.97  thf('23', plain,
% 0.76/0.97      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.76/0.97         ((r2_hidden @ X6 @ X4) | ~ (r2_hidden @ X6 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.76/0.97      inference('simplify', [status(thm)], ['22'])).
% 0.76/0.97  thf('24', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.97         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r2_hidden @ X2 @ X1))),
% 0.76/0.97      inference('sup-', [status(thm)], ['21', '23'])).
% 0.76/0.97  thf('25', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.97         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.76/0.97          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.76/0.97      inference('clc', [status(thm)], ['20', '24'])).
% 0.76/0.97  thf('26', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         (((X0) = (k1_xboole_0))
% 0.76/0.97          | ~ (r2_hidden @ (sk_B @ X0) @ (k4_xboole_0 @ X0 @ X0)))),
% 0.76/0.97      inference('sup-', [status(thm)], ['17', '25'])).
% 0.76/0.97  thf('27', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         (~ (r2_hidden @ (sk_B @ (k1_tarski @ X0)) @ (k1_tarski @ X0))
% 0.76/0.97          | (r2_hidden @ X0 @ (k1_tarski @ X0))
% 0.76/0.97          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.76/0.97      inference('sup-', [status(thm)], ['11', '26'])).
% 0.76/0.97  thf('28', plain,
% 0.76/0.97      (![X18 : $i]:
% 0.76/0.97         (((X18) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X18) @ X18))),
% 0.76/0.97      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.76/0.97  thf('29', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.76/0.97          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.76/0.97      inference('clc', [status(thm)], ['27', '28'])).
% 0.76/0.97  thf('30', plain,
% 0.76/0.97      ((![X0 : $i]:
% 0.76/0.97          (~ (r2_hidden @ sk_A @ X0)
% 0.76/0.97           | (r2_hidden @ sk_A @ (k3_xboole_0 @ X0 @ sk_B_1))))
% 0.76/0.97         <= (((r2_hidden @ sk_A @ sk_B_1)))),
% 0.76/0.97      inference('sup-', [status(thm)], ['5', '7'])).
% 0.76/0.97  thf('31', plain,
% 0.76/0.97      (((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.76/0.97         | (r2_hidden @ sk_A @ (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1))))
% 0.76/0.97         <= (((r2_hidden @ sk_A @ sk_B_1)))),
% 0.76/0.97      inference('sup-', [status(thm)], ['29', '30'])).
% 0.76/0.97  thf('32', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.76/0.97      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.76/0.97  thf('33', plain,
% 0.76/0.97      (((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.76/0.97         | (r2_hidden @ sk_A @ (k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))))
% 0.76/0.97         <= (((r2_hidden @ sk_A @ sk_B_1)))),
% 0.76/0.97      inference('demod', [status(thm)], ['31', '32'])).
% 0.76/0.97  thf('34', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.76/0.97      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.76/0.97  thf('35', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.97         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.76/0.97          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.76/0.97      inference('clc', [status(thm)], ['20', '24'])).
% 0.76/0.97  thf('36', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.97         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.76/0.97          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.76/0.97      inference('sup-', [status(thm)], ['34', '35'])).
% 0.76/0.97  thf('37', plain,
% 0.76/0.97      (((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.76/0.97         | ~ (r2_hidden @ sk_A @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1))))
% 0.76/0.97         <= (((r2_hidden @ sk_A @ sk_B_1)))),
% 0.76/0.97      inference('sup-', [status(thm)], ['33', '36'])).
% 0.76/0.97  thf('38', plain,
% 0.76/0.97      (((~ (r2_hidden @ sk_A @ (k1_tarski @ sk_A))
% 0.76/0.97         | ((k1_tarski @ sk_A) = (k1_xboole_0))))
% 0.76/0.97         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))) & 
% 0.76/0.97             ((r2_hidden @ sk_A @ sk_B_1)))),
% 0.76/0.97      inference('sup-', [status(thm)], ['10', '37'])).
% 0.76/0.97  thf('39', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.76/0.97          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.76/0.97      inference('clc', [status(thm)], ['27', '28'])).
% 0.76/0.97  thf('40', plain,
% 0.76/0.97      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 0.76/0.97         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))) & 
% 0.76/0.97             ((r2_hidden @ sk_A @ sk_B_1)))),
% 0.76/0.97      inference('clc', [status(thm)], ['38', '39'])).
% 0.76/0.97  thf('41', plain,
% 0.76/0.97      (![X43 : $i, X44 : $i]:
% 0.76/0.97         (~ (r2_hidden @ X43 @ X44)
% 0.76/0.97          | ((k4_xboole_0 @ X44 @ (k1_tarski @ X43)) != (X44)))),
% 0.76/0.97      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.76/0.97  thf('42', plain,
% 0.76/0.97      ((![X0 : $i]:
% 0.76/0.97          (((k4_xboole_0 @ X0 @ k1_xboole_0) != (X0))
% 0.76/0.97           | ~ (r2_hidden @ sk_A @ X0)))
% 0.76/0.97         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))) & 
% 0.76/0.97             ((r2_hidden @ sk_A @ sk_B_1)))),
% 0.76/0.97      inference('sup-', [status(thm)], ['40', '41'])).
% 0.76/0.97  thf(t3_boole, axiom,
% 0.76/0.97    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.76/0.97  thf('43', plain, (![X21 : $i]: ((k4_xboole_0 @ X21 @ k1_xboole_0) = (X21))),
% 0.76/0.97      inference('cnf', [status(esa)], [t3_boole])).
% 0.76/0.97  thf('44', plain,
% 0.76/0.97      ((![X0 : $i]: (((X0) != (X0)) | ~ (r2_hidden @ sk_A @ X0)))
% 0.76/0.97         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))) & 
% 0.76/0.97             ((r2_hidden @ sk_A @ sk_B_1)))),
% 0.76/0.97      inference('demod', [status(thm)], ['42', '43'])).
% 0.76/0.97  thf('45', plain,
% 0.76/0.97      ((![X0 : $i]: ~ (r2_hidden @ sk_A @ X0))
% 0.76/0.97         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))) & 
% 0.76/0.97             ((r2_hidden @ sk_A @ sk_B_1)))),
% 0.76/0.97      inference('simplify', [status(thm)], ['44'])).
% 0.76/0.97  thf('46', plain,
% 0.76/0.97      (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))) | 
% 0.76/0.97       ~ ((r2_hidden @ sk_A @ sk_B_1))),
% 0.76/0.97      inference('sup-', [status(thm)], ['9', '45'])).
% 0.76/0.97  thf('47', plain, (~ ((r2_hidden @ sk_A @ sk_B_1))),
% 0.76/0.97      inference('sat_resolution*', [status(thm)], ['2', '46'])).
% 0.76/0.97  thf('48', plain, (~ (r2_hidden @ sk_A @ sk_B_1)),
% 0.76/0.97      inference('simpl_trail', [status(thm)], ['1', '47'])).
% 0.76/0.97  thf('49', plain,
% 0.76/0.97      (![X3 : $i, X4 : $i, X7 : $i]:
% 0.76/0.97         (((X7) = (k3_xboole_0 @ X3 @ X4))
% 0.76/0.97          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 0.76/0.97          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 0.76/0.97      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.76/0.97  thf('50', plain, (![X21 : $i]: ((k4_xboole_0 @ X21 @ k1_xboole_0) = (X21))),
% 0.76/0.97      inference('cnf', [status(esa)], [t3_boole])).
% 0.76/0.97  thf('51', plain,
% 0.76/0.97      (![X18 : $i]:
% 0.76/0.97         (((X18) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X18) @ X18))),
% 0.76/0.97      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.76/0.97  thf('52', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.97         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.76/0.97          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.76/0.97      inference('clc', [status(thm)], ['20', '24'])).
% 0.76/0.97  thf('53', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]:
% 0.76/0.97         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.76/0.97          | ~ (r2_hidden @ (sk_B @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.76/0.97               (k4_xboole_0 @ X1 @ X0)))),
% 0.76/0.97      inference('sup-', [status(thm)], ['51', '52'])).
% 0.76/0.97  thf('54', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         (~ (r2_hidden @ (sk_B @ (k3_xboole_0 @ X0 @ k1_xboole_0)) @ X0)
% 0.76/0.97          | ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.76/0.97      inference('sup-', [status(thm)], ['50', '53'])).
% 0.76/0.97  thf('55', plain,
% 0.76/0.97      (![X18 : $i]:
% 0.76/0.97         (((X18) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X18) @ X18))),
% 0.76/0.97      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.76/0.97  thf('56', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.97         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r2_hidden @ X2 @ X1))),
% 0.76/0.97      inference('sup-', [status(thm)], ['21', '23'])).
% 0.76/0.97  thf('57', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]:
% 0.76/0.97         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.76/0.97          | (r2_hidden @ (sk_B @ (k3_xboole_0 @ X1 @ X0)) @ X1))),
% 0.76/0.97      inference('sup-', [status(thm)], ['55', '56'])).
% 0.76/0.97  thf('58', plain,
% 0.76/0.97      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.76/0.97      inference('clc', [status(thm)], ['54', '57'])).
% 0.76/0.97  thf('59', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.97         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.76/0.97          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.76/0.97      inference('clc', [status(thm)], ['20', '24'])).
% 0.76/0.97  thf('60', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]:
% 0.76/0.97         (~ (r2_hidden @ X1 @ k1_xboole_0)
% 0.76/0.97          | ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.76/0.97      inference('sup-', [status(thm)], ['58', '59'])).
% 0.76/0.97  thf('61', plain, (![X21 : $i]: ((k4_xboole_0 @ X21 @ k1_xboole_0) = (X21))),
% 0.76/0.97      inference('cnf', [status(esa)], [t3_boole])).
% 0.76/0.97  thf('62', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]:
% 0.76/0.97         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r2_hidden @ X1 @ X0))),
% 0.76/0.97      inference('demod', [status(thm)], ['60', '61'])).
% 0.76/0.97  thf('63', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.76/0.97      inference('condensation', [status(thm)], ['62'])).
% 0.76/0.97  thf('64', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]:
% 0.76/0.97         ((r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X1)
% 0.76/0.97          | ((X1) = (k3_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.76/0.97      inference('sup-', [status(thm)], ['49', '63'])).
% 0.76/0.97  thf('65', plain,
% 0.76/0.97      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.76/0.97      inference('clc', [status(thm)], ['54', '57'])).
% 0.76/0.97  thf('66', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]:
% 0.76/0.97         ((r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X1)
% 0.76/0.97          | ((X1) = (k1_xboole_0)))),
% 0.76/0.97      inference('demod', [status(thm)], ['64', '65'])).
% 0.76/0.97  thf('67', plain,
% 0.76/0.97      (![X44 : $i, X45 : $i]:
% 0.76/0.97         (((k4_xboole_0 @ X44 @ (k1_tarski @ X45)) = (X44))
% 0.76/0.97          | (r2_hidden @ X45 @ X44))),
% 0.76/0.97      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.76/0.97  thf('68', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]:
% 0.76/0.97         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.76/0.97          | (r2_hidden @ (sk_B @ (k3_xboole_0 @ X1 @ X0)) @ X1))),
% 0.76/0.97      inference('sup-', [status(thm)], ['55', '56'])).
% 0.76/0.97  thf('69', plain,
% 0.76/0.97      (![X18 : $i]:
% 0.76/0.97         (((X18) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X18) @ X18))),
% 0.76/0.97      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.76/0.97  thf('70', plain,
% 0.76/0.97      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.76/0.97         ((r2_hidden @ X6 @ X4) | ~ (r2_hidden @ X6 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.76/0.97      inference('simplify', [status(thm)], ['22'])).
% 0.76/0.97  thf('71', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]:
% 0.76/0.97         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.76/0.97          | (r2_hidden @ (sk_B @ (k3_xboole_0 @ X1 @ X0)) @ X0))),
% 0.76/0.97      inference('sup-', [status(thm)], ['69', '70'])).
% 0.76/0.97  thf('72', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.97         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.76/0.97          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.76/0.97      inference('clc', [status(thm)], ['20', '24'])).
% 0.76/0.97  thf('73', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.97         (((k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)) = (k1_xboole_0))
% 0.76/0.97          | ~ (r2_hidden @ 
% 0.76/0.97               (sk_B @ (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))) @ 
% 0.76/0.97               (k4_xboole_0 @ X1 @ X0)))),
% 0.76/0.97      inference('sup-', [status(thm)], ['71', '72'])).
% 0.76/0.97  thf('74', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]:
% 0.76/0.97         (((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 0.76/0.97            = (k1_xboole_0))
% 0.76/0.97          | ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 0.76/0.97              = (k1_xboole_0)))),
% 0.76/0.97      inference('sup-', [status(thm)], ['68', '73'])).
% 0.76/0.97  thf('75', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.76/0.97      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.76/0.97  thf('76', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.76/0.97      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.76/0.97  thf('77', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]:
% 0.76/0.97         (((k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 0.76/0.97            = (k1_xboole_0))
% 0.76/0.97          | ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 0.76/0.97              = (k1_xboole_0)))),
% 0.76/0.97      inference('demod', [status(thm)], ['74', '75', '76'])).
% 0.76/0.97  thf('78', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]:
% 0.76/0.97         ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 0.76/0.97           = (k1_xboole_0))),
% 0.76/0.97      inference('simplify', [status(thm)], ['77'])).
% 0.76/0.97  thf('79', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]:
% 0.76/0.97         (((k3_xboole_0 @ (k3_xboole_0 @ X0 @ (k1_tarski @ X1)) @ X0)
% 0.76/0.97            = (k1_xboole_0))
% 0.76/0.97          | (r2_hidden @ X1 @ X0))),
% 0.76/0.97      inference('sup+', [status(thm)], ['67', '78'])).
% 0.76/0.97  thf('80', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.76/0.97      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.76/0.97  thf('81', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]:
% 0.76/0.97         (((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ (k1_tarski @ X1)))
% 0.76/0.97            = (k1_xboole_0))
% 0.76/0.97          | (r2_hidden @ X1 @ X0))),
% 0.76/0.97      inference('demod', [status(thm)], ['79', '80'])).
% 0.76/0.97  thf('82', plain,
% 0.76/0.97      (![X19 : $i, X20 : $i]:
% 0.76/0.97         ((k4_xboole_0 @ X19 @ X20)
% 0.76/0.97           = (k5_xboole_0 @ X19 @ (k3_xboole_0 @ X19 @ X20)))),
% 0.76/0.97      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.76/0.97  thf('83', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]:
% 0.76/0.97         (((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 0.76/0.97            = (k5_xboole_0 @ X1 @ k1_xboole_0))
% 0.76/0.97          | (r2_hidden @ X0 @ X1))),
% 0.76/0.97      inference('sup+', [status(thm)], ['81', '82'])).
% 0.76/0.97  thf('84', plain,
% 0.76/0.97      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.76/0.97      inference('clc', [status(thm)], ['54', '57'])).
% 0.76/0.97  thf('85', plain,
% 0.76/0.97      (![X19 : $i, X20 : $i]:
% 0.76/0.97         ((k4_xboole_0 @ X19 @ X20)
% 0.76/0.97           = (k5_xboole_0 @ X19 @ (k3_xboole_0 @ X19 @ X20)))),
% 0.76/0.97      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.76/0.97  thf('86', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.76/0.97      inference('sup+', [status(thm)], ['84', '85'])).
% 0.76/0.97  thf('87', plain, (![X21 : $i]: ((k4_xboole_0 @ X21 @ k1_xboole_0) = (X21))),
% 0.76/0.97      inference('cnf', [status(esa)], [t3_boole])).
% 0.76/0.97  thf('88', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.76/0.97      inference('sup+', [status(thm)], ['86', '87'])).
% 0.76/0.97  thf('89', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]:
% 0.76/0.97         (((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ (k1_tarski @ X0))) = (X1))
% 0.76/0.97          | (r2_hidden @ X0 @ X1))),
% 0.76/0.97      inference('demod', [status(thm)], ['83', '88'])).
% 0.76/0.97  thf(d5_xboole_0, axiom,
% 0.76/0.97    (![A:$i,B:$i,C:$i]:
% 0.76/0.97     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.76/0.97       ( ![D:$i]:
% 0.76/0.97         ( ( r2_hidden @ D @ C ) <=>
% 0.76/0.97           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.76/0.97  thf('90', plain,
% 0.76/0.97      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.76/0.97         (~ (r2_hidden @ X12 @ X11)
% 0.76/0.97          | ~ (r2_hidden @ X12 @ X10)
% 0.76/0.97          | ((X11) != (k4_xboole_0 @ X9 @ X10)))),
% 0.76/0.97      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.76/0.97  thf('91', plain,
% 0.76/0.97      (![X9 : $i, X10 : $i, X12 : $i]:
% 0.76/0.97         (~ (r2_hidden @ X12 @ X10)
% 0.76/0.97          | ~ (r2_hidden @ X12 @ (k4_xboole_0 @ X9 @ X10)))),
% 0.76/0.97      inference('simplify', [status(thm)], ['90'])).
% 0.76/0.97  thf('92', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.97         (~ (r2_hidden @ X2 @ X0)
% 0.76/0.97          | (r2_hidden @ X1 @ X0)
% 0.76/0.97          | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ (k1_tarski @ X1))))),
% 0.76/0.97      inference('sup-', [status(thm)], ['89', '91'])).
% 0.76/0.97  thf('93', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.97         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r2_hidden @ X2 @ X1))),
% 0.76/0.97      inference('sup-', [status(thm)], ['21', '23'])).
% 0.76/0.97  thf('94', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.97         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ (k1_tarski @ X1)))
% 0.76/0.97          | (r2_hidden @ X1 @ X0))),
% 0.76/0.97      inference('clc', [status(thm)], ['92', '93'])).
% 0.76/0.97  thf('95', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]:
% 0.76/0.97         (((k3_xboole_0 @ X1 @ (k1_tarski @ X0)) = (k1_xboole_0))
% 0.76/0.97          | (r2_hidden @ X0 @ X1))),
% 0.76/0.97      inference('sup-', [status(thm)], ['66', '94'])).
% 0.76/0.97  thf('96', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.76/0.97      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.76/0.97  thf('97', plain,
% 0.76/0.97      (![X19 : $i, X20 : $i]:
% 0.76/0.97         ((k4_xboole_0 @ X19 @ X20)
% 0.76/0.97           = (k5_xboole_0 @ X19 @ (k3_xboole_0 @ X19 @ X20)))),
% 0.76/0.97      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.76/0.97  thf('98', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]:
% 0.76/0.97         ((k4_xboole_0 @ X0 @ X1)
% 0.76/0.97           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.76/0.97      inference('sup+', [status(thm)], ['96', '97'])).
% 0.76/0.97  thf('99', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]:
% 0.76/0.97         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1)
% 0.76/0.97            = (k5_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0))
% 0.76/0.97          | (r2_hidden @ X0 @ X1))),
% 0.76/0.97      inference('sup+', [status(thm)], ['95', '98'])).
% 0.76/0.97  thf('100', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.76/0.97      inference('sup+', [status(thm)], ['86', '87'])).
% 0.76/0.97  thf('101', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]:
% 0.76/0.97         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_tarski @ X0))
% 0.76/0.97          | (r2_hidden @ X0 @ X1))),
% 0.76/0.97      inference('demod', [status(thm)], ['99', '100'])).
% 0.76/0.97  thf('102', plain,
% 0.76/0.97      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) != (k1_tarski @ sk_A)))
% 0.76/0.98         <= (~
% 0.76/0.98             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 0.76/0.98      inference('split', [status(esa)], ['3'])).
% 0.76/0.98  thf('103', plain,
% 0.76/0.98      (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))) | 
% 0.76/0.98       ((r2_hidden @ sk_A @ sk_B_1))),
% 0.76/0.98      inference('split', [status(esa)], ['3'])).
% 0.76/0.98  thf('104', plain,
% 0.76/0.98      (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A)))),
% 0.76/0.98      inference('sat_resolution*', [status(thm)], ['2', '46', '103'])).
% 0.76/0.98  thf('105', plain,
% 0.76/0.98      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) != (k1_tarski @ sk_A))),
% 0.76/0.98      inference('simpl_trail', [status(thm)], ['102', '104'])).
% 0.76/0.98  thf('106', plain,
% 0.76/0.98      ((((k1_tarski @ sk_A) != (k1_tarski @ sk_A))
% 0.76/0.98        | (r2_hidden @ sk_A @ sk_B_1))),
% 0.76/0.98      inference('sup-', [status(thm)], ['101', '105'])).
% 0.76/0.98  thf('107', plain, ((r2_hidden @ sk_A @ sk_B_1)),
% 0.76/0.98      inference('simplify', [status(thm)], ['106'])).
% 0.76/0.98  thf('108', plain, ($false), inference('demod', [status(thm)], ['48', '107'])).
% 0.76/0.98  
% 0.76/0.98  % SZS output end Refutation
% 0.76/0.98  
% 0.76/0.98  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
