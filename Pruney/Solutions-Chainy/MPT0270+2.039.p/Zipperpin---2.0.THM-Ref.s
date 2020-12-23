%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lOi4SBkHUJ

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:17 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 331 expanded)
%              Number of leaves         :   18 ( 100 expanded)
%              Depth                    :   21
%              Number of atoms          :  828 (3090 expanded)
%              Number of equality atoms :   71 ( 252 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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
    ! [X31: $i,X32: $i] :
      ( ( ( k4_xboole_0 @ X31 @ ( k1_tarski @ X32 ) )
        = X31 )
      | ( r2_hidden @ X32 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('12',plain,(
    ! [X12: $i] :
      ( ( X12 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X12 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('13',plain,(
    ! [X12: $i] :
      ( ( X12 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X12 ) @ X12 ) ) ),
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
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('19',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r2_hidden @ X8 @ X10 )
      | ~ ( r2_hidden @ X8 @ ( k5_xboole_0 @ X9 @ X10 ) ) ) ),
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
    ! [X12: $i] :
      ( ( X12 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X12 ) @ X12 ) ) ),
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

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('41',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( X26 != X28 )
      | ~ ( r2_hidden @ X26 @ ( k4_xboole_0 @ X27 @ ( k1_tarski @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('42',plain,(
    ! [X27: $i,X28: $i] :
      ~ ( r2_hidden @ X28 @ ( k4_xboole_0 @ X27 @ ( k1_tarski @ X28 ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['40','42'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('44',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('45',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ sk_A @ X0 )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['43','44'])).

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
    ! [X31: $i,X32: $i] :
      ( ( ( k4_xboole_0 @ X31 @ ( k1_tarski @ X32 ) )
        = X31 )
      | ( r2_hidden @ X32 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('50',plain,(
    ! [X12: $i] :
      ( ( X12 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X12 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['20','24'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_B @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_B @ ( k3_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( ( k3_xboole_0 @ X0 @ ( k1_tarski @ X1 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf('54',plain,(
    ! [X12: $i] :
      ( ( X12 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X12 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ ( k1_tarski @ X1 ) )
        = k1_xboole_0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference(clc,[status(thm)],['53','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('59',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['57','60'])).

thf('62',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_B @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_B @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) @ X0 )
      | ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['61','70'])).

thf('72',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
     != ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('73',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
     != ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['3'])).

thf('74',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','46','73'])).

thf('75',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['72','74'])).

thf('76',plain,
    ( ( ( k1_tarski @ sk_A )
     != ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['71','75'])).

thf('77',plain,(
    r2_hidden @ sk_A @ sk_B_1 ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    $false ),
    inference(demod,[status(thm)],['48','77'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lOi4SBkHUJ
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:41:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.58/0.83  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.58/0.83  % Solved by: fo/fo7.sh
% 0.58/0.83  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.58/0.83  % done 551 iterations in 0.368s
% 0.58/0.83  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.58/0.83  % SZS output start Refutation
% 0.58/0.83  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.58/0.83  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.58/0.83  thf(sk_A_type, type, sk_A: $i).
% 0.58/0.83  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.58/0.83  thf(sk_B_type, type, sk_B: $i > $i).
% 0.58/0.83  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.58/0.83  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.58/0.83  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.58/0.83  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.58/0.83  thf(t67_zfmisc_1, conjecture,
% 0.58/0.83    (![A:$i,B:$i]:
% 0.58/0.83     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 0.58/0.83       ( ~( r2_hidden @ A @ B ) ) ))).
% 0.58/0.83  thf(zf_stmt_0, negated_conjecture,
% 0.58/0.83    (~( ![A:$i,B:$i]:
% 0.58/0.83        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 0.58/0.83          ( ~( r2_hidden @ A @ B ) ) ) )),
% 0.58/0.83    inference('cnf.neg', [status(esa)], [t67_zfmisc_1])).
% 0.58/0.83  thf('0', plain,
% 0.58/0.83      ((~ (r2_hidden @ sk_A @ sk_B_1)
% 0.58/0.83        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A)))),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf('1', plain,
% 0.58/0.83      ((~ (r2_hidden @ sk_A @ sk_B_1)) <= (~ ((r2_hidden @ sk_A @ sk_B_1)))),
% 0.58/0.83      inference('split', [status(esa)], ['0'])).
% 0.58/0.83  thf('2', plain,
% 0.58/0.83      (~ ((r2_hidden @ sk_A @ sk_B_1)) | 
% 0.58/0.83       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A)))),
% 0.58/0.83      inference('split', [status(esa)], ['0'])).
% 0.58/0.83  thf('3', plain,
% 0.58/0.83      (((r2_hidden @ sk_A @ sk_B_1)
% 0.58/0.83        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) != (k1_tarski @ sk_A)))),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf('4', plain,
% 0.58/0.83      (((r2_hidden @ sk_A @ sk_B_1)) <= (((r2_hidden @ sk_A @ sk_B_1)))),
% 0.58/0.83      inference('split', [status(esa)], ['3'])).
% 0.58/0.83  thf('5', plain,
% 0.58/0.83      (((r2_hidden @ sk_A @ sk_B_1)) <= (((r2_hidden @ sk_A @ sk_B_1)))),
% 0.58/0.83      inference('split', [status(esa)], ['3'])).
% 0.58/0.83  thf(d4_xboole_0, axiom,
% 0.58/0.83    (![A:$i,B:$i,C:$i]:
% 0.58/0.83     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.58/0.83       ( ![D:$i]:
% 0.58/0.83         ( ( r2_hidden @ D @ C ) <=>
% 0.58/0.83           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.58/0.83  thf('6', plain,
% 0.58/0.83      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.58/0.83         (~ (r2_hidden @ X2 @ X3)
% 0.58/0.83          | ~ (r2_hidden @ X2 @ X4)
% 0.58/0.83          | (r2_hidden @ X2 @ X5)
% 0.58/0.83          | ((X5) != (k3_xboole_0 @ X3 @ X4)))),
% 0.58/0.83      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.58/0.83  thf('7', plain,
% 0.58/0.83      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.58/0.83         ((r2_hidden @ X2 @ (k3_xboole_0 @ X3 @ X4))
% 0.58/0.83          | ~ (r2_hidden @ X2 @ X4)
% 0.58/0.83          | ~ (r2_hidden @ X2 @ X3))),
% 0.58/0.83      inference('simplify', [status(thm)], ['6'])).
% 0.58/0.83  thf('8', plain,
% 0.58/0.83      ((![X0 : $i]:
% 0.58/0.83          (~ (r2_hidden @ sk_A @ X0)
% 0.58/0.83           | (r2_hidden @ sk_A @ (k3_xboole_0 @ X0 @ sk_B_1))))
% 0.58/0.83         <= (((r2_hidden @ sk_A @ sk_B_1)))),
% 0.58/0.83      inference('sup-', [status(thm)], ['5', '7'])).
% 0.58/0.83  thf('9', plain,
% 0.58/0.83      (((r2_hidden @ sk_A @ (k3_xboole_0 @ sk_B_1 @ sk_B_1)))
% 0.58/0.83         <= (((r2_hidden @ sk_A @ sk_B_1)))),
% 0.58/0.83      inference('sup-', [status(thm)], ['4', '8'])).
% 0.58/0.83  thf('10', plain,
% 0.58/0.83      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A)))
% 0.58/0.83         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 0.58/0.83      inference('split', [status(esa)], ['0'])).
% 0.58/0.83  thf(t65_zfmisc_1, axiom,
% 0.58/0.83    (![A:$i,B:$i]:
% 0.58/0.83     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.58/0.83       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.58/0.83  thf('11', plain,
% 0.58/0.83      (![X31 : $i, X32 : $i]:
% 0.58/0.83         (((k4_xboole_0 @ X31 @ (k1_tarski @ X32)) = (X31))
% 0.58/0.83          | (r2_hidden @ X32 @ X31))),
% 0.58/0.83      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.58/0.83  thf(t7_xboole_0, axiom,
% 0.58/0.83    (![A:$i]:
% 0.58/0.83     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.58/0.83          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.58/0.83  thf('12', plain,
% 0.58/0.83      (![X12 : $i]:
% 0.58/0.83         (((X12) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X12) @ X12))),
% 0.58/0.83      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.58/0.83  thf('13', plain,
% 0.58/0.83      (![X12 : $i]:
% 0.58/0.83         (((X12) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X12) @ X12))),
% 0.58/0.83      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.58/0.83  thf('14', plain,
% 0.58/0.83      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.58/0.83         ((r2_hidden @ X2 @ (k3_xboole_0 @ X3 @ X4))
% 0.58/0.83          | ~ (r2_hidden @ X2 @ X4)
% 0.58/0.83          | ~ (r2_hidden @ X2 @ X3))),
% 0.58/0.83      inference('simplify', [status(thm)], ['6'])).
% 0.58/0.83  thf('15', plain,
% 0.58/0.83      (![X0 : $i, X1 : $i]:
% 0.58/0.83         (((X0) = (k1_xboole_0))
% 0.58/0.83          | ~ (r2_hidden @ (sk_B @ X0) @ X1)
% 0.58/0.83          | (r2_hidden @ (sk_B @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 0.58/0.83      inference('sup-', [status(thm)], ['13', '14'])).
% 0.58/0.83  thf('16', plain,
% 0.58/0.83      (![X0 : $i]:
% 0.58/0.83         (((X0) = (k1_xboole_0))
% 0.58/0.83          | (r2_hidden @ (sk_B @ X0) @ (k3_xboole_0 @ X0 @ X0))
% 0.58/0.83          | ((X0) = (k1_xboole_0)))),
% 0.58/0.83      inference('sup-', [status(thm)], ['12', '15'])).
% 0.58/0.83  thf('17', plain,
% 0.58/0.83      (![X0 : $i]:
% 0.58/0.83         ((r2_hidden @ (sk_B @ X0) @ (k3_xboole_0 @ X0 @ X0))
% 0.58/0.83          | ((X0) = (k1_xboole_0)))),
% 0.58/0.83      inference('simplify', [status(thm)], ['16'])).
% 0.58/0.83  thf(t100_xboole_1, axiom,
% 0.58/0.83    (![A:$i,B:$i]:
% 0.58/0.83     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.58/0.83  thf('18', plain,
% 0.58/0.83      (![X13 : $i, X14 : $i]:
% 0.58/0.83         ((k4_xboole_0 @ X13 @ X14)
% 0.58/0.83           = (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)))),
% 0.58/0.83      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.58/0.83  thf(t1_xboole_0, axiom,
% 0.58/0.83    (![A:$i,B:$i,C:$i]:
% 0.58/0.83     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.58/0.83       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 0.58/0.83  thf('19', plain,
% 0.58/0.83      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.58/0.83         (~ (r2_hidden @ X8 @ X9)
% 0.58/0.83          | ~ (r2_hidden @ X8 @ X10)
% 0.58/0.83          | ~ (r2_hidden @ X8 @ (k5_xboole_0 @ X9 @ X10)))),
% 0.58/0.83      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.58/0.83  thf('20', plain,
% 0.58/0.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.83         (~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 0.58/0.83          | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.58/0.83          | ~ (r2_hidden @ X2 @ X1))),
% 0.58/0.83      inference('sup-', [status(thm)], ['18', '19'])).
% 0.58/0.83  thf(commutativity_k3_xboole_0, axiom,
% 0.58/0.83    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.58/0.83  thf('21', plain,
% 0.58/0.83      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.58/0.83      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.58/0.83  thf('22', plain,
% 0.58/0.83      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.58/0.83         (~ (r2_hidden @ X6 @ X5)
% 0.58/0.83          | (r2_hidden @ X6 @ X4)
% 0.58/0.83          | ((X5) != (k3_xboole_0 @ X3 @ X4)))),
% 0.58/0.83      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.58/0.83  thf('23', plain,
% 0.58/0.83      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.58/0.83         ((r2_hidden @ X6 @ X4) | ~ (r2_hidden @ X6 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.58/0.83      inference('simplify', [status(thm)], ['22'])).
% 0.58/0.83  thf('24', plain,
% 0.58/0.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.83         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r2_hidden @ X2 @ X1))),
% 0.58/0.83      inference('sup-', [status(thm)], ['21', '23'])).
% 0.58/0.83  thf('25', plain,
% 0.58/0.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.83         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.58/0.83          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.58/0.83      inference('clc', [status(thm)], ['20', '24'])).
% 0.58/0.83  thf('26', plain,
% 0.58/0.83      (![X0 : $i]:
% 0.58/0.83         (((X0) = (k1_xboole_0))
% 0.58/0.83          | ~ (r2_hidden @ (sk_B @ X0) @ (k4_xboole_0 @ X0 @ X0)))),
% 0.58/0.83      inference('sup-', [status(thm)], ['17', '25'])).
% 0.58/0.83  thf('27', plain,
% 0.58/0.83      (![X0 : $i]:
% 0.58/0.83         (~ (r2_hidden @ (sk_B @ (k1_tarski @ X0)) @ (k1_tarski @ X0))
% 0.58/0.83          | (r2_hidden @ X0 @ (k1_tarski @ X0))
% 0.58/0.83          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.58/0.83      inference('sup-', [status(thm)], ['11', '26'])).
% 0.58/0.83  thf('28', plain,
% 0.58/0.83      (![X12 : $i]:
% 0.58/0.83         (((X12) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X12) @ X12))),
% 0.58/0.83      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.58/0.83  thf('29', plain,
% 0.58/0.83      (![X0 : $i]:
% 0.58/0.83         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.58/0.83          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.58/0.83      inference('clc', [status(thm)], ['27', '28'])).
% 0.58/0.83  thf('30', plain,
% 0.58/0.83      ((![X0 : $i]:
% 0.58/0.83          (~ (r2_hidden @ sk_A @ X0)
% 0.58/0.83           | (r2_hidden @ sk_A @ (k3_xboole_0 @ X0 @ sk_B_1))))
% 0.58/0.83         <= (((r2_hidden @ sk_A @ sk_B_1)))),
% 0.58/0.83      inference('sup-', [status(thm)], ['5', '7'])).
% 0.58/0.83  thf('31', plain,
% 0.58/0.83      (((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.58/0.83         | (r2_hidden @ sk_A @ (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1))))
% 0.58/0.83         <= (((r2_hidden @ sk_A @ sk_B_1)))),
% 0.58/0.83      inference('sup-', [status(thm)], ['29', '30'])).
% 0.58/0.83  thf('32', plain,
% 0.58/0.83      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.58/0.83      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.58/0.83  thf('33', plain,
% 0.58/0.83      (((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.58/0.83         | (r2_hidden @ sk_A @ (k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))))
% 0.58/0.83         <= (((r2_hidden @ sk_A @ sk_B_1)))),
% 0.58/0.83      inference('demod', [status(thm)], ['31', '32'])).
% 0.58/0.83  thf('34', plain,
% 0.58/0.83      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.58/0.83      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.58/0.83  thf('35', plain,
% 0.58/0.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.83         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.58/0.83          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.58/0.83      inference('clc', [status(thm)], ['20', '24'])).
% 0.58/0.83  thf('36', plain,
% 0.58/0.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.83         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.58/0.83          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.58/0.83      inference('sup-', [status(thm)], ['34', '35'])).
% 0.58/0.83  thf('37', plain,
% 0.58/0.83      (((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.58/0.83         | ~ (r2_hidden @ sk_A @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1))))
% 0.58/0.83         <= (((r2_hidden @ sk_A @ sk_B_1)))),
% 0.58/0.83      inference('sup-', [status(thm)], ['33', '36'])).
% 0.58/0.83  thf('38', plain,
% 0.58/0.83      (((~ (r2_hidden @ sk_A @ (k1_tarski @ sk_A))
% 0.58/0.83         | ((k1_tarski @ sk_A) = (k1_xboole_0))))
% 0.58/0.83         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))) & 
% 0.58/0.83             ((r2_hidden @ sk_A @ sk_B_1)))),
% 0.58/0.83      inference('sup-', [status(thm)], ['10', '37'])).
% 0.58/0.83  thf('39', plain,
% 0.58/0.83      (![X0 : $i]:
% 0.58/0.83         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.58/0.83          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.58/0.83      inference('clc', [status(thm)], ['27', '28'])).
% 0.58/0.83  thf('40', plain,
% 0.58/0.83      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 0.58/0.83         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))) & 
% 0.58/0.83             ((r2_hidden @ sk_A @ sk_B_1)))),
% 0.58/0.83      inference('clc', [status(thm)], ['38', '39'])).
% 0.58/0.83  thf(t64_zfmisc_1, axiom,
% 0.58/0.83    (![A:$i,B:$i,C:$i]:
% 0.58/0.83     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.58/0.83       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 0.58/0.83  thf('41', plain,
% 0.58/0.83      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.58/0.83         (((X26) != (X28))
% 0.58/0.83          | ~ (r2_hidden @ X26 @ (k4_xboole_0 @ X27 @ (k1_tarski @ X28))))),
% 0.58/0.83      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.58/0.83  thf('42', plain,
% 0.58/0.83      (![X27 : $i, X28 : $i]:
% 0.58/0.83         ~ (r2_hidden @ X28 @ (k4_xboole_0 @ X27 @ (k1_tarski @ X28)))),
% 0.58/0.83      inference('simplify', [status(thm)], ['41'])).
% 0.58/0.83  thf('43', plain,
% 0.58/0.83      ((![X0 : $i]: ~ (r2_hidden @ sk_A @ (k4_xboole_0 @ X0 @ k1_xboole_0)))
% 0.58/0.83         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))) & 
% 0.58/0.83             ((r2_hidden @ sk_A @ sk_B_1)))),
% 0.58/0.83      inference('sup-', [status(thm)], ['40', '42'])).
% 0.58/0.83  thf(t3_boole, axiom,
% 0.58/0.83    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.58/0.83  thf('44', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.58/0.83      inference('cnf', [status(esa)], [t3_boole])).
% 0.58/0.83  thf('45', plain,
% 0.58/0.83      ((![X0 : $i]: ~ (r2_hidden @ sk_A @ X0))
% 0.58/0.83         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))) & 
% 0.58/0.83             ((r2_hidden @ sk_A @ sk_B_1)))),
% 0.58/0.83      inference('demod', [status(thm)], ['43', '44'])).
% 0.58/0.83  thf('46', plain,
% 0.58/0.83      (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))) | 
% 0.58/0.83       ~ ((r2_hidden @ sk_A @ sk_B_1))),
% 0.58/0.83      inference('sup-', [status(thm)], ['9', '45'])).
% 0.58/0.83  thf('47', plain, (~ ((r2_hidden @ sk_A @ sk_B_1))),
% 0.58/0.83      inference('sat_resolution*', [status(thm)], ['2', '46'])).
% 0.58/0.83  thf('48', plain, (~ (r2_hidden @ sk_A @ sk_B_1)),
% 0.58/0.83      inference('simpl_trail', [status(thm)], ['1', '47'])).
% 0.58/0.83  thf('49', plain,
% 0.58/0.83      (![X31 : $i, X32 : $i]:
% 0.58/0.83         (((k4_xboole_0 @ X31 @ (k1_tarski @ X32)) = (X31))
% 0.58/0.83          | (r2_hidden @ X32 @ X31))),
% 0.58/0.83      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.58/0.83  thf('50', plain,
% 0.58/0.83      (![X12 : $i]:
% 0.58/0.83         (((X12) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X12) @ X12))),
% 0.58/0.83      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.58/0.83  thf('51', plain,
% 0.58/0.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.83         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.58/0.83          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.58/0.83      inference('clc', [status(thm)], ['20', '24'])).
% 0.58/0.83  thf('52', plain,
% 0.58/0.83      (![X0 : $i, X1 : $i]:
% 0.58/0.83         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.58/0.83          | ~ (r2_hidden @ (sk_B @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.58/0.83               (k4_xboole_0 @ X1 @ X0)))),
% 0.58/0.83      inference('sup-', [status(thm)], ['50', '51'])).
% 0.58/0.83  thf('53', plain,
% 0.58/0.83      (![X0 : $i, X1 : $i]:
% 0.58/0.83         (~ (r2_hidden @ (sk_B @ (k3_xboole_0 @ X0 @ (k1_tarski @ X1))) @ X0)
% 0.58/0.83          | (r2_hidden @ X1 @ X0)
% 0.58/0.83          | ((k3_xboole_0 @ X0 @ (k1_tarski @ X1)) = (k1_xboole_0)))),
% 0.58/0.83      inference('sup-', [status(thm)], ['49', '52'])).
% 0.58/0.83  thf('54', plain,
% 0.58/0.83      (![X12 : $i]:
% 0.58/0.83         (((X12) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X12) @ X12))),
% 0.58/0.83      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.58/0.83  thf('55', plain,
% 0.58/0.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.83         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r2_hidden @ X2 @ X1))),
% 0.58/0.83      inference('sup-', [status(thm)], ['21', '23'])).
% 0.58/0.83  thf('56', plain,
% 0.58/0.83      (![X0 : $i, X1 : $i]:
% 0.58/0.83         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.58/0.83          | (r2_hidden @ (sk_B @ (k3_xboole_0 @ X1 @ X0)) @ X1))),
% 0.58/0.83      inference('sup-', [status(thm)], ['54', '55'])).
% 0.58/0.83  thf('57', plain,
% 0.58/0.83      (![X0 : $i, X1 : $i]:
% 0.58/0.83         (((k3_xboole_0 @ X0 @ (k1_tarski @ X1)) = (k1_xboole_0))
% 0.58/0.83          | (r2_hidden @ X1 @ X0))),
% 0.58/0.83      inference('clc', [status(thm)], ['53', '56'])).
% 0.58/0.83  thf('58', plain,
% 0.58/0.83      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.58/0.83      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.58/0.83  thf('59', plain,
% 0.58/0.83      (![X13 : $i, X14 : $i]:
% 0.58/0.83         ((k4_xboole_0 @ X13 @ X14)
% 0.58/0.83           = (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)))),
% 0.58/0.83      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.58/0.83  thf('60', plain,
% 0.58/0.83      (![X0 : $i, X1 : $i]:
% 0.58/0.83         ((k4_xboole_0 @ X0 @ X1)
% 0.58/0.83           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.58/0.83      inference('sup+', [status(thm)], ['58', '59'])).
% 0.58/0.83  thf('61', plain,
% 0.58/0.83      (![X0 : $i, X1 : $i]:
% 0.58/0.83         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1)
% 0.58/0.83            = (k5_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0))
% 0.58/0.83          | (r2_hidden @ X0 @ X1))),
% 0.58/0.83      inference('sup+', [status(thm)], ['57', '60'])).
% 0.58/0.83  thf('62', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.58/0.83      inference('cnf', [status(esa)], [t3_boole])).
% 0.58/0.83  thf('63', plain,
% 0.58/0.83      (![X0 : $i, X1 : $i]:
% 0.58/0.83         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.58/0.83          | ~ (r2_hidden @ (sk_B @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.58/0.83               (k4_xboole_0 @ X1 @ X0)))),
% 0.58/0.83      inference('sup-', [status(thm)], ['50', '51'])).
% 0.58/0.83  thf('64', plain,
% 0.58/0.83      (![X0 : $i]:
% 0.58/0.83         (~ (r2_hidden @ (sk_B @ (k3_xboole_0 @ X0 @ k1_xboole_0)) @ X0)
% 0.58/0.83          | ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.58/0.83      inference('sup-', [status(thm)], ['62', '63'])).
% 0.58/0.83  thf('65', plain,
% 0.58/0.83      (![X0 : $i, X1 : $i]:
% 0.58/0.83         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.58/0.83          | (r2_hidden @ (sk_B @ (k3_xboole_0 @ X1 @ X0)) @ X1))),
% 0.58/0.83      inference('sup-', [status(thm)], ['54', '55'])).
% 0.58/0.83  thf('66', plain,
% 0.58/0.83      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.58/0.83      inference('clc', [status(thm)], ['64', '65'])).
% 0.58/0.83  thf('67', plain,
% 0.58/0.83      (![X13 : $i, X14 : $i]:
% 0.58/0.83         ((k4_xboole_0 @ X13 @ X14)
% 0.58/0.83           = (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)))),
% 0.58/0.83      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.58/0.83  thf('68', plain,
% 0.58/0.83      (![X0 : $i]:
% 0.58/0.83         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.58/0.83      inference('sup+', [status(thm)], ['66', '67'])).
% 0.58/0.83  thf('69', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.58/0.83      inference('cnf', [status(esa)], [t3_boole])).
% 0.58/0.83  thf('70', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.58/0.83      inference('sup+', [status(thm)], ['68', '69'])).
% 0.58/0.83  thf('71', plain,
% 0.58/0.83      (![X0 : $i, X1 : $i]:
% 0.58/0.83         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_tarski @ X0))
% 0.58/0.83          | (r2_hidden @ X0 @ X1))),
% 0.58/0.83      inference('demod', [status(thm)], ['61', '70'])).
% 0.58/0.83  thf('72', plain,
% 0.58/0.83      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) != (k1_tarski @ sk_A)))
% 0.58/0.83         <= (~
% 0.58/0.83             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 0.58/0.83      inference('split', [status(esa)], ['3'])).
% 0.58/0.83  thf('73', plain,
% 0.58/0.83      (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))) | 
% 0.58/0.83       ((r2_hidden @ sk_A @ sk_B_1))),
% 0.58/0.83      inference('split', [status(esa)], ['3'])).
% 0.58/0.83  thf('74', plain,
% 0.58/0.83      (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A)))),
% 0.58/0.83      inference('sat_resolution*', [status(thm)], ['2', '46', '73'])).
% 0.58/0.83  thf('75', plain,
% 0.58/0.83      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) != (k1_tarski @ sk_A))),
% 0.58/0.83      inference('simpl_trail', [status(thm)], ['72', '74'])).
% 0.58/0.83  thf('76', plain,
% 0.58/0.83      ((((k1_tarski @ sk_A) != (k1_tarski @ sk_A))
% 0.58/0.83        | (r2_hidden @ sk_A @ sk_B_1))),
% 0.58/0.83      inference('sup-', [status(thm)], ['71', '75'])).
% 0.58/0.83  thf('77', plain, ((r2_hidden @ sk_A @ sk_B_1)),
% 0.58/0.83      inference('simplify', [status(thm)], ['76'])).
% 0.58/0.83  thf('78', plain, ($false), inference('demod', [status(thm)], ['48', '77'])).
% 0.58/0.83  
% 0.58/0.83  % SZS output end Refutation
% 0.58/0.83  
% 0.58/0.83  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
