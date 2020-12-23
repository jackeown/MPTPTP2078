%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7ncjg3S3DG

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:17 EST 2020

% Result     : Theorem 1.03s
% Output     : Refutation 1.03s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 518 expanded)
%              Number of leaves         :   19 ( 157 expanded)
%              Depth                    :   24
%              Number of atoms          :  998 (4751 expanded)
%              Number of equality atoms :   81 ( 364 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

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
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
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
        | ( r2_hidden @ sk_A @ ( k3_xboole_0 @ X0 @ sk_B ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,
    ( ( r2_hidden @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_B ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['4','8'])).

thf('10',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('11',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k3_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('12',plain,(
    ! [X16: $i] :
      ( r1_tarski @ k1_xboole_0 @ X16 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('13',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_xboole_0 @ X14 @ X15 )
        = X14 )
      | ~ ( r1_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('17',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('18',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r2_hidden @ X8 @ X10 )
      | ~ ( r2_hidden @ X8 @ ( k5_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('21',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('22',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['19','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['16','24'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('26',plain,(
    ! [X17: $i] :
      ( ( k4_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1
        = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('32',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k4_xboole_0 @ X29 @ ( k1_tarski @ X30 ) )
        = X29 )
      | ( r2_hidden @ X30 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('33',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k3_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['33'])).

thf('35',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k3_xboole_0 @ X3 @ X4 ) )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X0 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k3_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['37','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['19','23'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['32','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['31','44'])).

thf('46',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ sk_A @ X0 )
        | ( r2_hidden @ sk_A @ ( k3_xboole_0 @ X0 @ sk_B ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('47',plain,
    ( ( ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ( r2_hidden @ sk_A @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('49',plain,
    ( ( ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ( r2_hidden @ sk_A @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['19','23'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf('54',plain,
    ( ( ~ ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['31','44'])).

thf('56',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ X28 @ X29 )
      | ( ( k4_xboole_0 @ X29 @ ( k1_tarski @ X28 ) )
       != X29 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('58',plain,
    ( ! [X0: $i] :
        ( ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
         != X0 )
        | ~ ( r2_hidden @ sk_A @ X0 ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X17: $i] :
      ( ( k4_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('60',plain,
    ( ! [X0: $i] :
        ( ( X0 != X0 )
        | ~ ( r2_hidden @ sk_A @ X0 ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ sk_A @ X0 )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != ( k1_tarski @ sk_A ) )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['9','61'])).

thf('63',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['2','62'])).

thf('64',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','63'])).

thf('65',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k4_xboole_0 @ X29 @ ( k1_tarski @ X30 ) )
        = X29 )
      | ( r2_hidden @ X30 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('66',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k3_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('67',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['27'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X1 )
      | ( X1
        = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['19','23'])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 @ X2 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) @ k1_xboole_0 @ X2 ) @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( ( k3_xboole_0 @ X0 @ ( k1_tarski @ X1 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['65','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ ( k1_tarski @ X1 ) )
        = k1_xboole_0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference(clc,[status(thm)],['73','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('79',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['77','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X17: $i] :
      ( ( k4_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['81','86'])).

thf('88',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('89',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf('90',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','62','89'])).

thf('91',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['88','90'])).

thf('92',plain,
    ( ( ( k1_tarski @ sk_A )
     != ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['87','91'])).

thf('93',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,(
    $false ),
    inference(demod,[status(thm)],['64','93'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7ncjg3S3DG
% 0.15/0.35  % Computer   : n019.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 13:02:22 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.35  % Running in FO mode
% 1.03/1.19  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.03/1.19  % Solved by: fo/fo7.sh
% 1.03/1.19  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.03/1.19  % done 1228 iterations in 0.727s
% 1.03/1.19  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.03/1.19  % SZS output start Refutation
% 1.03/1.19  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.03/1.19  thf(sk_B_type, type, sk_B: $i).
% 1.03/1.19  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.03/1.19  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 1.03/1.19  thf(sk_A_type, type, sk_A: $i).
% 1.03/1.19  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.03/1.19  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.03/1.19  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.03/1.19  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.03/1.19  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.03/1.19  thf(t67_zfmisc_1, conjecture,
% 1.03/1.19    (![A:$i,B:$i]:
% 1.03/1.19     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 1.03/1.19       ( ~( r2_hidden @ A @ B ) ) ))).
% 1.03/1.19  thf(zf_stmt_0, negated_conjecture,
% 1.03/1.19    (~( ![A:$i,B:$i]:
% 1.03/1.19        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 1.03/1.19          ( ~( r2_hidden @ A @ B ) ) ) )),
% 1.03/1.19    inference('cnf.neg', [status(esa)], [t67_zfmisc_1])).
% 1.03/1.19  thf('0', plain,
% 1.03/1.19      ((~ (r2_hidden @ sk_A @ sk_B)
% 1.03/1.19        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A)))),
% 1.03/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.19  thf('1', plain,
% 1.03/1.19      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 1.03/1.19      inference('split', [status(esa)], ['0'])).
% 1.03/1.19  thf('2', plain,
% 1.03/1.19      (~ ((r2_hidden @ sk_A @ sk_B)) | 
% 1.03/1.19       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A)))),
% 1.03/1.19      inference('split', [status(esa)], ['0'])).
% 1.03/1.19  thf('3', plain,
% 1.03/1.19      (((r2_hidden @ sk_A @ sk_B)
% 1.03/1.19        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A)))),
% 1.03/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.19  thf('4', plain,
% 1.03/1.19      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 1.03/1.19      inference('split', [status(esa)], ['3'])).
% 1.03/1.19  thf('5', plain,
% 1.03/1.19      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 1.03/1.19      inference('split', [status(esa)], ['3'])).
% 1.03/1.19  thf(d4_xboole_0, axiom,
% 1.03/1.19    (![A:$i,B:$i,C:$i]:
% 1.03/1.19     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 1.03/1.19       ( ![D:$i]:
% 1.03/1.19         ( ( r2_hidden @ D @ C ) <=>
% 1.03/1.19           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 1.03/1.19  thf('6', plain,
% 1.03/1.19      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 1.03/1.19         (~ (r2_hidden @ X2 @ X3)
% 1.03/1.19          | ~ (r2_hidden @ X2 @ X4)
% 1.03/1.19          | (r2_hidden @ X2 @ X5)
% 1.03/1.19          | ((X5) != (k3_xboole_0 @ X3 @ X4)))),
% 1.03/1.19      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.03/1.19  thf('7', plain,
% 1.03/1.19      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.03/1.19         ((r2_hidden @ X2 @ (k3_xboole_0 @ X3 @ X4))
% 1.03/1.19          | ~ (r2_hidden @ X2 @ X4)
% 1.03/1.19          | ~ (r2_hidden @ X2 @ X3))),
% 1.03/1.19      inference('simplify', [status(thm)], ['6'])).
% 1.03/1.19  thf('8', plain,
% 1.03/1.19      ((![X0 : $i]:
% 1.03/1.19          (~ (r2_hidden @ sk_A @ X0)
% 1.03/1.19           | (r2_hidden @ sk_A @ (k3_xboole_0 @ X0 @ sk_B))))
% 1.03/1.19         <= (((r2_hidden @ sk_A @ sk_B)))),
% 1.03/1.19      inference('sup-', [status(thm)], ['5', '7'])).
% 1.03/1.19  thf('9', plain,
% 1.03/1.19      (((r2_hidden @ sk_A @ (k3_xboole_0 @ sk_B @ sk_B)))
% 1.03/1.19         <= (((r2_hidden @ sk_A @ sk_B)))),
% 1.03/1.19      inference('sup-', [status(thm)], ['4', '8'])).
% 1.03/1.19  thf('10', plain,
% 1.03/1.19      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A)))
% 1.03/1.19         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 1.03/1.19      inference('split', [status(esa)], ['0'])).
% 1.03/1.19  thf('11', plain,
% 1.03/1.19      (![X3 : $i, X4 : $i, X7 : $i]:
% 1.03/1.19         (((X7) = (k3_xboole_0 @ X3 @ X4))
% 1.03/1.19          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 1.03/1.19          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 1.03/1.19      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.03/1.19  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 1.03/1.19  thf('12', plain, (![X16 : $i]: (r1_tarski @ k1_xboole_0 @ X16)),
% 1.03/1.19      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.03/1.19  thf(t28_xboole_1, axiom,
% 1.03/1.19    (![A:$i,B:$i]:
% 1.03/1.19     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.03/1.19  thf('13', plain,
% 1.03/1.19      (![X14 : $i, X15 : $i]:
% 1.03/1.19         (((k3_xboole_0 @ X14 @ X15) = (X14)) | ~ (r1_tarski @ X14 @ X15))),
% 1.03/1.19      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.03/1.19  thf('14', plain,
% 1.03/1.19      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.03/1.19      inference('sup-', [status(thm)], ['12', '13'])).
% 1.03/1.19  thf(commutativity_k3_xboole_0, axiom,
% 1.03/1.19    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.03/1.19  thf('15', plain,
% 1.03/1.19      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.03/1.19      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.03/1.19  thf('16', plain,
% 1.03/1.19      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.03/1.19      inference('sup+', [status(thm)], ['14', '15'])).
% 1.03/1.19  thf(t100_xboole_1, axiom,
% 1.03/1.19    (![A:$i,B:$i]:
% 1.03/1.19     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.03/1.19  thf('17', plain,
% 1.03/1.19      (![X12 : $i, X13 : $i]:
% 1.03/1.19         ((k4_xboole_0 @ X12 @ X13)
% 1.03/1.19           = (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)))),
% 1.03/1.19      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.03/1.19  thf(t1_xboole_0, axiom,
% 1.03/1.19    (![A:$i,B:$i,C:$i]:
% 1.03/1.19     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 1.03/1.19       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 1.03/1.19  thf('18', plain,
% 1.03/1.19      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.03/1.19         (~ (r2_hidden @ X8 @ X9)
% 1.03/1.19          | ~ (r2_hidden @ X8 @ X10)
% 1.03/1.19          | ~ (r2_hidden @ X8 @ (k5_xboole_0 @ X9 @ X10)))),
% 1.03/1.19      inference('cnf', [status(esa)], [t1_xboole_0])).
% 1.03/1.19  thf('19', plain,
% 1.03/1.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.03/1.19         (~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 1.03/1.19          | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 1.03/1.19          | ~ (r2_hidden @ X2 @ X1))),
% 1.03/1.19      inference('sup-', [status(thm)], ['17', '18'])).
% 1.03/1.19  thf('20', plain,
% 1.03/1.19      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.03/1.19      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.03/1.19  thf('21', plain,
% 1.03/1.19      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.03/1.19         (~ (r2_hidden @ X6 @ X5)
% 1.03/1.19          | (r2_hidden @ X6 @ X4)
% 1.03/1.19          | ((X5) != (k3_xboole_0 @ X3 @ X4)))),
% 1.03/1.19      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.03/1.19  thf('22', plain,
% 1.03/1.19      (![X3 : $i, X4 : $i, X6 : $i]:
% 1.03/1.19         ((r2_hidden @ X6 @ X4) | ~ (r2_hidden @ X6 @ (k3_xboole_0 @ X3 @ X4)))),
% 1.03/1.19      inference('simplify', [status(thm)], ['21'])).
% 1.03/1.19  thf('23', plain,
% 1.03/1.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.03/1.19         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r2_hidden @ X2 @ X1))),
% 1.03/1.19      inference('sup-', [status(thm)], ['20', '22'])).
% 1.03/1.19  thf('24', plain,
% 1.03/1.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.03/1.19         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 1.03/1.19          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.03/1.19      inference('clc', [status(thm)], ['19', '23'])).
% 1.03/1.19  thf('25', plain,
% 1.03/1.19      (![X0 : $i, X1 : $i]:
% 1.03/1.19         (~ (r2_hidden @ X1 @ k1_xboole_0)
% 1.03/1.19          | ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ k1_xboole_0)))),
% 1.03/1.19      inference('sup-', [status(thm)], ['16', '24'])).
% 1.03/1.19  thf(t3_boole, axiom,
% 1.03/1.19    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.03/1.19  thf('26', plain, (![X17 : $i]: ((k4_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 1.03/1.19      inference('cnf', [status(esa)], [t3_boole])).
% 1.03/1.19  thf('27', plain,
% 1.03/1.19      (![X0 : $i, X1 : $i]:
% 1.03/1.19         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r2_hidden @ X1 @ X0))),
% 1.03/1.19      inference('demod', [status(thm)], ['25', '26'])).
% 1.03/1.19  thf('28', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 1.03/1.19      inference('condensation', [status(thm)], ['27'])).
% 1.03/1.19  thf('29', plain,
% 1.03/1.19      (![X0 : $i, X1 : $i]:
% 1.03/1.19         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 1.03/1.19          | ((X1) = (k3_xboole_0 @ k1_xboole_0 @ X0)))),
% 1.03/1.19      inference('sup-', [status(thm)], ['11', '28'])).
% 1.03/1.19  thf('30', plain,
% 1.03/1.19      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.03/1.19      inference('sup-', [status(thm)], ['12', '13'])).
% 1.03/1.19  thf('31', plain,
% 1.03/1.19      (![X0 : $i, X1 : $i]:
% 1.03/1.19         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 1.03/1.19          | ((X1) = (k1_xboole_0)))),
% 1.03/1.19      inference('demod', [status(thm)], ['29', '30'])).
% 1.03/1.19  thf(t65_zfmisc_1, axiom,
% 1.03/1.19    (![A:$i,B:$i]:
% 1.03/1.19     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 1.03/1.19       ( ~( r2_hidden @ B @ A ) ) ))).
% 1.03/1.19  thf('32', plain,
% 1.03/1.19      (![X29 : $i, X30 : $i]:
% 1.03/1.19         (((k4_xboole_0 @ X29 @ (k1_tarski @ X30)) = (X29))
% 1.03/1.19          | (r2_hidden @ X30 @ X29))),
% 1.03/1.19      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 1.03/1.19  thf('33', plain,
% 1.03/1.19      (![X3 : $i, X4 : $i, X7 : $i]:
% 1.03/1.19         (((X7) = (k3_xboole_0 @ X3 @ X4))
% 1.03/1.19          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 1.03/1.19          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 1.03/1.19      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.03/1.19  thf('34', plain,
% 1.03/1.19      (![X0 : $i, X1 : $i]:
% 1.03/1.19         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 1.03/1.19          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 1.03/1.19      inference('eq_fact', [status(thm)], ['33'])).
% 1.03/1.19  thf('35', plain,
% 1.03/1.19      (![X3 : $i, X4 : $i, X7 : $i]:
% 1.03/1.19         (((X7) = (k3_xboole_0 @ X3 @ X4))
% 1.03/1.19          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 1.03/1.19          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 1.03/1.19          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 1.03/1.19      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.03/1.19  thf('36', plain,
% 1.03/1.19      (![X0 : $i]:
% 1.03/1.19         (((X0) = (k3_xboole_0 @ X0 @ X0))
% 1.03/1.19          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X0) @ X0)
% 1.03/1.19          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X0) @ X0)
% 1.03/1.19          | ((X0) = (k3_xboole_0 @ X0 @ X0)))),
% 1.03/1.19      inference('sup-', [status(thm)], ['34', '35'])).
% 1.03/1.19  thf('37', plain,
% 1.03/1.19      (![X0 : $i]:
% 1.03/1.19         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X0) @ X0)
% 1.03/1.19          | ((X0) = (k3_xboole_0 @ X0 @ X0)))),
% 1.03/1.19      inference('simplify', [status(thm)], ['36'])).
% 1.03/1.19  thf('38', plain,
% 1.03/1.19      (![X3 : $i, X4 : $i, X7 : $i]:
% 1.03/1.19         (((X7) = (k3_xboole_0 @ X3 @ X4))
% 1.03/1.19          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 1.03/1.19          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 1.03/1.19      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.03/1.19  thf('39', plain,
% 1.03/1.19      (![X0 : $i, X1 : $i]:
% 1.03/1.19         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 1.03/1.19          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 1.03/1.19      inference('eq_fact', [status(thm)], ['38'])).
% 1.03/1.19  thf('40', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 1.03/1.19      inference('clc', [status(thm)], ['37', '39'])).
% 1.03/1.19  thf('41', plain,
% 1.03/1.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.03/1.19         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 1.03/1.19          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.03/1.19      inference('clc', [status(thm)], ['19', '23'])).
% 1.03/1.19  thf('42', plain,
% 1.03/1.19      (![X0 : $i, X1 : $i]:
% 1.03/1.19         (~ (r2_hidden @ X1 @ X0)
% 1.03/1.19          | ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0)))),
% 1.03/1.19      inference('sup-', [status(thm)], ['40', '41'])).
% 1.03/1.19  thf('43', plain,
% 1.03/1.19      (![X0 : $i, X1 : $i]:
% 1.03/1.19         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 1.03/1.19          | (r2_hidden @ X0 @ (k1_tarski @ X0))
% 1.03/1.19          | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 1.03/1.19      inference('sup-', [status(thm)], ['32', '42'])).
% 1.03/1.19  thf('44', plain,
% 1.03/1.19      (![X0 : $i, X1 : $i]:
% 1.03/1.19         ((r2_hidden @ X0 @ (k1_tarski @ X0))
% 1.03/1.19          | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 1.03/1.19      inference('simplify', [status(thm)], ['43'])).
% 1.03/1.19  thf('45', plain,
% 1.03/1.19      (![X0 : $i]:
% 1.03/1.19         (((k1_tarski @ X0) = (k1_xboole_0))
% 1.03/1.19          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 1.03/1.19      inference('sup-', [status(thm)], ['31', '44'])).
% 1.03/1.19  thf('46', plain,
% 1.03/1.19      ((![X0 : $i]:
% 1.03/1.19          (~ (r2_hidden @ sk_A @ X0)
% 1.03/1.19           | (r2_hidden @ sk_A @ (k3_xboole_0 @ X0 @ sk_B))))
% 1.03/1.19         <= (((r2_hidden @ sk_A @ sk_B)))),
% 1.03/1.19      inference('sup-', [status(thm)], ['5', '7'])).
% 1.03/1.19  thf('47', plain,
% 1.03/1.19      (((((k1_tarski @ sk_A) = (k1_xboole_0))
% 1.03/1.19         | (r2_hidden @ sk_A @ (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))))
% 1.03/1.19         <= (((r2_hidden @ sk_A @ sk_B)))),
% 1.03/1.19      inference('sup-', [status(thm)], ['45', '46'])).
% 1.03/1.19  thf('48', plain,
% 1.03/1.19      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.03/1.19      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.03/1.19  thf('49', plain,
% 1.03/1.19      (((((k1_tarski @ sk_A) = (k1_xboole_0))
% 1.03/1.19         | (r2_hidden @ sk_A @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))
% 1.03/1.19         <= (((r2_hidden @ sk_A @ sk_B)))),
% 1.03/1.19      inference('demod', [status(thm)], ['47', '48'])).
% 1.03/1.19  thf('50', plain,
% 1.03/1.19      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.03/1.19      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.03/1.19  thf('51', plain,
% 1.03/1.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.03/1.19         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 1.03/1.19          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.03/1.19      inference('clc', [status(thm)], ['19', '23'])).
% 1.03/1.19  thf('52', plain,
% 1.03/1.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.03/1.19         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 1.03/1.19          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X0 @ X1)))),
% 1.03/1.19      inference('sup-', [status(thm)], ['50', '51'])).
% 1.03/1.19  thf('53', plain,
% 1.03/1.19      (((((k1_tarski @ sk_A) = (k1_xboole_0))
% 1.03/1.19         | ~ (r2_hidden @ sk_A @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))))
% 1.03/1.19         <= (((r2_hidden @ sk_A @ sk_B)))),
% 1.03/1.19      inference('sup-', [status(thm)], ['49', '52'])).
% 1.03/1.19  thf('54', plain,
% 1.03/1.19      (((~ (r2_hidden @ sk_A @ (k1_tarski @ sk_A))
% 1.03/1.19         | ((k1_tarski @ sk_A) = (k1_xboole_0))))
% 1.03/1.19         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 1.03/1.19             ((r2_hidden @ sk_A @ sk_B)))),
% 1.03/1.19      inference('sup-', [status(thm)], ['10', '53'])).
% 1.03/1.19  thf('55', plain,
% 1.03/1.19      (![X0 : $i]:
% 1.03/1.19         (((k1_tarski @ X0) = (k1_xboole_0))
% 1.03/1.19          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 1.03/1.19      inference('sup-', [status(thm)], ['31', '44'])).
% 1.03/1.19  thf('56', plain,
% 1.03/1.19      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 1.03/1.19         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 1.03/1.19             ((r2_hidden @ sk_A @ sk_B)))),
% 1.03/1.19      inference('clc', [status(thm)], ['54', '55'])).
% 1.03/1.19  thf('57', plain,
% 1.03/1.19      (![X28 : $i, X29 : $i]:
% 1.03/1.19         (~ (r2_hidden @ X28 @ X29)
% 1.03/1.19          | ((k4_xboole_0 @ X29 @ (k1_tarski @ X28)) != (X29)))),
% 1.03/1.19      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 1.03/1.19  thf('58', plain,
% 1.03/1.19      ((![X0 : $i]:
% 1.03/1.19          (((k4_xboole_0 @ X0 @ k1_xboole_0) != (X0))
% 1.03/1.19           | ~ (r2_hidden @ sk_A @ X0)))
% 1.03/1.19         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 1.03/1.19             ((r2_hidden @ sk_A @ sk_B)))),
% 1.03/1.19      inference('sup-', [status(thm)], ['56', '57'])).
% 1.03/1.19  thf('59', plain, (![X17 : $i]: ((k4_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 1.03/1.19      inference('cnf', [status(esa)], [t3_boole])).
% 1.03/1.19  thf('60', plain,
% 1.03/1.19      ((![X0 : $i]: (((X0) != (X0)) | ~ (r2_hidden @ sk_A @ X0)))
% 1.03/1.19         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 1.03/1.19             ((r2_hidden @ sk_A @ sk_B)))),
% 1.03/1.19      inference('demod', [status(thm)], ['58', '59'])).
% 1.03/1.19  thf('61', plain,
% 1.03/1.19      ((![X0 : $i]: ~ (r2_hidden @ sk_A @ X0))
% 1.03/1.19         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 1.03/1.19             ((r2_hidden @ sk_A @ sk_B)))),
% 1.03/1.19      inference('simplify', [status(thm)], ['60'])).
% 1.03/1.19  thf('62', plain,
% 1.03/1.19      (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) | 
% 1.03/1.19       ~ ((r2_hidden @ sk_A @ sk_B))),
% 1.03/1.19      inference('sup-', [status(thm)], ['9', '61'])).
% 1.03/1.19  thf('63', plain, (~ ((r2_hidden @ sk_A @ sk_B))),
% 1.03/1.19      inference('sat_resolution*', [status(thm)], ['2', '62'])).
% 1.03/1.19  thf('64', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 1.03/1.19      inference('simpl_trail', [status(thm)], ['1', '63'])).
% 1.03/1.19  thf('65', plain,
% 1.03/1.19      (![X29 : $i, X30 : $i]:
% 1.03/1.19         (((k4_xboole_0 @ X29 @ (k1_tarski @ X30)) = (X29))
% 1.03/1.19          | (r2_hidden @ X30 @ X29))),
% 1.03/1.19      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 1.03/1.19  thf('66', plain,
% 1.03/1.19      (![X3 : $i, X4 : $i, X7 : $i]:
% 1.03/1.19         (((X7) = (k3_xboole_0 @ X3 @ X4))
% 1.03/1.19          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 1.03/1.19          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 1.03/1.19      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.03/1.19  thf('67', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 1.03/1.19      inference('condensation', [status(thm)], ['27'])).
% 1.03/1.19  thf('68', plain,
% 1.03/1.19      (![X0 : $i, X1 : $i]:
% 1.03/1.19         ((r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X1)
% 1.03/1.19          | ((X1) = (k3_xboole_0 @ X0 @ k1_xboole_0)))),
% 1.03/1.19      inference('sup-', [status(thm)], ['66', '67'])).
% 1.03/1.19  thf('69', plain,
% 1.03/1.19      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.03/1.19      inference('sup+', [status(thm)], ['14', '15'])).
% 1.03/1.19  thf('70', plain,
% 1.03/1.19      (![X0 : $i, X1 : $i]:
% 1.03/1.19         ((r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X1)
% 1.03/1.19          | ((X1) = (k1_xboole_0)))),
% 1.03/1.19      inference('demod', [status(thm)], ['68', '69'])).
% 1.03/1.19  thf('71', plain,
% 1.03/1.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.03/1.19         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 1.03/1.19          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.03/1.19      inference('clc', [status(thm)], ['19', '23'])).
% 1.03/1.19  thf('72', plain,
% 1.03/1.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.03/1.19         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 1.03/1.19          | ~ (r2_hidden @ 
% 1.03/1.19               (sk_D @ (k3_xboole_0 @ X1 @ X0) @ k1_xboole_0 @ X2) @ 
% 1.03/1.19               (k4_xboole_0 @ X1 @ X0)))),
% 1.03/1.19      inference('sup-', [status(thm)], ['70', '71'])).
% 1.03/1.19  thf('73', plain,
% 1.03/1.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.03/1.19         (~ (r2_hidden @ 
% 1.03/1.19             (sk_D @ (k3_xboole_0 @ X0 @ (k1_tarski @ X1)) @ k1_xboole_0 @ X2) @ 
% 1.03/1.19             X0)
% 1.03/1.19          | (r2_hidden @ X1 @ X0)
% 1.03/1.19          | ((k3_xboole_0 @ X0 @ (k1_tarski @ X1)) = (k1_xboole_0)))),
% 1.03/1.19      inference('sup-', [status(thm)], ['65', '72'])).
% 1.03/1.19  thf('74', plain,
% 1.03/1.19      (![X0 : $i, X1 : $i]:
% 1.03/1.19         ((r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X1)
% 1.03/1.19          | ((X1) = (k1_xboole_0)))),
% 1.03/1.19      inference('demod', [status(thm)], ['68', '69'])).
% 1.03/1.19  thf('75', plain,
% 1.03/1.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.03/1.19         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r2_hidden @ X2 @ X1))),
% 1.03/1.19      inference('sup-', [status(thm)], ['20', '22'])).
% 1.03/1.19  thf('76', plain,
% 1.03/1.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.03/1.19         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 1.03/1.19          | (r2_hidden @ (sk_D @ (k3_xboole_0 @ X1 @ X0) @ k1_xboole_0 @ X2) @ 
% 1.03/1.19             X1))),
% 1.03/1.19      inference('sup-', [status(thm)], ['74', '75'])).
% 1.03/1.19  thf('77', plain,
% 1.03/1.19      (![X0 : $i, X1 : $i]:
% 1.03/1.19         (((k3_xboole_0 @ X0 @ (k1_tarski @ X1)) = (k1_xboole_0))
% 1.03/1.19          | (r2_hidden @ X1 @ X0))),
% 1.03/1.19      inference('clc', [status(thm)], ['73', '76'])).
% 1.03/1.19  thf('78', plain,
% 1.03/1.19      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.03/1.19      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.03/1.19  thf('79', plain,
% 1.03/1.19      (![X12 : $i, X13 : $i]:
% 1.03/1.19         ((k4_xboole_0 @ X12 @ X13)
% 1.03/1.19           = (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)))),
% 1.03/1.19      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.03/1.19  thf('80', plain,
% 1.03/1.19      (![X0 : $i, X1 : $i]:
% 1.03/1.19         ((k4_xboole_0 @ X0 @ X1)
% 1.03/1.19           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.03/1.19      inference('sup+', [status(thm)], ['78', '79'])).
% 1.03/1.19  thf('81', plain,
% 1.03/1.19      (![X0 : $i, X1 : $i]:
% 1.03/1.19         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1)
% 1.03/1.19            = (k5_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0))
% 1.03/1.19          | (r2_hidden @ X0 @ X1))),
% 1.03/1.19      inference('sup+', [status(thm)], ['77', '80'])).
% 1.03/1.19  thf('82', plain,
% 1.03/1.19      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.03/1.19      inference('sup-', [status(thm)], ['12', '13'])).
% 1.03/1.19  thf('83', plain,
% 1.03/1.19      (![X0 : $i, X1 : $i]:
% 1.03/1.19         ((k4_xboole_0 @ X0 @ X1)
% 1.03/1.19           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.03/1.19      inference('sup+', [status(thm)], ['78', '79'])).
% 1.03/1.19  thf('84', plain,
% 1.03/1.19      (![X0 : $i]:
% 1.03/1.19         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.03/1.19      inference('sup+', [status(thm)], ['82', '83'])).
% 1.03/1.19  thf('85', plain, (![X17 : $i]: ((k4_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 1.03/1.19      inference('cnf', [status(esa)], [t3_boole])).
% 1.03/1.19  thf('86', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.03/1.19      inference('sup+', [status(thm)], ['84', '85'])).
% 1.03/1.19  thf('87', plain,
% 1.03/1.19      (![X0 : $i, X1 : $i]:
% 1.03/1.19         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_tarski @ X0))
% 1.03/1.19          | (r2_hidden @ X0 @ X1))),
% 1.03/1.19      inference('demod', [status(thm)], ['81', '86'])).
% 1.03/1.19  thf('88', plain,
% 1.03/1.19      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A)))
% 1.03/1.19         <= (~
% 1.03/1.19             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 1.03/1.19      inference('split', [status(esa)], ['3'])).
% 1.03/1.19  thf('89', plain,
% 1.03/1.19      (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) | 
% 1.03/1.19       ((r2_hidden @ sk_A @ sk_B))),
% 1.03/1.19      inference('split', [status(esa)], ['3'])).
% 1.03/1.19  thf('90', plain,
% 1.03/1.19      (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A)))),
% 1.03/1.19      inference('sat_resolution*', [status(thm)], ['2', '62', '89'])).
% 1.03/1.19  thf('91', plain,
% 1.03/1.19      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A))),
% 1.03/1.19      inference('simpl_trail', [status(thm)], ['88', '90'])).
% 1.03/1.19  thf('92', plain,
% 1.03/1.19      ((((k1_tarski @ sk_A) != (k1_tarski @ sk_A)) | (r2_hidden @ sk_A @ sk_B))),
% 1.03/1.19      inference('sup-', [status(thm)], ['87', '91'])).
% 1.03/1.19  thf('93', plain, ((r2_hidden @ sk_A @ sk_B)),
% 1.03/1.19      inference('simplify', [status(thm)], ['92'])).
% 1.03/1.19  thf('94', plain, ($false), inference('demod', [status(thm)], ['64', '93'])).
% 1.03/1.19  
% 1.03/1.19  % SZS output end Refutation
% 1.03/1.19  
% 1.03/1.20  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
