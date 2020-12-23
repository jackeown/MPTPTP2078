%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.H62nWWXIsW

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:23 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 230 expanded)
%              Number of leaves         :   28 (  74 expanded)
%              Depth                    :   13
%              Number of atoms          :  654 (1828 expanded)
%              Number of equality atoms :   60 ( 162 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(t38_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) )
      <=> ( B
          = ( k1_subset_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) )
        <=> ( B
            = ( k1_subset_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t38_subset_1])).

thf('0',plain,
    ( ( sk_B_1
      = ( k1_subset_1 @ sk_A ) )
    | ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
   <= ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('2',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k3_xboole_0 @ X22 @ X23 )
        = X22 )
      | ~ ( r1_tarski @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('3',plain,
    ( ( ( k3_xboole_0 @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
      = sk_B_1 )
   <= ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X36: $i,X37: $i] :
      ( ( ( k3_subset_1 @ X36 @ X37 )
        = ( k4_xboole_0 @ X36 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('6',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( ( k3_xboole_0 @ sk_B_1 @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) )
      = sk_B_1 )
   <= ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['3','6'])).

thf('8',plain,
    ( ( sk_B_1
     != ( k1_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( sk_B_1
     != ( k1_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['8'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('10',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('11',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k3_xboole_0 @ X22 @ X23 )
        = X22 )
      | ~ ( r1_tarski @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('16',plain,(
    ! [X12: $i,X14: $i] :
      ( ( r1_xboole_0 @ X12 @ X14 )
      | ( ( k3_xboole_0 @ X12 @ X14 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('20',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

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

thf('21',plain,(
    ! [X15: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X17 @ X15 )
      | ~ ( r2_hidden @ X17 @ X18 )
      | ~ ( r1_xboole_0 @ X15 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['18','24'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('26',plain,(
    ! [X35: $i] :
      ( ( k1_subset_1 @ X35 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('27',plain,
    ( ( sk_B_1
      = ( k1_subset_1 @ sk_A ) )
   <= ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('28',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
   <= ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X36: $i,X37: $i] :
      ( ( ( k3_subset_1 @ X36 @ X37 )
        = ( k4_xboole_0 @ X36 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('32',plain,
    ( ( ( k3_subset_1 @ sk_A @ k1_xboole_0 )
      = ( k4_xboole_0 @ sk_A @ k1_xboole_0 ) )
   <= ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('34',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
   <= ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['8'])).

thf('35',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ k1_xboole_0 ) )
   <= ( ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
      & ( sk_B_1
        = ( k1_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('37',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k3_subset_1 @ sk_A @ k1_xboole_0 ) )
   <= ( ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
      & ( sk_B_1
        = ( k1_subset_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k4_xboole_0 @ sk_A @ k1_xboole_0 ) )
   <= ( ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
      & ( sk_B_1
        = ( k1_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['32','37'])).

thf('39',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    | ( sk_B_1
     != ( k1_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','38'])).

thf('40',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    | ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('41',plain,(
    r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['9','39','40'])).

thf('42',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) )
    = sk_B_1 ),
    inference(simpl_trail,[status(thm)],['7','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('44',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X32 @ X33 )
      | ( r2_hidden @ X32 @ X33 )
      | ( v1_xboole_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('45',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('46',plain,(
    ! [X40: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('47',plain,(
    r2_hidden @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['45','46'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('48',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( r2_hidden @ X30 @ X29 )
      | ( r1_tarski @ X30 @ X28 )
      | ( X29
       != ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('49',plain,(
    ! [X28: $i,X30: $i] :
      ( ( r1_tarski @ X30 @ X28 )
      | ~ ( r2_hidden @ X30 @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    r1_tarski @ sk_B_1 @ sk_A ),
    inference('sup-',[status(thm)],['47','49'])).

thf('51',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k3_xboole_0 @ X22 @ X23 )
        = X22 )
      | ~ ( r1_tarski @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('52',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_A )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['50','51'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('54',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B_1 )
    = sk_B_1 ),
    inference(demod,[status(thm)],['52','53'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('55',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ X20 @ ( k3_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('56',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
    = ( k5_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ ( k5_xboole_0 @ sk_A @ sk_B_1 ) )
    = sk_B_1 ),
    inference(demod,[status(thm)],['42','56'])).

thf('58',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
    = ( k5_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('59',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['12'])).

thf(t85_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ) )).

thf('60',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( r1_tarski @ X24 @ X25 )
      | ( r1_xboole_0 @ X24 @ ( k4_xboole_0 @ X26 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ ( k5_xboole_0 @ sk_A @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['58','63'])).

thf('65',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('sup+',[status(thm)],['57','64'])).

thf('66',plain,
    ( ( sk_B_1
     != ( k1_subset_1 @ sk_A ) )
   <= ( sk_B_1
     != ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['8'])).

thf('67',plain,(
    ! [X35: $i] :
      ( ( k1_subset_1 @ X35 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('68',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    sk_B_1
 != ( k1_subset_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['9','39'])).

thf('70',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['68','69'])).

thf('71',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['65','70'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.H62nWWXIsW
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:11:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.19/0.35  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.40/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.40/0.61  % Solved by: fo/fo7.sh
% 0.40/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.61  % done 351 iterations in 0.149s
% 0.40/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.40/0.61  % SZS output start Refutation
% 0.40/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.40/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.61  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.40/0.61  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.40/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.40/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.40/0.61  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.40/0.61  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.40/0.61  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.40/0.61  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.40/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.40/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.40/0.61  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.40/0.61  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.40/0.61  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.40/0.61  thf(t38_subset_1, conjecture,
% 0.40/0.61    (![A:$i,B:$i]:
% 0.40/0.61     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.40/0.61       ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 0.40/0.61         ( ( B ) = ( k1_subset_1 @ A ) ) ) ))).
% 0.40/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.61    (~( ![A:$i,B:$i]:
% 0.40/0.61        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.40/0.61          ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 0.40/0.61            ( ( B ) = ( k1_subset_1 @ A ) ) ) ) )),
% 0.40/0.61    inference('cnf.neg', [status(esa)], [t38_subset_1])).
% 0.40/0.61  thf('0', plain,
% 0.40/0.61      ((((sk_B_1) = (k1_subset_1 @ sk_A))
% 0.40/0.61        | (r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('1', plain,
% 0.40/0.61      (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))
% 0.40/0.61         <= (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))))),
% 0.40/0.61      inference('split', [status(esa)], ['0'])).
% 0.40/0.61  thf(t28_xboole_1, axiom,
% 0.40/0.61    (![A:$i,B:$i]:
% 0.40/0.61     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.40/0.61  thf('2', plain,
% 0.40/0.61      (![X22 : $i, X23 : $i]:
% 0.40/0.61         (((k3_xboole_0 @ X22 @ X23) = (X22)) | ~ (r1_tarski @ X22 @ X23))),
% 0.40/0.61      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.40/0.61  thf('3', plain,
% 0.40/0.61      ((((k3_xboole_0 @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)) = (sk_B_1)))
% 0.40/0.61         <= (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))))),
% 0.40/0.61      inference('sup-', [status(thm)], ['1', '2'])).
% 0.40/0.61  thf('4', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf(d5_subset_1, axiom,
% 0.40/0.61    (![A:$i,B:$i]:
% 0.40/0.61     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.40/0.61       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.40/0.61  thf('5', plain,
% 0.40/0.61      (![X36 : $i, X37 : $i]:
% 0.40/0.61         (((k3_subset_1 @ X36 @ X37) = (k4_xboole_0 @ X36 @ X37))
% 0.40/0.61          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X36)))),
% 0.40/0.61      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.40/0.61  thf('6', plain,
% 0.40/0.61      (((k3_subset_1 @ sk_A @ sk_B_1) = (k4_xboole_0 @ sk_A @ sk_B_1))),
% 0.40/0.61      inference('sup-', [status(thm)], ['4', '5'])).
% 0.40/0.61  thf('7', plain,
% 0.40/0.61      ((((k3_xboole_0 @ sk_B_1 @ (k4_xboole_0 @ sk_A @ sk_B_1)) = (sk_B_1)))
% 0.40/0.61         <= (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))))),
% 0.40/0.61      inference('demod', [status(thm)], ['3', '6'])).
% 0.40/0.61  thf('8', plain,
% 0.40/0.61      ((((sk_B_1) != (k1_subset_1 @ sk_A))
% 0.40/0.61        | ~ (r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('9', plain,
% 0.40/0.61      (~ (((sk_B_1) = (k1_subset_1 @ sk_A))) | 
% 0.40/0.61       ~ ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.40/0.61      inference('split', [status(esa)], ['8'])).
% 0.40/0.61  thf(d3_tarski, axiom,
% 0.40/0.61    (![A:$i,B:$i]:
% 0.40/0.61     ( ( r1_tarski @ A @ B ) <=>
% 0.40/0.61       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.40/0.61  thf('10', plain,
% 0.40/0.61      (![X3 : $i, X5 : $i]:
% 0.40/0.61         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.40/0.61      inference('cnf', [status(esa)], [d3_tarski])).
% 0.40/0.61  thf('11', plain,
% 0.40/0.61      (![X3 : $i, X5 : $i]:
% 0.40/0.61         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 0.40/0.61      inference('cnf', [status(esa)], [d3_tarski])).
% 0.40/0.61  thf('12', plain,
% 0.40/0.61      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.40/0.61      inference('sup-', [status(thm)], ['10', '11'])).
% 0.40/0.61  thf('13', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.40/0.61      inference('simplify', [status(thm)], ['12'])).
% 0.40/0.61  thf('14', plain,
% 0.40/0.61      (![X22 : $i, X23 : $i]:
% 0.40/0.61         (((k3_xboole_0 @ X22 @ X23) = (X22)) | ~ (r1_tarski @ X22 @ X23))),
% 0.40/0.61      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.40/0.61  thf('15', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.40/0.61      inference('sup-', [status(thm)], ['13', '14'])).
% 0.40/0.61  thf(d7_xboole_0, axiom,
% 0.40/0.61    (![A:$i,B:$i]:
% 0.40/0.61     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.40/0.61       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.40/0.61  thf('16', plain,
% 0.40/0.61      (![X12 : $i, X14 : $i]:
% 0.40/0.61         ((r1_xboole_0 @ X12 @ X14)
% 0.40/0.61          | ((k3_xboole_0 @ X12 @ X14) != (k1_xboole_0)))),
% 0.40/0.61      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.40/0.61  thf('17', plain,
% 0.40/0.61      (![X0 : $i]: (((X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X0))),
% 0.40/0.61      inference('sup-', [status(thm)], ['15', '16'])).
% 0.40/0.61  thf('18', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.40/0.61      inference('simplify', [status(thm)], ['17'])).
% 0.40/0.61  thf('19', plain,
% 0.40/0.61      (![X3 : $i, X5 : $i]:
% 0.40/0.61         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.40/0.61      inference('cnf', [status(esa)], [d3_tarski])).
% 0.40/0.61  thf('20', plain,
% 0.40/0.61      (![X3 : $i, X5 : $i]:
% 0.40/0.61         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.40/0.61      inference('cnf', [status(esa)], [d3_tarski])).
% 0.40/0.61  thf(t3_xboole_0, axiom,
% 0.40/0.61    (![A:$i,B:$i]:
% 0.40/0.61     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.40/0.61            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.40/0.61       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.40/0.61            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.40/0.61  thf('21', plain,
% 0.40/0.61      (![X15 : $i, X17 : $i, X18 : $i]:
% 0.40/0.61         (~ (r2_hidden @ X17 @ X15)
% 0.40/0.61          | ~ (r2_hidden @ X17 @ X18)
% 0.40/0.61          | ~ (r1_xboole_0 @ X15 @ X18))),
% 0.40/0.61      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.40/0.61  thf('22', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.61         ((r1_tarski @ X0 @ X1)
% 0.40/0.61          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.40/0.61          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 0.40/0.61      inference('sup-', [status(thm)], ['20', '21'])).
% 0.40/0.61  thf('23', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i]:
% 0.40/0.61         ((r1_tarski @ X0 @ X1)
% 0.40/0.61          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.40/0.61          | (r1_tarski @ X0 @ X1))),
% 0.40/0.61      inference('sup-', [status(thm)], ['19', '22'])).
% 0.40/0.61  thf('24', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i]: (~ (r1_xboole_0 @ X0 @ X0) | (r1_tarski @ X0 @ X1))),
% 0.40/0.61      inference('simplify', [status(thm)], ['23'])).
% 0.40/0.61  thf('25', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.40/0.61      inference('sup-', [status(thm)], ['18', '24'])).
% 0.40/0.61  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.40/0.61  thf('26', plain, (![X35 : $i]: ((k1_subset_1 @ X35) = (k1_xboole_0))),
% 0.40/0.61      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.40/0.61  thf('27', plain,
% 0.40/0.61      ((((sk_B_1) = (k1_subset_1 @ sk_A)))
% 0.40/0.61         <= ((((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.40/0.61      inference('split', [status(esa)], ['0'])).
% 0.40/0.61  thf('28', plain,
% 0.40/0.61      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.40/0.61      inference('sup+', [status(thm)], ['26', '27'])).
% 0.40/0.61  thf('29', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('30', plain,
% 0.40/0.61      (((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ sk_A)))
% 0.40/0.61         <= ((((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.40/0.61      inference('sup+', [status(thm)], ['28', '29'])).
% 0.40/0.61  thf('31', plain,
% 0.40/0.61      (![X36 : $i, X37 : $i]:
% 0.40/0.61         (((k3_subset_1 @ X36 @ X37) = (k4_xboole_0 @ X36 @ X37))
% 0.40/0.61          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X36)))),
% 0.40/0.61      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.40/0.61  thf('32', plain,
% 0.40/0.61      ((((k3_subset_1 @ sk_A @ k1_xboole_0)
% 0.40/0.61          = (k4_xboole_0 @ sk_A @ k1_xboole_0)))
% 0.40/0.61         <= ((((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.40/0.61      inference('sup-', [status(thm)], ['30', '31'])).
% 0.40/0.61  thf('33', plain,
% 0.40/0.61      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.40/0.61      inference('sup+', [status(thm)], ['26', '27'])).
% 0.40/0.61  thf('34', plain,
% 0.40/0.61      ((~ (r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))
% 0.40/0.61         <= (~ ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))))),
% 0.40/0.61      inference('split', [status(esa)], ['8'])).
% 0.40/0.61  thf('35', plain,
% 0.40/0.61      ((~ (r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ k1_xboole_0)))
% 0.40/0.61         <= (~ ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))) & 
% 0.40/0.61             (((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.40/0.61      inference('sup-', [status(thm)], ['33', '34'])).
% 0.40/0.61  thf('36', plain,
% 0.40/0.61      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.40/0.61      inference('sup+', [status(thm)], ['26', '27'])).
% 0.40/0.61  thf('37', plain,
% 0.40/0.61      ((~ (r1_tarski @ k1_xboole_0 @ (k3_subset_1 @ sk_A @ k1_xboole_0)))
% 0.40/0.61         <= (~ ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))) & 
% 0.40/0.61             (((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.40/0.61      inference('demod', [status(thm)], ['35', '36'])).
% 0.40/0.61  thf('38', plain,
% 0.40/0.61      ((~ (r1_tarski @ k1_xboole_0 @ (k4_xboole_0 @ sk_A @ k1_xboole_0)))
% 0.40/0.61         <= (~ ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))) & 
% 0.40/0.61             (((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.40/0.61      inference('sup-', [status(thm)], ['32', '37'])).
% 0.40/0.61  thf('39', plain,
% 0.40/0.61      (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))) | 
% 0.40/0.61       ~ (((sk_B_1) = (k1_subset_1 @ sk_A)))),
% 0.40/0.61      inference('sup-', [status(thm)], ['25', '38'])).
% 0.40/0.61  thf('40', plain,
% 0.40/0.61      (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))) | 
% 0.40/0.61       (((sk_B_1) = (k1_subset_1 @ sk_A)))),
% 0.40/0.61      inference('split', [status(esa)], ['0'])).
% 0.40/0.61  thf('41', plain, (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.40/0.61      inference('sat_resolution*', [status(thm)], ['9', '39', '40'])).
% 0.40/0.61  thf('42', plain,
% 0.40/0.61      (((k3_xboole_0 @ sk_B_1 @ (k4_xboole_0 @ sk_A @ sk_B_1)) = (sk_B_1))),
% 0.40/0.61      inference('simpl_trail', [status(thm)], ['7', '41'])).
% 0.40/0.61  thf('43', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf(d2_subset_1, axiom,
% 0.40/0.61    (![A:$i,B:$i]:
% 0.40/0.61     ( ( ( v1_xboole_0 @ A ) =>
% 0.40/0.61         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.40/0.61       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.40/0.61         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.40/0.61  thf('44', plain,
% 0.40/0.61      (![X32 : $i, X33 : $i]:
% 0.40/0.61         (~ (m1_subset_1 @ X32 @ X33)
% 0.40/0.61          | (r2_hidden @ X32 @ X33)
% 0.40/0.61          | (v1_xboole_0 @ X33))),
% 0.40/0.61      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.40/0.61  thf('45', plain,
% 0.40/0.61      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.40/0.61        | (r2_hidden @ sk_B_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.40/0.61      inference('sup-', [status(thm)], ['43', '44'])).
% 0.40/0.61  thf(fc1_subset_1, axiom,
% 0.40/0.61    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.40/0.61  thf('46', plain, (![X40 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X40))),
% 0.40/0.61      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.40/0.61  thf('47', plain, ((r2_hidden @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.40/0.61      inference('clc', [status(thm)], ['45', '46'])).
% 0.40/0.61  thf(d1_zfmisc_1, axiom,
% 0.40/0.61    (![A:$i,B:$i]:
% 0.40/0.61     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.40/0.61       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.40/0.61  thf('48', plain,
% 0.40/0.61      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.40/0.61         (~ (r2_hidden @ X30 @ X29)
% 0.40/0.61          | (r1_tarski @ X30 @ X28)
% 0.40/0.61          | ((X29) != (k1_zfmisc_1 @ X28)))),
% 0.40/0.61      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.40/0.61  thf('49', plain,
% 0.40/0.61      (![X28 : $i, X30 : $i]:
% 0.40/0.61         ((r1_tarski @ X30 @ X28) | ~ (r2_hidden @ X30 @ (k1_zfmisc_1 @ X28)))),
% 0.40/0.61      inference('simplify', [status(thm)], ['48'])).
% 0.40/0.61  thf('50', plain, ((r1_tarski @ sk_B_1 @ sk_A)),
% 0.40/0.61      inference('sup-', [status(thm)], ['47', '49'])).
% 0.40/0.61  thf('51', plain,
% 0.40/0.61      (![X22 : $i, X23 : $i]:
% 0.40/0.61         (((k3_xboole_0 @ X22 @ X23) = (X22)) | ~ (r1_tarski @ X22 @ X23))),
% 0.40/0.61      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.40/0.61  thf('52', plain, (((k3_xboole_0 @ sk_B_1 @ sk_A) = (sk_B_1))),
% 0.40/0.61      inference('sup-', [status(thm)], ['50', '51'])).
% 0.40/0.61  thf(commutativity_k3_xboole_0, axiom,
% 0.40/0.61    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.40/0.61  thf('53', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.40/0.61      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.40/0.61  thf('54', plain, (((k3_xboole_0 @ sk_A @ sk_B_1) = (sk_B_1))),
% 0.40/0.61      inference('demod', [status(thm)], ['52', '53'])).
% 0.40/0.61  thf(t100_xboole_1, axiom,
% 0.40/0.61    (![A:$i,B:$i]:
% 0.40/0.61     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.40/0.61  thf('55', plain,
% 0.40/0.61      (![X20 : $i, X21 : $i]:
% 0.40/0.61         ((k4_xboole_0 @ X20 @ X21)
% 0.40/0.61           = (k5_xboole_0 @ X20 @ (k3_xboole_0 @ X20 @ X21)))),
% 0.40/0.61      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.40/0.61  thf('56', plain,
% 0.40/0.61      (((k4_xboole_0 @ sk_A @ sk_B_1) = (k5_xboole_0 @ sk_A @ sk_B_1))),
% 0.40/0.61      inference('sup+', [status(thm)], ['54', '55'])).
% 0.40/0.61  thf('57', plain,
% 0.40/0.61      (((k3_xboole_0 @ sk_B_1 @ (k5_xboole_0 @ sk_A @ sk_B_1)) = (sk_B_1))),
% 0.40/0.61      inference('demod', [status(thm)], ['42', '56'])).
% 0.40/0.61  thf('58', plain,
% 0.40/0.61      (((k4_xboole_0 @ sk_A @ sk_B_1) = (k5_xboole_0 @ sk_A @ sk_B_1))),
% 0.40/0.61      inference('sup+', [status(thm)], ['54', '55'])).
% 0.40/0.61  thf('59', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.40/0.61      inference('simplify', [status(thm)], ['12'])).
% 0.40/0.61  thf(t85_xboole_1, axiom,
% 0.40/0.61    (![A:$i,B:$i,C:$i]:
% 0.40/0.61     ( ( r1_tarski @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ))).
% 0.40/0.61  thf('60', plain,
% 0.40/0.61      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.40/0.61         (~ (r1_tarski @ X24 @ X25)
% 0.40/0.61          | (r1_xboole_0 @ X24 @ (k4_xboole_0 @ X26 @ X25)))),
% 0.40/0.61      inference('cnf', [status(esa)], [t85_xboole_1])).
% 0.40/0.61  thf('61', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.40/0.61      inference('sup-', [status(thm)], ['59', '60'])).
% 0.40/0.61  thf('62', plain,
% 0.40/0.61      (![X12 : $i, X13 : $i]:
% 0.40/0.61         (((k3_xboole_0 @ X12 @ X13) = (k1_xboole_0))
% 0.40/0.61          | ~ (r1_xboole_0 @ X12 @ X13))),
% 0.40/0.61      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.40/0.61  thf('63', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i]:
% 0.40/0.61         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.40/0.61      inference('sup-', [status(thm)], ['61', '62'])).
% 0.40/0.61  thf('64', plain,
% 0.40/0.61      (((k3_xboole_0 @ sk_B_1 @ (k5_xboole_0 @ sk_A @ sk_B_1)) = (k1_xboole_0))),
% 0.40/0.61      inference('sup+', [status(thm)], ['58', '63'])).
% 0.40/0.61  thf('65', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.40/0.61      inference('sup+', [status(thm)], ['57', '64'])).
% 0.40/0.61  thf('66', plain,
% 0.40/0.61      ((((sk_B_1) != (k1_subset_1 @ sk_A)))
% 0.40/0.61         <= (~ (((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.40/0.61      inference('split', [status(esa)], ['8'])).
% 0.40/0.61  thf('67', plain, (![X35 : $i]: ((k1_subset_1 @ X35) = (k1_xboole_0))),
% 0.40/0.61      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.40/0.61  thf('68', plain,
% 0.40/0.61      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.40/0.61      inference('demod', [status(thm)], ['66', '67'])).
% 0.40/0.61  thf('69', plain, (~ (((sk_B_1) = (k1_subset_1 @ sk_A)))),
% 0.40/0.61      inference('sat_resolution*', [status(thm)], ['9', '39'])).
% 0.40/0.61  thf('70', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.40/0.61      inference('simpl_trail', [status(thm)], ['68', '69'])).
% 0.40/0.61  thf('71', plain, ($false),
% 0.40/0.61      inference('simplify_reflect-', [status(thm)], ['65', '70'])).
% 0.40/0.61  
% 0.40/0.61  % SZS output end Refutation
% 0.40/0.61  
% 0.40/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
