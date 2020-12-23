%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TGKqeVfNUE

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:35 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 277 expanded)
%              Number of leaves         :   26 (  89 expanded)
%              Depth                    :   13
%              Number of atoms          :  726 (2249 expanded)
%              Number of equality atoms :   68 ( 205 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t39_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B )
      <=> ( B
          = ( k2_subset_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B )
        <=> ( B
            = ( k2_subset_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t39_subset_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('1',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k3_subset_1 @ X28 @ ( k3_subset_1 @ X28 @ X27 ) )
        = X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('2',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('3',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('4',plain,
    ( ( sk_B
      = ( k2_subset_1 @ sk_A ) )
    | ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('7',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ sk_B )
        | ~ ( r2_hidden @ X0 @ ( k3_subset_1 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ X0 )
        | ( r2_hidden @ ( sk_C @ X0 @ ( k3_subset_1 @ sk_A @ sk_B ) ) @ sk_B ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['3','7'])).

thf('9',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('11',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k3_subset_1 @ X25 @ X26 )
        = ( k4_xboole_0 @ X25 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('12',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('13',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X16 @ X15 )
      | ~ ( r2_hidden @ X16 @ X14 )
      | ( X15
       != ( k4_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('14',plain,(
    ! [X13: $i,X14: $i,X16: $i] :
      ( ~ ( r2_hidden @ X16 @ X14 )
      | ~ ( r2_hidden @ X16 @ ( k4_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k3_subset_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ X0 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ ( k3_subset_1 @ sk_A @ sk_B ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','15'])).

thf('17',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ X0 )
        | ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ X0 ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['8','16'])).

thf('18',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ X0 )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(simplify,[status(thm)],['17'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('19',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k3_xboole_0 @ X20 @ X21 )
        = X20 )
      | ~ ( r1_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('20',plain,
    ( ! [X0: $i] :
        ( ( k3_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ X0 )
        = ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('21',plain,(
    ! [X22: $i] :
      ( r1_tarski @ k1_xboole_0 @ X22 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('22',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k3_xboole_0 @ X20 @ X21 )
        = X20 )
      | ~ ( r1_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( ( k3_subset_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup+',[status(thm)],['20','25'])).

thf('27',plain,
    ( ( sk_B
     != ( k2_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( sk_B
     != ( k2_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['27'])).

thf('29',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('30',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('31',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k3_xboole_0 @ X20 @ X21 )
        = X20 )
      | ~ ( r1_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('37',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k3_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['35','38'])).

thf('40',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X16 @ X15 )
      | ( r2_hidden @ X16 @ X13 )
      | ( X15
       != ( k4_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('41',plain,(
    ! [X13: $i,X14: $i,X16: $i] :
      ( ( r2_hidden @ X16 @ X13 )
      | ~ ( r2_hidden @ X16 @ ( k4_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['35','38'])).

thf('44',plain,(
    ! [X13: $i,X14: $i,X16: $i] :
      ( ~ ( r2_hidden @ X16 @ X14 )
      | ~ ( r2_hidden @ X16 @ ( k4_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['42','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['29','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['35','38'])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('49',plain,(
    ! [X24: $i] :
      ( ( k2_subset_1 @ X24 )
      = X24 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('50',plain,
    ( ( sk_B
      = ( k2_subset_1 @ sk_A ) )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['4'])).

thf('51',plain,
    ( ( sk_B = sk_A )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ sk_A ) )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k3_subset_1 @ X25 @ X26 )
        = ( k4_xboole_0 @ X25 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('55',plain,
    ( ( ( k3_subset_1 @ sk_A @ sk_A )
      = ( k4_xboole_0 @ sk_A @ sk_A ) )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( ( k3_subset_1 @ sk_A @ sk_A )
      = ( k5_xboole_0 @ sk_A @ sk_A ) )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['48','55'])).

thf('57',plain,
    ( ( sk_B = sk_A )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('58',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
   <= ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['27'])).

thf('59',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_A )
   <= ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
      & ( sk_B
        = ( k2_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( sk_B = sk_A )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('61',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_A ) @ sk_A )
   <= ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
      & ( sk_B
        = ( k2_subset_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( ~ ( r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_A ) @ sk_A )
   <= ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
      & ( sk_B
        = ( k2_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['56','61'])).

thf('63',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
    | ( sk_B
     != ( k2_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','62'])).

thf('64',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
    | ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['4'])).

thf('65',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ),
    inference('sat_resolution*',[status(thm)],['28','63','64'])).

thf('66',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['26','65'])).

thf(t22_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ) )).

thf('67',plain,(
    ! [X29: $i] :
      ( ( k2_subset_1 @ X29 )
      = ( k3_subset_1 @ X29 @ ( k1_subset_1 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t22_subset_1])).

thf('68',plain,(
    ! [X24: $i] :
      ( ( k2_subset_1 @ X24 )
      = X24 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('69',plain,(
    ! [X23: $i] :
      ( ( k1_subset_1 @ X23 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('70',plain,(
    ! [X29: $i] :
      ( X29
      = ( k3_subset_1 @ X29 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,(
    sk_A = sk_B ),
    inference(demod,[status(thm)],['2','66','70'])).

thf('72',plain,
    ( ( sk_B
     != ( k2_subset_1 @ sk_A ) )
   <= ( sk_B
     != ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['27'])).

thf('73',plain,(
    ! [X24: $i] :
      ( ( k2_subset_1 @ X24 )
      = X24 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('74',plain,
    ( ( sk_B != sk_A )
   <= ( sk_B
     != ( k2_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    sk_B
 != ( k2_subset_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['28','63'])).

thf('76',plain,(
    sk_B != sk_A ),
    inference(simpl_trail,[status(thm)],['74','75'])).

thf('77',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['71','76'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TGKqeVfNUE
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:46:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.20/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.54  % Solved by: fo/fo7.sh
% 0.20/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.54  % done 296 iterations in 0.091s
% 0.20/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.54  % SZS output start Refutation
% 0.20/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.54  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.20/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.54  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.20/0.54  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.20/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.54  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.54  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.54  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.20/0.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.54  thf(t39_subset_1, conjecture,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.54       ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B ) <=>
% 0.20/0.54         ( ( B ) = ( k2_subset_1 @ A ) ) ) ))).
% 0.20/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.54    (~( ![A:$i,B:$i]:
% 0.20/0.54        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.54          ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B ) <=>
% 0.20/0.54            ( ( B ) = ( k2_subset_1 @ A ) ) ) ) )),
% 0.20/0.54    inference('cnf.neg', [status(esa)], [t39_subset_1])).
% 0.20/0.54  thf('0', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(involutiveness_k3_subset_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.54       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.20/0.54  thf('1', plain,
% 0.20/0.54      (![X27 : $i, X28 : $i]:
% 0.20/0.54         (((k3_subset_1 @ X28 @ (k3_subset_1 @ X28 @ X27)) = (X27))
% 0.20/0.54          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X28)))),
% 0.20/0.54      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.20/0.54  thf('2', plain,
% 0.20/0.54      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.20/0.54      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.54  thf(d3_tarski, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.54       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.54  thf('3', plain,
% 0.20/0.54      (![X3 : $i, X5 : $i]:
% 0.20/0.54         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.20/0.54      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.54  thf('4', plain,
% 0.20/0.54      ((((sk_B) = (k2_subset_1 @ sk_A))
% 0.20/0.54        | (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('5', plain,
% 0.20/0.54      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))
% 0.20/0.54         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.20/0.54      inference('split', [status(esa)], ['4'])).
% 0.20/0.54  thf('6', plain,
% 0.20/0.54      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X2 @ X3)
% 0.20/0.54          | (r2_hidden @ X2 @ X4)
% 0.20/0.54          | ~ (r1_tarski @ X3 @ X4))),
% 0.20/0.54      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.54  thf('7', plain,
% 0.20/0.54      ((![X0 : $i]:
% 0.20/0.54          ((r2_hidden @ X0 @ sk_B)
% 0.20/0.54           | ~ (r2_hidden @ X0 @ (k3_subset_1 @ sk_A @ sk_B))))
% 0.20/0.54         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.54  thf('8', plain,
% 0.20/0.54      ((![X0 : $i]:
% 0.20/0.54          ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ X0)
% 0.20/0.54           | (r2_hidden @ (sk_C @ X0 @ (k3_subset_1 @ sk_A @ sk_B)) @ sk_B)))
% 0.20/0.54         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['3', '7'])).
% 0.20/0.54  thf('9', plain,
% 0.20/0.54      (![X3 : $i, X5 : $i]:
% 0.20/0.54         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.20/0.54      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.54  thf('10', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(d5_subset_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.54       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.20/0.54  thf('11', plain,
% 0.20/0.54      (![X25 : $i, X26 : $i]:
% 0.20/0.54         (((k3_subset_1 @ X25 @ X26) = (k4_xboole_0 @ X25 @ X26))
% 0.20/0.54          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X25)))),
% 0.20/0.54      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.20/0.54  thf('12', plain,
% 0.20/0.54      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.54      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.54  thf(d5_xboole_0, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.20/0.54       ( ![D:$i]:
% 0.20/0.54         ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.54           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.20/0.54  thf('13', plain,
% 0.20/0.54      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X16 @ X15)
% 0.20/0.54          | ~ (r2_hidden @ X16 @ X14)
% 0.20/0.54          | ((X15) != (k4_xboole_0 @ X13 @ X14)))),
% 0.20/0.54      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.20/0.54  thf('14', plain,
% 0.20/0.54      (![X13 : $i, X14 : $i, X16 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X16 @ X14)
% 0.20/0.54          | ~ (r2_hidden @ X16 @ (k4_xboole_0 @ X13 @ X14)))),
% 0.20/0.54      inference('simplify', [status(thm)], ['13'])).
% 0.20/0.54  thf('15', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X0 @ (k3_subset_1 @ sk_A @ sk_B))
% 0.20/0.54          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.20/0.54      inference('sup-', [status(thm)], ['12', '14'])).
% 0.20/0.54  thf('16', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ X0)
% 0.20/0.54          | ~ (r2_hidden @ (sk_C @ X0 @ (k3_subset_1 @ sk_A @ sk_B)) @ sk_B))),
% 0.20/0.54      inference('sup-', [status(thm)], ['9', '15'])).
% 0.20/0.54  thf('17', plain,
% 0.20/0.54      ((![X0 : $i]:
% 0.20/0.54          ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ X0)
% 0.20/0.54           | (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ X0)))
% 0.20/0.54         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['8', '16'])).
% 0.20/0.54  thf('18', plain,
% 0.20/0.54      ((![X0 : $i]: (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ X0))
% 0.20/0.54         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.20/0.54      inference('simplify', [status(thm)], ['17'])).
% 0.20/0.54  thf(t28_xboole_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.54  thf('19', plain,
% 0.20/0.54      (![X20 : $i, X21 : $i]:
% 0.20/0.54         (((k3_xboole_0 @ X20 @ X21) = (X20)) | ~ (r1_tarski @ X20 @ X21))),
% 0.20/0.54      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.54  thf('20', plain,
% 0.20/0.54      ((![X0 : $i]:
% 0.20/0.54          ((k3_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ X0)
% 0.20/0.54            = (k3_subset_1 @ sk_A @ sk_B)))
% 0.20/0.54         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.54  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.20/0.54  thf('21', plain, (![X22 : $i]: (r1_tarski @ k1_xboole_0 @ X22)),
% 0.20/0.54      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.54  thf('22', plain,
% 0.20/0.54      (![X20 : $i, X21 : $i]:
% 0.20/0.54         (((k3_xboole_0 @ X20 @ X21) = (X20)) | ~ (r1_tarski @ X20 @ X21))),
% 0.20/0.54      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.54  thf('23', plain,
% 0.20/0.54      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.20/0.54      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.54  thf(commutativity_k3_xboole_0, axiom,
% 0.20/0.54    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.20/0.54  thf('24', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.54      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.54  thf('25', plain,
% 0.20/0.54      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.54      inference('sup+', [status(thm)], ['23', '24'])).
% 0.20/0.54  thf('26', plain,
% 0.20/0.54      ((((k3_subset_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.20/0.54         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['20', '25'])).
% 0.20/0.54  thf('27', plain,
% 0.20/0.54      ((((sk_B) != (k2_subset_1 @ sk_A))
% 0.20/0.54        | ~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('28', plain,
% 0.20/0.54      (~ (((sk_B) = (k2_subset_1 @ sk_A))) | 
% 0.20/0.54       ~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.20/0.54      inference('split', [status(esa)], ['27'])).
% 0.20/0.54  thf('29', plain,
% 0.20/0.54      (![X3 : $i, X5 : $i]:
% 0.20/0.54         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.20/0.54      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.54  thf('30', plain,
% 0.20/0.54      (![X3 : $i, X5 : $i]:
% 0.20/0.54         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.20/0.54      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.54  thf('31', plain,
% 0.20/0.54      (![X3 : $i, X5 : $i]:
% 0.20/0.54         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 0.20/0.54      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.54  thf('32', plain,
% 0.20/0.54      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.20/0.54      inference('sup-', [status(thm)], ['30', '31'])).
% 0.20/0.54  thf('33', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.20/0.54      inference('simplify', [status(thm)], ['32'])).
% 0.20/0.54  thf('34', plain,
% 0.20/0.54      (![X20 : $i, X21 : $i]:
% 0.20/0.54         (((k3_xboole_0 @ X20 @ X21) = (X20)) | ~ (r1_tarski @ X20 @ X21))),
% 0.20/0.54      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.54  thf('35', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.20/0.54      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.54  thf('36', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.54      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.54  thf(t100_xboole_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.54  thf('37', plain,
% 0.20/0.54      (![X18 : $i, X19 : $i]:
% 0.20/0.54         ((k4_xboole_0 @ X18 @ X19)
% 0.20/0.54           = (k5_xboole_0 @ X18 @ (k3_xboole_0 @ X18 @ X19)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.54  thf('38', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         ((k4_xboole_0 @ X0 @ X1)
% 0.20/0.54           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['36', '37'])).
% 0.20/0.54  thf('39', plain,
% 0.20/0.54      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.20/0.54      inference('sup+', [status(thm)], ['35', '38'])).
% 0.20/0.54  thf('40', plain,
% 0.20/0.54      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X16 @ X15)
% 0.20/0.54          | (r2_hidden @ X16 @ X13)
% 0.20/0.54          | ((X15) != (k4_xboole_0 @ X13 @ X14)))),
% 0.20/0.54      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.20/0.54  thf('41', plain,
% 0.20/0.54      (![X13 : $i, X14 : $i, X16 : $i]:
% 0.20/0.54         ((r2_hidden @ X16 @ X13)
% 0.20/0.54          | ~ (r2_hidden @ X16 @ (k4_xboole_0 @ X13 @ X14)))),
% 0.20/0.54      inference('simplify', [status(thm)], ['40'])).
% 0.20/0.54  thf('42', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0)) | (r2_hidden @ X1 @ X0))),
% 0.20/0.54      inference('sup-', [status(thm)], ['39', '41'])).
% 0.20/0.54  thf('43', plain,
% 0.20/0.54      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.20/0.54      inference('sup+', [status(thm)], ['35', '38'])).
% 0.20/0.54  thf('44', plain,
% 0.20/0.54      (![X13 : $i, X14 : $i, X16 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X16 @ X14)
% 0.20/0.54          | ~ (r2_hidden @ X16 @ (k4_xboole_0 @ X13 @ X14)))),
% 0.20/0.54      inference('simplify', [status(thm)], ['13'])).
% 0.20/0.54  thf('45', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 0.20/0.54          | ~ (r2_hidden @ X1 @ X0))),
% 0.20/0.54      inference('sup-', [status(thm)], ['43', '44'])).
% 0.20/0.54  thf('46', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))),
% 0.20/0.54      inference('clc', [status(thm)], ['42', '45'])).
% 0.20/0.54  thf('47', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]: (r1_tarski @ (k5_xboole_0 @ X0 @ X0) @ X1)),
% 0.20/0.54      inference('sup-', [status(thm)], ['29', '46'])).
% 0.20/0.54  thf('48', plain,
% 0.20/0.54      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.20/0.54      inference('sup+', [status(thm)], ['35', '38'])).
% 0.20/0.54  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.20/0.54  thf('49', plain, (![X24 : $i]: ((k2_subset_1 @ X24) = (X24))),
% 0.20/0.54      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.20/0.54  thf('50', plain,
% 0.20/0.54      ((((sk_B) = (k2_subset_1 @ sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.54      inference('split', [status(esa)], ['4'])).
% 0.20/0.54  thf('51', plain,
% 0.20/0.54      ((((sk_B) = (sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.54      inference('sup+', [status(thm)], ['49', '50'])).
% 0.20/0.54  thf('52', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('53', plain,
% 0.20/0.54      (((m1_subset_1 @ sk_A @ (k1_zfmisc_1 @ sk_A)))
% 0.20/0.54         <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.54      inference('sup+', [status(thm)], ['51', '52'])).
% 0.20/0.54  thf('54', plain,
% 0.20/0.54      (![X25 : $i, X26 : $i]:
% 0.20/0.54         (((k3_subset_1 @ X25 @ X26) = (k4_xboole_0 @ X25 @ X26))
% 0.20/0.54          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X25)))),
% 0.20/0.54      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.20/0.54  thf('55', plain,
% 0.20/0.54      ((((k3_subset_1 @ sk_A @ sk_A) = (k4_xboole_0 @ sk_A @ sk_A)))
% 0.20/0.54         <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['53', '54'])).
% 0.20/0.54  thf('56', plain,
% 0.20/0.54      ((((k3_subset_1 @ sk_A @ sk_A) = (k5_xboole_0 @ sk_A @ sk_A)))
% 0.20/0.54         <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.54      inference('sup+', [status(thm)], ['48', '55'])).
% 0.20/0.54  thf('57', plain,
% 0.20/0.54      ((((sk_B) = (sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.54      inference('sup+', [status(thm)], ['49', '50'])).
% 0.20/0.54  thf('58', plain,
% 0.20/0.54      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))
% 0.20/0.54         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.20/0.54      inference('split', [status(esa)], ['27'])).
% 0.20/0.54  thf('59', plain,
% 0.20/0.54      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_A))
% 0.20/0.54         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) & 
% 0.20/0.54             (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['57', '58'])).
% 0.20/0.54  thf('60', plain,
% 0.20/0.54      ((((sk_B) = (sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.54      inference('sup+', [status(thm)], ['49', '50'])).
% 0.20/0.54  thf('61', plain,
% 0.20/0.54      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_A) @ sk_A))
% 0.20/0.54         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) & 
% 0.20/0.54             (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.54      inference('demod', [status(thm)], ['59', '60'])).
% 0.20/0.54  thf('62', plain,
% 0.20/0.54      ((~ (r1_tarski @ (k5_xboole_0 @ sk_A @ sk_A) @ sk_A))
% 0.20/0.54         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) & 
% 0.20/0.54             (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['56', '61'])).
% 0.20/0.54  thf('63', plain,
% 0.20/0.54      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) | 
% 0.20/0.54       ~ (((sk_B) = (k2_subset_1 @ sk_A)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['47', '62'])).
% 0.20/0.54  thf('64', plain,
% 0.20/0.54      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) | 
% 0.20/0.54       (((sk_B) = (k2_subset_1 @ sk_A)))),
% 0.20/0.54      inference('split', [status(esa)], ['4'])).
% 0.20/0.54  thf('65', plain, (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.20/0.54      inference('sat_resolution*', [status(thm)], ['28', '63', '64'])).
% 0.20/0.54  thf('66', plain, (((k3_subset_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.20/0.54      inference('simpl_trail', [status(thm)], ['26', '65'])).
% 0.20/0.54  thf(t22_subset_1, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( k2_subset_1 @ A ) = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ))).
% 0.20/0.54  thf('67', plain,
% 0.20/0.54      (![X29 : $i]:
% 0.20/0.54         ((k2_subset_1 @ X29) = (k3_subset_1 @ X29 @ (k1_subset_1 @ X29)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t22_subset_1])).
% 0.20/0.54  thf('68', plain, (![X24 : $i]: ((k2_subset_1 @ X24) = (X24))),
% 0.20/0.54      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.20/0.54  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.20/0.54  thf('69', plain, (![X23 : $i]: ((k1_subset_1 @ X23) = (k1_xboole_0))),
% 0.20/0.54      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.20/0.54  thf('70', plain, (![X29 : $i]: ((X29) = (k3_subset_1 @ X29 @ k1_xboole_0))),
% 0.20/0.54      inference('demod', [status(thm)], ['67', '68', '69'])).
% 0.20/0.54  thf('71', plain, (((sk_A) = (sk_B))),
% 0.20/0.54      inference('demod', [status(thm)], ['2', '66', '70'])).
% 0.20/0.54  thf('72', plain,
% 0.20/0.54      ((((sk_B) != (k2_subset_1 @ sk_A)))
% 0.20/0.54         <= (~ (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.54      inference('split', [status(esa)], ['27'])).
% 0.20/0.54  thf('73', plain, (![X24 : $i]: ((k2_subset_1 @ X24) = (X24))),
% 0.20/0.54      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.20/0.54  thf('74', plain,
% 0.20/0.54      ((((sk_B) != (sk_A))) <= (~ (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.54      inference('demod', [status(thm)], ['72', '73'])).
% 0.20/0.54  thf('75', plain, (~ (((sk_B) = (k2_subset_1 @ sk_A)))),
% 0.20/0.54      inference('sat_resolution*', [status(thm)], ['28', '63'])).
% 0.20/0.54  thf('76', plain, (((sk_B) != (sk_A))),
% 0.20/0.54      inference('simpl_trail', [status(thm)], ['74', '75'])).
% 0.20/0.54  thf('77', plain, ($false),
% 0.20/0.54      inference('simplify_reflect-', [status(thm)], ['71', '76'])).
% 0.20/0.54  
% 0.20/0.54  % SZS output end Refutation
% 0.20/0.54  
% 0.20/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
