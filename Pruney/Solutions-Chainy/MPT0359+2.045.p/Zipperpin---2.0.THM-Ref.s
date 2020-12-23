%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.iul1zbRYat

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:37 EST 2020

% Result     : Theorem 0.34s
% Output     : Refutation 0.34s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 205 expanded)
%              Number of leaves         :   22 (  65 expanded)
%              Depth                    :   14
%              Number of atoms          :  672 (1745 expanded)
%              Number of equality atoms :   58 ( 160 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

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
    ! [X19: $i,X20: $i] :
      ( ( ( k3_subset_1 @ X20 @ ( k3_subset_1 @ X20 @ X19 ) )
        = X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('2',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k3_subset_1 @ X17 @ X18 )
        = ( k4_xboole_0 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('5',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( k3_subset_1 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['2','5'])).

thf('7',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('8',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('9',plain,
    ( ( sk_B
      = ( k2_subset_1 @ sk_A ) )
    | ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('12',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ sk_B )
        | ~ ( r2_hidden @ X0 @ ( k3_subset_1 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ X0 )
        | ( r2_hidden @ ( sk_C @ X0 @ ( k3_subset_1 @ sk_A @ sk_B ) ) @ sk_B ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['8','12'])).

thf('14',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_C @ X0 @ ( k4_xboole_0 @ sk_A @ sk_B ) ) @ sk_B )
        | ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ X0 ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup+',[status(thm)],['7','13'])).

thf('15',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('16',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_C @ X0 @ ( k4_xboole_0 @ sk_A @ sk_B ) ) @ sk_B )
        | ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B ) @ X0 ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( sk_B
     != ( k2_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( sk_B
     != ( k2_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['17'])).

thf('19',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('20',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ X8 @ X5 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('21',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(simplify,[status(thm)],['24'])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('26',plain,(
    ! [X16: $i] :
      ( ( k2_subset_1 @ X16 )
      = X16 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('27',plain,
    ( ( sk_B
      = ( k2_subset_1 @ sk_A ) )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['9'])).

thf('28',plain,
    ( ( sk_B = sk_A )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ sk_A ) )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k3_subset_1 @ X17 @ X18 )
        = ( k4_xboole_0 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('32',plain,
    ( ( ( k3_subset_1 @ sk_A @ sk_A )
      = ( k4_xboole_0 @ sk_A @ sk_A ) )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( sk_B = sk_A )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('34',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
   <= ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['17'])).

thf('35',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_A )
   <= ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
      & ( sk_B
        = ( k2_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( sk_B = sk_A )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('37',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_A ) @ sk_A )
   <= ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
      & ( sk_B
        = ( k2_subset_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ~ ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_A ) @ sk_A )
   <= ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
      & ( sk_B
        = ( k2_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['32','37'])).

thf('39',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
    | ( sk_B
     != ( k2_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','38'])).

thf('40',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
    | ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['9'])).

thf('41',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ),
    inference('sat_resolution*',[status(thm)],['18','39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( k4_xboole_0 @ sk_A @ sk_B ) ) @ sk_B )
      | ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['16','41'])).

thf('43',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('44',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( r2_hidden @ X8 @ X6 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('45',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B ) @ X0 ) ),
    inference(clc,[status(thm)],['42','46'])).

thf('48',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('49',plain,(
    ! [X24: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('50',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k3_subset_1 @ X17 @ X18 )
        = ( k4_xboole_0 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf(t22_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ) )).

thf('52',plain,(
    ! [X21: $i] :
      ( ( k2_subset_1 @ X21 )
      = ( k3_subset_1 @ X21 @ ( k1_subset_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t22_subset_1])).

thf('53',plain,(
    ! [X16: $i] :
      ( ( k2_subset_1 @ X16 )
      = X16 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('54',plain,(
    ! [X15: $i] :
      ( ( k1_subset_1 @ X15 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('55',plain,(
    ! [X21: $i] :
      ( X21
      = ( k3_subset_1 @ X21 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['51','55'])).

thf('57',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['48','59'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('61',plain,(
    ! [X10: $i,X12: $i] :
      ( ( X10 = X12 )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['47','62'])).

thf('64',plain,(
    ! [X21: $i] :
      ( X21
      = ( k3_subset_1 @ X21 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('65',plain,(
    sk_A = sk_B ),
    inference(demod,[status(thm)],['6','63','64'])).

thf('66',plain,
    ( ( sk_B
     != ( k2_subset_1 @ sk_A ) )
   <= ( sk_B
     != ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['17'])).

thf('67',plain,(
    ! [X16: $i] :
      ( ( k2_subset_1 @ X16 )
      = X16 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('68',plain,
    ( ( sk_B != sk_A )
   <= ( sk_B
     != ( k2_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    sk_B
 != ( k2_subset_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['18','39'])).

thf('70',plain,(
    sk_B != sk_A ),
    inference(simpl_trail,[status(thm)],['68','69'])).

thf('71',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['65','70'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.iul1zbRYat
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:44:11 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.34/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.34/0.51  % Solved by: fo/fo7.sh
% 0.34/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.34/0.51  % done 177 iterations in 0.070s
% 0.34/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.34/0.51  % SZS output start Refutation
% 0.34/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.34/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.34/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.34/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.34/0.51  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.34/0.51  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.34/0.51  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.34/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.34/0.51  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.34/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.34/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.34/0.51  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.34/0.51  thf(t39_subset_1, conjecture,
% 0.34/0.51    (![A:$i,B:$i]:
% 0.34/0.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.34/0.51       ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B ) <=>
% 0.34/0.51         ( ( B ) = ( k2_subset_1 @ A ) ) ) ))).
% 0.34/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.34/0.51    (~( ![A:$i,B:$i]:
% 0.34/0.51        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.34/0.51          ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B ) <=>
% 0.34/0.51            ( ( B ) = ( k2_subset_1 @ A ) ) ) ) )),
% 0.34/0.51    inference('cnf.neg', [status(esa)], [t39_subset_1])).
% 0.34/0.51  thf('0', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.34/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.51  thf(involutiveness_k3_subset_1, axiom,
% 0.34/0.51    (![A:$i,B:$i]:
% 0.34/0.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.34/0.51       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.34/0.51  thf('1', plain,
% 0.34/0.51      (![X19 : $i, X20 : $i]:
% 0.34/0.51         (((k3_subset_1 @ X20 @ (k3_subset_1 @ X20 @ X19)) = (X19))
% 0.34/0.51          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20)))),
% 0.34/0.51      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.34/0.51  thf('2', plain,
% 0.34/0.51      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.34/0.51      inference('sup-', [status(thm)], ['0', '1'])).
% 0.34/0.51  thf('3', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.34/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.51  thf(d5_subset_1, axiom,
% 0.34/0.51    (![A:$i,B:$i]:
% 0.34/0.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.34/0.51       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.34/0.51  thf('4', plain,
% 0.34/0.51      (![X17 : $i, X18 : $i]:
% 0.34/0.51         (((k3_subset_1 @ X17 @ X18) = (k4_xboole_0 @ X17 @ X18))
% 0.34/0.51          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X17)))),
% 0.34/0.51      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.34/0.51  thf('5', plain,
% 0.34/0.51      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.34/0.51      inference('sup-', [status(thm)], ['3', '4'])).
% 0.34/0.51  thf('6', plain,
% 0.34/0.51      (((k3_subset_1 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B)) = (sk_B))),
% 0.34/0.51      inference('demod', [status(thm)], ['2', '5'])).
% 0.34/0.51  thf('7', plain,
% 0.34/0.51      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.34/0.51      inference('sup-', [status(thm)], ['3', '4'])).
% 0.34/0.51  thf(d3_tarski, axiom,
% 0.34/0.51    (![A:$i,B:$i]:
% 0.34/0.51     ( ( r1_tarski @ A @ B ) <=>
% 0.34/0.51       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.34/0.51  thf('8', plain,
% 0.34/0.51      (![X1 : $i, X3 : $i]:
% 0.34/0.51         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.34/0.51      inference('cnf', [status(esa)], [d3_tarski])).
% 0.34/0.51  thf('9', plain,
% 0.34/0.51      ((((sk_B) = (k2_subset_1 @ sk_A))
% 0.34/0.51        | (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.34/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.51  thf('10', plain,
% 0.34/0.51      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))
% 0.34/0.51         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.34/0.51      inference('split', [status(esa)], ['9'])).
% 0.34/0.51  thf('11', plain,
% 0.34/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.34/0.51         (~ (r2_hidden @ X0 @ X1)
% 0.34/0.51          | (r2_hidden @ X0 @ X2)
% 0.34/0.51          | ~ (r1_tarski @ X1 @ X2))),
% 0.34/0.51      inference('cnf', [status(esa)], [d3_tarski])).
% 0.34/0.51  thf('12', plain,
% 0.34/0.51      ((![X0 : $i]:
% 0.34/0.51          ((r2_hidden @ X0 @ sk_B)
% 0.34/0.51           | ~ (r2_hidden @ X0 @ (k3_subset_1 @ sk_A @ sk_B))))
% 0.34/0.51         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.34/0.51      inference('sup-', [status(thm)], ['10', '11'])).
% 0.34/0.51  thf('13', plain,
% 0.34/0.51      ((![X0 : $i]:
% 0.34/0.51          ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ X0)
% 0.34/0.51           | (r2_hidden @ (sk_C @ X0 @ (k3_subset_1 @ sk_A @ sk_B)) @ sk_B)))
% 0.34/0.51         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.34/0.51      inference('sup-', [status(thm)], ['8', '12'])).
% 0.34/0.51  thf('14', plain,
% 0.34/0.51      ((![X0 : $i]:
% 0.34/0.51          ((r2_hidden @ (sk_C @ X0 @ (k4_xboole_0 @ sk_A @ sk_B)) @ sk_B)
% 0.34/0.51           | (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ X0)))
% 0.34/0.51         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.34/0.51      inference('sup+', [status(thm)], ['7', '13'])).
% 0.34/0.51  thf('15', plain,
% 0.34/0.51      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.34/0.51      inference('sup-', [status(thm)], ['3', '4'])).
% 0.34/0.51  thf('16', plain,
% 0.34/0.51      ((![X0 : $i]:
% 0.34/0.51          ((r2_hidden @ (sk_C @ X0 @ (k4_xboole_0 @ sk_A @ sk_B)) @ sk_B)
% 0.34/0.51           | (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B) @ X0)))
% 0.34/0.51         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.34/0.51      inference('demod', [status(thm)], ['14', '15'])).
% 0.34/0.51  thf('17', plain,
% 0.34/0.51      ((((sk_B) != (k2_subset_1 @ sk_A))
% 0.34/0.51        | ~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.34/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.51  thf('18', plain,
% 0.34/0.51      (~ (((sk_B) = (k2_subset_1 @ sk_A))) | 
% 0.34/0.51       ~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.34/0.51      inference('split', [status(esa)], ['17'])).
% 0.34/0.51  thf('19', plain,
% 0.34/0.51      (![X1 : $i, X3 : $i]:
% 0.34/0.51         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.34/0.51      inference('cnf', [status(esa)], [d3_tarski])).
% 0.34/0.51  thf(d5_xboole_0, axiom,
% 0.34/0.51    (![A:$i,B:$i,C:$i]:
% 0.34/0.51     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.34/0.51       ( ![D:$i]:
% 0.34/0.51         ( ( r2_hidden @ D @ C ) <=>
% 0.34/0.51           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.34/0.51  thf('20', plain,
% 0.34/0.51      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.34/0.51         (~ (r2_hidden @ X8 @ X7)
% 0.34/0.51          | (r2_hidden @ X8 @ X5)
% 0.34/0.51          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 0.34/0.51      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.34/0.51  thf('21', plain,
% 0.34/0.51      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.34/0.51         ((r2_hidden @ X8 @ X5) | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 0.34/0.51      inference('simplify', [status(thm)], ['20'])).
% 0.34/0.51  thf('22', plain,
% 0.34/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.34/0.52         ((r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 0.34/0.52          | (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 0.34/0.52      inference('sup-', [status(thm)], ['19', '21'])).
% 0.34/0.52  thf('23', plain,
% 0.34/0.52      (![X1 : $i, X3 : $i]:
% 0.34/0.52         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.34/0.52      inference('cnf', [status(esa)], [d3_tarski])).
% 0.34/0.52  thf('24', plain,
% 0.34/0.52      (![X0 : $i, X1 : $i]:
% 0.34/0.52         ((r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 0.34/0.52          | (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 0.34/0.52      inference('sup-', [status(thm)], ['22', '23'])).
% 0.34/0.52  thf('25', plain,
% 0.34/0.52      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 0.34/0.52      inference('simplify', [status(thm)], ['24'])).
% 0.34/0.52  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.34/0.52  thf('26', plain, (![X16 : $i]: ((k2_subset_1 @ X16) = (X16))),
% 0.34/0.52      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.34/0.52  thf('27', plain,
% 0.34/0.52      ((((sk_B) = (k2_subset_1 @ sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.34/0.52      inference('split', [status(esa)], ['9'])).
% 0.34/0.52  thf('28', plain,
% 0.34/0.52      ((((sk_B) = (sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.34/0.52      inference('sup+', [status(thm)], ['26', '27'])).
% 0.34/0.52  thf('29', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf('30', plain,
% 0.34/0.52      (((m1_subset_1 @ sk_A @ (k1_zfmisc_1 @ sk_A)))
% 0.34/0.52         <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.34/0.52      inference('sup+', [status(thm)], ['28', '29'])).
% 0.34/0.52  thf('31', plain,
% 0.34/0.52      (![X17 : $i, X18 : $i]:
% 0.34/0.52         (((k3_subset_1 @ X17 @ X18) = (k4_xboole_0 @ X17 @ X18))
% 0.34/0.52          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X17)))),
% 0.34/0.52      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.34/0.52  thf('32', plain,
% 0.34/0.52      ((((k3_subset_1 @ sk_A @ sk_A) = (k4_xboole_0 @ sk_A @ sk_A)))
% 0.34/0.52         <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.34/0.52      inference('sup-', [status(thm)], ['30', '31'])).
% 0.34/0.52  thf('33', plain,
% 0.34/0.52      ((((sk_B) = (sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.34/0.52      inference('sup+', [status(thm)], ['26', '27'])).
% 0.34/0.52  thf('34', plain,
% 0.34/0.52      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))
% 0.34/0.52         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.34/0.52      inference('split', [status(esa)], ['17'])).
% 0.34/0.52  thf('35', plain,
% 0.34/0.52      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_A))
% 0.34/0.52         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) & 
% 0.34/0.52             (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.34/0.52      inference('sup-', [status(thm)], ['33', '34'])).
% 0.34/0.52  thf('36', plain,
% 0.34/0.52      ((((sk_B) = (sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.34/0.52      inference('sup+', [status(thm)], ['26', '27'])).
% 0.34/0.52  thf('37', plain,
% 0.34/0.52      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_A) @ sk_A))
% 0.34/0.52         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) & 
% 0.34/0.52             (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.34/0.52      inference('demod', [status(thm)], ['35', '36'])).
% 0.34/0.52  thf('38', plain,
% 0.34/0.52      ((~ (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_A) @ sk_A))
% 0.34/0.52         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) & 
% 0.34/0.52             (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.34/0.52      inference('sup-', [status(thm)], ['32', '37'])).
% 0.34/0.52  thf('39', plain,
% 0.34/0.52      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) | 
% 0.34/0.52       ~ (((sk_B) = (k2_subset_1 @ sk_A)))),
% 0.34/0.52      inference('sup-', [status(thm)], ['25', '38'])).
% 0.34/0.52  thf('40', plain,
% 0.34/0.52      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) | 
% 0.34/0.52       (((sk_B) = (k2_subset_1 @ sk_A)))),
% 0.34/0.52      inference('split', [status(esa)], ['9'])).
% 0.34/0.52  thf('41', plain, (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.34/0.52      inference('sat_resolution*', [status(thm)], ['18', '39', '40'])).
% 0.34/0.52  thf('42', plain,
% 0.34/0.52      (![X0 : $i]:
% 0.34/0.52         ((r2_hidden @ (sk_C @ X0 @ (k4_xboole_0 @ sk_A @ sk_B)) @ sk_B)
% 0.34/0.52          | (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B) @ X0))),
% 0.34/0.52      inference('simpl_trail', [status(thm)], ['16', '41'])).
% 0.34/0.52  thf('43', plain,
% 0.34/0.52      (![X1 : $i, X3 : $i]:
% 0.34/0.52         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.34/0.52      inference('cnf', [status(esa)], [d3_tarski])).
% 0.34/0.52  thf('44', plain,
% 0.34/0.52      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.34/0.52         (~ (r2_hidden @ X8 @ X7)
% 0.34/0.52          | ~ (r2_hidden @ X8 @ X6)
% 0.34/0.52          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 0.34/0.52      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.34/0.52  thf('45', plain,
% 0.34/0.52      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.34/0.52         (~ (r2_hidden @ X8 @ X6)
% 0.34/0.52          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 0.34/0.52      inference('simplify', [status(thm)], ['44'])).
% 0.34/0.52  thf('46', plain,
% 0.34/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.34/0.52         ((r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 0.34/0.52          | ~ (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 0.34/0.52      inference('sup-', [status(thm)], ['43', '45'])).
% 0.34/0.52  thf('47', plain,
% 0.34/0.52      (![X0 : $i]: (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B) @ X0)),
% 0.34/0.52      inference('clc', [status(thm)], ['42', '46'])).
% 0.34/0.52  thf('48', plain,
% 0.34/0.52      (![X1 : $i, X3 : $i]:
% 0.34/0.52         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.34/0.52      inference('cnf', [status(esa)], [d3_tarski])).
% 0.34/0.52  thf(t4_subset_1, axiom,
% 0.34/0.52    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.34/0.52  thf('49', plain,
% 0.34/0.52      (![X24 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X24))),
% 0.34/0.52      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.34/0.52  thf('50', plain,
% 0.34/0.52      (![X17 : $i, X18 : $i]:
% 0.34/0.52         (((k3_subset_1 @ X17 @ X18) = (k4_xboole_0 @ X17 @ X18))
% 0.34/0.52          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X17)))),
% 0.34/0.52      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.34/0.52  thf('51', plain,
% 0.34/0.52      (![X0 : $i]:
% 0.34/0.52         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.34/0.52      inference('sup-', [status(thm)], ['49', '50'])).
% 0.34/0.52  thf(t22_subset_1, axiom,
% 0.34/0.52    (![A:$i]:
% 0.34/0.52     ( ( k2_subset_1 @ A ) = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ))).
% 0.34/0.52  thf('52', plain,
% 0.34/0.52      (![X21 : $i]:
% 0.34/0.52         ((k2_subset_1 @ X21) = (k3_subset_1 @ X21 @ (k1_subset_1 @ X21)))),
% 0.34/0.52      inference('cnf', [status(esa)], [t22_subset_1])).
% 0.34/0.52  thf('53', plain, (![X16 : $i]: ((k2_subset_1 @ X16) = (X16))),
% 0.34/0.52      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.34/0.52  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.34/0.52  thf('54', plain, (![X15 : $i]: ((k1_subset_1 @ X15) = (k1_xboole_0))),
% 0.34/0.52      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.34/0.52  thf('55', plain, (![X21 : $i]: ((X21) = (k3_subset_1 @ X21 @ k1_xboole_0))),
% 0.34/0.52      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.34/0.52  thf('56', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.34/0.52      inference('sup+', [status(thm)], ['51', '55'])).
% 0.34/0.52  thf('57', plain,
% 0.34/0.52      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.34/0.52         (~ (r2_hidden @ X8 @ X6)
% 0.34/0.52          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 0.34/0.52      inference('simplify', [status(thm)], ['44'])).
% 0.34/0.52  thf('58', plain,
% 0.34/0.52      (![X0 : $i, X1 : $i]:
% 0.34/0.52         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.34/0.52      inference('sup-', [status(thm)], ['56', '57'])).
% 0.34/0.52  thf('59', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.34/0.52      inference('condensation', [status(thm)], ['58'])).
% 0.34/0.52  thf('60', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.34/0.52      inference('sup-', [status(thm)], ['48', '59'])).
% 0.34/0.52  thf(d10_xboole_0, axiom,
% 0.34/0.52    (![A:$i,B:$i]:
% 0.34/0.52     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.34/0.52  thf('61', plain,
% 0.34/0.52      (![X10 : $i, X12 : $i]:
% 0.34/0.52         (((X10) = (X12))
% 0.34/0.52          | ~ (r1_tarski @ X12 @ X10)
% 0.34/0.52          | ~ (r1_tarski @ X10 @ X12))),
% 0.34/0.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.34/0.52  thf('62', plain,
% 0.34/0.52      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.34/0.52      inference('sup-', [status(thm)], ['60', '61'])).
% 0.34/0.52  thf('63', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.34/0.52      inference('sup-', [status(thm)], ['47', '62'])).
% 0.34/0.52  thf('64', plain, (![X21 : $i]: ((X21) = (k3_subset_1 @ X21 @ k1_xboole_0))),
% 0.34/0.52      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.34/0.52  thf('65', plain, (((sk_A) = (sk_B))),
% 0.34/0.52      inference('demod', [status(thm)], ['6', '63', '64'])).
% 0.34/0.52  thf('66', plain,
% 0.34/0.52      ((((sk_B) != (k2_subset_1 @ sk_A)))
% 0.34/0.52         <= (~ (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.34/0.52      inference('split', [status(esa)], ['17'])).
% 0.34/0.52  thf('67', plain, (![X16 : $i]: ((k2_subset_1 @ X16) = (X16))),
% 0.34/0.52      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.34/0.52  thf('68', plain,
% 0.34/0.52      ((((sk_B) != (sk_A))) <= (~ (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.34/0.52      inference('demod', [status(thm)], ['66', '67'])).
% 0.34/0.52  thf('69', plain, (~ (((sk_B) = (k2_subset_1 @ sk_A)))),
% 0.34/0.52      inference('sat_resolution*', [status(thm)], ['18', '39'])).
% 0.34/0.52  thf('70', plain, (((sk_B) != (sk_A))),
% 0.34/0.52      inference('simpl_trail', [status(thm)], ['68', '69'])).
% 0.34/0.52  thf('71', plain, ($false),
% 0.34/0.52      inference('simplify_reflect-', [status(thm)], ['65', '70'])).
% 0.34/0.52  
% 0.34/0.52  % SZS output end Refutation
% 0.34/0.52  
% 0.34/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
