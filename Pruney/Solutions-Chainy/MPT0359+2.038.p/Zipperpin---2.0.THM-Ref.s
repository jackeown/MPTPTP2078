%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Teum1xX9em

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:36 EST 2020

% Result     : Theorem 0.69s
% Output     : Refutation 0.69s
% Verified   : 
% Statistics : Number of formulae       :  154 ( 469 expanded)
%              Number of leaves         :   28 ( 146 expanded)
%              Depth                    :   20
%              Number of atoms          : 1070 (3597 expanded)
%              Number of equality atoms :  116 ( 405 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('0',plain,(
    ! [X16: $i] :
      ( ( k4_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

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

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('2',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X34 @ X35 )
      | ( r2_hidden @ X34 @ X35 )
      | ( v1_xboole_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('3',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('4',plain,(
    ! [X40: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('5',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['3','4'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('6',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( r2_hidden @ X30 @ X29 )
      | ( r1_tarski @ X30 @ X28 )
      | ( X29
       != ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('7',plain,(
    ! [X28: $i,X30: $i] :
      ( ( r1_tarski @ X30 @ X28 )
      | ~ ( r2_hidden @ X30 @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['5','7'])).

thf(t109_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ) )).

thf('9',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ( r1_tarski @ ( k4_xboole_0 @ X10 @ X12 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t109_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('11',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) )
      | ( sk_A
        = ( k4_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B )
    | ( sk_A
      = ( k4_xboole_0 @ sk_B @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','12'])).

thf('14',plain,(
    ! [X16: $i] :
      ( ( k4_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('15',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B )
    | ( sk_A = sk_B ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ( sk_B
     != ( k2_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( sk_B
     != ( k2_subset_1 @ sk_A ) )
   <= ( sk_B
     != ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['16'])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('18',plain,(
    ! [X37: $i] :
      ( ( k2_subset_1 @ X37 )
      = X37 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('19',plain,
    ( ( sk_B != sk_A )
   <= ( sk_B
     != ( k2_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( sk_B
     != ( k2_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['16'])).

thf('21',plain,(
    ! [X37: $i] :
      ( ( k2_subset_1 @ X37 )
      = X37 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('22',plain,
    ( ( sk_B
      = ( k2_subset_1 @ sk_A ) )
    | ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( sk_B
      = ( k2_subset_1 @ sk_A ) )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['22'])).

thf('24',plain,
    ( ( sk_B = sk_A )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['21','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ sk_A ) )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('27',plain,(
    ! [X38: $i,X39: $i] :
      ( ( ( k3_subset_1 @ X38 @ X39 )
        = ( k4_xboole_0 @ X38 @ X39 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('28',plain,
    ( ( ( k3_subset_1 @ sk_A @ sk_A )
      = ( k4_xboole_0 @ sk_A @ sk_A ) )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( X1 != X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('30',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['29'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('31',plain,(
    ! [X4: $i,X6: $i] :
      ( ( ( k4_xboole_0 @ X4 @ X6 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( ( k3_subset_1 @ sk_A @ sk_A )
      = k1_xboole_0 )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','32'])).

thf('34',plain,
    ( ( sk_B = sk_A )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['21','23'])).

thf('35',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
   <= ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['16'])).

thf('36',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_A )
   <= ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
      & ( sk_B
        = ( k2_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( sk_B = sk_A )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['21','23'])).

thf('38',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_A ) @ sk_A )
   <= ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
      & ( sk_B
        = ( k2_subset_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_A )
   <= ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
      & ( sk_B
        = ( k2_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['33','38'])).

thf('40',plain,(
    ! [X16: $i] :
      ( ( k4_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(l36_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ C ) ) ) )).

thf('41',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k3_xboole_0 @ X8 @ X9 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X7 @ X8 ) @ ( k4_xboole_0 @ X7 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[l36_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ k1_xboole_0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X16: $i] :
      ( ( k4_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('44',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('47',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X16: $i] :
      ( ( k4_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['42','47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('51',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X17 @ X18 ) @ X19 )
      = ( k4_xboole_0 @ X17 @ ( k2_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('52',plain,(
    ! [X16: $i] :
      ( ( k4_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['50','53'])).

thf('55',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( ( k4_xboole_0 @ X4 @ X5 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ( X0
        = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('62',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( ( k4_xboole_0 @ X4 @ X5 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_tarski @ X1 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ X0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['60','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['59','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['49','66'])).

thf('68',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( ( k4_xboole_0 @ X4 @ X5 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
    | ( sk_B
     != ( k2_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['39','70'])).

thf('72',plain,(
    sk_B
 != ( k2_subset_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['20','71'])).

thf('73',plain,(
    sk_B != sk_A ),
    inference(simpl_trail,[status(thm)],['19','72'])).

thf('74',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['15','73'])).

thf('75',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X38: $i,X39: $i] :
      ( ( ( k3_subset_1 @ X38 @ X39 )
        = ( k4_xboole_0 @ X38 @ X39 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('77',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('79',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['5','7'])).

thf('81',plain,(
    ! [X4: $i,X6: $i] :
      ( ( ( k4_xboole_0 @ X4 @ X6 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('82',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('84',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k3_xboole_0 @ X8 @ X9 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X7 @ X8 ) @ ( k4_xboole_0 @ X7 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[l36_xboole_1])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['59','65'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( ( k4_xboole_0 @ X4 @ X5 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_tarski @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_B @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['82','89'])).

thf('91',plain,(
    r1_tarski @ sk_B @ ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['90'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('92',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(t31_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) @ ( k2_xboole_0 @ B @ C ) ) )).

thf('93',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ X13 @ X14 ) @ ( k3_xboole_0 @ X13 @ X15 ) ) @ ( k2_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t31_xboole_1])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['91','98'])).

thf('100',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['79','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('102',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X17 @ X18 ) @ X19 )
      = ( k4_xboole_0 @ X17 @ ( k2_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( ( k4_xboole_0 @ X4 @ X5 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['105'])).

thf('107',plain,(
    r1_tarski @ sk_A @ ( k2_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup+',[status(thm)],['100','106'])).

thf('108',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['22'])).

thf('109',plain,(
    ! [X4: $i,X6: $i] :
      ( ( ( k4_xboole_0 @ X4 @ X6 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('110',plain,
    ( ( ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
      = k1_xboole_0 )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
    | ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['22'])).

thf('112',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ),
    inference('sat_resolution*',[status(thm)],['20','71','111'])).

thf('113',plain,
    ( ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['110','112'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_tarski @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('115',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k3_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k3_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['115'])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('118',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k3_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['42','47','48'])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['119','120'])).

thf('122',plain,
    ( sk_B
    = ( k2_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup+',[status(thm)],['118','121'])).

thf('123',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['107','122'])).

thf('124',plain,(
    $false ),
    inference(demod,[status(thm)],['74','123'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Teum1xX9em
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:44:45 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.69/0.87  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.69/0.87  % Solved by: fo/fo7.sh
% 0.69/0.87  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.69/0.87  % done 1187 iterations in 0.419s
% 0.69/0.87  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.69/0.87  % SZS output start Refutation
% 0.69/0.87  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.69/0.87  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.69/0.87  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.69/0.87  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.69/0.87  thf(sk_A_type, type, sk_A: $i).
% 0.69/0.87  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.69/0.87  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.69/0.87  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.69/0.87  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.69/0.87  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.69/0.87  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.69/0.87  thf(sk_B_type, type, sk_B: $i).
% 0.69/0.87  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.69/0.87  thf(t3_boole, axiom,
% 0.69/0.87    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.69/0.87  thf('0', plain, (![X16 : $i]: ((k4_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.69/0.87      inference('cnf', [status(esa)], [t3_boole])).
% 0.69/0.87  thf(t39_subset_1, conjecture,
% 0.69/0.87    (![A:$i,B:$i]:
% 0.69/0.87     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.69/0.87       ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B ) <=>
% 0.69/0.87         ( ( B ) = ( k2_subset_1 @ A ) ) ) ))).
% 0.69/0.87  thf(zf_stmt_0, negated_conjecture,
% 0.69/0.87    (~( ![A:$i,B:$i]:
% 0.69/0.87        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.69/0.87          ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B ) <=>
% 0.69/0.87            ( ( B ) = ( k2_subset_1 @ A ) ) ) ) )),
% 0.69/0.87    inference('cnf.neg', [status(esa)], [t39_subset_1])).
% 0.69/0.87  thf('1', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf(d2_subset_1, axiom,
% 0.69/0.87    (![A:$i,B:$i]:
% 0.69/0.87     ( ( ( v1_xboole_0 @ A ) =>
% 0.69/0.87         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.69/0.87       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.69/0.87         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.69/0.87  thf('2', plain,
% 0.69/0.87      (![X34 : $i, X35 : $i]:
% 0.69/0.87         (~ (m1_subset_1 @ X34 @ X35)
% 0.69/0.87          | (r2_hidden @ X34 @ X35)
% 0.69/0.87          | (v1_xboole_0 @ X35))),
% 0.69/0.87      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.69/0.87  thf('3', plain,
% 0.69/0.87      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.69/0.87        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.69/0.87      inference('sup-', [status(thm)], ['1', '2'])).
% 0.69/0.87  thf(fc1_subset_1, axiom,
% 0.69/0.87    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.69/0.87  thf('4', plain, (![X40 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X40))),
% 0.69/0.87      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.69/0.87  thf('5', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.69/0.87      inference('clc', [status(thm)], ['3', '4'])).
% 0.69/0.87  thf(d1_zfmisc_1, axiom,
% 0.69/0.87    (![A:$i,B:$i]:
% 0.69/0.87     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.69/0.87       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.69/0.87  thf('6', plain,
% 0.69/0.87      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.69/0.87         (~ (r2_hidden @ X30 @ X29)
% 0.69/0.87          | (r1_tarski @ X30 @ X28)
% 0.69/0.87          | ((X29) != (k1_zfmisc_1 @ X28)))),
% 0.69/0.87      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.69/0.87  thf('7', plain,
% 0.69/0.87      (![X28 : $i, X30 : $i]:
% 0.69/0.87         ((r1_tarski @ X30 @ X28) | ~ (r2_hidden @ X30 @ (k1_zfmisc_1 @ X28)))),
% 0.69/0.87      inference('simplify', [status(thm)], ['6'])).
% 0.69/0.87  thf('8', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.69/0.87      inference('sup-', [status(thm)], ['5', '7'])).
% 0.69/0.87  thf(t109_xboole_1, axiom,
% 0.69/0.87    (![A:$i,B:$i,C:$i]:
% 0.69/0.87     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ))).
% 0.69/0.87  thf('9', plain,
% 0.69/0.87      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.69/0.87         (~ (r1_tarski @ X10 @ X11)
% 0.69/0.87          | (r1_tarski @ (k4_xboole_0 @ X10 @ X12) @ X11))),
% 0.69/0.87      inference('cnf', [status(esa)], [t109_xboole_1])).
% 0.69/0.87  thf('10', plain,
% 0.69/0.87      (![X0 : $i]: (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ sk_A)),
% 0.69/0.87      inference('sup-', [status(thm)], ['8', '9'])).
% 0.69/0.87  thf(d10_xboole_0, axiom,
% 0.69/0.87    (![A:$i,B:$i]:
% 0.69/0.87     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.69/0.87  thf('11', plain,
% 0.69/0.87      (![X1 : $i, X3 : $i]:
% 0.69/0.87         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 0.69/0.87      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.69/0.87  thf('12', plain,
% 0.69/0.87      (![X0 : $i]:
% 0.69/0.87         (~ (r1_tarski @ sk_A @ (k4_xboole_0 @ sk_B @ X0))
% 0.69/0.87          | ((sk_A) = (k4_xboole_0 @ sk_B @ X0)))),
% 0.69/0.87      inference('sup-', [status(thm)], ['10', '11'])).
% 0.69/0.87  thf('13', plain,
% 0.69/0.87      ((~ (r1_tarski @ sk_A @ sk_B)
% 0.69/0.87        | ((sk_A) = (k4_xboole_0 @ sk_B @ k1_xboole_0)))),
% 0.69/0.87      inference('sup-', [status(thm)], ['0', '12'])).
% 0.69/0.87  thf('14', plain, (![X16 : $i]: ((k4_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.69/0.87      inference('cnf', [status(esa)], [t3_boole])).
% 0.69/0.87  thf('15', plain, ((~ (r1_tarski @ sk_A @ sk_B) | ((sk_A) = (sk_B)))),
% 0.69/0.87      inference('demod', [status(thm)], ['13', '14'])).
% 0.69/0.87  thf('16', plain,
% 0.69/0.87      ((((sk_B) != (k2_subset_1 @ sk_A))
% 0.69/0.87        | ~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf('17', plain,
% 0.69/0.87      ((((sk_B) != (k2_subset_1 @ sk_A)))
% 0.69/0.87         <= (~ (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.69/0.87      inference('split', [status(esa)], ['16'])).
% 0.69/0.87  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.69/0.87  thf('18', plain, (![X37 : $i]: ((k2_subset_1 @ X37) = (X37))),
% 0.69/0.87      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.69/0.87  thf('19', plain,
% 0.69/0.87      ((((sk_B) != (sk_A))) <= (~ (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.69/0.87      inference('demod', [status(thm)], ['17', '18'])).
% 0.69/0.87  thf('20', plain,
% 0.69/0.87      (~ (((sk_B) = (k2_subset_1 @ sk_A))) | 
% 0.69/0.87       ~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.69/0.87      inference('split', [status(esa)], ['16'])).
% 0.69/0.87  thf('21', plain, (![X37 : $i]: ((k2_subset_1 @ X37) = (X37))),
% 0.69/0.87      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.69/0.87  thf('22', plain,
% 0.69/0.87      ((((sk_B) = (k2_subset_1 @ sk_A))
% 0.69/0.87        | (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf('23', plain,
% 0.69/0.87      ((((sk_B) = (k2_subset_1 @ sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.69/0.87      inference('split', [status(esa)], ['22'])).
% 0.69/0.87  thf('24', plain,
% 0.69/0.87      ((((sk_B) = (sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.69/0.87      inference('sup+', [status(thm)], ['21', '23'])).
% 0.69/0.87  thf('25', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf('26', plain,
% 0.69/0.87      (((m1_subset_1 @ sk_A @ (k1_zfmisc_1 @ sk_A)))
% 0.69/0.87         <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.69/0.87      inference('sup+', [status(thm)], ['24', '25'])).
% 0.69/0.87  thf(d5_subset_1, axiom,
% 0.69/0.87    (![A:$i,B:$i]:
% 0.69/0.87     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.69/0.87       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.69/0.87  thf('27', plain,
% 0.69/0.87      (![X38 : $i, X39 : $i]:
% 0.69/0.87         (((k3_subset_1 @ X38 @ X39) = (k4_xboole_0 @ X38 @ X39))
% 0.69/0.87          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X38)))),
% 0.69/0.87      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.69/0.87  thf('28', plain,
% 0.69/0.87      ((((k3_subset_1 @ sk_A @ sk_A) = (k4_xboole_0 @ sk_A @ sk_A)))
% 0.69/0.87         <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.69/0.87      inference('sup-', [status(thm)], ['26', '27'])).
% 0.69/0.87  thf('29', plain,
% 0.69/0.87      (![X1 : $i, X2 : $i]: ((r1_tarski @ X1 @ X2) | ((X1) != (X2)))),
% 0.69/0.87      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.69/0.87  thf('30', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 0.69/0.87      inference('simplify', [status(thm)], ['29'])).
% 0.69/0.87  thf(l32_xboole_1, axiom,
% 0.69/0.87    (![A:$i,B:$i]:
% 0.69/0.87     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.69/0.87  thf('31', plain,
% 0.69/0.87      (![X4 : $i, X6 : $i]:
% 0.69/0.87         (((k4_xboole_0 @ X4 @ X6) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ X6))),
% 0.69/0.87      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.69/0.87  thf('32', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.69/0.87      inference('sup-', [status(thm)], ['30', '31'])).
% 0.69/0.87  thf('33', plain,
% 0.69/0.87      ((((k3_subset_1 @ sk_A @ sk_A) = (k1_xboole_0)))
% 0.69/0.87         <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.69/0.87      inference('demod', [status(thm)], ['28', '32'])).
% 0.69/0.87  thf('34', plain,
% 0.69/0.87      ((((sk_B) = (sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.69/0.87      inference('sup+', [status(thm)], ['21', '23'])).
% 0.69/0.87  thf('35', plain,
% 0.69/0.87      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))
% 0.69/0.87         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.69/0.87      inference('split', [status(esa)], ['16'])).
% 0.69/0.87  thf('36', plain,
% 0.69/0.87      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_A))
% 0.69/0.87         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) & 
% 0.69/0.87             (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.69/0.87      inference('sup-', [status(thm)], ['34', '35'])).
% 0.69/0.87  thf('37', plain,
% 0.69/0.87      ((((sk_B) = (sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.69/0.87      inference('sup+', [status(thm)], ['21', '23'])).
% 0.69/0.87  thf('38', plain,
% 0.69/0.87      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_A) @ sk_A))
% 0.69/0.87         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) & 
% 0.69/0.87             (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.69/0.87      inference('demod', [status(thm)], ['36', '37'])).
% 0.69/0.87  thf('39', plain,
% 0.69/0.87      ((~ (r1_tarski @ k1_xboole_0 @ sk_A))
% 0.69/0.87         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) & 
% 0.69/0.87             (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.69/0.87      inference('sup-', [status(thm)], ['33', '38'])).
% 0.69/0.87  thf('40', plain, (![X16 : $i]: ((k4_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.69/0.87      inference('cnf', [status(esa)], [t3_boole])).
% 0.69/0.87  thf(l36_xboole_1, axiom,
% 0.69/0.87    (![A:$i,B:$i,C:$i]:
% 0.69/0.87     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) =
% 0.69/0.87       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ C ) ) ))).
% 0.69/0.87  thf('41', plain,
% 0.69/0.87      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.69/0.87         ((k4_xboole_0 @ X7 @ (k3_xboole_0 @ X8 @ X9))
% 0.69/0.87           = (k2_xboole_0 @ (k4_xboole_0 @ X7 @ X8) @ (k4_xboole_0 @ X7 @ X9)))),
% 0.69/0.87      inference('cnf', [status(esa)], [l36_xboole_1])).
% 0.69/0.87  thf('42', plain,
% 0.69/0.87      (![X0 : $i, X1 : $i]:
% 0.69/0.87         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ k1_xboole_0))
% 0.69/0.87           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 0.69/0.87      inference('sup+', [status(thm)], ['40', '41'])).
% 0.69/0.87  thf('43', plain, (![X16 : $i]: ((k4_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.69/0.87      inference('cnf', [status(esa)], [t3_boole])).
% 0.69/0.87  thf(t48_xboole_1, axiom,
% 0.69/0.87    (![A:$i,B:$i]:
% 0.69/0.87     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.69/0.87  thf('44', plain,
% 0.69/0.87      (![X20 : $i, X21 : $i]:
% 0.69/0.87         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X20 @ X21))
% 0.69/0.87           = (k3_xboole_0 @ X20 @ X21))),
% 0.69/0.87      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.69/0.87  thf('45', plain,
% 0.69/0.87      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.69/0.87      inference('sup+', [status(thm)], ['43', '44'])).
% 0.69/0.88  thf('46', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.69/0.88      inference('sup-', [status(thm)], ['30', '31'])).
% 0.69/0.88  thf('47', plain,
% 0.69/0.88      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.69/0.88      inference('demod', [status(thm)], ['45', '46'])).
% 0.69/0.88  thf('48', plain, (![X16 : $i]: ((k4_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.69/0.88      inference('cnf', [status(esa)], [t3_boole])).
% 0.69/0.88  thf('49', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i]:
% 0.69/0.88         ((X0) = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 0.69/0.88      inference('demod', [status(thm)], ['42', '47', '48'])).
% 0.69/0.88  thf('50', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.69/0.88      inference('sup-', [status(thm)], ['30', '31'])).
% 0.69/0.88  thf(t41_xboole_1, axiom,
% 0.69/0.88    (![A:$i,B:$i,C:$i]:
% 0.69/0.88     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.69/0.88       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.69/0.88  thf('51', plain,
% 0.69/0.88      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.69/0.88         ((k4_xboole_0 @ (k4_xboole_0 @ X17 @ X18) @ X19)
% 0.69/0.88           = (k4_xboole_0 @ X17 @ (k2_xboole_0 @ X18 @ X19)))),
% 0.69/0.88      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.69/0.88  thf('52', plain, (![X16 : $i]: ((k4_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.69/0.88      inference('cnf', [status(esa)], [t3_boole])).
% 0.69/0.88  thf('53', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i]:
% 0.69/0.88         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ k1_xboole_0))
% 0.69/0.88           = (k4_xboole_0 @ X1 @ X0))),
% 0.69/0.88      inference('sup+', [status(thm)], ['51', '52'])).
% 0.69/0.88  thf('54', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         ((k1_xboole_0) = (k4_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ X0))),
% 0.69/0.88      inference('sup+', [status(thm)], ['50', '53'])).
% 0.69/0.88  thf('55', plain,
% 0.69/0.88      (![X4 : $i, X5 : $i]:
% 0.69/0.88         ((r1_tarski @ X4 @ X5) | ((k4_xboole_0 @ X4 @ X5) != (k1_xboole_0)))),
% 0.69/0.88      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.69/0.88  thf('56', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         (((k1_xboole_0) != (k1_xboole_0))
% 0.69/0.88          | (r1_tarski @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ X0))),
% 0.69/0.88      inference('sup-', [status(thm)], ['54', '55'])).
% 0.69/0.88  thf('57', plain,
% 0.69/0.88      (![X0 : $i]: (r1_tarski @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ X0)),
% 0.69/0.88      inference('simplify', [status(thm)], ['56'])).
% 0.69/0.88  thf('58', plain,
% 0.69/0.88      (![X1 : $i, X3 : $i]:
% 0.69/0.88         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 0.69/0.88      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.69/0.88  thf('59', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ X0 @ k1_xboole_0))
% 0.69/0.88          | ((X0) = (k2_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.69/0.88      inference('sup-', [status(thm)], ['57', '58'])).
% 0.69/0.88  thf('60', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.69/0.88      inference('sup-', [status(thm)], ['30', '31'])).
% 0.69/0.88  thf('61', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i]:
% 0.69/0.88         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ k1_xboole_0))
% 0.69/0.88           = (k4_xboole_0 @ X1 @ X0))),
% 0.69/0.88      inference('sup+', [status(thm)], ['51', '52'])).
% 0.69/0.88  thf('62', plain,
% 0.69/0.88      (![X4 : $i, X5 : $i]:
% 0.69/0.88         ((r1_tarski @ X4 @ X5) | ((k4_xboole_0 @ X4 @ X5) != (k1_xboole_0)))),
% 0.69/0.88      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.69/0.88  thf('63', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i]:
% 0.69/0.88         (((k4_xboole_0 @ X1 @ X0) != (k1_xboole_0))
% 0.69/0.88          | (r1_tarski @ X1 @ (k2_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.69/0.88      inference('sup-', [status(thm)], ['61', '62'])).
% 0.69/0.88  thf('64', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         (((k1_xboole_0) != (k1_xboole_0))
% 0.69/0.88          | (r1_tarski @ X0 @ (k2_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.69/0.88      inference('sup-', [status(thm)], ['60', '63'])).
% 0.69/0.88  thf('65', plain,
% 0.69/0.88      (![X0 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 0.69/0.88      inference('simplify', [status(thm)], ['64'])).
% 0.69/0.88  thf('66', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 0.69/0.88      inference('demod', [status(thm)], ['59', '65'])).
% 0.69/0.88  thf('67', plain,
% 0.69/0.88      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.69/0.88      inference('sup+', [status(thm)], ['49', '66'])).
% 0.69/0.88  thf('68', plain,
% 0.69/0.88      (![X4 : $i, X5 : $i]:
% 0.69/0.88         ((r1_tarski @ X4 @ X5) | ((k4_xboole_0 @ X4 @ X5) != (k1_xboole_0)))),
% 0.69/0.88      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.69/0.88  thf('69', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         (((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ k1_xboole_0 @ X0))),
% 0.69/0.88      inference('sup-', [status(thm)], ['67', '68'])).
% 0.69/0.88  thf('70', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.69/0.88      inference('simplify', [status(thm)], ['69'])).
% 0.69/0.88  thf('71', plain,
% 0.69/0.88      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) | 
% 0.69/0.88       ~ (((sk_B) = (k2_subset_1 @ sk_A)))),
% 0.69/0.88      inference('demod', [status(thm)], ['39', '70'])).
% 0.69/0.88  thf('72', plain, (~ (((sk_B) = (k2_subset_1 @ sk_A)))),
% 0.69/0.88      inference('sat_resolution*', [status(thm)], ['20', '71'])).
% 0.69/0.88  thf('73', plain, (((sk_B) != (sk_A))),
% 0.69/0.88      inference('simpl_trail', [status(thm)], ['19', '72'])).
% 0.69/0.88  thf('74', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.69/0.88      inference('simplify_reflect-', [status(thm)], ['15', '73'])).
% 0.69/0.88  thf('75', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf('76', plain,
% 0.69/0.88      (![X38 : $i, X39 : $i]:
% 0.69/0.88         (((k3_subset_1 @ X38 @ X39) = (k4_xboole_0 @ X38 @ X39))
% 0.69/0.88          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X38)))),
% 0.69/0.88      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.69/0.88  thf('77', plain,
% 0.69/0.88      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.69/0.88      inference('sup-', [status(thm)], ['75', '76'])).
% 0.69/0.88  thf('78', plain,
% 0.69/0.88      (![X20 : $i, X21 : $i]:
% 0.69/0.88         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X20 @ X21))
% 0.69/0.88           = (k3_xboole_0 @ X20 @ X21))),
% 0.69/0.88      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.69/0.88  thf('79', plain,
% 0.69/0.88      (((k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 0.69/0.88         = (k3_xboole_0 @ sk_A @ sk_B))),
% 0.69/0.88      inference('sup+', [status(thm)], ['77', '78'])).
% 0.69/0.88  thf('80', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.69/0.88      inference('sup-', [status(thm)], ['5', '7'])).
% 0.69/0.88  thf('81', plain,
% 0.69/0.88      (![X4 : $i, X6 : $i]:
% 0.69/0.88         (((k4_xboole_0 @ X4 @ X6) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ X6))),
% 0.69/0.88      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.69/0.88  thf('82', plain, (((k4_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0))),
% 0.69/0.88      inference('sup-', [status(thm)], ['80', '81'])).
% 0.69/0.88  thf('83', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.69/0.88      inference('sup-', [status(thm)], ['30', '31'])).
% 0.69/0.88  thf('84', plain,
% 0.69/0.88      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.69/0.88         ((k4_xboole_0 @ X7 @ (k3_xboole_0 @ X8 @ X9))
% 0.69/0.88           = (k2_xboole_0 @ (k4_xboole_0 @ X7 @ X8) @ (k4_xboole_0 @ X7 @ X9)))),
% 0.69/0.88      inference('cnf', [status(esa)], [l36_xboole_1])).
% 0.69/0.88  thf('85', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i]:
% 0.69/0.88         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.69/0.88           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ k1_xboole_0))),
% 0.69/0.88      inference('sup+', [status(thm)], ['83', '84'])).
% 0.69/0.88  thf('86', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 0.69/0.88      inference('demod', [status(thm)], ['59', '65'])).
% 0.69/0.88  thf('87', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i]:
% 0.69/0.88         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.69/0.88           = (k4_xboole_0 @ X0 @ X1))),
% 0.69/0.88      inference('demod', [status(thm)], ['85', '86'])).
% 0.69/0.88  thf('88', plain,
% 0.69/0.88      (![X4 : $i, X5 : $i]:
% 0.69/0.88         ((r1_tarski @ X4 @ X5) | ((k4_xboole_0 @ X4 @ X5) != (k1_xboole_0)))),
% 0.69/0.88      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.69/0.88  thf('89', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i]:
% 0.69/0.88         (((k4_xboole_0 @ X1 @ X0) != (k1_xboole_0))
% 0.69/0.88          | (r1_tarski @ X1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.69/0.88      inference('sup-', [status(thm)], ['87', '88'])).
% 0.69/0.88  thf('90', plain,
% 0.69/0.88      ((((k1_xboole_0) != (k1_xboole_0))
% 0.69/0.88        | (r1_tarski @ sk_B @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.69/0.88      inference('sup-', [status(thm)], ['82', '89'])).
% 0.69/0.88  thf('91', plain, ((r1_tarski @ sk_B @ (k3_xboole_0 @ sk_A @ sk_B))),
% 0.69/0.88      inference('simplify', [status(thm)], ['90'])).
% 0.69/0.88  thf(idempotence_k2_xboole_0, axiom,
% 0.69/0.88    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.69/0.88  thf('92', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.69/0.88      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.69/0.88  thf(t31_xboole_1, axiom,
% 0.69/0.88    (![A:$i,B:$i,C:$i]:
% 0.69/0.88     ( r1_tarski @
% 0.69/0.88       ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) @ 
% 0.69/0.88       ( k2_xboole_0 @ B @ C ) ))).
% 0.69/0.88  thf('93', plain,
% 0.69/0.88      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.69/0.88         (r1_tarski @ 
% 0.69/0.88          (k2_xboole_0 @ (k3_xboole_0 @ X13 @ X14) @ (k3_xboole_0 @ X13 @ X15)) @ 
% 0.69/0.88          (k2_xboole_0 @ X14 @ X15))),
% 0.69/0.88      inference('cnf', [status(esa)], [t31_xboole_1])).
% 0.69/0.88  thf('94', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i]:
% 0.69/0.88         (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X0))),
% 0.69/0.88      inference('sup+', [status(thm)], ['92', '93'])).
% 0.69/0.88  thf('95', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.69/0.88      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.69/0.88  thf('96', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.69/0.88      inference('demod', [status(thm)], ['94', '95'])).
% 0.69/0.88  thf('97', plain,
% 0.69/0.88      (![X1 : $i, X3 : $i]:
% 0.69/0.88         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 0.69/0.88      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.69/0.88  thf('98', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i]:
% 0.69/0.88         (~ (r1_tarski @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.69/0.88          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.69/0.88      inference('sup-', [status(thm)], ['96', '97'])).
% 0.69/0.88  thf('99', plain, (((sk_B) = (k3_xboole_0 @ sk_A @ sk_B))),
% 0.69/0.88      inference('sup-', [status(thm)], ['91', '98'])).
% 0.69/0.88  thf('100', plain,
% 0.69/0.88      (((k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.69/0.88      inference('demod', [status(thm)], ['79', '99'])).
% 0.69/0.88  thf('101', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.69/0.88      inference('sup-', [status(thm)], ['30', '31'])).
% 0.69/0.88  thf('102', plain,
% 0.69/0.88      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.69/0.88         ((k4_xboole_0 @ (k4_xboole_0 @ X17 @ X18) @ X19)
% 0.69/0.88           = (k4_xboole_0 @ X17 @ (k2_xboole_0 @ X18 @ X19)))),
% 0.69/0.88      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.69/0.88  thf('103', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i]:
% 0.69/0.88         ((k1_xboole_0)
% 0.69/0.88           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 0.69/0.88      inference('sup+', [status(thm)], ['101', '102'])).
% 0.69/0.88  thf('104', plain,
% 0.69/0.88      (![X4 : $i, X5 : $i]:
% 0.69/0.88         ((r1_tarski @ X4 @ X5) | ((k4_xboole_0 @ X4 @ X5) != (k1_xboole_0)))),
% 0.69/0.88      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.69/0.88  thf('105', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i]:
% 0.69/0.88         (((k1_xboole_0) != (k1_xboole_0))
% 0.69/0.88          | (r1_tarski @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 0.69/0.88      inference('sup-', [status(thm)], ['103', '104'])).
% 0.69/0.88  thf('106', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i]:
% 0.69/0.88         (r1_tarski @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.69/0.88      inference('simplify', [status(thm)], ['105'])).
% 0.69/0.88  thf('107', plain,
% 0.69/0.88      ((r1_tarski @ sk_A @ (k2_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.69/0.88      inference('sup+', [status(thm)], ['100', '106'])).
% 0.69/0.88  thf('108', plain,
% 0.69/0.88      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))
% 0.69/0.88         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.69/0.88      inference('split', [status(esa)], ['22'])).
% 0.69/0.88  thf('109', plain,
% 0.69/0.88      (![X4 : $i, X6 : $i]:
% 0.69/0.88         (((k4_xboole_0 @ X4 @ X6) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ X6))),
% 0.69/0.88      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.69/0.88  thf('110', plain,
% 0.69/0.88      ((((k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B) = (k1_xboole_0)))
% 0.69/0.88         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.69/0.88      inference('sup-', [status(thm)], ['108', '109'])).
% 0.69/0.88  thf('111', plain,
% 0.69/0.88      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) | 
% 0.69/0.88       (((sk_B) = (k2_subset_1 @ sk_A)))),
% 0.69/0.88      inference('split', [status(esa)], ['22'])).
% 0.69/0.88  thf('112', plain, (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.69/0.88      inference('sat_resolution*', [status(thm)], ['20', '71', '111'])).
% 0.69/0.88  thf('113', plain,
% 0.69/0.88      (((k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B) = (k1_xboole_0))),
% 0.69/0.88      inference('simpl_trail', [status(thm)], ['110', '112'])).
% 0.69/0.88  thf('114', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i]:
% 0.69/0.88         (((k4_xboole_0 @ X1 @ X0) != (k1_xboole_0))
% 0.69/0.88          | (r1_tarski @ X1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.69/0.88      inference('sup-', [status(thm)], ['87', '88'])).
% 0.69/0.88  thf('115', plain,
% 0.69/0.88      ((((k1_xboole_0) != (k1_xboole_0))
% 0.69/0.88        | (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ 
% 0.69/0.88           (k3_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))))),
% 0.69/0.88      inference('sup-', [status(thm)], ['113', '114'])).
% 0.69/0.88  thf('116', plain,
% 0.69/0.88      ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ 
% 0.69/0.88        (k3_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.69/0.88      inference('simplify', [status(thm)], ['115'])).
% 0.69/0.88  thf('117', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i]:
% 0.69/0.88         (~ (r1_tarski @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.69/0.88          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.69/0.88      inference('sup-', [status(thm)], ['96', '97'])).
% 0.69/0.88  thf('118', plain,
% 0.69/0.88      (((k3_subset_1 @ sk_A @ sk_B)
% 0.69/0.88         = (k3_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.69/0.88      inference('sup-', [status(thm)], ['116', '117'])).
% 0.69/0.88  thf('119', plain,
% 0.69/0.88      (![X20 : $i, X21 : $i]:
% 0.69/0.88         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X20 @ X21))
% 0.69/0.88           = (k3_xboole_0 @ X20 @ X21))),
% 0.69/0.88      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.69/0.88  thf('120', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i]:
% 0.69/0.88         ((X0) = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 0.69/0.88      inference('demod', [status(thm)], ['42', '47', '48'])).
% 0.69/0.88  thf('121', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i]:
% 0.69/0.88         ((X1) = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))),
% 0.69/0.88      inference('sup+', [status(thm)], ['119', '120'])).
% 0.69/0.88  thf('122', plain,
% 0.69/0.88      (((sk_B) = (k2_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.69/0.88      inference('sup+', [status(thm)], ['118', '121'])).
% 0.69/0.88  thf('123', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.69/0.88      inference('demod', [status(thm)], ['107', '122'])).
% 0.69/0.88  thf('124', plain, ($false), inference('demod', [status(thm)], ['74', '123'])).
% 0.69/0.88  
% 0.69/0.88  % SZS output end Refutation
% 0.69/0.88  
% 0.69/0.89  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
