%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.w4d2a8N2v9

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:02 EST 2020

% Result     : Theorem 0.67s
% Output     : Refutation 0.67s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 220 expanded)
%              Number of leaves         :   38 (  78 expanded)
%              Depth                    :   18
%              Number of atoms          :  813 (1672 expanded)
%              Number of equality atoms :   57 (  91 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t44_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_xboole_0 @ B @ ( k3_subset_1 @ A @ C ) )
          <=> ( r1_tarski @ B @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( ( r1_xboole_0 @ B @ ( k3_subset_1 @ A @ C ) )
            <=> ( r1_tarski @ B @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t44_subset_1])).

thf('0',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ sk_C_2 )
    | ~ ( r1_xboole_0 @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_C_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ sk_C_2 )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_C_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ sk_C_2 )
    | ~ ( r1_xboole_0 @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_C_2 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X48: $i,X49: $i] :
      ( ( ( k3_subset_1 @ X48 @ X49 )
        = ( k4_xboole_0 @ X48 @ X49 ) )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('5',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_2 )
    = ( k4_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( r1_tarski @ sk_B_1 @ sk_C_2 )
    | ( r1_xboole_0 @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_C_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( r1_tarski @ sk_B_1 @ sk_C_2 )
   <= ( r1_tarski @ sk_B_1 @ sk_C_2 ) ),
    inference(split,[status(esa)],['6'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('8',plain,(
    ! [X11: $i,X13: $i] :
      ( ( ( k4_xboole_0 @ X11 @ X13 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('9',plain,
    ( ( ( k4_xboole_0 @ sk_B_1 @ sk_C_2 )
      = k1_xboole_0 )
   <= ( r1_tarski @ sk_B_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t81_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ) )).

thf('10',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( r1_xboole_0 @ X27 @ ( k4_xboole_0 @ X28 @ X29 ) )
      | ~ ( r1_xboole_0 @ X28 @ ( k4_xboole_0 @ X27 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t81_xboole_1])).

thf('11',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 )
        | ( r1_xboole_0 @ sk_B_1 @ ( k4_xboole_0 @ X0 @ sk_C_2 ) ) )
   <= ( r1_tarski @ sk_B_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('12',plain,(
    ! [X18: $i] :
      ( ( k3_xboole_0 @ X18 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('13',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ X7 @ X8 )
      | ( r2_hidden @ ( sk_C @ X8 @ X7 ) @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('14',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('17',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ sk_B_1 @ ( k4_xboole_0 @ X0 @ sk_C_2 ) )
   <= ( r1_tarski @ sk_B_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['11','18'])).

thf('20',plain,
    ( ( r1_xboole_0 @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_C_2 ) )
   <= ( r1_tarski @ sk_B_1 @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['5','19'])).

thf('21',plain,
    ( ~ ( r1_xboole_0 @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_C_2 ) )
   <= ~ ( r1_xboole_0 @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_C_2 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('22',plain,
    ( ( r1_xboole_0 @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_C_2 ) )
    | ~ ( r1_tarski @ sk_B_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ~ ( r1_tarski @ sk_B_1 @ sk_C_2 ) ),
    inference('sat_resolution*',[status(thm)],['2','22'])).

thf('24',plain,(
    ~ ( r1_tarski @ sk_B_1 @ sk_C_2 ) ),
    inference(simpl_trail,[status(thm)],['1','23'])).

thf('25',plain,
    ( ( r1_xboole_0 @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_C_2 ) )
   <= ( r1_xboole_0 @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_C_2 ) ) ),
    inference(split,[status(esa)],['6'])).

thf('26',plain,
    ( ( r1_xboole_0 @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_C_2 ) )
    | ( r1_tarski @ sk_B_1 @ sk_C_2 ) ),
    inference(split,[status(esa)],['6'])).

thf('27',plain,(
    r1_xboole_0 @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_C_2 ) ),
    inference('sat_resolution*',[status(thm)],['2','22','26'])).

thf('28',plain,(
    r1_xboole_0 @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_C_2 ) ),
    inference(simpl_trail,[status(thm)],['25','27'])).

thf('29',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_2 )
    = ( k4_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('30',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( r1_xboole_0 @ X27 @ ( k4_xboole_0 @ X28 @ X29 ) )
      | ~ ( r1_xboole_0 @ X28 @ ( k4_xboole_0 @ X27 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t81_xboole_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_C_2 ) )
      | ( r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
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

thf('34',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X45 @ X46 )
      | ( r2_hidden @ X45 @ X46 )
      | ( v1_xboole_0 @ X46 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('35',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('36',plain,(
    ! [X50: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('37',plain,(
    r2_hidden @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['35','36'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('38',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( r2_hidden @ X43 @ X42 )
      | ( r1_tarski @ X43 @ X41 )
      | ( X42
       != ( k1_zfmisc_1 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('39',plain,(
    ! [X41: $i,X43: $i] :
      ( ( r1_tarski @ X43 @ X41 )
      | ~ ( r2_hidden @ X43 @ ( k1_zfmisc_1 @ X41 ) ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    r1_tarski @ sk_B_1 @ sk_A ),
    inference('sup-',[status(thm)],['37','39'])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('41',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( r1_tarski @ X24 @ X25 )
      | ~ ( r1_xboole_0 @ X25 @ X26 )
      | ( r1_xboole_0 @ X24 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_B_1 @ X0 )
      | ~ ( r1_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    r1_xboole_0 @ sk_B_1 @ ( k4_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['32','42'])).

thf('44',plain,(
    ! [X6: $i] :
      ( ( v1_xboole_0 @ X6 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('45',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ ( k3_xboole_0 @ X7 @ X10 ) )
      | ~ ( r1_xboole_0 @ X7 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v1_xboole_0 @ ( k3_xboole_0 @ sk_B_1 @ ( k4_xboole_0 @ sk_B_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('48',plain,(
    ! [X19: $i,X20: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X19 @ X20 ) @ X19 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('49',plain,(
    ! [X11: $i,X13: $i] :
      ( ( ( k4_xboole_0 @ X11 @ X13 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('51',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('52',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('53',plain,(
    ! [X23: $i] :
      ( ( k5_xboole_0 @ X23 @ k1_xboole_0 )
      = X23 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('55',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k3_xboole_0 @ X38 @ X39 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X38 @ X39 ) @ ( k2_xboole_0 @ X38 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('56',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X35 @ X36 ) @ X37 )
      = ( k5_xboole_0 @ X35 @ ( k5_xboole_0 @ X36 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('57',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k3_xboole_0 @ X38 @ X39 )
      = ( k5_xboole_0 @ X38 @ ( k5_xboole_0 @ X39 @ ( k2_xboole_0 @ X38 @ X39 ) ) ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['54','57'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('60',plain,(
    ! [X18: $i] :
      ( ( k3_xboole_0 @ X18 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('63',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ( ( k4_xboole_0 @ X11 @ X12 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['68'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('70',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k2_xboole_0 @ X17 @ X16 )
        = X16 )
      | ~ ( r1_tarski @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['58','61','71'])).

thf('73',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X35 @ X36 ) @ X37 )
      = ( k5_xboole_0 @ X35 @ ( k5_xboole_0 @ X36 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['51','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['50','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('80',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['78','79','80','81'])).

thf('83',plain,(
    v1_xboole_0 @ ( k4_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['47','82'])).

thf('84',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('85',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( v1_xboole_0 @ X33 )
      | ~ ( v1_xboole_0 @ X34 )
      | ( X33 = X34 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['83','86'])).

thf('88',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ( ( k4_xboole_0 @ X11 @ X12 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('89',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_B_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    r1_tarski @ sk_B_1 @ sk_C_2 ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,(
    $false ),
    inference(demod,[status(thm)],['24','90'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.w4d2a8N2v9
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:41:16 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.67/0.92  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.67/0.92  % Solved by: fo/fo7.sh
% 0.67/0.92  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.67/0.92  % done 1368 iterations in 0.460s
% 0.67/0.92  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.67/0.92  % SZS output start Refutation
% 0.67/0.92  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.67/0.92  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.67/0.92  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.67/0.92  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.67/0.92  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.67/0.92  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.67/0.92  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.67/0.92  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.67/0.92  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.67/0.92  thf(sk_B_type, type, sk_B: $i > $i).
% 0.67/0.92  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.67/0.92  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.67/0.92  thf(sk_A_type, type, sk_A: $i).
% 0.67/0.92  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.67/0.92  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.67/0.92  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.67/0.92  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.67/0.92  thf(t44_subset_1, conjecture,
% 0.67/0.92    (![A:$i,B:$i]:
% 0.67/0.92     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.67/0.92       ( ![C:$i]:
% 0.67/0.92         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.67/0.92           ( ( r1_xboole_0 @ B @ ( k3_subset_1 @ A @ C ) ) <=>
% 0.67/0.92             ( r1_tarski @ B @ C ) ) ) ) ))).
% 0.67/0.92  thf(zf_stmt_0, negated_conjecture,
% 0.67/0.92    (~( ![A:$i,B:$i]:
% 0.67/0.92        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.67/0.92          ( ![C:$i]:
% 0.67/0.92            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.67/0.92              ( ( r1_xboole_0 @ B @ ( k3_subset_1 @ A @ C ) ) <=>
% 0.67/0.92                ( r1_tarski @ B @ C ) ) ) ) ) )),
% 0.67/0.92    inference('cnf.neg', [status(esa)], [t44_subset_1])).
% 0.67/0.92  thf('0', plain,
% 0.67/0.92      ((~ (r1_tarski @ sk_B_1 @ sk_C_2)
% 0.67/0.92        | ~ (r1_xboole_0 @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_C_2)))),
% 0.67/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.92  thf('1', plain,
% 0.67/0.92      ((~ (r1_tarski @ sk_B_1 @ sk_C_2)) <= (~ ((r1_tarski @ sk_B_1 @ sk_C_2)))),
% 0.67/0.92      inference('split', [status(esa)], ['0'])).
% 0.67/0.92  thf('2', plain,
% 0.67/0.92      (~ ((r1_tarski @ sk_B_1 @ sk_C_2)) | 
% 0.67/0.92       ~ ((r1_xboole_0 @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_C_2)))),
% 0.67/0.92      inference('split', [status(esa)], ['0'])).
% 0.67/0.92  thf('3', plain, ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ sk_A))),
% 0.67/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.92  thf(d5_subset_1, axiom,
% 0.67/0.92    (![A:$i,B:$i]:
% 0.67/0.92     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.67/0.92       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.67/0.92  thf('4', plain,
% 0.67/0.92      (![X48 : $i, X49 : $i]:
% 0.67/0.92         (((k3_subset_1 @ X48 @ X49) = (k4_xboole_0 @ X48 @ X49))
% 0.67/0.92          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ X48)))),
% 0.67/0.92      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.67/0.92  thf('5', plain,
% 0.67/0.92      (((k3_subset_1 @ sk_A @ sk_C_2) = (k4_xboole_0 @ sk_A @ sk_C_2))),
% 0.67/0.92      inference('sup-', [status(thm)], ['3', '4'])).
% 0.67/0.92  thf('6', plain,
% 0.67/0.92      (((r1_tarski @ sk_B_1 @ sk_C_2)
% 0.67/0.92        | (r1_xboole_0 @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_C_2)))),
% 0.67/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.92  thf('7', plain,
% 0.67/0.92      (((r1_tarski @ sk_B_1 @ sk_C_2)) <= (((r1_tarski @ sk_B_1 @ sk_C_2)))),
% 0.67/0.92      inference('split', [status(esa)], ['6'])).
% 0.67/0.92  thf(l32_xboole_1, axiom,
% 0.67/0.92    (![A:$i,B:$i]:
% 0.67/0.92     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.67/0.92  thf('8', plain,
% 0.67/0.92      (![X11 : $i, X13 : $i]:
% 0.67/0.92         (((k4_xboole_0 @ X11 @ X13) = (k1_xboole_0))
% 0.67/0.92          | ~ (r1_tarski @ X11 @ X13))),
% 0.67/0.92      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.67/0.92  thf('9', plain,
% 0.67/0.92      ((((k4_xboole_0 @ sk_B_1 @ sk_C_2) = (k1_xboole_0)))
% 0.67/0.92         <= (((r1_tarski @ sk_B_1 @ sk_C_2)))),
% 0.67/0.92      inference('sup-', [status(thm)], ['7', '8'])).
% 0.67/0.92  thf(t81_xboole_1, axiom,
% 0.67/0.92    (![A:$i,B:$i,C:$i]:
% 0.67/0.92     ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.67/0.92       ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ))).
% 0.67/0.92  thf('10', plain,
% 0.67/0.92      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.67/0.92         ((r1_xboole_0 @ X27 @ (k4_xboole_0 @ X28 @ X29))
% 0.67/0.92          | ~ (r1_xboole_0 @ X28 @ (k4_xboole_0 @ X27 @ X29)))),
% 0.67/0.92      inference('cnf', [status(esa)], [t81_xboole_1])).
% 0.67/0.92  thf('11', plain,
% 0.67/0.92      ((![X0 : $i]:
% 0.67/0.92          (~ (r1_xboole_0 @ X0 @ k1_xboole_0)
% 0.67/0.92           | (r1_xboole_0 @ sk_B_1 @ (k4_xboole_0 @ X0 @ sk_C_2))))
% 0.67/0.92         <= (((r1_tarski @ sk_B_1 @ sk_C_2)))),
% 0.67/0.92      inference('sup-', [status(thm)], ['9', '10'])).
% 0.67/0.92  thf(t2_boole, axiom,
% 0.67/0.92    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.67/0.92  thf('12', plain,
% 0.67/0.92      (![X18 : $i]: ((k3_xboole_0 @ X18 @ k1_xboole_0) = (k1_xboole_0))),
% 0.67/0.92      inference('cnf', [status(esa)], [t2_boole])).
% 0.67/0.92  thf(t4_xboole_0, axiom,
% 0.67/0.92    (![A:$i,B:$i]:
% 0.67/0.92     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.67/0.92            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.67/0.92       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.67/0.92            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.67/0.92  thf('13', plain,
% 0.67/0.92      (![X7 : $i, X8 : $i]:
% 0.67/0.92         ((r1_xboole_0 @ X7 @ X8)
% 0.67/0.92          | (r2_hidden @ (sk_C @ X8 @ X7) @ (k3_xboole_0 @ X7 @ X8)))),
% 0.67/0.92      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.67/0.92  thf(d1_xboole_0, axiom,
% 0.67/0.92    (![A:$i]:
% 0.67/0.92     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.67/0.92  thf('14', plain,
% 0.67/0.92      (![X4 : $i, X5 : $i]: (~ (r2_hidden @ X4 @ X5) | ~ (v1_xboole_0 @ X5))),
% 0.67/0.92      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.67/0.92  thf('15', plain,
% 0.67/0.92      (![X0 : $i, X1 : $i]:
% 0.67/0.92         ((r1_xboole_0 @ X1 @ X0) | ~ (v1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.67/0.92      inference('sup-', [status(thm)], ['13', '14'])).
% 0.67/0.92  thf('16', plain,
% 0.67/0.92      (![X0 : $i]:
% 0.67/0.92         (~ (v1_xboole_0 @ k1_xboole_0) | (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.67/0.92      inference('sup-', [status(thm)], ['12', '15'])).
% 0.67/0.92  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.67/0.92  thf('17', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.67/0.92      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.67/0.92  thf('18', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.67/0.92      inference('demod', [status(thm)], ['16', '17'])).
% 0.67/0.92  thf('19', plain,
% 0.67/0.92      ((![X0 : $i]: (r1_xboole_0 @ sk_B_1 @ (k4_xboole_0 @ X0 @ sk_C_2)))
% 0.67/0.92         <= (((r1_tarski @ sk_B_1 @ sk_C_2)))),
% 0.67/0.92      inference('demod', [status(thm)], ['11', '18'])).
% 0.67/0.92  thf('20', plain,
% 0.67/0.92      (((r1_xboole_0 @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_C_2)))
% 0.67/0.92         <= (((r1_tarski @ sk_B_1 @ sk_C_2)))),
% 0.67/0.92      inference('sup+', [status(thm)], ['5', '19'])).
% 0.67/0.92  thf('21', plain,
% 0.67/0.92      ((~ (r1_xboole_0 @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_C_2)))
% 0.67/0.92         <= (~ ((r1_xboole_0 @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_C_2))))),
% 0.67/0.92      inference('split', [status(esa)], ['0'])).
% 0.67/0.92  thf('22', plain,
% 0.67/0.92      (((r1_xboole_0 @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_C_2))) | 
% 0.67/0.92       ~ ((r1_tarski @ sk_B_1 @ sk_C_2))),
% 0.67/0.92      inference('sup-', [status(thm)], ['20', '21'])).
% 0.67/0.92  thf('23', plain, (~ ((r1_tarski @ sk_B_1 @ sk_C_2))),
% 0.67/0.92      inference('sat_resolution*', [status(thm)], ['2', '22'])).
% 0.67/0.92  thf('24', plain, (~ (r1_tarski @ sk_B_1 @ sk_C_2)),
% 0.67/0.92      inference('simpl_trail', [status(thm)], ['1', '23'])).
% 0.67/0.92  thf('25', plain,
% 0.67/0.92      (((r1_xboole_0 @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_C_2)))
% 0.67/0.92         <= (((r1_xboole_0 @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_C_2))))),
% 0.67/0.92      inference('split', [status(esa)], ['6'])).
% 0.67/0.92  thf('26', plain,
% 0.67/0.92      (((r1_xboole_0 @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_C_2))) | 
% 0.67/0.92       ((r1_tarski @ sk_B_1 @ sk_C_2))),
% 0.67/0.92      inference('split', [status(esa)], ['6'])).
% 0.67/0.92  thf('27', plain, (((r1_xboole_0 @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_C_2)))),
% 0.67/0.92      inference('sat_resolution*', [status(thm)], ['2', '22', '26'])).
% 0.67/0.92  thf('28', plain, ((r1_xboole_0 @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_C_2))),
% 0.67/0.92      inference('simpl_trail', [status(thm)], ['25', '27'])).
% 0.67/0.92  thf('29', plain,
% 0.67/0.92      (((k3_subset_1 @ sk_A @ sk_C_2) = (k4_xboole_0 @ sk_A @ sk_C_2))),
% 0.67/0.92      inference('sup-', [status(thm)], ['3', '4'])).
% 0.67/0.92  thf('30', plain,
% 0.67/0.92      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.67/0.92         ((r1_xboole_0 @ X27 @ (k4_xboole_0 @ X28 @ X29))
% 0.67/0.92          | ~ (r1_xboole_0 @ X28 @ (k4_xboole_0 @ X27 @ X29)))),
% 0.67/0.92      inference('cnf', [status(esa)], [t81_xboole_1])).
% 0.67/0.92  thf('31', plain,
% 0.67/0.92      (![X0 : $i]:
% 0.67/0.92         (~ (r1_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_C_2))
% 0.67/0.92          | (r1_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_C_2)))),
% 0.67/0.92      inference('sup-', [status(thm)], ['29', '30'])).
% 0.67/0.92  thf('32', plain, ((r1_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.67/0.92      inference('sup-', [status(thm)], ['28', '31'])).
% 0.67/0.92  thf('33', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.67/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.92  thf(d2_subset_1, axiom,
% 0.67/0.92    (![A:$i,B:$i]:
% 0.67/0.92     ( ( ( v1_xboole_0 @ A ) =>
% 0.67/0.92         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.67/0.92       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.67/0.92         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.67/0.92  thf('34', plain,
% 0.67/0.92      (![X45 : $i, X46 : $i]:
% 0.67/0.92         (~ (m1_subset_1 @ X45 @ X46)
% 0.67/0.92          | (r2_hidden @ X45 @ X46)
% 0.67/0.92          | (v1_xboole_0 @ X46))),
% 0.67/0.92      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.67/0.92  thf('35', plain,
% 0.67/0.92      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.67/0.92        | (r2_hidden @ sk_B_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.67/0.92      inference('sup-', [status(thm)], ['33', '34'])).
% 0.67/0.92  thf(fc1_subset_1, axiom,
% 0.67/0.92    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.67/0.92  thf('36', plain, (![X50 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X50))),
% 0.67/0.92      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.67/0.92  thf('37', plain, ((r2_hidden @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.67/0.92      inference('clc', [status(thm)], ['35', '36'])).
% 0.67/0.92  thf(d1_zfmisc_1, axiom,
% 0.67/0.92    (![A:$i,B:$i]:
% 0.67/0.92     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.67/0.92       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.67/0.92  thf('38', plain,
% 0.67/0.92      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.67/0.92         (~ (r2_hidden @ X43 @ X42)
% 0.67/0.92          | (r1_tarski @ X43 @ X41)
% 0.67/0.92          | ((X42) != (k1_zfmisc_1 @ X41)))),
% 0.67/0.92      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.67/0.92  thf('39', plain,
% 0.67/0.92      (![X41 : $i, X43 : $i]:
% 0.67/0.92         ((r1_tarski @ X43 @ X41) | ~ (r2_hidden @ X43 @ (k1_zfmisc_1 @ X41)))),
% 0.67/0.92      inference('simplify', [status(thm)], ['38'])).
% 0.67/0.92  thf('40', plain, ((r1_tarski @ sk_B_1 @ sk_A)),
% 0.67/0.92      inference('sup-', [status(thm)], ['37', '39'])).
% 0.67/0.92  thf(t63_xboole_1, axiom,
% 0.67/0.92    (![A:$i,B:$i,C:$i]:
% 0.67/0.92     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.67/0.92       ( r1_xboole_0 @ A @ C ) ))).
% 0.67/0.92  thf('41', plain,
% 0.67/0.92      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.67/0.92         (~ (r1_tarski @ X24 @ X25)
% 0.67/0.92          | ~ (r1_xboole_0 @ X25 @ X26)
% 0.67/0.92          | (r1_xboole_0 @ X24 @ X26))),
% 0.67/0.92      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.67/0.92  thf('42', plain,
% 0.67/0.92      (![X0 : $i]: ((r1_xboole_0 @ sk_B_1 @ X0) | ~ (r1_xboole_0 @ sk_A @ X0))),
% 0.67/0.92      inference('sup-', [status(thm)], ['40', '41'])).
% 0.67/0.92  thf('43', plain, ((r1_xboole_0 @ sk_B_1 @ (k4_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.67/0.92      inference('sup-', [status(thm)], ['32', '42'])).
% 0.67/0.92  thf('44', plain,
% 0.67/0.92      (![X6 : $i]: ((v1_xboole_0 @ X6) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.67/0.92      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.67/0.92  thf('45', plain,
% 0.67/0.92      (![X7 : $i, X9 : $i, X10 : $i]:
% 0.67/0.92         (~ (r2_hidden @ X9 @ (k3_xboole_0 @ X7 @ X10))
% 0.67/0.92          | ~ (r1_xboole_0 @ X7 @ X10))),
% 0.67/0.92      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.67/0.92  thf('46', plain,
% 0.67/0.92      (![X0 : $i, X1 : $i]:
% 0.67/0.92         ((v1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.67/0.92      inference('sup-', [status(thm)], ['44', '45'])).
% 0.67/0.92  thf('47', plain,
% 0.67/0.92      ((v1_xboole_0 @ (k3_xboole_0 @ sk_B_1 @ (k4_xboole_0 @ sk_B_1 @ sk_C_2)))),
% 0.67/0.92      inference('sup-', [status(thm)], ['43', '46'])).
% 0.67/0.92  thf(t36_xboole_1, axiom,
% 0.67/0.92    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.67/0.92  thf('48', plain,
% 0.67/0.92      (![X19 : $i, X20 : $i]: (r1_tarski @ (k4_xboole_0 @ X19 @ X20) @ X19)),
% 0.67/0.92      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.67/0.92  thf('49', plain,
% 0.67/0.92      (![X11 : $i, X13 : $i]:
% 0.67/0.92         (((k4_xboole_0 @ X11 @ X13) = (k1_xboole_0))
% 0.67/0.92          | ~ (r1_tarski @ X11 @ X13))),
% 0.67/0.92      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.67/0.92  thf('50', plain,
% 0.67/0.92      (![X0 : $i, X1 : $i]:
% 0.67/0.92         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.67/0.92      inference('sup-', [status(thm)], ['48', '49'])).
% 0.67/0.92  thf(t100_xboole_1, axiom,
% 0.67/0.92    (![A:$i,B:$i]:
% 0.67/0.92     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.67/0.92  thf('51', plain,
% 0.67/0.92      (![X14 : $i, X15 : $i]:
% 0.67/0.92         ((k4_xboole_0 @ X14 @ X15)
% 0.67/0.92           = (k5_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)))),
% 0.67/0.92      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.67/0.92  thf(commutativity_k5_xboole_0, axiom,
% 0.67/0.92    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.67/0.92  thf('52', plain,
% 0.67/0.92      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.67/0.92      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.67/0.92  thf(t5_boole, axiom,
% 0.67/0.92    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.67/0.92  thf('53', plain, (![X23 : $i]: ((k5_xboole_0 @ X23 @ k1_xboole_0) = (X23))),
% 0.67/0.92      inference('cnf', [status(esa)], [t5_boole])).
% 0.67/0.92  thf('54', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.67/0.92      inference('sup+', [status(thm)], ['52', '53'])).
% 0.67/0.92  thf(t95_xboole_1, axiom,
% 0.67/0.92    (![A:$i,B:$i]:
% 0.67/0.92     ( ( k3_xboole_0 @ A @ B ) =
% 0.67/0.92       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.67/0.92  thf('55', plain,
% 0.67/0.92      (![X38 : $i, X39 : $i]:
% 0.67/0.92         ((k3_xboole_0 @ X38 @ X39)
% 0.67/0.92           = (k5_xboole_0 @ (k5_xboole_0 @ X38 @ X39) @ 
% 0.67/0.92              (k2_xboole_0 @ X38 @ X39)))),
% 0.67/0.92      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.67/0.92  thf(t91_xboole_1, axiom,
% 0.67/0.92    (![A:$i,B:$i,C:$i]:
% 0.67/0.92     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.67/0.92       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.67/0.92  thf('56', plain,
% 0.67/0.92      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.67/0.92         ((k5_xboole_0 @ (k5_xboole_0 @ X35 @ X36) @ X37)
% 0.67/0.92           = (k5_xboole_0 @ X35 @ (k5_xboole_0 @ X36 @ X37)))),
% 0.67/0.92      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.67/0.92  thf('57', plain,
% 0.67/0.92      (![X38 : $i, X39 : $i]:
% 0.67/0.92         ((k3_xboole_0 @ X38 @ X39)
% 0.67/0.92           = (k5_xboole_0 @ X38 @ 
% 0.67/0.92              (k5_xboole_0 @ X39 @ (k2_xboole_0 @ X38 @ X39))))),
% 0.67/0.92      inference('demod', [status(thm)], ['55', '56'])).
% 0.67/0.92  thf('58', plain,
% 0.67/0.92      (![X0 : $i]:
% 0.67/0.92         ((k3_xboole_0 @ k1_xboole_0 @ X0)
% 0.67/0.92           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.67/0.92      inference('sup+', [status(thm)], ['54', '57'])).
% 0.67/0.92  thf(commutativity_k3_xboole_0, axiom,
% 0.67/0.92    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.67/0.92  thf('59', plain,
% 0.67/0.92      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.67/0.92      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.67/0.92  thf('60', plain,
% 0.67/0.92      (![X18 : $i]: ((k3_xboole_0 @ X18 @ k1_xboole_0) = (k1_xboole_0))),
% 0.67/0.92      inference('cnf', [status(esa)], [t2_boole])).
% 0.67/0.92  thf('61', plain,
% 0.67/0.92      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.67/0.92      inference('sup+', [status(thm)], ['59', '60'])).
% 0.67/0.92  thf('62', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.67/0.92      inference('sup+', [status(thm)], ['52', '53'])).
% 0.67/0.92  thf('63', plain,
% 0.67/0.92      (![X14 : $i, X15 : $i]:
% 0.67/0.92         ((k4_xboole_0 @ X14 @ X15)
% 0.67/0.92           = (k5_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)))),
% 0.67/0.92      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.67/0.92  thf('64', plain,
% 0.67/0.92      (![X0 : $i]:
% 0.67/0.92         ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.67/0.92      inference('sup+', [status(thm)], ['62', '63'])).
% 0.67/0.92  thf('65', plain,
% 0.67/0.92      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.67/0.92      inference('sup+', [status(thm)], ['59', '60'])).
% 0.67/0.92  thf('66', plain,
% 0.67/0.92      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.67/0.92      inference('demod', [status(thm)], ['64', '65'])).
% 0.67/0.92  thf('67', plain,
% 0.67/0.92      (![X11 : $i, X12 : $i]:
% 0.67/0.92         ((r1_tarski @ X11 @ X12)
% 0.67/0.92          | ((k4_xboole_0 @ X11 @ X12) != (k1_xboole_0)))),
% 0.67/0.92      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.67/0.92  thf('68', plain,
% 0.67/0.92      (![X0 : $i]:
% 0.67/0.92         (((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ k1_xboole_0 @ X0))),
% 0.67/0.92      inference('sup-', [status(thm)], ['66', '67'])).
% 0.67/0.92  thf('69', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.67/0.92      inference('simplify', [status(thm)], ['68'])).
% 0.67/0.92  thf(t12_xboole_1, axiom,
% 0.67/0.92    (![A:$i,B:$i]:
% 0.67/0.92     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.67/0.92  thf('70', plain,
% 0.67/0.92      (![X16 : $i, X17 : $i]:
% 0.67/0.92         (((k2_xboole_0 @ X17 @ X16) = (X16)) | ~ (r1_tarski @ X17 @ X16))),
% 0.67/0.92      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.67/0.92  thf('71', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.67/0.92      inference('sup-', [status(thm)], ['69', '70'])).
% 0.67/0.92  thf('72', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.67/0.92      inference('demod', [status(thm)], ['58', '61', '71'])).
% 0.67/0.92  thf('73', plain,
% 0.67/0.92      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.67/0.92         ((k5_xboole_0 @ (k5_xboole_0 @ X35 @ X36) @ X37)
% 0.67/0.92           = (k5_xboole_0 @ X35 @ (k5_xboole_0 @ X36 @ X37)))),
% 0.67/0.92      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.67/0.92  thf('74', plain,
% 0.67/0.92      (![X0 : $i, X1 : $i]:
% 0.67/0.92         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.67/0.92           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.67/0.92      inference('sup+', [status(thm)], ['72', '73'])).
% 0.67/0.92  thf('75', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.67/0.92      inference('sup+', [status(thm)], ['52', '53'])).
% 0.67/0.92  thf('76', plain,
% 0.67/0.92      (![X0 : $i, X1 : $i]:
% 0.67/0.92         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.67/0.92      inference('demod', [status(thm)], ['74', '75'])).
% 0.67/0.92  thf('77', plain,
% 0.67/0.92      (![X0 : $i, X1 : $i]:
% 0.67/0.92         ((k3_xboole_0 @ X1 @ X0)
% 0.67/0.92           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.67/0.92      inference('sup+', [status(thm)], ['51', '76'])).
% 0.67/0.92  thf('78', plain,
% 0.67/0.92      (![X0 : $i, X1 : $i]:
% 0.67/0.92         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 0.67/0.92           = (k5_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ k1_xboole_0))),
% 0.67/0.92      inference('sup+', [status(thm)], ['50', '77'])).
% 0.67/0.92  thf('79', plain,
% 0.67/0.92      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.67/0.92      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.67/0.92  thf('80', plain,
% 0.67/0.92      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.67/0.92      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.67/0.92  thf('81', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.67/0.92      inference('sup+', [status(thm)], ['52', '53'])).
% 0.67/0.92  thf('82', plain,
% 0.67/0.92      (![X0 : $i, X1 : $i]:
% 0.67/0.92         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.67/0.92           = (k4_xboole_0 @ X0 @ X1))),
% 0.67/0.92      inference('demod', [status(thm)], ['78', '79', '80', '81'])).
% 0.67/0.92  thf('83', plain, ((v1_xboole_0 @ (k4_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.67/0.92      inference('demod', [status(thm)], ['47', '82'])).
% 0.67/0.92  thf('84', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.67/0.92      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.67/0.92  thf(t8_boole, axiom,
% 0.67/0.92    (![A:$i,B:$i]:
% 0.67/0.92     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.67/0.92  thf('85', plain,
% 0.67/0.92      (![X33 : $i, X34 : $i]:
% 0.67/0.92         (~ (v1_xboole_0 @ X33) | ~ (v1_xboole_0 @ X34) | ((X33) = (X34)))),
% 0.67/0.92      inference('cnf', [status(esa)], [t8_boole])).
% 0.67/0.92  thf('86', plain,
% 0.67/0.92      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.67/0.92      inference('sup-', [status(thm)], ['84', '85'])).
% 0.67/0.92  thf('87', plain, (((k1_xboole_0) = (k4_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.67/0.92      inference('sup-', [status(thm)], ['83', '86'])).
% 0.67/0.92  thf('88', plain,
% 0.67/0.92      (![X11 : $i, X12 : $i]:
% 0.67/0.92         ((r1_tarski @ X11 @ X12)
% 0.67/0.92          | ((k4_xboole_0 @ X11 @ X12) != (k1_xboole_0)))),
% 0.67/0.92      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.67/0.92  thf('89', plain,
% 0.67/0.92      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ sk_B_1 @ sk_C_2))),
% 0.67/0.92      inference('sup-', [status(thm)], ['87', '88'])).
% 0.67/0.92  thf('90', plain, ((r1_tarski @ sk_B_1 @ sk_C_2)),
% 0.67/0.92      inference('simplify', [status(thm)], ['89'])).
% 0.67/0.92  thf('91', plain, ($false), inference('demod', [status(thm)], ['24', '90'])).
% 0.67/0.92  
% 0.67/0.92  % SZS output end Refutation
% 0.67/0.92  
% 0.79/0.93  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
