%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BejQsjX2dF

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:07 EST 2020

% Result     : Theorem 3.14s
% Output     : Refutation 3.14s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 377 expanded)
%              Number of leaves         :   40 ( 127 expanded)
%              Depth                    :   20
%              Number of atoms          : 1001 (3098 expanded)
%              Number of equality atoms :   55 ( 150 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t31_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ C )
          <=> ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( ( r1_tarski @ B @ C )
            <=> ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t31_subset_1])).

thf('0',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ~ ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ~ ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('6',plain,(
    ! [X50: $i,X51: $i] :
      ( ( ( k3_subset_1 @ X50 @ X51 )
        = ( k4_xboole_0 @ X50 @ X51 ) )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('7',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t106_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('8',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X7 @ X9 )
      | ~ ( r1_tarski @ X7 @ ( k4_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_subset_1 @ sk_A @ sk_B ) )
      | ( r1_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( r1_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ sk_B )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('11',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ~ ( r1_xboole_0 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('12',plain,
    ( ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X50: $i,X51: $i] :
      ( ( ( k3_subset_1 @ X50 @ X51 )
        = ( k4_xboole_0 @ X50 @ X51 ) )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('15',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('16',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) )
      = ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('17',plain,
    ( ( k2_xboole_0 @ sk_C_1 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
    = ( k2_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('19',plain,(
    ! [X47: $i,X48: $i] :
      ( ~ ( m1_subset_1 @ X47 @ X48 )
      | ( r2_hidden @ X47 @ X48 )
      | ( v1_xboole_0 @ X48 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('20',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('21',plain,(
    ! [X52: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('22',plain,(
    r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['20','21'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('23',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( r2_hidden @ X43 @ X42 )
      | ( r1_tarski @ X43 @ X41 )
      | ( X42
       != ( k1_zfmisc_1 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('24',plain,(
    ! [X41: $i,X43: $i] :
      ( ( r1_tarski @ X43 @ X41 )
      | ~ ( r2_hidden @ X43 @ ( k1_zfmisc_1 @ X41 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    r1_tarski @ sk_C_1 @ sk_A ),
    inference('sup-',[status(thm)],['22','24'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('26',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X15 @ X16 ) @ X15 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('27',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X12 @ X13 )
      | ~ ( r1_tarski @ X13 @ X14 )
      | ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_C_1 @ X0 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('30',plain,(
    ! [X26: $i,X27: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X26 @ X27 ) @ X27 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('31',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( r1_xboole_0 @ X21 @ X22 )
      | ~ ( r1_tarski @ X21 @ X22 )
      | ( v1_xboole_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_xboole_0 @ ( k4_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('34',plain,(
    ! [X2: $i] :
      ( ( X2 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('35',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) )
      = ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('37',plain,
    ( ( k2_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X15 @ X16 ) @ X15 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('39',plain,(
    ! [X20: $i] :
      ( ( X20 = k1_xboole_0 )
      | ~ ( r1_tarski @ X20 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('41',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k2_xboole_0 @ X34 @ X35 )
      = ( k5_xboole_0 @ X34 @ ( k4_xboole_0 @ X35 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('43',plain,(
    ! [X19: $i] :
      ( ( k4_xboole_0 @ X19 @ k1_xboole_0 )
      = X19 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('44',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('47',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X10 @ X11 ) @ X10 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X20: $i] :
      ( ( X20 = k1_xboole_0 )
      | ~ ( r1_tarski @ X20 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['45','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['42','51'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('53',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k2_tarski @ X37 @ X36 )
      = ( k2_tarski @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('54',plain,(
    ! [X45: $i,X46: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X45 @ X46 ) )
      = ( k2_xboole_0 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X45: $i,X46: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X45 @ X46 ) )
      = ( k2_xboole_0 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['37','52','57'])).

thf('59',plain,
    ( ( k2_xboole_0 @ sk_C_1 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
    = sk_A ),
    inference(demod,[status(thm)],['17','58'])).

thf(t73_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf('60',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( r1_tarski @ X23 @ X24 )
      | ~ ( r1_tarski @ X23 @ ( k2_xboole_0 @ X24 @ X25 ) )
      | ~ ( r1_xboole_0 @ X23 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t73_xboole_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( r1_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
      | ( r1_tarski @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( ( r1_tarski @ sk_B @ sk_C_1 )
      | ~ ( r1_tarski @ sk_B @ sk_A ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X47: $i,X48: $i] :
      ( ~ ( m1_subset_1 @ X47 @ X48 )
      | ( r2_hidden @ X47 @ X48 )
      | ( v1_xboole_0 @ X48 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('65',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X52: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('67',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X41: $i,X43: $i] :
      ( ( r1_tarski @ X43 @ X41 )
      | ~ ( r2_hidden @ X43 @ ( k1_zfmisc_1 @ X41 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('69',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( r1_tarski @ sk_B @ sk_C_1 )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['62','69'])).

thf('71',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C_1 )
   <= ~ ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('72',plain,
    ( ( r1_tarski @ sk_B @ sk_C_1 )
    | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['2','72'])).

thf('74',plain,(
    ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['1','73'])).

thf('75',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('76',plain,
    ( ( r1_tarski @ sk_B @ sk_C_1 )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['3'])).

thf(t85_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ) )).

thf('77',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( r1_tarski @ X28 @ X29 )
      | ( r1_xboole_0 @ X28 @ ( k4_xboole_0 @ X30 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('78',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ sk_C_1 ) )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['75','78'])).

thf('80',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ~ ( r1_xboole_0 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('81',plain,
    ( ( r1_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ sk_B )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( r1_tarski @ sk_B @ sk_C_1 )
    | ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['3'])).

thf('83',plain,(
    r1_tarski @ sk_B @ sk_C_1 ),
    inference('sat_resolution*',[status(thm)],['2','72','82'])).

thf('84',plain,(
    r1_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ sk_B ),
    inference(simpl_trail,[status(thm)],['81','83'])).

thf('85',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('86',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) )
      = ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('87',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['67','68'])).

thf('89',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('90',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('92',plain,(
    v1_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X2: $i] :
      ( ( X2 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('94',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) )
      = ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('96',plain,
    ( ( k2_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['42','51'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('99',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['96','97','98'])).

thf('100',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['87','99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('102',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( r1_tarski @ X23 @ X24 )
      | ~ ( r1_tarski @ X23 @ ( k2_xboole_0 @ X24 @ X25 ) )
      | ~ ( r1_xboole_0 @ X23 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t73_xboole_1])).

thf('103',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X2 @ X1 )
      | ( r1_tarski @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( r1_tarski @ X0 @ ( k3_subset_1 @ sk_A @ sk_B ) )
      | ~ ( r1_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['100','103'])).

thf('105',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['84','104'])).

thf('106',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('107',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X15 @ X16 ) @ X15 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('108',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ sk_A ),
    inference('sup+',[status(thm)],['106','107'])).

thf('109',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['105','108'])).

thf('110',plain,(
    $false ),
    inference(demod,[status(thm)],['74','109'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BejQsjX2dF
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:48:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 3.14/3.37  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.14/3.37  % Solved by: fo/fo7.sh
% 3.14/3.37  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.14/3.37  % done 5893 iterations in 2.928s
% 3.14/3.37  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.14/3.37  % SZS output start Refutation
% 3.14/3.37  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.14/3.37  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 3.14/3.37  thf(sk_C_1_type, type, sk_C_1: $i).
% 3.14/3.37  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 3.14/3.37  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.14/3.37  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 3.14/3.37  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 3.14/3.37  thf(sk_A_type, type, sk_A: $i).
% 3.14/3.37  thf(sk_B_type, type, sk_B: $i).
% 3.14/3.37  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 3.14/3.37  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.14/3.37  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 3.14/3.37  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.14/3.37  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 3.14/3.37  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 3.14/3.37  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.14/3.37  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.14/3.37  thf(t31_subset_1, conjecture,
% 3.14/3.37    (![A:$i,B:$i]:
% 3.14/3.37     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 3.14/3.37       ( ![C:$i]:
% 3.14/3.37         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 3.14/3.37           ( ( r1_tarski @ B @ C ) <=>
% 3.14/3.37             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 3.14/3.37  thf(zf_stmt_0, negated_conjecture,
% 3.14/3.37    (~( ![A:$i,B:$i]:
% 3.14/3.37        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 3.14/3.37          ( ![C:$i]:
% 3.14/3.37            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 3.14/3.37              ( ( r1_tarski @ B @ C ) <=>
% 3.14/3.37                ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) )),
% 3.14/3.37    inference('cnf.neg', [status(esa)], [t31_subset_1])).
% 3.14/3.37  thf('0', plain,
% 3.14/3.37      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 3.14/3.37           (k3_subset_1 @ sk_A @ sk_B))
% 3.14/3.37        | ~ (r1_tarski @ sk_B @ sk_C_1))),
% 3.14/3.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.14/3.37  thf('1', plain,
% 3.14/3.37      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 3.14/3.37           (k3_subset_1 @ sk_A @ sk_B)))
% 3.14/3.37         <= (~
% 3.14/3.37             ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 3.14/3.37               (k3_subset_1 @ sk_A @ sk_B))))),
% 3.14/3.37      inference('split', [status(esa)], ['0'])).
% 3.14/3.37  thf('2', plain,
% 3.14/3.37      (~
% 3.14/3.37       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 3.14/3.37         (k3_subset_1 @ sk_A @ sk_B))) | 
% 3.14/3.37       ~ ((r1_tarski @ sk_B @ sk_C_1))),
% 3.14/3.37      inference('split', [status(esa)], ['0'])).
% 3.14/3.37  thf('3', plain,
% 3.14/3.37      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 3.14/3.37         (k3_subset_1 @ sk_A @ sk_B))
% 3.14/3.37        | (r1_tarski @ sk_B @ sk_C_1))),
% 3.14/3.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.14/3.37  thf('4', plain,
% 3.14/3.37      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 3.14/3.37         (k3_subset_1 @ sk_A @ sk_B)))
% 3.14/3.37         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 3.14/3.37               (k3_subset_1 @ sk_A @ sk_B))))),
% 3.14/3.37      inference('split', [status(esa)], ['3'])).
% 3.14/3.37  thf('5', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 3.14/3.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.14/3.37  thf(d5_subset_1, axiom,
% 3.14/3.37    (![A:$i,B:$i]:
% 3.14/3.37     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 3.14/3.37       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 3.14/3.37  thf('6', plain,
% 3.14/3.37      (![X50 : $i, X51 : $i]:
% 3.14/3.37         (((k3_subset_1 @ X50 @ X51) = (k4_xboole_0 @ X50 @ X51))
% 3.14/3.37          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ X50)))),
% 3.14/3.37      inference('cnf', [status(esa)], [d5_subset_1])).
% 3.14/3.37  thf('7', plain,
% 3.14/3.37      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 3.14/3.37      inference('sup-', [status(thm)], ['5', '6'])).
% 3.14/3.37  thf(t106_xboole_1, axiom,
% 3.14/3.37    (![A:$i,B:$i,C:$i]:
% 3.14/3.37     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 3.14/3.37       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 3.14/3.37  thf('8', plain,
% 3.14/3.37      (![X7 : $i, X8 : $i, X9 : $i]:
% 3.14/3.37         ((r1_xboole_0 @ X7 @ X9)
% 3.14/3.37          | ~ (r1_tarski @ X7 @ (k4_xboole_0 @ X8 @ X9)))),
% 3.14/3.37      inference('cnf', [status(esa)], [t106_xboole_1])).
% 3.14/3.37  thf('9', plain,
% 3.14/3.37      (![X0 : $i]:
% 3.14/3.37         (~ (r1_tarski @ X0 @ (k3_subset_1 @ sk_A @ sk_B))
% 3.14/3.37          | (r1_xboole_0 @ X0 @ sk_B))),
% 3.14/3.37      inference('sup-', [status(thm)], ['7', '8'])).
% 3.14/3.37  thf('10', plain,
% 3.14/3.37      (((r1_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C_1) @ sk_B))
% 3.14/3.37         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 3.14/3.37               (k3_subset_1 @ sk_A @ sk_B))))),
% 3.14/3.37      inference('sup-', [status(thm)], ['4', '9'])).
% 3.14/3.37  thf(symmetry_r1_xboole_0, axiom,
% 3.14/3.37    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 3.14/3.37  thf('11', plain,
% 3.14/3.37      (![X3 : $i, X4 : $i]:
% 3.14/3.37         ((r1_xboole_0 @ X3 @ X4) | ~ (r1_xboole_0 @ X4 @ X3))),
% 3.14/3.37      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 3.14/3.37  thf('12', plain,
% 3.14/3.37      (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)))
% 3.14/3.37         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 3.14/3.37               (k3_subset_1 @ sk_A @ sk_B))))),
% 3.14/3.37      inference('sup-', [status(thm)], ['10', '11'])).
% 3.14/3.37  thf('13', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 3.14/3.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.14/3.37  thf('14', plain,
% 3.14/3.37      (![X50 : $i, X51 : $i]:
% 3.14/3.37         (((k3_subset_1 @ X50 @ X51) = (k4_xboole_0 @ X50 @ X51))
% 3.14/3.37          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ X50)))),
% 3.14/3.37      inference('cnf', [status(esa)], [d5_subset_1])).
% 3.14/3.37  thf('15', plain,
% 3.14/3.37      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 3.14/3.37      inference('sup-', [status(thm)], ['13', '14'])).
% 3.14/3.37  thf(t39_xboole_1, axiom,
% 3.14/3.37    (![A:$i,B:$i]:
% 3.14/3.37     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 3.14/3.37  thf('16', plain,
% 3.14/3.37      (![X17 : $i, X18 : $i]:
% 3.14/3.37         ((k2_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X17))
% 3.14/3.37           = (k2_xboole_0 @ X17 @ X18))),
% 3.14/3.37      inference('cnf', [status(esa)], [t39_xboole_1])).
% 3.14/3.37  thf('17', plain,
% 3.14/3.37      (((k2_xboole_0 @ sk_C_1 @ (k3_subset_1 @ sk_A @ sk_C_1))
% 3.14/3.37         = (k2_xboole_0 @ sk_C_1 @ sk_A))),
% 3.14/3.37      inference('sup+', [status(thm)], ['15', '16'])).
% 3.14/3.37  thf('18', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 3.14/3.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.14/3.37  thf(d2_subset_1, axiom,
% 3.14/3.37    (![A:$i,B:$i]:
% 3.14/3.37     ( ( ( v1_xboole_0 @ A ) =>
% 3.14/3.37         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 3.14/3.37       ( ( ~( v1_xboole_0 @ A ) ) =>
% 3.14/3.37         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 3.14/3.37  thf('19', plain,
% 3.14/3.37      (![X47 : $i, X48 : $i]:
% 3.14/3.37         (~ (m1_subset_1 @ X47 @ X48)
% 3.14/3.37          | (r2_hidden @ X47 @ X48)
% 3.14/3.37          | (v1_xboole_0 @ X48))),
% 3.14/3.37      inference('cnf', [status(esa)], [d2_subset_1])).
% 3.14/3.37  thf('20', plain,
% 3.14/3.37      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 3.14/3.37        | (r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A)))),
% 3.14/3.37      inference('sup-', [status(thm)], ['18', '19'])).
% 3.14/3.37  thf(fc1_subset_1, axiom,
% 3.14/3.37    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 3.14/3.37  thf('21', plain, (![X52 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X52))),
% 3.14/3.37      inference('cnf', [status(esa)], [fc1_subset_1])).
% 3.14/3.37  thf('22', plain, ((r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 3.14/3.37      inference('clc', [status(thm)], ['20', '21'])).
% 3.14/3.37  thf(d1_zfmisc_1, axiom,
% 3.14/3.37    (![A:$i,B:$i]:
% 3.14/3.37     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 3.14/3.37       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 3.14/3.37  thf('23', plain,
% 3.14/3.37      (![X41 : $i, X42 : $i, X43 : $i]:
% 3.14/3.37         (~ (r2_hidden @ X43 @ X42)
% 3.14/3.37          | (r1_tarski @ X43 @ X41)
% 3.14/3.37          | ((X42) != (k1_zfmisc_1 @ X41)))),
% 3.14/3.37      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 3.14/3.37  thf('24', plain,
% 3.14/3.37      (![X41 : $i, X43 : $i]:
% 3.14/3.37         ((r1_tarski @ X43 @ X41) | ~ (r2_hidden @ X43 @ (k1_zfmisc_1 @ X41)))),
% 3.14/3.37      inference('simplify', [status(thm)], ['23'])).
% 3.14/3.37  thf('25', plain, ((r1_tarski @ sk_C_1 @ sk_A)),
% 3.14/3.37      inference('sup-', [status(thm)], ['22', '24'])).
% 3.14/3.37  thf(t36_xboole_1, axiom,
% 3.14/3.37    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 3.14/3.37  thf('26', plain,
% 3.14/3.37      (![X15 : $i, X16 : $i]: (r1_tarski @ (k4_xboole_0 @ X15 @ X16) @ X15)),
% 3.14/3.37      inference('cnf', [status(esa)], [t36_xboole_1])).
% 3.14/3.37  thf(t1_xboole_1, axiom,
% 3.14/3.37    (![A:$i,B:$i,C:$i]:
% 3.14/3.37     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 3.14/3.37       ( r1_tarski @ A @ C ) ))).
% 3.14/3.37  thf('27', plain,
% 3.14/3.37      (![X12 : $i, X13 : $i, X14 : $i]:
% 3.14/3.37         (~ (r1_tarski @ X12 @ X13)
% 3.14/3.37          | ~ (r1_tarski @ X13 @ X14)
% 3.14/3.37          | (r1_tarski @ X12 @ X14))),
% 3.14/3.37      inference('cnf', [status(esa)], [t1_xboole_1])).
% 3.14/3.37  thf('28', plain,
% 3.14/3.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.14/3.37         ((r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 3.14/3.37      inference('sup-', [status(thm)], ['26', '27'])).
% 3.14/3.37  thf('29', plain,
% 3.14/3.37      (![X0 : $i]: (r1_tarski @ (k4_xboole_0 @ sk_C_1 @ X0) @ sk_A)),
% 3.14/3.37      inference('sup-', [status(thm)], ['25', '28'])).
% 3.14/3.37  thf(t79_xboole_1, axiom,
% 3.14/3.37    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 3.14/3.37  thf('30', plain,
% 3.14/3.37      (![X26 : $i, X27 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X26 @ X27) @ X27)),
% 3.14/3.37      inference('cnf', [status(esa)], [t79_xboole_1])).
% 3.14/3.37  thf(t69_xboole_1, axiom,
% 3.14/3.37    (![A:$i,B:$i]:
% 3.14/3.37     ( ( ~( v1_xboole_0 @ B ) ) =>
% 3.14/3.37       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 3.14/3.37  thf('31', plain,
% 3.14/3.37      (![X21 : $i, X22 : $i]:
% 3.14/3.37         (~ (r1_xboole_0 @ X21 @ X22)
% 3.14/3.37          | ~ (r1_tarski @ X21 @ X22)
% 3.14/3.37          | (v1_xboole_0 @ X21))),
% 3.14/3.37      inference('cnf', [status(esa)], [t69_xboole_1])).
% 3.14/3.37  thf('32', plain,
% 3.14/3.37      (![X0 : $i, X1 : $i]:
% 3.14/3.37         ((v1_xboole_0 @ (k4_xboole_0 @ X1 @ X0))
% 3.14/3.37          | ~ (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 3.14/3.37      inference('sup-', [status(thm)], ['30', '31'])).
% 3.14/3.37  thf('33', plain, ((v1_xboole_0 @ (k4_xboole_0 @ sk_C_1 @ sk_A))),
% 3.14/3.37      inference('sup-', [status(thm)], ['29', '32'])).
% 3.14/3.37  thf(l13_xboole_0, axiom,
% 3.14/3.37    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 3.14/3.37  thf('34', plain,
% 3.14/3.37      (![X2 : $i]: (((X2) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X2))),
% 3.14/3.37      inference('cnf', [status(esa)], [l13_xboole_0])).
% 3.14/3.37  thf('35', plain, (((k4_xboole_0 @ sk_C_1 @ sk_A) = (k1_xboole_0))),
% 3.14/3.37      inference('sup-', [status(thm)], ['33', '34'])).
% 3.14/3.37  thf('36', plain,
% 3.14/3.37      (![X17 : $i, X18 : $i]:
% 3.14/3.37         ((k2_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X17))
% 3.14/3.37           = (k2_xboole_0 @ X17 @ X18))),
% 3.14/3.37      inference('cnf', [status(esa)], [t39_xboole_1])).
% 3.14/3.37  thf('37', plain,
% 3.14/3.37      (((k2_xboole_0 @ sk_A @ k1_xboole_0) = (k2_xboole_0 @ sk_A @ sk_C_1))),
% 3.14/3.37      inference('sup+', [status(thm)], ['35', '36'])).
% 3.14/3.37  thf('38', plain,
% 3.14/3.37      (![X15 : $i, X16 : $i]: (r1_tarski @ (k4_xboole_0 @ X15 @ X16) @ X15)),
% 3.14/3.37      inference('cnf', [status(esa)], [t36_xboole_1])).
% 3.14/3.37  thf(t3_xboole_1, axiom,
% 3.14/3.37    (![A:$i]:
% 3.14/3.37     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 3.14/3.37  thf('39', plain,
% 3.14/3.37      (![X20 : $i]:
% 3.14/3.37         (((X20) = (k1_xboole_0)) | ~ (r1_tarski @ X20 @ k1_xboole_0))),
% 3.14/3.37      inference('cnf', [status(esa)], [t3_xboole_1])).
% 3.14/3.37  thf('40', plain,
% 3.14/3.37      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 3.14/3.37      inference('sup-', [status(thm)], ['38', '39'])).
% 3.14/3.37  thf(t98_xboole_1, axiom,
% 3.14/3.37    (![A:$i,B:$i]:
% 3.14/3.37     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 3.14/3.37  thf('41', plain,
% 3.14/3.37      (![X34 : $i, X35 : $i]:
% 3.14/3.37         ((k2_xboole_0 @ X34 @ X35)
% 3.14/3.37           = (k5_xboole_0 @ X34 @ (k4_xboole_0 @ X35 @ X34)))),
% 3.14/3.37      inference('cnf', [status(esa)], [t98_xboole_1])).
% 3.14/3.37  thf('42', plain,
% 3.14/3.37      (![X0 : $i]:
% 3.14/3.37         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 3.14/3.37      inference('sup+', [status(thm)], ['40', '41'])).
% 3.14/3.37  thf(t3_boole, axiom,
% 3.14/3.37    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 3.14/3.37  thf('43', plain, (![X19 : $i]: ((k4_xboole_0 @ X19 @ k1_xboole_0) = (X19))),
% 3.14/3.37      inference('cnf', [status(esa)], [t3_boole])).
% 3.14/3.37  thf(t100_xboole_1, axiom,
% 3.14/3.37    (![A:$i,B:$i]:
% 3.14/3.37     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 3.14/3.37  thf('44', plain,
% 3.14/3.37      (![X5 : $i, X6 : $i]:
% 3.14/3.37         ((k4_xboole_0 @ X5 @ X6)
% 3.14/3.37           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 3.14/3.37      inference('cnf', [status(esa)], [t100_xboole_1])).
% 3.14/3.37  thf('45', plain,
% 3.14/3.37      (![X0 : $i]:
% 3.14/3.37         ((X0) = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ k1_xboole_0)))),
% 3.14/3.37      inference('sup+', [status(thm)], ['43', '44'])).
% 3.14/3.37  thf(commutativity_k3_xboole_0, axiom,
% 3.14/3.37    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 3.14/3.37  thf('46', plain,
% 3.14/3.37      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.14/3.37      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.14/3.37  thf(t17_xboole_1, axiom,
% 3.14/3.37    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 3.14/3.37  thf('47', plain,
% 3.14/3.37      (![X10 : $i, X11 : $i]: (r1_tarski @ (k3_xboole_0 @ X10 @ X11) @ X10)),
% 3.14/3.37      inference('cnf', [status(esa)], [t17_xboole_1])).
% 3.14/3.37  thf('48', plain,
% 3.14/3.37      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 3.14/3.37      inference('sup+', [status(thm)], ['46', '47'])).
% 3.14/3.37  thf('49', plain,
% 3.14/3.37      (![X20 : $i]:
% 3.14/3.37         (((X20) = (k1_xboole_0)) | ~ (r1_tarski @ X20 @ k1_xboole_0))),
% 3.14/3.37      inference('cnf', [status(esa)], [t3_xboole_1])).
% 3.14/3.37  thf('50', plain,
% 3.14/3.37      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 3.14/3.37      inference('sup-', [status(thm)], ['48', '49'])).
% 3.14/3.37  thf('51', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 3.14/3.37      inference('demod', [status(thm)], ['45', '50'])).
% 3.14/3.37  thf('52', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 3.14/3.37      inference('demod', [status(thm)], ['42', '51'])).
% 3.14/3.37  thf(commutativity_k2_tarski, axiom,
% 3.14/3.37    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 3.14/3.37  thf('53', plain,
% 3.14/3.37      (![X36 : $i, X37 : $i]:
% 3.14/3.37         ((k2_tarski @ X37 @ X36) = (k2_tarski @ X36 @ X37))),
% 3.14/3.37      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 3.14/3.37  thf(l51_zfmisc_1, axiom,
% 3.14/3.37    (![A:$i,B:$i]:
% 3.14/3.37     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 3.14/3.37  thf('54', plain,
% 3.14/3.37      (![X45 : $i, X46 : $i]:
% 3.14/3.37         ((k3_tarski @ (k2_tarski @ X45 @ X46)) = (k2_xboole_0 @ X45 @ X46))),
% 3.14/3.37      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 3.14/3.37  thf('55', plain,
% 3.14/3.37      (![X0 : $i, X1 : $i]:
% 3.14/3.37         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 3.14/3.37      inference('sup+', [status(thm)], ['53', '54'])).
% 3.14/3.37  thf('56', plain,
% 3.14/3.37      (![X45 : $i, X46 : $i]:
% 3.14/3.37         ((k3_tarski @ (k2_tarski @ X45 @ X46)) = (k2_xboole_0 @ X45 @ X46))),
% 3.14/3.37      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 3.14/3.37  thf('57', plain,
% 3.14/3.37      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 3.14/3.37      inference('sup+', [status(thm)], ['55', '56'])).
% 3.14/3.37  thf('58', plain, (((sk_A) = (k2_xboole_0 @ sk_C_1 @ sk_A))),
% 3.14/3.37      inference('demod', [status(thm)], ['37', '52', '57'])).
% 3.14/3.37  thf('59', plain,
% 3.14/3.37      (((k2_xboole_0 @ sk_C_1 @ (k3_subset_1 @ sk_A @ sk_C_1)) = (sk_A))),
% 3.14/3.37      inference('demod', [status(thm)], ['17', '58'])).
% 3.14/3.37  thf(t73_xboole_1, axiom,
% 3.14/3.37    (![A:$i,B:$i,C:$i]:
% 3.14/3.37     ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & ( r1_xboole_0 @ A @ C ) ) =>
% 3.14/3.37       ( r1_tarski @ A @ B ) ))).
% 3.14/3.37  thf('60', plain,
% 3.14/3.37      (![X23 : $i, X24 : $i, X25 : $i]:
% 3.14/3.37         ((r1_tarski @ X23 @ X24)
% 3.14/3.37          | ~ (r1_tarski @ X23 @ (k2_xboole_0 @ X24 @ X25))
% 3.14/3.37          | ~ (r1_xboole_0 @ X23 @ X25))),
% 3.14/3.37      inference('cnf', [status(esa)], [t73_xboole_1])).
% 3.14/3.37  thf('61', plain,
% 3.14/3.37      (![X0 : $i]:
% 3.14/3.37         (~ (r1_tarski @ X0 @ sk_A)
% 3.14/3.37          | ~ (r1_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_C_1))
% 3.14/3.37          | (r1_tarski @ X0 @ sk_C_1))),
% 3.14/3.37      inference('sup-', [status(thm)], ['59', '60'])).
% 3.14/3.37  thf('62', plain,
% 3.14/3.37      ((((r1_tarski @ sk_B @ sk_C_1) | ~ (r1_tarski @ sk_B @ sk_A)))
% 3.14/3.37         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 3.14/3.37               (k3_subset_1 @ sk_A @ sk_B))))),
% 3.14/3.37      inference('sup-', [status(thm)], ['12', '61'])).
% 3.14/3.37  thf('63', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 3.14/3.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.14/3.37  thf('64', plain,
% 3.14/3.37      (![X47 : $i, X48 : $i]:
% 3.14/3.37         (~ (m1_subset_1 @ X47 @ X48)
% 3.14/3.37          | (r2_hidden @ X47 @ X48)
% 3.14/3.37          | (v1_xboole_0 @ X48))),
% 3.14/3.37      inference('cnf', [status(esa)], [d2_subset_1])).
% 3.14/3.37  thf('65', plain,
% 3.14/3.37      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 3.14/3.37        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 3.14/3.37      inference('sup-', [status(thm)], ['63', '64'])).
% 3.14/3.37  thf('66', plain, (![X52 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X52))),
% 3.14/3.37      inference('cnf', [status(esa)], [fc1_subset_1])).
% 3.14/3.37  thf('67', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 3.14/3.37      inference('clc', [status(thm)], ['65', '66'])).
% 3.14/3.37  thf('68', plain,
% 3.14/3.37      (![X41 : $i, X43 : $i]:
% 3.14/3.37         ((r1_tarski @ X43 @ X41) | ~ (r2_hidden @ X43 @ (k1_zfmisc_1 @ X41)))),
% 3.14/3.37      inference('simplify', [status(thm)], ['23'])).
% 3.14/3.37  thf('69', plain, ((r1_tarski @ sk_B @ sk_A)),
% 3.14/3.37      inference('sup-', [status(thm)], ['67', '68'])).
% 3.14/3.37  thf('70', plain,
% 3.14/3.37      (((r1_tarski @ sk_B @ sk_C_1))
% 3.14/3.37         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 3.14/3.37               (k3_subset_1 @ sk_A @ sk_B))))),
% 3.14/3.37      inference('demod', [status(thm)], ['62', '69'])).
% 3.14/3.37  thf('71', plain,
% 3.14/3.37      ((~ (r1_tarski @ sk_B @ sk_C_1)) <= (~ ((r1_tarski @ sk_B @ sk_C_1)))),
% 3.14/3.37      inference('split', [status(esa)], ['0'])).
% 3.14/3.37  thf('72', plain,
% 3.14/3.37      (((r1_tarski @ sk_B @ sk_C_1)) | 
% 3.14/3.37       ~
% 3.14/3.37       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 3.14/3.37         (k3_subset_1 @ sk_A @ sk_B)))),
% 3.14/3.37      inference('sup-', [status(thm)], ['70', '71'])).
% 3.14/3.37  thf('73', plain,
% 3.14/3.37      (~
% 3.14/3.37       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 3.14/3.37         (k3_subset_1 @ sk_A @ sk_B)))),
% 3.14/3.37      inference('sat_resolution*', [status(thm)], ['2', '72'])).
% 3.14/3.37  thf('74', plain,
% 3.14/3.37      (~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 3.14/3.37          (k3_subset_1 @ sk_A @ sk_B))),
% 3.14/3.37      inference('simpl_trail', [status(thm)], ['1', '73'])).
% 3.14/3.37  thf('75', plain,
% 3.14/3.37      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 3.14/3.37      inference('sup-', [status(thm)], ['13', '14'])).
% 3.14/3.37  thf('76', plain,
% 3.14/3.37      (((r1_tarski @ sk_B @ sk_C_1)) <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 3.14/3.37      inference('split', [status(esa)], ['3'])).
% 3.14/3.37  thf(t85_xboole_1, axiom,
% 3.14/3.37    (![A:$i,B:$i,C:$i]:
% 3.14/3.37     ( ( r1_tarski @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ))).
% 3.14/3.37  thf('77', plain,
% 3.14/3.37      (![X28 : $i, X29 : $i, X30 : $i]:
% 3.14/3.37         (~ (r1_tarski @ X28 @ X29)
% 3.14/3.37          | (r1_xboole_0 @ X28 @ (k4_xboole_0 @ X30 @ X29)))),
% 3.14/3.37      inference('cnf', [status(esa)], [t85_xboole_1])).
% 3.14/3.37  thf('78', plain,
% 3.14/3.37      ((![X0 : $i]: (r1_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ sk_C_1)))
% 3.14/3.37         <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 3.14/3.37      inference('sup-', [status(thm)], ['76', '77'])).
% 3.14/3.37  thf('79', plain,
% 3.14/3.37      (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)))
% 3.14/3.37         <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 3.14/3.37      inference('sup+', [status(thm)], ['75', '78'])).
% 3.14/3.37  thf('80', plain,
% 3.14/3.37      (![X3 : $i, X4 : $i]:
% 3.14/3.37         ((r1_xboole_0 @ X3 @ X4) | ~ (r1_xboole_0 @ X4 @ X3))),
% 3.14/3.37      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 3.14/3.37  thf('81', plain,
% 3.14/3.37      (((r1_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C_1) @ sk_B))
% 3.14/3.37         <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 3.14/3.37      inference('sup-', [status(thm)], ['79', '80'])).
% 3.14/3.37  thf('82', plain,
% 3.14/3.37      (((r1_tarski @ sk_B @ sk_C_1)) | 
% 3.14/3.37       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 3.14/3.37         (k3_subset_1 @ sk_A @ sk_B)))),
% 3.14/3.37      inference('split', [status(esa)], ['3'])).
% 3.14/3.37  thf('83', plain, (((r1_tarski @ sk_B @ sk_C_1))),
% 3.14/3.37      inference('sat_resolution*', [status(thm)], ['2', '72', '82'])).
% 3.14/3.37  thf('84', plain, ((r1_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C_1) @ sk_B)),
% 3.14/3.37      inference('simpl_trail', [status(thm)], ['81', '83'])).
% 3.14/3.37  thf('85', plain,
% 3.14/3.37      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 3.14/3.37      inference('sup-', [status(thm)], ['5', '6'])).
% 3.14/3.37  thf('86', plain,
% 3.14/3.37      (![X17 : $i, X18 : $i]:
% 3.14/3.37         ((k2_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X17))
% 3.14/3.37           = (k2_xboole_0 @ X17 @ X18))),
% 3.14/3.37      inference('cnf', [status(esa)], [t39_xboole_1])).
% 3.14/3.37  thf('87', plain,
% 3.14/3.37      (((k2_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 3.14/3.37         = (k2_xboole_0 @ sk_B @ sk_A))),
% 3.14/3.37      inference('sup+', [status(thm)], ['85', '86'])).
% 3.14/3.37  thf('88', plain, ((r1_tarski @ sk_B @ sk_A)),
% 3.14/3.37      inference('sup-', [status(thm)], ['67', '68'])).
% 3.14/3.37  thf('89', plain,
% 3.14/3.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.14/3.37         ((r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 3.14/3.37      inference('sup-', [status(thm)], ['26', '27'])).
% 3.14/3.37  thf('90', plain,
% 3.14/3.37      (![X0 : $i]: (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ sk_A)),
% 3.14/3.37      inference('sup-', [status(thm)], ['88', '89'])).
% 3.14/3.37  thf('91', plain,
% 3.14/3.37      (![X0 : $i, X1 : $i]:
% 3.14/3.37         ((v1_xboole_0 @ (k4_xboole_0 @ X1 @ X0))
% 3.14/3.37          | ~ (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 3.14/3.37      inference('sup-', [status(thm)], ['30', '31'])).
% 3.14/3.37  thf('92', plain, ((v1_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_A))),
% 3.14/3.37      inference('sup-', [status(thm)], ['90', '91'])).
% 3.14/3.37  thf('93', plain,
% 3.14/3.37      (![X2 : $i]: (((X2) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X2))),
% 3.14/3.37      inference('cnf', [status(esa)], [l13_xboole_0])).
% 3.14/3.37  thf('94', plain, (((k4_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0))),
% 3.14/3.37      inference('sup-', [status(thm)], ['92', '93'])).
% 3.14/3.37  thf('95', plain,
% 3.14/3.37      (![X17 : $i, X18 : $i]:
% 3.14/3.37         ((k2_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X17))
% 3.14/3.37           = (k2_xboole_0 @ X17 @ X18))),
% 3.14/3.37      inference('cnf', [status(esa)], [t39_xboole_1])).
% 3.14/3.37  thf('96', plain,
% 3.14/3.37      (((k2_xboole_0 @ sk_A @ k1_xboole_0) = (k2_xboole_0 @ sk_A @ sk_B))),
% 3.14/3.37      inference('sup+', [status(thm)], ['94', '95'])).
% 3.14/3.37  thf('97', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 3.14/3.37      inference('demod', [status(thm)], ['42', '51'])).
% 3.14/3.37  thf('98', plain,
% 3.14/3.37      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 3.14/3.37      inference('sup+', [status(thm)], ['55', '56'])).
% 3.14/3.37  thf('99', plain, (((sk_A) = (k2_xboole_0 @ sk_B @ sk_A))),
% 3.14/3.37      inference('demod', [status(thm)], ['96', '97', '98'])).
% 3.14/3.37  thf('100', plain,
% 3.14/3.37      (((k2_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_A))),
% 3.14/3.37      inference('demod', [status(thm)], ['87', '99'])).
% 3.14/3.37  thf('101', plain,
% 3.14/3.37      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 3.14/3.37      inference('sup+', [status(thm)], ['55', '56'])).
% 3.14/3.37  thf('102', plain,
% 3.14/3.37      (![X23 : $i, X24 : $i, X25 : $i]:
% 3.14/3.37         ((r1_tarski @ X23 @ X24)
% 3.14/3.37          | ~ (r1_tarski @ X23 @ (k2_xboole_0 @ X24 @ X25))
% 3.14/3.37          | ~ (r1_xboole_0 @ X23 @ X25))),
% 3.14/3.37      inference('cnf', [status(esa)], [t73_xboole_1])).
% 3.14/3.37  thf('103', plain,
% 3.14/3.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.14/3.37         (~ (r1_tarski @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 3.14/3.37          | ~ (r1_xboole_0 @ X2 @ X1)
% 3.14/3.37          | (r1_tarski @ X2 @ X0))),
% 3.14/3.37      inference('sup-', [status(thm)], ['101', '102'])).
% 3.14/3.37  thf('104', plain,
% 3.14/3.37      (![X0 : $i]:
% 3.14/3.37         (~ (r1_tarski @ X0 @ sk_A)
% 3.14/3.37          | (r1_tarski @ X0 @ (k3_subset_1 @ sk_A @ sk_B))
% 3.14/3.37          | ~ (r1_xboole_0 @ X0 @ sk_B))),
% 3.14/3.37      inference('sup-', [status(thm)], ['100', '103'])).
% 3.14/3.37  thf('105', plain,
% 3.14/3.37      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 3.14/3.37         (k3_subset_1 @ sk_A @ sk_B))
% 3.14/3.37        | ~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ sk_A))),
% 3.14/3.37      inference('sup-', [status(thm)], ['84', '104'])).
% 3.14/3.37  thf('106', plain,
% 3.14/3.37      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 3.14/3.37      inference('sup-', [status(thm)], ['13', '14'])).
% 3.14/3.37  thf('107', plain,
% 3.14/3.37      (![X15 : $i, X16 : $i]: (r1_tarski @ (k4_xboole_0 @ X15 @ X16) @ X15)),
% 3.14/3.37      inference('cnf', [status(esa)], [t36_xboole_1])).
% 3.14/3.38  thf('108', plain, ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ sk_A)),
% 3.14/3.38      inference('sup+', [status(thm)], ['106', '107'])).
% 3.14/3.38  thf('109', plain,
% 3.14/3.38      ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ (k3_subset_1 @ sk_A @ sk_B))),
% 3.14/3.38      inference('demod', [status(thm)], ['105', '108'])).
% 3.14/3.38  thf('110', plain, ($false), inference('demod', [status(thm)], ['74', '109'])).
% 3.14/3.38  
% 3.14/3.38  % SZS output end Refutation
% 3.14/3.38  
% 3.25/3.38  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
