%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cJCL5tAvom

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:10 EST 2020

% Result     : Theorem 38.25s
% Output     : Refutation 38.25s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 288 expanded)
%              Number of leaves         :   28 (  97 expanded)
%              Depth                    :   21
%              Number of atoms          : 1209 (2579 expanded)
%              Number of equality atoms :   75 ( 133 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    | ~ ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X36: $i,X37: $i] :
      ( ( ( k3_subset_1 @ X36 @ X37 )
        = ( k4_xboole_0 @ X36 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('4',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( r1_tarski @ sk_B @ sk_C_1 )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['5'])).

thf(t34_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k4_xboole_0 @ C @ B ) @ ( k4_xboole_0 @ C @ A ) ) ) )).

thf('7',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X13 @ X14 )
      | ( r1_tarski @ ( k4_xboole_0 @ X15 @ X14 ) @ ( k4_xboole_0 @ X15 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t34_xboole_1])).

thf('8',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k4_xboole_0 @ X0 @ sk_C_1 ) @ ( k4_xboole_0 @ X0 @ sk_B ) )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k4_xboole_0 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['4','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X36: $i,X37: $i] :
      ( ( ( k3_subset_1 @ X36 @ X37 )
        = ( k4_xboole_0 @ X36 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('12',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['9','12'])).

thf('14',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('15',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ~ ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['5'])).

thf('17',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('18',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ X20 @ ( k4_xboole_0 @ X21 @ X20 ) )
      = ( k2_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('19',plain,
    ( ( k2_xboole_0 @ sk_C_1 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
    = ( k2_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
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

thf('21',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X33 @ X34 )
      | ( r2_hidden @ X33 @ X34 )
      | ( v1_xboole_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('22',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('23',plain,(
    ! [X38: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('24',plain,(
    r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['22','23'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('25',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ X31 @ X30 )
      | ( r1_tarski @ X31 @ X29 )
      | ( X30
       != ( k1_zfmisc_1 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('26',plain,(
    ! [X29: $i,X31: $i] :
      ( ( r1_tarski @ X31 @ X29 )
      | ~ ( r2_hidden @ X31 @ ( k1_zfmisc_1 @ X29 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    r1_tarski @ sk_C_1 @ sk_A ),
    inference('sup-',[status(thm)],['24','26'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('28',plain,(
    ! [X4: $i,X6: $i] :
      ( ( ( k4_xboole_0 @ X4 @ X6 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('29',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ X20 @ ( k4_xboole_0 @ X21 @ X20 ) )
      = ( k2_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('31',plain,
    ( ( k2_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('34',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ sk_A )
    = ( k2_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,
    ( ( k2_xboole_0 @ sk_C_1 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
    = ( k2_xboole_0 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['19','34'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('36',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X22 @ X23 ) @ X24 )
      = ( k4_xboole_0 @ X22 @ ( k2_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('37',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ X20 @ ( k4_xboole_0 @ X21 @ X20 ) )
      = ( k2_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ k1_xboole_0 @ sk_A ) ) )
      = ( k2_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k4_xboole_0 @ X0 @ sk_C_1 ) ) ) ),
    inference('sup+',[status(thm)],['35','38'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('40',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X16 @ X17 ) @ X16 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('41',plain,(
    ! [X4: $i,X6: $i] :
      ( ( ( k4_xboole_0 @ X4 @ X6 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X22 @ X23 ) @ X24 )
      = ( k4_xboole_0 @ X22 @ ( k2_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X16 @ X17 ) @ X16 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X4: $i,X6: $i] :
      ( ( ( k4_xboole_0 @ X4 @ X6 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('49',plain,(
    ! [X25: $i,X27: $i] :
      ( ( r1_xboole_0 @ X25 @ X27 )
      | ( ( k4_xboole_0 @ X25 @ X27 )
       != X25 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['50'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('52',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('53',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k4_xboole_0 @ X25 @ X26 )
        = X25 )
      | ~ ( r1_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X22 @ X23 ) @ X24 )
      = ( k4_xboole_0 @ X22 @ ( k2_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ k1_xboole_0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k4_xboole_0 @ X0 @ sk_A ) )
      = ( k2_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k4_xboole_0 @ X0 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['39','57'])).

thf('59',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['5'])).

thf('60',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t106_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('61',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X7 @ X9 )
      | ~ ( r1_tarski @ X7 @ ( k4_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_subset_1 @ sk_A @ sk_B ) )
      | ( r1_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( r1_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ sk_B )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['59','62'])).

thf('64',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('65',plain,
    ( ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k4_xboole_0 @ X25 @ X26 )
        = X25 )
      | ~ ( r1_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('67',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
      = sk_B )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X22 @ X23 ) @ X24 )
      = ( k4_xboole_0 @ X22 @ ( k2_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('69',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ sk_B @ X0 )
        = ( k4_xboole_0 @ sk_B @ ( k2_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ X0 ) ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ sk_A ) )
        = ( k4_xboole_0 @ sk_B @ ( k2_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k4_xboole_0 @ X0 @ sk_C_1 ) ) ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['58','69'])).

thf('71',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('72',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ X20 @ ( k4_xboole_0 @ X21 @ X20 ) )
      = ( k2_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('73',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X33 @ X34 )
      | ( r2_hidden @ X33 @ X34 )
      | ( v1_xboole_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('76',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X38: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('78',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X29: $i,X31: $i] :
      ( ( r1_tarski @ X31 @ X29 )
      | ~ ( r2_hidden @ X31 @ ( k1_zfmisc_1 @ X29 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('80',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['78','79'])).

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
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ X20 @ ( k4_xboole_0 @ X21 @ X20 ) )
      = ( k2_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('84',plain,
    ( ( k2_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('87',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['84','85','86'])).

thf('88',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['73','87'])).

thf('89',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X22 @ X23 ) @ X24 )
      = ( k4_xboole_0 @ X22 @ ( k2_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('90',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X16 @ X17 ) @ X16 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('91',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X7 @ X9 )
      | ~ ( r1_tarski @ X7 @ ( k4_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X2 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ k1_xboole_0 @ sk_A ) ) @ sk_B ) ),
    inference('sup+',[status(thm)],['88','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ k1_xboole_0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('96',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('98',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k4_xboole_0 @ X25 @ X26 )
        = X25 )
      | ~ ( r1_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ sk_A ) )
      = sk_B ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ sk_B @ X0 )
        = ( k4_xboole_0 @ sk_B @ ( k2_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ X0 ) ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('102',plain,
    ( ! [X0: $i] :
        ( sk_B
        = ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ sk_C_1 ) ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['70','100','101'])).

thf('103',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X16 @ X17 ) @ X16 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('104',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( r1_tarski @ X28 @ X29 )
      | ( r2_hidden @ X28 @ X30 )
      | ( X30
       != ( k1_zfmisc_1 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('105',plain,(
    ! [X28: $i,X29: $i] :
      ( ( r2_hidden @ X28 @ ( k1_zfmisc_1 @ X29 ) )
      | ~ ( r1_tarski @ X28 @ X29 ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['103','105'])).

thf('107',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( r2_hidden @ X33 @ X34 )
      | ( m1_subset_1 @ X33 @ X34 )
      | ( v1_xboole_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X38: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X36: $i,X37: $i] :
      ( ( ( k3_subset_1 @ X36 @ X37 )
        = ( k4_xboole_0 @ X36 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) )
      = sk_B )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['102','112'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf(t38_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) )
     => ( A = k1_xboole_0 ) ) )).

thf('115',plain,(
    ! [X18: $i,X19: $i] :
      ( ( X18 = k1_xboole_0 )
      | ~ ( r1_tarski @ X18 @ ( k4_xboole_0 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_subset_1 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,
    ( ( ~ ( r1_tarski @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) @ sk_B )
      | ( ( k4_xboole_0 @ sk_B @ sk_C_1 )
        = k1_xboole_0 ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['113','116'])).

thf('118',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X16 @ X17 ) @ X16 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('119',plain,
    ( ( ( k4_xboole_0 @ sk_B @ sk_C_1 )
      = k1_xboole_0 )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( ( k4_xboole_0 @ X4 @ X5 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('121',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ sk_B @ sk_C_1 ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,
    ( ( r1_tarski @ sk_B @ sk_C_1 )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['121'])).

thf('123',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C_1 )
   <= ~ ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('124',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','15','16','124'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cJCL5tAvom
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:32:16 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 38.25/38.45  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 38.25/38.45  % Solved by: fo/fo7.sh
% 38.25/38.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 38.25/38.45  % done 30780 iterations in 37.979s
% 38.25/38.45  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 38.25/38.45  % SZS output start Refutation
% 38.25/38.45  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 38.25/38.45  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 38.25/38.45  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 38.25/38.45  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 38.25/38.45  thf(sk_C_1_type, type, sk_C_1: $i).
% 38.25/38.45  thf(sk_B_type, type, sk_B: $i).
% 38.25/38.45  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 38.25/38.45  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 38.25/38.45  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 38.25/38.45  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 38.25/38.45  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 38.25/38.45  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 38.25/38.45  thf(sk_A_type, type, sk_A: $i).
% 38.25/38.45  thf(t31_subset_1, conjecture,
% 38.25/38.45    (![A:$i,B:$i]:
% 38.25/38.45     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 38.25/38.45       ( ![C:$i]:
% 38.25/38.45         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 38.25/38.45           ( ( r1_tarski @ B @ C ) <=>
% 38.25/38.45             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 38.25/38.45  thf(zf_stmt_0, negated_conjecture,
% 38.25/38.45    (~( ![A:$i,B:$i]:
% 38.25/38.45        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 38.25/38.45          ( ![C:$i]:
% 38.25/38.45            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 38.25/38.45              ( ( r1_tarski @ B @ C ) <=>
% 38.25/38.45                ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) )),
% 38.25/38.45    inference('cnf.neg', [status(esa)], [t31_subset_1])).
% 38.25/38.45  thf('0', plain,
% 38.25/38.45      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 38.25/38.45           (k3_subset_1 @ sk_A @ sk_B))
% 38.25/38.45        | ~ (r1_tarski @ sk_B @ sk_C_1))),
% 38.25/38.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.25/38.45  thf('1', plain,
% 38.25/38.45      (~
% 38.25/38.45       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 38.25/38.45         (k3_subset_1 @ sk_A @ sk_B))) | 
% 38.25/38.45       ~ ((r1_tarski @ sk_B @ sk_C_1))),
% 38.25/38.45      inference('split', [status(esa)], ['0'])).
% 38.25/38.45  thf('2', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 38.25/38.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.25/38.45  thf(d5_subset_1, axiom,
% 38.25/38.45    (![A:$i,B:$i]:
% 38.25/38.45     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 38.25/38.45       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 38.25/38.45  thf('3', plain,
% 38.25/38.45      (![X36 : $i, X37 : $i]:
% 38.25/38.45         (((k3_subset_1 @ X36 @ X37) = (k4_xboole_0 @ X36 @ X37))
% 38.25/38.45          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X36)))),
% 38.25/38.45      inference('cnf', [status(esa)], [d5_subset_1])).
% 38.25/38.45  thf('4', plain,
% 38.25/38.45      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 38.25/38.45      inference('sup-', [status(thm)], ['2', '3'])).
% 38.25/38.45  thf('5', plain,
% 38.25/38.45      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 38.25/38.45         (k3_subset_1 @ sk_A @ sk_B))
% 38.25/38.45        | (r1_tarski @ sk_B @ sk_C_1))),
% 38.25/38.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.25/38.45  thf('6', plain,
% 38.25/38.45      (((r1_tarski @ sk_B @ sk_C_1)) <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 38.25/38.45      inference('split', [status(esa)], ['5'])).
% 38.25/38.45  thf(t34_xboole_1, axiom,
% 38.25/38.45    (![A:$i,B:$i,C:$i]:
% 38.25/38.45     ( ( r1_tarski @ A @ B ) =>
% 38.25/38.45       ( r1_tarski @ ( k4_xboole_0 @ C @ B ) @ ( k4_xboole_0 @ C @ A ) ) ))).
% 38.25/38.45  thf('7', plain,
% 38.25/38.45      (![X13 : $i, X14 : $i, X15 : $i]:
% 38.25/38.45         (~ (r1_tarski @ X13 @ X14)
% 38.25/38.45          | (r1_tarski @ (k4_xboole_0 @ X15 @ X14) @ (k4_xboole_0 @ X15 @ X13)))),
% 38.25/38.45      inference('cnf', [status(esa)], [t34_xboole_1])).
% 38.25/38.45  thf('8', plain,
% 38.25/38.45      ((![X0 : $i]:
% 38.25/38.45          (r1_tarski @ (k4_xboole_0 @ X0 @ sk_C_1) @ (k4_xboole_0 @ X0 @ sk_B)))
% 38.25/38.45         <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 38.25/38.45      inference('sup-', [status(thm)], ['6', '7'])).
% 38.25/38.45  thf('9', plain,
% 38.25/38.45      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 38.25/38.45         (k4_xboole_0 @ sk_A @ sk_B))) <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 38.25/38.45      inference('sup+', [status(thm)], ['4', '8'])).
% 38.25/38.45  thf('10', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 38.25/38.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.25/38.45  thf('11', plain,
% 38.25/38.45      (![X36 : $i, X37 : $i]:
% 38.25/38.45         (((k3_subset_1 @ X36 @ X37) = (k4_xboole_0 @ X36 @ X37))
% 38.25/38.45          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X36)))),
% 38.25/38.45      inference('cnf', [status(esa)], [d5_subset_1])).
% 38.25/38.45  thf('12', plain,
% 38.25/38.45      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 38.25/38.45      inference('sup-', [status(thm)], ['10', '11'])).
% 38.25/38.45  thf('13', plain,
% 38.25/38.45      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 38.25/38.45         (k3_subset_1 @ sk_A @ sk_B))) <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 38.25/38.45      inference('demod', [status(thm)], ['9', '12'])).
% 38.25/38.45  thf('14', plain,
% 38.25/38.45      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 38.25/38.45           (k3_subset_1 @ sk_A @ sk_B)))
% 38.25/38.45         <= (~
% 38.25/38.45             ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 38.25/38.45               (k3_subset_1 @ sk_A @ sk_B))))),
% 38.25/38.45      inference('split', [status(esa)], ['0'])).
% 38.25/38.45  thf('15', plain,
% 38.25/38.45      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 38.25/38.45         (k3_subset_1 @ sk_A @ sk_B))) | 
% 38.25/38.45       ~ ((r1_tarski @ sk_B @ sk_C_1))),
% 38.25/38.45      inference('sup-', [status(thm)], ['13', '14'])).
% 38.25/38.45  thf('16', plain,
% 38.25/38.45      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 38.25/38.45         (k3_subset_1 @ sk_A @ sk_B))) | 
% 38.25/38.45       ((r1_tarski @ sk_B @ sk_C_1))),
% 38.25/38.45      inference('split', [status(esa)], ['5'])).
% 38.25/38.45  thf('17', plain,
% 38.25/38.45      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 38.25/38.45      inference('sup-', [status(thm)], ['2', '3'])).
% 38.25/38.45  thf(t39_xboole_1, axiom,
% 38.25/38.45    (![A:$i,B:$i]:
% 38.25/38.45     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 38.25/38.45  thf('18', plain,
% 38.25/38.45      (![X20 : $i, X21 : $i]:
% 38.25/38.45         ((k2_xboole_0 @ X20 @ (k4_xboole_0 @ X21 @ X20))
% 38.25/38.45           = (k2_xboole_0 @ X20 @ X21))),
% 38.25/38.45      inference('cnf', [status(esa)], [t39_xboole_1])).
% 38.25/38.45  thf('19', plain,
% 38.25/38.45      (((k2_xboole_0 @ sk_C_1 @ (k3_subset_1 @ sk_A @ sk_C_1))
% 38.25/38.45         = (k2_xboole_0 @ sk_C_1 @ sk_A))),
% 38.25/38.45      inference('sup+', [status(thm)], ['17', '18'])).
% 38.25/38.45  thf('20', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 38.25/38.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.25/38.45  thf(d2_subset_1, axiom,
% 38.25/38.45    (![A:$i,B:$i]:
% 38.25/38.45     ( ( ( v1_xboole_0 @ A ) =>
% 38.25/38.45         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 38.25/38.45       ( ( ~( v1_xboole_0 @ A ) ) =>
% 38.25/38.45         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 38.25/38.45  thf('21', plain,
% 38.25/38.45      (![X33 : $i, X34 : $i]:
% 38.25/38.45         (~ (m1_subset_1 @ X33 @ X34)
% 38.25/38.45          | (r2_hidden @ X33 @ X34)
% 38.25/38.45          | (v1_xboole_0 @ X34))),
% 38.25/38.45      inference('cnf', [status(esa)], [d2_subset_1])).
% 38.25/38.45  thf('22', plain,
% 38.25/38.45      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 38.25/38.45        | (r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A)))),
% 38.25/38.45      inference('sup-', [status(thm)], ['20', '21'])).
% 38.25/38.45  thf(fc1_subset_1, axiom,
% 38.25/38.45    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 38.25/38.45  thf('23', plain, (![X38 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X38))),
% 38.25/38.45      inference('cnf', [status(esa)], [fc1_subset_1])).
% 38.25/38.45  thf('24', plain, ((r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 38.25/38.45      inference('clc', [status(thm)], ['22', '23'])).
% 38.25/38.45  thf(d1_zfmisc_1, axiom,
% 38.25/38.45    (![A:$i,B:$i]:
% 38.25/38.45     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 38.25/38.45       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 38.25/38.45  thf('25', plain,
% 38.25/38.45      (![X29 : $i, X30 : $i, X31 : $i]:
% 38.25/38.45         (~ (r2_hidden @ X31 @ X30)
% 38.25/38.45          | (r1_tarski @ X31 @ X29)
% 38.25/38.45          | ((X30) != (k1_zfmisc_1 @ X29)))),
% 38.25/38.45      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 38.25/38.45  thf('26', plain,
% 38.25/38.45      (![X29 : $i, X31 : $i]:
% 38.25/38.45         ((r1_tarski @ X31 @ X29) | ~ (r2_hidden @ X31 @ (k1_zfmisc_1 @ X29)))),
% 38.25/38.45      inference('simplify', [status(thm)], ['25'])).
% 38.25/38.45  thf('27', plain, ((r1_tarski @ sk_C_1 @ sk_A)),
% 38.25/38.45      inference('sup-', [status(thm)], ['24', '26'])).
% 38.25/38.45  thf(l32_xboole_1, axiom,
% 38.25/38.45    (![A:$i,B:$i]:
% 38.25/38.45     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 38.25/38.45  thf('28', plain,
% 38.25/38.45      (![X4 : $i, X6 : $i]:
% 38.25/38.45         (((k4_xboole_0 @ X4 @ X6) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ X6))),
% 38.25/38.45      inference('cnf', [status(esa)], [l32_xboole_1])).
% 38.25/38.45  thf('29', plain, (((k4_xboole_0 @ sk_C_1 @ sk_A) = (k1_xboole_0))),
% 38.25/38.45      inference('sup-', [status(thm)], ['27', '28'])).
% 38.25/38.45  thf('30', plain,
% 38.25/38.45      (![X20 : $i, X21 : $i]:
% 38.25/38.45         ((k2_xboole_0 @ X20 @ (k4_xboole_0 @ X21 @ X20))
% 38.25/38.45           = (k2_xboole_0 @ X20 @ X21))),
% 38.25/38.45      inference('cnf', [status(esa)], [t39_xboole_1])).
% 38.25/38.45  thf('31', plain,
% 38.25/38.45      (((k2_xboole_0 @ sk_A @ k1_xboole_0) = (k2_xboole_0 @ sk_A @ sk_C_1))),
% 38.25/38.45      inference('sup+', [status(thm)], ['29', '30'])).
% 38.25/38.45  thf(commutativity_k2_xboole_0, axiom,
% 38.25/38.45    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 38.25/38.45  thf('32', plain,
% 38.25/38.45      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 38.25/38.45      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 38.25/38.45  thf('33', plain,
% 38.25/38.45      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 38.25/38.45      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 38.25/38.45  thf('34', plain,
% 38.25/38.45      (((k2_xboole_0 @ k1_xboole_0 @ sk_A) = (k2_xboole_0 @ sk_C_1 @ sk_A))),
% 38.25/38.45      inference('demod', [status(thm)], ['31', '32', '33'])).
% 38.25/38.45  thf('35', plain,
% 38.25/38.45      (((k2_xboole_0 @ sk_C_1 @ (k3_subset_1 @ sk_A @ sk_C_1))
% 38.25/38.45         = (k2_xboole_0 @ k1_xboole_0 @ sk_A))),
% 38.25/38.45      inference('demod', [status(thm)], ['19', '34'])).
% 38.25/38.45  thf(t41_xboole_1, axiom,
% 38.25/38.45    (![A:$i,B:$i,C:$i]:
% 38.25/38.45     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 38.25/38.45       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 38.25/38.45  thf('36', plain,
% 38.25/38.45      (![X22 : $i, X23 : $i, X24 : $i]:
% 38.25/38.45         ((k4_xboole_0 @ (k4_xboole_0 @ X22 @ X23) @ X24)
% 38.25/38.45           = (k4_xboole_0 @ X22 @ (k2_xboole_0 @ X23 @ X24)))),
% 38.25/38.45      inference('cnf', [status(esa)], [t41_xboole_1])).
% 38.25/38.45  thf('37', plain,
% 38.25/38.45      (![X20 : $i, X21 : $i]:
% 38.25/38.45         ((k2_xboole_0 @ X20 @ (k4_xboole_0 @ X21 @ X20))
% 38.25/38.45           = (k2_xboole_0 @ X20 @ X21))),
% 38.25/38.45      inference('cnf', [status(esa)], [t39_xboole_1])).
% 38.25/38.45  thf('38', plain,
% 38.25/38.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 38.25/38.45         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 38.25/38.45           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1)))),
% 38.25/38.45      inference('sup+', [status(thm)], ['36', '37'])).
% 38.25/38.45  thf('39', plain,
% 38.25/38.45      (![X0 : $i]:
% 38.25/38.45         ((k2_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 38.25/38.45           (k4_xboole_0 @ X0 @ (k2_xboole_0 @ k1_xboole_0 @ sk_A)))
% 38.25/38.45           = (k2_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 38.25/38.45              (k4_xboole_0 @ X0 @ sk_C_1)))),
% 38.25/38.45      inference('sup+', [status(thm)], ['35', '38'])).
% 38.25/38.45  thf(t36_xboole_1, axiom,
% 38.25/38.45    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 38.25/38.45  thf('40', plain,
% 38.25/38.45      (![X16 : $i, X17 : $i]: (r1_tarski @ (k4_xboole_0 @ X16 @ X17) @ X16)),
% 38.25/38.45      inference('cnf', [status(esa)], [t36_xboole_1])).
% 38.25/38.45  thf('41', plain,
% 38.25/38.45      (![X4 : $i, X6 : $i]:
% 38.25/38.45         (((k4_xboole_0 @ X4 @ X6) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ X6))),
% 38.25/38.45      inference('cnf', [status(esa)], [l32_xboole_1])).
% 38.25/38.45  thf('42', plain,
% 38.25/38.45      (![X0 : $i, X1 : $i]:
% 38.25/38.45         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 38.25/38.45      inference('sup-', [status(thm)], ['40', '41'])).
% 38.25/38.45  thf('43', plain,
% 38.25/38.45      (![X22 : $i, X23 : $i, X24 : $i]:
% 38.25/38.45         ((k4_xboole_0 @ (k4_xboole_0 @ X22 @ X23) @ X24)
% 38.25/38.45           = (k4_xboole_0 @ X22 @ (k2_xboole_0 @ X23 @ X24)))),
% 38.25/38.45      inference('cnf', [status(esa)], [t41_xboole_1])).
% 38.25/38.45  thf('44', plain,
% 38.25/38.45      (![X0 : $i, X1 : $i]:
% 38.25/38.45         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 38.25/38.45      inference('demod', [status(thm)], ['42', '43'])).
% 38.25/38.45  thf('45', plain,
% 38.25/38.45      (![X16 : $i, X17 : $i]: (r1_tarski @ (k4_xboole_0 @ X16 @ X17) @ X16)),
% 38.25/38.45      inference('cnf', [status(esa)], [t36_xboole_1])).
% 38.25/38.45  thf('46', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 38.25/38.45      inference('sup+', [status(thm)], ['44', '45'])).
% 38.25/38.45  thf('47', plain,
% 38.25/38.45      (![X4 : $i, X6 : $i]:
% 38.25/38.45         (((k4_xboole_0 @ X4 @ X6) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ X6))),
% 38.25/38.45      inference('cnf', [status(esa)], [l32_xboole_1])).
% 38.25/38.45  thf('48', plain,
% 38.25/38.45      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 38.25/38.45      inference('sup-', [status(thm)], ['46', '47'])).
% 38.25/38.45  thf(t83_xboole_1, axiom,
% 38.25/38.45    (![A:$i,B:$i]:
% 38.25/38.45     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 38.25/38.45  thf('49', plain,
% 38.25/38.45      (![X25 : $i, X27 : $i]:
% 38.25/38.45         ((r1_xboole_0 @ X25 @ X27) | ((k4_xboole_0 @ X25 @ X27) != (X25)))),
% 38.25/38.45      inference('cnf', [status(esa)], [t83_xboole_1])).
% 38.25/38.45  thf('50', plain,
% 38.25/38.45      (![X0 : $i]:
% 38.25/38.45         (((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 38.25/38.45      inference('sup-', [status(thm)], ['48', '49'])).
% 38.25/38.45  thf('51', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 38.25/38.45      inference('simplify', [status(thm)], ['50'])).
% 38.25/38.45  thf(symmetry_r1_xboole_0, axiom,
% 38.25/38.45    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 38.25/38.45  thf('52', plain,
% 38.25/38.45      (![X2 : $i, X3 : $i]:
% 38.25/38.45         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 38.25/38.45      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 38.25/38.45  thf('53', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 38.25/38.45      inference('sup-', [status(thm)], ['51', '52'])).
% 38.25/38.45  thf('54', plain,
% 38.25/38.45      (![X25 : $i, X26 : $i]:
% 38.25/38.45         (((k4_xboole_0 @ X25 @ X26) = (X25)) | ~ (r1_xboole_0 @ X25 @ X26))),
% 38.25/38.45      inference('cnf', [status(esa)], [t83_xboole_1])).
% 38.25/38.45  thf('55', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 38.25/38.45      inference('sup-', [status(thm)], ['53', '54'])).
% 38.25/38.45  thf('56', plain,
% 38.25/38.45      (![X22 : $i, X23 : $i, X24 : $i]:
% 38.25/38.45         ((k4_xboole_0 @ (k4_xboole_0 @ X22 @ X23) @ X24)
% 38.25/38.45           = (k4_xboole_0 @ X22 @ (k2_xboole_0 @ X23 @ X24)))),
% 38.25/38.45      inference('cnf', [status(esa)], [t41_xboole_1])).
% 38.25/38.45  thf('57', plain,
% 38.25/38.45      (![X0 : $i, X1 : $i]:
% 38.25/38.45         ((k4_xboole_0 @ X0 @ X1)
% 38.25/38.45           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ k1_xboole_0 @ X1)))),
% 38.25/38.45      inference('sup+', [status(thm)], ['55', '56'])).
% 38.25/38.45  thf('58', plain,
% 38.25/38.45      (![X0 : $i]:
% 38.25/38.45         ((k2_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 38.25/38.45           (k4_xboole_0 @ X0 @ sk_A))
% 38.25/38.45           = (k2_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 38.25/38.45              (k4_xboole_0 @ X0 @ sk_C_1)))),
% 38.25/38.45      inference('demod', [status(thm)], ['39', '57'])).
% 38.25/38.45  thf('59', plain,
% 38.25/38.45      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 38.25/38.45         (k3_subset_1 @ sk_A @ sk_B)))
% 38.25/38.45         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 38.25/38.45               (k3_subset_1 @ sk_A @ sk_B))))),
% 38.25/38.45      inference('split', [status(esa)], ['5'])).
% 38.25/38.45  thf('60', plain,
% 38.25/38.45      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 38.25/38.45      inference('sup-', [status(thm)], ['10', '11'])).
% 38.25/38.45  thf(t106_xboole_1, axiom,
% 38.25/38.45    (![A:$i,B:$i,C:$i]:
% 38.25/38.45     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 38.25/38.45       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 38.25/38.45  thf('61', plain,
% 38.25/38.45      (![X7 : $i, X8 : $i, X9 : $i]:
% 38.25/38.45         ((r1_xboole_0 @ X7 @ X9)
% 38.25/38.45          | ~ (r1_tarski @ X7 @ (k4_xboole_0 @ X8 @ X9)))),
% 38.25/38.45      inference('cnf', [status(esa)], [t106_xboole_1])).
% 38.25/38.45  thf('62', plain,
% 38.25/38.45      (![X0 : $i]:
% 38.25/38.45         (~ (r1_tarski @ X0 @ (k3_subset_1 @ sk_A @ sk_B))
% 38.25/38.45          | (r1_xboole_0 @ X0 @ sk_B))),
% 38.25/38.45      inference('sup-', [status(thm)], ['60', '61'])).
% 38.25/38.45  thf('63', plain,
% 38.25/38.45      (((r1_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C_1) @ sk_B))
% 38.25/38.45         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 38.25/38.45               (k3_subset_1 @ sk_A @ sk_B))))),
% 38.25/38.45      inference('sup-', [status(thm)], ['59', '62'])).
% 38.25/38.45  thf('64', plain,
% 38.25/38.45      (![X2 : $i, X3 : $i]:
% 38.25/38.45         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 38.25/38.45      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 38.25/38.45  thf('65', plain,
% 38.25/38.45      (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)))
% 38.25/38.45         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 38.25/38.45               (k3_subset_1 @ sk_A @ sk_B))))),
% 38.25/38.45      inference('sup-', [status(thm)], ['63', '64'])).
% 38.25/38.45  thf('66', plain,
% 38.25/38.45      (![X25 : $i, X26 : $i]:
% 38.25/38.45         (((k4_xboole_0 @ X25 @ X26) = (X25)) | ~ (r1_xboole_0 @ X25 @ X26))),
% 38.25/38.45      inference('cnf', [status(esa)], [t83_xboole_1])).
% 38.25/38.45  thf('67', plain,
% 38.25/38.45      ((((k4_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)) = (sk_B)))
% 38.25/38.45         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 38.25/38.45               (k3_subset_1 @ sk_A @ sk_B))))),
% 38.25/38.45      inference('sup-', [status(thm)], ['65', '66'])).
% 38.25/38.45  thf('68', plain,
% 38.25/38.45      (![X22 : $i, X23 : $i, X24 : $i]:
% 38.25/38.45         ((k4_xboole_0 @ (k4_xboole_0 @ X22 @ X23) @ X24)
% 38.25/38.45           = (k4_xboole_0 @ X22 @ (k2_xboole_0 @ X23 @ X24)))),
% 38.25/38.45      inference('cnf', [status(esa)], [t41_xboole_1])).
% 38.25/38.45  thf('69', plain,
% 38.25/38.45      ((![X0 : $i]:
% 38.25/38.45          ((k4_xboole_0 @ sk_B @ X0)
% 38.25/38.45            = (k4_xboole_0 @ sk_B @ 
% 38.25/38.45               (k2_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C_1) @ X0))))
% 38.25/38.45         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 38.25/38.45               (k3_subset_1 @ sk_A @ sk_B))))),
% 38.25/38.45      inference('sup+', [status(thm)], ['67', '68'])).
% 38.25/38.45  thf('70', plain,
% 38.25/38.45      ((![X0 : $i]:
% 38.25/38.45          ((k4_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ sk_A))
% 38.25/38.45            = (k4_xboole_0 @ sk_B @ 
% 38.25/38.45               (k2_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 38.25/38.45                (k4_xboole_0 @ X0 @ sk_C_1)))))
% 38.25/38.45         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 38.25/38.45               (k3_subset_1 @ sk_A @ sk_B))))),
% 38.25/38.45      inference('sup+', [status(thm)], ['58', '69'])).
% 38.25/38.45  thf('71', plain,
% 38.25/38.45      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 38.25/38.45      inference('sup-', [status(thm)], ['10', '11'])).
% 38.25/38.45  thf('72', plain,
% 38.25/38.45      (![X20 : $i, X21 : $i]:
% 38.25/38.45         ((k2_xboole_0 @ X20 @ (k4_xboole_0 @ X21 @ X20))
% 38.25/38.45           = (k2_xboole_0 @ X20 @ X21))),
% 38.25/38.45      inference('cnf', [status(esa)], [t39_xboole_1])).
% 38.25/38.45  thf('73', plain,
% 38.25/38.45      (((k2_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 38.25/38.45         = (k2_xboole_0 @ sk_B @ sk_A))),
% 38.25/38.45      inference('sup+', [status(thm)], ['71', '72'])).
% 38.25/38.45  thf('74', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 38.25/38.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.25/38.45  thf('75', plain,
% 38.25/38.45      (![X33 : $i, X34 : $i]:
% 38.25/38.45         (~ (m1_subset_1 @ X33 @ X34)
% 38.25/38.45          | (r2_hidden @ X33 @ X34)
% 38.25/38.45          | (v1_xboole_0 @ X34))),
% 38.25/38.45      inference('cnf', [status(esa)], [d2_subset_1])).
% 38.25/38.45  thf('76', plain,
% 38.25/38.45      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 38.25/38.45        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 38.25/38.45      inference('sup-', [status(thm)], ['74', '75'])).
% 38.25/38.45  thf('77', plain, (![X38 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X38))),
% 38.25/38.45      inference('cnf', [status(esa)], [fc1_subset_1])).
% 38.25/38.45  thf('78', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 38.25/38.45      inference('clc', [status(thm)], ['76', '77'])).
% 38.25/38.45  thf('79', plain,
% 38.25/38.45      (![X29 : $i, X31 : $i]:
% 38.25/38.45         ((r1_tarski @ X31 @ X29) | ~ (r2_hidden @ X31 @ (k1_zfmisc_1 @ X29)))),
% 38.25/38.45      inference('simplify', [status(thm)], ['25'])).
% 38.25/38.45  thf('80', plain, ((r1_tarski @ sk_B @ sk_A)),
% 38.25/38.45      inference('sup-', [status(thm)], ['78', '79'])).
% 38.25/38.45  thf('81', plain,
% 38.25/38.45      (![X4 : $i, X6 : $i]:
% 38.25/38.45         (((k4_xboole_0 @ X4 @ X6) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ X6))),
% 38.25/38.45      inference('cnf', [status(esa)], [l32_xboole_1])).
% 38.25/38.45  thf('82', plain, (((k4_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0))),
% 38.25/38.45      inference('sup-', [status(thm)], ['80', '81'])).
% 38.25/38.45  thf('83', plain,
% 38.25/38.45      (![X20 : $i, X21 : $i]:
% 38.25/38.45         ((k2_xboole_0 @ X20 @ (k4_xboole_0 @ X21 @ X20))
% 38.25/38.45           = (k2_xboole_0 @ X20 @ X21))),
% 38.25/38.45      inference('cnf', [status(esa)], [t39_xboole_1])).
% 38.25/38.45  thf('84', plain,
% 38.25/38.45      (((k2_xboole_0 @ sk_A @ k1_xboole_0) = (k2_xboole_0 @ sk_A @ sk_B))),
% 38.25/38.45      inference('sup+', [status(thm)], ['82', '83'])).
% 38.25/38.45  thf('85', plain,
% 38.25/38.45      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 38.25/38.45      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 38.25/38.45  thf('86', plain,
% 38.25/38.45      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 38.25/38.45      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 38.25/38.45  thf('87', plain,
% 38.25/38.45      (((k2_xboole_0 @ k1_xboole_0 @ sk_A) = (k2_xboole_0 @ sk_B @ sk_A))),
% 38.25/38.45      inference('demod', [status(thm)], ['84', '85', '86'])).
% 38.25/38.45  thf('88', plain,
% 38.25/38.45      (((k2_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 38.25/38.45         = (k2_xboole_0 @ k1_xboole_0 @ sk_A))),
% 38.25/38.45      inference('demod', [status(thm)], ['73', '87'])).
% 38.25/38.45  thf('89', plain,
% 38.25/38.45      (![X22 : $i, X23 : $i, X24 : $i]:
% 38.25/38.45         ((k4_xboole_0 @ (k4_xboole_0 @ X22 @ X23) @ X24)
% 38.25/38.45           = (k4_xboole_0 @ X22 @ (k2_xboole_0 @ X23 @ X24)))),
% 38.25/38.45      inference('cnf', [status(esa)], [t41_xboole_1])).
% 38.25/38.45  thf('90', plain,
% 38.25/38.45      (![X16 : $i, X17 : $i]: (r1_tarski @ (k4_xboole_0 @ X16 @ X17) @ X16)),
% 38.25/38.45      inference('cnf', [status(esa)], [t36_xboole_1])).
% 38.25/38.45  thf('91', plain,
% 38.25/38.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 38.25/38.45         (r1_tarski @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ 
% 38.25/38.45          (k4_xboole_0 @ X2 @ X1))),
% 38.25/38.45      inference('sup+', [status(thm)], ['89', '90'])).
% 38.25/38.45  thf('92', plain,
% 38.25/38.45      (![X7 : $i, X8 : $i, X9 : $i]:
% 38.25/38.45         ((r1_xboole_0 @ X7 @ X9)
% 38.25/38.45          | ~ (r1_tarski @ X7 @ (k4_xboole_0 @ X8 @ X9)))),
% 38.25/38.45      inference('cnf', [status(esa)], [t106_xboole_1])).
% 38.25/38.45  thf('93', plain,
% 38.25/38.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 38.25/38.45         (r1_xboole_0 @ (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X2)) @ X0)),
% 38.25/38.45      inference('sup-', [status(thm)], ['91', '92'])).
% 38.25/38.45  thf('94', plain,
% 38.25/38.45      (![X0 : $i]:
% 38.25/38.45         (r1_xboole_0 @ 
% 38.25/38.45          (k4_xboole_0 @ X0 @ (k2_xboole_0 @ k1_xboole_0 @ sk_A)) @ sk_B)),
% 38.25/38.45      inference('sup+', [status(thm)], ['88', '93'])).
% 38.25/38.45  thf('95', plain,
% 38.25/38.45      (![X0 : $i, X1 : $i]:
% 38.25/38.45         ((k4_xboole_0 @ X0 @ X1)
% 38.25/38.45           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ k1_xboole_0 @ X1)))),
% 38.25/38.45      inference('sup+', [status(thm)], ['55', '56'])).
% 38.25/38.45  thf('96', plain,
% 38.25/38.45      (![X0 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X0 @ sk_A) @ sk_B)),
% 38.25/38.45      inference('demod', [status(thm)], ['94', '95'])).
% 38.25/38.45  thf('97', plain,
% 38.25/38.45      (![X2 : $i, X3 : $i]:
% 38.25/38.45         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 38.25/38.45      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 38.25/38.45  thf('98', plain,
% 38.25/38.45      (![X0 : $i]: (r1_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ sk_A))),
% 38.25/38.45      inference('sup-', [status(thm)], ['96', '97'])).
% 38.25/38.45  thf('99', plain,
% 38.25/38.45      (![X25 : $i, X26 : $i]:
% 38.25/38.45         (((k4_xboole_0 @ X25 @ X26) = (X25)) | ~ (r1_xboole_0 @ X25 @ X26))),
% 38.25/38.45      inference('cnf', [status(esa)], [t83_xboole_1])).
% 38.25/38.45  thf('100', plain,
% 38.25/38.45      (![X0 : $i]: ((k4_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ sk_A)) = (sk_B))),
% 38.25/38.45      inference('sup-', [status(thm)], ['98', '99'])).
% 38.25/38.45  thf('101', plain,
% 38.25/38.45      ((![X0 : $i]:
% 38.25/38.45          ((k4_xboole_0 @ sk_B @ X0)
% 38.25/38.45            = (k4_xboole_0 @ sk_B @ 
% 38.25/38.45               (k2_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C_1) @ X0))))
% 38.25/38.45         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 38.25/38.45               (k3_subset_1 @ sk_A @ sk_B))))),
% 38.25/38.45      inference('sup+', [status(thm)], ['67', '68'])).
% 38.25/38.45  thf('102', plain,
% 38.25/38.45      ((![X0 : $i]:
% 38.25/38.45          ((sk_B) = (k4_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ sk_C_1))))
% 38.25/38.45         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 38.25/38.45               (k3_subset_1 @ sk_A @ sk_B))))),
% 38.25/38.45      inference('demod', [status(thm)], ['70', '100', '101'])).
% 38.25/38.45  thf('103', plain,
% 38.25/38.45      (![X16 : $i, X17 : $i]: (r1_tarski @ (k4_xboole_0 @ X16 @ X17) @ X16)),
% 38.25/38.45      inference('cnf', [status(esa)], [t36_xboole_1])).
% 38.25/38.45  thf('104', plain,
% 38.25/38.45      (![X28 : $i, X29 : $i, X30 : $i]:
% 38.25/38.45         (~ (r1_tarski @ X28 @ X29)
% 38.25/38.45          | (r2_hidden @ X28 @ X30)
% 38.25/38.45          | ((X30) != (k1_zfmisc_1 @ X29)))),
% 38.25/38.45      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 38.25/38.45  thf('105', plain,
% 38.25/38.45      (![X28 : $i, X29 : $i]:
% 38.25/38.45         ((r2_hidden @ X28 @ (k1_zfmisc_1 @ X29)) | ~ (r1_tarski @ X28 @ X29))),
% 38.25/38.45      inference('simplify', [status(thm)], ['104'])).
% 38.25/38.45  thf('106', plain,
% 38.25/38.45      (![X0 : $i, X1 : $i]:
% 38.25/38.45         (r2_hidden @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 38.25/38.45      inference('sup-', [status(thm)], ['103', '105'])).
% 38.25/38.45  thf('107', plain,
% 38.25/38.45      (![X33 : $i, X34 : $i]:
% 38.25/38.45         (~ (r2_hidden @ X33 @ X34)
% 38.25/38.45          | (m1_subset_1 @ X33 @ X34)
% 38.25/38.45          | (v1_xboole_0 @ X34))),
% 38.25/38.45      inference('cnf', [status(esa)], [d2_subset_1])).
% 38.25/38.45  thf('108', plain,
% 38.25/38.45      (![X0 : $i, X1 : $i]:
% 38.25/38.45         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 38.25/38.45          | (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0)))),
% 38.25/38.45      inference('sup-', [status(thm)], ['106', '107'])).
% 38.25/38.45  thf('109', plain, (![X38 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X38))),
% 38.25/38.45      inference('cnf', [status(esa)], [fc1_subset_1])).
% 38.25/38.45  thf('110', plain,
% 38.25/38.45      (![X0 : $i, X1 : $i]:
% 38.25/38.45         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 38.25/38.45      inference('clc', [status(thm)], ['108', '109'])).
% 38.25/38.45  thf('111', plain,
% 38.25/38.45      (![X36 : $i, X37 : $i]:
% 38.25/38.45         (((k3_subset_1 @ X36 @ X37) = (k4_xboole_0 @ X36 @ X37))
% 38.25/38.45          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X36)))),
% 38.25/38.45      inference('cnf', [status(esa)], [d5_subset_1])).
% 38.25/38.45  thf('112', plain,
% 38.25/38.45      (![X0 : $i, X1 : $i]:
% 38.25/38.45         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 38.25/38.45           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 38.25/38.45      inference('sup-', [status(thm)], ['110', '111'])).
% 38.25/38.45  thf('113', plain,
% 38.25/38.45      ((((k3_subset_1 @ sk_B @ (k4_xboole_0 @ sk_B @ sk_C_1)) = (sk_B)))
% 38.25/38.45         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 38.25/38.45               (k3_subset_1 @ sk_A @ sk_B))))),
% 38.25/38.45      inference('sup+', [status(thm)], ['102', '112'])).
% 38.25/38.45  thf('114', plain,
% 38.25/38.45      (![X0 : $i, X1 : $i]:
% 38.25/38.45         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 38.25/38.45           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 38.25/38.45      inference('sup-', [status(thm)], ['110', '111'])).
% 38.25/38.45  thf(t38_xboole_1, axiom,
% 38.25/38.45    (![A:$i,B:$i]:
% 38.25/38.45     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) ) =>
% 38.25/38.45       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 38.25/38.45  thf('115', plain,
% 38.25/38.45      (![X18 : $i, X19 : $i]:
% 38.25/38.45         (((X18) = (k1_xboole_0))
% 38.25/38.45          | ~ (r1_tarski @ X18 @ (k4_xboole_0 @ X19 @ X18)))),
% 38.25/38.45      inference('cnf', [status(esa)], [t38_xboole_1])).
% 38.25/38.45  thf('116', plain,
% 38.25/38.45      (![X0 : $i, X1 : $i]:
% 38.25/38.45         (~ (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ 
% 38.25/38.45             (k3_subset_1 @ X1 @ (k4_xboole_0 @ X1 @ X0)))
% 38.25/38.45          | ((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0)))),
% 38.25/38.45      inference('sup-', [status(thm)], ['114', '115'])).
% 38.25/38.45  thf('117', plain,
% 38.25/38.45      (((~ (r1_tarski @ (k4_xboole_0 @ sk_B @ sk_C_1) @ sk_B)
% 38.25/38.45         | ((k4_xboole_0 @ sk_B @ sk_C_1) = (k1_xboole_0))))
% 38.25/38.45         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 38.25/38.45               (k3_subset_1 @ sk_A @ sk_B))))),
% 38.25/38.45      inference('sup-', [status(thm)], ['113', '116'])).
% 38.25/38.45  thf('118', plain,
% 38.25/38.45      (![X16 : $i, X17 : $i]: (r1_tarski @ (k4_xboole_0 @ X16 @ X17) @ X16)),
% 38.25/38.45      inference('cnf', [status(esa)], [t36_xboole_1])).
% 38.25/38.45  thf('119', plain,
% 38.25/38.45      ((((k4_xboole_0 @ sk_B @ sk_C_1) = (k1_xboole_0)))
% 38.25/38.45         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 38.25/38.45               (k3_subset_1 @ sk_A @ sk_B))))),
% 38.25/38.45      inference('demod', [status(thm)], ['117', '118'])).
% 38.25/38.45  thf('120', plain,
% 38.25/38.45      (![X4 : $i, X5 : $i]:
% 38.25/38.45         ((r1_tarski @ X4 @ X5) | ((k4_xboole_0 @ X4 @ X5) != (k1_xboole_0)))),
% 38.25/38.45      inference('cnf', [status(esa)], [l32_xboole_1])).
% 38.25/38.45  thf('121', plain,
% 38.25/38.45      (((((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ sk_B @ sk_C_1)))
% 38.25/38.45         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 38.25/38.45               (k3_subset_1 @ sk_A @ sk_B))))),
% 38.25/38.45      inference('sup-', [status(thm)], ['119', '120'])).
% 38.25/38.45  thf('122', plain,
% 38.25/38.45      (((r1_tarski @ sk_B @ sk_C_1))
% 38.25/38.45         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 38.25/38.45               (k3_subset_1 @ sk_A @ sk_B))))),
% 38.25/38.45      inference('simplify', [status(thm)], ['121'])).
% 38.25/38.45  thf('123', plain,
% 38.25/38.45      ((~ (r1_tarski @ sk_B @ sk_C_1)) <= (~ ((r1_tarski @ sk_B @ sk_C_1)))),
% 38.25/38.45      inference('split', [status(esa)], ['0'])).
% 38.25/38.45  thf('124', plain,
% 38.25/38.45      (~
% 38.25/38.45       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 38.25/38.45         (k3_subset_1 @ sk_A @ sk_B))) | 
% 38.25/38.45       ((r1_tarski @ sk_B @ sk_C_1))),
% 38.25/38.45      inference('sup-', [status(thm)], ['122', '123'])).
% 38.25/38.45  thf('125', plain, ($false),
% 38.25/38.45      inference('sat_resolution*', [status(thm)], ['1', '15', '16', '124'])).
% 38.25/38.45  
% 38.25/38.45  % SZS output end Refutation
% 38.25/38.45  
% 38.25/38.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
