%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1UJLVpLxPZ

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:40 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 183 expanded)
%              Number of leaves         :   30 (  69 expanded)
%              Depth                    :   17
%              Number of atoms          :  476 (1286 expanded)
%              Number of equality atoms :   32 ( 101 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(t40_subset_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( ( r1_tarski @ B @ C )
          & ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) )
       => ( B = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
       => ( ( ( r1_tarski @ B @ C )
            & ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) )
         => ( B = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t40_subset_1])).

thf('0',plain,(
    r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t35_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) )
           => ( r1_tarski @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf('2',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X29 ) )
      | ( r1_tarski @ X28 @ ( k3_subset_1 @ X29 @ X30 ) )
      | ~ ( r1_tarski @ X30 @ ( k3_subset_1 @ X29 @ X28 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t35_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r1_tarski @ X0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
      | ( r1_tarski @ sk_C_1 @ ( k3_subset_1 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,(
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

thf('6',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ X23 )
      | ( r2_hidden @ X22 @ X23 )
      | ( v1_xboole_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('7',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('8',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X20 @ X19 )
      | ( r1_tarski @ X20 @ X18 )
      | ( X19
       != ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('9',plain,(
    ! [X18: $i,X20: $i] :
      ( ( r1_tarski @ X20 @ X18 )
      | ~ ( r2_hidden @ X20 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r1_tarski @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    r1_tarski @ sk_B_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('12',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_xboole_0 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('13',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_C_1 )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('14',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('15',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ sk_C_1 )
    = ( k5_xboole_0 @ sk_B_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('16',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ X16 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('17',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ sk_C_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['15','16'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('18',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) )
      = ( k2_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('19',plain,
    ( ( k2_xboole_0 @ sk_C_1 @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_C_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('22',plain,(
    ! [X10: $i] :
      ( ( k2_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('25',plain,
    ( sk_C_1
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['19','20','23','24'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('26',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X7 @ X9 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_C_1 @ X0 )
      | ( r1_tarski @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r1_tarski @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['10','27'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('29',plain,(
    ! [X13: $i] :
      ( r1_tarski @ k1_xboole_0 @ X13 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('30',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ X17 @ X18 )
      | ( r2_hidden @ X17 @ X19 )
      | ( X19
       != ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('31',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r2_hidden @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ~ ( r1_tarski @ X17 @ X18 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( r2_hidden @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','31'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('33',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('34',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    r1_tarski @ sk_B_1 @ sk_A ),
    inference('sup-',[status(thm)],['28','34'])).

thf('36',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r2_hidden @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ~ ( r1_tarski @ X17 @ X18 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('37',plain,(
    r2_hidden @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X22 @ X23 )
      | ( m1_subset_1 @ X22 @ X23 )
      | ( v1_xboole_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('39',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('40',plain,(
    ! [X22: $i,X23: $i] :
      ( ( m1_subset_1 @ X22 @ X23 )
      | ~ ( r2_hidden @ X22 @ X23 ) ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,(
    r1_tarski @ sk_C_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['4','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_C_1 @ X0 )
      | ( r1_tarski @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('44',plain,(
    r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf(t38_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) )
      <=> ( B
          = ( k1_subset_1 @ A ) ) ) ) )).

thf('45',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( r1_tarski @ X32 @ ( k3_subset_1 @ X31 @ X32 ) )
      | ( X32
        = ( k1_subset_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t38_subset_1])).

thf('46',plain,
    ( ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('48',plain,(
    ! [X25: $i] :
      ( ( k1_subset_1 @ X25 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('49',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['49','50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1UJLVpLxPZ
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:54:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.19/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.51  % Solved by: fo/fo7.sh
% 0.19/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.51  % done 266 iterations in 0.065s
% 0.19/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.51  % SZS output start Refutation
% 0.19/0.51  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.19/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.51  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.19/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.51  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.19/0.51  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.19/0.51  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.19/0.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.51  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.19/0.51  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.19/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.51  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.19/0.51  thf(t40_subset_1, conjecture,
% 0.19/0.51    (![A:$i,B:$i,C:$i]:
% 0.19/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.51       ( ( ( r1_tarski @ B @ C ) & ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) =>
% 0.19/0.51         ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.19/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.51    (~( ![A:$i,B:$i,C:$i]:
% 0.19/0.51        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.51          ( ( ( r1_tarski @ B @ C ) & 
% 0.19/0.51              ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) =>
% 0.19/0.51            ( ( B ) = ( k1_xboole_0 ) ) ) ) )),
% 0.19/0.51    inference('cnf.neg', [status(esa)], [t40_subset_1])).
% 0.19/0.51  thf('0', plain, ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_C_1))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('1', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf(t35_subset_1, axiom,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.51       ( ![C:$i]:
% 0.19/0.51         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.51           ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) =>
% 0.19/0.51             ( r1_tarski @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 0.19/0.51  thf('2', plain,
% 0.19/0.51      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.19/0.51         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X29))
% 0.19/0.51          | (r1_tarski @ X28 @ (k3_subset_1 @ X29 @ X30))
% 0.19/0.51          | ~ (r1_tarski @ X30 @ (k3_subset_1 @ X29 @ X28))
% 0.19/0.51          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X29)))),
% 0.19/0.51      inference('cnf', [status(esa)], [t35_subset_1])).
% 0.19/0.51  thf('3', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.19/0.51          | ~ (r1_tarski @ X0 @ (k3_subset_1 @ sk_A @ sk_C_1))
% 0.19/0.51          | (r1_tarski @ sk_C_1 @ (k3_subset_1 @ sk_A @ X0)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.51  thf('4', plain,
% 0.19/0.51      (((r1_tarski @ sk_C_1 @ (k3_subset_1 @ sk_A @ sk_B_1))
% 0.19/0.51        | ~ (m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['0', '3'])).
% 0.19/0.51  thf('5', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf(d2_subset_1, axiom,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( ( v1_xboole_0 @ A ) =>
% 0.19/0.51         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.19/0.51       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.19/0.51         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.19/0.51  thf('6', plain,
% 0.19/0.51      (![X22 : $i, X23 : $i]:
% 0.19/0.51         (~ (m1_subset_1 @ X22 @ X23)
% 0.19/0.51          | (r2_hidden @ X22 @ X23)
% 0.19/0.51          | (v1_xboole_0 @ X23))),
% 0.19/0.51      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.19/0.51  thf('7', plain,
% 0.19/0.51      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.19/0.51        | (r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['5', '6'])).
% 0.19/0.51  thf(d1_zfmisc_1, axiom,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.19/0.51       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.19/0.51  thf('8', plain,
% 0.19/0.51      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.19/0.51         (~ (r2_hidden @ X20 @ X19)
% 0.19/0.51          | (r1_tarski @ X20 @ X18)
% 0.19/0.51          | ((X19) != (k1_zfmisc_1 @ X18)))),
% 0.19/0.51      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.19/0.51  thf('9', plain,
% 0.19/0.51      (![X18 : $i, X20 : $i]:
% 0.19/0.51         ((r1_tarski @ X20 @ X18) | ~ (r2_hidden @ X20 @ (k1_zfmisc_1 @ X18)))),
% 0.19/0.51      inference('simplify', [status(thm)], ['8'])).
% 0.19/0.51  thf('10', plain,
% 0.19/0.51      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A)) | (r1_tarski @ sk_C_1 @ sk_A))),
% 0.19/0.51      inference('sup-', [status(thm)], ['7', '9'])).
% 0.19/0.51  thf('11', plain, ((r1_tarski @ sk_B_1 @ sk_C_1)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf(t28_xboole_1, axiom,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.19/0.51  thf('12', plain,
% 0.19/0.51      (![X11 : $i, X12 : $i]:
% 0.19/0.51         (((k3_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_tarski @ X11 @ X12))),
% 0.19/0.51      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.19/0.51  thf('13', plain, (((k3_xboole_0 @ sk_B_1 @ sk_C_1) = (sk_B_1))),
% 0.19/0.51      inference('sup-', [status(thm)], ['11', '12'])).
% 0.19/0.51  thf(t100_xboole_1, axiom,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.19/0.51  thf('14', plain,
% 0.19/0.51      (![X5 : $i, X6 : $i]:
% 0.19/0.51         ((k4_xboole_0 @ X5 @ X6)
% 0.19/0.51           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.19/0.51      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.19/0.51  thf('15', plain,
% 0.19/0.51      (((k4_xboole_0 @ sk_B_1 @ sk_C_1) = (k5_xboole_0 @ sk_B_1 @ sk_B_1))),
% 0.19/0.51      inference('sup+', [status(thm)], ['13', '14'])).
% 0.19/0.51  thf(t92_xboole_1, axiom,
% 0.19/0.51    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.19/0.51  thf('16', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ X16) = (k1_xboole_0))),
% 0.19/0.51      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.19/0.51  thf('17', plain, (((k4_xboole_0 @ sk_B_1 @ sk_C_1) = (k1_xboole_0))),
% 0.19/0.51      inference('demod', [status(thm)], ['15', '16'])).
% 0.19/0.51  thf(t39_xboole_1, axiom,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.19/0.51  thf('18', plain,
% 0.19/0.51      (![X14 : $i, X15 : $i]:
% 0.19/0.51         ((k2_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14))
% 0.19/0.51           = (k2_xboole_0 @ X14 @ X15))),
% 0.19/0.51      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.19/0.51  thf('19', plain,
% 0.19/0.51      (((k2_xboole_0 @ sk_C_1 @ k1_xboole_0) = (k2_xboole_0 @ sk_C_1 @ sk_B_1))),
% 0.19/0.51      inference('sup+', [status(thm)], ['17', '18'])).
% 0.19/0.51  thf(commutativity_k2_xboole_0, axiom,
% 0.19/0.51    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.19/0.51  thf('20', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.19/0.51      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.19/0.51  thf('21', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.19/0.51      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.19/0.51  thf(t1_boole, axiom,
% 0.19/0.51    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.19/0.51  thf('22', plain, (![X10 : $i]: ((k2_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.19/0.51      inference('cnf', [status(esa)], [t1_boole])).
% 0.19/0.51  thf('23', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.19/0.51      inference('sup+', [status(thm)], ['21', '22'])).
% 0.19/0.51  thf('24', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.19/0.51      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.19/0.51  thf('25', plain, (((sk_C_1) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.19/0.51      inference('demod', [status(thm)], ['19', '20', '23', '24'])).
% 0.19/0.51  thf(t11_xboole_1, axiom,
% 0.19/0.51    (![A:$i,B:$i,C:$i]:
% 0.19/0.51     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.19/0.51  thf('26', plain,
% 0.19/0.51      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.19/0.51         ((r1_tarski @ X7 @ X8) | ~ (r1_tarski @ (k2_xboole_0 @ X7 @ X9) @ X8))),
% 0.19/0.51      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.19/0.51  thf('27', plain,
% 0.19/0.51      (![X0 : $i]: (~ (r1_tarski @ sk_C_1 @ X0) | (r1_tarski @ sk_B_1 @ X0))),
% 0.19/0.51      inference('sup-', [status(thm)], ['25', '26'])).
% 0.19/0.51  thf('28', plain,
% 0.19/0.51      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A)) | (r1_tarski @ sk_B_1 @ sk_A))),
% 0.19/0.51      inference('sup-', [status(thm)], ['10', '27'])).
% 0.19/0.51  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.19/0.51  thf('29', plain, (![X13 : $i]: (r1_tarski @ k1_xboole_0 @ X13)),
% 0.19/0.51      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.19/0.51  thf('30', plain,
% 0.19/0.51      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.19/0.51         (~ (r1_tarski @ X17 @ X18)
% 0.19/0.51          | (r2_hidden @ X17 @ X19)
% 0.19/0.51          | ((X19) != (k1_zfmisc_1 @ X18)))),
% 0.19/0.51      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.19/0.51  thf('31', plain,
% 0.19/0.51      (![X17 : $i, X18 : $i]:
% 0.19/0.51         ((r2_hidden @ X17 @ (k1_zfmisc_1 @ X18)) | ~ (r1_tarski @ X17 @ X18))),
% 0.19/0.51      inference('simplify', [status(thm)], ['30'])).
% 0.19/0.51  thf('32', plain,
% 0.19/0.51      (![X0 : $i]: (r2_hidden @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.19/0.51      inference('sup-', [status(thm)], ['29', '31'])).
% 0.19/0.51  thf(d1_xboole_0, axiom,
% 0.19/0.51    (![A:$i]:
% 0.19/0.51     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.19/0.51  thf('33', plain,
% 0.19/0.51      (![X2 : $i, X3 : $i]: (~ (r2_hidden @ X2 @ X3) | ~ (v1_xboole_0 @ X3))),
% 0.19/0.51      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.19/0.51  thf('34', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.19/0.51      inference('sup-', [status(thm)], ['32', '33'])).
% 0.19/0.51  thf('35', plain, ((r1_tarski @ sk_B_1 @ sk_A)),
% 0.19/0.51      inference('sup-', [status(thm)], ['28', '34'])).
% 0.19/0.51  thf('36', plain,
% 0.19/0.51      (![X17 : $i, X18 : $i]:
% 0.19/0.51         ((r2_hidden @ X17 @ (k1_zfmisc_1 @ X18)) | ~ (r1_tarski @ X17 @ X18))),
% 0.19/0.51      inference('simplify', [status(thm)], ['30'])).
% 0.19/0.51  thf('37', plain, ((r2_hidden @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.19/0.51      inference('sup-', [status(thm)], ['35', '36'])).
% 0.19/0.51  thf('38', plain,
% 0.19/0.51      (![X22 : $i, X23 : $i]:
% 0.19/0.51         (~ (r2_hidden @ X22 @ X23)
% 0.19/0.51          | (m1_subset_1 @ X22 @ X23)
% 0.19/0.51          | (v1_xboole_0 @ X23))),
% 0.19/0.51      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.19/0.51  thf('39', plain,
% 0.19/0.51      (![X2 : $i, X3 : $i]: (~ (r2_hidden @ X2 @ X3) | ~ (v1_xboole_0 @ X3))),
% 0.19/0.51      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.19/0.51  thf('40', plain,
% 0.19/0.51      (![X22 : $i, X23 : $i]:
% 0.19/0.51         ((m1_subset_1 @ X22 @ X23) | ~ (r2_hidden @ X22 @ X23))),
% 0.19/0.51      inference('clc', [status(thm)], ['38', '39'])).
% 0.19/0.51  thf('41', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.19/0.51      inference('sup-', [status(thm)], ['37', '40'])).
% 0.19/0.51  thf('42', plain, ((r1_tarski @ sk_C_1 @ (k3_subset_1 @ sk_A @ sk_B_1))),
% 0.19/0.51      inference('demod', [status(thm)], ['4', '41'])).
% 0.19/0.51  thf('43', plain,
% 0.19/0.51      (![X0 : $i]: (~ (r1_tarski @ sk_C_1 @ X0) | (r1_tarski @ sk_B_1 @ X0))),
% 0.19/0.51      inference('sup-', [status(thm)], ['25', '26'])).
% 0.19/0.51  thf('44', plain, ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))),
% 0.19/0.51      inference('sup-', [status(thm)], ['42', '43'])).
% 0.19/0.51  thf(t38_subset_1, axiom,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.51       ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 0.19/0.51         ( ( B ) = ( k1_subset_1 @ A ) ) ) ))).
% 0.19/0.51  thf('45', plain,
% 0.19/0.51      (![X31 : $i, X32 : $i]:
% 0.19/0.51         (~ (r1_tarski @ X32 @ (k3_subset_1 @ X31 @ X32))
% 0.19/0.51          | ((X32) = (k1_subset_1 @ X31))
% 0.19/0.51          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X31)))),
% 0.19/0.51      inference('cnf', [status(esa)], [t38_subset_1])).
% 0.19/0.51  thf('46', plain,
% 0.19/0.51      ((~ (m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))
% 0.19/0.51        | ((sk_B_1) = (k1_subset_1 @ sk_A)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['44', '45'])).
% 0.19/0.51  thf('47', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.19/0.51      inference('sup-', [status(thm)], ['37', '40'])).
% 0.19/0.51  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.19/0.51  thf('48', plain, (![X25 : $i]: ((k1_subset_1 @ X25) = (k1_xboole_0))),
% 0.19/0.51      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.19/0.51  thf('49', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.19/0.51      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.19/0.51  thf('50', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('51', plain, ($false),
% 0.19/0.51      inference('simplify_reflect-', [status(thm)], ['49', '50'])).
% 0.19/0.51  
% 0.19/0.51  % SZS output end Refutation
% 0.19/0.51  
% 0.19/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
