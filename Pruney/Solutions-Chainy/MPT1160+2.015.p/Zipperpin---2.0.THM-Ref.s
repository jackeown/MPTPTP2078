%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.eQp3GJSOLS

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:01 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 137 expanded)
%              Number of leaves         :   27 (  54 expanded)
%              Depth                    :   11
%              Number of atoms          :  525 (1589 expanded)
%              Number of equality atoms :   19 (  66 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(r2_orders_2_type,type,(
    r2_orders_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_orders_2_type,type,(
    k3_orders_2: $i > $i > $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(k1_struct_0_type,type,(
    k1_struct_0: $i > $i )).

thf(t60_orders_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( k3_orders_2 @ A @ ( k1_struct_0 @ A ) @ B )
            = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v3_orders_2 @ A )
          & ( v4_orders_2 @ A )
          & ( v5_orders_2 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ( ( k3_orders_2 @ A @ ( k1_struct_0 @ A ) @ B )
              = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t60_orders_2])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('2',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(dt_k3_orders_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( m1_subset_1 @ ( k3_orders_2 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('3',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( l1_orders_2 @ X13 )
      | ~ ( v5_orders_2 @ X13 )
      | ~ ( v4_orders_2 @ X13 )
      | ~ ( v3_orders_2 @ X13 )
      | ( v2_struct_0 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ( m1_subset_1 @ ( k3_orders_2 @ X13 @ X12 @ X14 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_orders_2])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_orders_2 @ X0 @ k1_xboole_0 @ X1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['5','6','7','8','9'])).

thf('11',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['10','11'])).

thf(t10_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ~ ( ( B != k1_xboole_0 )
          & ! [C: $i] :
              ( ( m1_subset_1 @ C @ A )
             => ~ ( r2_hidden @ C @ B ) ) ) ) )).

thf('13',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r2_hidden @ ( sk_C @ X5 @ X6 ) @ X5 )
      | ( X5 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t10_subset_1])).

thf('14',plain,
    ( ( ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B )
      = k1_xboole_0 )
    | ( r2_hidden @ ( sk_C @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(d2_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k1_struct_0 @ A )
        = k1_xboole_0 ) ) )).

thf('15',plain,(
    ! [X11: $i] :
      ( ( ( k1_struct_0 @ X11 )
        = k1_xboole_0 )
      | ~ ( l1_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d2_struct_0])).

thf('16',plain,(
    ( k3_orders_2 @ sk_A @ ( k1_struct_0 @ sk_A ) @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B )
     != k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('19',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_orders_2 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf('20',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['17','20'])).

thf('22',plain,(
    r2_hidden @ ( sk_C @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['14','21'])).

thf('23',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t57_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ( ( r2_hidden @ B @ ( k3_orders_2 @ A @ D @ C ) )
                  <=> ( ( r2_orders_2 @ A @ B @ C )
                      & ( r2_hidden @ B @ D ) ) ) ) ) ) ) )).

thf('24',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X17 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( r2_hidden @ X16 @ ( k3_orders_2 @ X17 @ X18 @ X19 ) )
      | ( r2_hidden @ X16 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X17 ) )
      | ~ ( l1_orders_2 @ X17 )
      | ~ ( v5_orders_2 @ X17 )
      | ~ ( v4_orders_2 @ X17 )
      | ~ ( v3_orders_2 @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t57_orders_2])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r2_hidden @ X2 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X2 @ ( k3_orders_2 @ X0 @ k1_xboole_0 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ~ ( m1_subset_1 @ ( sk_C @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_C @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    m1_subset_1 @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('28',plain,(
    ! [X5: $i,X6: $i] :
      ( ( m1_subset_1 @ ( sk_C @ X5 @ X6 ) @ X6 )
      | ( X5 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t10_subset_1])).

thf('29',plain,
    ( ( ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B )
      = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_C @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['17','20'])).

thf('31',plain,(
    m1_subset_1 @ ( sk_C @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( r2_hidden @ ( sk_C @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ k1_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['26','31','32','33','34','35','36'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('38',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X2 )
        = k1_xboole_0 )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('39',plain,(
    ! [X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['38'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('40',plain,(
    ! [X3: $i,X4: $i] :
      ~ ( r2_hidden @ X3 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('41',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['37','41'])).

thf('43',plain,(
    $false ),
    inference(demod,[status(thm)],['0','42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.eQp3GJSOLS
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:48:48 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.39/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.39/0.59  % Solved by: fo/fo7.sh
% 0.39/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.59  % done 475 iterations in 0.148s
% 0.39/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.39/0.59  % SZS output start Refutation
% 0.39/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.59  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.39/0.59  thf(r2_orders_2_type, type, r2_orders_2: $i > $i > $i > $o).
% 0.39/0.59  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.39/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.59  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.39/0.59  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.39/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.59  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.39/0.59  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.39/0.59  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.39/0.59  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.39/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.39/0.59  thf(k3_orders_2_type, type, k3_orders_2: $i > $i > $i > $i).
% 0.39/0.59  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.39/0.59  thf(k1_struct_0_type, type, k1_struct_0: $i > $i).
% 0.39/0.59  thf(t60_orders_2, conjecture,
% 0.39/0.59    (![A:$i]:
% 0.39/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.39/0.59         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.39/0.59       ( ![B:$i]:
% 0.39/0.59         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.39/0.59           ( ( k3_orders_2 @ A @ ( k1_struct_0 @ A ) @ B ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.39/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.59    (~( ![A:$i]:
% 0.39/0.59        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.39/0.59            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.39/0.59          ( ![B:$i]:
% 0.39/0.59            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.39/0.59              ( ( k3_orders_2 @ A @ ( k1_struct_0 @ A ) @ B ) = ( k1_xboole_0 ) ) ) ) ) )),
% 0.39/0.59    inference('cnf.neg', [status(esa)], [t60_orders_2])).
% 0.39/0.59  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('1', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf(t4_subset_1, axiom,
% 0.39/0.59    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.39/0.59  thf('2', plain,
% 0.39/0.59      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 0.39/0.59      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.39/0.59  thf(dt_k3_orders_2, axiom,
% 0.39/0.59    (![A:$i,B:$i,C:$i]:
% 0.39/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.39/0.59         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 0.39/0.59         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.39/0.59         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.59       ( m1_subset_1 @
% 0.39/0.59         ( k3_orders_2 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.39/0.59  thf('3', plain,
% 0.39/0.59      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.39/0.59         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.39/0.59          | ~ (l1_orders_2 @ X13)
% 0.39/0.59          | ~ (v5_orders_2 @ X13)
% 0.39/0.59          | ~ (v4_orders_2 @ X13)
% 0.39/0.59          | ~ (v3_orders_2 @ X13)
% 0.39/0.59          | (v2_struct_0 @ X13)
% 0.39/0.59          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X13))
% 0.39/0.59          | (m1_subset_1 @ (k3_orders_2 @ X13 @ X12 @ X14) @ 
% 0.39/0.59             (k1_zfmisc_1 @ (u1_struct_0 @ X13))))),
% 0.39/0.59      inference('cnf', [status(esa)], [dt_k3_orders_2])).
% 0.39/0.59  thf('4', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         ((m1_subset_1 @ (k3_orders_2 @ X0 @ k1_xboole_0 @ X1) @ 
% 0.39/0.59           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.39/0.59          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.39/0.59          | (v2_struct_0 @ X0)
% 0.39/0.59          | ~ (v3_orders_2 @ X0)
% 0.39/0.59          | ~ (v4_orders_2 @ X0)
% 0.39/0.59          | ~ (v5_orders_2 @ X0)
% 0.39/0.59          | ~ (l1_orders_2 @ X0))),
% 0.39/0.59      inference('sup-', [status(thm)], ['2', '3'])).
% 0.39/0.59  thf('5', plain,
% 0.39/0.59      ((~ (l1_orders_2 @ sk_A)
% 0.39/0.59        | ~ (v5_orders_2 @ sk_A)
% 0.39/0.59        | ~ (v4_orders_2 @ sk_A)
% 0.39/0.59        | ~ (v3_orders_2 @ sk_A)
% 0.39/0.59        | (v2_struct_0 @ sk_A)
% 0.39/0.59        | (m1_subset_1 @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) @ 
% 0.39/0.59           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.39/0.59      inference('sup-', [status(thm)], ['1', '4'])).
% 0.39/0.59  thf('6', plain, ((l1_orders_2 @ sk_A)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('7', plain, ((v5_orders_2 @ sk_A)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('8', plain, ((v4_orders_2 @ sk_A)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('9', plain, ((v3_orders_2 @ sk_A)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('10', plain,
% 0.39/0.59      (((v2_struct_0 @ sk_A)
% 0.39/0.59        | (m1_subset_1 @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) @ 
% 0.39/0.59           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.39/0.59      inference('demod', [status(thm)], ['5', '6', '7', '8', '9'])).
% 0.39/0.59  thf('11', plain, (~ (v2_struct_0 @ sk_A)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('12', plain,
% 0.39/0.59      ((m1_subset_1 @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) @ 
% 0.39/0.59        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.59      inference('clc', [status(thm)], ['10', '11'])).
% 0.39/0.59  thf(t10_subset_1, axiom,
% 0.39/0.59    (![A:$i,B:$i]:
% 0.39/0.59     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.39/0.59       ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.39/0.59            ( ![C:$i]:
% 0.39/0.59              ( ( m1_subset_1 @ C @ A ) => ( ~( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.39/0.59  thf('13', plain,
% 0.39/0.59      (![X5 : $i, X6 : $i]:
% 0.39/0.59         ((r2_hidden @ (sk_C @ X5 @ X6) @ X5)
% 0.39/0.59          | ((X5) = (k1_xboole_0))
% 0.39/0.59          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.39/0.59      inference('cnf', [status(esa)], [t10_subset_1])).
% 0.39/0.59  thf('14', plain,
% 0.39/0.59      ((((k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) = (k1_xboole_0))
% 0.39/0.59        | (r2_hidden @ 
% 0.39/0.59           (sk_C @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) @ 
% 0.39/0.59            (u1_struct_0 @ sk_A)) @ 
% 0.39/0.59           (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['12', '13'])).
% 0.39/0.59  thf(d2_struct_0, axiom,
% 0.39/0.59    (![A:$i]:
% 0.39/0.59     ( ( l1_struct_0 @ A ) => ( ( k1_struct_0 @ A ) = ( k1_xboole_0 ) ) ))).
% 0.39/0.59  thf('15', plain,
% 0.39/0.59      (![X11 : $i]:
% 0.39/0.59         (((k1_struct_0 @ X11) = (k1_xboole_0)) | ~ (l1_struct_0 @ X11))),
% 0.39/0.59      inference('cnf', [status(esa)], [d2_struct_0])).
% 0.39/0.59  thf('16', plain,
% 0.39/0.59      (((k3_orders_2 @ sk_A @ (k1_struct_0 @ sk_A) @ sk_B) != (k1_xboole_0))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('17', plain,
% 0.39/0.59      ((((k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) != (k1_xboole_0))
% 0.39/0.59        | ~ (l1_struct_0 @ sk_A))),
% 0.39/0.59      inference('sup-', [status(thm)], ['15', '16'])).
% 0.39/0.59  thf('18', plain, ((l1_orders_2 @ sk_A)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf(dt_l1_orders_2, axiom,
% 0.39/0.59    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 0.39/0.59  thf('19', plain,
% 0.39/0.59      (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_orders_2 @ X15))),
% 0.39/0.59      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 0.39/0.59  thf('20', plain, ((l1_struct_0 @ sk_A)),
% 0.39/0.59      inference('sup-', [status(thm)], ['18', '19'])).
% 0.39/0.59  thf('21', plain,
% 0.39/0.59      (((k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) != (k1_xboole_0))),
% 0.39/0.59      inference('demod', [status(thm)], ['17', '20'])).
% 0.39/0.59  thf('22', plain,
% 0.39/0.59      ((r2_hidden @ 
% 0.39/0.59        (sk_C @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) @ 
% 0.39/0.59         (u1_struct_0 @ sk_A)) @ 
% 0.39/0.59        (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B))),
% 0.39/0.59      inference('simplify_reflect-', [status(thm)], ['14', '21'])).
% 0.39/0.59  thf('23', plain,
% 0.39/0.59      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 0.39/0.59      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.39/0.59  thf(t57_orders_2, axiom,
% 0.39/0.59    (![A:$i]:
% 0.39/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.39/0.59         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.39/0.59       ( ![B:$i]:
% 0.39/0.59         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.39/0.59           ( ![C:$i]:
% 0.39/0.59             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.39/0.59               ( ![D:$i]:
% 0.39/0.59                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.59                   ( ( r2_hidden @ B @ ( k3_orders_2 @ A @ D @ C ) ) <=>
% 0.39/0.59                     ( ( r2_orders_2 @ A @ B @ C ) & ( r2_hidden @ B @ D ) ) ) ) ) ) ) ) ) ))).
% 0.39/0.59  thf('24', plain,
% 0.39/0.59      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.39/0.59         (~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X17))
% 0.39/0.59          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.39/0.59          | ~ (r2_hidden @ X16 @ (k3_orders_2 @ X17 @ X18 @ X19))
% 0.39/0.59          | (r2_hidden @ X16 @ X18)
% 0.39/0.59          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X17))
% 0.39/0.59          | ~ (l1_orders_2 @ X17)
% 0.39/0.59          | ~ (v5_orders_2 @ X17)
% 0.39/0.59          | ~ (v4_orders_2 @ X17)
% 0.39/0.59          | ~ (v3_orders_2 @ X17)
% 0.39/0.59          | (v2_struct_0 @ X17))),
% 0.39/0.59      inference('cnf', [status(esa)], [t57_orders_2])).
% 0.39/0.59  thf('25', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.59         ((v2_struct_0 @ X0)
% 0.39/0.59          | ~ (v3_orders_2 @ X0)
% 0.39/0.59          | ~ (v4_orders_2 @ X0)
% 0.39/0.59          | ~ (v5_orders_2 @ X0)
% 0.39/0.59          | ~ (l1_orders_2 @ X0)
% 0.39/0.59          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.39/0.59          | (r2_hidden @ X2 @ k1_xboole_0)
% 0.39/0.59          | ~ (r2_hidden @ X2 @ (k3_orders_2 @ X0 @ k1_xboole_0 @ X1))
% 0.39/0.59          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['23', '24'])).
% 0.39/0.59  thf('26', plain,
% 0.39/0.59      ((~ (m1_subset_1 @ 
% 0.39/0.59           (sk_C @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) @ 
% 0.39/0.59            (u1_struct_0 @ sk_A)) @ 
% 0.39/0.59           (u1_struct_0 @ sk_A))
% 0.39/0.59        | (r2_hidden @ 
% 0.39/0.59           (sk_C @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) @ 
% 0.39/0.59            (u1_struct_0 @ sk_A)) @ 
% 0.39/0.59           k1_xboole_0)
% 0.39/0.59        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.39/0.59        | ~ (l1_orders_2 @ sk_A)
% 0.39/0.59        | ~ (v5_orders_2 @ sk_A)
% 0.39/0.59        | ~ (v4_orders_2 @ sk_A)
% 0.39/0.59        | ~ (v3_orders_2 @ sk_A)
% 0.39/0.59        | (v2_struct_0 @ sk_A))),
% 0.39/0.59      inference('sup-', [status(thm)], ['22', '25'])).
% 0.39/0.59  thf('27', plain,
% 0.39/0.59      ((m1_subset_1 @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) @ 
% 0.39/0.59        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.59      inference('clc', [status(thm)], ['10', '11'])).
% 0.39/0.59  thf('28', plain,
% 0.39/0.59      (![X5 : $i, X6 : $i]:
% 0.39/0.59         ((m1_subset_1 @ (sk_C @ X5 @ X6) @ X6)
% 0.39/0.59          | ((X5) = (k1_xboole_0))
% 0.39/0.59          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.39/0.59      inference('cnf', [status(esa)], [t10_subset_1])).
% 0.39/0.59  thf('29', plain,
% 0.39/0.59      ((((k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) = (k1_xboole_0))
% 0.39/0.59        | (m1_subset_1 @ 
% 0.39/0.59           (sk_C @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) @ 
% 0.39/0.59            (u1_struct_0 @ sk_A)) @ 
% 0.39/0.59           (u1_struct_0 @ sk_A)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['27', '28'])).
% 0.39/0.59  thf('30', plain,
% 0.39/0.59      (((k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) != (k1_xboole_0))),
% 0.39/0.59      inference('demod', [status(thm)], ['17', '20'])).
% 0.39/0.59  thf('31', plain,
% 0.39/0.59      ((m1_subset_1 @ 
% 0.39/0.59        (sk_C @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) @ 
% 0.39/0.59         (u1_struct_0 @ sk_A)) @ 
% 0.39/0.59        (u1_struct_0 @ sk_A))),
% 0.39/0.59      inference('simplify_reflect-', [status(thm)], ['29', '30'])).
% 0.39/0.59  thf('32', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('33', plain, ((l1_orders_2 @ sk_A)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('34', plain, ((v5_orders_2 @ sk_A)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('35', plain, ((v4_orders_2 @ sk_A)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('36', plain, ((v3_orders_2 @ sk_A)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('37', plain,
% 0.39/0.59      (((r2_hidden @ 
% 0.39/0.59         (sk_C @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) @ 
% 0.39/0.59          (u1_struct_0 @ sk_A)) @ 
% 0.39/0.59         k1_xboole_0)
% 0.39/0.59        | (v2_struct_0 @ sk_A))),
% 0.39/0.59      inference('demod', [status(thm)],
% 0.39/0.59                ['26', '31', '32', '33', '34', '35', '36'])).
% 0.39/0.59  thf(t113_zfmisc_1, axiom,
% 0.39/0.59    (![A:$i,B:$i]:
% 0.39/0.59     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.39/0.59       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.39/0.59  thf('38', plain,
% 0.39/0.59      (![X1 : $i, X2 : $i]:
% 0.39/0.59         (((k2_zfmisc_1 @ X1 @ X2) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 0.39/0.59      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.39/0.59  thf('39', plain,
% 0.39/0.59      (![X1 : $i]: ((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.39/0.59      inference('simplify', [status(thm)], ['38'])).
% 0.39/0.59  thf(t152_zfmisc_1, axiom,
% 0.39/0.59    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.39/0.59  thf('40', plain,
% 0.39/0.59      (![X3 : $i, X4 : $i]: ~ (r2_hidden @ X3 @ (k2_zfmisc_1 @ X3 @ X4))),
% 0.39/0.59      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.39/0.59  thf('41', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.39/0.59      inference('sup-', [status(thm)], ['39', '40'])).
% 0.39/0.59  thf('42', plain, ((v2_struct_0 @ sk_A)),
% 0.39/0.59      inference('clc', [status(thm)], ['37', '41'])).
% 0.39/0.59  thf('43', plain, ($false), inference('demod', [status(thm)], ['0', '42'])).
% 0.39/0.59  
% 0.39/0.59  % SZS output end Refutation
% 0.39/0.59  
% 0.43/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
