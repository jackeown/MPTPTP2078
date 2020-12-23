%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.shFnSC4MJ5

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:02 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 115 expanded)
%              Number of leaves         :   29 (  48 expanded)
%              Depth                    :   13
%              Number of atoms          :  554 (1244 expanded)
%              Number of equality atoms :   22 (  58 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k3_orders_2_type,type,(
    k3_orders_2: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(r2_orders_2_type,type,(
    r2_orders_2: $i > $i > $i > $o )).

thf(k1_struct_0_type,type,(
    k1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t9_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k4_tarski @ C @ D ) ) ) ) ) )).

thf('0',plain,(
    ! [X9: $i] :
      ( ( X9 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X9 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

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

thf('1',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('2',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X5 ) ) ),
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
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_orders_2 @ X14 )
      | ~ ( v5_orders_2 @ X14 )
      | ~ ( v4_orders_2 @ X14 )
      | ~ ( v3_orders_2 @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) )
      | ( m1_subset_1 @ ( k3_orders_2 @ X14 @ X13 @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) ) ) ),
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
    | ( m1_subset_1 @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
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
    | ( m1_subset_1 @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['5','6','7','8','9'])).

thf('11',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['10','11'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('13',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( m1_subset_1 @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1 )
      = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_B @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','14'])).

thf(d2_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k1_struct_0 @ A )
        = k1_xboole_0 ) ) )).

thf('16',plain,(
    ! [X12: $i] :
      ( ( ( k1_struct_0 @ X12 )
        = k1_xboole_0 )
      | ~ ( l1_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d2_struct_0])).

thf('17',plain,(
    ( k3_orders_2 @ sk_A @ ( k1_struct_0 @ sk_A ) @ sk_B_1 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1 )
     != k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('20',plain,(
    ! [X16: $i] :
      ( ( l1_struct_0 @ X16 )
      | ~ ( l1_orders_2 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf('21',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1 )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['18','21'])).

thf('23',plain,(
    m1_subset_1 @ ( sk_B @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['15','22'])).

thf('24',plain,(
    ! [X9: $i] :
      ( ( X9 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X9 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('25',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X5 ) ) ),
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

thf('26',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X18 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( r2_hidden @ X17 @ ( k3_orders_2 @ X18 @ X19 @ X20 ) )
      | ( r2_hidden @ X17 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X18 ) )
      | ~ ( l1_orders_2 @ X18 )
      | ~ ( v5_orders_2 @ X18 )
      | ~ ( v4_orders_2 @ X18 )
      | ~ ( v3_orders_2 @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t57_orders_2])).

thf('27',plain,(
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
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_orders_2 @ X1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
      | ~ ( m1_subset_1 @ ( sk_B @ ( k3_orders_2 @ X1 @ k1_xboole_0 @ X0 ) ) @ ( u1_struct_0 @ X1 ) )
      | ( r2_hidden @ ( sk_B @ ( k3_orders_2 @ X1 @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 )
      | ~ ( v5_orders_2 @ X1 )
      | ~ ( v4_orders_2 @ X1 )
      | ~ ( v3_orders_2 @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_B @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1 ) ) @ k1_xboole_0 )
    | ( ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','28'])).

thf('30',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_B @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1 ) ) @ k1_xboole_0 )
    | ( ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['29','30','31','32','33','34'])).

thf('36',plain,(
    ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1 )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['18','21'])).

thf('37',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_B @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1 ) ) @ k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['35','36'])).

thf('38',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    r2_hidden @ ( sk_B @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1 ) ) @ k1_xboole_0 ),
    inference(clc,[status(thm)],['37','38'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('40',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X2 )
        = k1_xboole_0 )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('41',plain,(
    ! [X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['40'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('42',plain,(
    ! [X3: $i,X4: $i] :
      ~ ( r2_hidden @ X3 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('43',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    $false ),
    inference('sup-',[status(thm)],['39','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.shFnSC4MJ5
% 0.14/0.38  % Computer   : n004.cluster.edu
% 0.14/0.38  % Model      : x86_64 x86_64
% 0.14/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.38  % Memory     : 8042.1875MB
% 0.14/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.38  % CPULimit   : 60
% 0.14/0.38  % DateTime   : Tue Dec  1 11:23:54 EST 2020
% 0.14/0.38  % CPUTime    : 
% 0.14/0.38  % Running portfolio for 600 s
% 0.14/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.38  % Number of cores: 8
% 0.14/0.38  % Python version: Python 3.6.8
% 0.14/0.38  % Running in FO mode
% 0.24/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.56  % Solved by: fo/fo7.sh
% 0.24/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.56  % done 114 iterations in 0.074s
% 0.24/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.56  % SZS output start Refutation
% 0.24/0.56  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.24/0.56  thf(sk_B_type, type, sk_B: $i > $i).
% 0.24/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.24/0.56  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.24/0.56  thf(k3_orders_2_type, type, k3_orders_2: $i > $i > $i > $i).
% 0.24/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.24/0.56  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.24/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.24/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.24/0.56  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.24/0.56  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.24/0.56  thf(r2_orders_2_type, type, r2_orders_2: $i > $i > $i > $o).
% 0.24/0.56  thf(k1_struct_0_type, type, k1_struct_0: $i > $i).
% 0.24/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.56  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.24/0.56  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.24/0.56  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.24/0.56  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.24/0.56  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.24/0.56  thf(t9_mcart_1, axiom,
% 0.24/0.56    (![A:$i]:
% 0.24/0.56     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.24/0.56          ( ![B:$i]:
% 0.24/0.56            ( ~( ( r2_hidden @ B @ A ) & 
% 0.24/0.56                 ( ![C:$i,D:$i]:
% 0.24/0.56                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.24/0.56                        ( ( B ) = ( k4_tarski @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.24/0.56  thf('0', plain,
% 0.24/0.56      (![X9 : $i]: (((X9) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X9) @ X9))),
% 0.24/0.56      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.24/0.56  thf(t60_orders_2, conjecture,
% 0.24/0.56    (![A:$i]:
% 0.24/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.24/0.56         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.24/0.56       ( ![B:$i]:
% 0.24/0.56         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.24/0.56           ( ( k3_orders_2 @ A @ ( k1_struct_0 @ A ) @ B ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.24/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.56    (~( ![A:$i]:
% 0.24/0.56        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.24/0.56            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.24/0.56          ( ![B:$i]:
% 0.24/0.56            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.24/0.56              ( ( k3_orders_2 @ A @ ( k1_struct_0 @ A ) @ B ) = ( k1_xboole_0 ) ) ) ) ) )),
% 0.24/0.56    inference('cnf.neg', [status(esa)], [t60_orders_2])).
% 0.24/0.56  thf('1', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf(t4_subset_1, axiom,
% 0.24/0.56    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.24/0.56  thf('2', plain,
% 0.24/0.56      (![X5 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X5))),
% 0.24/0.56      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.24/0.56  thf(dt_k3_orders_2, axiom,
% 0.24/0.56    (![A:$i,B:$i,C:$i]:
% 0.24/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.24/0.56         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 0.24/0.56         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.24/0.56         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.24/0.56       ( m1_subset_1 @
% 0.24/0.56         ( k3_orders_2 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.24/0.56  thf('3', plain,
% 0.24/0.56      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.24/0.56         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.24/0.56          | ~ (l1_orders_2 @ X14)
% 0.24/0.56          | ~ (v5_orders_2 @ X14)
% 0.24/0.56          | ~ (v4_orders_2 @ X14)
% 0.24/0.56          | ~ (v3_orders_2 @ X14)
% 0.24/0.56          | (v2_struct_0 @ X14)
% 0.24/0.56          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X14))
% 0.24/0.56          | (m1_subset_1 @ (k3_orders_2 @ X14 @ X13 @ X15) @ 
% 0.24/0.56             (k1_zfmisc_1 @ (u1_struct_0 @ X14))))),
% 0.24/0.56      inference('cnf', [status(esa)], [dt_k3_orders_2])).
% 0.24/0.56  thf('4', plain,
% 0.24/0.56      (![X0 : $i, X1 : $i]:
% 0.24/0.56         ((m1_subset_1 @ (k3_orders_2 @ X0 @ k1_xboole_0 @ X1) @ 
% 0.24/0.56           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.24/0.56          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.24/0.56          | (v2_struct_0 @ X0)
% 0.24/0.56          | ~ (v3_orders_2 @ X0)
% 0.24/0.56          | ~ (v4_orders_2 @ X0)
% 0.24/0.56          | ~ (v5_orders_2 @ X0)
% 0.24/0.56          | ~ (l1_orders_2 @ X0))),
% 0.24/0.56      inference('sup-', [status(thm)], ['2', '3'])).
% 0.24/0.56  thf('5', plain,
% 0.24/0.56      ((~ (l1_orders_2 @ sk_A)
% 0.24/0.56        | ~ (v5_orders_2 @ sk_A)
% 0.24/0.56        | ~ (v4_orders_2 @ sk_A)
% 0.24/0.56        | ~ (v3_orders_2 @ sk_A)
% 0.24/0.56        | (v2_struct_0 @ sk_A)
% 0.24/0.56        | (m1_subset_1 @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1) @ 
% 0.24/0.56           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.24/0.56      inference('sup-', [status(thm)], ['1', '4'])).
% 0.24/0.56  thf('6', plain, ((l1_orders_2 @ sk_A)),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf('7', plain, ((v5_orders_2 @ sk_A)),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf('8', plain, ((v4_orders_2 @ sk_A)),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf('9', plain, ((v3_orders_2 @ sk_A)),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf('10', plain,
% 0.24/0.56      (((v2_struct_0 @ sk_A)
% 0.24/0.56        | (m1_subset_1 @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1) @ 
% 0.24/0.56           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.24/0.56      inference('demod', [status(thm)], ['5', '6', '7', '8', '9'])).
% 0.24/0.56  thf('11', plain, (~ (v2_struct_0 @ sk_A)),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf('12', plain,
% 0.24/0.56      ((m1_subset_1 @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1) @ 
% 0.24/0.56        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.56      inference('clc', [status(thm)], ['10', '11'])).
% 0.24/0.56  thf(t4_subset, axiom,
% 0.24/0.56    (![A:$i,B:$i,C:$i]:
% 0.24/0.56     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.24/0.56       ( m1_subset_1 @ A @ C ) ))).
% 0.24/0.56  thf('13', plain,
% 0.24/0.56      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.24/0.56         (~ (r2_hidden @ X6 @ X7)
% 0.24/0.56          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 0.24/0.56          | (m1_subset_1 @ X6 @ X8))),
% 0.24/0.56      inference('cnf', [status(esa)], [t4_subset])).
% 0.24/0.56  thf('14', plain,
% 0.24/0.56      (![X0 : $i]:
% 0.24/0.56         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.24/0.56          | ~ (r2_hidden @ X0 @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1)))),
% 0.24/0.56      inference('sup-', [status(thm)], ['12', '13'])).
% 0.24/0.56  thf('15', plain,
% 0.24/0.56      ((((k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1) = (k1_xboole_0))
% 0.24/0.56        | (m1_subset_1 @ 
% 0.24/0.56           (sk_B @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1)) @ 
% 0.24/0.56           (u1_struct_0 @ sk_A)))),
% 0.24/0.56      inference('sup-', [status(thm)], ['0', '14'])).
% 0.24/0.56  thf(d2_struct_0, axiom,
% 0.24/0.56    (![A:$i]:
% 0.24/0.56     ( ( l1_struct_0 @ A ) => ( ( k1_struct_0 @ A ) = ( k1_xboole_0 ) ) ))).
% 0.24/0.56  thf('16', plain,
% 0.24/0.56      (![X12 : $i]:
% 0.24/0.56         (((k1_struct_0 @ X12) = (k1_xboole_0)) | ~ (l1_struct_0 @ X12))),
% 0.24/0.56      inference('cnf', [status(esa)], [d2_struct_0])).
% 0.24/0.56  thf('17', plain,
% 0.24/0.56      (((k3_orders_2 @ sk_A @ (k1_struct_0 @ sk_A) @ sk_B_1) != (k1_xboole_0))),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf('18', plain,
% 0.24/0.56      ((((k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1) != (k1_xboole_0))
% 0.24/0.56        | ~ (l1_struct_0 @ sk_A))),
% 0.24/0.56      inference('sup-', [status(thm)], ['16', '17'])).
% 0.24/0.56  thf('19', plain, ((l1_orders_2 @ sk_A)),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf(dt_l1_orders_2, axiom,
% 0.24/0.56    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 0.24/0.56  thf('20', plain,
% 0.24/0.56      (![X16 : $i]: ((l1_struct_0 @ X16) | ~ (l1_orders_2 @ X16))),
% 0.24/0.56      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 0.24/0.56  thf('21', plain, ((l1_struct_0 @ sk_A)),
% 0.24/0.56      inference('sup-', [status(thm)], ['19', '20'])).
% 0.24/0.56  thf('22', plain,
% 0.24/0.56      (((k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1) != (k1_xboole_0))),
% 0.24/0.56      inference('demod', [status(thm)], ['18', '21'])).
% 0.24/0.56  thf('23', plain,
% 0.24/0.56      ((m1_subset_1 @ (sk_B @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1)) @ 
% 0.24/0.56        (u1_struct_0 @ sk_A))),
% 0.24/0.56      inference('simplify_reflect-', [status(thm)], ['15', '22'])).
% 0.24/0.56  thf('24', plain,
% 0.24/0.56      (![X9 : $i]: (((X9) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X9) @ X9))),
% 0.24/0.56      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.24/0.56  thf('25', plain,
% 0.24/0.56      (![X5 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X5))),
% 0.24/0.56      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.24/0.56  thf(t57_orders_2, axiom,
% 0.24/0.56    (![A:$i]:
% 0.24/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.24/0.56         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.24/0.56       ( ![B:$i]:
% 0.24/0.56         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.24/0.56           ( ![C:$i]:
% 0.24/0.56             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.24/0.56               ( ![D:$i]:
% 0.24/0.56                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.24/0.56                   ( ( r2_hidden @ B @ ( k3_orders_2 @ A @ D @ C ) ) <=>
% 0.24/0.56                     ( ( r2_orders_2 @ A @ B @ C ) & ( r2_hidden @ B @ D ) ) ) ) ) ) ) ) ) ))).
% 0.24/0.56  thf('26', plain,
% 0.24/0.56      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.24/0.56         (~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X18))
% 0.24/0.56          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.24/0.56          | ~ (r2_hidden @ X17 @ (k3_orders_2 @ X18 @ X19 @ X20))
% 0.24/0.56          | (r2_hidden @ X17 @ X19)
% 0.24/0.56          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X18))
% 0.24/0.56          | ~ (l1_orders_2 @ X18)
% 0.24/0.56          | ~ (v5_orders_2 @ X18)
% 0.24/0.56          | ~ (v4_orders_2 @ X18)
% 0.24/0.56          | ~ (v3_orders_2 @ X18)
% 0.24/0.56          | (v2_struct_0 @ X18))),
% 0.24/0.56      inference('cnf', [status(esa)], [t57_orders_2])).
% 0.24/0.56  thf('27', plain,
% 0.24/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.24/0.56         ((v2_struct_0 @ X0)
% 0.24/0.56          | ~ (v3_orders_2 @ X0)
% 0.24/0.56          | ~ (v4_orders_2 @ X0)
% 0.24/0.56          | ~ (v5_orders_2 @ X0)
% 0.24/0.56          | ~ (l1_orders_2 @ X0)
% 0.24/0.56          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.24/0.56          | (r2_hidden @ X2 @ k1_xboole_0)
% 0.24/0.56          | ~ (r2_hidden @ X2 @ (k3_orders_2 @ X0 @ k1_xboole_0 @ X1))
% 0.24/0.56          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0)))),
% 0.24/0.56      inference('sup-', [status(thm)], ['25', '26'])).
% 0.24/0.56  thf('28', plain,
% 0.24/0.56      (![X0 : $i, X1 : $i]:
% 0.24/0.56         (((k3_orders_2 @ X1 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 0.24/0.56          | ~ (m1_subset_1 @ (sk_B @ (k3_orders_2 @ X1 @ k1_xboole_0 @ X0)) @ 
% 0.24/0.56               (u1_struct_0 @ X1))
% 0.24/0.56          | (r2_hidden @ (sk_B @ (k3_orders_2 @ X1 @ k1_xboole_0 @ X0)) @ 
% 0.24/0.56             k1_xboole_0)
% 0.24/0.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 0.24/0.56          | ~ (l1_orders_2 @ X1)
% 0.24/0.56          | ~ (v5_orders_2 @ X1)
% 0.24/0.56          | ~ (v4_orders_2 @ X1)
% 0.24/0.56          | ~ (v3_orders_2 @ X1)
% 0.24/0.56          | (v2_struct_0 @ X1))),
% 0.24/0.56      inference('sup-', [status(thm)], ['24', '27'])).
% 0.24/0.56  thf('29', plain,
% 0.24/0.56      (((v2_struct_0 @ sk_A)
% 0.24/0.56        | ~ (v3_orders_2 @ sk_A)
% 0.24/0.56        | ~ (v4_orders_2 @ sk_A)
% 0.24/0.56        | ~ (v5_orders_2 @ sk_A)
% 0.24/0.56        | ~ (l1_orders_2 @ sk_A)
% 0.24/0.56        | ~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.24/0.56        | (r2_hidden @ (sk_B @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1)) @ 
% 0.24/0.56           k1_xboole_0)
% 0.24/0.56        | ((k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1) = (k1_xboole_0)))),
% 0.24/0.56      inference('sup-', [status(thm)], ['23', '28'])).
% 0.24/0.56  thf('30', plain, ((v3_orders_2 @ sk_A)),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf('31', plain, ((v4_orders_2 @ sk_A)),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf('32', plain, ((v5_orders_2 @ sk_A)),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf('33', plain, ((l1_orders_2 @ sk_A)),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf('34', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf('35', plain,
% 0.24/0.56      (((v2_struct_0 @ sk_A)
% 0.24/0.56        | (r2_hidden @ (sk_B @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1)) @ 
% 0.24/0.56           k1_xboole_0)
% 0.24/0.56        | ((k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1) = (k1_xboole_0)))),
% 0.24/0.56      inference('demod', [status(thm)], ['29', '30', '31', '32', '33', '34'])).
% 0.24/0.56  thf('36', plain,
% 0.24/0.56      (((k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1) != (k1_xboole_0))),
% 0.24/0.56      inference('demod', [status(thm)], ['18', '21'])).
% 0.24/0.56  thf('37', plain,
% 0.24/0.56      (((v2_struct_0 @ sk_A)
% 0.24/0.56        | (r2_hidden @ (sk_B @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1)) @ 
% 0.24/0.56           k1_xboole_0))),
% 0.24/0.56      inference('simplify_reflect-', [status(thm)], ['35', '36'])).
% 0.24/0.56  thf('38', plain, (~ (v2_struct_0 @ sk_A)),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf('39', plain,
% 0.24/0.56      ((r2_hidden @ (sk_B @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1)) @ 
% 0.24/0.56        k1_xboole_0)),
% 0.24/0.56      inference('clc', [status(thm)], ['37', '38'])).
% 0.24/0.56  thf(t113_zfmisc_1, axiom,
% 0.24/0.56    (![A:$i,B:$i]:
% 0.24/0.56     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.24/0.56       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.24/0.56  thf('40', plain,
% 0.24/0.56      (![X1 : $i, X2 : $i]:
% 0.24/0.56         (((k2_zfmisc_1 @ X1 @ X2) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 0.24/0.56      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.24/0.56  thf('41', plain,
% 0.24/0.56      (![X1 : $i]: ((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.24/0.56      inference('simplify', [status(thm)], ['40'])).
% 0.24/0.56  thf(t152_zfmisc_1, axiom,
% 0.24/0.56    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.24/0.56  thf('42', plain,
% 0.24/0.56      (![X3 : $i, X4 : $i]: ~ (r2_hidden @ X3 @ (k2_zfmisc_1 @ X3 @ X4))),
% 0.24/0.56      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.24/0.56  thf('43', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.24/0.56      inference('sup-', [status(thm)], ['41', '42'])).
% 0.24/0.56  thf('44', plain, ($false), inference('sup-', [status(thm)], ['39', '43'])).
% 0.24/0.56  
% 0.24/0.56  % SZS output end Refutation
% 0.24/0.56  
% 0.40/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
