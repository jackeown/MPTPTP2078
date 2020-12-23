%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8Ucu3aK0CZ

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:02 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 114 expanded)
%              Number of leaves         :   29 (  48 expanded)
%              Depth                    :   14
%              Number of atoms          :  549 (1246 expanded)
%              Number of equality atoms :   15 (  50 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_struct_0_type,type,(
    k1_struct_0: $i > $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_orders_2_type,type,(
    r2_orders_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(k3_orders_2_type,type,(
    k3_orders_2: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(t6_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i,F: $i,G: $i] :
                  ( ( ( r2_hidden @ C @ D )
                    & ( r2_hidden @ D @ E )
                    & ( r2_hidden @ E @ F )
                    & ( r2_hidden @ F @ G )
                    & ( r2_hidden @ G @ B ) )
                 => ( r1_xboole_0 @ C @ A ) ) ) ) )).

thf('0',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t6_mcart_1])).

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
    ! [X1: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X1 ) ) ),
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
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( l1_orders_2 @ X15 )
      | ~ ( v5_orders_2 @ X15 )
      | ~ ( v4_orders_2 @ X15 )
      | ~ ( v3_orders_2 @ X15 )
      | ( v2_struct_0 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X15 ) )
      | ( m1_subset_1 @ ( k3_orders_2 @ X15 @ X14 @ X16 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) ) ) ),
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
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( m1_subset_1 @ X2 @ X4 ) ) ),
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
    ! [X13: $i] :
      ( ( ( k1_struct_0 @ X13 )
        = k1_xboole_0 )
      | ~ ( l1_struct_0 @ X13 ) ) ),
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
    ! [X17: $i] :
      ( ( l1_struct_0 @ X17 )
      | ~ ( l1_orders_2 @ X17 ) ) ),
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
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t6_mcart_1])).

thf('25',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X1 ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X19 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( r2_hidden @ X18 @ ( k3_orders_2 @ X19 @ X20 @ X21 ) )
      | ( r2_hidden @ X18 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X19 ) )
      | ~ ( l1_orders_2 @ X19 )
      | ~ ( v5_orders_2 @ X19 )
      | ~ ( v4_orders_2 @ X19 )
      | ~ ( v3_orders_2 @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
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

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('40',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('41',plain,(
    ~ ( r1_tarski @ k1_xboole_0 @ ( sk_B @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('42',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('43',plain,(
    $false ),
    inference(demod,[status(thm)],['41','42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.15/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8Ucu3aK0CZ
% 0.15/0.37  % Computer   : n012.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 14:22:37 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.15/0.37  % Running portfolio for 600 s
% 0.15/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.37  % Number of cores: 8
% 0.15/0.37  % Python version: Python 3.6.8
% 0.15/0.37  % Running in FO mode
% 0.41/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.41/0.57  % Solved by: fo/fo7.sh
% 0.41/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.57  % done 114 iterations in 0.092s
% 0.41/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.41/0.57  % SZS output start Refutation
% 0.41/0.57  thf(k1_struct_0_type, type, k1_struct_0: $i > $i).
% 0.41/0.57  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.41/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.41/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.41/0.57  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.41/0.57  thf(r2_orders_2_type, type, r2_orders_2: $i > $i > $i > $o).
% 0.41/0.57  thf(sk_B_type, type, sk_B: $i > $i).
% 0.41/0.57  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.41/0.57  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.41/0.57  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.41/0.57  thf(k3_orders_2_type, type, k3_orders_2: $i > $i > $i > $i).
% 0.41/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.41/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.41/0.57  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.41/0.57  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.41/0.57  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.41/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.41/0.57  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.41/0.57  thf(t6_mcart_1, axiom,
% 0.41/0.57    (![A:$i]:
% 0.41/0.57     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.41/0.57          ( ![B:$i]:
% 0.41/0.57            ( ~( ( r2_hidden @ B @ A ) & 
% 0.41/0.57                 ( ![C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.41/0.57                   ( ( ( r2_hidden @ C @ D ) & ( r2_hidden @ D @ E ) & 
% 0.41/0.57                       ( r2_hidden @ E @ F ) & ( r2_hidden @ F @ G ) & 
% 0.41/0.57                       ( r2_hidden @ G @ B ) ) =>
% 0.41/0.57                     ( r1_xboole_0 @ C @ A ) ) ) ) ) ) ) ))).
% 0.41/0.57  thf('0', plain,
% 0.41/0.57      (![X7 : $i]: (((X7) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X7) @ X7))),
% 0.41/0.57      inference('cnf', [status(esa)], [t6_mcart_1])).
% 0.41/0.57  thf(t60_orders_2, conjecture,
% 0.41/0.57    (![A:$i]:
% 0.41/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.41/0.57         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.41/0.57       ( ![B:$i]:
% 0.41/0.57         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.41/0.57           ( ( k3_orders_2 @ A @ ( k1_struct_0 @ A ) @ B ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.41/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.57    (~( ![A:$i]:
% 0.41/0.57        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.41/0.57            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.41/0.57          ( ![B:$i]:
% 0.41/0.57            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.41/0.57              ( ( k3_orders_2 @ A @ ( k1_struct_0 @ A ) @ B ) = ( k1_xboole_0 ) ) ) ) ) )),
% 0.41/0.57    inference('cnf.neg', [status(esa)], [t60_orders_2])).
% 0.41/0.57  thf('1', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.41/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.57  thf(t4_subset_1, axiom,
% 0.41/0.57    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.41/0.57  thf('2', plain,
% 0.41/0.57      (![X1 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X1))),
% 0.41/0.57      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.41/0.57  thf(dt_k3_orders_2, axiom,
% 0.41/0.57    (![A:$i,B:$i,C:$i]:
% 0.41/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.41/0.57         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 0.41/0.57         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.41/0.57         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.57       ( m1_subset_1 @
% 0.41/0.57         ( k3_orders_2 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.41/0.57  thf('3', plain,
% 0.41/0.57      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.41/0.57         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.41/0.57          | ~ (l1_orders_2 @ X15)
% 0.41/0.57          | ~ (v5_orders_2 @ X15)
% 0.41/0.57          | ~ (v4_orders_2 @ X15)
% 0.41/0.57          | ~ (v3_orders_2 @ X15)
% 0.41/0.57          | (v2_struct_0 @ X15)
% 0.41/0.57          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X15))
% 0.41/0.57          | (m1_subset_1 @ (k3_orders_2 @ X15 @ X14 @ X16) @ 
% 0.41/0.57             (k1_zfmisc_1 @ (u1_struct_0 @ X15))))),
% 0.41/0.57      inference('cnf', [status(esa)], [dt_k3_orders_2])).
% 0.41/0.57  thf('4', plain,
% 0.41/0.57      (![X0 : $i, X1 : $i]:
% 0.41/0.57         ((m1_subset_1 @ (k3_orders_2 @ X0 @ k1_xboole_0 @ X1) @ 
% 0.41/0.57           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.41/0.57          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.41/0.57          | (v2_struct_0 @ X0)
% 0.41/0.57          | ~ (v3_orders_2 @ X0)
% 0.41/0.57          | ~ (v4_orders_2 @ X0)
% 0.41/0.57          | ~ (v5_orders_2 @ X0)
% 0.41/0.57          | ~ (l1_orders_2 @ X0))),
% 0.41/0.57      inference('sup-', [status(thm)], ['2', '3'])).
% 0.41/0.57  thf('5', plain,
% 0.41/0.57      ((~ (l1_orders_2 @ sk_A)
% 0.41/0.57        | ~ (v5_orders_2 @ sk_A)
% 0.41/0.57        | ~ (v4_orders_2 @ sk_A)
% 0.41/0.57        | ~ (v3_orders_2 @ sk_A)
% 0.41/0.57        | (v2_struct_0 @ sk_A)
% 0.41/0.57        | (m1_subset_1 @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1) @ 
% 0.41/0.57           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.41/0.57      inference('sup-', [status(thm)], ['1', '4'])).
% 0.41/0.57  thf('6', plain, ((l1_orders_2 @ sk_A)),
% 0.41/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.57  thf('7', plain, ((v5_orders_2 @ sk_A)),
% 0.41/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.57  thf('8', plain, ((v4_orders_2 @ sk_A)),
% 0.41/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.57  thf('9', plain, ((v3_orders_2 @ sk_A)),
% 0.41/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.57  thf('10', plain,
% 0.41/0.57      (((v2_struct_0 @ sk_A)
% 0.41/0.57        | (m1_subset_1 @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1) @ 
% 0.41/0.57           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.41/0.57      inference('demod', [status(thm)], ['5', '6', '7', '8', '9'])).
% 0.41/0.57  thf('11', plain, (~ (v2_struct_0 @ sk_A)),
% 0.41/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.57  thf('12', plain,
% 0.41/0.57      ((m1_subset_1 @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1) @ 
% 0.41/0.57        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.57      inference('clc', [status(thm)], ['10', '11'])).
% 0.41/0.57  thf(t4_subset, axiom,
% 0.41/0.57    (![A:$i,B:$i,C:$i]:
% 0.41/0.57     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.41/0.57       ( m1_subset_1 @ A @ C ) ))).
% 0.41/0.57  thf('13', plain,
% 0.41/0.57      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.41/0.57         (~ (r2_hidden @ X2 @ X3)
% 0.41/0.57          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.41/0.57          | (m1_subset_1 @ X2 @ X4))),
% 0.41/0.57      inference('cnf', [status(esa)], [t4_subset])).
% 0.41/0.57  thf('14', plain,
% 0.41/0.57      (![X0 : $i]:
% 0.41/0.57         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.41/0.57          | ~ (r2_hidden @ X0 @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1)))),
% 0.41/0.57      inference('sup-', [status(thm)], ['12', '13'])).
% 0.41/0.57  thf('15', plain,
% 0.41/0.57      ((((k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1) = (k1_xboole_0))
% 0.41/0.57        | (m1_subset_1 @ 
% 0.41/0.57           (sk_B @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1)) @ 
% 0.41/0.57           (u1_struct_0 @ sk_A)))),
% 0.41/0.57      inference('sup-', [status(thm)], ['0', '14'])).
% 0.41/0.57  thf(d2_struct_0, axiom,
% 0.41/0.57    (![A:$i]:
% 0.41/0.57     ( ( l1_struct_0 @ A ) => ( ( k1_struct_0 @ A ) = ( k1_xboole_0 ) ) ))).
% 0.41/0.57  thf('16', plain,
% 0.41/0.57      (![X13 : $i]:
% 0.41/0.57         (((k1_struct_0 @ X13) = (k1_xboole_0)) | ~ (l1_struct_0 @ X13))),
% 0.41/0.57      inference('cnf', [status(esa)], [d2_struct_0])).
% 0.41/0.57  thf('17', plain,
% 0.41/0.57      (((k3_orders_2 @ sk_A @ (k1_struct_0 @ sk_A) @ sk_B_1) != (k1_xboole_0))),
% 0.41/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.57  thf('18', plain,
% 0.41/0.57      ((((k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1) != (k1_xboole_0))
% 0.41/0.57        | ~ (l1_struct_0 @ sk_A))),
% 0.41/0.57      inference('sup-', [status(thm)], ['16', '17'])).
% 0.41/0.57  thf('19', plain, ((l1_orders_2 @ sk_A)),
% 0.41/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.57  thf(dt_l1_orders_2, axiom,
% 0.41/0.57    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 0.41/0.57  thf('20', plain,
% 0.41/0.57      (![X17 : $i]: ((l1_struct_0 @ X17) | ~ (l1_orders_2 @ X17))),
% 0.41/0.57      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 0.41/0.58  thf('21', plain, ((l1_struct_0 @ sk_A)),
% 0.41/0.58      inference('sup-', [status(thm)], ['19', '20'])).
% 0.41/0.58  thf('22', plain,
% 0.41/0.58      (((k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1) != (k1_xboole_0))),
% 0.41/0.58      inference('demod', [status(thm)], ['18', '21'])).
% 0.41/0.58  thf('23', plain,
% 0.41/0.58      ((m1_subset_1 @ (sk_B @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1)) @ 
% 0.41/0.58        (u1_struct_0 @ sk_A))),
% 0.41/0.58      inference('simplify_reflect-', [status(thm)], ['15', '22'])).
% 0.41/0.58  thf('24', plain,
% 0.41/0.58      (![X7 : $i]: (((X7) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X7) @ X7))),
% 0.41/0.58      inference('cnf', [status(esa)], [t6_mcart_1])).
% 0.41/0.58  thf('25', plain,
% 0.41/0.58      (![X1 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X1))),
% 0.41/0.58      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.41/0.58  thf(t57_orders_2, axiom,
% 0.41/0.58    (![A:$i]:
% 0.41/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.41/0.58         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.41/0.58       ( ![B:$i]:
% 0.41/0.58         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.41/0.58           ( ![C:$i]:
% 0.41/0.58             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.41/0.58               ( ![D:$i]:
% 0.41/0.58                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.58                   ( ( r2_hidden @ B @ ( k3_orders_2 @ A @ D @ C ) ) <=>
% 0.41/0.58                     ( ( r2_orders_2 @ A @ B @ C ) & ( r2_hidden @ B @ D ) ) ) ) ) ) ) ) ) ))).
% 0.41/0.58  thf('26', plain,
% 0.41/0.58      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.41/0.58         (~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X19))
% 0.41/0.58          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.41/0.58          | ~ (r2_hidden @ X18 @ (k3_orders_2 @ X19 @ X20 @ X21))
% 0.41/0.58          | (r2_hidden @ X18 @ X20)
% 0.41/0.58          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X19))
% 0.41/0.58          | ~ (l1_orders_2 @ X19)
% 0.41/0.58          | ~ (v5_orders_2 @ X19)
% 0.41/0.58          | ~ (v4_orders_2 @ X19)
% 0.41/0.58          | ~ (v3_orders_2 @ X19)
% 0.41/0.58          | (v2_struct_0 @ X19))),
% 0.41/0.58      inference('cnf', [status(esa)], [t57_orders_2])).
% 0.41/0.58  thf('27', plain,
% 0.41/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.58         ((v2_struct_0 @ X0)
% 0.41/0.58          | ~ (v3_orders_2 @ X0)
% 0.41/0.58          | ~ (v4_orders_2 @ X0)
% 0.41/0.58          | ~ (v5_orders_2 @ X0)
% 0.41/0.58          | ~ (l1_orders_2 @ X0)
% 0.41/0.58          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.41/0.58          | (r2_hidden @ X2 @ k1_xboole_0)
% 0.41/0.58          | ~ (r2_hidden @ X2 @ (k3_orders_2 @ X0 @ k1_xboole_0 @ X1))
% 0.41/0.58          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0)))),
% 0.41/0.58      inference('sup-', [status(thm)], ['25', '26'])).
% 0.41/0.58  thf('28', plain,
% 0.41/0.58      (![X0 : $i, X1 : $i]:
% 0.41/0.58         (((k3_orders_2 @ X1 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 0.41/0.58          | ~ (m1_subset_1 @ (sk_B @ (k3_orders_2 @ X1 @ k1_xboole_0 @ X0)) @ 
% 0.41/0.58               (u1_struct_0 @ X1))
% 0.41/0.58          | (r2_hidden @ (sk_B @ (k3_orders_2 @ X1 @ k1_xboole_0 @ X0)) @ 
% 0.41/0.58             k1_xboole_0)
% 0.41/0.58          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 0.41/0.58          | ~ (l1_orders_2 @ X1)
% 0.41/0.58          | ~ (v5_orders_2 @ X1)
% 0.41/0.58          | ~ (v4_orders_2 @ X1)
% 0.41/0.58          | ~ (v3_orders_2 @ X1)
% 0.41/0.58          | (v2_struct_0 @ X1))),
% 0.41/0.58      inference('sup-', [status(thm)], ['24', '27'])).
% 0.41/0.58  thf('29', plain,
% 0.41/0.58      (((v2_struct_0 @ sk_A)
% 0.41/0.58        | ~ (v3_orders_2 @ sk_A)
% 0.41/0.58        | ~ (v4_orders_2 @ sk_A)
% 0.41/0.58        | ~ (v5_orders_2 @ sk_A)
% 0.41/0.58        | ~ (l1_orders_2 @ sk_A)
% 0.41/0.58        | ~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.41/0.58        | (r2_hidden @ (sk_B @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1)) @ 
% 0.41/0.58           k1_xboole_0)
% 0.41/0.58        | ((k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1) = (k1_xboole_0)))),
% 0.41/0.58      inference('sup-', [status(thm)], ['23', '28'])).
% 0.41/0.58  thf('30', plain, ((v3_orders_2 @ sk_A)),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf('31', plain, ((v4_orders_2 @ sk_A)),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf('32', plain, ((v5_orders_2 @ sk_A)),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf('33', plain, ((l1_orders_2 @ sk_A)),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf('34', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf('35', plain,
% 0.41/0.58      (((v2_struct_0 @ sk_A)
% 0.41/0.58        | (r2_hidden @ (sk_B @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1)) @ 
% 0.41/0.58           k1_xboole_0)
% 0.41/0.58        | ((k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1) = (k1_xboole_0)))),
% 0.41/0.58      inference('demod', [status(thm)], ['29', '30', '31', '32', '33', '34'])).
% 0.41/0.58  thf('36', plain,
% 0.41/0.58      (((k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1) != (k1_xboole_0))),
% 0.41/0.58      inference('demod', [status(thm)], ['18', '21'])).
% 0.41/0.58  thf('37', plain,
% 0.41/0.58      (((v2_struct_0 @ sk_A)
% 0.41/0.58        | (r2_hidden @ (sk_B @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1)) @ 
% 0.41/0.58           k1_xboole_0))),
% 0.41/0.58      inference('simplify_reflect-', [status(thm)], ['35', '36'])).
% 0.41/0.58  thf('38', plain, (~ (v2_struct_0 @ sk_A)),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf('39', plain,
% 0.41/0.58      ((r2_hidden @ (sk_B @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1)) @ 
% 0.41/0.58        k1_xboole_0)),
% 0.41/0.58      inference('clc', [status(thm)], ['37', '38'])).
% 0.41/0.58  thf(t7_ordinal1, axiom,
% 0.41/0.58    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.41/0.58  thf('40', plain,
% 0.41/0.58      (![X5 : $i, X6 : $i]: (~ (r2_hidden @ X5 @ X6) | ~ (r1_tarski @ X6 @ X5))),
% 0.41/0.58      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.41/0.58  thf('41', plain,
% 0.41/0.58      (~ (r1_tarski @ k1_xboole_0 @ 
% 0.41/0.58          (sk_B @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1)))),
% 0.41/0.58      inference('sup-', [status(thm)], ['39', '40'])).
% 0.41/0.58  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.41/0.58  thf('42', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.41/0.58      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.41/0.58  thf('43', plain, ($false), inference('demod', [status(thm)], ['41', '42'])).
% 0.41/0.58  
% 0.41/0.58  % SZS output end Refutation
% 0.41/0.58  
% 0.41/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
