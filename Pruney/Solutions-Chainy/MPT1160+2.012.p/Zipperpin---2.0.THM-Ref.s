%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BkiiqW8Vcj

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:01 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 117 expanded)
%              Number of leaves         :   29 (  49 expanded)
%              Depth                    :   14
%              Number of atoms          :  557 (1258 expanded)
%              Number of equality atoms :   15 (  50 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_struct_0_type,type,(
    k1_struct_0: $i > $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r2_orders_2_type,type,(
    r2_orders_2: $i > $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(k3_orders_2_type,type,(
    k3_orders_2: $i > $i > $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('0',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

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

thf('1',plain,(
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

thf('2',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('3',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
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

thf('4',plain,(
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

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_orders_2 @ X0 @ k1_xboole_0 @ X1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['6','7','8','9','10'])).

thf('12',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    m1_subset_1 @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['11','12'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('14',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) )
      | ( m1_subset_1 @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1 )
      = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_B @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','15'])).

thf(d2_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k1_struct_0 @ A )
        = k1_xboole_0 ) ) )).

thf('17',plain,(
    ! [X13: $i] :
      ( ( ( k1_struct_0 @ X13 )
        = k1_xboole_0 )
      | ~ ( l1_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d2_struct_0])).

thf('18',plain,(
    ( k3_orders_2 @ sk_A @ ( k1_struct_0 @ sk_A ) @ sk_B_1 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1 )
     != k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('21',plain,(
    ! [X17: $i] :
      ( ( l1_struct_0 @ X17 )
      | ~ ( l1_orders_2 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf('22',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1 )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['19','22'])).

thf('24',plain,(
    m1_subset_1 @ ( sk_B @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['16','23'])).

thf('25',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t6_mcart_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
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

thf('27',plain,(
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

thf('28',plain,(
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
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
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
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_B @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1 ) ) @ k1_xboole_0 )
    | ( ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','29'])).

thf('31',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_B @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1 ) ) @ k1_xboole_0 )
    | ( ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['30','31','32','33','34','35'])).

thf('37',plain,(
    ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1 )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['19','22'])).

thf('38',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_B @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1 ) ) @ k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['36','37'])).

thf('39',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    r2_hidden @ ( sk_B @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1 ) ) @ k1_xboole_0 ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('42',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( v1_xboole_0 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,(
    $false ),
    inference('sup-',[status(thm)],['0','44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BkiiqW8Vcj
% 0.13/0.35  % Computer   : n021.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:59:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.20/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.53  % Solved by: fo/fo7.sh
% 0.20/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.53  % done 115 iterations in 0.073s
% 0.20/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.53  % SZS output start Refutation
% 0.20/0.53  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.53  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.53  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.20/0.53  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.53  thf(k1_struct_0_type, type, k1_struct_0: $i > $i).
% 0.20/0.53  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.20/0.53  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.53  thf(r2_orders_2_type, type, r2_orders_2: $i > $i > $i > $o).
% 0.20/0.53  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.53  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.20/0.53  thf(k3_orders_2_type, type, k3_orders_2: $i > $i > $i > $i).
% 0.20/0.53  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.20/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.53  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.20/0.53  thf('0', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.53      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.53  thf(t6_mcart_1, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.53          ( ![B:$i]:
% 0.20/0.53            ( ~( ( r2_hidden @ B @ A ) & 
% 0.20/0.53                 ( ![C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.20/0.53                   ( ( ( r2_hidden @ C @ D ) & ( r2_hidden @ D @ E ) & 
% 0.20/0.53                       ( r2_hidden @ E @ F ) & ( r2_hidden @ F @ G ) & 
% 0.20/0.53                       ( r2_hidden @ G @ B ) ) =>
% 0.20/0.53                     ( r1_xboole_0 @ C @ A ) ) ) ) ) ) ) ))).
% 0.20/0.53  thf('1', plain,
% 0.20/0.53      (![X7 : $i]: (((X7) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X7) @ X7))),
% 0.20/0.53      inference('cnf', [status(esa)], [t6_mcart_1])).
% 0.20/0.53  thf(t60_orders_2, conjecture,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.53         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.53           ( ( k3_orders_2 @ A @ ( k1_struct_0 @ A ) @ B ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.20/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.53    (~( ![A:$i]:
% 0.20/0.53        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.53            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.53          ( ![B:$i]:
% 0.20/0.53            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.53              ( ( k3_orders_2 @ A @ ( k1_struct_0 @ A ) @ B ) = ( k1_xboole_0 ) ) ) ) ) )),
% 0.20/0.53    inference('cnf.neg', [status(esa)], [t60_orders_2])).
% 0.20/0.53  thf('2', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(t4_subset_1, axiom,
% 0.20/0.53    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.20/0.53  thf('3', plain,
% 0.20/0.53      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.20/0.53      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.20/0.53  thf(dt_k3_orders_2, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.53         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 0.20/0.53         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.20/0.53         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.53       ( m1_subset_1 @
% 0.20/0.53         ( k3_orders_2 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.20/0.53  thf('4', plain,
% 0.20/0.53      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.20/0.53          | ~ (l1_orders_2 @ X15)
% 0.20/0.53          | ~ (v5_orders_2 @ X15)
% 0.20/0.53          | ~ (v4_orders_2 @ X15)
% 0.20/0.53          | ~ (v3_orders_2 @ X15)
% 0.20/0.53          | (v2_struct_0 @ X15)
% 0.20/0.53          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X15))
% 0.20/0.53          | (m1_subset_1 @ (k3_orders_2 @ X15 @ X14 @ X16) @ 
% 0.20/0.53             (k1_zfmisc_1 @ (u1_struct_0 @ X15))))),
% 0.20/0.53      inference('cnf', [status(esa)], [dt_k3_orders_2])).
% 0.20/0.53  thf('5', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((m1_subset_1 @ (k3_orders_2 @ X0 @ k1_xboole_0 @ X1) @ 
% 0.20/0.53           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.53          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.20/0.53          | (v2_struct_0 @ X0)
% 0.20/0.53          | ~ (v3_orders_2 @ X0)
% 0.20/0.53          | ~ (v4_orders_2 @ X0)
% 0.20/0.53          | ~ (v5_orders_2 @ X0)
% 0.20/0.53          | ~ (l1_orders_2 @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.53  thf('6', plain,
% 0.20/0.53      ((~ (l1_orders_2 @ sk_A)
% 0.20/0.53        | ~ (v5_orders_2 @ sk_A)
% 0.20/0.53        | ~ (v4_orders_2 @ sk_A)
% 0.20/0.53        | ~ (v3_orders_2 @ sk_A)
% 0.20/0.53        | (v2_struct_0 @ sk_A)
% 0.20/0.53        | (m1_subset_1 @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1) @ 
% 0.20/0.53           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['2', '5'])).
% 0.20/0.53  thf('7', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('8', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('9', plain, ((v4_orders_2 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('10', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('11', plain,
% 0.20/0.53      (((v2_struct_0 @ sk_A)
% 0.20/0.53        | (m1_subset_1 @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1) @ 
% 0.20/0.53           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.53      inference('demod', [status(thm)], ['6', '7', '8', '9', '10'])).
% 0.20/0.53  thf('12', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('13', plain,
% 0.20/0.53      ((m1_subset_1 @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1) @ 
% 0.20/0.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('clc', [status(thm)], ['11', '12'])).
% 0.20/0.53  thf(t4_subset, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.20/0.53       ( m1_subset_1 @ A @ C ) ))).
% 0.20/0.53  thf('14', plain,
% 0.20/0.53      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X1 @ X2)
% 0.20/0.53          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3))
% 0.20/0.53          | (m1_subset_1 @ X1 @ X3))),
% 0.20/0.53      inference('cnf', [status(esa)], [t4_subset])).
% 0.20/0.53  thf('15', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.53          | ~ (r2_hidden @ X0 @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.53  thf('16', plain,
% 0.20/0.53      ((((k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1) = (k1_xboole_0))
% 0.20/0.53        | (m1_subset_1 @ 
% 0.20/0.53           (sk_B @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1)) @ 
% 0.20/0.53           (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['1', '15'])).
% 0.20/0.53  thf(d2_struct_0, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( l1_struct_0 @ A ) => ( ( k1_struct_0 @ A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.53  thf('17', plain,
% 0.20/0.53      (![X13 : $i]:
% 0.20/0.53         (((k1_struct_0 @ X13) = (k1_xboole_0)) | ~ (l1_struct_0 @ X13))),
% 0.20/0.53      inference('cnf', [status(esa)], [d2_struct_0])).
% 0.20/0.53  thf('18', plain,
% 0.20/0.53      (((k3_orders_2 @ sk_A @ (k1_struct_0 @ sk_A) @ sk_B_1) != (k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('19', plain,
% 0.20/0.53      ((((k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1) != (k1_xboole_0))
% 0.20/0.53        | ~ (l1_struct_0 @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.53  thf('20', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(dt_l1_orders_2, axiom,
% 0.20/0.53    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 0.20/0.53  thf('21', plain,
% 0.20/0.53      (![X17 : $i]: ((l1_struct_0 @ X17) | ~ (l1_orders_2 @ X17))),
% 0.20/0.53      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 0.20/0.53  thf('22', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.53      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.53  thf('23', plain,
% 0.20/0.53      (((k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1) != (k1_xboole_0))),
% 0.20/0.53      inference('demod', [status(thm)], ['19', '22'])).
% 0.20/0.53  thf('24', plain,
% 0.20/0.53      ((m1_subset_1 @ (sk_B @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1)) @ 
% 0.20/0.53        (u1_struct_0 @ sk_A))),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['16', '23'])).
% 0.20/0.53  thf('25', plain,
% 0.20/0.53      (![X7 : $i]: (((X7) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X7) @ X7))),
% 0.20/0.53      inference('cnf', [status(esa)], [t6_mcart_1])).
% 0.20/0.53  thf('26', plain,
% 0.20/0.53      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.20/0.53      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.20/0.53  thf(t57_orders_2, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.53         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.53           ( ![C:$i]:
% 0.20/0.53             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.53               ( ![D:$i]:
% 0.20/0.53                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.53                   ( ( r2_hidden @ B @ ( k3_orders_2 @ A @ D @ C ) ) <=>
% 0.20/0.53                     ( ( r2_orders_2 @ A @ B @ C ) & ( r2_hidden @ B @ D ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.53  thf('27', plain,
% 0.20/0.53      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X19))
% 0.20/0.53          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.20/0.53          | ~ (r2_hidden @ X18 @ (k3_orders_2 @ X19 @ X20 @ X21))
% 0.20/0.53          | (r2_hidden @ X18 @ X20)
% 0.20/0.53          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X19))
% 0.20/0.53          | ~ (l1_orders_2 @ X19)
% 0.20/0.53          | ~ (v5_orders_2 @ X19)
% 0.20/0.53          | ~ (v4_orders_2 @ X19)
% 0.20/0.53          | ~ (v3_orders_2 @ X19)
% 0.20/0.53          | (v2_struct_0 @ X19))),
% 0.20/0.53      inference('cnf', [status(esa)], [t57_orders_2])).
% 0.20/0.53  thf('28', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.53         ((v2_struct_0 @ X0)
% 0.20/0.53          | ~ (v3_orders_2 @ X0)
% 0.20/0.53          | ~ (v4_orders_2 @ X0)
% 0.20/0.53          | ~ (v5_orders_2 @ X0)
% 0.20/0.53          | ~ (l1_orders_2 @ X0)
% 0.20/0.53          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.20/0.53          | (r2_hidden @ X2 @ k1_xboole_0)
% 0.20/0.53          | ~ (r2_hidden @ X2 @ (k3_orders_2 @ X0 @ k1_xboole_0 @ X1))
% 0.20/0.53          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.53  thf('29', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (((k3_orders_2 @ X1 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 0.20/0.53          | ~ (m1_subset_1 @ (sk_B @ (k3_orders_2 @ X1 @ k1_xboole_0 @ X0)) @ 
% 0.20/0.53               (u1_struct_0 @ X1))
% 0.20/0.53          | (r2_hidden @ (sk_B @ (k3_orders_2 @ X1 @ k1_xboole_0 @ X0)) @ 
% 0.20/0.53             k1_xboole_0)
% 0.20/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 0.20/0.53          | ~ (l1_orders_2 @ X1)
% 0.20/0.53          | ~ (v5_orders_2 @ X1)
% 0.20/0.53          | ~ (v4_orders_2 @ X1)
% 0.20/0.53          | ~ (v3_orders_2 @ X1)
% 0.20/0.53          | (v2_struct_0 @ X1))),
% 0.20/0.53      inference('sup-', [status(thm)], ['25', '28'])).
% 0.20/0.53  thf('30', plain,
% 0.20/0.53      (((v2_struct_0 @ sk_A)
% 0.20/0.53        | ~ (v3_orders_2 @ sk_A)
% 0.20/0.53        | ~ (v4_orders_2 @ sk_A)
% 0.20/0.53        | ~ (v5_orders_2 @ sk_A)
% 0.20/0.53        | ~ (l1_orders_2 @ sk_A)
% 0.20/0.53        | ~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.20/0.53        | (r2_hidden @ (sk_B @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1)) @ 
% 0.20/0.53           k1_xboole_0)
% 0.20/0.53        | ((k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1) = (k1_xboole_0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['24', '29'])).
% 0.20/0.53  thf('31', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('32', plain, ((v4_orders_2 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('33', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('34', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('35', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('36', plain,
% 0.20/0.53      (((v2_struct_0 @ sk_A)
% 0.20/0.53        | (r2_hidden @ (sk_B @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1)) @ 
% 0.20/0.53           k1_xboole_0)
% 0.20/0.53        | ((k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1) = (k1_xboole_0)))),
% 0.20/0.53      inference('demod', [status(thm)], ['30', '31', '32', '33', '34', '35'])).
% 0.20/0.53  thf('37', plain,
% 0.20/0.53      (((k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1) != (k1_xboole_0))),
% 0.20/0.53      inference('demod', [status(thm)], ['19', '22'])).
% 0.20/0.53  thf('38', plain,
% 0.20/0.53      (((v2_struct_0 @ sk_A)
% 0.20/0.53        | (r2_hidden @ (sk_B @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1)) @ 
% 0.20/0.53           k1_xboole_0))),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['36', '37'])).
% 0.20/0.53  thf('39', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('40', plain,
% 0.20/0.53      ((r2_hidden @ (sk_B @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1)) @ 
% 0.20/0.53        k1_xboole_0)),
% 0.20/0.53      inference('clc', [status(thm)], ['38', '39'])).
% 0.20/0.53  thf('41', plain,
% 0.20/0.53      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.20/0.53      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.20/0.53  thf(t5_subset, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.20/0.53          ( v1_xboole_0 @ C ) ) ))).
% 0.20/0.53  thf('42', plain,
% 0.20/0.53      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X4 @ X5)
% 0.20/0.53          | ~ (v1_xboole_0 @ X6)
% 0.20/0.53          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t5_subset])).
% 0.20/0.53  thf('43', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['41', '42'])).
% 0.20/0.53  thf('44', plain, (![X0 : $i]: ~ (v1_xboole_0 @ X0)),
% 0.20/0.53      inference('sup-', [status(thm)], ['40', '43'])).
% 0.20/0.53  thf('45', plain, ($false), inference('sup-', [status(thm)], ['0', '44'])).
% 0.20/0.53  
% 0.20/0.53  % SZS output end Refutation
% 0.20/0.53  
% 0.20/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
