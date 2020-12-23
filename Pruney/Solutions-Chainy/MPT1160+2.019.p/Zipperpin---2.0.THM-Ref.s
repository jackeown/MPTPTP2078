%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ckVase1VzC

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:02 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 114 expanded)
%              Number of leaves         :   29 (  48 expanded)
%              Depth                    :   14
%              Number of atoms          :  544 (1236 expanded)
%              Number of equality atoms :   16 (  52 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_struct_0_type,type,(
    k1_struct_0: $i > $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_mcart_1_type,type,(
    k4_mcart_1: $i > $i > $i > $i > $i )).

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

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t34_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i,F: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k4_mcart_1 @ C @ D @ E @ F ) ) ) ) ) )).

thf('0',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t34_mcart_1])).

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
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t34_mcart_1])).

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
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ckVase1VzC
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:55:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.35/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.35/0.53  % Solved by: fo/fo7.sh
% 0.35/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.53  % done 95 iterations in 0.069s
% 0.35/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.35/0.53  % SZS output start Refutation
% 0.35/0.53  thf(k1_struct_0_type, type, k1_struct_0: $i > $i).
% 0.35/0.53  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.35/0.53  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.35/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.35/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.35/0.53  thf(k4_mcart_1_type, type, k4_mcart_1: $i > $i > $i > $i > $i).
% 0.35/0.53  thf(r2_orders_2_type, type, r2_orders_2: $i > $i > $i > $o).
% 0.35/0.53  thf(sk_B_type, type, sk_B: $i > $i).
% 0.35/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.35/0.53  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.35/0.53  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.35/0.53  thf(k3_orders_2_type, type, k3_orders_2: $i > $i > $i > $i).
% 0.35/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.35/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.35/0.53  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.35/0.53  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.35/0.53  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.35/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.35/0.53  thf(t34_mcart_1, axiom,
% 0.35/0.53    (![A:$i]:
% 0.35/0.53     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.35/0.53          ( ![B:$i]:
% 0.35/0.53            ( ~( ( r2_hidden @ B @ A ) & 
% 0.35/0.53                 ( ![C:$i,D:$i,E:$i,F:$i]:
% 0.35/0.53                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.35/0.53                        ( ( B ) = ( k4_mcart_1 @ C @ D @ E @ F ) ) ) ) ) ) ) ) ) ))).
% 0.35/0.53  thf('0', plain,
% 0.35/0.53      (![X7 : $i]: (((X7) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X7) @ X7))),
% 0.35/0.53      inference('cnf', [status(esa)], [t34_mcart_1])).
% 0.35/0.53  thf(t60_orders_2, conjecture,
% 0.35/0.53    (![A:$i]:
% 0.35/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.35/0.53         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.35/0.53       ( ![B:$i]:
% 0.35/0.53         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.35/0.53           ( ( k3_orders_2 @ A @ ( k1_struct_0 @ A ) @ B ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.35/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.53    (~( ![A:$i]:
% 0.35/0.53        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.35/0.53            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.35/0.53          ( ![B:$i]:
% 0.35/0.53            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.35/0.53              ( ( k3_orders_2 @ A @ ( k1_struct_0 @ A ) @ B ) = ( k1_xboole_0 ) ) ) ) ) )),
% 0.35/0.53    inference('cnf.neg', [status(esa)], [t60_orders_2])).
% 0.35/0.53  thf('1', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf(t4_subset_1, axiom,
% 0.35/0.53    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.35/0.53  thf('2', plain,
% 0.35/0.53      (![X1 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X1))),
% 0.35/0.53      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.35/0.53  thf(dt_k3_orders_2, axiom,
% 0.35/0.53    (![A:$i,B:$i,C:$i]:
% 0.35/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.35/0.53         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 0.35/0.53         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.35/0.53         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.53       ( m1_subset_1 @
% 0.35/0.53         ( k3_orders_2 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.35/0.53  thf('3', plain,
% 0.35/0.53      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.35/0.53         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.35/0.53          | ~ (l1_orders_2 @ X14)
% 0.35/0.53          | ~ (v5_orders_2 @ X14)
% 0.35/0.53          | ~ (v4_orders_2 @ X14)
% 0.35/0.53          | ~ (v3_orders_2 @ X14)
% 0.35/0.53          | (v2_struct_0 @ X14)
% 0.35/0.53          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X14))
% 0.35/0.53          | (m1_subset_1 @ (k3_orders_2 @ X14 @ X13 @ X15) @ 
% 0.35/0.53             (k1_zfmisc_1 @ (u1_struct_0 @ X14))))),
% 0.35/0.53      inference('cnf', [status(esa)], [dt_k3_orders_2])).
% 0.35/0.53  thf('4', plain,
% 0.35/0.53      (![X0 : $i, X1 : $i]:
% 0.35/0.53         ((m1_subset_1 @ (k3_orders_2 @ X0 @ k1_xboole_0 @ X1) @ 
% 0.35/0.53           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.35/0.53          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.35/0.53          | (v2_struct_0 @ X0)
% 0.35/0.53          | ~ (v3_orders_2 @ X0)
% 0.35/0.53          | ~ (v4_orders_2 @ X0)
% 0.35/0.53          | ~ (v5_orders_2 @ X0)
% 0.35/0.53          | ~ (l1_orders_2 @ X0))),
% 0.35/0.53      inference('sup-', [status(thm)], ['2', '3'])).
% 0.35/0.53  thf('5', plain,
% 0.35/0.53      ((~ (l1_orders_2 @ sk_A)
% 0.35/0.53        | ~ (v5_orders_2 @ sk_A)
% 0.35/0.53        | ~ (v4_orders_2 @ sk_A)
% 0.35/0.53        | ~ (v3_orders_2 @ sk_A)
% 0.35/0.53        | (v2_struct_0 @ sk_A)
% 0.35/0.53        | (m1_subset_1 @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1) @ 
% 0.35/0.53           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.35/0.53      inference('sup-', [status(thm)], ['1', '4'])).
% 0.35/0.53  thf('6', plain, ((l1_orders_2 @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('7', plain, ((v5_orders_2 @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('8', plain, ((v4_orders_2 @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('9', plain, ((v3_orders_2 @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('10', plain,
% 0.35/0.53      (((v2_struct_0 @ sk_A)
% 0.35/0.53        | (m1_subset_1 @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1) @ 
% 0.35/0.53           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.35/0.53      inference('demod', [status(thm)], ['5', '6', '7', '8', '9'])).
% 0.35/0.53  thf('11', plain, (~ (v2_struct_0 @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('12', plain,
% 0.35/0.53      ((m1_subset_1 @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1) @ 
% 0.35/0.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.53      inference('clc', [status(thm)], ['10', '11'])).
% 0.35/0.53  thf(t4_subset, axiom,
% 0.35/0.53    (![A:$i,B:$i,C:$i]:
% 0.35/0.53     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.35/0.53       ( m1_subset_1 @ A @ C ) ))).
% 0.35/0.53  thf('13', plain,
% 0.35/0.53      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.35/0.53         (~ (r2_hidden @ X2 @ X3)
% 0.35/0.53          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.35/0.53          | (m1_subset_1 @ X2 @ X4))),
% 0.35/0.53      inference('cnf', [status(esa)], [t4_subset])).
% 0.35/0.53  thf('14', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.35/0.53          | ~ (r2_hidden @ X0 @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['12', '13'])).
% 0.35/0.53  thf('15', plain,
% 0.35/0.53      ((((k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1) = (k1_xboole_0))
% 0.35/0.53        | (m1_subset_1 @ 
% 0.35/0.53           (sk_B @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1)) @ 
% 0.35/0.53           (u1_struct_0 @ sk_A)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['0', '14'])).
% 0.35/0.53  thf(d2_struct_0, axiom,
% 0.35/0.53    (![A:$i]:
% 0.35/0.53     ( ( l1_struct_0 @ A ) => ( ( k1_struct_0 @ A ) = ( k1_xboole_0 ) ) ))).
% 0.35/0.53  thf('16', plain,
% 0.35/0.53      (![X12 : $i]:
% 0.35/0.53         (((k1_struct_0 @ X12) = (k1_xboole_0)) | ~ (l1_struct_0 @ X12))),
% 0.35/0.53      inference('cnf', [status(esa)], [d2_struct_0])).
% 0.35/0.53  thf('17', plain,
% 0.35/0.53      (((k3_orders_2 @ sk_A @ (k1_struct_0 @ sk_A) @ sk_B_1) != (k1_xboole_0))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('18', plain,
% 0.35/0.53      ((((k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1) != (k1_xboole_0))
% 0.35/0.53        | ~ (l1_struct_0 @ sk_A))),
% 0.35/0.53      inference('sup-', [status(thm)], ['16', '17'])).
% 0.35/0.53  thf('19', plain, ((l1_orders_2 @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf(dt_l1_orders_2, axiom,
% 0.35/0.53    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 0.35/0.53  thf('20', plain,
% 0.35/0.53      (![X16 : $i]: ((l1_struct_0 @ X16) | ~ (l1_orders_2 @ X16))),
% 0.35/0.53      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 0.35/0.53  thf('21', plain, ((l1_struct_0 @ sk_A)),
% 0.35/0.53      inference('sup-', [status(thm)], ['19', '20'])).
% 0.35/0.53  thf('22', plain,
% 0.35/0.53      (((k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1) != (k1_xboole_0))),
% 0.35/0.53      inference('demod', [status(thm)], ['18', '21'])).
% 0.35/0.53  thf('23', plain,
% 0.35/0.53      ((m1_subset_1 @ (sk_B @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1)) @ 
% 0.35/0.53        (u1_struct_0 @ sk_A))),
% 0.35/0.53      inference('simplify_reflect-', [status(thm)], ['15', '22'])).
% 0.35/0.53  thf('24', plain,
% 0.35/0.53      (![X7 : $i]: (((X7) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X7) @ X7))),
% 0.35/0.53      inference('cnf', [status(esa)], [t34_mcart_1])).
% 0.35/0.53  thf('25', plain,
% 0.35/0.53      (![X1 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X1))),
% 0.35/0.53      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.35/0.53  thf(t57_orders_2, axiom,
% 0.35/0.53    (![A:$i]:
% 0.35/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.35/0.53         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.35/0.53       ( ![B:$i]:
% 0.35/0.53         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.35/0.53           ( ![C:$i]:
% 0.35/0.53             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.35/0.53               ( ![D:$i]:
% 0.35/0.53                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.53                   ( ( r2_hidden @ B @ ( k3_orders_2 @ A @ D @ C ) ) <=>
% 0.35/0.53                     ( ( r2_orders_2 @ A @ B @ C ) & ( r2_hidden @ B @ D ) ) ) ) ) ) ) ) ) ))).
% 0.35/0.53  thf('26', plain,
% 0.35/0.53      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.35/0.53         (~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X18))
% 0.35/0.53          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.35/0.53          | ~ (r2_hidden @ X17 @ (k3_orders_2 @ X18 @ X19 @ X20))
% 0.35/0.53          | (r2_hidden @ X17 @ X19)
% 0.35/0.53          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X18))
% 0.35/0.53          | ~ (l1_orders_2 @ X18)
% 0.35/0.53          | ~ (v5_orders_2 @ X18)
% 0.35/0.53          | ~ (v4_orders_2 @ X18)
% 0.35/0.53          | ~ (v3_orders_2 @ X18)
% 0.35/0.53          | (v2_struct_0 @ X18))),
% 0.35/0.53      inference('cnf', [status(esa)], [t57_orders_2])).
% 0.35/0.53  thf('27', plain,
% 0.35/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.35/0.53         ((v2_struct_0 @ X0)
% 0.35/0.53          | ~ (v3_orders_2 @ X0)
% 0.35/0.53          | ~ (v4_orders_2 @ X0)
% 0.35/0.53          | ~ (v5_orders_2 @ X0)
% 0.35/0.53          | ~ (l1_orders_2 @ X0)
% 0.35/0.53          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.35/0.53          | (r2_hidden @ X2 @ k1_xboole_0)
% 0.35/0.53          | ~ (r2_hidden @ X2 @ (k3_orders_2 @ X0 @ k1_xboole_0 @ X1))
% 0.35/0.53          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['25', '26'])).
% 0.35/0.53  thf('28', plain,
% 0.35/0.53      (![X0 : $i, X1 : $i]:
% 0.35/0.53         (((k3_orders_2 @ X1 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 0.35/0.53          | ~ (m1_subset_1 @ (sk_B @ (k3_orders_2 @ X1 @ k1_xboole_0 @ X0)) @ 
% 0.35/0.53               (u1_struct_0 @ X1))
% 0.35/0.53          | (r2_hidden @ (sk_B @ (k3_orders_2 @ X1 @ k1_xboole_0 @ X0)) @ 
% 0.35/0.53             k1_xboole_0)
% 0.35/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 0.35/0.53          | ~ (l1_orders_2 @ X1)
% 0.35/0.53          | ~ (v5_orders_2 @ X1)
% 0.35/0.53          | ~ (v4_orders_2 @ X1)
% 0.35/0.53          | ~ (v3_orders_2 @ X1)
% 0.35/0.53          | (v2_struct_0 @ X1))),
% 0.35/0.53      inference('sup-', [status(thm)], ['24', '27'])).
% 0.35/0.53  thf('29', plain,
% 0.35/0.53      (((v2_struct_0 @ sk_A)
% 0.35/0.53        | ~ (v3_orders_2 @ sk_A)
% 0.35/0.53        | ~ (v4_orders_2 @ sk_A)
% 0.35/0.53        | ~ (v5_orders_2 @ sk_A)
% 0.35/0.53        | ~ (l1_orders_2 @ sk_A)
% 0.35/0.53        | ~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.35/0.53        | (r2_hidden @ (sk_B @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1)) @ 
% 0.35/0.53           k1_xboole_0)
% 0.35/0.53        | ((k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1) = (k1_xboole_0)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['23', '28'])).
% 0.35/0.53  thf('30', plain, ((v3_orders_2 @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('31', plain, ((v4_orders_2 @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('32', plain, ((v5_orders_2 @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('33', plain, ((l1_orders_2 @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('34', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('35', plain,
% 0.35/0.53      (((v2_struct_0 @ sk_A)
% 0.35/0.53        | (r2_hidden @ (sk_B @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1)) @ 
% 0.35/0.53           k1_xboole_0)
% 0.35/0.53        | ((k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1) = (k1_xboole_0)))),
% 0.35/0.53      inference('demod', [status(thm)], ['29', '30', '31', '32', '33', '34'])).
% 0.35/0.53  thf('36', plain,
% 0.35/0.53      (((k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1) != (k1_xboole_0))),
% 0.35/0.53      inference('demod', [status(thm)], ['18', '21'])).
% 0.35/0.53  thf('37', plain,
% 0.35/0.53      (((v2_struct_0 @ sk_A)
% 0.35/0.53        | (r2_hidden @ (sk_B @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1)) @ 
% 0.35/0.53           k1_xboole_0))),
% 0.35/0.53      inference('simplify_reflect-', [status(thm)], ['35', '36'])).
% 0.35/0.53  thf('38', plain, (~ (v2_struct_0 @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('39', plain,
% 0.35/0.53      ((r2_hidden @ (sk_B @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1)) @ 
% 0.35/0.53        k1_xboole_0)),
% 0.35/0.53      inference('clc', [status(thm)], ['37', '38'])).
% 0.35/0.53  thf(t7_ordinal1, axiom,
% 0.35/0.53    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.35/0.53  thf('40', plain,
% 0.35/0.53      (![X5 : $i, X6 : $i]: (~ (r2_hidden @ X5 @ X6) | ~ (r1_tarski @ X6 @ X5))),
% 0.35/0.53      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.35/0.53  thf('41', plain,
% 0.35/0.53      (~ (r1_tarski @ k1_xboole_0 @ 
% 0.35/0.53          (sk_B @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['39', '40'])).
% 0.35/0.53  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.35/0.53  thf('42', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.35/0.53      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.35/0.53  thf('43', plain, ($false), inference('demod', [status(thm)], ['41', '42'])).
% 0.35/0.53  
% 0.35/0.53  % SZS output end Refutation
% 0.35/0.53  
% 0.37/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
