%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dqMmltrrJr

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:07 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 112 expanded)
%              Number of leaves         :   20 (  43 expanded)
%              Depth                    :   11
%              Number of atoms          :  418 (1751 expanded)
%              Number of equality atoms :   14 (  57 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_orders_2_type,type,(
    m1_orders_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t69_orders_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ~ ( ( B != k1_xboole_0 )
                  & ( m1_orders_2 @ B @ A @ C )
                  & ( m1_orders_2 @ C @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v3_orders_2 @ A )
          & ( v4_orders_2 @ A )
          & ( v5_orders_2 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ~ ( ( B != k1_xboole_0 )
                    & ( m1_orders_2 @ B @ A @ C )
                    & ( m1_orders_2 @ C @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t69_orders_2])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t68_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ~ ( ( B != k1_xboole_0 )
                & ( m1_orders_2 @ B @ A @ B ) )
            & ~ ( ~ ( m1_orders_2 @ B @ A @ B )
                & ( B = k1_xboole_0 ) ) ) ) ) )).

thf('1',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( m1_orders_2 @ X9 @ X10 @ X9 )
      | ( X9 = k1_xboole_0 )
      | ~ ( l1_orders_2 @ X10 )
      | ~ ( v5_orders_2 @ X10 )
      | ~ ( v4_orders_2 @ X10 )
      | ~ ( v3_orders_2 @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t68_orders_2])).

thf('2',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( sk_B = k1_xboole_0 )
    | ~ ( m1_orders_2 @ sk_B @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B = k1_xboole_0 )
    | ~ ( m1_orders_2 @ sk_B @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['2','3','4','5','6'])).

thf('8',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_orders_2 @ sk_B @ sk_A @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['7','8'])).

thf('10',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ~ ( m1_orders_2 @ sk_B @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['9','10'])).

thf('12',plain,(
    m1_orders_2 @ sk_B @ sk_A @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    m1_orders_2 @ sk_B @ sk_A @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t67_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_orders_2 @ C @ A @ B )
             => ( r1_tarski @ C @ B ) ) ) ) )).

thf('15',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( r1_tarski @ X8 @ X6 )
      | ~ ( m1_orders_2 @ X8 @ X7 @ X6 )
      | ~ ( l1_orders_2 @ X7 )
      | ~ ( v5_orders_2 @ X7 )
      | ~ ( v4_orders_2 @ X7 )
      | ~ ( v3_orders_2 @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t67_orders_2])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_C )
      | ( r1_tarski @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_C )
      | ( r1_tarski @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['16','17','18','19','20'])).

thf('22',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ sk_C )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_C ) ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('24',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference('sup-',[status(thm)],['13','23'])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('25',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r2_xboole_0 @ X0 @ X2 )
      | ( X0 = X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('26',plain,
    ( ( sk_B = sk_C )
    | ( r2_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    m1_orders_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( r1_tarski @ X8 @ X6 )
      | ~ ( m1_orders_2 @ X8 @ X7 @ X6 )
      | ~ ( l1_orders_2 @ X7 )
      | ~ ( v5_orders_2 @ X7 )
      | ~ ( v4_orders_2 @ X7 )
      | ~ ( v3_orders_2 @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t67_orders_2])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_B )
      | ( r1_tarski @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

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
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_B )
      | ( r1_tarski @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['30','31','32','33','34'])).

thf('36',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ sk_B )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,(
    r1_tarski @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['27','37'])).

thf(t58_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_xboole_0 @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r2_xboole_0 @ A @ C ) ) )).

thf('39',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_xboole_0 @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r2_xboole_0 @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t58_xboole_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( r2_xboole_0 @ X0 @ sk_B )
      | ~ ( r2_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( sk_B = sk_C )
    | ( r2_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['26','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != X1 )
      | ~ ( r2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('43',plain,(
    ! [X1: $i] :
      ~ ( r2_xboole_0 @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    sk_B = sk_C ),
    inference(clc,[status(thm)],['41','43'])).

thf('45',plain,(
    m1_orders_2 @ sk_B @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['12','44'])).

thf('46',plain,(
    $false ),
    inference(demod,[status(thm)],['11','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dqMmltrrJr
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:23:36 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 32 iterations in 0.016s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.20/0.47  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.20/0.47  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.20/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.47  thf(m1_orders_2_type, type, m1_orders_2: $i > $i > $i > $o).
% 0.20/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.47  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.20/0.47  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.20/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.47  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.47  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(t69_orders_2, conjecture,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.47         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.47           ( ![C:$i]:
% 0.20/0.47             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.47               ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.47                    ( m1_orders_2 @ B @ A @ C ) & ( m1_orders_2 @ C @ A @ B ) ) ) ) ) ) ) ))).
% 0.20/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.47    (~( ![A:$i]:
% 0.20/0.47        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.47            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.47          ( ![B:$i]:
% 0.20/0.47            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.47              ( ![C:$i]:
% 0.20/0.47                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.47                  ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.47                       ( m1_orders_2 @ B @ A @ C ) & 
% 0.20/0.47                       ( m1_orders_2 @ C @ A @ B ) ) ) ) ) ) ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t69_orders_2])).
% 0.20/0.47  thf('0', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(t68_orders_2, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.47         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.47           ( ( ~( ( ( B ) != ( k1_xboole_0 ) ) & ( m1_orders_2 @ B @ A @ B ) ) ) & 
% 0.20/0.47             ( ~( ( ~( m1_orders_2 @ B @ A @ B ) ) & 
% 0.20/0.47                  ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ) ) ))).
% 0.20/0.47  thf('1', plain,
% 0.20/0.47      (![X9 : $i, X10 : $i]:
% 0.20/0.47         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.20/0.47          | ~ (m1_orders_2 @ X9 @ X10 @ X9)
% 0.20/0.47          | ((X9) = (k1_xboole_0))
% 0.20/0.47          | ~ (l1_orders_2 @ X10)
% 0.20/0.47          | ~ (v5_orders_2 @ X10)
% 0.20/0.47          | ~ (v4_orders_2 @ X10)
% 0.20/0.47          | ~ (v3_orders_2 @ X10)
% 0.20/0.47          | (v2_struct_0 @ X10))),
% 0.20/0.47      inference('cnf', [status(esa)], [t68_orders_2])).
% 0.20/0.47  thf('2', plain,
% 0.20/0.47      (((v2_struct_0 @ sk_A)
% 0.20/0.47        | ~ (v3_orders_2 @ sk_A)
% 0.20/0.47        | ~ (v4_orders_2 @ sk_A)
% 0.20/0.47        | ~ (v5_orders_2 @ sk_A)
% 0.20/0.47        | ~ (l1_orders_2 @ sk_A)
% 0.20/0.47        | ((sk_B) = (k1_xboole_0))
% 0.20/0.47        | ~ (m1_orders_2 @ sk_B @ sk_A @ sk_B))),
% 0.20/0.47      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.47  thf('3', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('4', plain, ((v4_orders_2 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('5', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('6', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('7', plain,
% 0.20/0.47      (((v2_struct_0 @ sk_A)
% 0.20/0.47        | ((sk_B) = (k1_xboole_0))
% 0.20/0.47        | ~ (m1_orders_2 @ sk_B @ sk_A @ sk_B))),
% 0.20/0.47      inference('demod', [status(thm)], ['2', '3', '4', '5', '6'])).
% 0.20/0.47  thf('8', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('9', plain,
% 0.20/0.47      (((v2_struct_0 @ sk_A) | ~ (m1_orders_2 @ sk_B @ sk_A @ sk_B))),
% 0.20/0.47      inference('simplify_reflect-', [status(thm)], ['7', '8'])).
% 0.20/0.47  thf('10', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('11', plain, (~ (m1_orders_2 @ sk_B @ sk_A @ sk_B)),
% 0.20/0.47      inference('clc', [status(thm)], ['9', '10'])).
% 0.20/0.47  thf('12', plain, ((m1_orders_2 @ sk_B @ sk_A @ sk_C)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('13', plain, ((m1_orders_2 @ sk_B @ sk_A @ sk_C)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('14', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(t67_orders_2, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.47         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.47           ( ![C:$i]: ( ( m1_orders_2 @ C @ A @ B ) => ( r1_tarski @ C @ B ) ) ) ) ) ))).
% 0.20/0.47  thf('15', plain,
% 0.20/0.47      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.47         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.20/0.47          | (r1_tarski @ X8 @ X6)
% 0.20/0.47          | ~ (m1_orders_2 @ X8 @ X7 @ X6)
% 0.20/0.47          | ~ (l1_orders_2 @ X7)
% 0.20/0.47          | ~ (v5_orders_2 @ X7)
% 0.20/0.47          | ~ (v4_orders_2 @ X7)
% 0.20/0.47          | ~ (v3_orders_2 @ X7)
% 0.20/0.47          | (v2_struct_0 @ X7))),
% 0.20/0.47      inference('cnf', [status(esa)], [t67_orders_2])).
% 0.20/0.47  thf('16', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((v2_struct_0 @ sk_A)
% 0.20/0.47          | ~ (v3_orders_2 @ sk_A)
% 0.20/0.47          | ~ (v4_orders_2 @ sk_A)
% 0.20/0.47          | ~ (v5_orders_2 @ sk_A)
% 0.20/0.47          | ~ (l1_orders_2 @ sk_A)
% 0.20/0.47          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C)
% 0.20/0.47          | (r1_tarski @ X0 @ sk_C))),
% 0.20/0.47      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.47  thf('17', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('18', plain, ((v4_orders_2 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('19', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('20', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('21', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((v2_struct_0 @ sk_A)
% 0.20/0.47          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C)
% 0.20/0.47          | (r1_tarski @ X0 @ sk_C))),
% 0.20/0.47      inference('demod', [status(thm)], ['16', '17', '18', '19', '20'])).
% 0.20/0.47  thf('22', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('23', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((r1_tarski @ X0 @ sk_C) | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C))),
% 0.20/0.47      inference('clc', [status(thm)], ['21', '22'])).
% 0.20/0.47  thf('24', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.20/0.47      inference('sup-', [status(thm)], ['13', '23'])).
% 0.20/0.47  thf(d8_xboole_0, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.20/0.47       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.20/0.47  thf('25', plain,
% 0.20/0.47      (![X0 : $i, X2 : $i]:
% 0.20/0.47         ((r2_xboole_0 @ X0 @ X2) | ((X0) = (X2)) | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.47      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.20/0.47  thf('26', plain, ((((sk_B) = (sk_C)) | (r2_xboole_0 @ sk_B @ sk_C))),
% 0.20/0.47      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.47  thf('27', plain, ((m1_orders_2 @ sk_C @ sk_A @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('28', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('29', plain,
% 0.20/0.47      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.47         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.20/0.47          | (r1_tarski @ X8 @ X6)
% 0.20/0.47          | ~ (m1_orders_2 @ X8 @ X7 @ X6)
% 0.20/0.47          | ~ (l1_orders_2 @ X7)
% 0.20/0.47          | ~ (v5_orders_2 @ X7)
% 0.20/0.47          | ~ (v4_orders_2 @ X7)
% 0.20/0.47          | ~ (v3_orders_2 @ X7)
% 0.20/0.47          | (v2_struct_0 @ X7))),
% 0.20/0.47      inference('cnf', [status(esa)], [t67_orders_2])).
% 0.20/0.47  thf('30', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((v2_struct_0 @ sk_A)
% 0.20/0.47          | ~ (v3_orders_2 @ sk_A)
% 0.20/0.47          | ~ (v4_orders_2 @ sk_A)
% 0.20/0.47          | ~ (v5_orders_2 @ sk_A)
% 0.20/0.47          | ~ (l1_orders_2 @ sk_A)
% 0.20/0.47          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_B)
% 0.20/0.47          | (r1_tarski @ X0 @ sk_B))),
% 0.20/0.47      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.47  thf('31', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('32', plain, ((v4_orders_2 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('33', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('34', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('35', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((v2_struct_0 @ sk_A)
% 0.20/0.47          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_B)
% 0.20/0.47          | (r1_tarski @ X0 @ sk_B))),
% 0.20/0.47      inference('demod', [status(thm)], ['30', '31', '32', '33', '34'])).
% 0.20/0.47  thf('36', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('37', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((r1_tarski @ X0 @ sk_B) | ~ (m1_orders_2 @ X0 @ sk_A @ sk_B))),
% 0.20/0.47      inference('clc', [status(thm)], ['35', '36'])).
% 0.20/0.47  thf('38', plain, ((r1_tarski @ sk_C @ sk_B)),
% 0.20/0.47      inference('sup-', [status(thm)], ['27', '37'])).
% 0.20/0.47  thf(t58_xboole_1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i]:
% 0.20/0.47     ( ( ( r2_xboole_0 @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.20/0.47       ( r2_xboole_0 @ A @ C ) ))).
% 0.20/0.47  thf('39', plain,
% 0.20/0.47      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.47         (~ (r2_xboole_0 @ X3 @ X4)
% 0.20/0.47          | ~ (r1_tarski @ X4 @ X5)
% 0.20/0.47          | (r2_xboole_0 @ X3 @ X5))),
% 0.20/0.47      inference('cnf', [status(esa)], [t58_xboole_1])).
% 0.20/0.47  thf('40', plain,
% 0.20/0.47      (![X0 : $i]: ((r2_xboole_0 @ X0 @ sk_B) | ~ (r2_xboole_0 @ X0 @ sk_C))),
% 0.20/0.47      inference('sup-', [status(thm)], ['38', '39'])).
% 0.20/0.47  thf('41', plain, ((((sk_B) = (sk_C)) | (r2_xboole_0 @ sk_B @ sk_B))),
% 0.20/0.47      inference('sup-', [status(thm)], ['26', '40'])).
% 0.20/0.47  thf('42', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]: (((X0) != (X1)) | ~ (r2_xboole_0 @ X0 @ X1))),
% 0.20/0.47      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.20/0.47  thf('43', plain, (![X1 : $i]: ~ (r2_xboole_0 @ X1 @ X1)),
% 0.20/0.47      inference('simplify', [status(thm)], ['42'])).
% 0.20/0.47  thf('44', plain, (((sk_B) = (sk_C))),
% 0.20/0.47      inference('clc', [status(thm)], ['41', '43'])).
% 0.20/0.47  thf('45', plain, ((m1_orders_2 @ sk_B @ sk_A @ sk_B)),
% 0.20/0.47      inference('demod', [status(thm)], ['12', '44'])).
% 0.20/0.47  thf('46', plain, ($false), inference('demod', [status(thm)], ['11', '45'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
