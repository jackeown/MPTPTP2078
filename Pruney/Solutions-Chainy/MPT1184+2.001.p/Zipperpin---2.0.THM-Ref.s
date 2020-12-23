%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AmLkzNJfLw

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:29 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   64 (  95 expanded)
%              Number of leaves         :   26 (  41 expanded)
%              Depth                    :   11
%              Number of atoms          :  334 ( 983 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r8_relat_2_type,type,(
    r8_relat_2: $i > $i > $o )).

thf(r6_relat_2_type,type,(
    r6_relat_2: $i > $i > $o )).

thf(r4_relat_2_type,type,(
    r4_relat_2: $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(r3_orders_1_type,type,(
    r3_orders_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_relat_2_type,type,(
    r1_relat_2: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r7_relat_2_type,type,(
    r7_relat_2: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v6_orders_2_type,type,(
    v6_orders_2: $i > $i > $o )).

thf(t135_orders_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( r3_orders_1 @ ( u1_orders_2 @ A ) @ B )
           => ( ( v6_orders_2 @ B @ A )
              & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v3_orders_2 @ A )
          & ( v4_orders_2 @ A )
          & ( v5_orders_2 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( r3_orders_1 @ ( u1_orders_2 @ A ) @ B )
             => ( ( v6_orders_2 @ B @ A )
                & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t135_orders_2])).

thf('0',plain,
    ( ~ ( v6_orders_2 @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v6_orders_2 @ sk_B @ sk_A )
   <= ~ ( v6_orders_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ~ ( v6_orders_2 @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('6',plain,(
    ~ ( v6_orders_2 @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['4','5'])).

thf('7',plain,(
    ~ ( v6_orders_2 @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d11_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v6_orders_2 @ B @ A )
          <=> ( r7_relat_2 @ ( u1_orders_2 @ A ) @ B ) ) ) ) )).

thf('9',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( r7_relat_2 @ ( u1_orders_2 @ X4 ) @ X3 )
      | ( v6_orders_2 @ X3 @ X4 )
      | ~ ( l1_orders_2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d11_orders_2])).

thf('10',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( v6_orders_2 @ sk_B @ sk_A )
    | ~ ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_u1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( u1_orders_2 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('12',plain,(
    ! [X8: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X8 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X8 ) ) ) )
      | ~ ( l1_orders_2 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_orders_2])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_relat_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('16',plain,(
    r3_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d8_orders_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r3_orders_1 @ A @ B )
        <=> ( ( r1_relat_2 @ A @ B )
            & ( r8_relat_2 @ A @ B )
            & ( r4_relat_2 @ A @ B )
            & ( r6_relat_2 @ A @ B ) ) ) ) )).

thf('17',plain,(
    ! [X5: $i,X7: $i] :
      ( ~ ( r3_orders_1 @ X5 @ X7 )
      | ( r1_relat_2 @ X5 @ X7 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d8_orders_1])).

thf('18',plain,
    ( ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
    | ( r1_relat_2 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( r1_relat_2 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    r1_relat_2 @ ( u1_orders_2 @ sk_A ) @ sk_B ),
    inference(demod,[status(thm)],['19','20'])).

thf(t92_orders_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r7_relat_2 @ B @ A )
      <=> ( ( r1_relat_2 @ B @ A )
          & ( r6_relat_2 @ B @ A ) ) ) ) )).

thf('22',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( r1_relat_2 @ X9 @ X10 )
      | ~ ( r6_relat_2 @ X9 @ X10 )
      | ( r7_relat_2 @ X9 @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t92_orders_1])).

thf('23',plain,
    ( ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
    | ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ sk_B )
    | ~ ( r6_relat_2 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('25',plain,(
    r3_orders_1 @ ( u1_orders_2 @ sk_A ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X5: $i,X7: $i] :
      ( ~ ( r3_orders_1 @ X5 @ X7 )
      | ( r6_relat_2 @ X5 @ X7 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d8_orders_1])).

thf('27',plain,
    ( ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
    | ( r6_relat_2 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( r6_relat_2 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    r6_relat_2 @ ( u1_orders_2 @ sk_A ) @ sk_B ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
    | ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['23','30'])).

thf('32',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['14','31'])).

thf('33',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ sk_B ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    v6_orders_2 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['10','11','34'])).

thf('36',plain,(
    $false ),
    inference(demod,[status(thm)],['7','35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AmLkzNJfLw
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:36:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 35 iterations in 0.016s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(r8_relat_2_type, type, r8_relat_2: $i > $i > $o).
% 0.20/0.47  thf(r6_relat_2_type, type, r6_relat_2: $i > $i > $o).
% 0.20/0.47  thf(r4_relat_2_type, type, r4_relat_2: $i > $i > $o).
% 0.20/0.47  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.20/0.47  thf(r3_orders_1_type, type, r3_orders_1: $i > $i > $o).
% 0.20/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.47  thf(r1_relat_2_type, type, r1_relat_2: $i > $i > $o).
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.47  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.20/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.47  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.47  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.20/0.47  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.20/0.47  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.20/0.47  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.47  thf(r7_relat_2_type, type, r7_relat_2: $i > $i > $o).
% 0.20/0.47  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.47  thf(v6_orders_2_type, type, v6_orders_2: $i > $i > $o).
% 0.20/0.47  thf(t135_orders_2, conjecture,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.47         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.47           ( ( r3_orders_1 @ ( u1_orders_2 @ A ) @ B ) =>
% 0.20/0.47             ( ( v6_orders_2 @ B @ A ) & 
% 0.20/0.47               ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ))).
% 0.20/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.47    (~( ![A:$i]:
% 0.20/0.47        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.47            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.47          ( ![B:$i]:
% 0.20/0.47            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.47              ( ( r3_orders_1 @ ( u1_orders_2 @ A ) @ B ) =>
% 0.20/0.47                ( ( v6_orders_2 @ B @ A ) & 
% 0.20/0.47                  ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t135_orders_2])).
% 0.20/0.47  thf('0', plain,
% 0.20/0.47      ((~ (v6_orders_2 @ sk_B @ sk_A)
% 0.20/0.47        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('1', plain,
% 0.20/0.47      ((~ (v6_orders_2 @ sk_B @ sk_A)) <= (~ ((v6_orders_2 @ sk_B @ sk_A)))),
% 0.20/0.47      inference('split', [status(esa)], ['0'])).
% 0.20/0.47  thf('2', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('3', plain,
% 0.20/0.47      ((~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.20/0.47         <= (~ ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.20/0.47      inference('split', [status(esa)], ['0'])).
% 0.20/0.47  thf('4', plain,
% 0.20/0.47      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.47  thf('5', plain,
% 0.20/0.47      (~ ((v6_orders_2 @ sk_B @ sk_A)) | 
% 0.20/0.47       ~ ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.47      inference('split', [status(esa)], ['0'])).
% 0.20/0.47  thf('6', plain, (~ ((v6_orders_2 @ sk_B @ sk_A))),
% 0.20/0.47      inference('sat_resolution*', [status(thm)], ['4', '5'])).
% 0.20/0.47  thf('7', plain, (~ (v6_orders_2 @ sk_B @ sk_A)),
% 0.20/0.47      inference('simpl_trail', [status(thm)], ['1', '6'])).
% 0.20/0.47  thf('8', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(d11_orders_2, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( l1_orders_2 @ A ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.47           ( ( v6_orders_2 @ B @ A ) <=>
% 0.20/0.47             ( r7_relat_2 @ ( u1_orders_2 @ A ) @ B ) ) ) ) ))).
% 0.20/0.47  thf('9', plain,
% 0.20/0.47      (![X3 : $i, X4 : $i]:
% 0.20/0.47         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.20/0.47          | ~ (r7_relat_2 @ (u1_orders_2 @ X4) @ X3)
% 0.20/0.47          | (v6_orders_2 @ X3 @ X4)
% 0.20/0.47          | ~ (l1_orders_2 @ X4))),
% 0.20/0.47      inference('cnf', [status(esa)], [d11_orders_2])).
% 0.20/0.47  thf('10', plain,
% 0.20/0.47      ((~ (l1_orders_2 @ sk_A)
% 0.20/0.47        | (v6_orders_2 @ sk_B @ sk_A)
% 0.20/0.47        | ~ (r7_relat_2 @ (u1_orders_2 @ sk_A) @ sk_B))),
% 0.20/0.47      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.47  thf('11', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(dt_u1_orders_2, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( l1_orders_2 @ A ) =>
% 0.20/0.47       ( m1_subset_1 @
% 0.20/0.47         ( u1_orders_2 @ A ) @ 
% 0.20/0.47         ( k1_zfmisc_1 @
% 0.20/0.47           ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.20/0.47  thf('12', plain,
% 0.20/0.47      (![X8 : $i]:
% 0.20/0.47         ((m1_subset_1 @ (u1_orders_2 @ X8) @ 
% 0.20/0.47           (k1_zfmisc_1 @ 
% 0.20/0.47            (k2_zfmisc_1 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X8))))
% 0.20/0.47          | ~ (l1_orders_2 @ X8))),
% 0.20/0.47      inference('cnf', [status(esa)], [dt_u1_orders_2])).
% 0.20/0.47  thf(cc1_relset_1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i]:
% 0.20/0.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.47       ( v1_relat_1 @ C ) ))).
% 0.20/0.47  thf('13', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.47         ((v1_relat_1 @ X0)
% 0.20/0.47          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2))))),
% 0.20/0.47      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.20/0.47  thf('14', plain,
% 0.20/0.47      (![X0 : $i]: (~ (l1_orders_2 @ X0) | (v1_relat_1 @ (u1_orders_2 @ X0)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.47  thf('15', plain,
% 0.20/0.47      (![X0 : $i]: (~ (l1_orders_2 @ X0) | (v1_relat_1 @ (u1_orders_2 @ X0)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.47  thf('16', plain, ((r3_orders_1 @ (u1_orders_2 @ sk_A) @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(d8_orders_1, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( v1_relat_1 @ A ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( r3_orders_1 @ A @ B ) <=>
% 0.20/0.47           ( ( r1_relat_2 @ A @ B ) & ( r8_relat_2 @ A @ B ) & 
% 0.20/0.47             ( r4_relat_2 @ A @ B ) & ( r6_relat_2 @ A @ B ) ) ) ) ))).
% 0.20/0.47  thf('17', plain,
% 0.20/0.47      (![X5 : $i, X7 : $i]:
% 0.20/0.47         (~ (r3_orders_1 @ X5 @ X7)
% 0.20/0.47          | (r1_relat_2 @ X5 @ X7)
% 0.20/0.47          | ~ (v1_relat_1 @ X5))),
% 0.20/0.47      inference('cnf', [status(esa)], [d8_orders_1])).
% 0.20/0.47  thf('18', plain,
% 0.20/0.47      ((~ (v1_relat_1 @ (u1_orders_2 @ sk_A))
% 0.20/0.47        | (r1_relat_2 @ (u1_orders_2 @ sk_A) @ sk_B))),
% 0.20/0.47      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.47  thf('19', plain,
% 0.20/0.47      ((~ (l1_orders_2 @ sk_A) | (r1_relat_2 @ (u1_orders_2 @ sk_A) @ sk_B))),
% 0.20/0.47      inference('sup-', [status(thm)], ['15', '18'])).
% 0.20/0.47  thf('20', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('21', plain, ((r1_relat_2 @ (u1_orders_2 @ sk_A) @ sk_B)),
% 0.20/0.47      inference('demod', [status(thm)], ['19', '20'])).
% 0.20/0.47  thf(t92_orders_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( v1_relat_1 @ B ) =>
% 0.20/0.47       ( ( r7_relat_2 @ B @ A ) <=>
% 0.20/0.47         ( ( r1_relat_2 @ B @ A ) & ( r6_relat_2 @ B @ A ) ) ) ))).
% 0.20/0.47  thf('22', plain,
% 0.20/0.47      (![X9 : $i, X10 : $i]:
% 0.20/0.47         (~ (r1_relat_2 @ X9 @ X10)
% 0.20/0.47          | ~ (r6_relat_2 @ X9 @ X10)
% 0.20/0.47          | (r7_relat_2 @ X9 @ X10)
% 0.20/0.47          | ~ (v1_relat_1 @ X9))),
% 0.20/0.47      inference('cnf', [status(esa)], [t92_orders_1])).
% 0.20/0.47  thf('23', plain,
% 0.20/0.47      ((~ (v1_relat_1 @ (u1_orders_2 @ sk_A))
% 0.20/0.47        | (r7_relat_2 @ (u1_orders_2 @ sk_A) @ sk_B)
% 0.20/0.47        | ~ (r6_relat_2 @ (u1_orders_2 @ sk_A) @ sk_B))),
% 0.20/0.47      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.47  thf('24', plain,
% 0.20/0.47      (![X0 : $i]: (~ (l1_orders_2 @ X0) | (v1_relat_1 @ (u1_orders_2 @ X0)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.47  thf('25', plain, ((r3_orders_1 @ (u1_orders_2 @ sk_A) @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('26', plain,
% 0.20/0.47      (![X5 : $i, X7 : $i]:
% 0.20/0.47         (~ (r3_orders_1 @ X5 @ X7)
% 0.20/0.47          | (r6_relat_2 @ X5 @ X7)
% 0.20/0.47          | ~ (v1_relat_1 @ X5))),
% 0.20/0.47      inference('cnf', [status(esa)], [d8_orders_1])).
% 0.20/0.47  thf('27', plain,
% 0.20/0.47      ((~ (v1_relat_1 @ (u1_orders_2 @ sk_A))
% 0.20/0.47        | (r6_relat_2 @ (u1_orders_2 @ sk_A) @ sk_B))),
% 0.20/0.47      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.47  thf('28', plain,
% 0.20/0.47      ((~ (l1_orders_2 @ sk_A) | (r6_relat_2 @ (u1_orders_2 @ sk_A) @ sk_B))),
% 0.20/0.47      inference('sup-', [status(thm)], ['24', '27'])).
% 0.20/0.47  thf('29', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('30', plain, ((r6_relat_2 @ (u1_orders_2 @ sk_A) @ sk_B)),
% 0.20/0.47      inference('demod', [status(thm)], ['28', '29'])).
% 0.20/0.47  thf('31', plain,
% 0.20/0.47      ((~ (v1_relat_1 @ (u1_orders_2 @ sk_A))
% 0.20/0.47        | (r7_relat_2 @ (u1_orders_2 @ sk_A) @ sk_B))),
% 0.20/0.47      inference('demod', [status(thm)], ['23', '30'])).
% 0.20/0.47  thf('32', plain,
% 0.20/0.47      ((~ (l1_orders_2 @ sk_A) | (r7_relat_2 @ (u1_orders_2 @ sk_A) @ sk_B))),
% 0.20/0.47      inference('sup-', [status(thm)], ['14', '31'])).
% 0.20/0.47  thf('33', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('34', plain, ((r7_relat_2 @ (u1_orders_2 @ sk_A) @ sk_B)),
% 0.20/0.47      inference('demod', [status(thm)], ['32', '33'])).
% 0.20/0.47  thf('35', plain, ((v6_orders_2 @ sk_B @ sk_A)),
% 0.20/0.47      inference('demod', [status(thm)], ['10', '11', '34'])).
% 0.20/0.47  thf('36', plain, ($false), inference('demod', [status(thm)], ['7', '35'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
