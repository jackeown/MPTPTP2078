%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ctyndaS9KY

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:38 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 102 expanded)
%              Number of leaves         :   24 (  41 expanded)
%              Depth                    :   10
%              Number of atoms          :  343 ( 873 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v6_orders_2_type,type,(
    v6_orders_2: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_wellord1_type,type,(
    r1_wellord1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(r7_relat_2_type,type,(
    r7_relat_2: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r6_relat_2_type,type,(
    r6_relat_2: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_wellord1_type,type,(
    r2_wellord1: $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(r8_relat_2_type,type,(
    r8_relat_2: $i > $i > $o )).

thf(r4_relat_2_type,type,(
    r4_relat_2: $i > $i > $o )).

thf(r1_relat_2_type,type,(
    r1_relat_2: $i > $i > $o )).

thf(dt_u1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( u1_orders_2 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('0',plain,(
    ! [X9: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X9 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X9 ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( l1_orders_2 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_orders_2])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) )
      | ( v1_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('3',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t40_orders_2,conjecture,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( r2_wellord1 @ ( u1_orders_2 @ A ) @ B )
           => ( ( v6_orders_2 @ B @ A )
              & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_orders_2 @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( r2_wellord1 @ ( u1_orders_2 @ A ) @ B )
             => ( ( v6_orders_2 @ B @ A )
                & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t40_orders_2])).

thf('6',plain,(
    r2_wellord1 @ ( u1_orders_2 @ sk_A ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r2_wellord1 @ A @ B )
        <=> ( ( r1_relat_2 @ A @ B )
            & ( r8_relat_2 @ A @ B )
            & ( r4_relat_2 @ A @ B )
            & ( r6_relat_2 @ A @ B )
            & ( r1_wellord1 @ A @ B ) ) ) ) )).

thf('7',plain,(
    ! [X4: $i,X6: $i] :
      ( ~ ( r2_wellord1 @ X4 @ X6 )
      | ( r1_relat_2 @ X4 @ X6 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d5_wellord1])).

thf('8',plain,
    ( ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
    | ( r1_relat_2 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( r1_relat_2 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    r1_relat_2 @ ( u1_orders_2 @ sk_A ) @ sk_B ),
    inference(demod,[status(thm)],['9','10'])).

thf(t92_orders_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r7_relat_2 @ B @ A )
      <=> ( ( r1_relat_2 @ B @ A )
          & ( r6_relat_2 @ B @ A ) ) ) ) )).

thf('12',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r1_relat_2 @ X10 @ X11 )
      | ~ ( r6_relat_2 @ X10 @ X11 )
      | ( r7_relat_2 @ X10 @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t92_orders_1])).

thf('13',plain,
    ( ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
    | ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ sk_B )
    | ~ ( r6_relat_2 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('15',plain,(
    r2_wellord1 @ ( u1_orders_2 @ sk_A ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X4: $i,X6: $i] :
      ( ~ ( r2_wellord1 @ X4 @ X6 )
      | ( r6_relat_2 @ X4 @ X6 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d5_wellord1])).

thf('17',plain,
    ( ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
    | ( r6_relat_2 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( r6_relat_2 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    r6_relat_2 @ ( u1_orders_2 @ sk_A ) @ sk_B ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
    | ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['13','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d11_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v6_orders_2 @ B @ A )
          <=> ( r7_relat_2 @ ( u1_orders_2 @ A ) @ B ) ) ) ) )).

thf('23',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( r7_relat_2 @ ( u1_orders_2 @ X8 ) @ X7 )
      | ( v6_orders_2 @ X7 @ X8 )
      | ~ ( l1_orders_2 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d11_orders_2])).

thf('24',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( v6_orders_2 @ sk_B @ sk_A )
    | ~ ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( v6_orders_2 @ sk_B @ sk_A )
    | ~ ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ~ ( v6_orders_2 @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ~ ( v6_orders_2 @ sk_B @ sk_A )
   <= ~ ( v6_orders_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['27'])).

thf('29',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['27'])).

thf('31',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ~ ( v6_orders_2 @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['27'])).

thf('33',plain,(
    ~ ( v6_orders_2 @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['31','32'])).

thf('34',plain,(
    ~ ( v6_orders_2 @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['28','33'])).

thf('35',plain,(
    ~ ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['26','34'])).

thf('36',plain,(
    ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) ) ),
    inference(clc,[status(thm)],['21','35'])).

thf('37',plain,(
    ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','36'])).

thf('38',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    $false ),
    inference(demod,[status(thm)],['37','38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ctyndaS9KY
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:33:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 36 iterations in 0.017s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(v6_orders_2_type, type, v6_orders_2: $i > $i > $o).
% 0.21/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.47  thf(r1_wellord1_type, type, r1_wellord1: $i > $i > $o).
% 0.21/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.47  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.47  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.47  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.21/0.47  thf(r7_relat_2_type, type, r7_relat_2: $i > $i > $o).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(r6_relat_2_type, type, r6_relat_2: $i > $i > $o).
% 0.21/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.47  thf(r2_wellord1_type, type, r2_wellord1: $i > $i > $o).
% 0.21/0.47  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.21/0.47  thf(r8_relat_2_type, type, r8_relat_2: $i > $i > $o).
% 0.21/0.47  thf(r4_relat_2_type, type, r4_relat_2: $i > $i > $o).
% 0.21/0.47  thf(r1_relat_2_type, type, r1_relat_2: $i > $i > $o).
% 0.21/0.47  thf(dt_u1_orders_2, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( l1_orders_2 @ A ) =>
% 0.21/0.47       ( m1_subset_1 @
% 0.21/0.47         ( u1_orders_2 @ A ) @ 
% 0.21/0.47         ( k1_zfmisc_1 @
% 0.21/0.47           ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.21/0.47  thf('0', plain,
% 0.21/0.47      (![X9 : $i]:
% 0.21/0.47         ((m1_subset_1 @ (u1_orders_2 @ X9) @ 
% 0.21/0.47           (k1_zfmisc_1 @ 
% 0.21/0.47            (k2_zfmisc_1 @ (u1_struct_0 @ X9) @ (u1_struct_0 @ X9))))
% 0.21/0.47          | ~ (l1_orders_2 @ X9))),
% 0.21/0.47      inference('cnf', [status(esa)], [dt_u1_orders_2])).
% 0.21/0.47  thf(cc2_relat_1, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( v1_relat_1 @ A ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.21/0.47  thf('1', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.21/0.47          | (v1_relat_1 @ X0)
% 0.21/0.47          | ~ (v1_relat_1 @ X1))),
% 0.21/0.47      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.21/0.47  thf('2', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (l1_orders_2 @ X0)
% 0.21/0.47          | ~ (v1_relat_1 @ 
% 0.21/0.47               (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0)))
% 0.21/0.47          | (v1_relat_1 @ (u1_orders_2 @ X0)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.47  thf(fc6_relat_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.21/0.47  thf('3', plain,
% 0.21/0.47      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.21/0.47      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.21/0.47  thf('4', plain,
% 0.21/0.47      (![X0 : $i]: (~ (l1_orders_2 @ X0) | (v1_relat_1 @ (u1_orders_2 @ X0)))),
% 0.21/0.47      inference('demod', [status(thm)], ['2', '3'])).
% 0.21/0.47  thf('5', plain,
% 0.21/0.47      (![X0 : $i]: (~ (l1_orders_2 @ X0) | (v1_relat_1 @ (u1_orders_2 @ X0)))),
% 0.21/0.47      inference('demod', [status(thm)], ['2', '3'])).
% 0.21/0.47  thf(t40_orders_2, conjecture,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( l1_orders_2 @ A ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.47           ( ( r2_wellord1 @ ( u1_orders_2 @ A ) @ B ) =>
% 0.21/0.47             ( ( v6_orders_2 @ B @ A ) & 
% 0.21/0.47               ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i]:
% 0.21/0.47        ( ( l1_orders_2 @ A ) =>
% 0.21/0.47          ( ![B:$i]:
% 0.21/0.47            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.47              ( ( r2_wellord1 @ ( u1_orders_2 @ A ) @ B ) =>
% 0.21/0.47                ( ( v6_orders_2 @ B @ A ) & 
% 0.21/0.47                  ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t40_orders_2])).
% 0.21/0.47  thf('6', plain, ((r2_wellord1 @ (u1_orders_2 @ sk_A) @ sk_B)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(d5_wellord1, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( v1_relat_1 @ A ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( r2_wellord1 @ A @ B ) <=>
% 0.21/0.47           ( ( r1_relat_2 @ A @ B ) & ( r8_relat_2 @ A @ B ) & 
% 0.21/0.47             ( r4_relat_2 @ A @ B ) & ( r6_relat_2 @ A @ B ) & 
% 0.21/0.47             ( r1_wellord1 @ A @ B ) ) ) ) ))).
% 0.21/0.47  thf('7', plain,
% 0.21/0.47      (![X4 : $i, X6 : $i]:
% 0.21/0.47         (~ (r2_wellord1 @ X4 @ X6)
% 0.21/0.47          | (r1_relat_2 @ X4 @ X6)
% 0.21/0.47          | ~ (v1_relat_1 @ X4))),
% 0.21/0.47      inference('cnf', [status(esa)], [d5_wellord1])).
% 0.21/0.47  thf('8', plain,
% 0.21/0.47      ((~ (v1_relat_1 @ (u1_orders_2 @ sk_A))
% 0.21/0.47        | (r1_relat_2 @ (u1_orders_2 @ sk_A) @ sk_B))),
% 0.21/0.47      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.47  thf('9', plain,
% 0.21/0.47      ((~ (l1_orders_2 @ sk_A) | (r1_relat_2 @ (u1_orders_2 @ sk_A) @ sk_B))),
% 0.21/0.47      inference('sup-', [status(thm)], ['5', '8'])).
% 0.21/0.47  thf('10', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('11', plain, ((r1_relat_2 @ (u1_orders_2 @ sk_A) @ sk_B)),
% 0.21/0.47      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.47  thf(t92_orders_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( v1_relat_1 @ B ) =>
% 0.21/0.47       ( ( r7_relat_2 @ B @ A ) <=>
% 0.21/0.47         ( ( r1_relat_2 @ B @ A ) & ( r6_relat_2 @ B @ A ) ) ) ))).
% 0.21/0.47  thf('12', plain,
% 0.21/0.47      (![X10 : $i, X11 : $i]:
% 0.21/0.47         (~ (r1_relat_2 @ X10 @ X11)
% 0.21/0.47          | ~ (r6_relat_2 @ X10 @ X11)
% 0.21/0.47          | (r7_relat_2 @ X10 @ X11)
% 0.21/0.47          | ~ (v1_relat_1 @ X10))),
% 0.21/0.47      inference('cnf', [status(esa)], [t92_orders_1])).
% 0.21/0.47  thf('13', plain,
% 0.21/0.47      ((~ (v1_relat_1 @ (u1_orders_2 @ sk_A))
% 0.21/0.47        | (r7_relat_2 @ (u1_orders_2 @ sk_A) @ sk_B)
% 0.21/0.47        | ~ (r6_relat_2 @ (u1_orders_2 @ sk_A) @ sk_B))),
% 0.21/0.47      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.47  thf('14', plain,
% 0.21/0.47      (![X0 : $i]: (~ (l1_orders_2 @ X0) | (v1_relat_1 @ (u1_orders_2 @ X0)))),
% 0.21/0.47      inference('demod', [status(thm)], ['2', '3'])).
% 0.21/0.47  thf('15', plain, ((r2_wellord1 @ (u1_orders_2 @ sk_A) @ sk_B)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('16', plain,
% 0.21/0.47      (![X4 : $i, X6 : $i]:
% 0.21/0.47         (~ (r2_wellord1 @ X4 @ X6)
% 0.21/0.47          | (r6_relat_2 @ X4 @ X6)
% 0.21/0.47          | ~ (v1_relat_1 @ X4))),
% 0.21/0.47      inference('cnf', [status(esa)], [d5_wellord1])).
% 0.21/0.47  thf('17', plain,
% 0.21/0.47      ((~ (v1_relat_1 @ (u1_orders_2 @ sk_A))
% 0.21/0.47        | (r6_relat_2 @ (u1_orders_2 @ sk_A) @ sk_B))),
% 0.21/0.47      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.47  thf('18', plain,
% 0.21/0.47      ((~ (l1_orders_2 @ sk_A) | (r6_relat_2 @ (u1_orders_2 @ sk_A) @ sk_B))),
% 0.21/0.47      inference('sup-', [status(thm)], ['14', '17'])).
% 0.21/0.47  thf('19', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('20', plain, ((r6_relat_2 @ (u1_orders_2 @ sk_A) @ sk_B)),
% 0.21/0.47      inference('demod', [status(thm)], ['18', '19'])).
% 0.21/0.47  thf('21', plain,
% 0.21/0.47      ((~ (v1_relat_1 @ (u1_orders_2 @ sk_A))
% 0.21/0.47        | (r7_relat_2 @ (u1_orders_2 @ sk_A) @ sk_B))),
% 0.21/0.47      inference('demod', [status(thm)], ['13', '20'])).
% 0.21/0.47  thf('22', plain,
% 0.21/0.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(d11_orders_2, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( l1_orders_2 @ A ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.47           ( ( v6_orders_2 @ B @ A ) <=>
% 0.21/0.47             ( r7_relat_2 @ ( u1_orders_2 @ A ) @ B ) ) ) ) ))).
% 0.21/0.47  thf('23', plain,
% 0.21/0.47      (![X7 : $i, X8 : $i]:
% 0.21/0.47         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.21/0.47          | ~ (r7_relat_2 @ (u1_orders_2 @ X8) @ X7)
% 0.21/0.47          | (v6_orders_2 @ X7 @ X8)
% 0.21/0.47          | ~ (l1_orders_2 @ X8))),
% 0.21/0.47      inference('cnf', [status(esa)], [d11_orders_2])).
% 0.21/0.47  thf('24', plain,
% 0.21/0.47      ((~ (l1_orders_2 @ sk_A)
% 0.21/0.47        | (v6_orders_2 @ sk_B @ sk_A)
% 0.21/0.47        | ~ (r7_relat_2 @ (u1_orders_2 @ sk_A) @ sk_B))),
% 0.21/0.47      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.47  thf('25', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('26', plain,
% 0.21/0.47      (((v6_orders_2 @ sk_B @ sk_A)
% 0.21/0.47        | ~ (r7_relat_2 @ (u1_orders_2 @ sk_A) @ sk_B))),
% 0.21/0.47      inference('demod', [status(thm)], ['24', '25'])).
% 0.21/0.47  thf('27', plain,
% 0.21/0.47      ((~ (v6_orders_2 @ sk_B @ sk_A)
% 0.21/0.47        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('28', plain,
% 0.21/0.47      ((~ (v6_orders_2 @ sk_B @ sk_A)) <= (~ ((v6_orders_2 @ sk_B @ sk_A)))),
% 0.21/0.47      inference('split', [status(esa)], ['27'])).
% 0.21/0.47  thf('29', plain,
% 0.21/0.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('30', plain,
% 0.21/0.47      ((~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.21/0.47         <= (~ ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.47      inference('split', [status(esa)], ['27'])).
% 0.21/0.47  thf('31', plain,
% 0.21/0.47      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['29', '30'])).
% 0.21/0.47  thf('32', plain,
% 0.21/0.47      (~ ((v6_orders_2 @ sk_B @ sk_A)) | 
% 0.21/0.47       ~ ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.47      inference('split', [status(esa)], ['27'])).
% 0.21/0.47  thf('33', plain, (~ ((v6_orders_2 @ sk_B @ sk_A))),
% 0.21/0.47      inference('sat_resolution*', [status(thm)], ['31', '32'])).
% 0.21/0.47  thf('34', plain, (~ (v6_orders_2 @ sk_B @ sk_A)),
% 0.21/0.47      inference('simpl_trail', [status(thm)], ['28', '33'])).
% 0.21/0.47  thf('35', plain, (~ (r7_relat_2 @ (u1_orders_2 @ sk_A) @ sk_B)),
% 0.21/0.47      inference('clc', [status(thm)], ['26', '34'])).
% 0.21/0.47  thf('36', plain, (~ (v1_relat_1 @ (u1_orders_2 @ sk_A))),
% 0.21/0.47      inference('clc', [status(thm)], ['21', '35'])).
% 0.21/0.47  thf('37', plain, (~ (l1_orders_2 @ sk_A)),
% 0.21/0.47      inference('sup-', [status(thm)], ['4', '36'])).
% 0.21/0.47  thf('38', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('39', plain, ($false), inference('demod', [status(thm)], ['37', '38'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
