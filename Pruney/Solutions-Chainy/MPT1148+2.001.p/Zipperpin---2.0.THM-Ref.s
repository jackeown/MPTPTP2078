%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0BqRe51LFQ

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
% Statistics : Number of formulae       :   62 (  93 expanded)
%              Number of leaves         :   23 (  38 expanded)
%              Depth                    :   10
%              Number of atoms          :  324 ( 816 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r2_wellord1_type,type,(
    r2_wellord1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r8_relat_2_type,type,(
    r8_relat_2: $i > $i > $o )).

thf(r6_relat_2_type,type,(
    r6_relat_2: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(r1_wellord1_type,type,(
    r1_wellord1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r7_relat_2_type,type,(
    r7_relat_2: $i > $i > $o )).

thf(v6_orders_2_type,type,(
    v6_orders_2: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r4_relat_2_type,type,(
    r4_relat_2: $i > $i > $o )).

thf(r1_relat_2_type,type,(
    r1_relat_2: $i > $i > $o )).

thf(dt_u1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( u1_orders_2 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('0',plain,(
    ! [X8: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X8 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X8 ) ) ) )
      | ~ ( l1_orders_2 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_orders_2])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('1',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( v1_relat_1 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

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

thf('4',plain,(
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

thf('5',plain,(
    ! [X0: $i,X2: $i] :
      ( ~ ( r2_wellord1 @ X0 @ X2 )
      | ( r1_relat_2 @ X0 @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d5_wellord1])).

thf('6',plain,
    ( ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
    | ( r1_relat_2 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( r1_relat_2 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    r1_relat_2 @ ( u1_orders_2 @ sk_A ) @ sk_B ),
    inference(demod,[status(thm)],['7','8'])).

thf(t92_orders_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r7_relat_2 @ B @ A )
      <=> ( ( r1_relat_2 @ B @ A )
          & ( r6_relat_2 @ B @ A ) ) ) ) )).

thf('10',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( r1_relat_2 @ X9 @ X10 )
      | ~ ( r6_relat_2 @ X9 @ X10 )
      | ( r7_relat_2 @ X9 @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t92_orders_1])).

thf('11',plain,
    ( ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
    | ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ sk_B )
    | ~ ( r6_relat_2 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('13',plain,(
    r2_wellord1 @ ( u1_orders_2 @ sk_A ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i,X2: $i] :
      ( ~ ( r2_wellord1 @ X0 @ X2 )
      | ( r6_relat_2 @ X0 @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d5_wellord1])).

thf('15',plain,
    ( ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
    | ( r6_relat_2 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( r6_relat_2 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    r6_relat_2 @ ( u1_orders_2 @ sk_A ) @ sk_B ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
    | ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['11','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d11_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v6_orders_2 @ B @ A )
          <=> ( r7_relat_2 @ ( u1_orders_2 @ A ) @ B ) ) ) ) )).

thf('21',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( r7_relat_2 @ ( u1_orders_2 @ X7 ) @ X6 )
      | ( v6_orders_2 @ X6 @ X7 )
      | ~ ( l1_orders_2 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d11_orders_2])).

thf('22',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( v6_orders_2 @ sk_B @ sk_A )
    | ~ ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( v6_orders_2 @ sk_B @ sk_A )
    | ~ ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ~ ( v6_orders_2 @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ~ ( v6_orders_2 @ sk_B @ sk_A )
   <= ~ ( v6_orders_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['25'])).

thf('27',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['25'])).

thf('29',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ~ ( v6_orders_2 @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['25'])).

thf('31',plain,(
    ~ ( v6_orders_2 @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['29','30'])).

thf('32',plain,(
    ~ ( v6_orders_2 @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['26','31'])).

thf('33',plain,(
    ~ ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['24','32'])).

thf('34',plain,(
    ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) ) ),
    inference(clc,[status(thm)],['19','33'])).

thf('35',plain,(
    ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','34'])).

thf('36',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    $false ),
    inference(demod,[status(thm)],['35','36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0BqRe51LFQ
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:22:57 EST 2020
% 0.19/0.35  % CPUTime    : 
% 0.19/0.35  % Running portfolio for 600 s
% 0.19/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.19/0.35  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 34 iterations in 0.018s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.48  thf(r2_wellord1_type, type, r2_wellord1: $i > $i > $o).
% 0.21/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.48  thf(r8_relat_2_type, type, r8_relat_2: $i > $i > $o).
% 0.21/0.48  thf(r6_relat_2_type, type, r6_relat_2: $i > $i > $o).
% 0.21/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.48  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.48  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.21/0.48  thf(r1_wellord1_type, type, r1_wellord1: $i > $i > $o).
% 0.21/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.48  thf(r7_relat_2_type, type, r7_relat_2: $i > $i > $o).
% 0.21/0.48  thf(v6_orders_2_type, type, v6_orders_2: $i > $i > $o).
% 0.21/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.48  thf(r4_relat_2_type, type, r4_relat_2: $i > $i > $o).
% 0.21/0.48  thf(r1_relat_2_type, type, r1_relat_2: $i > $i > $o).
% 0.21/0.48  thf(dt_u1_orders_2, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( l1_orders_2 @ A ) =>
% 0.21/0.48       ( m1_subset_1 @
% 0.21/0.48         ( u1_orders_2 @ A ) @ 
% 0.21/0.48         ( k1_zfmisc_1 @
% 0.21/0.48           ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.21/0.48  thf('0', plain,
% 0.21/0.48      (![X8 : $i]:
% 0.21/0.48         ((m1_subset_1 @ (u1_orders_2 @ X8) @ 
% 0.21/0.48           (k1_zfmisc_1 @ 
% 0.21/0.48            (k2_zfmisc_1 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X8))))
% 0.21/0.48          | ~ (l1_orders_2 @ X8))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_u1_orders_2])).
% 0.21/0.48  thf(cc1_relset_1, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.48       ( v1_relat_1 @ C ) ))).
% 0.21/0.48  thf('1', plain,
% 0.21/0.48      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.48         ((v1_relat_1 @ X3)
% 0.21/0.48          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5))))),
% 0.21/0.48      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.21/0.48  thf('2', plain,
% 0.21/0.48      (![X0 : $i]: (~ (l1_orders_2 @ X0) | (v1_relat_1 @ (u1_orders_2 @ X0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.48  thf('3', plain,
% 0.21/0.48      (![X0 : $i]: (~ (l1_orders_2 @ X0) | (v1_relat_1 @ (u1_orders_2 @ X0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.48  thf(t40_orders_2, conjecture,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( l1_orders_2 @ A ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.48           ( ( r2_wellord1 @ ( u1_orders_2 @ A ) @ B ) =>
% 0.21/0.48             ( ( v6_orders_2 @ B @ A ) & 
% 0.21/0.48               ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i]:
% 0.21/0.48        ( ( l1_orders_2 @ A ) =>
% 0.21/0.48          ( ![B:$i]:
% 0.21/0.48            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.48              ( ( r2_wellord1 @ ( u1_orders_2 @ A ) @ B ) =>
% 0.21/0.48                ( ( v6_orders_2 @ B @ A ) & 
% 0.21/0.48                  ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t40_orders_2])).
% 0.21/0.48  thf('4', plain, ((r2_wellord1 @ (u1_orders_2 @ sk_A) @ sk_B)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(d5_wellord1, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( v1_relat_1 @ A ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( r2_wellord1 @ A @ B ) <=>
% 0.21/0.48           ( ( r1_relat_2 @ A @ B ) & ( r8_relat_2 @ A @ B ) & 
% 0.21/0.48             ( r4_relat_2 @ A @ B ) & ( r6_relat_2 @ A @ B ) & 
% 0.21/0.48             ( r1_wellord1 @ A @ B ) ) ) ) ))).
% 0.21/0.48  thf('5', plain,
% 0.21/0.48      (![X0 : $i, X2 : $i]:
% 0.21/0.48         (~ (r2_wellord1 @ X0 @ X2)
% 0.21/0.48          | (r1_relat_2 @ X0 @ X2)
% 0.21/0.48          | ~ (v1_relat_1 @ X0))),
% 0.21/0.48      inference('cnf', [status(esa)], [d5_wellord1])).
% 0.21/0.48  thf('6', plain,
% 0.21/0.48      ((~ (v1_relat_1 @ (u1_orders_2 @ sk_A))
% 0.21/0.48        | (r1_relat_2 @ (u1_orders_2 @ sk_A) @ sk_B))),
% 0.21/0.48      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.48  thf('7', plain,
% 0.21/0.48      ((~ (l1_orders_2 @ sk_A) | (r1_relat_2 @ (u1_orders_2 @ sk_A) @ sk_B))),
% 0.21/0.48      inference('sup-', [status(thm)], ['3', '6'])).
% 0.21/0.48  thf('8', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('9', plain, ((r1_relat_2 @ (u1_orders_2 @ sk_A) @ sk_B)),
% 0.21/0.48      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.48  thf(t92_orders_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( v1_relat_1 @ B ) =>
% 0.21/0.48       ( ( r7_relat_2 @ B @ A ) <=>
% 0.21/0.48         ( ( r1_relat_2 @ B @ A ) & ( r6_relat_2 @ B @ A ) ) ) ))).
% 0.21/0.48  thf('10', plain,
% 0.21/0.48      (![X9 : $i, X10 : $i]:
% 0.21/0.48         (~ (r1_relat_2 @ X9 @ X10)
% 0.21/0.48          | ~ (r6_relat_2 @ X9 @ X10)
% 0.21/0.48          | (r7_relat_2 @ X9 @ X10)
% 0.21/0.48          | ~ (v1_relat_1 @ X9))),
% 0.21/0.48      inference('cnf', [status(esa)], [t92_orders_1])).
% 0.21/0.48  thf('11', plain,
% 0.21/0.48      ((~ (v1_relat_1 @ (u1_orders_2 @ sk_A))
% 0.21/0.48        | (r7_relat_2 @ (u1_orders_2 @ sk_A) @ sk_B)
% 0.21/0.48        | ~ (r6_relat_2 @ (u1_orders_2 @ sk_A) @ sk_B))),
% 0.21/0.48      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.48  thf('12', plain,
% 0.21/0.48      (![X0 : $i]: (~ (l1_orders_2 @ X0) | (v1_relat_1 @ (u1_orders_2 @ X0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.48  thf('13', plain, ((r2_wellord1 @ (u1_orders_2 @ sk_A) @ sk_B)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('14', plain,
% 0.21/0.48      (![X0 : $i, X2 : $i]:
% 0.21/0.48         (~ (r2_wellord1 @ X0 @ X2)
% 0.21/0.48          | (r6_relat_2 @ X0 @ X2)
% 0.21/0.48          | ~ (v1_relat_1 @ X0))),
% 0.21/0.48      inference('cnf', [status(esa)], [d5_wellord1])).
% 0.21/0.48  thf('15', plain,
% 0.21/0.48      ((~ (v1_relat_1 @ (u1_orders_2 @ sk_A))
% 0.21/0.48        | (r6_relat_2 @ (u1_orders_2 @ sk_A) @ sk_B))),
% 0.21/0.48      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.48  thf('16', plain,
% 0.21/0.48      ((~ (l1_orders_2 @ sk_A) | (r6_relat_2 @ (u1_orders_2 @ sk_A) @ sk_B))),
% 0.21/0.48      inference('sup-', [status(thm)], ['12', '15'])).
% 0.21/0.48  thf('17', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('18', plain, ((r6_relat_2 @ (u1_orders_2 @ sk_A) @ sk_B)),
% 0.21/0.48      inference('demod', [status(thm)], ['16', '17'])).
% 0.21/0.48  thf('19', plain,
% 0.21/0.48      ((~ (v1_relat_1 @ (u1_orders_2 @ sk_A))
% 0.21/0.48        | (r7_relat_2 @ (u1_orders_2 @ sk_A) @ sk_B))),
% 0.21/0.48      inference('demod', [status(thm)], ['11', '18'])).
% 0.21/0.48  thf('20', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(d11_orders_2, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( l1_orders_2 @ A ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.48           ( ( v6_orders_2 @ B @ A ) <=>
% 0.21/0.48             ( r7_relat_2 @ ( u1_orders_2 @ A ) @ B ) ) ) ) ))).
% 0.21/0.48  thf('21', plain,
% 0.21/0.48      (![X6 : $i, X7 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.21/0.48          | ~ (r7_relat_2 @ (u1_orders_2 @ X7) @ X6)
% 0.21/0.48          | (v6_orders_2 @ X6 @ X7)
% 0.21/0.48          | ~ (l1_orders_2 @ X7))),
% 0.21/0.48      inference('cnf', [status(esa)], [d11_orders_2])).
% 0.21/0.48  thf('22', plain,
% 0.21/0.48      ((~ (l1_orders_2 @ sk_A)
% 0.21/0.48        | (v6_orders_2 @ sk_B @ sk_A)
% 0.21/0.48        | ~ (r7_relat_2 @ (u1_orders_2 @ sk_A) @ sk_B))),
% 0.21/0.48      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.48  thf('23', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('24', plain,
% 0.21/0.48      (((v6_orders_2 @ sk_B @ sk_A)
% 0.21/0.48        | ~ (r7_relat_2 @ (u1_orders_2 @ sk_A) @ sk_B))),
% 0.21/0.48      inference('demod', [status(thm)], ['22', '23'])).
% 0.21/0.48  thf('25', plain,
% 0.21/0.48      ((~ (v6_orders_2 @ sk_B @ sk_A)
% 0.21/0.48        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('26', plain,
% 0.21/0.48      ((~ (v6_orders_2 @ sk_B @ sk_A)) <= (~ ((v6_orders_2 @ sk_B @ sk_A)))),
% 0.21/0.48      inference('split', [status(esa)], ['25'])).
% 0.21/0.48  thf('27', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('28', plain,
% 0.21/0.48      ((~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.21/0.48         <= (~ ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.48      inference('split', [status(esa)], ['25'])).
% 0.21/0.48  thf('29', plain,
% 0.21/0.48      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.48  thf('30', plain,
% 0.21/0.48      (~ ((v6_orders_2 @ sk_B @ sk_A)) | 
% 0.21/0.48       ~ ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.48      inference('split', [status(esa)], ['25'])).
% 0.21/0.48  thf('31', plain, (~ ((v6_orders_2 @ sk_B @ sk_A))),
% 0.21/0.48      inference('sat_resolution*', [status(thm)], ['29', '30'])).
% 0.21/0.48  thf('32', plain, (~ (v6_orders_2 @ sk_B @ sk_A)),
% 0.21/0.48      inference('simpl_trail', [status(thm)], ['26', '31'])).
% 0.21/0.48  thf('33', plain, (~ (r7_relat_2 @ (u1_orders_2 @ sk_A) @ sk_B)),
% 0.21/0.48      inference('clc', [status(thm)], ['24', '32'])).
% 0.21/0.48  thf('34', plain, (~ (v1_relat_1 @ (u1_orders_2 @ sk_A))),
% 0.21/0.48      inference('clc', [status(thm)], ['19', '33'])).
% 0.21/0.48  thf('35', plain, (~ (l1_orders_2 @ sk_A)),
% 0.21/0.48      inference('sup-', [status(thm)], ['2', '34'])).
% 0.21/0.48  thf('36', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('37', plain, ($false), inference('demod', [status(thm)], ['35', '36'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
