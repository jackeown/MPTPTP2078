%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.otYN8PYRwm

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:56 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   58 (  75 expanded)
%              Number of leaves         :   24 (  34 expanded)
%              Depth                    :    8
%              Number of atoms          :  321 ( 524 expanded)
%              Number of equality atoms :   16 (  32 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(v1_tex_2_type,type,(
    v1_tex_2: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_orders_2_type,type,(
    v1_orders_2: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(k1_yellow_1_type,type,(
    k1_yellow_1: $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(t15_tex_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ~ ( ( ( u1_struct_0 @ B )
                = ( u1_struct_0 @ A ) )
              & ( v1_tex_2 @ B @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_pre_topc @ B @ A )
           => ~ ( ( ( u1_struct_0 @ B )
                  = ( u1_struct_0 @ A ) )
                & ( v1_tex_2 @ B @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t15_tex_2])).

thf('0',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_pre_topc @ X7 @ X8 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X7 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('2',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf('6',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tex_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ( v1_tex_2 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( C
                    = ( u1_struct_0 @ B ) )
                 => ( v1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )).

thf('7',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X9 @ X10 )
      | ~ ( v1_tex_2 @ X9 @ X10 )
      | ( X11
       != ( u1_struct_0 @ X9 ) )
      | ( v1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('8',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X9 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( v1_subset_1 @ ( u1_struct_0 @ X9 ) @ ( u1_struct_0 @ X10 ) )
      | ~ ( v1_tex_2 @ X9 @ X10 )
      | ~ ( m1_pre_topc @ X9 @ X10 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( v1_tex_2 @ X0 @ sk_A )
      | ( v1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( v1_tex_2 @ X0 @ sk_A )
      | ( v1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,
    ( ( v1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_tex_2 @ sk_B @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['5','12'])).

thf('14',plain,(
    v1_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('17',plain,(
    ! [X2: $i] :
      ( ( l1_struct_0 @ X2 )
      | ~ ( l1_orders_2 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf(t1_yellow_1,axiom,(
    ! [A: $i] :
      ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) )
        = ( k1_yellow_1 @ A ) )
      & ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) )
        = A ) ) )).

thf('18',plain,(
    ! [X5: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X5 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf(fc12_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ~ ( v1_subset_1 @ ( k2_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) )).

thf('19',plain,(
    ! [X1: $i] :
      ( ~ ( v1_subset_1 @ ( k2_struct_0 @ X1 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc12_struct_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v1_subset_1 @ ( k2_struct_0 @ ( k2_yellow_1 @ X0 ) ) @ X0 )
      | ~ ( l1_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X2: $i] :
      ( ( l1_struct_0 @ X2 )
      | ~ ( l1_orders_2 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('23',plain,(
    ! [X5: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X5 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ ( k2_yellow_1 @ X0 ) )
        = X0 )
      | ~ ( l1_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ( ( k2_struct_0 @ ( k2_yellow_1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf(dt_k2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) )).

thf('26',plain,(
    ! [X4: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k2_struct_0 @ ( k2_yellow_1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v1_subset_1 @ X0 @ X0 )
      | ~ ( l1_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['20','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v1_subset_1 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','28'])).

thf('30',plain,(
    ! [X4: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('31',plain,(
    ! [X0: $i] :
      ~ ( v1_subset_1 @ X0 @ X0 ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    $false ),
    inference('sup-',[status(thm)],['16','31'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.otYN8PYRwm
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:13:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.49  % Solved by: fo/fo7.sh
% 0.22/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.49  % done 43 iterations in 0.027s
% 0.22/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.49  % SZS output start Refutation
% 0.22/0.49  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.22/0.49  thf(v1_tex_2_type, type, v1_tex_2: $i > $i > $o).
% 0.22/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.49  thf(v1_orders_2_type, type, v1_orders_2: $i > $o).
% 0.22/0.49  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.22/0.49  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.22/0.49  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.22/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.49  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.22/0.49  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.49  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.22/0.49  thf(k1_yellow_1_type, type, k1_yellow_1: $i > $i).
% 0.22/0.49  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.22/0.49  thf(t15_tex_2, conjecture,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( l1_pre_topc @ A ) =>
% 0.22/0.49       ( ![B:$i]:
% 0.22/0.49         ( ( m1_pre_topc @ B @ A ) =>
% 0.22/0.49           ( ~( ( ( u1_struct_0 @ B ) = ( u1_struct_0 @ A ) ) & 
% 0.22/0.49                ( v1_tex_2 @ B @ A ) ) ) ) ) ))).
% 0.22/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.49    (~( ![A:$i]:
% 0.22/0.49        ( ( l1_pre_topc @ A ) =>
% 0.22/0.49          ( ![B:$i]:
% 0.22/0.49            ( ( m1_pre_topc @ B @ A ) =>
% 0.22/0.49              ( ~( ( ( u1_struct_0 @ B ) = ( u1_struct_0 @ A ) ) & 
% 0.22/0.49                   ( v1_tex_2 @ B @ A ) ) ) ) ) ) )),
% 0.22/0.49    inference('cnf.neg', [status(esa)], [t15_tex_2])).
% 0.22/0.49  thf('0', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(t1_tsep_1, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( l1_pre_topc @ A ) =>
% 0.22/0.49       ( ![B:$i]:
% 0.22/0.49         ( ( m1_pre_topc @ B @ A ) =>
% 0.22/0.49           ( m1_subset_1 @
% 0.22/0.49             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.22/0.49  thf('1', plain,
% 0.22/0.49      (![X7 : $i, X8 : $i]:
% 0.22/0.49         (~ (m1_pre_topc @ X7 @ X8)
% 0.22/0.49          | (m1_subset_1 @ (u1_struct_0 @ X7) @ 
% 0.22/0.49             (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.22/0.49          | ~ (l1_pre_topc @ X8))),
% 0.22/0.49      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.22/0.49  thf('2', plain,
% 0.22/0.49      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.49        | (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.22/0.49           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['0', '1'])).
% 0.22/0.49  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('4', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('5', plain,
% 0.22/0.49      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.22/0.49        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.22/0.49      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.22/0.49  thf('6', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(d3_tex_2, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( l1_pre_topc @ A ) =>
% 0.22/0.49       ( ![B:$i]:
% 0.22/0.49         ( ( m1_pre_topc @ B @ A ) =>
% 0.22/0.49           ( ( v1_tex_2 @ B @ A ) <=>
% 0.22/0.49             ( ![C:$i]:
% 0.22/0.49               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.49                 ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.22/0.49                   ( v1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.22/0.49  thf('7', plain,
% 0.22/0.49      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.22/0.49         (~ (m1_pre_topc @ X9 @ X10)
% 0.22/0.49          | ~ (v1_tex_2 @ X9 @ X10)
% 0.22/0.49          | ((X11) != (u1_struct_0 @ X9))
% 0.22/0.49          | (v1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 0.22/0.49          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.22/0.49          | ~ (l1_pre_topc @ X10))),
% 0.22/0.49      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.22/0.49  thf('8', plain,
% 0.22/0.49      (![X9 : $i, X10 : $i]:
% 0.22/0.49         (~ (l1_pre_topc @ X10)
% 0.22/0.49          | ~ (m1_subset_1 @ (u1_struct_0 @ X9) @ 
% 0.22/0.49               (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.22/0.49          | (v1_subset_1 @ (u1_struct_0 @ X9) @ (u1_struct_0 @ X10))
% 0.22/0.49          | ~ (v1_tex_2 @ X9 @ X10)
% 0.22/0.49          | ~ (m1_pre_topc @ X9 @ X10))),
% 0.22/0.49      inference('simplify', [status(thm)], ['7'])).
% 0.22/0.49  thf('9', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (~ (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.22/0.49             (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.22/0.49          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.22/0.49          | ~ (v1_tex_2 @ X0 @ sk_A)
% 0.22/0.49          | (v1_subset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 0.22/0.49          | ~ (l1_pre_topc @ sk_A))),
% 0.22/0.49      inference('sup-', [status(thm)], ['6', '8'])).
% 0.22/0.49  thf('10', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('12', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (~ (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.22/0.49             (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.22/0.49          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.22/0.49          | ~ (v1_tex_2 @ X0 @ sk_A)
% 0.22/0.49          | (v1_subset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 0.22/0.49      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.22/0.49  thf('13', plain,
% 0.22/0.49      (((v1_subset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_B))
% 0.22/0.49        | ~ (v1_tex_2 @ sk_B @ sk_A)
% 0.22/0.49        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 0.22/0.49      inference('sup-', [status(thm)], ['5', '12'])).
% 0.22/0.49  thf('14', plain, ((v1_tex_2 @ sk_B @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('15', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('16', plain,
% 0.22/0.49      ((v1_subset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_B))),
% 0.22/0.49      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.22/0.49  thf(dt_l1_orders_2, axiom,
% 0.22/0.49    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 0.22/0.49  thf('17', plain, (![X2 : $i]: ((l1_struct_0 @ X2) | ~ (l1_orders_2 @ X2))),
% 0.22/0.49      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 0.22/0.49  thf(t1_yellow_1, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) ) = ( k1_yellow_1 @ A ) ) & 
% 0.22/0.49       ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) = ( A ) ) ))).
% 0.22/0.49  thf('18', plain, (![X5 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X5)) = (X5))),
% 0.22/0.49      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.22/0.49  thf(fc12_struct_0, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( l1_struct_0 @ A ) =>
% 0.22/0.49       ( ~( v1_subset_1 @ ( k2_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ))).
% 0.22/0.49  thf('19', plain,
% 0.22/0.49      (![X1 : $i]:
% 0.22/0.49         (~ (v1_subset_1 @ (k2_struct_0 @ X1) @ (u1_struct_0 @ X1))
% 0.22/0.49          | ~ (l1_struct_0 @ X1))),
% 0.22/0.49      inference('cnf', [status(esa)], [fc12_struct_0])).
% 0.22/0.49  thf('20', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (~ (v1_subset_1 @ (k2_struct_0 @ (k2_yellow_1 @ X0)) @ X0)
% 0.22/0.49          | ~ (l1_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['18', '19'])).
% 0.22/0.49  thf('21', plain, (![X2 : $i]: ((l1_struct_0 @ X2) | ~ (l1_orders_2 @ X2))),
% 0.22/0.49      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 0.22/0.49  thf(d3_struct_0, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.22/0.49  thf('22', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (((k2_struct_0 @ X0) = (u1_struct_0 @ X0)) | ~ (l1_struct_0 @ X0))),
% 0.22/0.49      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.22/0.49  thf('23', plain, (![X5 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X5)) = (X5))),
% 0.22/0.49      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.22/0.49  thf('24', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (((k2_struct_0 @ (k2_yellow_1 @ X0)) = (X0))
% 0.22/0.49          | ~ (l1_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.22/0.49      inference('sup+', [status(thm)], ['22', '23'])).
% 0.22/0.49  thf('25', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (~ (l1_orders_2 @ (k2_yellow_1 @ X0))
% 0.22/0.49          | ((k2_struct_0 @ (k2_yellow_1 @ X0)) = (X0)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['21', '24'])).
% 0.22/0.49  thf(dt_k2_yellow_1, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.22/0.49       ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ))).
% 0.22/0.49  thf('26', plain, (![X4 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X4))),
% 0.22/0.49      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.22/0.49  thf('27', plain, (![X0 : $i]: ((k2_struct_0 @ (k2_yellow_1 @ X0)) = (X0))),
% 0.22/0.49      inference('demod', [status(thm)], ['25', '26'])).
% 0.22/0.49  thf('28', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (~ (v1_subset_1 @ X0 @ X0) | ~ (l1_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.22/0.49      inference('demod', [status(thm)], ['20', '27'])).
% 0.22/0.49  thf('29', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (~ (l1_orders_2 @ (k2_yellow_1 @ X0)) | ~ (v1_subset_1 @ X0 @ X0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['17', '28'])).
% 0.22/0.49  thf('30', plain, (![X4 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X4))),
% 0.22/0.49      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.22/0.49  thf('31', plain, (![X0 : $i]: ~ (v1_subset_1 @ X0 @ X0)),
% 0.22/0.49      inference('demod', [status(thm)], ['29', '30'])).
% 0.22/0.49  thf('32', plain, ($false), inference('sup-', [status(thm)], ['16', '31'])).
% 0.22/0.49  
% 0.22/0.49  % SZS output end Refutation
% 0.22/0.49  
% 0.22/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
