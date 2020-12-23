%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Fyk4yVBY0H

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:56 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 119 expanded)
%              Number of leaves         :   24 (  49 expanded)
%              Depth                    :   12
%              Number of atoms          :  350 ( 804 expanded)
%              Number of equality atoms :   17 (  46 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(v1_tex_2_type,type,(
    v1_tex_2: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_yellow_1_type,type,(
    k1_yellow_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(v1_orders_2_type,type,(
    v1_orders_2: $i > $o )).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('0',plain,(
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

thf('1',plain,(
    ! [X5: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X5 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf(dt_k2_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( m1_subset_1 @ ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ ( k2_yellow_1 @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( l1_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ( m1_subset_1 @ ( k2_struct_0 @ ( k2_yellow_1 @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf(dt_k2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) )).

thf('5',plain,(
    ! [X4: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_struct_0 @ ( k2_yellow_1 @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X2: $i] :
      ( ( l1_struct_0 @ X2 )
      | ~ ( l1_orders_2 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf('8',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_struct_0 @ ( k2_yellow_1 @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('9',plain,(
    ! [X10: $i,X11: $i] :
      ( ( X11 = X10 )
      | ( v1_subset_1 @ X11 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( v1_subset_1 @ ( k2_struct_0 @ ( k2_yellow_1 @ X0 ) ) @ X0 )
      | ( ( k2_struct_0 @ ( k2_yellow_1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X5: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X5 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf(fc12_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ~ ( v1_subset_1 @ ( k2_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) )).

thf('12',plain,(
    ! [X1: $i] :
      ( ~ ( v1_subset_1 @ ( k2_struct_0 @ X1 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc12_struct_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v1_subset_1 @ ( k2_struct_0 @ ( k2_yellow_1 @ X0 ) ) @ X0 )
      | ~ ( l1_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ ( k2_yellow_1 @ X0 ) )
        = X0 )
      | ~ ( l1_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ( ( k2_struct_0 @ ( k2_yellow_1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['7','14'])).

thf('16',plain,(
    ! [X4: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k2_struct_0 @ ( k2_yellow_1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['6','17'])).

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

thf('19',plain,
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

thf('20',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X7 @ X8 )
      | ~ ( v1_tex_2 @ X7 @ X8 )
      | ( X9
       != ( u1_struct_0 @ X7 ) )
      | ( v1_subset_1 @ X9 @ ( u1_struct_0 @ X8 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('21',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( l1_pre_topc @ X8 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X7 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( v1_subset_1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X8 ) )
      | ~ ( v1_tex_2 @ X7 @ X8 )
      | ~ ( m1_pre_topc @ X7 @ X8 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( v1_tex_2 @ X0 @ sk_A )
      | ( v1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( v1_tex_2 @ X0 @ sk_A )
      | ( v1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,
    ( ( v1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_tex_2 @ sk_B @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['18','25'])).

thf('27',plain,(
    v1_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_subset_1 @ X11 @ X10 )
      | ( X11 != X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('31',plain,(
    ! [X10: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( v1_subset_1 @ X10 @ X10 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['6','17'])).

thf('33',plain,(
    ! [X10: $i] :
      ~ ( v1_subset_1 @ X10 @ X10 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    $false ),
    inference('sup-',[status(thm)],['29','33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Fyk4yVBY0H
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:32:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 39 iterations in 0.022s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.48  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.48  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.21/0.48  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.21/0.48  thf(v1_tex_2_type, type, v1_tex_2: $i > $i > $o).
% 0.21/0.48  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.21/0.48  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.21/0.48  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.48  thf(k1_yellow_1_type, type, k1_yellow_1: $i > $i).
% 0.21/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.48  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.21/0.48  thf(v1_orders_2_type, type, v1_orders_2: $i > $o).
% 0.21/0.48  thf(dt_l1_orders_2, axiom,
% 0.21/0.48    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.48  thf('0', plain, (![X2 : $i]: ((l1_struct_0 @ X2) | ~ (l1_orders_2 @ X2))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 0.21/0.48  thf(t1_yellow_1, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) ) = ( k1_yellow_1 @ A ) ) & 
% 0.21/0.48       ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) = ( A ) ) ))).
% 0.21/0.48  thf('1', plain, (![X5 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X5)) = (X5))),
% 0.21/0.48      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.21/0.48  thf(dt_k2_struct_0, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( l1_struct_0 @ A ) =>
% 0.21/0.48       ( m1_subset_1 @
% 0.21/0.48         ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.48  thf('2', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((m1_subset_1 @ (k2_struct_0 @ X0) @ 
% 0.21/0.48           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.21/0.48          | ~ (l1_struct_0 @ X0))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.21/0.48  thf('3', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((m1_subset_1 @ (k2_struct_0 @ (k2_yellow_1 @ X0)) @ 
% 0.21/0.48           (k1_zfmisc_1 @ X0))
% 0.21/0.48          | ~ (l1_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.21/0.48      inference('sup+', [status(thm)], ['1', '2'])).
% 0.21/0.48  thf('4', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (~ (l1_orders_2 @ (k2_yellow_1 @ X0))
% 0.21/0.48          | (m1_subset_1 @ (k2_struct_0 @ (k2_yellow_1 @ X0)) @ 
% 0.21/0.48             (k1_zfmisc_1 @ X0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['0', '3'])).
% 0.21/0.48  thf(dt_k2_yellow_1, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.21/0.48       ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ))).
% 0.21/0.48  thf('5', plain, (![X4 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X4))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.21/0.48  thf('6', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (m1_subset_1 @ (k2_struct_0 @ (k2_yellow_1 @ X0)) @ (k1_zfmisc_1 @ X0))),
% 0.21/0.48      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.48  thf('7', plain, (![X2 : $i]: ((l1_struct_0 @ X2) | ~ (l1_orders_2 @ X2))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 0.21/0.48  thf('8', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (m1_subset_1 @ (k2_struct_0 @ (k2_yellow_1 @ X0)) @ (k1_zfmisc_1 @ X0))),
% 0.21/0.48      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.48  thf(d7_subset_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.48       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.21/0.48  thf('9', plain,
% 0.21/0.48      (![X10 : $i, X11 : $i]:
% 0.21/0.48         (((X11) = (X10))
% 0.21/0.48          | (v1_subset_1 @ X11 @ X10)
% 0.21/0.48          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X10)))),
% 0.21/0.48      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.21/0.48  thf('10', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((v1_subset_1 @ (k2_struct_0 @ (k2_yellow_1 @ X0)) @ X0)
% 0.21/0.48          | ((k2_struct_0 @ (k2_yellow_1 @ X0)) = (X0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.48  thf('11', plain, (![X5 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X5)) = (X5))),
% 0.21/0.48      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.21/0.48  thf(fc12_struct_0, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( l1_struct_0 @ A ) =>
% 0.21/0.48       ( ~( v1_subset_1 @ ( k2_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.48  thf('12', plain,
% 0.21/0.48      (![X1 : $i]:
% 0.21/0.48         (~ (v1_subset_1 @ (k2_struct_0 @ X1) @ (u1_struct_0 @ X1))
% 0.21/0.48          | ~ (l1_struct_0 @ X1))),
% 0.21/0.48      inference('cnf', [status(esa)], [fc12_struct_0])).
% 0.21/0.48  thf('13', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (~ (v1_subset_1 @ (k2_struct_0 @ (k2_yellow_1 @ X0)) @ X0)
% 0.21/0.48          | ~ (l1_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.48  thf('14', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (((k2_struct_0 @ (k2_yellow_1 @ X0)) = (X0))
% 0.21/0.48          | ~ (l1_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['10', '13'])).
% 0.21/0.48  thf('15', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (~ (l1_orders_2 @ (k2_yellow_1 @ X0))
% 0.21/0.48          | ((k2_struct_0 @ (k2_yellow_1 @ X0)) = (X0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['7', '14'])).
% 0.21/0.48  thf('16', plain, (![X4 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X4))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.21/0.48  thf('17', plain, (![X0 : $i]: ((k2_struct_0 @ (k2_yellow_1 @ X0)) = (X0))),
% 0.21/0.48      inference('demod', [status(thm)], ['15', '16'])).
% 0.21/0.48  thf('18', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.21/0.48      inference('demod', [status(thm)], ['6', '17'])).
% 0.21/0.48  thf(t15_tex_2, conjecture,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( l1_pre_topc @ A ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.48           ( ~( ( ( u1_struct_0 @ B ) = ( u1_struct_0 @ A ) ) & 
% 0.21/0.48                ( v1_tex_2 @ B @ A ) ) ) ) ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i]:
% 0.21/0.48        ( ( l1_pre_topc @ A ) =>
% 0.21/0.48          ( ![B:$i]:
% 0.21/0.48            ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.48              ( ~( ( ( u1_struct_0 @ B ) = ( u1_struct_0 @ A ) ) & 
% 0.21/0.48                   ( v1_tex_2 @ B @ A ) ) ) ) ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t15_tex_2])).
% 0.21/0.48  thf('19', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(d3_tex_2, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( l1_pre_topc @ A ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.48           ( ( v1_tex_2 @ B @ A ) <=>
% 0.21/0.48             ( ![C:$i]:
% 0.21/0.48               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.48                 ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.21/0.48                   ( v1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.21/0.48  thf('20', plain,
% 0.21/0.48      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.48         (~ (m1_pre_topc @ X7 @ X8)
% 0.21/0.48          | ~ (v1_tex_2 @ X7 @ X8)
% 0.21/0.48          | ((X9) != (u1_struct_0 @ X7))
% 0.21/0.48          | (v1_subset_1 @ X9 @ (u1_struct_0 @ X8))
% 0.21/0.48          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.21/0.48          | ~ (l1_pre_topc @ X8))),
% 0.21/0.48      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.21/0.48  thf('21', plain,
% 0.21/0.48      (![X7 : $i, X8 : $i]:
% 0.21/0.48         (~ (l1_pre_topc @ X8)
% 0.21/0.48          | ~ (m1_subset_1 @ (u1_struct_0 @ X7) @ 
% 0.21/0.48               (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.21/0.48          | (v1_subset_1 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X8))
% 0.21/0.48          | ~ (v1_tex_2 @ X7 @ X8)
% 0.21/0.48          | ~ (m1_pre_topc @ X7 @ X8))),
% 0.21/0.48      inference('simplify', [status(thm)], ['20'])).
% 0.21/0.48  thf('22', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.21/0.48             (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.21/0.48          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.21/0.48          | ~ (v1_tex_2 @ X0 @ sk_A)
% 0.21/0.48          | (v1_subset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 0.21/0.48          | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['19', '21'])).
% 0.21/0.48  thf('23', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('25', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.21/0.48             (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.21/0.48          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.21/0.48          | ~ (v1_tex_2 @ X0 @ sk_A)
% 0.21/0.48          | (v1_subset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 0.21/0.48      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.21/0.48  thf('26', plain,
% 0.21/0.48      (((v1_subset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_B))
% 0.21/0.48        | ~ (v1_tex_2 @ sk_B @ sk_A)
% 0.21/0.48        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['18', '25'])).
% 0.21/0.48  thf('27', plain, ((v1_tex_2 @ sk_B @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('28', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('29', plain,
% 0.21/0.48      ((v1_subset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_B))),
% 0.21/0.48      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.21/0.48  thf('30', plain,
% 0.21/0.48      (![X10 : $i, X11 : $i]:
% 0.21/0.48         (~ (v1_subset_1 @ X11 @ X10)
% 0.21/0.48          | ((X11) != (X10))
% 0.21/0.48          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X10)))),
% 0.21/0.48      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.21/0.48  thf('31', plain,
% 0.21/0.48      (![X10 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X10))
% 0.21/0.48          | ~ (v1_subset_1 @ X10 @ X10))),
% 0.21/0.48      inference('simplify', [status(thm)], ['30'])).
% 0.21/0.48  thf('32', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.21/0.48      inference('demod', [status(thm)], ['6', '17'])).
% 0.21/0.48  thf('33', plain, (![X10 : $i]: ~ (v1_subset_1 @ X10 @ X10)),
% 0.21/0.48      inference('demod', [status(thm)], ['31', '32'])).
% 0.21/0.48  thf('34', plain, ($false), inference('sup-', [status(thm)], ['29', '33'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
