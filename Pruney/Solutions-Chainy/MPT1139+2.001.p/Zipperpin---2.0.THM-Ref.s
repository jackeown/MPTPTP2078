%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QhnmBjJatO

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:36 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   49 (  79 expanded)
%              Number of leaves         :   12 (  28 expanded)
%              Depth                    :    9
%              Number of atoms          :  359 ( 961 expanded)
%              Number of equality atoms :    8 (  10 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_orders_2_type,type,(
    r2_orders_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t28_orders_2,conjecture,(
    ! [A: $i] :
      ( ( ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ~ ( ( r2_orders_2 @ A @ B @ C )
                  & ( r2_orders_2 @ A @ C @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v5_orders_2 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ~ ( ( r2_orders_2 @ A @ B @ C )
                    & ( r2_orders_2 @ A @ C @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t28_orders_2])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r2_orders_2 @ A @ B @ C )
              <=> ( ( r1_orders_2 @ A @ B @ C )
                  & ( B != C ) ) ) ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r2_orders_2 @ X1 @ X0 @ X2 )
      | ( X0 != X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d10_orders_2])).

thf('2',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X1 )
      | ~ ( r2_orders_2 @ X1 @ X2 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,
    ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_B )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf('4',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    r2_orders_2 @ sk_A @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t25_orders_2,axiom,(
    ! [A: $i] :
      ( ( ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( ( r1_orders_2 @ A @ B @ C )
                  & ( r1_orders_2 @ A @ C @ B ) )
               => ( B = C ) ) ) ) ) )).

thf('9',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X4 ) )
      | ~ ( r1_orders_2 @ X4 @ X3 @ X5 )
      | ~ ( r1_orders_2 @ X4 @ X5 @ X3 )
      | ( X3 = X5 )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X4 ) )
      | ~ ( l1_orders_2 @ X4 )
      | ~ ( v5_orders_2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t25_orders_2])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( sk_B = X0 )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( sk_B = X0 )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('14',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_C )
    | ~ ( r1_orders_2 @ sk_A @ sk_C @ sk_B )
    | ( sk_B = sk_C ) ),
    inference('sup-',[status(thm)],['7','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r2_orders_2 @ X1 @ X0 @ X2 )
      | ( r1_orders_2 @ X1 @ X0 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d10_orders_2])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( r2_orders_2 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( r2_orders_2 @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
    | ( r1_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['15','20'])).

thf('22',plain,(
    r2_orders_2 @ sk_A @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    r1_orders_2 @ sk_A @ sk_B @ sk_C ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r2_orders_2 @ X1 @ X0 @ X2 )
      | ( r1_orders_2 @ X1 @ X0 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d10_orders_2])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_C @ X0 )
      | ~ ( r2_orders_2 @ sk_A @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_C @ X0 )
      | ~ ( r2_orders_2 @ sk_A @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ~ ( r2_orders_2 @ sk_A @ sk_C @ sk_B )
    | ( r1_orders_2 @ sk_A @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['24','29'])).

thf('31',plain,(
    r2_orders_2 @ sk_A @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    r1_orders_2 @ sk_A @ sk_C @ sk_B ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    sk_B = sk_C ),
    inference(demod,[status(thm)],['14','23','32'])).

thf('34',plain,(
    r2_orders_2 @ sk_A @ sk_B @ sk_B ),
    inference(demod,[status(thm)],['6','33'])).

thf('35',plain,(
    $false ),
    inference(demod,[status(thm)],['5','34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QhnmBjJatO
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:21:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.22/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.48  % Solved by: fo/fo7.sh
% 0.22/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.48  % done 24 iterations in 0.015s
% 0.22/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.48  % SZS output start Refutation
% 0.22/0.48  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.22/0.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.48  thf(r2_orders_2_type, type, r2_orders_2: $i > $i > $i > $o).
% 0.22/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.48  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.22/0.48  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.22/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.48  thf(t28_orders_2, conjecture,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ( ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.22/0.48       ( ![B:$i]:
% 0.22/0.48         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.48           ( ![C:$i]:
% 0.22/0.48             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.48               ( ~( ( r2_orders_2 @ A @ B @ C ) & ( r2_orders_2 @ A @ C @ B ) ) ) ) ) ) ) ))).
% 0.22/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.48    (~( ![A:$i]:
% 0.22/0.48        ( ( ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.22/0.48          ( ![B:$i]:
% 0.22/0.48            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.48              ( ![C:$i]:
% 0.22/0.48                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.48                  ( ~( ( r2_orders_2 @ A @ B @ C ) & 
% 0.22/0.48                       ( r2_orders_2 @ A @ C @ B ) ) ) ) ) ) ) ) )),
% 0.22/0.48    inference('cnf.neg', [status(esa)], [t28_orders_2])).
% 0.22/0.48  thf('0', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf(d10_orders_2, axiom,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ( l1_orders_2 @ A ) =>
% 0.22/0.48       ( ![B:$i]:
% 0.22/0.48         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.48           ( ![C:$i]:
% 0.22/0.48             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.48               ( ( r2_orders_2 @ A @ B @ C ) <=>
% 0.22/0.48                 ( ( r1_orders_2 @ A @ B @ C ) & ( ( B ) != ( C ) ) ) ) ) ) ) ) ))).
% 0.22/0.48  thf('1', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.48         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 0.22/0.48          | ~ (r2_orders_2 @ X1 @ X0 @ X2)
% 0.22/0.48          | ((X0) != (X2))
% 0.22/0.48          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.22/0.48          | ~ (l1_orders_2 @ X1))),
% 0.22/0.48      inference('cnf', [status(esa)], [d10_orders_2])).
% 0.22/0.48  thf('2', plain,
% 0.22/0.48      (![X1 : $i, X2 : $i]:
% 0.22/0.48         (~ (l1_orders_2 @ X1)
% 0.22/0.48          | ~ (r2_orders_2 @ X1 @ X2 @ X2)
% 0.22/0.48          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1)))),
% 0.22/0.48      inference('simplify', [status(thm)], ['1'])).
% 0.22/0.48  thf('3', plain,
% 0.22/0.48      ((~ (r2_orders_2 @ sk_A @ sk_B @ sk_B) | ~ (l1_orders_2 @ sk_A))),
% 0.22/0.48      inference('sup-', [status(thm)], ['0', '2'])).
% 0.22/0.48  thf('4', plain, ((l1_orders_2 @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('5', plain, (~ (r2_orders_2 @ sk_A @ sk_B @ sk_B)),
% 0.22/0.48      inference('demod', [status(thm)], ['3', '4'])).
% 0.22/0.48  thf('6', plain, ((r2_orders_2 @ sk_A @ sk_B @ sk_C)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('7', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('8', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf(t25_orders_2, axiom,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ( ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.22/0.48       ( ![B:$i]:
% 0.22/0.48         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.48           ( ![C:$i]:
% 0.22/0.48             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.48               ( ( ( r1_orders_2 @ A @ B @ C ) & ( r1_orders_2 @ A @ C @ B ) ) =>
% 0.22/0.48                 ( ( B ) = ( C ) ) ) ) ) ) ) ))).
% 0.22/0.48  thf('9', plain,
% 0.22/0.48      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.22/0.48         (~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X4))
% 0.22/0.48          | ~ (r1_orders_2 @ X4 @ X3 @ X5)
% 0.22/0.48          | ~ (r1_orders_2 @ X4 @ X5 @ X3)
% 0.22/0.48          | ((X3) = (X5))
% 0.22/0.48          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X4))
% 0.22/0.48          | ~ (l1_orders_2 @ X4)
% 0.22/0.48          | ~ (v5_orders_2 @ X4))),
% 0.22/0.48      inference('cnf', [status(esa)], [t25_orders_2])).
% 0.22/0.48  thf('10', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         (~ (v5_orders_2 @ sk_A)
% 0.22/0.48          | ~ (l1_orders_2 @ sk_A)
% 0.22/0.48          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.22/0.48          | ((sk_B) = (X0))
% 0.22/0.48          | ~ (r1_orders_2 @ sk_A @ X0 @ sk_B)
% 0.22/0.48          | ~ (r1_orders_2 @ sk_A @ sk_B @ X0))),
% 0.22/0.48      inference('sup-', [status(thm)], ['8', '9'])).
% 0.22/0.48  thf('11', plain, ((v5_orders_2 @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('12', plain, ((l1_orders_2 @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('13', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.22/0.48          | ((sk_B) = (X0))
% 0.22/0.48          | ~ (r1_orders_2 @ sk_A @ X0 @ sk_B)
% 0.22/0.48          | ~ (r1_orders_2 @ sk_A @ sk_B @ X0))),
% 0.22/0.48      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.22/0.48  thf('14', plain,
% 0.22/0.48      ((~ (r1_orders_2 @ sk_A @ sk_B @ sk_C)
% 0.22/0.48        | ~ (r1_orders_2 @ sk_A @ sk_C @ sk_B)
% 0.22/0.48        | ((sk_B) = (sk_C)))),
% 0.22/0.48      inference('sup-', [status(thm)], ['7', '13'])).
% 0.22/0.48  thf('15', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('16', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('17', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.48         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 0.22/0.48          | ~ (r2_orders_2 @ X1 @ X0 @ X2)
% 0.22/0.48          | (r1_orders_2 @ X1 @ X0 @ X2)
% 0.22/0.48          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.22/0.48          | ~ (l1_orders_2 @ X1))),
% 0.22/0.48      inference('cnf', [status(esa)], [d10_orders_2])).
% 0.22/0.48  thf('18', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         (~ (l1_orders_2 @ sk_A)
% 0.22/0.48          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.22/0.48          | (r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.22/0.48          | ~ (r2_orders_2 @ sk_A @ sk_B @ X0))),
% 0.22/0.48      inference('sup-', [status(thm)], ['16', '17'])).
% 0.22/0.48  thf('19', plain, ((l1_orders_2 @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('20', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.22/0.48          | (r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.22/0.48          | ~ (r2_orders_2 @ sk_A @ sk_B @ X0))),
% 0.22/0.48      inference('demod', [status(thm)], ['18', '19'])).
% 0.22/0.48  thf('21', plain,
% 0.22/0.48      ((~ (r2_orders_2 @ sk_A @ sk_B @ sk_C)
% 0.22/0.48        | (r1_orders_2 @ sk_A @ sk_B @ sk_C))),
% 0.22/0.48      inference('sup-', [status(thm)], ['15', '20'])).
% 0.22/0.48  thf('22', plain, ((r2_orders_2 @ sk_A @ sk_B @ sk_C)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('23', plain, ((r1_orders_2 @ sk_A @ sk_B @ sk_C)),
% 0.22/0.48      inference('demod', [status(thm)], ['21', '22'])).
% 0.22/0.48  thf('24', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('25', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('26', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.48         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 0.22/0.48          | ~ (r2_orders_2 @ X1 @ X0 @ X2)
% 0.22/0.48          | (r1_orders_2 @ X1 @ X0 @ X2)
% 0.22/0.48          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.22/0.48          | ~ (l1_orders_2 @ X1))),
% 0.22/0.48      inference('cnf', [status(esa)], [d10_orders_2])).
% 0.22/0.48  thf('27', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         (~ (l1_orders_2 @ sk_A)
% 0.22/0.48          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.22/0.48          | (r1_orders_2 @ sk_A @ sk_C @ X0)
% 0.22/0.48          | ~ (r2_orders_2 @ sk_A @ sk_C @ X0))),
% 0.22/0.48      inference('sup-', [status(thm)], ['25', '26'])).
% 0.22/0.48  thf('28', plain, ((l1_orders_2 @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('29', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.22/0.48          | (r1_orders_2 @ sk_A @ sk_C @ X0)
% 0.22/0.48          | ~ (r2_orders_2 @ sk_A @ sk_C @ X0))),
% 0.22/0.48      inference('demod', [status(thm)], ['27', '28'])).
% 0.22/0.48  thf('30', plain,
% 0.22/0.48      ((~ (r2_orders_2 @ sk_A @ sk_C @ sk_B)
% 0.22/0.48        | (r1_orders_2 @ sk_A @ sk_C @ sk_B))),
% 0.22/0.48      inference('sup-', [status(thm)], ['24', '29'])).
% 0.22/0.48  thf('31', plain, ((r2_orders_2 @ sk_A @ sk_C @ sk_B)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('32', plain, ((r1_orders_2 @ sk_A @ sk_C @ sk_B)),
% 0.22/0.48      inference('demod', [status(thm)], ['30', '31'])).
% 0.22/0.48  thf('33', plain, (((sk_B) = (sk_C))),
% 0.22/0.48      inference('demod', [status(thm)], ['14', '23', '32'])).
% 0.22/0.48  thf('34', plain, ((r2_orders_2 @ sk_A @ sk_B @ sk_B)),
% 0.22/0.48      inference('demod', [status(thm)], ['6', '33'])).
% 0.22/0.48  thf('35', plain, ($false), inference('demod', [status(thm)], ['5', '34'])).
% 0.22/0.48  
% 0.22/0.48  % SZS output end Refutation
% 0.22/0.48  
% 0.22/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
