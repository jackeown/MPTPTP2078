%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2xmyALc7oD

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:30 EST 2020

% Result     : Theorem 0.62s
% Output     : Refutation 0.62s
% Verified   : 
% Statistics : Number of formulae       :   56 (  84 expanded)
%              Number of leaves         :   21 (  35 expanded)
%              Depth                    :   10
%              Number of atoms          :  426 (1182 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_lattices_type,type,(
    k1_lattices: $i > $i > $i > $i )).

thf(v5_lattices_type,type,(
    v5_lattices: $i > $o )).

thf(v8_lattices_type,type,(
    v8_lattices: $i > $o )).

thf(v9_lattices_type,type,(
    v9_lattices: $i > $o )).

thf(k2_lattices_type,type,(
    k2_lattices: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r1_lattices_type,type,(
    r1_lattices: $i > $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v6_lattices_type,type,(
    v6_lattices: $i > $o )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(l1_lattices_type,type,(
    l1_lattices: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(l2_lattices_type,type,(
    l2_lattices: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t22_lattices,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v5_lattices @ A )
        & ( v6_lattices @ A )
        & ( v8_lattices @ A )
        & ( v9_lattices @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( r1_lattices @ A @ B @ ( k1_lattices @ A @ B @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v5_lattices @ A )
          & ( v6_lattices @ A )
          & ( v8_lattices @ A )
          & ( v9_lattices @ A )
          & ( l3_lattices @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ( r1_lattices @ A @ B @ ( k1_lattices @ A @ B @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t22_lattices])).

thf('0',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A ) )
     => ( ( v9_lattices @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ( ( k2_lattices @ A @ B @ ( k1_lattices @ A @ B @ C ) )
                  = B ) ) ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v9_lattices @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( ( k2_lattices @ X0 @ X2 @ ( k1_lattices @ X0 @ X2 @ X1 ) )
        = X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d9_lattices])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ X0 @ ( k1_lattices @ sk_A @ X0 @ sk_C_1 ) )
        = X0 )
      | ~ ( v9_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v9_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ X0 @ ( k1_lattices @ sk_A @ X0 @ sk_C_1 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( ( k2_lattices @ sk_A @ X0 @ ( k1_lattices @ sk_A @ X0 @ sk_C_1 ) )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('9',plain,
    ( ( k2_lattices @ sk_A @ sk_B_1 @ ( k1_lattices @ sk_A @ sk_B_1 @ sk_C_1 ) )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['0','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_lattices,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l2_lattices @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( m1_subset_1 @ ( k1_lattices @ A @ B @ C ) @ ( u1_struct_0 @ A ) ) ) )).

thf('12',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X4 ) )
      | ~ ( l2_lattices @ X4 )
      | ( v2_struct_0 @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X4 ) )
      | ( m1_subset_1 @ ( k1_lattices @ X4 @ X3 @ X5 ) @ ( u1_struct_0 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_lattices])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k1_lattices @ sk_A @ sk_B_1 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l2_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l3_lattices,axiom,(
    ! [A: $i] :
      ( ( l3_lattices @ A )
     => ( ( l1_lattices @ A )
        & ( l2_lattices @ A ) ) ) )).

thf('15',plain,(
    ! [X6: $i] :
      ( ( l2_lattices @ X6 )
      | ~ ( l3_lattices @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('16',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k1_lattices @ sk_A @ sk_B_1 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','16'])).

thf('18',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_subset_1 @ ( k1_lattices @ sk_A @ sk_B_1 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ ( k1_lattices @ sk_A @ sk_B_1 @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['10','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t21_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v8_lattices @ A )
        & ( v9_lattices @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r1_lattices @ A @ B @ C )
              <=> ( ( k2_lattices @ A @ B @ C )
                  = B ) ) ) ) ) )).

thf('22',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X8 ) )
      | ( ( k2_lattices @ X8 @ X7 @ X9 )
       != X7 )
      | ( r1_lattices @ X8 @ X7 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l3_lattices @ X8 )
      | ~ ( v9_lattices @ X8 )
      | ~ ( v8_lattices @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t21_lattices])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v8_lattices @ sk_A )
      | ~ ( v9_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ sk_B_1 @ X0 )
      | ( ( k2_lattices @ sk_A @ sk_B_1 @ X0 )
       != sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v8_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v9_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ sk_B_1 @ X0 )
      | ( ( k2_lattices @ sk_A @ sk_B_1 @ X0 )
       != sk_B_1 ) ) ),
    inference(demod,[status(thm)],['23','24','25','26'])).

thf('28',plain,
    ( ( ( k2_lattices @ sk_A @ sk_B_1 @ ( k1_lattices @ sk_A @ sk_B_1 @ sk_C_1 ) )
     != sk_B_1 )
    | ( r1_lattices @ sk_A @ sk_B_1 @ ( k1_lattices @ sk_A @ sk_B_1 @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','27'])).

thf('29',plain,(
    ~ ( r1_lattices @ sk_A @ sk_B_1 @ ( k1_lattices @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_lattices @ sk_A @ sk_B_1 @ ( k1_lattices @ sk_A @ sk_B_1 @ sk_C_1 ) )
     != sk_B_1 ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('31',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ( k2_lattices @ sk_A @ sk_B_1 @ ( k1_lattices @ sk_A @ sk_B_1 @ sk_C_1 ) )
 != sk_B_1 ),
    inference(clc,[status(thm)],['30','31'])).

thf('33',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['9','32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2xmyALc7oD
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:38:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.62/0.82  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.62/0.82  % Solved by: fo/fo7.sh
% 0.62/0.82  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.62/0.82  % done 140 iterations in 0.356s
% 0.62/0.82  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.62/0.82  % SZS output start Refutation
% 0.62/0.82  thf(k1_lattices_type, type, k1_lattices: $i > $i > $i > $i).
% 0.62/0.82  thf(v5_lattices_type, type, v5_lattices: $i > $o).
% 0.62/0.82  thf(v8_lattices_type, type, v8_lattices: $i > $o).
% 0.62/0.82  thf(v9_lattices_type, type, v9_lattices: $i > $o).
% 0.62/0.82  thf(k2_lattices_type, type, k2_lattices: $i > $i > $i > $i).
% 0.62/0.82  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.62/0.82  thf(r1_lattices_type, type, r1_lattices: $i > $i > $i > $o).
% 0.62/0.82  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.62/0.82  thf(v6_lattices_type, type, v6_lattices: $i > $o).
% 0.62/0.82  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 0.62/0.82  thf(l1_lattices_type, type, l1_lattices: $i > $o).
% 0.62/0.82  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.62/0.82  thf(l2_lattices_type, type, l2_lattices: $i > $o).
% 0.62/0.82  thf(sk_A_type, type, sk_A: $i).
% 0.62/0.82  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.62/0.82  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.62/0.82  thf(t22_lattices, conjecture,
% 0.62/0.82    (![A:$i]:
% 0.62/0.82     ( ( ( ~( v2_struct_0 @ A ) ) & ( v5_lattices @ A ) & 
% 0.62/0.82         ( v6_lattices @ A ) & ( v8_lattices @ A ) & ( v9_lattices @ A ) & 
% 0.62/0.82         ( l3_lattices @ A ) ) =>
% 0.62/0.82       ( ![B:$i]:
% 0.62/0.82         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.62/0.82           ( ![C:$i]:
% 0.62/0.82             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.62/0.82               ( r1_lattices @ A @ B @ ( k1_lattices @ A @ B @ C ) ) ) ) ) ) ))).
% 0.62/0.82  thf(zf_stmt_0, negated_conjecture,
% 0.62/0.82    (~( ![A:$i]:
% 0.62/0.82        ( ( ( ~( v2_struct_0 @ A ) ) & ( v5_lattices @ A ) & 
% 0.62/0.82            ( v6_lattices @ A ) & ( v8_lattices @ A ) & ( v9_lattices @ A ) & 
% 0.62/0.82            ( l3_lattices @ A ) ) =>
% 0.62/0.82          ( ![B:$i]:
% 0.62/0.82            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.62/0.82              ( ![C:$i]:
% 0.62/0.82                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.62/0.82                  ( r1_lattices @ A @ B @ ( k1_lattices @ A @ B @ C ) ) ) ) ) ) ) )),
% 0.62/0.82    inference('cnf.neg', [status(esa)], [t22_lattices])).
% 0.62/0.82  thf('0', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.62/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.82  thf('1', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.62/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.82  thf(d9_lattices, axiom,
% 0.62/0.82    (![A:$i]:
% 0.62/0.82     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.62/0.82       ( ( v9_lattices @ A ) <=>
% 0.62/0.82         ( ![B:$i]:
% 0.62/0.82           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.62/0.82             ( ![C:$i]:
% 0.62/0.82               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.62/0.82                 ( ( k2_lattices @ A @ B @ ( k1_lattices @ A @ B @ C ) ) =
% 0.62/0.82                   ( B ) ) ) ) ) ) ) ))).
% 0.62/0.82  thf('2', plain,
% 0.62/0.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.62/0.82         (~ (v9_lattices @ X0)
% 0.62/0.82          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.62/0.82          | ((k2_lattices @ X0 @ X2 @ (k1_lattices @ X0 @ X2 @ X1)) = (X2))
% 0.62/0.82          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.62/0.82          | ~ (l3_lattices @ X0)
% 0.62/0.82          | (v2_struct_0 @ X0))),
% 0.62/0.82      inference('cnf', [status(esa)], [d9_lattices])).
% 0.62/0.82  thf('3', plain,
% 0.62/0.82      (![X0 : $i]:
% 0.62/0.82         ((v2_struct_0 @ sk_A)
% 0.62/0.82          | ~ (l3_lattices @ sk_A)
% 0.62/0.82          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.62/0.82          | ((k2_lattices @ sk_A @ X0 @ (k1_lattices @ sk_A @ X0 @ sk_C_1))
% 0.62/0.82              = (X0))
% 0.62/0.82          | ~ (v9_lattices @ sk_A))),
% 0.62/0.82      inference('sup-', [status(thm)], ['1', '2'])).
% 0.62/0.82  thf('4', plain, ((l3_lattices @ sk_A)),
% 0.62/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.82  thf('5', plain, ((v9_lattices @ sk_A)),
% 0.62/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.82  thf('6', plain,
% 0.62/0.82      (![X0 : $i]:
% 0.62/0.82         ((v2_struct_0 @ sk_A)
% 0.62/0.82          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.62/0.82          | ((k2_lattices @ sk_A @ X0 @ (k1_lattices @ sk_A @ X0 @ sk_C_1))
% 0.62/0.82              = (X0)))),
% 0.62/0.82      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.62/0.82  thf('7', plain, (~ (v2_struct_0 @ sk_A)),
% 0.62/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.82  thf('8', plain,
% 0.62/0.82      (![X0 : $i]:
% 0.62/0.82         (((k2_lattices @ sk_A @ X0 @ (k1_lattices @ sk_A @ X0 @ sk_C_1))
% 0.62/0.82            = (X0))
% 0.62/0.82          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.62/0.82      inference('clc', [status(thm)], ['6', '7'])).
% 0.62/0.82  thf('9', plain,
% 0.62/0.82      (((k2_lattices @ sk_A @ sk_B_1 @ (k1_lattices @ sk_A @ sk_B_1 @ sk_C_1))
% 0.62/0.82         = (sk_B_1))),
% 0.62/0.82      inference('sup-', [status(thm)], ['0', '8'])).
% 0.62/0.82  thf('10', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.62/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.82  thf('11', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.62/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.82  thf(dt_k1_lattices, axiom,
% 0.62/0.82    (![A:$i,B:$i,C:$i]:
% 0.62/0.82     ( ( ( ~( v2_struct_0 @ A ) ) & ( l2_lattices @ A ) & 
% 0.62/0.82         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.62/0.82         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.62/0.82       ( m1_subset_1 @ ( k1_lattices @ A @ B @ C ) @ ( u1_struct_0 @ A ) ) ))).
% 0.62/0.82  thf('12', plain,
% 0.62/0.82      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.62/0.82         (~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X4))
% 0.62/0.82          | ~ (l2_lattices @ X4)
% 0.62/0.82          | (v2_struct_0 @ X4)
% 0.62/0.82          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X4))
% 0.62/0.82          | (m1_subset_1 @ (k1_lattices @ X4 @ X3 @ X5) @ (u1_struct_0 @ X4)))),
% 0.62/0.82      inference('cnf', [status(esa)], [dt_k1_lattices])).
% 0.62/0.82  thf('13', plain,
% 0.62/0.82      (![X0 : $i]:
% 0.62/0.82         ((m1_subset_1 @ (k1_lattices @ sk_A @ sk_B_1 @ X0) @ 
% 0.62/0.82           (u1_struct_0 @ sk_A))
% 0.62/0.82          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.62/0.82          | (v2_struct_0 @ sk_A)
% 0.62/0.82          | ~ (l2_lattices @ sk_A))),
% 0.62/0.82      inference('sup-', [status(thm)], ['11', '12'])).
% 0.62/0.82  thf('14', plain, ((l3_lattices @ sk_A)),
% 0.62/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.82  thf(dt_l3_lattices, axiom,
% 0.62/0.82    (![A:$i]:
% 0.62/0.82     ( ( l3_lattices @ A ) => ( ( l1_lattices @ A ) & ( l2_lattices @ A ) ) ))).
% 0.62/0.82  thf('15', plain, (![X6 : $i]: ((l2_lattices @ X6) | ~ (l3_lattices @ X6))),
% 0.62/0.82      inference('cnf', [status(esa)], [dt_l3_lattices])).
% 0.62/0.82  thf('16', plain, ((l2_lattices @ sk_A)),
% 0.62/0.82      inference('sup-', [status(thm)], ['14', '15'])).
% 0.62/0.82  thf('17', plain,
% 0.62/0.82      (![X0 : $i]:
% 0.62/0.82         ((m1_subset_1 @ (k1_lattices @ sk_A @ sk_B_1 @ X0) @ 
% 0.62/0.82           (u1_struct_0 @ sk_A))
% 0.62/0.82          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.62/0.82          | (v2_struct_0 @ sk_A))),
% 0.62/0.82      inference('demod', [status(thm)], ['13', '16'])).
% 0.62/0.82  thf('18', plain, (~ (v2_struct_0 @ sk_A)),
% 0.62/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.82  thf('19', plain,
% 0.62/0.82      (![X0 : $i]:
% 0.62/0.82         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.62/0.82          | (m1_subset_1 @ (k1_lattices @ sk_A @ sk_B_1 @ X0) @ 
% 0.62/0.82             (u1_struct_0 @ sk_A)))),
% 0.62/0.82      inference('clc', [status(thm)], ['17', '18'])).
% 0.62/0.82  thf('20', plain,
% 0.62/0.82      ((m1_subset_1 @ (k1_lattices @ sk_A @ sk_B_1 @ sk_C_1) @ 
% 0.62/0.82        (u1_struct_0 @ sk_A))),
% 0.62/0.82      inference('sup-', [status(thm)], ['10', '19'])).
% 0.62/0.82  thf('21', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.62/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.82  thf(t21_lattices, axiom,
% 0.62/0.82    (![A:$i]:
% 0.62/0.82     ( ( ( ~( v2_struct_0 @ A ) ) & ( v8_lattices @ A ) & 
% 0.62/0.82         ( v9_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.62/0.82       ( ![B:$i]:
% 0.62/0.82         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.62/0.82           ( ![C:$i]:
% 0.62/0.82             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.62/0.82               ( ( r1_lattices @ A @ B @ C ) <=>
% 0.62/0.82                 ( ( k2_lattices @ A @ B @ C ) = ( B ) ) ) ) ) ) ) ))).
% 0.62/0.82  thf('22', plain,
% 0.62/0.82      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.62/0.82         (~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X8))
% 0.62/0.82          | ((k2_lattices @ X8 @ X7 @ X9) != (X7))
% 0.62/0.82          | (r1_lattices @ X8 @ X7 @ X9)
% 0.62/0.82          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X8))
% 0.62/0.82          | ~ (l3_lattices @ X8)
% 0.62/0.82          | ~ (v9_lattices @ X8)
% 0.62/0.82          | ~ (v8_lattices @ X8)
% 0.62/0.82          | (v2_struct_0 @ X8))),
% 0.62/0.82      inference('cnf', [status(esa)], [t21_lattices])).
% 0.62/0.82  thf('23', plain,
% 0.62/0.82      (![X0 : $i]:
% 0.62/0.82         ((v2_struct_0 @ sk_A)
% 0.62/0.82          | ~ (v8_lattices @ sk_A)
% 0.62/0.82          | ~ (v9_lattices @ sk_A)
% 0.62/0.82          | ~ (l3_lattices @ sk_A)
% 0.62/0.82          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.62/0.82          | (r1_lattices @ sk_A @ sk_B_1 @ X0)
% 0.62/0.82          | ((k2_lattices @ sk_A @ sk_B_1 @ X0) != (sk_B_1)))),
% 0.62/0.82      inference('sup-', [status(thm)], ['21', '22'])).
% 0.62/0.82  thf('24', plain, ((v8_lattices @ sk_A)),
% 0.62/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.82  thf('25', plain, ((v9_lattices @ sk_A)),
% 0.62/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.82  thf('26', plain, ((l3_lattices @ sk_A)),
% 0.62/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.82  thf('27', plain,
% 0.62/0.82      (![X0 : $i]:
% 0.62/0.82         ((v2_struct_0 @ sk_A)
% 0.62/0.82          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.62/0.82          | (r1_lattices @ sk_A @ sk_B_1 @ X0)
% 0.62/0.82          | ((k2_lattices @ sk_A @ sk_B_1 @ X0) != (sk_B_1)))),
% 0.62/0.82      inference('demod', [status(thm)], ['23', '24', '25', '26'])).
% 0.62/0.82  thf('28', plain,
% 0.62/0.82      ((((k2_lattices @ sk_A @ sk_B_1 @ (k1_lattices @ sk_A @ sk_B_1 @ sk_C_1))
% 0.62/0.82          != (sk_B_1))
% 0.62/0.82        | (r1_lattices @ sk_A @ sk_B_1 @ (k1_lattices @ sk_A @ sk_B_1 @ sk_C_1))
% 0.62/0.82        | (v2_struct_0 @ sk_A))),
% 0.62/0.82      inference('sup-', [status(thm)], ['20', '27'])).
% 0.62/0.82  thf('29', plain,
% 0.62/0.82      (~ (r1_lattices @ sk_A @ sk_B_1 @ (k1_lattices @ sk_A @ sk_B_1 @ sk_C_1))),
% 0.62/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.82  thf('30', plain,
% 0.62/0.82      (((v2_struct_0 @ sk_A)
% 0.62/0.82        | ((k2_lattices @ sk_A @ sk_B_1 @ 
% 0.62/0.82            (k1_lattices @ sk_A @ sk_B_1 @ sk_C_1)) != (sk_B_1)))),
% 0.62/0.82      inference('clc', [status(thm)], ['28', '29'])).
% 0.62/0.82  thf('31', plain, (~ (v2_struct_0 @ sk_A)),
% 0.62/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.82  thf('32', plain,
% 0.62/0.82      (((k2_lattices @ sk_A @ sk_B_1 @ (k1_lattices @ sk_A @ sk_B_1 @ sk_C_1))
% 0.62/0.82         != (sk_B_1))),
% 0.62/0.82      inference('clc', [status(thm)], ['30', '31'])).
% 0.62/0.82  thf('33', plain, ($false),
% 0.62/0.82      inference('simplify_reflect-', [status(thm)], ['9', '32'])).
% 0.62/0.82  
% 0.62/0.82  % SZS output end Refutation
% 0.62/0.82  
% 0.62/0.83  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
