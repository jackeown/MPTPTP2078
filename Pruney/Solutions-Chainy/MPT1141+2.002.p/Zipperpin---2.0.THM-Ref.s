%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zJhKCSx1yC

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:36 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   42 (  65 expanded)
%              Number of leaves         :   12 (  24 expanded)
%              Depth                    :    9
%              Number of atoms          :  297 ( 758 expanded)
%              Number of equality atoms :    8 (   9 expanded)
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

thf(t30_orders_2,conjecture,(
    ! [A: $i] :
      ( ( ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ~ ( ( r1_orders_2 @ A @ B @ C )
                  & ( r2_orders_2 @ A @ C @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v5_orders_2 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ~ ( ( r1_orders_2 @ A @ B @ C )
                    & ( r2_orders_2 @ A @ C @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t30_orders_2])).

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
    r2_orders_2 @ sk_A @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_orders_2 @ X1 @ X0 @ X2 )
      | ( X0 = X2 )
      | ( r2_orders_2 @ X1 @ X0 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d10_orders_2])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ sk_B @ X0 )
      | ( sk_B = X0 )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ sk_B @ X0 )
      | ( sk_B = X0 )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_C )
    | ( sk_B = sk_C )
    | ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('14',plain,(
    r1_orders_2 @ sk_A @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( sk_B = sk_C )
    | ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_orders_2,axiom,(
    ! [A: $i] :
      ( ( ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ~ ( ( r2_orders_2 @ A @ B @ C )
                  & ( r2_orders_2 @ A @ C @ B ) ) ) ) ) )).

thf('18',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X4 ) )
      | ~ ( r2_orders_2 @ X4 @ X5 @ X3 )
      | ~ ( r2_orders_2 @ X4 @ X3 @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X4 ) )
      | ~ ( l1_orders_2 @ X4 )
      | ~ ( v5_orders_2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t28_orders_2])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( r2_orders_2 @ sk_A @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( r2_orders_2 @ sk_A @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,
    ( ~ ( r2_orders_2 @ sk_A @ sk_C @ sk_B )
    | ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['16','22'])).

thf('24',plain,(
    r2_orders_2 @ sk_A @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    sk_B = sk_C ),
    inference('sup-',[status(thm)],['15','25'])).

thf('27',plain,(
    r2_orders_2 @ sk_A @ sk_B @ sk_B ),
    inference(demod,[status(thm)],['6','26'])).

thf('28',plain,(
    $false ),
    inference(demod,[status(thm)],['5','27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zJhKCSx1yC
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:07:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.19/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.47  % Solved by: fo/fo7.sh
% 0.19/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.47  % done 28 iterations in 0.017s
% 0.19/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.47  % SZS output start Refutation
% 0.19/0.47  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.19/0.47  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.19/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.47  thf(r2_orders_2_type, type, r2_orders_2: $i > $i > $i > $o).
% 0.19/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.47  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.19/0.47  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.19/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.47  thf(t30_orders_2, conjecture,
% 0.19/0.47    (![A:$i]:
% 0.19/0.47     ( ( ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.19/0.47       ( ![B:$i]:
% 0.19/0.47         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.47           ( ![C:$i]:
% 0.19/0.47             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.47               ( ~( ( r1_orders_2 @ A @ B @ C ) & ( r2_orders_2 @ A @ C @ B ) ) ) ) ) ) ) ))).
% 0.19/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.47    (~( ![A:$i]:
% 0.19/0.47        ( ( ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.19/0.47          ( ![B:$i]:
% 0.19/0.47            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.47              ( ![C:$i]:
% 0.19/0.47                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.47                  ( ~( ( r1_orders_2 @ A @ B @ C ) & 
% 0.19/0.47                       ( r2_orders_2 @ A @ C @ B ) ) ) ) ) ) ) ) )),
% 0.19/0.47    inference('cnf.neg', [status(esa)], [t30_orders_2])).
% 0.19/0.47  thf('0', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf(d10_orders_2, axiom,
% 0.19/0.47    (![A:$i]:
% 0.19/0.47     ( ( l1_orders_2 @ A ) =>
% 0.19/0.47       ( ![B:$i]:
% 0.19/0.47         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.47           ( ![C:$i]:
% 0.19/0.47             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.47               ( ( r2_orders_2 @ A @ B @ C ) <=>
% 0.19/0.47                 ( ( r1_orders_2 @ A @ B @ C ) & ( ( B ) != ( C ) ) ) ) ) ) ) ) ))).
% 0.19/0.47  thf('1', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.47         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 0.19/0.47          | ~ (r2_orders_2 @ X1 @ X0 @ X2)
% 0.19/0.47          | ((X0) != (X2))
% 0.19/0.47          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.19/0.47          | ~ (l1_orders_2 @ X1))),
% 0.19/0.47      inference('cnf', [status(esa)], [d10_orders_2])).
% 0.19/0.47  thf('2', plain,
% 0.19/0.47      (![X1 : $i, X2 : $i]:
% 0.19/0.47         (~ (l1_orders_2 @ X1)
% 0.19/0.47          | ~ (r2_orders_2 @ X1 @ X2 @ X2)
% 0.19/0.47          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1)))),
% 0.19/0.47      inference('simplify', [status(thm)], ['1'])).
% 0.19/0.47  thf('3', plain,
% 0.19/0.47      ((~ (r2_orders_2 @ sk_A @ sk_B @ sk_B) | ~ (l1_orders_2 @ sk_A))),
% 0.19/0.47      inference('sup-', [status(thm)], ['0', '2'])).
% 0.19/0.47  thf('4', plain, ((l1_orders_2 @ sk_A)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('5', plain, (~ (r2_orders_2 @ sk_A @ sk_B @ sk_B)),
% 0.19/0.47      inference('demod', [status(thm)], ['3', '4'])).
% 0.19/0.47  thf('6', plain, ((r2_orders_2 @ sk_A @ sk_C @ sk_B)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('7', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('8', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('9', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.47         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 0.19/0.47          | ~ (r1_orders_2 @ X1 @ X0 @ X2)
% 0.19/0.47          | ((X0) = (X2))
% 0.19/0.47          | (r2_orders_2 @ X1 @ X0 @ X2)
% 0.19/0.47          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.19/0.47          | ~ (l1_orders_2 @ X1))),
% 0.19/0.47      inference('cnf', [status(esa)], [d10_orders_2])).
% 0.19/0.47  thf('10', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         (~ (l1_orders_2 @ sk_A)
% 0.19/0.47          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.19/0.47          | (r2_orders_2 @ sk_A @ sk_B @ X0)
% 0.19/0.47          | ((sk_B) = (X0))
% 0.19/0.47          | ~ (r1_orders_2 @ sk_A @ sk_B @ X0))),
% 0.19/0.47      inference('sup-', [status(thm)], ['8', '9'])).
% 0.19/0.47  thf('11', plain, ((l1_orders_2 @ sk_A)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('12', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.19/0.47          | (r2_orders_2 @ sk_A @ sk_B @ X0)
% 0.19/0.47          | ((sk_B) = (X0))
% 0.19/0.47          | ~ (r1_orders_2 @ sk_A @ sk_B @ X0))),
% 0.19/0.47      inference('demod', [status(thm)], ['10', '11'])).
% 0.19/0.47  thf('13', plain,
% 0.19/0.47      ((~ (r1_orders_2 @ sk_A @ sk_B @ sk_C)
% 0.19/0.47        | ((sk_B) = (sk_C))
% 0.19/0.47        | (r2_orders_2 @ sk_A @ sk_B @ sk_C))),
% 0.19/0.47      inference('sup-', [status(thm)], ['7', '12'])).
% 0.19/0.47  thf('14', plain, ((r1_orders_2 @ sk_A @ sk_B @ sk_C)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('15', plain, ((((sk_B) = (sk_C)) | (r2_orders_2 @ sk_A @ sk_B @ sk_C))),
% 0.19/0.47      inference('demod', [status(thm)], ['13', '14'])).
% 0.19/0.47  thf('16', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('17', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf(t28_orders_2, axiom,
% 0.19/0.47    (![A:$i]:
% 0.19/0.47     ( ( ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.19/0.47       ( ![B:$i]:
% 0.19/0.47         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.47           ( ![C:$i]:
% 0.19/0.47             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.47               ( ~( ( r2_orders_2 @ A @ B @ C ) & ( r2_orders_2 @ A @ C @ B ) ) ) ) ) ) ) ))).
% 0.19/0.47  thf('18', plain,
% 0.19/0.47      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.19/0.47         (~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X4))
% 0.19/0.47          | ~ (r2_orders_2 @ X4 @ X5 @ X3)
% 0.19/0.47          | ~ (r2_orders_2 @ X4 @ X3 @ X5)
% 0.19/0.47          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X4))
% 0.19/0.47          | ~ (l1_orders_2 @ X4)
% 0.19/0.47          | ~ (v5_orders_2 @ X4))),
% 0.19/0.47      inference('cnf', [status(esa)], [t28_orders_2])).
% 0.19/0.47  thf('19', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         (~ (v5_orders_2 @ sk_A)
% 0.19/0.47          | ~ (l1_orders_2 @ sk_A)
% 0.19/0.47          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.19/0.47          | ~ (r2_orders_2 @ sk_A @ sk_B @ X0)
% 0.19/0.47          | ~ (r2_orders_2 @ sk_A @ X0 @ sk_B))),
% 0.19/0.47      inference('sup-', [status(thm)], ['17', '18'])).
% 0.19/0.47  thf('20', plain, ((v5_orders_2 @ sk_A)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('21', plain, ((l1_orders_2 @ sk_A)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('22', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.19/0.47          | ~ (r2_orders_2 @ sk_A @ sk_B @ X0)
% 0.19/0.47          | ~ (r2_orders_2 @ sk_A @ X0 @ sk_B))),
% 0.19/0.47      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.19/0.47  thf('23', plain,
% 0.19/0.47      ((~ (r2_orders_2 @ sk_A @ sk_C @ sk_B)
% 0.19/0.47        | ~ (r2_orders_2 @ sk_A @ sk_B @ sk_C))),
% 0.19/0.47      inference('sup-', [status(thm)], ['16', '22'])).
% 0.19/0.47  thf('24', plain, ((r2_orders_2 @ sk_A @ sk_C @ sk_B)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('25', plain, (~ (r2_orders_2 @ sk_A @ sk_B @ sk_C)),
% 0.19/0.47      inference('demod', [status(thm)], ['23', '24'])).
% 0.19/0.47  thf('26', plain, (((sk_B) = (sk_C))),
% 0.19/0.47      inference('sup-', [status(thm)], ['15', '25'])).
% 0.19/0.47  thf('27', plain, ((r2_orders_2 @ sk_A @ sk_B @ sk_B)),
% 0.19/0.47      inference('demod', [status(thm)], ['6', '26'])).
% 0.19/0.47  thf('28', plain, ($false), inference('demod', [status(thm)], ['5', '27'])).
% 0.19/0.47  
% 0.19/0.47  % SZS output end Refutation
% 0.19/0.47  
% 0.19/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
