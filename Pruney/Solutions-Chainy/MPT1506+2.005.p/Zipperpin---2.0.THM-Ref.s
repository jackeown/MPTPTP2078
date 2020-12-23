%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KhRATpopO9

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:29 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   33 (  45 expanded)
%              Number of leaves         :   15 (  21 expanded)
%              Depth                    :    9
%              Number of atoms          :  271 ( 535 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k16_lattice3_type,type,(
    k16_lattice3: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(v4_lattice3_type,type,(
    v4_lattice3: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r3_lattices_type,type,(
    r3_lattices: $i > $i > $i > $o )).

thf(r3_lattice3_type,type,(
    r3_lattice3: $i > $i > $i > $o )).

thf(t40_lattice3,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( v4_lattice3 @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( r3_lattice3 @ A @ B @ C )
             => ( r3_lattices @ A @ B @ ( k16_lattice3 @ A @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v10_lattices @ A )
          & ( v4_lattice3 @ A )
          & ( l3_lattices @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( r3_lattice3 @ A @ B @ C )
               => ( r3_lattices @ A @ B @ ( k16_lattice3 @ A @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t40_lattice3])).

thf('0',plain,(
    ~ ( r3_lattices @ sk_A @ sk_B @ ( k16_lattice3 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r3_lattice3 @ sk_A @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k16_lattice3,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A ) )
     => ( m1_subset_1 @ ( k16_lattice3 @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( m1_subset_1 @ ( k16_lattice3 @ X0 @ X1 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k16_lattice3])).

thf(t34_lattice3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( v4_lattice3 @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( B
                = ( k16_lattice3 @ A @ C ) )
            <=> ( ( r3_lattice3 @ A @ B @ C )
                & ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( ( r3_lattice3 @ A @ D @ C )
                     => ( r3_lattices @ A @ D @ B ) ) ) ) ) ) ) )).

thf('4',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X3 ) )
      | ( X2
       != ( k16_lattice3 @ X3 @ X4 ) )
      | ~ ( r3_lattice3 @ X3 @ X5 @ X4 )
      | ( r3_lattices @ X3 @ X5 @ X2 )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X3 ) )
      | ~ ( l3_lattices @ X3 )
      | ~ ( v4_lattice3 @ X3 )
      | ~ ( v10_lattices @ X3 )
      | ( v2_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t34_lattice3])).

thf('5',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( v2_struct_0 @ X3 )
      | ~ ( v10_lattices @ X3 )
      | ~ ( v4_lattice3 @ X3 )
      | ~ ( l3_lattices @ X3 )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X3 ) )
      | ( r3_lattices @ X3 @ X5 @ ( k16_lattice3 @ X3 @ X4 ) )
      | ~ ( r3_lattice3 @ X3 @ X5 @ X4 )
      | ~ ( m1_subset_1 @ ( k16_lattice3 @ X3 @ X4 ) @ ( u1_struct_0 @ X3 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( r3_lattice3 @ X0 @ X2 @ X1 )
      | ( r3_lattices @ X0 @ X2 @ ( k16_lattice3 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r3_lattices @ X0 @ X2 @ ( k16_lattice3 @ X0 @ X1 ) )
      | ~ ( r3_lattice3 @ X0 @ X2 @ X1 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( r3_lattice3 @ sk_A @ sk_B @ X0 )
      | ( r3_lattices @ sk_A @ sk_B @ ( k16_lattice3 @ sk_A @ X0 ) )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( v10_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf('9',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r3_lattice3 @ sk_A @ sk_B @ X0 )
      | ( r3_lattices @ sk_A @ sk_B @ ( k16_lattice3 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['8','9','10','11'])).

thf('13',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r3_lattices @ sk_A @ sk_B @ ( k16_lattice3 @ sk_A @ X0 ) )
      | ~ ( r3_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['12','13'])).

thf('15',plain,(
    r3_lattices @ sk_A @ sk_B @ ( k16_lattice3 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1','14'])).

thf('16',plain,(
    $false ),
    inference(demod,[status(thm)],['0','15'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KhRATpopO9
% 0.13/0.33  % Computer   : n019.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 11:27:37 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 35 iterations in 0.035s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(v10_lattices_type, type, v10_lattices: $i > $o).
% 0.20/0.48  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.48  thf(k16_lattice3_type, type, k16_lattice3: $i > $i > $i).
% 0.20/0.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 0.20/0.48  thf(v4_lattice3_type, type, v4_lattice3: $i > $o).
% 0.20/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.48  thf(r3_lattices_type, type, r3_lattices: $i > $i > $i > $o).
% 0.20/0.48  thf(r3_lattice3_type, type, r3_lattice3: $i > $i > $i > $o).
% 0.20/0.48  thf(t40_lattice3, conjecture,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.20/0.48         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.48           ( ![C:$i]:
% 0.20/0.48             ( ( r3_lattice3 @ A @ B @ C ) =>
% 0.20/0.48               ( r3_lattices @ A @ B @ ( k16_lattice3 @ A @ C ) ) ) ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i]:
% 0.20/0.48        ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.20/0.48            ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.20/0.48          ( ![B:$i]:
% 0.20/0.48            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.48              ( ![C:$i]:
% 0.20/0.48                ( ( r3_lattice3 @ A @ B @ C ) =>
% 0.20/0.48                  ( r3_lattices @ A @ B @ ( k16_lattice3 @ A @ C ) ) ) ) ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t40_lattice3])).
% 0.20/0.48  thf('0', plain,
% 0.20/0.48      (~ (r3_lattices @ sk_A @ sk_B @ (k16_lattice3 @ sk_A @ sk_C))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('1', plain, ((r3_lattice3 @ sk_A @ sk_B @ sk_C)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('2', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(dt_k16_lattice3, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.20/0.48       ( m1_subset_1 @ ( k16_lattice3 @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (~ (l3_lattices @ X0)
% 0.20/0.48          | (v2_struct_0 @ X0)
% 0.20/0.48          | (m1_subset_1 @ (k16_lattice3 @ X0 @ X1) @ (u1_struct_0 @ X0)))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_k16_lattice3])).
% 0.20/0.48  thf(t34_lattice3, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.20/0.48         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.48           ( ![C:$i]:
% 0.20/0.48             ( ( ( B ) = ( k16_lattice3 @ A @ C ) ) <=>
% 0.20/0.48               ( ( r3_lattice3 @ A @ B @ C ) & 
% 0.20/0.48                 ( ![D:$i]:
% 0.20/0.48                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.48                     ( ( r3_lattice3 @ A @ D @ C ) =>
% 0.20/0.48                       ( r3_lattices @ A @ D @ B ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.48  thf('4', plain,
% 0.20/0.48      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X3))
% 0.20/0.48          | ((X2) != (k16_lattice3 @ X3 @ X4))
% 0.20/0.48          | ~ (r3_lattice3 @ X3 @ X5 @ X4)
% 0.20/0.48          | (r3_lattices @ X3 @ X5 @ X2)
% 0.20/0.48          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X3))
% 0.20/0.48          | ~ (l3_lattices @ X3)
% 0.20/0.48          | ~ (v4_lattice3 @ X3)
% 0.20/0.48          | ~ (v10_lattices @ X3)
% 0.20/0.48          | (v2_struct_0 @ X3))),
% 0.20/0.48      inference('cnf', [status(esa)], [t34_lattice3])).
% 0.20/0.48  thf('5', plain,
% 0.20/0.48      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.48         ((v2_struct_0 @ X3)
% 0.20/0.48          | ~ (v10_lattices @ X3)
% 0.20/0.48          | ~ (v4_lattice3 @ X3)
% 0.20/0.48          | ~ (l3_lattices @ X3)
% 0.20/0.48          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X3))
% 0.20/0.48          | (r3_lattices @ X3 @ X5 @ (k16_lattice3 @ X3 @ X4))
% 0.20/0.48          | ~ (r3_lattice3 @ X3 @ X5 @ X4)
% 0.20/0.48          | ~ (m1_subset_1 @ (k16_lattice3 @ X3 @ X4) @ (u1_struct_0 @ X3)))),
% 0.20/0.48      inference('simplify', [status(thm)], ['4'])).
% 0.20/0.48  thf('6', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.48         ((v2_struct_0 @ X0)
% 0.20/0.48          | ~ (l3_lattices @ X0)
% 0.20/0.48          | ~ (r3_lattice3 @ X0 @ X2 @ X1)
% 0.20/0.48          | (r3_lattices @ X0 @ X2 @ (k16_lattice3 @ X0 @ X1))
% 0.20/0.48          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.20/0.48          | ~ (l3_lattices @ X0)
% 0.20/0.48          | ~ (v4_lattice3 @ X0)
% 0.20/0.48          | ~ (v10_lattices @ X0)
% 0.20/0.48          | (v2_struct_0 @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['3', '5'])).
% 0.20/0.48  thf('7', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.48         (~ (v10_lattices @ X0)
% 0.20/0.48          | ~ (v4_lattice3 @ X0)
% 0.20/0.48          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.20/0.48          | (r3_lattices @ X0 @ X2 @ (k16_lattice3 @ X0 @ X1))
% 0.20/0.48          | ~ (r3_lattice3 @ X0 @ X2 @ X1)
% 0.20/0.48          | ~ (l3_lattices @ X0)
% 0.20/0.48          | (v2_struct_0 @ X0))),
% 0.20/0.48      inference('simplify', [status(thm)], ['6'])).
% 0.20/0.48  thf('8', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((v2_struct_0 @ sk_A)
% 0.20/0.48          | ~ (l3_lattices @ sk_A)
% 0.20/0.48          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0)
% 0.20/0.48          | (r3_lattices @ sk_A @ sk_B @ (k16_lattice3 @ sk_A @ X0))
% 0.20/0.48          | ~ (v4_lattice3 @ sk_A)
% 0.20/0.48          | ~ (v10_lattices @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['2', '7'])).
% 0.20/0.48  thf('9', plain, ((l3_lattices @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('10', plain, ((v4_lattice3 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('11', plain, ((v10_lattices @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('12', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((v2_struct_0 @ sk_A)
% 0.20/0.48          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0)
% 0.20/0.48          | (r3_lattices @ sk_A @ sk_B @ (k16_lattice3 @ sk_A @ X0)))),
% 0.20/0.48      inference('demod', [status(thm)], ['8', '9', '10', '11'])).
% 0.20/0.48  thf('13', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('14', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((r3_lattices @ sk_A @ sk_B @ (k16_lattice3 @ sk_A @ X0))
% 0.20/0.48          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 0.20/0.48      inference('clc', [status(thm)], ['12', '13'])).
% 0.20/0.48  thf('15', plain,
% 0.20/0.48      ((r3_lattices @ sk_A @ sk_B @ (k16_lattice3 @ sk_A @ sk_C))),
% 0.20/0.48      inference('sup-', [status(thm)], ['1', '14'])).
% 0.20/0.48  thf('16', plain, ($false), inference('demod', [status(thm)], ['0', '15'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
