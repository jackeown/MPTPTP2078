%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.G0bHoKLB93

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:29 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   48 (  70 expanded)
%              Number of leaves         :   19 (  30 expanded)
%              Depth                    :   11
%              Number of atoms          :  313 ( 797 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(k16_lattice3_type,type,(
    k16_lattice3: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k15_lattice3_type,type,(
    k15_lattice3: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(a_2_1_lattice3_type,type,(
    a_2_1_lattice3: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v4_lattice3_type,type,(
    v4_lattice3: $i > $o )).

thf(r3_lattices_type,type,(
    r3_lattices: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(r3_lattice3_type,type,(
    r3_lattice3: $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d22_lattice3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( k16_lattice3 @ A @ B )
          = ( k15_lattice3 @ A @ ( a_2_1_lattice3 @ A @ B ) ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k16_lattice3 @ X0 @ X1 )
        = ( k15_lattice3 @ X0 @ ( a_2_1_lattice3 @ X0 @ X1 ) ) )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d22_lattice3])).

thf('2',plain,(
    r3_lattice3 @ sk_A @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fraenkel_a_2_1_lattice3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ B )
        & ( l3_lattices @ B ) )
     => ( ( r2_hidden @ A @ ( a_2_1_lattice3 @ B @ C ) )
      <=> ? [D: $i] :
            ( ( r3_lattice3 @ B @ D @ C )
            & ( A = D )
            & ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) )).

thf('4',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( l3_lattices @ X2 )
      | ( v2_struct_0 @ X2 )
      | ( r2_hidden @ X4 @ ( a_2_1_lattice3 @ X2 @ X3 ) )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X2 ) )
      | ( X4 != X5 )
      | ~ ( r3_lattice3 @ X2 @ X5 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_lattice3])).

thf('5',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ~ ( r3_lattice3 @ X2 @ X5 @ X3 )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X2 ) )
      | ( r2_hidden @ X5 @ ( a_2_1_lattice3 @ X2 @ X3 ) )
      | ( v2_struct_0 @ X2 )
      | ~ ( l3_lattices @ X2 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( l3_lattices @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ sk_B @ ( a_2_1_lattice3 @ sk_A @ X0 ) )
      | ~ ( r3_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ sk_B @ ( a_2_1_lattice3 @ sk_A @ X0 ) )
      | ~ ( r3_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( r3_lattice3 @ sk_A @ sk_B @ X0 )
      | ( r2_hidden @ sk_B @ ( a_2_1_lattice3 @ sk_A @ X0 ) ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('11',plain,(
    r2_hidden @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['2','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_lattice3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( v4_lattice3 @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( r2_hidden @ B @ C )
             => ( ( r3_lattices @ A @ B @ ( k15_lattice3 @ A @ C ) )
                & ( r3_lattices @ A @ ( k16_lattice3 @ A @ C ) @ B ) ) ) ) ) )).

thf('13',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X7 ) )
      | ( r3_lattices @ X7 @ X6 @ ( k15_lattice3 @ X7 @ X8 ) )
      | ~ ( r2_hidden @ X6 @ X8 )
      | ~ ( l3_lattices @ X7 )
      | ~ ( v4_lattice3 @ X7 )
      | ~ ( v10_lattices @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t38_lattice3])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( r2_hidden @ sk_B @ X0 )
      | ( r3_lattices @ sk_A @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r2_hidden @ sk_B @ X0 )
      | ( r3_lattices @ sk_A @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['14','15','16','17'])).

thf('19',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r3_lattices @ sk_A @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['18','19'])).

thf('21',plain,(
    r3_lattices @ sk_A @ sk_B @ ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['11','20'])).

thf('22',plain,
    ( ( r3_lattices @ sk_A @ sk_B @ ( k16_lattice3 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A ) ),
    inference('sup+',[status(thm)],['1','21'])).

thf('23',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( r3_lattices @ sk_A @ sk_B @ ( k16_lattice3 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ~ ( r3_lattices @ sk_A @ sk_B @ ( k16_lattice3 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,(
    $false ),
    inference(demod,[status(thm)],['0','26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.G0bHoKLB93
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:40:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.19/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.47  % Solved by: fo/fo7.sh
% 0.19/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.47  % done 23 iterations in 0.016s
% 0.19/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.47  % SZS output start Refutation
% 0.19/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.47  thf(v10_lattices_type, type, v10_lattices: $i > $o).
% 0.19/0.47  thf(k16_lattice3_type, type, k16_lattice3: $i > $i > $i).
% 0.19/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.47  thf(k15_lattice3_type, type, k15_lattice3: $i > $i > $i).
% 0.19/0.47  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.19/0.47  thf(a_2_1_lattice3_type, type, a_2_1_lattice3: $i > $i > $i).
% 0.19/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.47  thf(v4_lattice3_type, type, v4_lattice3: $i > $o).
% 0.19/0.47  thf(r3_lattices_type, type, r3_lattices: $i > $i > $i > $o).
% 0.19/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.47  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 0.19/0.47  thf(r3_lattice3_type, type, r3_lattice3: $i > $i > $i > $o).
% 0.19/0.47  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.19/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.47  thf(t40_lattice3, conjecture,
% 0.19/0.47    (![A:$i]:
% 0.19/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.19/0.47         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.19/0.47       ( ![B:$i]:
% 0.19/0.47         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.47           ( ![C:$i]:
% 0.19/0.47             ( ( r3_lattice3 @ A @ B @ C ) =>
% 0.19/0.47               ( r3_lattices @ A @ B @ ( k16_lattice3 @ A @ C ) ) ) ) ) ) ))).
% 0.19/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.47    (~( ![A:$i]:
% 0.19/0.47        ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.19/0.47            ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.19/0.47          ( ![B:$i]:
% 0.19/0.47            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.47              ( ![C:$i]:
% 0.19/0.47                ( ( r3_lattice3 @ A @ B @ C ) =>
% 0.19/0.47                  ( r3_lattices @ A @ B @ ( k16_lattice3 @ A @ C ) ) ) ) ) ) ) )),
% 0.19/0.47    inference('cnf.neg', [status(esa)], [t40_lattice3])).
% 0.19/0.47  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf(d22_lattice3, axiom,
% 0.19/0.47    (![A:$i]:
% 0.19/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.19/0.47       ( ![B:$i]:
% 0.19/0.47         ( ( k16_lattice3 @ A @ B ) =
% 0.19/0.47           ( k15_lattice3 @ A @ ( a_2_1_lattice3 @ A @ B ) ) ) ) ))).
% 0.19/0.47  thf('1', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i]:
% 0.19/0.47         (((k16_lattice3 @ X0 @ X1)
% 0.19/0.47            = (k15_lattice3 @ X0 @ (a_2_1_lattice3 @ X0 @ X1)))
% 0.19/0.47          | ~ (l3_lattices @ X0)
% 0.19/0.47          | (v2_struct_0 @ X0))),
% 0.19/0.47      inference('cnf', [status(esa)], [d22_lattice3])).
% 0.19/0.47  thf('2', plain, ((r3_lattice3 @ sk_A @ sk_B @ sk_C)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('3', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf(fraenkel_a_2_1_lattice3, axiom,
% 0.19/0.47    (![A:$i,B:$i,C:$i]:
% 0.19/0.47     ( ( ( ~( v2_struct_0 @ B ) ) & ( l3_lattices @ B ) ) =>
% 0.19/0.47       ( ( r2_hidden @ A @ ( a_2_1_lattice3 @ B @ C ) ) <=>
% 0.19/0.47         ( ?[D:$i]:
% 0.19/0.47           ( ( r3_lattice3 @ B @ D @ C ) & ( ( A ) = ( D ) ) & 
% 0.19/0.47             ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.19/0.47  thf('4', plain,
% 0.19/0.47      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.19/0.47         (~ (l3_lattices @ X2)
% 0.19/0.47          | (v2_struct_0 @ X2)
% 0.19/0.47          | (r2_hidden @ X4 @ (a_2_1_lattice3 @ X2 @ X3))
% 0.19/0.47          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X2))
% 0.19/0.47          | ((X4) != (X5))
% 0.19/0.47          | ~ (r3_lattice3 @ X2 @ X5 @ X3))),
% 0.19/0.47      inference('cnf', [status(esa)], [fraenkel_a_2_1_lattice3])).
% 0.19/0.47  thf('5', plain,
% 0.19/0.47      (![X2 : $i, X3 : $i, X5 : $i]:
% 0.19/0.47         (~ (r3_lattice3 @ X2 @ X5 @ X3)
% 0.19/0.47          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X2))
% 0.19/0.47          | (r2_hidden @ X5 @ (a_2_1_lattice3 @ X2 @ X3))
% 0.19/0.47          | (v2_struct_0 @ X2)
% 0.19/0.47          | ~ (l3_lattices @ X2))),
% 0.19/0.47      inference('simplify', [status(thm)], ['4'])).
% 0.19/0.47  thf('6', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         (~ (l3_lattices @ sk_A)
% 0.19/0.47          | (v2_struct_0 @ sk_A)
% 0.19/0.47          | (r2_hidden @ sk_B @ (a_2_1_lattice3 @ sk_A @ X0))
% 0.19/0.47          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 0.19/0.47      inference('sup-', [status(thm)], ['3', '5'])).
% 0.19/0.47  thf('7', plain, ((l3_lattices @ sk_A)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('8', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         ((v2_struct_0 @ sk_A)
% 0.19/0.47          | (r2_hidden @ sk_B @ (a_2_1_lattice3 @ sk_A @ X0))
% 0.19/0.47          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 0.19/0.47      inference('demod', [status(thm)], ['6', '7'])).
% 0.19/0.47  thf('9', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('10', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         (~ (r3_lattice3 @ sk_A @ sk_B @ X0)
% 0.19/0.47          | (r2_hidden @ sk_B @ (a_2_1_lattice3 @ sk_A @ X0)))),
% 0.19/0.47      inference('clc', [status(thm)], ['8', '9'])).
% 0.19/0.47  thf('11', plain, ((r2_hidden @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C))),
% 0.19/0.47      inference('sup-', [status(thm)], ['2', '10'])).
% 0.19/0.47  thf('12', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf(t38_lattice3, axiom,
% 0.19/0.47    (![A:$i]:
% 0.19/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.19/0.47         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.19/0.47       ( ![B:$i]:
% 0.19/0.47         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.47           ( ![C:$i]:
% 0.19/0.47             ( ( r2_hidden @ B @ C ) =>
% 0.19/0.47               ( ( r3_lattices @ A @ B @ ( k15_lattice3 @ A @ C ) ) & 
% 0.19/0.47                 ( r3_lattices @ A @ ( k16_lattice3 @ A @ C ) @ B ) ) ) ) ) ) ))).
% 0.19/0.47  thf('13', plain,
% 0.19/0.47      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.19/0.47         (~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X7))
% 0.19/0.47          | (r3_lattices @ X7 @ X6 @ (k15_lattice3 @ X7 @ X8))
% 0.19/0.47          | ~ (r2_hidden @ X6 @ X8)
% 0.19/0.47          | ~ (l3_lattices @ X7)
% 0.19/0.47          | ~ (v4_lattice3 @ X7)
% 0.19/0.47          | ~ (v10_lattices @ X7)
% 0.19/0.47          | (v2_struct_0 @ X7))),
% 0.19/0.47      inference('cnf', [status(esa)], [t38_lattice3])).
% 0.19/0.47  thf('14', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         ((v2_struct_0 @ sk_A)
% 0.19/0.47          | ~ (v10_lattices @ sk_A)
% 0.19/0.47          | ~ (v4_lattice3 @ sk_A)
% 0.19/0.47          | ~ (l3_lattices @ sk_A)
% 0.19/0.47          | ~ (r2_hidden @ sk_B @ X0)
% 0.19/0.47          | (r3_lattices @ sk_A @ sk_B @ (k15_lattice3 @ sk_A @ X0)))),
% 0.19/0.47      inference('sup-', [status(thm)], ['12', '13'])).
% 0.19/0.47  thf('15', plain, ((v10_lattices @ sk_A)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('16', plain, ((v4_lattice3 @ sk_A)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('17', plain, ((l3_lattices @ sk_A)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('18', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         ((v2_struct_0 @ sk_A)
% 0.19/0.47          | ~ (r2_hidden @ sk_B @ X0)
% 0.19/0.47          | (r3_lattices @ sk_A @ sk_B @ (k15_lattice3 @ sk_A @ X0)))),
% 0.19/0.47      inference('demod', [status(thm)], ['14', '15', '16', '17'])).
% 0.19/0.47  thf('19', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('20', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         ((r3_lattices @ sk_A @ sk_B @ (k15_lattice3 @ sk_A @ X0))
% 0.19/0.47          | ~ (r2_hidden @ sk_B @ X0))),
% 0.19/0.47      inference('clc', [status(thm)], ['18', '19'])).
% 0.19/0.47  thf('21', plain,
% 0.19/0.47      ((r3_lattices @ sk_A @ sk_B @ 
% 0.19/0.47        (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))),
% 0.19/0.47      inference('sup-', [status(thm)], ['11', '20'])).
% 0.19/0.47  thf('22', plain,
% 0.19/0.47      (((r3_lattices @ sk_A @ sk_B @ (k16_lattice3 @ sk_A @ sk_C))
% 0.19/0.47        | (v2_struct_0 @ sk_A)
% 0.19/0.47        | ~ (l3_lattices @ sk_A))),
% 0.19/0.47      inference('sup+', [status(thm)], ['1', '21'])).
% 0.19/0.47  thf('23', plain, ((l3_lattices @ sk_A)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('24', plain,
% 0.19/0.47      (((r3_lattices @ sk_A @ sk_B @ (k16_lattice3 @ sk_A @ sk_C))
% 0.19/0.47        | (v2_struct_0 @ sk_A))),
% 0.19/0.47      inference('demod', [status(thm)], ['22', '23'])).
% 0.19/0.47  thf('25', plain,
% 0.19/0.47      (~ (r3_lattices @ sk_A @ sk_B @ (k16_lattice3 @ sk_A @ sk_C))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('26', plain, ((v2_struct_0 @ sk_A)),
% 0.19/0.47      inference('clc', [status(thm)], ['24', '25'])).
% 0.19/0.47  thf('27', plain, ($false), inference('demod', [status(thm)], ['0', '26'])).
% 0.19/0.47  
% 0.19/0.47  % SZS output end Refutation
% 0.19/0.47  
% 0.19/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
