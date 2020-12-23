%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mfL1lCnncu

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:29 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   39 (  51 expanded)
%              Number of leaves         :   18 (  24 expanded)
%              Depth                    :   10
%              Number of atoms          :  321 ( 585 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r3_lattices_type,type,(
    r3_lattices: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k16_lattice3_type,type,(
    k16_lattice3: $i > $i > $i )).

thf(r3_lattice3_type,type,(
    r3_lattice3: $i > $i > $i > $o )).

thf(k15_lattice3_type,type,(
    k15_lattice3: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(a_2_1_lattice3_type,type,(
    a_2_1_lattice3: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v4_lattice3_type,type,(
    v4_lattice3: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

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

thf(d22_lattice3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( k16_lattice3 @ A @ B )
          = ( k15_lattice3 @ A @ ( a_2_1_lattice3 @ A @ B ) ) ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k16_lattice3 @ X0 @ X1 )
        = ( k15_lattice3 @ X0 @ ( a_2_1_lattice3 @ X0 @ X1 ) ) )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d22_lattice3])).

thf(dt_k15_lattice3,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A ) )
     => ( m1_subset_1 @ ( k15_lattice3 @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('4',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( l3_lattices @ X2 )
      | ( v2_struct_0 @ X2 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X2 @ X3 ) @ ( u1_struct_0 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k16_lattice3 @ X1 @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( m1_subset_1 @ ( k16_lattice3 @ X1 @ X0 ) @ ( u1_struct_0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

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

thf('7',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ( X4
       != ( k16_lattice3 @ X5 @ X6 ) )
      | ~ ( r3_lattice3 @ X5 @ X7 @ X6 )
      | ( r3_lattices @ X5 @ X7 @ X4 )
      | ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l3_lattices @ X5 )
      | ~ ( v4_lattice3 @ X5 )
      | ~ ( v10_lattices @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t34_lattice3])).

thf('8',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v2_struct_0 @ X5 )
      | ~ ( v10_lattices @ X5 )
      | ~ ( v4_lattice3 @ X5 )
      | ~ ( l3_lattices @ X5 )
      | ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X5 ) )
      | ( r3_lattices @ X5 @ X7 @ ( k16_lattice3 @ X5 @ X6 ) )
      | ~ ( r3_lattice3 @ X5 @ X7 @ X6 )
      | ~ ( m1_subset_1 @ ( k16_lattice3 @ X5 @ X6 ) @ ( u1_struct_0 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
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
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r3_lattices @ X0 @ X2 @ ( k16_lattice3 @ X0 @ X1 ) )
      | ~ ( r3_lattice3 @ X0 @ X2 @ X1 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( r3_lattice3 @ sk_A @ sk_B @ X0 )
      | ( r3_lattices @ sk_A @ sk_B @ ( k16_lattice3 @ sk_A @ X0 ) )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( v10_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','10'])).

thf('12',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r3_lattice3 @ sk_A @ sk_B @ X0 )
      | ( r3_lattices @ sk_A @ sk_B @ ( k16_lattice3 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['11','12','13','14'])).

thf('16',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r3_lattices @ sk_A @ sk_B @ ( k16_lattice3 @ sk_A @ X0 ) )
      | ~ ( r3_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['15','16'])).

thf('18',plain,(
    r3_lattices @ sk_A @ sk_B @ ( k16_lattice3 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1','17'])).

thf('19',plain,(
    $false ),
    inference(demod,[status(thm)],['0','18'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mfL1lCnncu
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:56:30 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 39 iterations in 0.035s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(r3_lattices_type, type, r3_lattices: $i > $i > $i > $o).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.49  thf(k16_lattice3_type, type, k16_lattice3: $i > $i > $i).
% 0.20/0.49  thf(r3_lattice3_type, type, r3_lattice3: $i > $i > $i > $o).
% 0.20/0.49  thf(k15_lattice3_type, type, k15_lattice3: $i > $i > $i).
% 0.20/0.49  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.49  thf(a_2_1_lattice3_type, type, a_2_1_lattice3: $i > $i > $i).
% 0.20/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.49  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 0.20/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.49  thf(v4_lattice3_type, type, v4_lattice3: $i > $o).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.49  thf(v10_lattices_type, type, v10_lattices: $i > $o).
% 0.20/0.49  thf(t40_lattice3, conjecture,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.20/0.49         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.49           ( ![C:$i]:
% 0.20/0.49             ( ( r3_lattice3 @ A @ B @ C ) =>
% 0.20/0.49               ( r3_lattices @ A @ B @ ( k16_lattice3 @ A @ C ) ) ) ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i]:
% 0.20/0.49        ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.20/0.49            ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.20/0.49          ( ![B:$i]:
% 0.20/0.49            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.49              ( ![C:$i]:
% 0.20/0.49                ( ( r3_lattice3 @ A @ B @ C ) =>
% 0.20/0.49                  ( r3_lattices @ A @ B @ ( k16_lattice3 @ A @ C ) ) ) ) ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t40_lattice3])).
% 0.20/0.49  thf('0', plain,
% 0.20/0.49      (~ (r3_lattices @ sk_A @ sk_B @ (k16_lattice3 @ sk_A @ sk_C))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('1', plain, ((r3_lattice3 @ sk_A @ sk_B @ sk_C)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('2', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(d22_lattice3, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( k16_lattice3 @ A @ B ) =
% 0.20/0.49           ( k15_lattice3 @ A @ ( a_2_1_lattice3 @ A @ B ) ) ) ) ))).
% 0.20/0.49  thf('3', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (((k16_lattice3 @ X0 @ X1)
% 0.20/0.49            = (k15_lattice3 @ X0 @ (a_2_1_lattice3 @ X0 @ X1)))
% 0.20/0.49          | ~ (l3_lattices @ X0)
% 0.20/0.49          | (v2_struct_0 @ X0))),
% 0.20/0.49      inference('cnf', [status(esa)], [d22_lattice3])).
% 0.20/0.49  thf(dt_k15_lattice3, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.20/0.49       ( m1_subset_1 @ ( k15_lattice3 @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 0.20/0.49  thf('4', plain,
% 0.20/0.49      (![X2 : $i, X3 : $i]:
% 0.20/0.49         (~ (l3_lattices @ X2)
% 0.20/0.49          | (v2_struct_0 @ X2)
% 0.20/0.49          | (m1_subset_1 @ (k15_lattice3 @ X2 @ X3) @ (u1_struct_0 @ X2)))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 0.20/0.49  thf('5', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         ((m1_subset_1 @ (k16_lattice3 @ X1 @ X0) @ (u1_struct_0 @ X1))
% 0.20/0.49          | (v2_struct_0 @ X1)
% 0.20/0.49          | ~ (l3_lattices @ X1)
% 0.20/0.49          | (v2_struct_0 @ X1)
% 0.20/0.49          | ~ (l3_lattices @ X1))),
% 0.20/0.49      inference('sup+', [status(thm)], ['3', '4'])).
% 0.20/0.49  thf('6', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (~ (l3_lattices @ X1)
% 0.20/0.49          | (v2_struct_0 @ X1)
% 0.20/0.49          | (m1_subset_1 @ (k16_lattice3 @ X1 @ X0) @ (u1_struct_0 @ X1)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['5'])).
% 0.20/0.49  thf(t34_lattice3, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.20/0.49         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.49           ( ![C:$i]:
% 0.20/0.49             ( ( ( B ) = ( k16_lattice3 @ A @ C ) ) <=>
% 0.20/0.49               ( ( r3_lattice3 @ A @ B @ C ) & 
% 0.20/0.49                 ( ![D:$i]:
% 0.20/0.49                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.49                     ( ( r3_lattice3 @ A @ D @ C ) =>
% 0.20/0.49                       ( r3_lattices @ A @ D @ B ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.49  thf('7', plain,
% 0.20/0.49      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 0.20/0.49          | ((X4) != (k16_lattice3 @ X5 @ X6))
% 0.20/0.49          | ~ (r3_lattice3 @ X5 @ X7 @ X6)
% 0.20/0.49          | (r3_lattices @ X5 @ X7 @ X4)
% 0.20/0.49          | ~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X5))
% 0.20/0.49          | ~ (l3_lattices @ X5)
% 0.20/0.49          | ~ (v4_lattice3 @ X5)
% 0.20/0.49          | ~ (v10_lattices @ X5)
% 0.20/0.49          | (v2_struct_0 @ X5))),
% 0.20/0.49      inference('cnf', [status(esa)], [t34_lattice3])).
% 0.20/0.49  thf('8', plain,
% 0.20/0.49      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.49         ((v2_struct_0 @ X5)
% 0.20/0.49          | ~ (v10_lattices @ X5)
% 0.20/0.49          | ~ (v4_lattice3 @ X5)
% 0.20/0.49          | ~ (l3_lattices @ X5)
% 0.20/0.49          | ~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X5))
% 0.20/0.49          | (r3_lattices @ X5 @ X7 @ (k16_lattice3 @ X5 @ X6))
% 0.20/0.49          | ~ (r3_lattice3 @ X5 @ X7 @ X6)
% 0.20/0.49          | ~ (m1_subset_1 @ (k16_lattice3 @ X5 @ X6) @ (u1_struct_0 @ X5)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['7'])).
% 0.20/0.49  thf('9', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.49         ((v2_struct_0 @ X0)
% 0.20/0.49          | ~ (l3_lattices @ X0)
% 0.20/0.49          | ~ (r3_lattice3 @ X0 @ X2 @ X1)
% 0.20/0.49          | (r3_lattices @ X0 @ X2 @ (k16_lattice3 @ X0 @ X1))
% 0.20/0.49          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.20/0.49          | ~ (l3_lattices @ X0)
% 0.20/0.49          | ~ (v4_lattice3 @ X0)
% 0.20/0.49          | ~ (v10_lattices @ X0)
% 0.20/0.49          | (v2_struct_0 @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['6', '8'])).
% 0.20/0.49  thf('10', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.49         (~ (v10_lattices @ X0)
% 0.20/0.49          | ~ (v4_lattice3 @ X0)
% 0.20/0.49          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.20/0.49          | (r3_lattices @ X0 @ X2 @ (k16_lattice3 @ X0 @ X1))
% 0.20/0.49          | ~ (r3_lattice3 @ X0 @ X2 @ X1)
% 0.20/0.49          | ~ (l3_lattices @ X0)
% 0.20/0.49          | (v2_struct_0 @ X0))),
% 0.20/0.49      inference('simplify', [status(thm)], ['9'])).
% 0.20/0.49  thf('11', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v2_struct_0 @ sk_A)
% 0.20/0.49          | ~ (l3_lattices @ sk_A)
% 0.20/0.49          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0)
% 0.20/0.49          | (r3_lattices @ sk_A @ sk_B @ (k16_lattice3 @ sk_A @ X0))
% 0.20/0.49          | ~ (v4_lattice3 @ sk_A)
% 0.20/0.49          | ~ (v10_lattices @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['2', '10'])).
% 0.20/0.49  thf('12', plain, ((l3_lattices @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('13', plain, ((v4_lattice3 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('14', plain, ((v10_lattices @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('15', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v2_struct_0 @ sk_A)
% 0.20/0.49          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0)
% 0.20/0.49          | (r3_lattices @ sk_A @ sk_B @ (k16_lattice3 @ sk_A @ X0)))),
% 0.20/0.49      inference('demod', [status(thm)], ['11', '12', '13', '14'])).
% 0.20/0.49  thf('16', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('17', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((r3_lattices @ sk_A @ sk_B @ (k16_lattice3 @ sk_A @ X0))
% 0.20/0.49          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 0.20/0.49      inference('clc', [status(thm)], ['15', '16'])).
% 0.20/0.49  thf('18', plain,
% 0.20/0.49      ((r3_lattices @ sk_A @ sk_B @ (k16_lattice3 @ sk_A @ sk_C))),
% 0.20/0.49      inference('sup-', [status(thm)], ['1', '17'])).
% 0.20/0.49  thf('19', plain, ($false), inference('demod', [status(thm)], ['0', '18'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
