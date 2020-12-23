%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6zN0bFclkX

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:53 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   34 (  36 expanded)
%              Number of leaves         :   17 (  18 expanded)
%              Depth                    :   10
%              Number of atoms          :  236 ( 252 expanded)
%              Number of equality atoms :   24 (  26 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_relset_1_type,type,(
    k3_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_orders_2_type,type,(
    v1_orders_2: $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k7_lattice3_type,type,(
    k7_lattice3: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(g1_orders_2_type,type,(
    g1_orders_2: $i > $i > $i )).

thf(d5_lattice3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( k7_lattice3 @ A )
        = ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( k3_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) ) ) ) ) )).

thf('0',plain,(
    ! [X5: $i] :
      ( ( ( k7_lattice3 @ X5 )
        = ( g1_orders_2 @ ( u1_struct_0 @ X5 ) @ ( k3_relset_1 @ ( u1_struct_0 @ X5 ) @ ( u1_struct_0 @ X5 ) @ ( u1_orders_2 @ X5 ) ) ) )
      | ~ ( l1_orders_2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_lattice3])).

thf(t8_lattice3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( k7_lattice3 @ ( k7_lattice3 @ A ) )
        = ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X7: $i] :
      ( ( ( k7_lattice3 @ ( k7_lattice3 @ X7 ) )
        = ( g1_orders_2 @ ( u1_struct_0 @ X7 ) @ ( u1_orders_2 @ X7 ) ) )
      | ~ ( l1_orders_2 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t8_lattice3])).

thf(dt_u1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( u1_orders_2 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('2',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_orders_2])).

thf(free_g1_orders_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
     => ! [C: $i,D: $i] :
          ( ( ( g1_orders_2 @ A @ B )
            = ( g1_orders_2 @ C @ D ) )
         => ( ( A = C )
            & ( B = D ) ) ) ) )).

thf('3',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( ( g1_orders_2 @ X3 @ X4 )
       != ( g1_orders_2 @ X1 @ X2 ) )
      | ( X3 = X1 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_orders_2])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = X1 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) )
       != ( g1_orders_2 @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_lattice3 @ ( k7_lattice3 @ X0 ) )
       != ( g1_orders_2 @ X2 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = X2 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( u1_struct_0 @ X0 )
        = X2 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( k7_lattice3 @ ( k7_lattice3 @ X0 ) )
       != ( g1_orders_2 @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_lattice3 @ ( k7_lattice3 @ X1 ) )
       != ( k7_lattice3 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X1 )
      | ( ( u1_struct_0 @ X1 )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
        = ( u1_struct_0 @ ( k7_lattice3 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ ( k7_lattice3 @ X0 ) ) ) ),
    inference(eq_res,[status(thm)],['7'])).

thf(dt_k7_lattice3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v1_orders_2 @ ( k7_lattice3 @ A ) )
        & ( l1_orders_2 @ ( k7_lattice3 @ A ) ) ) ) )).

thf('9',plain,(
    ! [X6: $i] :
      ( ( l1_orders_2 @ ( k7_lattice3 @ X6 ) )
      | ~ ( l1_orders_2 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k7_lattice3])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( u1_struct_0 @ ( k7_lattice3 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf(t12_yellow_6,conjecture,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( u1_struct_0 @ A )
        = ( u1_struct_0 @ ( k7_lattice3 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_orders_2 @ A )
       => ( ( u1_struct_0 @ A )
          = ( u1_struct_0 @ ( k7_lattice3 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t12_yellow_6])).

thf('11',plain,(
    ( u1_struct_0 @ sk_A )
 != ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( ( u1_struct_0 @ sk_A )
     != ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ( u1_struct_0 @ sk_A )
 != ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    $false ),
    inference(simplify,[status(thm)],['14'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6zN0bFclkX
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:43:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.46  % Solved by: fo/fo7.sh
% 0.20/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.46  % done 15 iterations in 0.010s
% 0.20/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.46  % SZS output start Refutation
% 0.20/0.46  thf(k3_relset_1_type, type, k3_relset_1: $i > $i > $i > $i).
% 0.20/0.46  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.46  thf(v1_orders_2_type, type, v1_orders_2: $i > $o).
% 0.20/0.46  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.20/0.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.46  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.20/0.46  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.46  thf(k7_lattice3_type, type, k7_lattice3: $i > $i).
% 0.20/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.46  thf(g1_orders_2_type, type, g1_orders_2: $i > $i > $i).
% 0.20/0.46  thf(d5_lattice3, axiom,
% 0.20/0.46    (![A:$i]:
% 0.20/0.46     ( ( l1_orders_2 @ A ) =>
% 0.20/0.46       ( ( k7_lattice3 @ A ) =
% 0.20/0.46         ( g1_orders_2 @
% 0.20/0.46           ( u1_struct_0 @ A ) @ 
% 0.20/0.46           ( k3_relset_1 @
% 0.20/0.46             ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) ) ) ) ))).
% 0.20/0.46  thf('0', plain,
% 0.20/0.46      (![X5 : $i]:
% 0.20/0.46         (((k7_lattice3 @ X5)
% 0.20/0.46            = (g1_orders_2 @ (u1_struct_0 @ X5) @ 
% 0.20/0.46               (k3_relset_1 @ (u1_struct_0 @ X5) @ (u1_struct_0 @ X5) @ 
% 0.20/0.46                (u1_orders_2 @ X5))))
% 0.20/0.46          | ~ (l1_orders_2 @ X5))),
% 0.20/0.46      inference('cnf', [status(esa)], [d5_lattice3])).
% 0.20/0.46  thf(t8_lattice3, axiom,
% 0.20/0.46    (![A:$i]:
% 0.20/0.46     ( ( l1_orders_2 @ A ) =>
% 0.20/0.46       ( ( k7_lattice3 @ ( k7_lattice3 @ A ) ) =
% 0.20/0.46         ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) ) ) ))).
% 0.20/0.46  thf('1', plain,
% 0.20/0.46      (![X7 : $i]:
% 0.20/0.46         (((k7_lattice3 @ (k7_lattice3 @ X7))
% 0.20/0.46            = (g1_orders_2 @ (u1_struct_0 @ X7) @ (u1_orders_2 @ X7)))
% 0.20/0.46          | ~ (l1_orders_2 @ X7))),
% 0.20/0.46      inference('cnf', [status(esa)], [t8_lattice3])).
% 0.20/0.46  thf(dt_u1_orders_2, axiom,
% 0.20/0.46    (![A:$i]:
% 0.20/0.46     ( ( l1_orders_2 @ A ) =>
% 0.20/0.46       ( m1_subset_1 @
% 0.20/0.46         ( u1_orders_2 @ A ) @ 
% 0.20/0.46         ( k1_zfmisc_1 @
% 0.20/0.46           ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.20/0.46  thf('2', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         ((m1_subset_1 @ (u1_orders_2 @ X0) @ 
% 0.20/0.46           (k1_zfmisc_1 @ 
% 0.20/0.46            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0))))
% 0.20/0.46          | ~ (l1_orders_2 @ X0))),
% 0.20/0.46      inference('cnf', [status(esa)], [dt_u1_orders_2])).
% 0.20/0.46  thf(free_g1_orders_2, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) =>
% 0.20/0.46       ( ![C:$i,D:$i]:
% 0.20/0.46         ( ( ( g1_orders_2 @ A @ B ) = ( g1_orders_2 @ C @ D ) ) =>
% 0.20/0.46           ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) ))).
% 0.20/0.46  thf('3', plain,
% 0.20/0.46      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.46         (((g1_orders_2 @ X3 @ X4) != (g1_orders_2 @ X1 @ X2))
% 0.20/0.46          | ((X3) = (X1))
% 0.20/0.46          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X3))))),
% 0.20/0.46      inference('cnf', [status(esa)], [free_g1_orders_2])).
% 0.20/0.46  thf('4', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.46         (~ (l1_orders_2 @ X0)
% 0.20/0.46          | ((u1_struct_0 @ X0) = (X1))
% 0.20/0.46          | ((g1_orders_2 @ (u1_struct_0 @ X0) @ (u1_orders_2 @ X0))
% 0.20/0.46              != (g1_orders_2 @ X1 @ X2)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.46  thf('5', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.46         (((k7_lattice3 @ (k7_lattice3 @ X0)) != (g1_orders_2 @ X2 @ X1))
% 0.20/0.46          | ~ (l1_orders_2 @ X0)
% 0.20/0.46          | ((u1_struct_0 @ X0) = (X2))
% 0.20/0.46          | ~ (l1_orders_2 @ X0))),
% 0.20/0.46      inference('sup-', [status(thm)], ['1', '4'])).
% 0.20/0.46  thf('6', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.46         (((u1_struct_0 @ X0) = (X2))
% 0.20/0.46          | ~ (l1_orders_2 @ X0)
% 0.20/0.46          | ((k7_lattice3 @ (k7_lattice3 @ X0)) != (g1_orders_2 @ X2 @ X1)))),
% 0.20/0.46      inference('simplify', [status(thm)], ['5'])).
% 0.20/0.46  thf('7', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i]:
% 0.20/0.46         (((k7_lattice3 @ (k7_lattice3 @ X1)) != (k7_lattice3 @ X0))
% 0.20/0.46          | ~ (l1_orders_2 @ X0)
% 0.20/0.46          | ~ (l1_orders_2 @ X1)
% 0.20/0.46          | ((u1_struct_0 @ X1) = (u1_struct_0 @ X0)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['0', '6'])).
% 0.20/0.46  thf('8', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         (((u1_struct_0 @ X0) = (u1_struct_0 @ (k7_lattice3 @ X0)))
% 0.20/0.46          | ~ (l1_orders_2 @ X0)
% 0.20/0.46          | ~ (l1_orders_2 @ (k7_lattice3 @ X0)))),
% 0.20/0.46      inference('eq_res', [status(thm)], ['7'])).
% 0.20/0.46  thf(dt_k7_lattice3, axiom,
% 0.20/0.46    (![A:$i]:
% 0.20/0.46     ( ( l1_orders_2 @ A ) =>
% 0.20/0.46       ( ( v1_orders_2 @ ( k7_lattice3 @ A ) ) & 
% 0.20/0.46         ( l1_orders_2 @ ( k7_lattice3 @ A ) ) ) ))).
% 0.20/0.46  thf('9', plain,
% 0.20/0.46      (![X6 : $i]: ((l1_orders_2 @ (k7_lattice3 @ X6)) | ~ (l1_orders_2 @ X6))),
% 0.20/0.46      inference('cnf', [status(esa)], [dt_k7_lattice3])).
% 0.20/0.46  thf('10', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         (~ (l1_orders_2 @ X0)
% 0.20/0.46          | ((u1_struct_0 @ X0) = (u1_struct_0 @ (k7_lattice3 @ X0))))),
% 0.20/0.46      inference('clc', [status(thm)], ['8', '9'])).
% 0.20/0.46  thf(t12_yellow_6, conjecture,
% 0.20/0.46    (![A:$i]:
% 0.20/0.46     ( ( l1_orders_2 @ A ) =>
% 0.20/0.46       ( ( u1_struct_0 @ A ) = ( u1_struct_0 @ ( k7_lattice3 @ A ) ) ) ))).
% 0.20/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.46    (~( ![A:$i]:
% 0.20/0.46        ( ( l1_orders_2 @ A ) =>
% 0.20/0.46          ( ( u1_struct_0 @ A ) = ( u1_struct_0 @ ( k7_lattice3 @ A ) ) ) ) )),
% 0.20/0.46    inference('cnf.neg', [status(esa)], [t12_yellow_6])).
% 0.20/0.46  thf('11', plain,
% 0.20/0.46      (((u1_struct_0 @ sk_A) != (u1_struct_0 @ (k7_lattice3 @ sk_A)))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('12', plain,
% 0.20/0.46      ((((u1_struct_0 @ sk_A) != (u1_struct_0 @ sk_A)) | ~ (l1_orders_2 @ sk_A))),
% 0.20/0.46      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.46  thf('13', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('14', plain, (((u1_struct_0 @ sk_A) != (u1_struct_0 @ sk_A))),
% 0.20/0.46      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.46  thf('15', plain, ($false), inference('simplify', [status(thm)], ['14'])).
% 0.20/0.46  
% 0.20/0.46  % SZS output end Refutation
% 0.20/0.46  
% 0.20/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
