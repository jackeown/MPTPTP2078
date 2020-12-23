%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0mhs2JQSEY

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:53 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   36 (  39 expanded)
%              Number of leaves         :   17 (  19 expanded)
%              Depth                    :   11
%              Number of atoms          :  259 ( 283 expanded)
%              Number of equality atoms :   24 (  26 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_lattice3_type,type,(
    k7_lattice3: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(k3_relset_1_type,type,(
    k3_relset_1: $i > $i > $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(g1_orders_2_type,type,(
    g1_orders_2: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_orders_2_type,type,(
    v1_orders_2: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(dt_k7_lattice3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v1_orders_2 @ ( k7_lattice3 @ A ) )
        & ( l1_orders_2 @ ( k7_lattice3 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X7: $i] :
      ( ( v1_orders_2 @ ( k7_lattice3 @ X7 ) )
      | ~ ( l1_orders_2 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k7_lattice3])).

thf(abstractness_v1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v1_orders_2 @ A )
       => ( A
          = ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X0: $i] :
      ( ~ ( v1_orders_2 @ X0 )
      | ( X0
        = ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_orders_2])).

thf(d5_lattice3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( k7_lattice3 @ A )
        = ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( k3_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) ) ) ) ) )).

thf('2',plain,(
    ! [X6: $i] :
      ( ( ( k7_lattice3 @ X6 )
        = ( g1_orders_2 @ ( u1_struct_0 @ X6 ) @ ( k3_relset_1 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X6 ) @ ( u1_orders_2 @ X6 ) ) ) )
      | ~ ( l1_orders_2 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d5_lattice3])).

thf(dt_u1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( u1_orders_2 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('3',plain,(
    ! [X1: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X1 ) ) ) )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_orders_2])).

thf(free_g1_orders_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
     => ! [C: $i,D: $i] :
          ( ( ( g1_orders_2 @ A @ B )
            = ( g1_orders_2 @ C @ D ) )
         => ( ( A = C )
            & ( B = D ) ) ) ) )).

thf('4',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( ( g1_orders_2 @ X4 @ X5 )
       != ( g1_orders_2 @ X2 @ X3 ) )
      | ( X4 = X2 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_orders_2])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = X1 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) )
       != ( g1_orders_2 @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ X1 ) @ ( u1_orders_2 @ X1 ) )
       != ( k7_lattice3 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( u1_struct_0 @ X1 )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
       != ( k7_lattice3 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    ! [X1: $i] :
      ( ~ ( l1_orders_2 @ X1 )
      | ( ( u1_struct_0 @ ( k7_lattice3 @ X1 ) )
        = ( u1_struct_0 @ X1 ) )
      | ~ ( v1_orders_2 @ ( k7_lattice3 @ X1 ) )
      | ~ ( l1_orders_2 @ ( k7_lattice3 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ ( k7_lattice3 @ X0 ) )
      | ( ( u1_struct_0 @ ( k7_lattice3 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ ( k7_lattice3 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ ( k7_lattice3 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X7: $i] :
      ( ( l1_orders_2 @ ( k7_lattice3 @ X7 ) )
      | ~ ( l1_orders_2 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k7_lattice3])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( u1_struct_0 @ ( k7_lattice3 @ X0 ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['10','11'])).

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

thf('13',plain,(
    ( u1_struct_0 @ sk_A )
 != ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( ( u1_struct_0 @ sk_A )
     != ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ( u1_struct_0 @ sk_A )
 != ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    $false ),
    inference(simplify,[status(thm)],['16'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0mhs2JQSEY
% 0.15/0.38  % Computer   : n011.cluster.edu
% 0.15/0.38  % Model      : x86_64 x86_64
% 0.15/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.38  % Memory     : 8042.1875MB
% 0.15/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.38  % CPULimit   : 60
% 0.15/0.38  % DateTime   : Tue Dec  1 20:43:27 EST 2020
% 0.15/0.38  % CPUTime    : 
% 0.15/0.38  % Running portfolio for 600 s
% 0.15/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 0.24/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.51  % Solved by: fo/fo7.sh
% 0.24/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.51  % done 15 iterations in 0.017s
% 0.24/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.51  % SZS output start Refutation
% 0.24/0.51  thf(k7_lattice3_type, type, k7_lattice3: $i > $i).
% 0.24/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.24/0.51  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.24/0.51  thf(k3_relset_1_type, type, k3_relset_1: $i > $i > $i > $i).
% 0.24/0.51  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.24/0.51  thf(g1_orders_2_type, type, g1_orders_2: $i > $i > $i).
% 0.24/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.24/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.24/0.51  thf(v1_orders_2_type, type, v1_orders_2: $i > $o).
% 0.24/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.24/0.51  thf(dt_k7_lattice3, axiom,
% 0.24/0.51    (![A:$i]:
% 0.24/0.51     ( ( l1_orders_2 @ A ) =>
% 0.24/0.51       ( ( v1_orders_2 @ ( k7_lattice3 @ A ) ) & 
% 0.24/0.51         ( l1_orders_2 @ ( k7_lattice3 @ A ) ) ) ))).
% 0.24/0.51  thf('0', plain,
% 0.24/0.51      (![X7 : $i]: ((v1_orders_2 @ (k7_lattice3 @ X7)) | ~ (l1_orders_2 @ X7))),
% 0.24/0.51      inference('cnf', [status(esa)], [dt_k7_lattice3])).
% 0.24/0.51  thf(abstractness_v1_orders_2, axiom,
% 0.24/0.51    (![A:$i]:
% 0.24/0.51     ( ( l1_orders_2 @ A ) =>
% 0.24/0.51       ( ( v1_orders_2 @ A ) =>
% 0.24/0.51         ( ( A ) = ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) ) ) ) ))).
% 0.24/0.51  thf('1', plain,
% 0.24/0.51      (![X0 : $i]:
% 0.24/0.51         (~ (v1_orders_2 @ X0)
% 0.24/0.51          | ((X0) = (g1_orders_2 @ (u1_struct_0 @ X0) @ (u1_orders_2 @ X0)))
% 0.24/0.51          | ~ (l1_orders_2 @ X0))),
% 0.24/0.51      inference('cnf', [status(esa)], [abstractness_v1_orders_2])).
% 0.24/0.51  thf(d5_lattice3, axiom,
% 0.24/0.51    (![A:$i]:
% 0.24/0.51     ( ( l1_orders_2 @ A ) =>
% 0.24/0.51       ( ( k7_lattice3 @ A ) =
% 0.24/0.51         ( g1_orders_2 @
% 0.24/0.51           ( u1_struct_0 @ A ) @ 
% 0.24/0.51           ( k3_relset_1 @
% 0.24/0.51             ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) ) ) ) ))).
% 0.24/0.51  thf('2', plain,
% 0.24/0.51      (![X6 : $i]:
% 0.24/0.51         (((k7_lattice3 @ X6)
% 0.24/0.51            = (g1_orders_2 @ (u1_struct_0 @ X6) @ 
% 0.24/0.51               (k3_relset_1 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X6) @ 
% 0.24/0.51                (u1_orders_2 @ X6))))
% 0.24/0.51          | ~ (l1_orders_2 @ X6))),
% 0.24/0.51      inference('cnf', [status(esa)], [d5_lattice3])).
% 0.24/0.51  thf(dt_u1_orders_2, axiom,
% 0.24/0.51    (![A:$i]:
% 0.24/0.51     ( ( l1_orders_2 @ A ) =>
% 0.24/0.51       ( m1_subset_1 @
% 0.24/0.51         ( u1_orders_2 @ A ) @ 
% 0.24/0.51         ( k1_zfmisc_1 @
% 0.24/0.51           ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.24/0.51  thf('3', plain,
% 0.24/0.51      (![X1 : $i]:
% 0.24/0.51         ((m1_subset_1 @ (u1_orders_2 @ X1) @ 
% 0.24/0.51           (k1_zfmisc_1 @ 
% 0.24/0.51            (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X1))))
% 0.24/0.51          | ~ (l1_orders_2 @ X1))),
% 0.24/0.51      inference('cnf', [status(esa)], [dt_u1_orders_2])).
% 0.24/0.51  thf(free_g1_orders_2, axiom,
% 0.24/0.51    (![A:$i,B:$i]:
% 0.24/0.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) =>
% 0.24/0.51       ( ![C:$i,D:$i]:
% 0.24/0.51         ( ( ( g1_orders_2 @ A @ B ) = ( g1_orders_2 @ C @ D ) ) =>
% 0.24/0.51           ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) ))).
% 0.24/0.51  thf('4', plain,
% 0.24/0.51      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.24/0.51         (((g1_orders_2 @ X4 @ X5) != (g1_orders_2 @ X2 @ X3))
% 0.24/0.51          | ((X4) = (X2))
% 0.24/0.51          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X4))))),
% 0.24/0.51      inference('cnf', [status(esa)], [free_g1_orders_2])).
% 0.24/0.51  thf('5', plain,
% 0.24/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.24/0.51         (~ (l1_orders_2 @ X0)
% 0.24/0.51          | ((u1_struct_0 @ X0) = (X1))
% 0.24/0.51          | ((g1_orders_2 @ (u1_struct_0 @ X0) @ (u1_orders_2 @ X0))
% 0.24/0.51              != (g1_orders_2 @ X1 @ X2)))),
% 0.24/0.51      inference('sup-', [status(thm)], ['3', '4'])).
% 0.24/0.51  thf('6', plain,
% 0.24/0.51      (![X0 : $i, X1 : $i]:
% 0.24/0.51         (((g1_orders_2 @ (u1_struct_0 @ X1) @ (u1_orders_2 @ X1))
% 0.24/0.51            != (k7_lattice3 @ X0))
% 0.24/0.51          | ~ (l1_orders_2 @ X0)
% 0.24/0.51          | ((u1_struct_0 @ X1) = (u1_struct_0 @ X0))
% 0.24/0.51          | ~ (l1_orders_2 @ X1))),
% 0.24/0.51      inference('sup-', [status(thm)], ['2', '5'])).
% 0.24/0.51  thf('7', plain,
% 0.24/0.51      (![X0 : $i, X1 : $i]:
% 0.24/0.51         (((X0) != (k7_lattice3 @ X1))
% 0.24/0.51          | ~ (l1_orders_2 @ X0)
% 0.24/0.51          | ~ (v1_orders_2 @ X0)
% 0.24/0.51          | ~ (l1_orders_2 @ X0)
% 0.24/0.51          | ((u1_struct_0 @ X0) = (u1_struct_0 @ X1))
% 0.24/0.51          | ~ (l1_orders_2 @ X1))),
% 0.24/0.51      inference('sup-', [status(thm)], ['1', '6'])).
% 0.24/0.51  thf('8', plain,
% 0.24/0.51      (![X1 : $i]:
% 0.24/0.51         (~ (l1_orders_2 @ X1)
% 0.24/0.51          | ((u1_struct_0 @ (k7_lattice3 @ X1)) = (u1_struct_0 @ X1))
% 0.24/0.51          | ~ (v1_orders_2 @ (k7_lattice3 @ X1))
% 0.24/0.51          | ~ (l1_orders_2 @ (k7_lattice3 @ X1)))),
% 0.24/0.51      inference('simplify', [status(thm)], ['7'])).
% 0.24/0.51  thf('9', plain,
% 0.24/0.51      (![X0 : $i]:
% 0.24/0.51         (~ (l1_orders_2 @ X0)
% 0.24/0.51          | ~ (l1_orders_2 @ (k7_lattice3 @ X0))
% 0.24/0.51          | ((u1_struct_0 @ (k7_lattice3 @ X0)) = (u1_struct_0 @ X0))
% 0.24/0.51          | ~ (l1_orders_2 @ X0))),
% 0.24/0.51      inference('sup-', [status(thm)], ['0', '8'])).
% 0.24/0.51  thf('10', plain,
% 0.24/0.51      (![X0 : $i]:
% 0.24/0.51         (((u1_struct_0 @ (k7_lattice3 @ X0)) = (u1_struct_0 @ X0))
% 0.24/0.51          | ~ (l1_orders_2 @ (k7_lattice3 @ X0))
% 0.24/0.51          | ~ (l1_orders_2 @ X0))),
% 0.24/0.51      inference('simplify', [status(thm)], ['9'])).
% 0.24/0.51  thf('11', plain,
% 0.24/0.51      (![X7 : $i]: ((l1_orders_2 @ (k7_lattice3 @ X7)) | ~ (l1_orders_2 @ X7))),
% 0.24/0.51      inference('cnf', [status(esa)], [dt_k7_lattice3])).
% 0.24/0.51  thf('12', plain,
% 0.24/0.51      (![X0 : $i]:
% 0.24/0.51         (~ (l1_orders_2 @ X0)
% 0.24/0.51          | ((u1_struct_0 @ (k7_lattice3 @ X0)) = (u1_struct_0 @ X0)))),
% 0.24/0.51      inference('clc', [status(thm)], ['10', '11'])).
% 0.24/0.51  thf(t12_yellow_6, conjecture,
% 0.24/0.51    (![A:$i]:
% 0.24/0.51     ( ( l1_orders_2 @ A ) =>
% 0.24/0.51       ( ( u1_struct_0 @ A ) = ( u1_struct_0 @ ( k7_lattice3 @ A ) ) ) ))).
% 0.24/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.51    (~( ![A:$i]:
% 0.24/0.51        ( ( l1_orders_2 @ A ) =>
% 0.24/0.51          ( ( u1_struct_0 @ A ) = ( u1_struct_0 @ ( k7_lattice3 @ A ) ) ) ) )),
% 0.24/0.51    inference('cnf.neg', [status(esa)], [t12_yellow_6])).
% 0.24/0.51  thf('13', plain,
% 0.24/0.51      (((u1_struct_0 @ sk_A) != (u1_struct_0 @ (k7_lattice3 @ sk_A)))),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf('14', plain,
% 0.24/0.51      ((((u1_struct_0 @ sk_A) != (u1_struct_0 @ sk_A)) | ~ (l1_orders_2 @ sk_A))),
% 0.24/0.51      inference('sup-', [status(thm)], ['12', '13'])).
% 0.24/0.51  thf('15', plain, ((l1_orders_2 @ sk_A)),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf('16', plain, (((u1_struct_0 @ sk_A) != (u1_struct_0 @ sk_A))),
% 0.24/0.51      inference('demod', [status(thm)], ['14', '15'])).
% 0.24/0.51  thf('17', plain, ($false), inference('simplify', [status(thm)], ['16'])).
% 0.24/0.51  
% 0.24/0.51  % SZS output end Refutation
% 0.24/0.51  
% 0.24/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
