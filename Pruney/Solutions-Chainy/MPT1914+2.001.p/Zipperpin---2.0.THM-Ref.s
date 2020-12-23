%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gTgRUZYxXB

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:53 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   49 (  59 expanded)
%              Number of leaves         :   18 (  25 expanded)
%              Depth                    :   11
%              Number of atoms          :  428 ( 551 expanded)
%              Number of equality atoms :   26 (  30 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(k3_relset_1_type,type,(
    k3_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_orders_2_type,type,(
    v1_orders_2: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_lattice3_type,type,(
    k7_lattice3: $i > $i )).

thf(g1_orders_2_type,type,(
    g1_orders_2: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(d5_lattice3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( k7_lattice3 @ A )
        = ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( k3_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) ) ) ) ) )).

thf('0',plain,(
    ! [X14: $i] :
      ( ( ( k7_lattice3 @ X14 )
        = ( g1_orders_2 @ ( u1_struct_0 @ X14 ) @ ( k3_relset_1 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X14 ) @ ( u1_orders_2 @ X14 ) ) ) )
      | ~ ( l1_orders_2 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d5_lattice3])).

thf(dt_u1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( u1_orders_2 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X9: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X9 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X9 ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( l1_orders_2 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_orders_2])).

thf(dt_k3_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k3_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k3_relset_1 @ X0 @ X1 @ X2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( m1_subset_1 @ ( k3_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(dt_g1_orders_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
     => ( ( v1_orders_2 @ ( g1_orders_2 @ A @ B ) )
        & ( l1_orders_2 @ ( g1_orders_2 @ A @ B ) ) ) ) )).

thf('4',plain,(
    ! [X7: $i,X8: $i] :
      ( ( v1_orders_2 @ ( g1_orders_2 @ X7 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_g1_orders_2])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_orders_2 @ ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( k3_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( v1_orders_2 @ ( k7_lattice3 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_orders_2 @ ( k7_lattice3 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(abstractness_v1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v1_orders_2 @ A )
       => ( A
          = ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) ) ) ) ) )).

thf('8',plain,(
    ! [X6: $i] :
      ( ~ ( v1_orders_2 @ X6 )
      | ( X6
        = ( g1_orders_2 @ ( u1_struct_0 @ X6 ) @ ( u1_orders_2 @ X6 ) ) )
      | ~ ( l1_orders_2 @ X6 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_orders_2])).

thf('9',plain,(
    ! [X14: $i] :
      ( ( ( k7_lattice3 @ X14 )
        = ( g1_orders_2 @ ( u1_struct_0 @ X14 ) @ ( k3_relset_1 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X14 ) @ ( u1_orders_2 @ X14 ) ) ) )
      | ~ ( l1_orders_2 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d5_lattice3])).

thf('10',plain,(
    ! [X9: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X9 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X9 ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( l1_orders_2 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_orders_2])).

thf(free_g1_orders_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
     => ! [C: $i,D: $i] :
          ( ( ( g1_orders_2 @ A @ B )
            = ( g1_orders_2 @ C @ D ) )
         => ( ( A = C )
            & ( B = D ) ) ) ) )).

thf('11',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( ( g1_orders_2 @ X12 @ X13 )
       != ( g1_orders_2 @ X10 @ X11 ) )
      | ( X12 = X10 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_orders_2])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = X1 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) )
       != ( g1_orders_2 @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ X1 ) @ ( u1_orders_2 @ X1 ) )
       != ( k7_lattice3 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( u1_struct_0 @ X1 )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
       != ( k7_lattice3 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf('15',plain,(
    ! [X1: $i] :
      ( ~ ( l1_orders_2 @ X1 )
      | ( ( u1_struct_0 @ ( k7_lattice3 @ X1 ) )
        = ( u1_struct_0 @ X1 ) )
      | ~ ( v1_orders_2 @ ( k7_lattice3 @ X1 ) )
      | ~ ( l1_orders_2 @ ( k7_lattice3 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ ( k7_lattice3 @ X0 ) )
      | ( ( u1_struct_0 @ ( k7_lattice3 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ ( k7_lattice3 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ ( k7_lattice3 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X14: $i] :
      ( ( ( k7_lattice3 @ X14 )
        = ( g1_orders_2 @ ( u1_struct_0 @ X14 ) @ ( k3_relset_1 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X14 ) @ ( u1_orders_2 @ X14 ) ) ) )
      | ~ ( l1_orders_2 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d5_lattice3])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( m1_subset_1 @ ( k3_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('20',plain,(
    ! [X7: $i,X8: $i] :
      ( ( l1_orders_2 @ ( g1_orders_2 @ X7 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_g1_orders_2])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( l1_orders_2 @ ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( k3_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( l1_orders_2 @ ( k7_lattice3 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( l1_orders_2 @ ( k7_lattice3 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( u1_struct_0 @ ( k7_lattice3 @ X0 ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['17','23'])).

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

thf('25',plain,(
    ( u1_struct_0 @ sk_A )
 != ( u1_struct_0 @ ( k7_lattice3 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( ( u1_struct_0 @ sk_A )
     != ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ( u1_struct_0 @ sk_A )
 != ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    $false ),
    inference(simplify,[status(thm)],['28'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gTgRUZYxXB
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:38:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 33 iterations in 0.032s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.20/0.48  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.20/0.48  thf(k3_relset_1_type, type, k3_relset_1: $i > $i > $i > $i).
% 0.20/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.48  thf(v1_orders_2_type, type, v1_orders_2: $i > $o).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(k7_lattice3_type, type, k7_lattice3: $i > $i).
% 0.20/0.48  thf(g1_orders_2_type, type, g1_orders_2: $i > $i > $i).
% 0.20/0.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.48  thf(d5_lattice3, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( l1_orders_2 @ A ) =>
% 0.20/0.48       ( ( k7_lattice3 @ A ) =
% 0.20/0.48         ( g1_orders_2 @
% 0.20/0.48           ( u1_struct_0 @ A ) @ 
% 0.20/0.48           ( k3_relset_1 @
% 0.20/0.48             ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) ) ) ) ))).
% 0.20/0.48  thf('0', plain,
% 0.20/0.48      (![X14 : $i]:
% 0.20/0.48         (((k7_lattice3 @ X14)
% 0.20/0.48            = (g1_orders_2 @ (u1_struct_0 @ X14) @ 
% 0.20/0.48               (k3_relset_1 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X14) @ 
% 0.20/0.48                (u1_orders_2 @ X14))))
% 0.20/0.48          | ~ (l1_orders_2 @ X14))),
% 0.20/0.48      inference('cnf', [status(esa)], [d5_lattice3])).
% 0.20/0.48  thf(dt_u1_orders_2, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( l1_orders_2 @ A ) =>
% 0.20/0.48       ( m1_subset_1 @
% 0.20/0.48         ( u1_orders_2 @ A ) @ 
% 0.20/0.48         ( k1_zfmisc_1 @
% 0.20/0.48           ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.20/0.48  thf('1', plain,
% 0.20/0.48      (![X9 : $i]:
% 0.20/0.48         ((m1_subset_1 @ (u1_orders_2 @ X9) @ 
% 0.20/0.48           (k1_zfmisc_1 @ 
% 0.20/0.48            (k2_zfmisc_1 @ (u1_struct_0 @ X9) @ (u1_struct_0 @ X9))))
% 0.20/0.48          | ~ (l1_orders_2 @ X9))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_u1_orders_2])).
% 0.20/0.48  thf(dt_k3_relset_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.48       ( m1_subset_1 @
% 0.20/0.48         ( k3_relset_1 @ A @ B @ C ) @ 
% 0.20/0.48         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ))).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.48         ((m1_subset_1 @ (k3_relset_1 @ X0 @ X1 @ X2) @ 
% 0.20/0.48           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 0.20/0.48          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1))))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_k3_relset_1])).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (l1_orders_2 @ X0)
% 0.20/0.48          | (m1_subset_1 @ 
% 0.20/0.48             (k3_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ 
% 0.20/0.48              (u1_orders_2 @ X0)) @ 
% 0.20/0.48             (k1_zfmisc_1 @ 
% 0.20/0.48              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0)))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.48  thf(dt_g1_orders_2, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) =>
% 0.20/0.48       ( ( v1_orders_2 @ ( g1_orders_2 @ A @ B ) ) & 
% 0.20/0.48         ( l1_orders_2 @ ( g1_orders_2 @ A @ B ) ) ) ))).
% 0.20/0.48  thf('4', plain,
% 0.20/0.48      (![X7 : $i, X8 : $i]:
% 0.20/0.48         ((v1_orders_2 @ (g1_orders_2 @ X7 @ X8))
% 0.20/0.48          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X7))))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_g1_orders_2])).
% 0.20/0.48  thf('5', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (l1_orders_2 @ X0)
% 0.20/0.48          | (v1_orders_2 @ 
% 0.20/0.48             (g1_orders_2 @ (u1_struct_0 @ X0) @ 
% 0.20/0.48              (k3_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ 
% 0.20/0.48               (u1_orders_2 @ X0)))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.48  thf('6', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((v1_orders_2 @ (k7_lattice3 @ X0))
% 0.20/0.48          | ~ (l1_orders_2 @ X0)
% 0.20/0.48          | ~ (l1_orders_2 @ X0))),
% 0.20/0.48      inference('sup+', [status(thm)], ['0', '5'])).
% 0.20/0.48  thf('7', plain,
% 0.20/0.48      (![X0 : $i]: (~ (l1_orders_2 @ X0) | (v1_orders_2 @ (k7_lattice3 @ X0)))),
% 0.20/0.48      inference('simplify', [status(thm)], ['6'])).
% 0.20/0.48  thf(abstractness_v1_orders_2, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( l1_orders_2 @ A ) =>
% 0.20/0.48       ( ( v1_orders_2 @ A ) =>
% 0.20/0.48         ( ( A ) = ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) ) ) ) ))).
% 0.20/0.48  thf('8', plain,
% 0.20/0.48      (![X6 : $i]:
% 0.20/0.48         (~ (v1_orders_2 @ X6)
% 0.20/0.48          | ((X6) = (g1_orders_2 @ (u1_struct_0 @ X6) @ (u1_orders_2 @ X6)))
% 0.20/0.48          | ~ (l1_orders_2 @ X6))),
% 0.20/0.48      inference('cnf', [status(esa)], [abstractness_v1_orders_2])).
% 0.20/0.48  thf('9', plain,
% 0.20/0.48      (![X14 : $i]:
% 0.20/0.48         (((k7_lattice3 @ X14)
% 0.20/0.48            = (g1_orders_2 @ (u1_struct_0 @ X14) @ 
% 0.20/0.48               (k3_relset_1 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X14) @ 
% 0.20/0.48                (u1_orders_2 @ X14))))
% 0.20/0.48          | ~ (l1_orders_2 @ X14))),
% 0.20/0.48      inference('cnf', [status(esa)], [d5_lattice3])).
% 0.20/0.48  thf('10', plain,
% 0.20/0.48      (![X9 : $i]:
% 0.20/0.48         ((m1_subset_1 @ (u1_orders_2 @ X9) @ 
% 0.20/0.48           (k1_zfmisc_1 @ 
% 0.20/0.48            (k2_zfmisc_1 @ (u1_struct_0 @ X9) @ (u1_struct_0 @ X9))))
% 0.20/0.48          | ~ (l1_orders_2 @ X9))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_u1_orders_2])).
% 0.20/0.48  thf(free_g1_orders_2, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) =>
% 0.20/0.48       ( ![C:$i,D:$i]:
% 0.20/0.48         ( ( ( g1_orders_2 @ A @ B ) = ( g1_orders_2 @ C @ D ) ) =>
% 0.20/0.48           ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) ))).
% 0.20/0.48  thf('11', plain,
% 0.20/0.48      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.48         (((g1_orders_2 @ X12 @ X13) != (g1_orders_2 @ X10 @ X11))
% 0.20/0.48          | ((X12) = (X10))
% 0.20/0.48          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X12))))),
% 0.20/0.48      inference('cnf', [status(esa)], [free_g1_orders_2])).
% 0.20/0.48  thf('12', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.48         (~ (l1_orders_2 @ X0)
% 0.20/0.48          | ((u1_struct_0 @ X0) = (X1))
% 0.20/0.48          | ((g1_orders_2 @ (u1_struct_0 @ X0) @ (u1_orders_2 @ X0))
% 0.20/0.48              != (g1_orders_2 @ X1 @ X2)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.48  thf('13', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (((g1_orders_2 @ (u1_struct_0 @ X1) @ (u1_orders_2 @ X1))
% 0.20/0.48            != (k7_lattice3 @ X0))
% 0.20/0.48          | ~ (l1_orders_2 @ X0)
% 0.20/0.48          | ((u1_struct_0 @ X1) = (u1_struct_0 @ X0))
% 0.20/0.48          | ~ (l1_orders_2 @ X1))),
% 0.20/0.48      inference('sup-', [status(thm)], ['9', '12'])).
% 0.20/0.48  thf('14', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (((X0) != (k7_lattice3 @ X1))
% 0.20/0.48          | ~ (l1_orders_2 @ X0)
% 0.20/0.48          | ~ (v1_orders_2 @ X0)
% 0.20/0.48          | ~ (l1_orders_2 @ X0)
% 0.20/0.48          | ((u1_struct_0 @ X0) = (u1_struct_0 @ X1))
% 0.20/0.48          | ~ (l1_orders_2 @ X1))),
% 0.20/0.48      inference('sup-', [status(thm)], ['8', '13'])).
% 0.20/0.48  thf('15', plain,
% 0.20/0.48      (![X1 : $i]:
% 0.20/0.48         (~ (l1_orders_2 @ X1)
% 0.20/0.48          | ((u1_struct_0 @ (k7_lattice3 @ X1)) = (u1_struct_0 @ X1))
% 0.20/0.48          | ~ (v1_orders_2 @ (k7_lattice3 @ X1))
% 0.20/0.48          | ~ (l1_orders_2 @ (k7_lattice3 @ X1)))),
% 0.20/0.48      inference('simplify', [status(thm)], ['14'])).
% 0.20/0.48  thf('16', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (l1_orders_2 @ X0)
% 0.20/0.48          | ~ (l1_orders_2 @ (k7_lattice3 @ X0))
% 0.20/0.48          | ((u1_struct_0 @ (k7_lattice3 @ X0)) = (u1_struct_0 @ X0))
% 0.20/0.48          | ~ (l1_orders_2 @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['7', '15'])).
% 0.20/0.48  thf('17', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (((u1_struct_0 @ (k7_lattice3 @ X0)) = (u1_struct_0 @ X0))
% 0.20/0.48          | ~ (l1_orders_2 @ (k7_lattice3 @ X0))
% 0.20/0.48          | ~ (l1_orders_2 @ X0))),
% 0.20/0.48      inference('simplify', [status(thm)], ['16'])).
% 0.20/0.48  thf('18', plain,
% 0.20/0.48      (![X14 : $i]:
% 0.20/0.48         (((k7_lattice3 @ X14)
% 0.20/0.48            = (g1_orders_2 @ (u1_struct_0 @ X14) @ 
% 0.20/0.48               (k3_relset_1 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X14) @ 
% 0.20/0.48                (u1_orders_2 @ X14))))
% 0.20/0.48          | ~ (l1_orders_2 @ X14))),
% 0.20/0.48      inference('cnf', [status(esa)], [d5_lattice3])).
% 0.20/0.48  thf('19', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (l1_orders_2 @ X0)
% 0.20/0.48          | (m1_subset_1 @ 
% 0.20/0.48             (k3_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ 
% 0.20/0.48              (u1_orders_2 @ X0)) @ 
% 0.20/0.48             (k1_zfmisc_1 @ 
% 0.20/0.48              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0)))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.48  thf('20', plain,
% 0.20/0.48      (![X7 : $i, X8 : $i]:
% 0.20/0.48         ((l1_orders_2 @ (g1_orders_2 @ X7 @ X8))
% 0.20/0.48          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X7))))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_g1_orders_2])).
% 0.20/0.48  thf('21', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (l1_orders_2 @ X0)
% 0.20/0.48          | (l1_orders_2 @ 
% 0.20/0.48             (g1_orders_2 @ (u1_struct_0 @ X0) @ 
% 0.20/0.48              (k3_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ 
% 0.20/0.48               (u1_orders_2 @ X0)))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.48  thf('22', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((l1_orders_2 @ (k7_lattice3 @ X0))
% 0.20/0.48          | ~ (l1_orders_2 @ X0)
% 0.20/0.48          | ~ (l1_orders_2 @ X0))),
% 0.20/0.48      inference('sup+', [status(thm)], ['18', '21'])).
% 0.20/0.48  thf('23', plain,
% 0.20/0.48      (![X0 : $i]: (~ (l1_orders_2 @ X0) | (l1_orders_2 @ (k7_lattice3 @ X0)))),
% 0.20/0.48      inference('simplify', [status(thm)], ['22'])).
% 0.20/0.48  thf('24', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (l1_orders_2 @ X0)
% 0.20/0.48          | ((u1_struct_0 @ (k7_lattice3 @ X0)) = (u1_struct_0 @ X0)))),
% 0.20/0.48      inference('clc', [status(thm)], ['17', '23'])).
% 0.20/0.48  thf(t12_yellow_6, conjecture,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( l1_orders_2 @ A ) =>
% 0.20/0.48       ( ( u1_struct_0 @ A ) = ( u1_struct_0 @ ( k7_lattice3 @ A ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i]:
% 0.20/0.48        ( ( l1_orders_2 @ A ) =>
% 0.20/0.48          ( ( u1_struct_0 @ A ) = ( u1_struct_0 @ ( k7_lattice3 @ A ) ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t12_yellow_6])).
% 0.20/0.48  thf('25', plain,
% 0.20/0.48      (((u1_struct_0 @ sk_A) != (u1_struct_0 @ (k7_lattice3 @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('26', plain,
% 0.20/0.48      ((((u1_struct_0 @ sk_A) != (u1_struct_0 @ sk_A)) | ~ (l1_orders_2 @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.48  thf('27', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('28', plain, (((u1_struct_0 @ sk_A) != (u1_struct_0 @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['26', '27'])).
% 0.20/0.48  thf('29', plain, ($false), inference('simplify', [status(thm)], ['28'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
