%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8bCRIkZSZo

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:03 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   54 (  67 expanded)
%              Number of leaves         :   21 (  30 expanded)
%              Depth                    :   12
%              Number of atoms          :  355 ( 496 expanded)
%              Number of equality atoms :   47 (  64 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_2_type,type,(
    v1_relat_2: $i > $o )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(g1_orders_2_type,type,(
    g1_orders_2: $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v8_relat_2_type,type,(
    v8_relat_2: $i > $o )).

thf(v4_relat_2_type,type,(
    v4_relat_2: $i > $o )).

thf(v1_orders_2_type,type,(
    v1_orders_2: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_yellow_1_type,type,(
    k1_yellow_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(t1_yellow_1,conjecture,(
    ! [A: $i] :
      ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) )
        = ( k1_yellow_1 @ A ) )
      & ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) )
        = A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) )
          = ( k1_yellow_1 @ A ) )
        & ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) )
          = A ) ) ),
    inference('cnf.neg',[status(esa)],[t1_yellow_1])).

thf('0',plain,
    ( ( ( u1_orders_2 @ ( k2_yellow_1 @ sk_A ) )
     != ( k1_yellow_1 @ sk_A ) )
    | ( ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) )
     != sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) )
     != sk_A )
   <= ( ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) )
     != sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(abstractness_v1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v1_orders_2 @ A )
       => ( A
          = ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) ) ) ) ) )).

thf('2',plain,(
    ! [X0: $i] :
      ( ~ ( v1_orders_2 @ X0 )
      | ( X0
        = ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_orders_2])).

thf(dt_k1_yellow_1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k1_yellow_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k1_yellow_1 @ A ) @ A )
      & ( v8_relat_2 @ ( k1_yellow_1 @ A ) )
      & ( v4_relat_2 @ ( k1_yellow_1 @ A ) )
      & ( v1_relat_2 @ ( k1_yellow_1 @ A ) ) ) )).

thf('3',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ ( k1_yellow_1 @ X10 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_1])).

thf(free_g1_orders_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
     => ! [C: $i,D: $i] :
          ( ( ( g1_orders_2 @ A @ B )
            = ( g1_orders_2 @ C @ D ) )
         => ( ( A = C )
            & ( B = D ) ) ) ) )).

thf('4',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( ( g1_orders_2 @ X3 @ X4 )
       != ( g1_orders_2 @ X1 @ X2 ) )
      | ( X4 = X2 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_orders_2])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_yellow_1 @ X0 )
        = X1 )
      | ( ( g1_orders_2 @ X0 @ ( k1_yellow_1 @ X0 ) )
       != ( g1_orders_2 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(d1_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k2_yellow_1 @ A )
      = ( g1_orders_2 @ A @ ( k1_yellow_1 @ A ) ) ) )).

thf('6',plain,(
    ! [X5: $i] :
      ( ( k2_yellow_1 @ X5 )
      = ( g1_orders_2 @ X5 @ ( k1_yellow_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d1_yellow_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_yellow_1 @ X0 )
        = X1 )
      | ( ( k2_yellow_1 @ X0 )
       != ( g1_orders_2 @ X2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_yellow_1 @ X1 )
       != X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_orders_2 @ X0 )
      | ( ( k1_yellow_1 @ X1 )
        = ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf('9',plain,(
    ! [X1: $i] :
      ( ( ( k1_yellow_1 @ X1 )
        = ( u1_orders_2 @ ( k2_yellow_1 @ X1 ) ) )
      | ~ ( v1_orders_2 @ ( k2_yellow_1 @ X1 ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf(dt_k2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) )).

thf('10',plain,(
    ! [X12: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('11',plain,(
    ! [X11: $i] :
      ( v1_orders_2 @ ( k2_yellow_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('12',plain,(
    ! [X1: $i] :
      ( ( k1_yellow_1 @ X1 )
      = ( u1_orders_2 @ ( k2_yellow_1 @ X1 ) ) ) ),
    inference('simplify_reflect+',[status(thm)],['9','10','11'])).

thf('13',plain,
    ( ( ( u1_orders_2 @ ( k2_yellow_1 @ sk_A ) )
     != ( k1_yellow_1 @ sk_A ) )
   <= ( ( u1_orders_2 @ ( k2_yellow_1 @ sk_A ) )
     != ( k1_yellow_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('14',plain,
    ( ( ( k1_yellow_1 @ sk_A )
     != ( k1_yellow_1 @ sk_A ) )
   <= ( ( u1_orders_2 @ ( k2_yellow_1 @ sk_A ) )
     != ( k1_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( u1_orders_2 @ ( k2_yellow_1 @ sk_A ) )
    = ( k1_yellow_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,
    ( ( ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) )
     != sk_A )
    | ( ( u1_orders_2 @ ( k2_yellow_1 @ sk_A ) )
     != ( k1_yellow_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('17',plain,(
    ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) )
 != sk_A ),
    inference('sat_resolution*',[status(thm)],['15','16'])).

thf('18',plain,(
    ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) )
 != sk_A ),
    inference(simpl_trail,[status(thm)],['1','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_orders_2 @ X0 )
      | ( X0
        = ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_orders_2])).

thf('20',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ ( k1_yellow_1 @ X10 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_1])).

thf('21',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( ( g1_orders_2 @ X3 @ X4 )
       != ( g1_orders_2 @ X1 @ X2 ) )
      | ( X3 = X1 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_orders_2])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = X1 )
      | ( ( g1_orders_2 @ X0 @ ( k1_yellow_1 @ X0 ) )
       != ( g1_orders_2 @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X5: $i] :
      ( ( k2_yellow_1 @ X5 )
      = ( g1_orders_2 @ X5 @ ( k1_yellow_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d1_yellow_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = X1 )
      | ( ( k2_yellow_1 @ X0 )
       != ( g1_orders_2 @ X1 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_yellow_1 @ X1 )
       != X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_orders_2 @ X0 )
      | ( X1
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','24'])).

thf('26',plain,(
    ! [X1: $i] :
      ( ( X1
        = ( u1_struct_0 @ ( k2_yellow_1 @ X1 ) ) )
      | ~ ( v1_orders_2 @ ( k2_yellow_1 @ X1 ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X12: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('28',plain,(
    ! [X11: $i] :
      ( v1_orders_2 @ ( k2_yellow_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('29',plain,(
    ! [X1: $i] :
      ( X1
      = ( u1_struct_0 @ ( k2_yellow_1 @ X1 ) ) ) ),
    inference('simplify_reflect+',[status(thm)],['26','27','28'])).

thf('30',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['18','29'])).

thf('31',plain,(
    $false ),
    inference(simplify,[status(thm)],['30'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8bCRIkZSZo
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:16:45 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.20/0.34  % Running in FO mode
% 0.21/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.46  % Solved by: fo/fo7.sh
% 0.21/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.46  % done 22 iterations in 0.014s
% 0.21/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.46  % SZS output start Refutation
% 0.21/0.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.46  thf(v1_relat_2_type, type, v1_relat_2: $i > $o).
% 0.21/0.46  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.21/0.46  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.21/0.46  thf(g1_orders_2_type, type, g1_orders_2: $i > $i > $i).
% 0.21/0.46  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.21/0.46  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.46  thf(v8_relat_2_type, type, v8_relat_2: $i > $o).
% 0.21/0.46  thf(v4_relat_2_type, type, v4_relat_2: $i > $o).
% 0.21/0.46  thf(v1_orders_2_type, type, v1_orders_2: $i > $o).
% 0.21/0.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.46  thf(k1_yellow_1_type, type, k1_yellow_1: $i > $i).
% 0.21/0.46  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.46  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.21/0.46  thf(t1_yellow_1, conjecture,
% 0.21/0.46    (![A:$i]:
% 0.21/0.46     ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) ) = ( k1_yellow_1 @ A ) ) & 
% 0.21/0.46       ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) = ( A ) ) ))).
% 0.21/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.46    (~( ![A:$i]:
% 0.21/0.46        ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) ) = ( k1_yellow_1 @ A ) ) & 
% 0.21/0.46          ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) = ( A ) ) ) )),
% 0.21/0.46    inference('cnf.neg', [status(esa)], [t1_yellow_1])).
% 0.21/0.46  thf('0', plain,
% 0.21/0.46      ((((u1_orders_2 @ (k2_yellow_1 @ sk_A)) != (k1_yellow_1 @ sk_A))
% 0.21/0.46        | ((u1_struct_0 @ (k2_yellow_1 @ sk_A)) != (sk_A)))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('1', plain,
% 0.21/0.46      ((((u1_struct_0 @ (k2_yellow_1 @ sk_A)) != (sk_A)))
% 0.21/0.46         <= (~ (((u1_struct_0 @ (k2_yellow_1 @ sk_A)) = (sk_A))))),
% 0.21/0.46      inference('split', [status(esa)], ['0'])).
% 0.21/0.46  thf(abstractness_v1_orders_2, axiom,
% 0.21/0.46    (![A:$i]:
% 0.21/0.46     ( ( l1_orders_2 @ A ) =>
% 0.21/0.46       ( ( v1_orders_2 @ A ) =>
% 0.21/0.46         ( ( A ) = ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) ) ) ) ))).
% 0.21/0.46  thf('2', plain,
% 0.21/0.46      (![X0 : $i]:
% 0.21/0.46         (~ (v1_orders_2 @ X0)
% 0.21/0.46          | ((X0) = (g1_orders_2 @ (u1_struct_0 @ X0) @ (u1_orders_2 @ X0)))
% 0.21/0.46          | ~ (l1_orders_2 @ X0))),
% 0.21/0.46      inference('cnf', [status(esa)], [abstractness_v1_orders_2])).
% 0.21/0.46  thf(dt_k1_yellow_1, axiom,
% 0.21/0.46    (![A:$i]:
% 0.21/0.46     ( ( m1_subset_1 @
% 0.21/0.46         ( k1_yellow_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.21/0.46       ( v1_partfun1 @ ( k1_yellow_1 @ A ) @ A ) & 
% 0.21/0.46       ( v8_relat_2 @ ( k1_yellow_1 @ A ) ) & 
% 0.21/0.46       ( v4_relat_2 @ ( k1_yellow_1 @ A ) ) & 
% 0.21/0.46       ( v1_relat_2 @ ( k1_yellow_1 @ A ) ) ))).
% 0.21/0.46  thf('3', plain,
% 0.21/0.46      (![X10 : $i]:
% 0.21/0.46         (m1_subset_1 @ (k1_yellow_1 @ X10) @ 
% 0.21/0.46          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X10)))),
% 0.21/0.46      inference('cnf', [status(esa)], [dt_k1_yellow_1])).
% 0.21/0.46  thf(free_g1_orders_2, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) =>
% 0.21/0.46       ( ![C:$i,D:$i]:
% 0.21/0.46         ( ( ( g1_orders_2 @ A @ B ) = ( g1_orders_2 @ C @ D ) ) =>
% 0.21/0.46           ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) ))).
% 0.21/0.46  thf('4', plain,
% 0.21/0.46      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.46         (((g1_orders_2 @ X3 @ X4) != (g1_orders_2 @ X1 @ X2))
% 0.21/0.46          | ((X4) = (X2))
% 0.21/0.46          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X3))))),
% 0.21/0.46      inference('cnf', [status(esa)], [free_g1_orders_2])).
% 0.21/0.46  thf('5', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.46         (((k1_yellow_1 @ X0) = (X1))
% 0.21/0.46          | ((g1_orders_2 @ X0 @ (k1_yellow_1 @ X0)) != (g1_orders_2 @ X2 @ X1)))),
% 0.21/0.46      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.46  thf(d1_yellow_1, axiom,
% 0.21/0.46    (![A:$i]:
% 0.21/0.46     ( ( k2_yellow_1 @ A ) = ( g1_orders_2 @ A @ ( k1_yellow_1 @ A ) ) ))).
% 0.21/0.46  thf('6', plain,
% 0.21/0.46      (![X5 : $i]:
% 0.21/0.46         ((k2_yellow_1 @ X5) = (g1_orders_2 @ X5 @ (k1_yellow_1 @ X5)))),
% 0.21/0.46      inference('cnf', [status(esa)], [d1_yellow_1])).
% 0.21/0.46  thf('7', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.46         (((k1_yellow_1 @ X0) = (X1))
% 0.21/0.46          | ((k2_yellow_1 @ X0) != (g1_orders_2 @ X2 @ X1)))),
% 0.21/0.46      inference('demod', [status(thm)], ['5', '6'])).
% 0.21/0.46  thf('8', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i]:
% 0.21/0.46         (((k2_yellow_1 @ X1) != (X0))
% 0.21/0.46          | ~ (l1_orders_2 @ X0)
% 0.21/0.46          | ~ (v1_orders_2 @ X0)
% 0.21/0.46          | ((k1_yellow_1 @ X1) = (u1_orders_2 @ X0)))),
% 0.21/0.46      inference('sup-', [status(thm)], ['2', '7'])).
% 0.21/0.46  thf('9', plain,
% 0.21/0.46      (![X1 : $i]:
% 0.21/0.46         (((k1_yellow_1 @ X1) = (u1_orders_2 @ (k2_yellow_1 @ X1)))
% 0.21/0.46          | ~ (v1_orders_2 @ (k2_yellow_1 @ X1))
% 0.21/0.46          | ~ (l1_orders_2 @ (k2_yellow_1 @ X1)))),
% 0.21/0.46      inference('simplify', [status(thm)], ['8'])).
% 0.21/0.46  thf(dt_k2_yellow_1, axiom,
% 0.21/0.46    (![A:$i]:
% 0.21/0.46     ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.21/0.46       ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ))).
% 0.21/0.46  thf('10', plain, (![X12 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X12))),
% 0.21/0.46      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.21/0.46  thf('11', plain, (![X11 : $i]: (v1_orders_2 @ (k2_yellow_1 @ X11))),
% 0.21/0.46      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.21/0.46  thf('12', plain,
% 0.21/0.46      (![X1 : $i]: ((k1_yellow_1 @ X1) = (u1_orders_2 @ (k2_yellow_1 @ X1)))),
% 0.21/0.46      inference('simplify_reflect+', [status(thm)], ['9', '10', '11'])).
% 0.21/0.46  thf('13', plain,
% 0.21/0.46      ((((u1_orders_2 @ (k2_yellow_1 @ sk_A)) != (k1_yellow_1 @ sk_A)))
% 0.21/0.46         <= (~ (((u1_orders_2 @ (k2_yellow_1 @ sk_A)) = (k1_yellow_1 @ sk_A))))),
% 0.21/0.46      inference('split', [status(esa)], ['0'])).
% 0.21/0.46  thf('14', plain,
% 0.21/0.46      ((((k1_yellow_1 @ sk_A) != (k1_yellow_1 @ sk_A)))
% 0.21/0.46         <= (~ (((u1_orders_2 @ (k2_yellow_1 @ sk_A)) = (k1_yellow_1 @ sk_A))))),
% 0.21/0.46      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.46  thf('15', plain,
% 0.21/0.46      ((((u1_orders_2 @ (k2_yellow_1 @ sk_A)) = (k1_yellow_1 @ sk_A)))),
% 0.21/0.46      inference('simplify', [status(thm)], ['14'])).
% 0.21/0.46  thf('16', plain,
% 0.21/0.46      (~ (((u1_struct_0 @ (k2_yellow_1 @ sk_A)) = (sk_A))) | 
% 0.21/0.46       ~ (((u1_orders_2 @ (k2_yellow_1 @ sk_A)) = (k1_yellow_1 @ sk_A)))),
% 0.21/0.46      inference('split', [status(esa)], ['0'])).
% 0.21/0.46  thf('17', plain, (~ (((u1_struct_0 @ (k2_yellow_1 @ sk_A)) = (sk_A)))),
% 0.21/0.46      inference('sat_resolution*', [status(thm)], ['15', '16'])).
% 0.21/0.46  thf('18', plain, (((u1_struct_0 @ (k2_yellow_1 @ sk_A)) != (sk_A))),
% 0.21/0.46      inference('simpl_trail', [status(thm)], ['1', '17'])).
% 0.21/0.46  thf('19', plain,
% 0.21/0.46      (![X0 : $i]:
% 0.21/0.46         (~ (v1_orders_2 @ X0)
% 0.21/0.46          | ((X0) = (g1_orders_2 @ (u1_struct_0 @ X0) @ (u1_orders_2 @ X0)))
% 0.21/0.46          | ~ (l1_orders_2 @ X0))),
% 0.21/0.46      inference('cnf', [status(esa)], [abstractness_v1_orders_2])).
% 0.21/0.46  thf('20', plain,
% 0.21/0.46      (![X10 : $i]:
% 0.21/0.46         (m1_subset_1 @ (k1_yellow_1 @ X10) @ 
% 0.21/0.46          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X10)))),
% 0.21/0.46      inference('cnf', [status(esa)], [dt_k1_yellow_1])).
% 0.21/0.46  thf('21', plain,
% 0.21/0.46      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.46         (((g1_orders_2 @ X3 @ X4) != (g1_orders_2 @ X1 @ X2))
% 0.21/0.46          | ((X3) = (X1))
% 0.21/0.46          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X3))))),
% 0.21/0.46      inference('cnf', [status(esa)], [free_g1_orders_2])).
% 0.21/0.46  thf('22', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.46         (((X0) = (X1))
% 0.21/0.46          | ((g1_orders_2 @ X0 @ (k1_yellow_1 @ X0)) != (g1_orders_2 @ X1 @ X2)))),
% 0.21/0.46      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.46  thf('23', plain,
% 0.21/0.46      (![X5 : $i]:
% 0.21/0.46         ((k2_yellow_1 @ X5) = (g1_orders_2 @ X5 @ (k1_yellow_1 @ X5)))),
% 0.21/0.46      inference('cnf', [status(esa)], [d1_yellow_1])).
% 0.21/0.46  thf('24', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.46         (((X0) = (X1)) | ((k2_yellow_1 @ X0) != (g1_orders_2 @ X1 @ X2)))),
% 0.21/0.46      inference('demod', [status(thm)], ['22', '23'])).
% 0.21/0.46  thf('25', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i]:
% 0.21/0.46         (((k2_yellow_1 @ X1) != (X0))
% 0.21/0.46          | ~ (l1_orders_2 @ X0)
% 0.21/0.46          | ~ (v1_orders_2 @ X0)
% 0.21/0.46          | ((X1) = (u1_struct_0 @ X0)))),
% 0.21/0.46      inference('sup-', [status(thm)], ['19', '24'])).
% 0.21/0.46  thf('26', plain,
% 0.21/0.46      (![X1 : $i]:
% 0.21/0.46         (((X1) = (u1_struct_0 @ (k2_yellow_1 @ X1)))
% 0.21/0.46          | ~ (v1_orders_2 @ (k2_yellow_1 @ X1))
% 0.21/0.46          | ~ (l1_orders_2 @ (k2_yellow_1 @ X1)))),
% 0.21/0.46      inference('simplify', [status(thm)], ['25'])).
% 0.21/0.46  thf('27', plain, (![X12 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X12))),
% 0.21/0.46      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.21/0.46  thf('28', plain, (![X11 : $i]: (v1_orders_2 @ (k2_yellow_1 @ X11))),
% 0.21/0.46      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.21/0.46  thf('29', plain, (![X1 : $i]: ((X1) = (u1_struct_0 @ (k2_yellow_1 @ X1)))),
% 0.21/0.46      inference('simplify_reflect+', [status(thm)], ['26', '27', '28'])).
% 0.21/0.46  thf('30', plain, (((sk_A) != (sk_A))),
% 0.21/0.46      inference('demod', [status(thm)], ['18', '29'])).
% 0.21/0.46  thf('31', plain, ($false), inference('simplify', [status(thm)], ['30'])).
% 0.21/0.46  
% 0.21/0.46  % SZS output end Refutation
% 0.21/0.46  
% 0.21/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
