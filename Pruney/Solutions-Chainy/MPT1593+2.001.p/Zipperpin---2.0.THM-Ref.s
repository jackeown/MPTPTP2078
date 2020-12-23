%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.add7EuutrO

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:03 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   62 (  91 expanded)
%              Number of leaves         :   21 (  38 expanded)
%              Depth                    :   12
%              Number of atoms          :  421 ( 752 expanded)
%              Number of equality atoms :   49 (  72 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v4_relat_2_type,type,(
    v4_relat_2: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(k1_yellow_1_type,type,(
    k1_yellow_1: $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(g1_orders_2_type,type,(
    g1_orders_2: $i > $i > $i )).

thf(v8_relat_2_type,type,(
    v8_relat_2: $i > $o )).

thf(v1_relat_2_type,type,(
    v1_relat_2: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_orders_2_type,type,(
    v1_orders_2: $i > $o )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

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
    ! [X12: $i] :
      ( m1_subset_1 @ ( k1_yellow_1 @ X12 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X12 ) ) ) ),
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
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( ( g1_orders_2 @ X5 @ X6 )
       != ( g1_orders_2 @ X3 @ X4 ) )
      | ( X6 = X4 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X5 ) ) ) ) ),
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
    ! [X7: $i] :
      ( ( k2_yellow_1 @ X7 )
      = ( g1_orders_2 @ X7 @ ( k1_yellow_1 @ X7 ) ) ) ),
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

thf('10',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ ( k1_yellow_1 @ X12 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_1])).

thf(dt_g1_orders_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
     => ( ( v1_orders_2 @ ( g1_orders_2 @ A @ B ) )
        & ( l1_orders_2 @ ( g1_orders_2 @ A @ B ) ) ) ) )).

thf('11',plain,(
    ! [X1: $i,X2: $i] :
      ( ( l1_orders_2 @ ( g1_orders_2 @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X1 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_g1_orders_2])).

thf('12',plain,(
    ! [X0: $i] :
      ( l1_orders_2 @ ( g1_orders_2 @ X0 @ ( k1_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X7: $i] :
      ( ( k2_yellow_1 @ X7 )
      = ( g1_orders_2 @ X7 @ ( k1_yellow_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d1_yellow_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ ( k1_yellow_1 @ X12 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_1])).

thf('16',plain,(
    ! [X1: $i,X2: $i] :
      ( ( v1_orders_2 @ ( g1_orders_2 @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X1 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_g1_orders_2])).

thf('17',plain,(
    ! [X0: $i] :
      ( v1_orders_2 @ ( g1_orders_2 @ X0 @ ( k1_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X7: $i] :
      ( ( k2_yellow_1 @ X7 )
      = ( g1_orders_2 @ X7 @ ( k1_yellow_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d1_yellow_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( v1_orders_2 @ ( k2_yellow_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X1: $i] :
      ( ( k1_yellow_1 @ X1 )
      = ( u1_orders_2 @ ( k2_yellow_1 @ X1 ) ) ) ),
    inference('simplify_reflect+',[status(thm)],['9','14','19'])).

thf('21',plain,
    ( ( ( u1_orders_2 @ ( k2_yellow_1 @ sk_A ) )
     != ( k1_yellow_1 @ sk_A ) )
   <= ( ( u1_orders_2 @ ( k2_yellow_1 @ sk_A ) )
     != ( k1_yellow_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('22',plain,
    ( ( ( k1_yellow_1 @ sk_A )
     != ( k1_yellow_1 @ sk_A ) )
   <= ( ( u1_orders_2 @ ( k2_yellow_1 @ sk_A ) )
     != ( k1_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( u1_orders_2 @ ( k2_yellow_1 @ sk_A ) )
    = ( k1_yellow_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ( ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) )
     != sk_A )
    | ( ( u1_orders_2 @ ( k2_yellow_1 @ sk_A ) )
     != ( k1_yellow_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('25',plain,(
    ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) )
 != sk_A ),
    inference('sat_resolution*',[status(thm)],['23','24'])).

thf('26',plain,(
    ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) )
 != sk_A ),
    inference(simpl_trail,[status(thm)],['1','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_orders_2 @ X0 )
      | ( X0
        = ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_orders_2])).

thf('28',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ ( k1_yellow_1 @ X12 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_1])).

thf('29',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( ( g1_orders_2 @ X5 @ X6 )
       != ( g1_orders_2 @ X3 @ X4 ) )
      | ( X5 = X3 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_orders_2])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = X1 )
      | ( ( g1_orders_2 @ X0 @ ( k1_yellow_1 @ X0 ) )
       != ( g1_orders_2 @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X7: $i] :
      ( ( k2_yellow_1 @ X7 )
      = ( g1_orders_2 @ X7 @ ( k1_yellow_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d1_yellow_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = X1 )
      | ( ( k2_yellow_1 @ X0 )
       != ( g1_orders_2 @ X1 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_yellow_1 @ X1 )
       != X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_orders_2 @ X0 )
      | ( X1
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['27','32'])).

thf('34',plain,(
    ! [X1: $i] :
      ( ( X1
        = ( u1_struct_0 @ ( k2_yellow_1 @ X1 ) ) )
      | ~ ( v1_orders_2 @ ( k2_yellow_1 @ X1 ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('36',plain,(
    ! [X0: $i] :
      ( v1_orders_2 @ ( k2_yellow_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('37',plain,(
    ! [X1: $i] :
      ( X1
      = ( u1_struct_0 @ ( k2_yellow_1 @ X1 ) ) ) ),
    inference('simplify_reflect+',[status(thm)],['34','35','36'])).

thf('38',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['26','37'])).

thf('39',plain,(
    $false ),
    inference(simplify,[status(thm)],['38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.add7EuutrO
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 20:04:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.45  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.45  % Solved by: fo/fo7.sh
% 0.20/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.45  % done 24 iterations in 0.008s
% 0.20/0.45  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.45  % SZS output start Refutation
% 0.20/0.45  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.45  thf(v4_relat_2_type, type, v4_relat_2: $i > $o).
% 0.20/0.45  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.20/0.45  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.20/0.45  thf(k1_yellow_1_type, type, k1_yellow_1: $i > $i).
% 0.20/0.45  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.20/0.45  thf(g1_orders_2_type, type, g1_orders_2: $i > $i > $i).
% 0.20/0.45  thf(v8_relat_2_type, type, v8_relat_2: $i > $o).
% 0.20/0.45  thf(v1_relat_2_type, type, v1_relat_2: $i > $o).
% 0.20/0.45  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.45  thf(v1_orders_2_type, type, v1_orders_2: $i > $o).
% 0.20/0.45  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.20/0.45  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.45  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.45  thf(t1_yellow_1, conjecture,
% 0.20/0.45    (![A:$i]:
% 0.20/0.45     ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) ) = ( k1_yellow_1 @ A ) ) & 
% 0.20/0.45       ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) = ( A ) ) ))).
% 0.20/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.45    (~( ![A:$i]:
% 0.20/0.45        ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) ) = ( k1_yellow_1 @ A ) ) & 
% 0.20/0.45          ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) = ( A ) ) ) )),
% 0.20/0.45    inference('cnf.neg', [status(esa)], [t1_yellow_1])).
% 0.20/0.45  thf('0', plain,
% 0.20/0.45      ((((u1_orders_2 @ (k2_yellow_1 @ sk_A)) != (k1_yellow_1 @ sk_A))
% 0.20/0.45        | ((u1_struct_0 @ (k2_yellow_1 @ sk_A)) != (sk_A)))),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('1', plain,
% 0.20/0.45      ((((u1_struct_0 @ (k2_yellow_1 @ sk_A)) != (sk_A)))
% 0.20/0.45         <= (~ (((u1_struct_0 @ (k2_yellow_1 @ sk_A)) = (sk_A))))),
% 0.20/0.45      inference('split', [status(esa)], ['0'])).
% 0.20/0.45  thf(abstractness_v1_orders_2, axiom,
% 0.20/0.45    (![A:$i]:
% 0.20/0.45     ( ( l1_orders_2 @ A ) =>
% 0.20/0.45       ( ( v1_orders_2 @ A ) =>
% 0.20/0.45         ( ( A ) = ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) ) ) ) ))).
% 0.20/0.45  thf('2', plain,
% 0.20/0.45      (![X0 : $i]:
% 0.20/0.45         (~ (v1_orders_2 @ X0)
% 0.20/0.45          | ((X0) = (g1_orders_2 @ (u1_struct_0 @ X0) @ (u1_orders_2 @ X0)))
% 0.20/0.45          | ~ (l1_orders_2 @ X0))),
% 0.20/0.45      inference('cnf', [status(esa)], [abstractness_v1_orders_2])).
% 0.20/0.45  thf(dt_k1_yellow_1, axiom,
% 0.20/0.45    (![A:$i]:
% 0.20/0.45     ( ( m1_subset_1 @
% 0.20/0.45         ( k1_yellow_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.20/0.45       ( v1_partfun1 @ ( k1_yellow_1 @ A ) @ A ) & 
% 0.20/0.45       ( v8_relat_2 @ ( k1_yellow_1 @ A ) ) & 
% 0.20/0.45       ( v4_relat_2 @ ( k1_yellow_1 @ A ) ) & 
% 0.20/0.45       ( v1_relat_2 @ ( k1_yellow_1 @ A ) ) ))).
% 0.20/0.45  thf('3', plain,
% 0.20/0.45      (![X12 : $i]:
% 0.20/0.45         (m1_subset_1 @ (k1_yellow_1 @ X12) @ 
% 0.20/0.45          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X12)))),
% 0.20/0.45      inference('cnf', [status(esa)], [dt_k1_yellow_1])).
% 0.20/0.45  thf(free_g1_orders_2, axiom,
% 0.20/0.45    (![A:$i,B:$i]:
% 0.20/0.45     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) =>
% 0.20/0.45       ( ![C:$i,D:$i]:
% 0.20/0.45         ( ( ( g1_orders_2 @ A @ B ) = ( g1_orders_2 @ C @ D ) ) =>
% 0.20/0.45           ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) ))).
% 0.20/0.45  thf('4', plain,
% 0.20/0.45      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.45         (((g1_orders_2 @ X5 @ X6) != (g1_orders_2 @ X3 @ X4))
% 0.20/0.45          | ((X6) = (X4))
% 0.20/0.45          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X5))))),
% 0.20/0.45      inference('cnf', [status(esa)], [free_g1_orders_2])).
% 0.20/0.45  thf('5', plain,
% 0.20/0.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.45         (((k1_yellow_1 @ X0) = (X1))
% 0.20/0.45          | ((g1_orders_2 @ X0 @ (k1_yellow_1 @ X0)) != (g1_orders_2 @ X2 @ X1)))),
% 0.20/0.45      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.45  thf(d1_yellow_1, axiom,
% 0.20/0.45    (![A:$i]:
% 0.20/0.45     ( ( k2_yellow_1 @ A ) = ( g1_orders_2 @ A @ ( k1_yellow_1 @ A ) ) ))).
% 0.20/0.45  thf('6', plain,
% 0.20/0.45      (![X7 : $i]:
% 0.20/0.45         ((k2_yellow_1 @ X7) = (g1_orders_2 @ X7 @ (k1_yellow_1 @ X7)))),
% 0.20/0.45      inference('cnf', [status(esa)], [d1_yellow_1])).
% 0.20/0.45  thf('7', plain,
% 0.20/0.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.45         (((k1_yellow_1 @ X0) = (X1))
% 0.20/0.45          | ((k2_yellow_1 @ X0) != (g1_orders_2 @ X2 @ X1)))),
% 0.20/0.45      inference('demod', [status(thm)], ['5', '6'])).
% 0.20/0.45  thf('8', plain,
% 0.20/0.45      (![X0 : $i, X1 : $i]:
% 0.20/0.45         (((k2_yellow_1 @ X1) != (X0))
% 0.20/0.45          | ~ (l1_orders_2 @ X0)
% 0.20/0.45          | ~ (v1_orders_2 @ X0)
% 0.20/0.45          | ((k1_yellow_1 @ X1) = (u1_orders_2 @ X0)))),
% 0.20/0.45      inference('sup-', [status(thm)], ['2', '7'])).
% 0.20/0.45  thf('9', plain,
% 0.20/0.45      (![X1 : $i]:
% 0.20/0.45         (((k1_yellow_1 @ X1) = (u1_orders_2 @ (k2_yellow_1 @ X1)))
% 0.20/0.45          | ~ (v1_orders_2 @ (k2_yellow_1 @ X1))
% 0.20/0.45          | ~ (l1_orders_2 @ (k2_yellow_1 @ X1)))),
% 0.20/0.45      inference('simplify', [status(thm)], ['8'])).
% 0.20/0.45  thf('10', plain,
% 0.20/0.45      (![X12 : $i]:
% 0.20/0.45         (m1_subset_1 @ (k1_yellow_1 @ X12) @ 
% 0.20/0.45          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X12)))),
% 0.20/0.45      inference('cnf', [status(esa)], [dt_k1_yellow_1])).
% 0.20/0.45  thf(dt_g1_orders_2, axiom,
% 0.20/0.45    (![A:$i,B:$i]:
% 0.20/0.45     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) =>
% 0.20/0.45       ( ( v1_orders_2 @ ( g1_orders_2 @ A @ B ) ) & 
% 0.20/0.45         ( l1_orders_2 @ ( g1_orders_2 @ A @ B ) ) ) ))).
% 0.20/0.45  thf('11', plain,
% 0.20/0.45      (![X1 : $i, X2 : $i]:
% 0.20/0.45         ((l1_orders_2 @ (g1_orders_2 @ X1 @ X2))
% 0.20/0.45          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X1))))),
% 0.20/0.45      inference('cnf', [status(esa)], [dt_g1_orders_2])).
% 0.20/0.45  thf('12', plain,
% 0.20/0.45      (![X0 : $i]: (l1_orders_2 @ (g1_orders_2 @ X0 @ (k1_yellow_1 @ X0)))),
% 0.20/0.45      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.45  thf('13', plain,
% 0.20/0.45      (![X7 : $i]:
% 0.20/0.45         ((k2_yellow_1 @ X7) = (g1_orders_2 @ X7 @ (k1_yellow_1 @ X7)))),
% 0.20/0.45      inference('cnf', [status(esa)], [d1_yellow_1])).
% 0.20/0.45  thf('14', plain, (![X0 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X0))),
% 0.20/0.45      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.45  thf('15', plain,
% 0.20/0.45      (![X12 : $i]:
% 0.20/0.45         (m1_subset_1 @ (k1_yellow_1 @ X12) @ 
% 0.20/0.45          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X12)))),
% 0.20/0.45      inference('cnf', [status(esa)], [dt_k1_yellow_1])).
% 0.20/0.45  thf('16', plain,
% 0.20/0.45      (![X1 : $i, X2 : $i]:
% 0.20/0.45         ((v1_orders_2 @ (g1_orders_2 @ X1 @ X2))
% 0.20/0.45          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X1))))),
% 0.20/0.45      inference('cnf', [status(esa)], [dt_g1_orders_2])).
% 0.20/0.45  thf('17', plain,
% 0.20/0.45      (![X0 : $i]: (v1_orders_2 @ (g1_orders_2 @ X0 @ (k1_yellow_1 @ X0)))),
% 0.20/0.45      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.45  thf('18', plain,
% 0.20/0.45      (![X7 : $i]:
% 0.20/0.45         ((k2_yellow_1 @ X7) = (g1_orders_2 @ X7 @ (k1_yellow_1 @ X7)))),
% 0.20/0.45      inference('cnf', [status(esa)], [d1_yellow_1])).
% 0.20/0.45  thf('19', plain, (![X0 : $i]: (v1_orders_2 @ (k2_yellow_1 @ X0))),
% 0.20/0.45      inference('demod', [status(thm)], ['17', '18'])).
% 0.20/0.45  thf('20', plain,
% 0.20/0.45      (![X1 : $i]: ((k1_yellow_1 @ X1) = (u1_orders_2 @ (k2_yellow_1 @ X1)))),
% 0.20/0.45      inference('simplify_reflect+', [status(thm)], ['9', '14', '19'])).
% 0.20/0.45  thf('21', plain,
% 0.20/0.45      ((((u1_orders_2 @ (k2_yellow_1 @ sk_A)) != (k1_yellow_1 @ sk_A)))
% 0.20/0.45         <= (~ (((u1_orders_2 @ (k2_yellow_1 @ sk_A)) = (k1_yellow_1 @ sk_A))))),
% 0.20/0.45      inference('split', [status(esa)], ['0'])).
% 0.20/0.45  thf('22', plain,
% 0.20/0.45      ((((k1_yellow_1 @ sk_A) != (k1_yellow_1 @ sk_A)))
% 0.20/0.45         <= (~ (((u1_orders_2 @ (k2_yellow_1 @ sk_A)) = (k1_yellow_1 @ sk_A))))),
% 0.20/0.45      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.45  thf('23', plain,
% 0.20/0.45      ((((u1_orders_2 @ (k2_yellow_1 @ sk_A)) = (k1_yellow_1 @ sk_A)))),
% 0.20/0.45      inference('simplify', [status(thm)], ['22'])).
% 0.20/0.45  thf('24', plain,
% 0.20/0.45      (~ (((u1_struct_0 @ (k2_yellow_1 @ sk_A)) = (sk_A))) | 
% 0.20/0.45       ~ (((u1_orders_2 @ (k2_yellow_1 @ sk_A)) = (k1_yellow_1 @ sk_A)))),
% 0.20/0.45      inference('split', [status(esa)], ['0'])).
% 0.20/0.45  thf('25', plain, (~ (((u1_struct_0 @ (k2_yellow_1 @ sk_A)) = (sk_A)))),
% 0.20/0.45      inference('sat_resolution*', [status(thm)], ['23', '24'])).
% 0.20/0.45  thf('26', plain, (((u1_struct_0 @ (k2_yellow_1 @ sk_A)) != (sk_A))),
% 0.20/0.45      inference('simpl_trail', [status(thm)], ['1', '25'])).
% 0.20/0.45  thf('27', plain,
% 0.20/0.45      (![X0 : $i]:
% 0.20/0.45         (~ (v1_orders_2 @ X0)
% 0.20/0.45          | ((X0) = (g1_orders_2 @ (u1_struct_0 @ X0) @ (u1_orders_2 @ X0)))
% 0.20/0.45          | ~ (l1_orders_2 @ X0))),
% 0.20/0.45      inference('cnf', [status(esa)], [abstractness_v1_orders_2])).
% 0.20/0.45  thf('28', plain,
% 0.20/0.45      (![X12 : $i]:
% 0.20/0.45         (m1_subset_1 @ (k1_yellow_1 @ X12) @ 
% 0.20/0.45          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X12)))),
% 0.20/0.45      inference('cnf', [status(esa)], [dt_k1_yellow_1])).
% 0.20/0.45  thf('29', plain,
% 0.20/0.45      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.45         (((g1_orders_2 @ X5 @ X6) != (g1_orders_2 @ X3 @ X4))
% 0.20/0.45          | ((X5) = (X3))
% 0.20/0.45          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X5))))),
% 0.20/0.45      inference('cnf', [status(esa)], [free_g1_orders_2])).
% 0.20/0.45  thf('30', plain,
% 0.20/0.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.45         (((X0) = (X1))
% 0.20/0.45          | ((g1_orders_2 @ X0 @ (k1_yellow_1 @ X0)) != (g1_orders_2 @ X1 @ X2)))),
% 0.20/0.45      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.45  thf('31', plain,
% 0.20/0.45      (![X7 : $i]:
% 0.20/0.45         ((k2_yellow_1 @ X7) = (g1_orders_2 @ X7 @ (k1_yellow_1 @ X7)))),
% 0.20/0.45      inference('cnf', [status(esa)], [d1_yellow_1])).
% 0.20/0.45  thf('32', plain,
% 0.20/0.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.45         (((X0) = (X1)) | ((k2_yellow_1 @ X0) != (g1_orders_2 @ X1 @ X2)))),
% 0.20/0.45      inference('demod', [status(thm)], ['30', '31'])).
% 0.20/0.45  thf('33', plain,
% 0.20/0.45      (![X0 : $i, X1 : $i]:
% 0.20/0.45         (((k2_yellow_1 @ X1) != (X0))
% 0.20/0.45          | ~ (l1_orders_2 @ X0)
% 0.20/0.45          | ~ (v1_orders_2 @ X0)
% 0.20/0.45          | ((X1) = (u1_struct_0 @ X0)))),
% 0.20/0.45      inference('sup-', [status(thm)], ['27', '32'])).
% 0.20/0.45  thf('34', plain,
% 0.20/0.45      (![X1 : $i]:
% 0.20/0.45         (((X1) = (u1_struct_0 @ (k2_yellow_1 @ X1)))
% 0.20/0.45          | ~ (v1_orders_2 @ (k2_yellow_1 @ X1))
% 0.20/0.45          | ~ (l1_orders_2 @ (k2_yellow_1 @ X1)))),
% 0.20/0.45      inference('simplify', [status(thm)], ['33'])).
% 0.20/0.45  thf('35', plain, (![X0 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X0))),
% 0.20/0.45      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.45  thf('36', plain, (![X0 : $i]: (v1_orders_2 @ (k2_yellow_1 @ X0))),
% 0.20/0.45      inference('demod', [status(thm)], ['17', '18'])).
% 0.20/0.45  thf('37', plain, (![X1 : $i]: ((X1) = (u1_struct_0 @ (k2_yellow_1 @ X1)))),
% 0.20/0.45      inference('simplify_reflect+', [status(thm)], ['34', '35', '36'])).
% 0.20/0.45  thf('38', plain, (((sk_A) != (sk_A))),
% 0.20/0.45      inference('demod', [status(thm)], ['26', '37'])).
% 0.20/0.45  thf('39', plain, ($false), inference('simplify', [status(thm)], ['38'])).
% 0.20/0.45  
% 0.20/0.45  % SZS output end Refutation
% 0.20/0.45  
% 0.20/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
