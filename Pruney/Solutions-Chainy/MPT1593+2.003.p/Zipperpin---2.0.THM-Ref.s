%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QCBGY5q1cS

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:03 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 113 expanded)
%              Number of leaves         :   17 (  45 expanded)
%              Depth                    :   13
%              Number of atoms          :  431 ( 981 expanded)
%              Number of equality atoms :   53 ( 110 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

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

thf(k1_yellow_1_type,type,(
    k1_yellow_1: $i > $i )).

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

thf(d1_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k2_yellow_1 @ A )
      = ( g1_orders_2 @ A @ ( k1_yellow_1 @ A ) ) ) )).

thf('2',plain,(
    ! [X6: $i] :
      ( ( k2_yellow_1 @ X6 )
      = ( g1_orders_2 @ X6 @ ( k1_yellow_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d1_yellow_1])).

thf(abstractness_v1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v1_orders_2 @ A )
       => ( A
          = ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) ) ) ) ) )).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( v1_orders_2 @ X0 )
      | ( X0
        = ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_orders_2])).

thf(dt_u1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( u1_orders_2 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('4',plain,(
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

thf('5',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( ( g1_orders_2 @ X4 @ X5 )
       != ( g1_orders_2 @ X2 @ X3 ) )
      | ( X5 = X3 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_orders_2])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( u1_orders_2 @ X0 )
        = X1 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) )
       != ( g1_orders_2 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( g1_orders_2 @ X2 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_orders_2 @ X0 )
      | ( ( u1_orders_2 @ X0 )
        = X1 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( u1_orders_2 @ ( g1_orders_2 @ X2 @ X1 ) )
        = X1 )
      | ~ ( v1_orders_2 @ ( g1_orders_2 @ X2 @ X1 ) )
      | ~ ( l1_orders_2 @ ( g1_orders_2 @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( l1_orders_2 @ ( g1_orders_2 @ X0 @ ( k1_yellow_1 @ X0 ) ) )
      | ( ( u1_orders_2 @ ( g1_orders_2 @ X0 @ ( k1_yellow_1 @ X0 ) ) )
        = ( k1_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','8'])).

thf(dt_k2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) )).

thf('10',plain,(
    ! [X7: $i] :
      ( v1_orders_2 @ ( k2_yellow_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('11',plain,(
    ! [X6: $i] :
      ( ( k2_yellow_1 @ X6 )
      = ( g1_orders_2 @ X6 @ ( k1_yellow_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d1_yellow_1])).

thf('12',plain,(
    ! [X8: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('13',plain,(
    ! [X6: $i] :
      ( ( k2_yellow_1 @ X6 )
      = ( g1_orders_2 @ X6 @ ( k1_yellow_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d1_yellow_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( u1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      = ( k1_yellow_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10','11','12','13'])).

thf('15',plain,
    ( ( ( u1_orders_2 @ ( k2_yellow_1 @ sk_A ) )
     != ( k1_yellow_1 @ sk_A ) )
   <= ( ( u1_orders_2 @ ( k2_yellow_1 @ sk_A ) )
     != ( k1_yellow_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('16',plain,
    ( ( ( k1_yellow_1 @ sk_A )
     != ( k1_yellow_1 @ sk_A ) )
   <= ( ( u1_orders_2 @ ( k2_yellow_1 @ sk_A ) )
     != ( k1_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( u1_orders_2 @ ( k2_yellow_1 @ sk_A ) )
    = ( k1_yellow_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,
    ( ( ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) )
     != sk_A )
    | ( ( u1_orders_2 @ ( k2_yellow_1 @ sk_A ) )
     != ( k1_yellow_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('19',plain,(
    ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) )
 != sk_A ),
    inference('sat_resolution*',[status(thm)],['17','18'])).

thf('20',plain,(
    ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) )
 != sk_A ),
    inference(simpl_trail,[status(thm)],['1','19'])).

thf('21',plain,(
    ! [X6: $i] :
      ( ( k2_yellow_1 @ X6 )
      = ( g1_orders_2 @ X6 @ ( k1_yellow_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d1_yellow_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( u1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      = ( k1_yellow_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10','11','12','13'])).

thf('23',plain,(
    ! [X1: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X1 ) ) ) )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_orders_2])).

thf('24',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( ( g1_orders_2 @ X4 @ X5 )
       != ( g1_orders_2 @ X2 @ X3 ) )
      | ( X4 = X2 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_orders_2])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = X1 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) )
       != ( g1_orders_2 @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) @ ( k1_yellow_1 @ X0 ) )
       != ( g1_orders_2 @ X2 @ X1 ) )
      | ( ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) )
        = X2 )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( u1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      = ( k1_yellow_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10','11','12','13'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v1_orders_2 @ X0 )
      | ( X0
        = ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_orders_2])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( ( k2_yellow_1 @ X0 )
        = ( g1_orders_2 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) @ ( k1_yellow_1 @ X0 ) ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v1_orders_2 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X8: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('31',plain,(
    ! [X7: $i] :
      ( v1_orders_2 @ ( k2_yellow_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k2_yellow_1 @ X0 )
      = ( g1_orders_2 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) @ ( k1_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,(
    ! [X8: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_yellow_1 @ X0 )
       != ( g1_orders_2 @ X2 @ X1 ) )
      | ( ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) )
        = X2 ) ) ),
    inference(demod,[status(thm)],['26','32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_yellow_1 @ X1 )
       != ( k2_yellow_1 @ X0 ) )
      | ( ( u1_struct_0 @ ( k2_yellow_1 @ X1 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['21','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) )
      = X0 ) ),
    inference(eq_res,[status(thm)],['35'])).

thf('37',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['20','36'])).

thf('38',plain,(
    $false ),
    inference(simplify,[status(thm)],['37'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QCBGY5q1cS
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:34:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 28 iterations in 0.020s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.20/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.48  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.20/0.48  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.20/0.48  thf(g1_orders_2_type, type, g1_orders_2: $i > $i > $i).
% 0.20/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.48  thf(v1_orders_2_type, type, v1_orders_2: $i > $o).
% 0.20/0.48  thf(k1_yellow_1_type, type, k1_yellow_1: $i > $i).
% 0.20/0.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.48  thf(t1_yellow_1, conjecture,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) ) = ( k1_yellow_1 @ A ) ) & 
% 0.20/0.48       ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) = ( A ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i]:
% 0.20/0.48        ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) ) = ( k1_yellow_1 @ A ) ) & 
% 0.20/0.48          ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) = ( A ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t1_yellow_1])).
% 0.20/0.48  thf('0', plain,
% 0.20/0.48      ((((u1_orders_2 @ (k2_yellow_1 @ sk_A)) != (k1_yellow_1 @ sk_A))
% 0.20/0.48        | ((u1_struct_0 @ (k2_yellow_1 @ sk_A)) != (sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('1', plain,
% 0.20/0.48      ((((u1_struct_0 @ (k2_yellow_1 @ sk_A)) != (sk_A)))
% 0.20/0.48         <= (~ (((u1_struct_0 @ (k2_yellow_1 @ sk_A)) = (sk_A))))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf(d1_yellow_1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( k2_yellow_1 @ A ) = ( g1_orders_2 @ A @ ( k1_yellow_1 @ A ) ) ))).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      (![X6 : $i]:
% 0.20/0.48         ((k2_yellow_1 @ X6) = (g1_orders_2 @ X6 @ (k1_yellow_1 @ X6)))),
% 0.20/0.48      inference('cnf', [status(esa)], [d1_yellow_1])).
% 0.20/0.48  thf(abstractness_v1_orders_2, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( l1_orders_2 @ A ) =>
% 0.20/0.48       ( ( v1_orders_2 @ A ) =>
% 0.20/0.48         ( ( A ) = ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) ) ) ) ))).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (v1_orders_2 @ X0)
% 0.20/0.48          | ((X0) = (g1_orders_2 @ (u1_struct_0 @ X0) @ (u1_orders_2 @ X0)))
% 0.20/0.48          | ~ (l1_orders_2 @ X0))),
% 0.20/0.48      inference('cnf', [status(esa)], [abstractness_v1_orders_2])).
% 0.20/0.48  thf(dt_u1_orders_2, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( l1_orders_2 @ A ) =>
% 0.20/0.48       ( m1_subset_1 @
% 0.20/0.48         ( u1_orders_2 @ A ) @ 
% 0.20/0.48         ( k1_zfmisc_1 @
% 0.20/0.48           ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.20/0.48  thf('4', plain,
% 0.20/0.48      (![X1 : $i]:
% 0.20/0.48         ((m1_subset_1 @ (u1_orders_2 @ X1) @ 
% 0.20/0.48           (k1_zfmisc_1 @ 
% 0.20/0.48            (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X1))))
% 0.20/0.48          | ~ (l1_orders_2 @ X1))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_u1_orders_2])).
% 0.20/0.48  thf(free_g1_orders_2, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) =>
% 0.20/0.48       ( ![C:$i,D:$i]:
% 0.20/0.48         ( ( ( g1_orders_2 @ A @ B ) = ( g1_orders_2 @ C @ D ) ) =>
% 0.20/0.48           ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) ))).
% 0.20/0.48  thf('5', plain,
% 0.20/0.48      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.48         (((g1_orders_2 @ X4 @ X5) != (g1_orders_2 @ X2 @ X3))
% 0.20/0.48          | ((X5) = (X3))
% 0.20/0.48          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X4))))),
% 0.20/0.48      inference('cnf', [status(esa)], [free_g1_orders_2])).
% 0.20/0.48  thf('6', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.48         (~ (l1_orders_2 @ X0)
% 0.20/0.48          | ((u1_orders_2 @ X0) = (X1))
% 0.20/0.48          | ((g1_orders_2 @ (u1_struct_0 @ X0) @ (u1_orders_2 @ X0))
% 0.20/0.48              != (g1_orders_2 @ X2 @ X1)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.48  thf('7', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.48         (((X0) != (g1_orders_2 @ X2 @ X1))
% 0.20/0.48          | ~ (l1_orders_2 @ X0)
% 0.20/0.48          | ~ (v1_orders_2 @ X0)
% 0.20/0.48          | ((u1_orders_2 @ X0) = (X1))
% 0.20/0.48          | ~ (l1_orders_2 @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['3', '6'])).
% 0.20/0.48  thf('8', plain,
% 0.20/0.48      (![X1 : $i, X2 : $i]:
% 0.20/0.48         (((u1_orders_2 @ (g1_orders_2 @ X2 @ X1)) = (X1))
% 0.20/0.48          | ~ (v1_orders_2 @ (g1_orders_2 @ X2 @ X1))
% 0.20/0.48          | ~ (l1_orders_2 @ (g1_orders_2 @ X2 @ X1)))),
% 0.20/0.48      inference('simplify', [status(thm)], ['7'])).
% 0.20/0.48  thf('9', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (v1_orders_2 @ (k2_yellow_1 @ X0))
% 0.20/0.48          | ~ (l1_orders_2 @ (g1_orders_2 @ X0 @ (k1_yellow_1 @ X0)))
% 0.20/0.48          | ((u1_orders_2 @ (g1_orders_2 @ X0 @ (k1_yellow_1 @ X0)))
% 0.20/0.48              = (k1_yellow_1 @ X0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['2', '8'])).
% 0.20/0.48  thf(dt_k2_yellow_1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.20/0.48       ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ))).
% 0.20/0.48  thf('10', plain, (![X7 : $i]: (v1_orders_2 @ (k2_yellow_1 @ X7))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.20/0.48  thf('11', plain,
% 0.20/0.48      (![X6 : $i]:
% 0.20/0.48         ((k2_yellow_1 @ X6) = (g1_orders_2 @ X6 @ (k1_yellow_1 @ X6)))),
% 0.20/0.48      inference('cnf', [status(esa)], [d1_yellow_1])).
% 0.20/0.48  thf('12', plain, (![X8 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X8))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.20/0.48  thf('13', plain,
% 0.20/0.48      (![X6 : $i]:
% 0.20/0.48         ((k2_yellow_1 @ X6) = (g1_orders_2 @ X6 @ (k1_yellow_1 @ X6)))),
% 0.20/0.48      inference('cnf', [status(esa)], [d1_yellow_1])).
% 0.20/0.48  thf('14', plain,
% 0.20/0.48      (![X0 : $i]: ((u1_orders_2 @ (k2_yellow_1 @ X0)) = (k1_yellow_1 @ X0))),
% 0.20/0.48      inference('demod', [status(thm)], ['9', '10', '11', '12', '13'])).
% 0.20/0.48  thf('15', plain,
% 0.20/0.48      ((((u1_orders_2 @ (k2_yellow_1 @ sk_A)) != (k1_yellow_1 @ sk_A)))
% 0.20/0.48         <= (~ (((u1_orders_2 @ (k2_yellow_1 @ sk_A)) = (k1_yellow_1 @ sk_A))))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf('16', plain,
% 0.20/0.48      ((((k1_yellow_1 @ sk_A) != (k1_yellow_1 @ sk_A)))
% 0.20/0.48         <= (~ (((u1_orders_2 @ (k2_yellow_1 @ sk_A)) = (k1_yellow_1 @ sk_A))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.48  thf('17', plain,
% 0.20/0.48      ((((u1_orders_2 @ (k2_yellow_1 @ sk_A)) = (k1_yellow_1 @ sk_A)))),
% 0.20/0.48      inference('simplify', [status(thm)], ['16'])).
% 0.20/0.48  thf('18', plain,
% 0.20/0.48      (~ (((u1_struct_0 @ (k2_yellow_1 @ sk_A)) = (sk_A))) | 
% 0.20/0.48       ~ (((u1_orders_2 @ (k2_yellow_1 @ sk_A)) = (k1_yellow_1 @ sk_A)))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf('19', plain, (~ (((u1_struct_0 @ (k2_yellow_1 @ sk_A)) = (sk_A)))),
% 0.20/0.48      inference('sat_resolution*', [status(thm)], ['17', '18'])).
% 0.20/0.48  thf('20', plain, (((u1_struct_0 @ (k2_yellow_1 @ sk_A)) != (sk_A))),
% 0.20/0.48      inference('simpl_trail', [status(thm)], ['1', '19'])).
% 0.20/0.48  thf('21', plain,
% 0.20/0.48      (![X6 : $i]:
% 0.20/0.48         ((k2_yellow_1 @ X6) = (g1_orders_2 @ X6 @ (k1_yellow_1 @ X6)))),
% 0.20/0.48      inference('cnf', [status(esa)], [d1_yellow_1])).
% 0.20/0.48  thf('22', plain,
% 0.20/0.48      (![X0 : $i]: ((u1_orders_2 @ (k2_yellow_1 @ X0)) = (k1_yellow_1 @ X0))),
% 0.20/0.48      inference('demod', [status(thm)], ['9', '10', '11', '12', '13'])).
% 0.20/0.48  thf('23', plain,
% 0.20/0.48      (![X1 : $i]:
% 0.20/0.48         ((m1_subset_1 @ (u1_orders_2 @ X1) @ 
% 0.20/0.48           (k1_zfmisc_1 @ 
% 0.20/0.48            (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X1))))
% 0.20/0.48          | ~ (l1_orders_2 @ X1))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_u1_orders_2])).
% 0.20/0.48  thf('24', plain,
% 0.20/0.48      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.48         (((g1_orders_2 @ X4 @ X5) != (g1_orders_2 @ X2 @ X3))
% 0.20/0.48          | ((X4) = (X2))
% 0.20/0.48          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X4))))),
% 0.20/0.48      inference('cnf', [status(esa)], [free_g1_orders_2])).
% 0.20/0.48  thf('25', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.48         (~ (l1_orders_2 @ X0)
% 0.20/0.48          | ((u1_struct_0 @ X0) = (X1))
% 0.20/0.48          | ((g1_orders_2 @ (u1_struct_0 @ X0) @ (u1_orders_2 @ X0))
% 0.20/0.48              != (g1_orders_2 @ X1 @ X2)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.48  thf('26', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.48         (((g1_orders_2 @ (u1_struct_0 @ (k2_yellow_1 @ X0)) @ 
% 0.20/0.48            (k1_yellow_1 @ X0)) != (g1_orders_2 @ X2 @ X1))
% 0.20/0.48          | ((u1_struct_0 @ (k2_yellow_1 @ X0)) = (X2))
% 0.20/0.48          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['22', '25'])).
% 0.20/0.48  thf('27', plain,
% 0.20/0.48      (![X0 : $i]: ((u1_orders_2 @ (k2_yellow_1 @ X0)) = (k1_yellow_1 @ X0))),
% 0.20/0.48      inference('demod', [status(thm)], ['9', '10', '11', '12', '13'])).
% 0.20/0.48  thf('28', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (v1_orders_2 @ X0)
% 0.20/0.48          | ((X0) = (g1_orders_2 @ (u1_struct_0 @ X0) @ (u1_orders_2 @ X0)))
% 0.20/0.48          | ~ (l1_orders_2 @ X0))),
% 0.20/0.48      inference('cnf', [status(esa)], [abstractness_v1_orders_2])).
% 0.20/0.48  thf('29', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (((k2_yellow_1 @ X0)
% 0.20/0.48            = (g1_orders_2 @ (u1_struct_0 @ (k2_yellow_1 @ X0)) @ 
% 0.20/0.48               (k1_yellow_1 @ X0)))
% 0.20/0.48          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0))
% 0.20/0.48          | ~ (v1_orders_2 @ (k2_yellow_1 @ X0)))),
% 0.20/0.48      inference('sup+', [status(thm)], ['27', '28'])).
% 0.20/0.48  thf('30', plain, (![X8 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X8))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.20/0.48  thf('31', plain, (![X7 : $i]: (v1_orders_2 @ (k2_yellow_1 @ X7))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.20/0.48  thf('32', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((k2_yellow_1 @ X0)
% 0.20/0.48           = (g1_orders_2 @ (u1_struct_0 @ (k2_yellow_1 @ X0)) @ 
% 0.20/0.48              (k1_yellow_1 @ X0)))),
% 0.20/0.48      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.20/0.48  thf('33', plain, (![X8 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X8))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.20/0.48  thf('34', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.48         (((k2_yellow_1 @ X0) != (g1_orders_2 @ X2 @ X1))
% 0.20/0.48          | ((u1_struct_0 @ (k2_yellow_1 @ X0)) = (X2)))),
% 0.20/0.48      inference('demod', [status(thm)], ['26', '32', '33'])).
% 0.20/0.48  thf('35', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (((k2_yellow_1 @ X1) != (k2_yellow_1 @ X0))
% 0.20/0.48          | ((u1_struct_0 @ (k2_yellow_1 @ X1)) = (X0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['21', '34'])).
% 0.20/0.48  thf('36', plain, (![X0 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X0)) = (X0))),
% 0.20/0.48      inference('eq_res', [status(thm)], ['35'])).
% 0.20/0.48  thf('37', plain, (((sk_A) != (sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['20', '36'])).
% 0.20/0.48  thf('38', plain, ($false), inference('simplify', [status(thm)], ['37'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
