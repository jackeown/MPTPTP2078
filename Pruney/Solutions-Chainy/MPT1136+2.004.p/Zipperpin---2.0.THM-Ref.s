%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SVUi3vM6ws

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:33 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   61 (  77 expanded)
%              Number of leaves         :   27 (  35 expanded)
%              Depth                    :   13
%              Number of atoms          :  357 ( 581 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(r1_relat_2_type,type,(
    r1_relat_2: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t24_orders_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( r1_orders_2 @ A @ B @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v3_orders_2 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ( r1_orders_2 @ A @ B @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t24_orders_2])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('3',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(dt_u1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( u1_orders_2 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('4',plain,(
    ! [X17: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X17 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X17 ) ) ) )
      | ~ ( l1_orders_2 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_orders_2])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('5',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) )
      | ( v1_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('7',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(d4_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v3_orders_2 @ A )
      <=> ( r1_relat_2 @ ( u1_orders_2 @ A ) @ ( u1_struct_0 @ A ) ) ) ) )).

thf('9',plain,(
    ! [X12: $i] :
      ( ~ ( v3_orders_2 @ X12 )
      | ( r1_relat_2 @ ( u1_orders_2 @ X12 ) @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_orders_2 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d4_orders_2])).

thf(d1_relat_2,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r1_relat_2 @ A @ B )
        <=> ! [C: $i] :
              ( ( r2_hidden @ C @ B )
             => ( r2_hidden @ ( k4_tarski @ C @ C ) @ A ) ) ) ) )).

thf('10',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_relat_2 @ X8 @ X9 )
      | ( r2_hidden @ ( k4_tarski @ X10 @ X10 ) @ X8 )
      | ~ ( r2_hidden @ X10 @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_2])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v1_relat_1 @ ( u1_orders_2 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ X1 @ X1 ) @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ X1 ) @ ( u1_orders_2 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_orders_2 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ X1 @ X1 ) @ ( u1_orders_2 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r2_hidden @ ( k4_tarski @ sk_B @ sk_B ) @ ( u1_orders_2 @ sk_A ) )
    | ~ ( v3_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','13'])).

thf('15',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( k4_tarski @ sk_B @ sk_B ) @ ( u1_orders_2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf(d9_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r1_orders_2 @ A @ B @ C )
              <=> ( r2_hidden @ ( k4_tarski @ B @ C ) @ ( u1_orders_2 @ A ) ) ) ) ) ) )).

thf('18',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X14 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X13 @ X15 ) @ ( u1_orders_2 @ X14 ) )
      | ( r1_orders_2 @ X14 @ X13 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_orders_2 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d9_orders_2])).

thf('19',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ sk_B @ sk_B )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['19','20','21','22'])).

thf('24',plain,(
    ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['23','24'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('26',plain,(
    ! [X11: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X11 ) )
      | ~ ( l1_struct_0 @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('27',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('29',plain,(
    ! [X16: $i] :
      ( ( l1_struct_0 @ X16 )
      | ~ ( l1_orders_2 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf('30',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['27','30'])).

thf('32',plain,(
    $false ),
    inference(demod,[status(thm)],['0','31'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SVUi3vM6ws
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:45:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.22/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.48  % Solved by: fo/fo7.sh
% 0.22/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.48  % done 40 iterations in 0.024s
% 0.22/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.48  % SZS output start Refutation
% 0.22/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.48  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.22/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.48  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.22/0.48  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.22/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.48  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.22/0.48  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.22/0.48  thf(r1_relat_2_type, type, r1_relat_2: $i > $i > $o).
% 0.22/0.48  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.22/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.48  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.22/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.48  thf(t24_orders_2, conjecture,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.22/0.48       ( ![B:$i]:
% 0.22/0.48         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.48           ( r1_orders_2 @ A @ B @ B ) ) ) ))).
% 0.22/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.48    (~( ![A:$i]:
% 0.22/0.48        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.22/0.48            ( l1_orders_2 @ A ) ) =>
% 0.22/0.48          ( ![B:$i]:
% 0.22/0.48            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.48              ( r1_orders_2 @ A @ B @ B ) ) ) ) )),
% 0.22/0.48    inference('cnf.neg', [status(esa)], [t24_orders_2])).
% 0.22/0.48  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('1', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf(d2_subset_1, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( ( v1_xboole_0 @ A ) =>
% 0.22/0.48         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.22/0.48       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.48         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.22/0.48  thf('2', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i]:
% 0.22/0.48         (~ (m1_subset_1 @ X0 @ X1)
% 0.22/0.48          | (r2_hidden @ X0 @ X1)
% 0.22/0.48          | (v1_xboole_0 @ X1))),
% 0.22/0.48      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.22/0.48  thf('3', plain,
% 0.22/0.48      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.48        | (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.22/0.48      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.48  thf(dt_u1_orders_2, axiom,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ( l1_orders_2 @ A ) =>
% 0.22/0.48       ( m1_subset_1 @
% 0.22/0.48         ( u1_orders_2 @ A ) @ 
% 0.22/0.48         ( k1_zfmisc_1 @
% 0.22/0.48           ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.22/0.48  thf('4', plain,
% 0.22/0.48      (![X17 : $i]:
% 0.22/0.48         ((m1_subset_1 @ (u1_orders_2 @ X17) @ 
% 0.22/0.48           (k1_zfmisc_1 @ 
% 0.22/0.48            (k2_zfmisc_1 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X17))))
% 0.22/0.48          | ~ (l1_orders_2 @ X17))),
% 0.22/0.48      inference('cnf', [status(esa)], [dt_u1_orders_2])).
% 0.22/0.48  thf(cc2_relat_1, axiom,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ( v1_relat_1 @ A ) =>
% 0.22/0.48       ( ![B:$i]:
% 0.22/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.22/0.48  thf('5', plain,
% 0.22/0.48      (![X3 : $i, X4 : $i]:
% 0.22/0.48         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.22/0.48          | (v1_relat_1 @ X3)
% 0.22/0.48          | ~ (v1_relat_1 @ X4))),
% 0.22/0.48      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.22/0.48  thf('6', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         (~ (l1_orders_2 @ X0)
% 0.22/0.48          | ~ (v1_relat_1 @ 
% 0.22/0.48               (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0)))
% 0.22/0.48          | (v1_relat_1 @ (u1_orders_2 @ X0)))),
% 0.22/0.48      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.48  thf(fc6_relat_1, axiom,
% 0.22/0.48    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.22/0.48  thf('7', plain,
% 0.22/0.48      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 0.22/0.48      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.22/0.48  thf('8', plain,
% 0.22/0.48      (![X0 : $i]: (~ (l1_orders_2 @ X0) | (v1_relat_1 @ (u1_orders_2 @ X0)))),
% 0.22/0.48      inference('demod', [status(thm)], ['6', '7'])).
% 0.22/0.48  thf(d4_orders_2, axiom,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ( l1_orders_2 @ A ) =>
% 0.22/0.48       ( ( v3_orders_2 @ A ) <=>
% 0.22/0.48         ( r1_relat_2 @ ( u1_orders_2 @ A ) @ ( u1_struct_0 @ A ) ) ) ))).
% 0.22/0.48  thf('9', plain,
% 0.22/0.48      (![X12 : $i]:
% 0.22/0.48         (~ (v3_orders_2 @ X12)
% 0.22/0.48          | (r1_relat_2 @ (u1_orders_2 @ X12) @ (u1_struct_0 @ X12))
% 0.22/0.48          | ~ (l1_orders_2 @ X12))),
% 0.22/0.48      inference('cnf', [status(esa)], [d4_orders_2])).
% 0.22/0.48  thf(d1_relat_2, axiom,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ( v1_relat_1 @ A ) =>
% 0.22/0.48       ( ![B:$i]:
% 0.22/0.48         ( ( r1_relat_2 @ A @ B ) <=>
% 0.22/0.48           ( ![C:$i]:
% 0.22/0.48             ( ( r2_hidden @ C @ B ) =>
% 0.22/0.48               ( r2_hidden @ ( k4_tarski @ C @ C ) @ A ) ) ) ) ) ))).
% 0.22/0.48  thf('10', plain,
% 0.22/0.48      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.22/0.48         (~ (r1_relat_2 @ X8 @ X9)
% 0.22/0.48          | (r2_hidden @ (k4_tarski @ X10 @ X10) @ X8)
% 0.22/0.48          | ~ (r2_hidden @ X10 @ X9)
% 0.22/0.48          | ~ (v1_relat_1 @ X8))),
% 0.22/0.48      inference('cnf', [status(esa)], [d1_relat_2])).
% 0.22/0.48  thf('11', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i]:
% 0.22/0.48         (~ (l1_orders_2 @ X0)
% 0.22/0.48          | ~ (v3_orders_2 @ X0)
% 0.22/0.48          | ~ (v1_relat_1 @ (u1_orders_2 @ X0))
% 0.22/0.48          | ~ (r2_hidden @ X1 @ (u1_struct_0 @ X0))
% 0.22/0.48          | (r2_hidden @ (k4_tarski @ X1 @ X1) @ (u1_orders_2 @ X0)))),
% 0.22/0.48      inference('sup-', [status(thm)], ['9', '10'])).
% 0.22/0.48  thf('12', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i]:
% 0.22/0.48         (~ (l1_orders_2 @ X0)
% 0.22/0.48          | (r2_hidden @ (k4_tarski @ X1 @ X1) @ (u1_orders_2 @ X0))
% 0.22/0.48          | ~ (r2_hidden @ X1 @ (u1_struct_0 @ X0))
% 0.22/0.48          | ~ (v3_orders_2 @ X0)
% 0.22/0.48          | ~ (l1_orders_2 @ X0))),
% 0.22/0.48      inference('sup-', [status(thm)], ['8', '11'])).
% 0.22/0.48  thf('13', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i]:
% 0.22/0.48         (~ (v3_orders_2 @ X0)
% 0.22/0.48          | ~ (r2_hidden @ X1 @ (u1_struct_0 @ X0))
% 0.22/0.48          | (r2_hidden @ (k4_tarski @ X1 @ X1) @ (u1_orders_2 @ X0))
% 0.22/0.48          | ~ (l1_orders_2 @ X0))),
% 0.22/0.48      inference('simplify', [status(thm)], ['12'])).
% 0.22/0.48  thf('14', plain,
% 0.22/0.48      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.48        | ~ (l1_orders_2 @ sk_A)
% 0.22/0.48        | (r2_hidden @ (k4_tarski @ sk_B @ sk_B) @ (u1_orders_2 @ sk_A))
% 0.22/0.48        | ~ (v3_orders_2 @ sk_A))),
% 0.22/0.48      inference('sup-', [status(thm)], ['3', '13'])).
% 0.22/0.48  thf('15', plain, ((l1_orders_2 @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('16', plain, ((v3_orders_2 @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('17', plain,
% 0.22/0.48      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.48        | (r2_hidden @ (k4_tarski @ sk_B @ sk_B) @ (u1_orders_2 @ sk_A)))),
% 0.22/0.48      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.22/0.48  thf(d9_orders_2, axiom,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ( l1_orders_2 @ A ) =>
% 0.22/0.48       ( ![B:$i]:
% 0.22/0.48         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.48           ( ![C:$i]:
% 0.22/0.48             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.48               ( ( r1_orders_2 @ A @ B @ C ) <=>
% 0.22/0.48                 ( r2_hidden @ ( k4_tarski @ B @ C ) @ ( u1_orders_2 @ A ) ) ) ) ) ) ) ))).
% 0.22/0.48  thf('18', plain,
% 0.22/0.48      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.22/0.48         (~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X14))
% 0.22/0.48          | ~ (r2_hidden @ (k4_tarski @ X13 @ X15) @ (u1_orders_2 @ X14))
% 0.22/0.48          | (r1_orders_2 @ X14 @ X13 @ X15)
% 0.22/0.48          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X14))
% 0.22/0.48          | ~ (l1_orders_2 @ X14))),
% 0.22/0.48      inference('cnf', [status(esa)], [d9_orders_2])).
% 0.22/0.48  thf('19', plain,
% 0.22/0.48      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.48        | ~ (l1_orders_2 @ sk_A)
% 0.22/0.48        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.22/0.48        | (r1_orders_2 @ sk_A @ sk_B @ sk_B)
% 0.22/0.48        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.22/0.48      inference('sup-', [status(thm)], ['17', '18'])).
% 0.22/0.48  thf('20', plain, ((l1_orders_2 @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('21', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('22', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('23', plain,
% 0.22/0.48      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.48        | (r1_orders_2 @ sk_A @ sk_B @ sk_B))),
% 0.22/0.48      inference('demod', [status(thm)], ['19', '20', '21', '22'])).
% 0.22/0.48  thf('24', plain, (~ (r1_orders_2 @ sk_A @ sk_B @ sk_B)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('25', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.22/0.48      inference('clc', [status(thm)], ['23', '24'])).
% 0.22/0.48  thf(fc2_struct_0, axiom,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.22/0.48       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.22/0.48  thf('26', plain,
% 0.22/0.48      (![X11 : $i]:
% 0.22/0.48         (~ (v1_xboole_0 @ (u1_struct_0 @ X11))
% 0.22/0.48          | ~ (l1_struct_0 @ X11)
% 0.22/0.48          | (v2_struct_0 @ X11))),
% 0.22/0.48      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.22/0.48  thf('27', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.22/0.48      inference('sup-', [status(thm)], ['25', '26'])).
% 0.22/0.48  thf('28', plain, ((l1_orders_2 @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf(dt_l1_orders_2, axiom,
% 0.22/0.48    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 0.22/0.48  thf('29', plain,
% 0.22/0.48      (![X16 : $i]: ((l1_struct_0 @ X16) | ~ (l1_orders_2 @ X16))),
% 0.22/0.48      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 0.22/0.48  thf('30', plain, ((l1_struct_0 @ sk_A)),
% 0.22/0.48      inference('sup-', [status(thm)], ['28', '29'])).
% 0.22/0.48  thf('31', plain, ((v2_struct_0 @ sk_A)),
% 0.22/0.48      inference('demod', [status(thm)], ['27', '30'])).
% 0.22/0.48  thf('32', plain, ($false), inference('demod', [status(thm)], ['0', '31'])).
% 0.22/0.48  
% 0.22/0.48  % SZS output end Refutation
% 0.22/0.48  
% 0.22/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
