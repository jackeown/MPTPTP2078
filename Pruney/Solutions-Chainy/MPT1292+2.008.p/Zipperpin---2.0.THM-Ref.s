%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uKEOWpGgQN

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:01 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 127 expanded)
%              Number of leaves         :   24 (  48 expanded)
%              Depth                    :   12
%              Number of atoms          :  308 (1073 expanded)
%              Number of equality atoms :   34 ( 100 expanded)
%              Maximal formula depth    :   10 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_setfam_1_type,type,(
    m1_setfam_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t5_tops_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ~ ( ( m1_setfam_1 @ B @ ( u1_struct_0 @ A ) )
              & ( B = k1_xboole_0 ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( l1_struct_0 @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ~ ( ( m1_setfam_1 @ B @ ( u1_struct_0 @ A ) )
                & ( B = k1_xboole_0 ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t5_tops_2])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_setfam_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_setfam_1 @ B @ A )
    <=> ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('2',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ X14 @ ( k3_tarski @ X15 ) )
      | ~ ( m1_setfam_1 @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d12_setfam_1])).

thf('3',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( k3_tarski @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('4',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('5',plain,
    ( ~ ( r1_tarski @ ( k3_tarski @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( k3_tarski @ sk_B_1 )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t91_orders_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( ( k3_tarski @ A )
           != k1_xboole_0 )
          & ! [B: $i] :
              ~ ( ( B != k1_xboole_0 )
                & ( r2_hidden @ B @ A ) ) )
      & ~ ( ? [B: $i] :
              ( ( r2_hidden @ B @ A )
              & ( B != k1_xboole_0 ) )
          & ( ( k3_tarski @ A )
            = k1_xboole_0 ) ) ) )).

thf('6',plain,(
    ! [X20: $i] :
      ( ( ( k3_tarski @ X20 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X20 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[t91_orders_1])).

thf('7',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X20: $i] :
      ( ( ( k3_tarski @ X20 )
        = sk_B_1 )
      | ( r2_hidden @ ( sk_B @ X20 ) @ X20 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('9',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('10',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X7: $i] :
      ( r1_tarski @ sk_B_1 @ X7 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( ( k3_tarski @ sk_B_1 )
        = sk_B_1 )
      | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('15',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X11 )
      | ( r1_tarski @ X12 @ X10 )
      | ( X11
       != ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('16',plain,(
    ! [X10: $i,X12: $i] :
      ( ( r1_tarski @ X12 @ X10 )
      | ~ ( r2_hidden @ X12 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( k3_tarski @ sk_B_1 )
        = sk_B_1 )
      | ( r1_tarski @ ( sk_B @ sk_B_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('18',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ~ ( r1_tarski @ X8 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('19',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X8: $i] :
      ( ( X8 = sk_B_1 )
      | ~ ( r1_tarski @ X8 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,
    ( ( ( k3_tarski @ sk_B_1 )
      = sk_B_1 )
    | ( ( sk_B @ sk_B_1 )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['17','21'])).

thf('23',plain,(
    ! [X20: $i] :
      ( ( ( k3_tarski @ X20 )
        = k1_xboole_0 )
      | ( ( sk_B @ X20 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t91_orders_1])).

thf('24',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X20: $i] :
      ( ( ( k3_tarski @ X20 )
        = sk_B_1 )
      | ( ( sk_B @ X20 )
       != sk_B_1 ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,
    ( ( k3_tarski @ sk_B_1 )
    = sk_B_1 ),
    inference(clc,[status(thm)],['22','26'])).

thf('28',plain,(
    ! [X7: $i] :
      ( r1_tarski @ sk_B_1 @ X7 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('29',plain,
    ( ( k3_tarski @ sk_B_1 )
    = sk_B_1 ),
    inference(clc,[status(thm)],['22','26'])).

thf('30',plain,
    ( sk_B_1
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['5','27','28','29'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('31',plain,(
    ! [X17: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('32',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('33',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('34',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['32','35','36'])).

thf('38',plain,(
    $false ),
    inference(demod,[status(thm)],['0','37'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uKEOWpGgQN
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:16:44 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 62 iterations in 0.046s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.50  thf(m1_setfam_1_type, type, m1_setfam_1: $i > $i > $o).
% 0.21/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.50  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.50  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.50  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.21/0.50  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.50  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.50  thf(t5_tops_2, conjecture,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( m1_subset_1 @
% 0.21/0.50             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.50           ( ~( ( m1_setfam_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.50                ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i]:
% 0.21/0.50        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.50          ( ![B:$i]:
% 0.21/0.50            ( ( m1_subset_1 @
% 0.21/0.50                B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.50              ( ~( ( m1_setfam_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.50                   ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t5_tops_2])).
% 0.21/0.50  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('1', plain, ((m1_setfam_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(d12_setfam_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( m1_setfam_1 @ B @ A ) <=> ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.21/0.50  thf('2', plain,
% 0.21/0.50      (![X14 : $i, X15 : $i]:
% 0.21/0.50         ((r1_tarski @ X14 @ (k3_tarski @ X15)) | ~ (m1_setfam_1 @ X15 @ X14))),
% 0.21/0.50      inference('cnf', [status(esa)], [d12_setfam_1])).
% 0.21/0.50  thf('3', plain, ((r1_tarski @ (u1_struct_0 @ sk_A) @ (k3_tarski @ sk_B_1))),
% 0.21/0.50      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.50  thf(d10_xboole_0, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.50  thf('4', plain,
% 0.21/0.50      (![X4 : $i, X6 : $i]:
% 0.21/0.50         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.21/0.50      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.50  thf('5', plain,
% 0.21/0.50      ((~ (r1_tarski @ (k3_tarski @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 0.21/0.50        | ((k3_tarski @ sk_B_1) = (u1_struct_0 @ sk_A)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.50  thf(t91_orders_1, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ~( ( ( k3_tarski @ A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.50            ( ![B:$i]:
% 0.21/0.50              ( ~( ( ( B ) != ( k1_xboole_0 ) ) & ( r2_hidden @ B @ A ) ) ) ) ) ) & 
% 0.21/0.50       ( ~( ( ?[B:$i]: ( ( r2_hidden @ B @ A ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 0.21/0.50            ( ( k3_tarski @ A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.21/0.50  thf('6', plain,
% 0.21/0.50      (![X20 : $i]:
% 0.21/0.50         (((k3_tarski @ X20) = (k1_xboole_0))
% 0.21/0.50          | (r2_hidden @ (sk_B @ X20) @ X20))),
% 0.21/0.50      inference('cnf', [status(esa)], [t91_orders_1])).
% 0.21/0.50  thf('7', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('8', plain,
% 0.21/0.50      (![X20 : $i]:
% 0.21/0.50         (((k3_tarski @ X20) = (sk_B_1)) | (r2_hidden @ (sk_B @ X20) @ X20))),
% 0.21/0.50      inference('demod', [status(thm)], ['6', '7'])).
% 0.21/0.50  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.50  thf('9', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.21/0.50      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.50  thf('10', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('11', plain, (![X7 : $i]: (r1_tarski @ sk_B_1 @ X7)),
% 0.21/0.50      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.50  thf(d3_tarski, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.50  thf('12', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.50          | (r2_hidden @ X0 @ X2)
% 0.21/0.50          | ~ (r1_tarski @ X1 @ X2))),
% 0.21/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.50  thf('13', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ sk_B_1))),
% 0.21/0.50      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.50  thf('14', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (((k3_tarski @ sk_B_1) = (sk_B_1))
% 0.21/0.50          | (r2_hidden @ (sk_B @ sk_B_1) @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['8', '13'])).
% 0.21/0.50  thf(d1_zfmisc_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.21/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.21/0.50  thf('15', plain,
% 0.21/0.50      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X12 @ X11)
% 0.21/0.50          | (r1_tarski @ X12 @ X10)
% 0.21/0.50          | ((X11) != (k1_zfmisc_1 @ X10)))),
% 0.21/0.50      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.21/0.50  thf('16', plain,
% 0.21/0.50      (![X10 : $i, X12 : $i]:
% 0.21/0.50         ((r1_tarski @ X12 @ X10) | ~ (r2_hidden @ X12 @ (k1_zfmisc_1 @ X10)))),
% 0.21/0.50      inference('simplify', [status(thm)], ['15'])).
% 0.21/0.50  thf('17', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (((k3_tarski @ sk_B_1) = (sk_B_1))
% 0.21/0.50          | (r1_tarski @ (sk_B @ sk_B_1) @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['14', '16'])).
% 0.21/0.50  thf(t3_xboole_1, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.50  thf('18', plain,
% 0.21/0.50      (![X8 : $i]: (((X8) = (k1_xboole_0)) | ~ (r1_tarski @ X8 @ k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.21/0.50  thf('19', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('20', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('21', plain,
% 0.21/0.50      (![X8 : $i]: (((X8) = (sk_B_1)) | ~ (r1_tarski @ X8 @ sk_B_1))),
% 0.21/0.50      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.21/0.50  thf('22', plain,
% 0.21/0.50      ((((k3_tarski @ sk_B_1) = (sk_B_1)) | ((sk_B @ sk_B_1) = (sk_B_1)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['17', '21'])).
% 0.21/0.50  thf('23', plain,
% 0.21/0.50      (![X20 : $i]:
% 0.21/0.50         (((k3_tarski @ X20) = (k1_xboole_0)) | ((sk_B @ X20) != (k1_xboole_0)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t91_orders_1])).
% 0.21/0.50  thf('24', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('25', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('26', plain,
% 0.21/0.50      (![X20 : $i]:
% 0.21/0.50         (((k3_tarski @ X20) = (sk_B_1)) | ((sk_B @ X20) != (sk_B_1)))),
% 0.21/0.50      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.21/0.50  thf('27', plain, (((k3_tarski @ sk_B_1) = (sk_B_1))),
% 0.21/0.50      inference('clc', [status(thm)], ['22', '26'])).
% 0.21/0.50  thf('28', plain, (![X7 : $i]: (r1_tarski @ sk_B_1 @ X7)),
% 0.21/0.50      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.50  thf('29', plain, (((k3_tarski @ sk_B_1) = (sk_B_1))),
% 0.21/0.50      inference('clc', [status(thm)], ['22', '26'])).
% 0.21/0.50  thf('30', plain, (((sk_B_1) = (u1_struct_0 @ sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['5', '27', '28', '29'])).
% 0.21/0.50  thf(fc2_struct_0, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.50       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.50  thf('31', plain,
% 0.21/0.50      (![X17 : $i]:
% 0.21/0.50         (~ (v1_xboole_0 @ (u1_struct_0 @ X17))
% 0.21/0.50          | ~ (l1_struct_0 @ X17)
% 0.21/0.50          | (v2_struct_0 @ X17))),
% 0.21/0.50      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.21/0.50  thf('32', plain,
% 0.21/0.50      ((~ (v1_xboole_0 @ sk_B_1)
% 0.21/0.50        | (v2_struct_0 @ sk_A)
% 0.21/0.50        | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['30', '31'])).
% 0.21/0.50  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.21/0.50  thf('33', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.50      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.50  thf('34', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('35', plain, ((v1_xboole_0 @ sk_B_1)),
% 0.21/0.50      inference('demod', [status(thm)], ['33', '34'])).
% 0.21/0.50  thf('36', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('37', plain, ((v2_struct_0 @ sk_A)),
% 0.21/0.50      inference('demod', [status(thm)], ['32', '35', '36'])).
% 0.21/0.50  thf('38', plain, ($false), inference('demod', [status(thm)], ['0', '37'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
