%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gf8InYW0aS

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:02 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   49 (  64 expanded)
%              Number of leaves         :   22 (  29 expanded)
%              Depth                    :   10
%              Number of atoms          :  203 ( 416 expanded)
%              Number of equality atoms :   17 (  30 expanded)
%              Maximal formula depth    :   10 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(m1_setfam_1_type,type,(
    m1_setfam_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ ( k3_tarski @ X5 ) )
      | ~ ( m1_setfam_1 @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d12_setfam_1])).

thf('3',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( k3_tarski @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('4',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('5',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X3: $i] :
      ( r1_tarski @ sk_B_1 @ X3 ) ),
    inference(demod,[status(thm)],['4','5'])).

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

thf('7',plain,(
    ! [X12: $i] :
      ( ( ( k3_tarski @ X12 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X12 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t91_orders_1])).

thf('8',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X12: $i] :
      ( ( ( k3_tarski @ X12 )
        = sk_B_1 )
      | ( r2_hidden @ ( sk_B @ X12 ) @ X12 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('10',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( ( k3_tarski @ X0 )
        = sk_B_1 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( k3_tarski @ sk_B_1 )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['6','11'])).

thf('13',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ),
    inference(demod,[status(thm)],['3','12'])).

thf('14',plain,(
    ! [X3: $i] :
      ( r1_tarski @ sk_B_1 @ X3 ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('15',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B_1 )
      | ( X0 = sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( u1_struct_0 @ sk_A )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['13','16'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('18',plain,(
    ! [X9: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('19',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('20',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('21',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['19','22','23'])).

thf('25',plain,(
    $false ),
    inference(demod,[status(thm)],['0','24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gf8InYW0aS
% 0.14/0.36  % Computer   : n007.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 16:54:21 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.46  % Solved by: fo/fo7.sh
% 0.22/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.46  % done 27 iterations in 0.014s
% 0.22/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.46  % SZS output start Refutation
% 0.22/0.46  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.22/0.46  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.46  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.22/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.46  thf(sk_B_type, type, sk_B: $i > $i).
% 0.22/0.46  thf(m1_setfam_1_type, type, m1_setfam_1: $i > $i > $o).
% 0.22/0.46  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.22/0.46  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.46  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.22/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.46  thf(t5_tops_2, conjecture,
% 0.22/0.46    (![A:$i]:
% 0.22/0.46     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.22/0.46       ( ![B:$i]:
% 0.22/0.46         ( ( m1_subset_1 @
% 0.22/0.46             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.22/0.46           ( ~( ( m1_setfam_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.22/0.46                ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.22/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.46    (~( ![A:$i]:
% 0.22/0.46        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.22/0.46          ( ![B:$i]:
% 0.22/0.46            ( ( m1_subset_1 @
% 0.22/0.46                B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.22/0.46              ( ~( ( m1_setfam_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.22/0.46                   ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ) ) )),
% 0.22/0.46    inference('cnf.neg', [status(esa)], [t5_tops_2])).
% 0.22/0.46  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.46  thf('1', plain, ((m1_setfam_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.22/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.46  thf(d12_setfam_1, axiom,
% 0.22/0.46    (![A:$i,B:$i]:
% 0.22/0.46     ( ( m1_setfam_1 @ B @ A ) <=> ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.22/0.46  thf('2', plain,
% 0.22/0.46      (![X4 : $i, X5 : $i]:
% 0.22/0.46         ((r1_tarski @ X4 @ (k3_tarski @ X5)) | ~ (m1_setfam_1 @ X5 @ X4))),
% 0.22/0.46      inference('cnf', [status(esa)], [d12_setfam_1])).
% 0.22/0.46  thf('3', plain, ((r1_tarski @ (u1_struct_0 @ sk_A) @ (k3_tarski @ sk_B_1))),
% 0.22/0.46      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.46  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.22/0.46  thf('4', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.22/0.46      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.22/0.46  thf('5', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.22/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.46  thf('6', plain, (![X3 : $i]: (r1_tarski @ sk_B_1 @ X3)),
% 0.22/0.46      inference('demod', [status(thm)], ['4', '5'])).
% 0.22/0.46  thf(t91_orders_1, axiom,
% 0.22/0.46    (![A:$i]:
% 0.22/0.46     ( ( ~( ( ( k3_tarski @ A ) != ( k1_xboole_0 ) ) & 
% 0.22/0.46            ( ![B:$i]:
% 0.22/0.46              ( ~( ( ( B ) != ( k1_xboole_0 ) ) & ( r2_hidden @ B @ A ) ) ) ) ) ) & 
% 0.22/0.46       ( ~( ( ?[B:$i]: ( ( r2_hidden @ B @ A ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 0.22/0.46            ( ( k3_tarski @ A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.22/0.46  thf('7', plain,
% 0.22/0.46      (![X12 : $i]:
% 0.22/0.46         (((k3_tarski @ X12) = (k1_xboole_0))
% 0.22/0.46          | (r2_hidden @ (sk_B @ X12) @ X12))),
% 0.22/0.46      inference('cnf', [status(esa)], [t91_orders_1])).
% 0.22/0.46  thf('8', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.22/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.46  thf('9', plain,
% 0.22/0.46      (![X12 : $i]:
% 0.22/0.46         (((k3_tarski @ X12) = (sk_B_1)) | (r2_hidden @ (sk_B @ X12) @ X12))),
% 0.22/0.46      inference('demod', [status(thm)], ['7', '8'])).
% 0.22/0.46  thf(t7_ordinal1, axiom,
% 0.22/0.46    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.46  thf('10', plain,
% 0.22/0.46      (![X7 : $i, X8 : $i]: (~ (r2_hidden @ X7 @ X8) | ~ (r1_tarski @ X8 @ X7))),
% 0.22/0.46      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.22/0.46  thf('11', plain,
% 0.22/0.46      (![X0 : $i]:
% 0.22/0.46         (((k3_tarski @ X0) = (sk_B_1)) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 0.22/0.46      inference('sup-', [status(thm)], ['9', '10'])).
% 0.22/0.46  thf('12', plain, (((k3_tarski @ sk_B_1) = (sk_B_1))),
% 0.22/0.46      inference('sup-', [status(thm)], ['6', '11'])).
% 0.22/0.46  thf('13', plain, ((r1_tarski @ (u1_struct_0 @ sk_A) @ sk_B_1)),
% 0.22/0.46      inference('demod', [status(thm)], ['3', '12'])).
% 0.22/0.46  thf('14', plain, (![X3 : $i]: (r1_tarski @ sk_B_1 @ X3)),
% 0.22/0.46      inference('demod', [status(thm)], ['4', '5'])).
% 0.22/0.46  thf(d10_xboole_0, axiom,
% 0.22/0.46    (![A:$i,B:$i]:
% 0.22/0.46     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.46  thf('15', plain,
% 0.22/0.46      (![X0 : $i, X2 : $i]:
% 0.22/0.46         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.22/0.46      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.46  thf('16', plain,
% 0.22/0.46      (![X0 : $i]: (~ (r1_tarski @ X0 @ sk_B_1) | ((X0) = (sk_B_1)))),
% 0.22/0.46      inference('sup-', [status(thm)], ['14', '15'])).
% 0.22/0.46  thf('17', plain, (((u1_struct_0 @ sk_A) = (sk_B_1))),
% 0.22/0.46      inference('sup-', [status(thm)], ['13', '16'])).
% 0.22/0.46  thf(fc2_struct_0, axiom,
% 0.22/0.46    (![A:$i]:
% 0.22/0.46     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.22/0.46       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.22/0.46  thf('18', plain,
% 0.22/0.46      (![X9 : $i]:
% 0.22/0.46         (~ (v1_xboole_0 @ (u1_struct_0 @ X9))
% 0.22/0.46          | ~ (l1_struct_0 @ X9)
% 0.22/0.46          | (v2_struct_0 @ X9))),
% 0.22/0.46      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.22/0.46  thf('19', plain,
% 0.22/0.46      ((~ (v1_xboole_0 @ sk_B_1)
% 0.22/0.46        | (v2_struct_0 @ sk_A)
% 0.22/0.46        | ~ (l1_struct_0 @ sk_A))),
% 0.22/0.46      inference('sup-', [status(thm)], ['17', '18'])).
% 0.22/0.46  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.22/0.46  thf('20', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.22/0.46      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.22/0.46  thf('21', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.22/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.46  thf('22', plain, ((v1_xboole_0 @ sk_B_1)),
% 0.22/0.46      inference('demod', [status(thm)], ['20', '21'])).
% 0.22/0.46  thf('23', plain, ((l1_struct_0 @ sk_A)),
% 0.22/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.46  thf('24', plain, ((v2_struct_0 @ sk_A)),
% 0.22/0.46      inference('demod', [status(thm)], ['19', '22', '23'])).
% 0.22/0.46  thf('25', plain, ($false), inference('demod', [status(thm)], ['0', '24'])).
% 0.22/0.46  
% 0.22/0.46  % SZS output end Refutation
% 0.22/0.46  
% 0.22/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
