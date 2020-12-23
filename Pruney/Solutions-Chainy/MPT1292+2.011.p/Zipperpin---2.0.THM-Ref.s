%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8dbzdx8ldD

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:02 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   51 (  74 expanded)
%              Number of leaves         :   21 (  31 expanded)
%              Depth                    :   10
%              Number of atoms          :  209 ( 490 expanded)
%              Number of equality atoms :   17 (  34 expanded)
%              Maximal formula depth    :   10 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_setfam_1_type,type,(
    m1_setfam_1: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

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
    m1_setfam_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_setfam_1 @ B @ A )
    <=> ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ ( k3_tarski @ X9 ) )
      | ~ ( m1_setfam_1 @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d12_setfam_1])).

thf('3',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( k3_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('4',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('5',plain,
    ( ~ ( r1_tarski @ ( k3_tarski @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( k3_tarski @ sk_B )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t99_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf('6',plain,(
    ! [X7: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X7 ) )
      = X7 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('7',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('8',plain,(
    sk_B = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X3: $i] :
      ( r1_tarski @ sk_B @ X3 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(t95_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) )).

thf('10',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X5 ) @ ( k3_tarski @ X6 ) )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t95_zfmisc_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_tarski @ sk_B ) @ ( k3_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_tarski @ sk_B ) @ X0 ) ),
    inference('sup+',[status(thm)],['6','11'])).

thf('13',plain,
    ( ( k3_tarski @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['5','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_tarski @ sk_B ) @ X0 ) ),
    inference('sup+',[status(thm)],['6','11'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('15',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('16',plain,(
    sk_B = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    sk_B = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X4: $i] :
      ( ( X4 = sk_B )
      | ~ ( r1_tarski @ X4 @ sk_B ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,
    ( ( k3_tarski @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['14','18'])).

thf('20',plain,
    ( sk_B
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['13','19'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('21',plain,(
    ! [X11: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X11 ) )
      | ~ ( l1_struct_0 @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('22',plain,
    ( ~ ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('23',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('24',plain,(
    sk_B = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_xboole_0 @ sk_B ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['22','25','26'])).

thf('28',plain,(
    $false ),
    inference(demod,[status(thm)],['0','27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8dbzdx8ldD
% 0.14/0.33  % Computer   : n022.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 20:19:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 0.21/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.46  % Solved by: fo/fo7.sh
% 0.21/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.46  % done 38 iterations in 0.017s
% 0.21/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.46  % SZS output start Refutation
% 0.21/0.46  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.46  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.21/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.46  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.46  thf(m1_setfam_1_type, type, m1_setfam_1: $i > $i > $o).
% 0.21/0.46  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.46  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.46  thf(t5_tops_2, conjecture,
% 0.21/0.46    (![A:$i]:
% 0.21/0.46     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.46       ( ![B:$i]:
% 0.21/0.46         ( ( m1_subset_1 @
% 0.21/0.46             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.46           ( ~( ( m1_setfam_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.46                ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.21/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.46    (~( ![A:$i]:
% 0.21/0.46        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.46          ( ![B:$i]:
% 0.21/0.46            ( ( m1_subset_1 @
% 0.21/0.46                B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.46              ( ~( ( m1_setfam_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.46                   ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ) ) )),
% 0.21/0.46    inference('cnf.neg', [status(esa)], [t5_tops_2])).
% 0.21/0.46  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('1', plain, ((m1_setfam_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf(d12_setfam_1, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( m1_setfam_1 @ B @ A ) <=> ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.21/0.46  thf('2', plain,
% 0.21/0.46      (![X8 : $i, X9 : $i]:
% 0.21/0.46         ((r1_tarski @ X8 @ (k3_tarski @ X9)) | ~ (m1_setfam_1 @ X9 @ X8))),
% 0.21/0.46      inference('cnf', [status(esa)], [d12_setfam_1])).
% 0.21/0.46  thf('3', plain, ((r1_tarski @ (u1_struct_0 @ sk_A) @ (k3_tarski @ sk_B))),
% 0.21/0.46      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.46  thf(d10_xboole_0, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.46  thf('4', plain,
% 0.21/0.46      (![X0 : $i, X2 : $i]:
% 0.21/0.46         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.21/0.46      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.46  thf('5', plain,
% 0.21/0.46      ((~ (r1_tarski @ (k3_tarski @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.21/0.46        | ((k3_tarski @ sk_B) = (u1_struct_0 @ sk_A)))),
% 0.21/0.46      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.46  thf(t99_zfmisc_1, axiom,
% 0.21/0.46    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 0.21/0.46  thf('6', plain, (![X7 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X7)) = (X7))),
% 0.21/0.46      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 0.21/0.46  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.46  thf('7', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.21/0.46      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.46  thf('8', plain, (((sk_B) = (k1_xboole_0))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('9', plain, (![X3 : $i]: (r1_tarski @ sk_B @ X3)),
% 0.21/0.46      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.46  thf(t95_zfmisc_1, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( r1_tarski @ A @ B ) =>
% 0.21/0.46       ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ))).
% 0.21/0.46  thf('10', plain,
% 0.21/0.46      (![X5 : $i, X6 : $i]:
% 0.21/0.46         ((r1_tarski @ (k3_tarski @ X5) @ (k3_tarski @ X6))
% 0.21/0.46          | ~ (r1_tarski @ X5 @ X6))),
% 0.21/0.46      inference('cnf', [status(esa)], [t95_zfmisc_1])).
% 0.21/0.46  thf('11', plain,
% 0.21/0.46      (![X0 : $i]: (r1_tarski @ (k3_tarski @ sk_B) @ (k3_tarski @ X0))),
% 0.21/0.46      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.46  thf('12', plain, (![X0 : $i]: (r1_tarski @ (k3_tarski @ sk_B) @ X0)),
% 0.21/0.46      inference('sup+', [status(thm)], ['6', '11'])).
% 0.21/0.46  thf('13', plain, (((k3_tarski @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.21/0.46      inference('demod', [status(thm)], ['5', '12'])).
% 0.21/0.46  thf('14', plain, (![X0 : $i]: (r1_tarski @ (k3_tarski @ sk_B) @ X0)),
% 0.21/0.46      inference('sup+', [status(thm)], ['6', '11'])).
% 0.21/0.46  thf(t3_xboole_1, axiom,
% 0.21/0.46    (![A:$i]:
% 0.21/0.46     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.46  thf('15', plain,
% 0.21/0.46      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ k1_xboole_0))),
% 0.21/0.46      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.21/0.46  thf('16', plain, (((sk_B) = (k1_xboole_0))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('17', plain, (((sk_B) = (k1_xboole_0))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('18', plain, (![X4 : $i]: (((X4) = (sk_B)) | ~ (r1_tarski @ X4 @ sk_B))),
% 0.21/0.46      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.21/0.46  thf('19', plain, (((k3_tarski @ sk_B) = (sk_B))),
% 0.21/0.46      inference('sup-', [status(thm)], ['14', '18'])).
% 0.21/0.46  thf('20', plain, (((sk_B) = (u1_struct_0 @ sk_A))),
% 0.21/0.46      inference('demod', [status(thm)], ['13', '19'])).
% 0.21/0.46  thf(fc2_struct_0, axiom,
% 0.21/0.46    (![A:$i]:
% 0.21/0.46     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.46       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.46  thf('21', plain,
% 0.21/0.46      (![X11 : $i]:
% 0.21/0.46         (~ (v1_xboole_0 @ (u1_struct_0 @ X11))
% 0.21/0.46          | ~ (l1_struct_0 @ X11)
% 0.21/0.46          | (v2_struct_0 @ X11))),
% 0.21/0.46      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.21/0.46  thf('22', plain,
% 0.21/0.46      ((~ (v1_xboole_0 @ sk_B) | (v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.46      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.46  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.21/0.46  thf('23', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.46      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.46  thf('24', plain, (((sk_B) = (k1_xboole_0))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('25', plain, ((v1_xboole_0 @ sk_B)),
% 0.21/0.46      inference('demod', [status(thm)], ['23', '24'])).
% 0.21/0.46  thf('26', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('27', plain, ((v2_struct_0 @ sk_A)),
% 0.21/0.46      inference('demod', [status(thm)], ['22', '25', '26'])).
% 0.21/0.46  thf('28', plain, ($false), inference('demod', [status(thm)], ['0', '27'])).
% 0.21/0.46  
% 0.21/0.46  % SZS output end Refutation
% 0.21/0.46  
% 0.21/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
