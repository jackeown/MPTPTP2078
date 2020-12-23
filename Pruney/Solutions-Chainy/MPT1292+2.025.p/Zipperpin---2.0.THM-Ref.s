%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2VYQ5gi3AW

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:04 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   53 (  67 expanded)
%              Number of leaves         :   23 (  30 expanded)
%              Depth                    :   11
%              Number of atoms          :  209 ( 447 expanded)
%              Number of equality atoms :   16 (  30 expanded)
%              Maximal formula depth    :   10 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(m1_setfam_1_type,type,(
    m1_setfam_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

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

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('2',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    ! [X4: $i] :
      ( ( X4 = sk_B_1 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,(
    m1_setfam_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_setfam_1 @ B @ A )
    <=> ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('5',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ ( k3_tarski @ X7 ) )
      | ~ ( m1_setfam_1 @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d12_setfam_1])).

thf('6',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( k3_tarski @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t2_zfmisc_1,axiom,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('7',plain,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t2_zfmisc_1])).

thf('8',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( k3_tarski @ sk_B_1 )
    = sk_B_1 ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('11',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ),
    inference(demod,[status(thm)],['6','10'])).

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
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_1 )
    | ( r2_hidden @ ( sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['3','13'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('15',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( r1_tarski @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('16',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_1 )
    | ~ ( r1_tarski @ sk_B_1 @ ( sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('17',plain,(
    ! [X5: $i] :
      ( r1_tarski @ k1_xboole_0 @ X5 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('18',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X5: $i] :
      ( r1_tarski @ sk_B_1 @ X5 ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( u1_struct_0 @ sk_A )
    = sk_B_1 ),
    inference(demod,[status(thm)],['16','19'])).

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
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('23',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('24',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_xboole_0 @ sk_B_1 ),
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
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2VYQ5gi3AW
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:53:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 22 iterations in 0.013s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.51  thf(m1_setfam_1_type, type, m1_setfam_1: $i > $i > $o).
% 0.21/0.51  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.51  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.51  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.51  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.21/0.51  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.51  thf(t5_tops_2, conjecture,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( m1_subset_1 @
% 0.21/0.51             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.51           ( ~( ( m1_setfam_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.51                ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.21/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.51    (~( ![A:$i]:
% 0.21/0.51        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.51          ( ![B:$i]:
% 0.21/0.51            ( ( m1_subset_1 @
% 0.21/0.51                B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.51              ( ~( ( m1_setfam_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.51                   ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ) ) )),
% 0.21/0.51    inference('cnf.neg', [status(esa)], [t5_tops_2])).
% 0.21/0.51  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(t7_xboole_0, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.51          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.21/0.51  thf('1', plain,
% 0.21/0.51      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.21/0.51      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.21/0.51  thf('2', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('3', plain,
% 0.21/0.51      (![X4 : $i]: (((X4) = (sk_B_1)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.21/0.51      inference('demod', [status(thm)], ['1', '2'])).
% 0.21/0.51  thf('4', plain, ((m1_setfam_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(d12_setfam_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( m1_setfam_1 @ B @ A ) <=> ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.21/0.51  thf('5', plain,
% 0.21/0.51      (![X6 : $i, X7 : $i]:
% 0.21/0.51         ((r1_tarski @ X6 @ (k3_tarski @ X7)) | ~ (m1_setfam_1 @ X7 @ X6))),
% 0.21/0.51      inference('cnf', [status(esa)], [d12_setfam_1])).
% 0.21/0.51  thf('6', plain, ((r1_tarski @ (u1_struct_0 @ sk_A) @ (k3_tarski @ sk_B_1))),
% 0.21/0.51      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.51  thf(t2_zfmisc_1, axiom, (( k3_tarski @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.21/0.51  thf('7', plain, (((k3_tarski @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.51      inference('cnf', [status(esa)], [t2_zfmisc_1])).
% 0.21/0.51  thf('8', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('9', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('10', plain, (((k3_tarski @ sk_B_1) = (sk_B_1))),
% 0.21/0.51      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.21/0.51  thf('11', plain, ((r1_tarski @ (u1_struct_0 @ sk_A) @ sk_B_1)),
% 0.21/0.51      inference('demod', [status(thm)], ['6', '10'])).
% 0.21/0.51  thf(d3_tarski, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.51       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.51  thf('12', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.51          | (r2_hidden @ X0 @ X2)
% 0.21/0.51          | ~ (r1_tarski @ X1 @ X2))),
% 0.21/0.51      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.51  thf('13', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((r2_hidden @ X0 @ sk_B_1) | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.51  thf('14', plain,
% 0.21/0.51      ((((u1_struct_0 @ sk_A) = (sk_B_1))
% 0.21/0.51        | (r2_hidden @ (sk_B @ (u1_struct_0 @ sk_A)) @ sk_B_1))),
% 0.21/0.51      inference('sup-', [status(thm)], ['3', '13'])).
% 0.21/0.51  thf(t7_ordinal1, axiom,
% 0.21/0.51    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.51  thf('15', plain,
% 0.21/0.51      (![X9 : $i, X10 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X9 @ X10) | ~ (r1_tarski @ X10 @ X9))),
% 0.21/0.51      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.21/0.51  thf('16', plain,
% 0.21/0.51      ((((u1_struct_0 @ sk_A) = (sk_B_1))
% 0.21/0.51        | ~ (r1_tarski @ sk_B_1 @ (sk_B @ (u1_struct_0 @ sk_A))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.51  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.51  thf('17', plain, (![X5 : $i]: (r1_tarski @ k1_xboole_0 @ X5)),
% 0.21/0.51      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.51  thf('18', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('19', plain, (![X5 : $i]: (r1_tarski @ sk_B_1 @ X5)),
% 0.21/0.51      inference('demod', [status(thm)], ['17', '18'])).
% 0.21/0.51  thf('20', plain, (((u1_struct_0 @ sk_A) = (sk_B_1))),
% 0.21/0.51      inference('demod', [status(thm)], ['16', '19'])).
% 0.21/0.51  thf(fc2_struct_0, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.51       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.51  thf('21', plain,
% 0.21/0.51      (![X11 : $i]:
% 0.21/0.51         (~ (v1_xboole_0 @ (u1_struct_0 @ X11))
% 0.21/0.51          | ~ (l1_struct_0 @ X11)
% 0.21/0.51          | (v2_struct_0 @ X11))),
% 0.21/0.51      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.21/0.51  thf('22', plain,
% 0.21/0.51      ((~ (v1_xboole_0 @ sk_B_1)
% 0.21/0.51        | (v2_struct_0 @ sk_A)
% 0.21/0.51        | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.51  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.21/0.51  thf('23', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.51      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.51  thf('24', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('25', plain, ((v1_xboole_0 @ sk_B_1)),
% 0.21/0.51      inference('demod', [status(thm)], ['23', '24'])).
% 0.21/0.51  thf('26', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('27', plain, ((v2_struct_0 @ sk_A)),
% 0.21/0.51      inference('demod', [status(thm)], ['22', '25', '26'])).
% 0.21/0.51  thf('28', plain, ($false), inference('demod', [status(thm)], ['0', '27'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.21/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
