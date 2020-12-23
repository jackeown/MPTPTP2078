%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OQA4Q8cssw

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:03 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   57 (  73 expanded)
%              Number of leaves         :   25 (  33 expanded)
%              Depth                    :   10
%              Number of atoms          :  230 ( 502 expanded)
%              Number of equality atoms :   23 (  39 expanded)
%              Maximal formula depth    :   14 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_setfam_1_type,type,(
    m1_setfam_1: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

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

thf(t9_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k4_tarski @ C @ D ) ) ) ) ) )).

thf('1',plain,(
    ! [X12: $i] :
      ( ( X12 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X12 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('2',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    ! [X12: $i] :
      ( ( X12 = sk_B_1 )
      | ( r2_hidden @ ( sk_B @ X12 ) @ X12 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,(
    m1_setfam_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_setfam_1 @ B @ A )
    <=> ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('5',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ ( k3_tarski @ X10 ) )
      | ~ ( m1_setfam_1 @ X10 @ X9 ) ) ),
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

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('14',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X6 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('15',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ sk_B_1 )
      = sk_B_1 ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('19',plain,(
    ! [X7: $i,X8: $i] :
      ~ ( r2_hidden @ X7 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('20',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['13','20'])).

thf('22',plain,
    ( ( u1_struct_0 @ sk_A )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['3','21'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('23',plain,(
    ! [X15: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X15 ) )
      | ~ ( l1_struct_0 @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('24',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('25',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('26',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['24','27','28'])).

thf('30',plain,(
    $false ),
    inference(demod,[status(thm)],['0','29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OQA4Q8cssw
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:32:16 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 28 iterations in 0.015s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.47  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.47  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.47  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.47  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.47  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.47  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.47  thf(m1_setfam_1_type, type, m1_setfam_1: $i > $i > $o).
% 0.21/0.47  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.21/0.47  thf(t5_tops_2, conjecture,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( m1_subset_1 @
% 0.21/0.47             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.47           ( ~( ( m1_setfam_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.47                ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i]:
% 0.21/0.47        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.47          ( ![B:$i]:
% 0.21/0.47            ( ( m1_subset_1 @
% 0.21/0.47                B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.47              ( ~( ( m1_setfam_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.47                   ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t5_tops_2])).
% 0.21/0.47  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(t9_mcart_1, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.47          ( ![B:$i]:
% 0.21/0.47            ( ~( ( r2_hidden @ B @ A ) & 
% 0.21/0.47                 ( ![C:$i,D:$i]:
% 0.21/0.47                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.21/0.47                        ( ( B ) = ( k4_tarski @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.47  thf('1', plain,
% 0.21/0.47      (![X12 : $i]:
% 0.21/0.47         (((X12) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X12) @ X12))),
% 0.21/0.47      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.21/0.47  thf('2', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('3', plain,
% 0.21/0.47      (![X12 : $i]: (((X12) = (sk_B_1)) | (r2_hidden @ (sk_B @ X12) @ X12))),
% 0.21/0.47      inference('demod', [status(thm)], ['1', '2'])).
% 0.21/0.47  thf('4', plain, ((m1_setfam_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(d12_setfam_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( m1_setfam_1 @ B @ A ) <=> ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.21/0.47  thf('5', plain,
% 0.21/0.47      (![X9 : $i, X10 : $i]:
% 0.21/0.47         ((r1_tarski @ X9 @ (k3_tarski @ X10)) | ~ (m1_setfam_1 @ X10 @ X9))),
% 0.21/0.47      inference('cnf', [status(esa)], [d12_setfam_1])).
% 0.21/0.47  thf('6', plain, ((r1_tarski @ (u1_struct_0 @ sk_A) @ (k3_tarski @ sk_B_1))),
% 0.21/0.47      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.47  thf(t2_zfmisc_1, axiom, (( k3_tarski @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.21/0.47  thf('7', plain, (((k3_tarski @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.47      inference('cnf', [status(esa)], [t2_zfmisc_1])).
% 0.21/0.47  thf('8', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('9', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('10', plain, (((k3_tarski @ sk_B_1) = (sk_B_1))),
% 0.21/0.47      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.21/0.47  thf('11', plain, ((r1_tarski @ (u1_struct_0 @ sk_A) @ sk_B_1)),
% 0.21/0.47      inference('demod', [status(thm)], ['6', '10'])).
% 0.21/0.47  thf(d3_tarski, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.47       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.47  thf('12', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.47         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.47          | (r2_hidden @ X0 @ X2)
% 0.21/0.47          | ~ (r1_tarski @ X1 @ X2))),
% 0.21/0.47      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.47  thf('13', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((r2_hidden @ X0 @ sk_B_1) | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.47  thf(t113_zfmisc_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.21/0.47       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.47  thf('14', plain,
% 0.21/0.47      (![X5 : $i, X6 : $i]:
% 0.21/0.47         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 0.21/0.47      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.21/0.47  thf('15', plain,
% 0.21/0.47      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.47      inference('simplify', [status(thm)], ['14'])).
% 0.21/0.47  thf('16', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('17', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('18', plain, (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ sk_B_1) = (sk_B_1))),
% 0.21/0.47      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.21/0.47  thf(t152_zfmisc_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.21/0.47  thf('19', plain,
% 0.21/0.47      (![X7 : $i, X8 : $i]: ~ (r2_hidden @ X7 @ (k2_zfmisc_1 @ X7 @ X8))),
% 0.21/0.47      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.21/0.47  thf('20', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_B_1)),
% 0.21/0.47      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.47  thf('21', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))),
% 0.21/0.47      inference('clc', [status(thm)], ['13', '20'])).
% 0.21/0.47  thf('22', plain, (((u1_struct_0 @ sk_A) = (sk_B_1))),
% 0.21/0.47      inference('sup-', [status(thm)], ['3', '21'])).
% 0.21/0.47  thf(fc2_struct_0, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.47       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.47  thf('23', plain,
% 0.21/0.47      (![X15 : $i]:
% 0.21/0.47         (~ (v1_xboole_0 @ (u1_struct_0 @ X15))
% 0.21/0.47          | ~ (l1_struct_0 @ X15)
% 0.21/0.47          | (v2_struct_0 @ X15))),
% 0.21/0.47      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.21/0.47  thf('24', plain,
% 0.21/0.47      ((~ (v1_xboole_0 @ sk_B_1)
% 0.21/0.47        | (v2_struct_0 @ sk_A)
% 0.21/0.47        | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.47  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.21/0.47  thf('25', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.47      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.47  thf('26', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('27', plain, ((v1_xboole_0 @ sk_B_1)),
% 0.21/0.47      inference('demod', [status(thm)], ['25', '26'])).
% 0.21/0.47  thf('28', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('29', plain, ((v2_struct_0 @ sk_A)),
% 0.21/0.47      inference('demod', [status(thm)], ['24', '27', '28'])).
% 0.21/0.47  thf('30', plain, ($false), inference('demod', [status(thm)], ['0', '29'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
