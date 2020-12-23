%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WBMfrP0s8A

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:29 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   48 (  57 expanded)
%              Number of leaves         :   19 (  25 expanded)
%              Depth                    :   13
%              Number of atoms          :  289 ( 413 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t31_tops_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) )
             => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_pre_topc @ B @ A )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) )
               => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t31_tops_2])).

thf('0',plain,(
    ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r2_hidden @ X6 @ X7 )
      | ( v1_xboole_0 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('3',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( r2_hidden @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('4',plain,(
    ! [X5: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('5',plain,(
    r2_hidden @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['3','4'])).

thf('6',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('8',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['7'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('9',plain,(
    ! [X8: $i,X10: $i] :
      ( ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('10',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t39_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
             => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('11',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_pre_topc @ X14 @ X15 )
      | ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t39_pre_topc])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X1 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['6','12'])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('17',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t79_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('18',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ ( k1_zfmisc_1 @ X3 ) @ ( k1_zfmisc_1 @ X4 ) )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t79_zfmisc_1])).

thf('19',plain,(
    r1_tarski @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ ( k1_zfmisc_1 @ X3 ) @ ( k1_zfmisc_1 @ X4 ) )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t79_zfmisc_1])).

thf('21',plain,(
    r1_tarski @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X8: $i,X10: $i] :
      ( ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('23',plain,(
    m1_subset_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('24',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ( m1_subset_1 @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['5','25'])).

thf('27',plain,(
    $false ),
    inference(demod,[status(thm)],['0','26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WBMfrP0s8A
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:58:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 72 iterations in 0.033s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.21/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.49  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.49  thf(t31_tops_2, conjecture,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( l1_pre_topc @ A ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.49           ( ![C:$i]:
% 0.21/0.49             ( ( m1_subset_1 @
% 0.21/0.49                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) =>
% 0.21/0.49               ( m1_subset_1 @
% 0.21/0.49                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i]:
% 0.21/0.49        ( ( l1_pre_topc @ A ) =>
% 0.21/0.49          ( ![B:$i]:
% 0.21/0.49            ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.49              ( ![C:$i]:
% 0.21/0.49                ( ( m1_subset_1 @
% 0.21/0.49                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) =>
% 0.21/0.49                  ( m1_subset_1 @
% 0.21/0.49                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t31_tops_2])).
% 0.21/0.49  thf('0', plain,
% 0.21/0.49      (~ (m1_subset_1 @ sk_C @ 
% 0.21/0.49          (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('1', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_C @ 
% 0.21/0.49        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(t2_subset, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( m1_subset_1 @ A @ B ) =>
% 0.21/0.49       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.21/0.49  thf('2', plain,
% 0.21/0.49      (![X6 : $i, X7 : $i]:
% 0.21/0.49         ((r2_hidden @ X6 @ X7)
% 0.21/0.49          | (v1_xboole_0 @ X7)
% 0.21/0.49          | ~ (m1_subset_1 @ X6 @ X7))),
% 0.21/0.49      inference('cnf', [status(esa)], [t2_subset])).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      (((v1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))
% 0.21/0.49        | (r2_hidden @ sk_C @ 
% 0.21/0.49           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.49  thf(fc1_subset_1, axiom,
% 0.21/0.49    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.21/0.49  thf('4', plain, (![X5 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X5))),
% 0.21/0.49      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.21/0.49  thf('5', plain,
% 0.21/0.49      ((r2_hidden @ sk_C @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.21/0.49      inference('clc', [status(thm)], ['3', '4'])).
% 0.21/0.49  thf('6', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(d10_xboole_0, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.49  thf('7', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.21/0.49      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.49  thf('8', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.21/0.49      inference('simplify', [status(thm)], ['7'])).
% 0.21/0.49  thf(t3_subset, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.49  thf('9', plain,
% 0.21/0.49      (![X8 : $i, X10 : $i]:
% 0.21/0.49         ((m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X10)) | ~ (r1_tarski @ X8 @ X10))),
% 0.21/0.49      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.49  thf('10', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.49  thf(t39_pre_topc, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( l1_pre_topc @ A ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.49           ( ![C:$i]:
% 0.21/0.49             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.21/0.49               ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ))).
% 0.21/0.49  thf('11', plain,
% 0.21/0.49      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.49         (~ (m1_pre_topc @ X14 @ X15)
% 0.21/0.49          | (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.21/0.49          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.21/0.49          | ~ (l1_pre_topc @ X15))),
% 0.21/0.49      inference('cnf', [status(esa)], [t39_pre_topc])).
% 0.21/0.49  thf('12', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (~ (l1_pre_topc @ X1)
% 0.21/0.49          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.21/0.49             (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.21/0.49          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.21/0.49      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.49  thf('13', plain,
% 0.21/0.49      (((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.49         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.49        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['6', '12'])).
% 0.21/0.49  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('15', plain,
% 0.21/0.49      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.49        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.49      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.49  thf('16', plain,
% 0.21/0.49      (![X8 : $i, X9 : $i]:
% 0.21/0.49         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.49  thf('17', plain, ((r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.49  thf(t79_zfmisc_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( r1_tarski @ A @ B ) =>
% 0.21/0.49       ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.21/0.49  thf('18', plain,
% 0.21/0.49      (![X3 : $i, X4 : $i]:
% 0.21/0.49         ((r1_tarski @ (k1_zfmisc_1 @ X3) @ (k1_zfmisc_1 @ X4))
% 0.21/0.49          | ~ (r1_tarski @ X3 @ X4))),
% 0.21/0.49      inference('cnf', [status(esa)], [t79_zfmisc_1])).
% 0.21/0.49  thf('19', plain,
% 0.21/0.49      ((r1_tarski @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)) @ 
% 0.21/0.49        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.49  thf('20', plain,
% 0.21/0.49      (![X3 : $i, X4 : $i]:
% 0.21/0.49         ((r1_tarski @ (k1_zfmisc_1 @ X3) @ (k1_zfmisc_1 @ X4))
% 0.21/0.49          | ~ (r1_tarski @ X3 @ X4))),
% 0.21/0.49      inference('cnf', [status(esa)], [t79_zfmisc_1])).
% 0.21/0.49  thf('21', plain,
% 0.21/0.49      ((r1_tarski @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))) @ 
% 0.21/0.49        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.49  thf('22', plain,
% 0.21/0.49      (![X8 : $i, X10 : $i]:
% 0.21/0.49         ((m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X10)) | ~ (r1_tarski @ X8 @ X10))),
% 0.21/0.49      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.49  thf('23', plain,
% 0.21/0.49      ((m1_subset_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))) @ 
% 0.21/0.49        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.49  thf(t4_subset, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.21/0.49       ( m1_subset_1 @ A @ C ) ))).
% 0.21/0.49  thf('24', plain,
% 0.21/0.49      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X11 @ X12)
% 0.21/0.49          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 0.21/0.49          | (m1_subset_1 @ X11 @ X13))),
% 0.21/0.49      inference('cnf', [status(esa)], [t4_subset])).
% 0.21/0.49  thf('25', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((m1_subset_1 @ X0 @ 
% 0.21/0.49           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.21/0.49          | ~ (r2_hidden @ X0 @ 
% 0.21/0.49               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.49  thf('26', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_C @ 
% 0.21/0.49        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['5', '25'])).
% 0.21/0.49  thf('27', plain, ($false), inference('demod', [status(thm)], ['0', '26'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
