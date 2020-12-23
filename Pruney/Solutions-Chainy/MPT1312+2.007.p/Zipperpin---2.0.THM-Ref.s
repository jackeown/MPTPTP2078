%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.S5Baq1THxp

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:30 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   48 (  57 expanded)
%              Number of leaves         :   19 (  25 expanded)
%              Depth                    :   12
%              Number of atoms          :  288 ( 412 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('3',plain,(
    r1_tarski @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('8',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X8 ) @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('9',plain,(
    ! [X7: $i] :
      ( ( k2_subset_1 @ X7 )
      = X7 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('10',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(t39_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
             => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('11',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X15 @ X16 )
      | ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
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
    inference('sup-',[status(thm)],['7','12'])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('17',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t79_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('18',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ ( k1_zfmisc_1 @ X5 ) @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t79_zfmisc_1])).

thf('19',plain,(
    r1_tarski @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ ( k1_zfmisc_1 @ X5 ) @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t79_zfmisc_1])).

thf('21',plain,(
    r1_tarski @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X9: $i,X11: $i] :
      ( ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
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
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ( m1_subset_1 @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['6','25'])).

thf('27',plain,(
    $false ),
    inference(demod,[status(thm)],['0','26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.S5Baq1THxp
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:15:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.21/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.52  % Solved by: fo/fo7.sh
% 0.21/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.52  % done 114 iterations in 0.063s
% 0.21/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.52  % SZS output start Refutation
% 0.21/0.52  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.21/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.52  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.52  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.21/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.52  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.52  thf(t31_tops_2, conjecture,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( l1_pre_topc @ A ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.52           ( ![C:$i]:
% 0.21/0.52             ( ( m1_subset_1 @
% 0.21/0.52                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) =>
% 0.21/0.52               ( m1_subset_1 @
% 0.21/0.52                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.21/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.52    (~( ![A:$i]:
% 0.21/0.52        ( ( l1_pre_topc @ A ) =>
% 0.21/0.52          ( ![B:$i]:
% 0.21/0.52            ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.52              ( ![C:$i]:
% 0.21/0.52                ( ( m1_subset_1 @
% 0.21/0.52                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) =>
% 0.21/0.52                  ( m1_subset_1 @
% 0.21/0.52                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 0.21/0.52    inference('cnf.neg', [status(esa)], [t31_tops_2])).
% 0.21/0.52  thf('0', plain,
% 0.21/0.52      (~ (m1_subset_1 @ sk_C_1 @ 
% 0.21/0.52          (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('1', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_C_1 @ 
% 0.21/0.52        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(t3_subset, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.52  thf('2', plain,
% 0.21/0.52      (![X9 : $i, X10 : $i]:
% 0.21/0.52         ((r1_tarski @ X9 @ X10) | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.52  thf('3', plain,
% 0.21/0.52      ((r1_tarski @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.52  thf(d1_zfmisc_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.21/0.52       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.21/0.52  thf('4', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         (~ (r1_tarski @ X0 @ X1)
% 0.21/0.52          | (r2_hidden @ X0 @ X2)
% 0.21/0.52          | ((X2) != (k1_zfmisc_1 @ X1)))),
% 0.21/0.52      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.21/0.52  thf('5', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((r2_hidden @ X0 @ (k1_zfmisc_1 @ X1)) | ~ (r1_tarski @ X0 @ X1))),
% 0.21/0.52      inference('simplify', [status(thm)], ['4'])).
% 0.21/0.52  thf('6', plain,
% 0.21/0.52      ((r2_hidden @ sk_C_1 @ 
% 0.21/0.52        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['3', '5'])).
% 0.21/0.52  thf('7', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(dt_k2_subset_1, axiom,
% 0.21/0.52    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.21/0.52  thf('8', plain,
% 0.21/0.52      (![X8 : $i]: (m1_subset_1 @ (k2_subset_1 @ X8) @ (k1_zfmisc_1 @ X8))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.21/0.52  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.21/0.52  thf('9', plain, (![X7 : $i]: ((k2_subset_1 @ X7) = (X7))),
% 0.21/0.52      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.21/0.52  thf('10', plain, (![X8 : $i]: (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X8))),
% 0.21/0.52      inference('demod', [status(thm)], ['8', '9'])).
% 0.21/0.52  thf(t39_pre_topc, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( l1_pre_topc @ A ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.52           ( ![C:$i]:
% 0.21/0.52             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.21/0.52               ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ))).
% 0.21/0.52  thf('11', plain,
% 0.21/0.52      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.52         (~ (m1_pre_topc @ X15 @ X16)
% 0.21/0.52          | (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.21/0.52          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.21/0.52          | ~ (l1_pre_topc @ X16))),
% 0.21/0.52      inference('cnf', [status(esa)], [t39_pre_topc])).
% 0.21/0.52  thf('12', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (~ (l1_pre_topc @ X1)
% 0.21/0.52          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.21/0.52             (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.21/0.52          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.21/0.52      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.52  thf('13', plain,
% 0.21/0.52      (((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.52         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.52        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['7', '12'])).
% 0.21/0.52  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('15', plain,
% 0.21/0.52      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.52        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.52  thf('16', plain,
% 0.21/0.52      (![X9 : $i, X10 : $i]:
% 0.21/0.52         ((r1_tarski @ X9 @ X10) | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.52  thf('17', plain, ((r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.52  thf(t79_zfmisc_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( r1_tarski @ A @ B ) =>
% 0.21/0.52       ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.21/0.52  thf('18', plain,
% 0.21/0.52      (![X5 : $i, X6 : $i]:
% 0.21/0.52         ((r1_tarski @ (k1_zfmisc_1 @ X5) @ (k1_zfmisc_1 @ X6))
% 0.21/0.52          | ~ (r1_tarski @ X5 @ X6))),
% 0.21/0.52      inference('cnf', [status(esa)], [t79_zfmisc_1])).
% 0.21/0.52  thf('19', plain,
% 0.21/0.52      ((r1_tarski @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)) @ 
% 0.21/0.52        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.52  thf('20', plain,
% 0.21/0.52      (![X5 : $i, X6 : $i]:
% 0.21/0.52         ((r1_tarski @ (k1_zfmisc_1 @ X5) @ (k1_zfmisc_1 @ X6))
% 0.21/0.52          | ~ (r1_tarski @ X5 @ X6))),
% 0.21/0.52      inference('cnf', [status(esa)], [t79_zfmisc_1])).
% 0.21/0.52  thf('21', plain,
% 0.21/0.52      ((r1_tarski @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))) @ 
% 0.21/0.52        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.52  thf('22', plain,
% 0.21/0.52      (![X9 : $i, X11 : $i]:
% 0.21/0.52         ((m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X11)) | ~ (r1_tarski @ X9 @ X11))),
% 0.21/0.52      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.52  thf('23', plain,
% 0.21/0.52      ((m1_subset_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))) @ 
% 0.21/0.52        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.52  thf(t4_subset, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.21/0.52       ( m1_subset_1 @ A @ C ) ))).
% 0.21/0.52  thf('24', plain,
% 0.21/0.52      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X12 @ X13)
% 0.21/0.52          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 0.21/0.52          | (m1_subset_1 @ X12 @ X14))),
% 0.21/0.52      inference('cnf', [status(esa)], [t4_subset])).
% 0.21/0.52  thf('25', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((m1_subset_1 @ X0 @ 
% 0.21/0.52           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.21/0.52          | ~ (r2_hidden @ X0 @ 
% 0.21/0.52               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.52  thf('26', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_C_1 @ 
% 0.21/0.52        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['6', '25'])).
% 0.21/0.52  thf('27', plain, ($false), inference('demod', [status(thm)], ['0', '26'])).
% 0.21/0.52  
% 0.21/0.52  % SZS output end Refutation
% 0.21/0.52  
% 0.21/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
