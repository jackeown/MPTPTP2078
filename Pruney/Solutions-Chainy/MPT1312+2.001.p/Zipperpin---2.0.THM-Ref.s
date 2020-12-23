%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.44KWICqkmI

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:29 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   50 (  57 expanded)
%              Number of leaves         :   23 (  27 expanded)
%              Depth                    :   13
%              Number of atoms          :  300 ( 411 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

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
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('3',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('4',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ( m1_subset_1 @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_1 @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf(t39_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
             => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('7',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_pre_topc @ X19 @ X20 )
      | ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t39_pre_topc])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_C_1 @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ sk_B @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_C @ X0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r1_tarski @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_C @ X0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ sk_C_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('12',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r2_hidden @ X10 @ X11 )
      | ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_1 @ X0 )
      | ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t61_setfam_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('14',plain,(
    ! [X18: $i] :
      ( m1_subset_1 @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t61_setfam_1])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('15',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ( v1_xboole_0 @ X8 )
      | ~ ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ ( k1_tarski @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(fc2_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ A ) ) )).

thf('17',plain,(
    ! [X7: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('18',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ sk_C_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['13','18'])).

thf('20',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('21',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( r1_tarski @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    r1_tarski @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('23',plain,(
    ! [X12: $i,X14: $i] :
      ( ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('24',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    $false ),
    inference(demod,[status(thm)],['0','24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.15/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.44KWICqkmI
% 0.16/0.37  % Computer   : n013.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 14:16:40 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.38  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 0.23/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.51  % Solved by: fo/fo7.sh
% 0.23/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.51  % done 104 iterations in 0.050s
% 0.23/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.51  % SZS output start Refutation
% 0.23/0.51  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.23/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.23/0.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.23/0.51  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.23/0.51  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.23/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.23/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.23/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.23/0.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.23/0.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.23/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.23/0.51  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.23/0.51  thf(t31_tops_2, conjecture,
% 0.23/0.51    (![A:$i]:
% 0.23/0.51     ( ( l1_pre_topc @ A ) =>
% 0.23/0.51       ( ![B:$i]:
% 0.23/0.51         ( ( m1_pre_topc @ B @ A ) =>
% 0.23/0.51           ( ![C:$i]:
% 0.23/0.51             ( ( m1_subset_1 @
% 0.23/0.51                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) =>
% 0.23/0.51               ( m1_subset_1 @
% 0.23/0.51                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.23/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.51    (~( ![A:$i]:
% 0.23/0.51        ( ( l1_pre_topc @ A ) =>
% 0.23/0.51          ( ![B:$i]:
% 0.23/0.51            ( ( m1_pre_topc @ B @ A ) =>
% 0.23/0.51              ( ![C:$i]:
% 0.23/0.51                ( ( m1_subset_1 @
% 0.23/0.51                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) =>
% 0.23/0.51                  ( m1_subset_1 @
% 0.23/0.51                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 0.23/0.51    inference('cnf.neg', [status(esa)], [t31_tops_2])).
% 0.23/0.51  thf('0', plain,
% 0.23/0.51      (~ (m1_subset_1 @ sk_C_1 @ 
% 0.23/0.51          (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('1', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf(d3_tarski, axiom,
% 0.23/0.51    (![A:$i,B:$i]:
% 0.23/0.51     ( ( r1_tarski @ A @ B ) <=>
% 0.23/0.51       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.23/0.51  thf('2', plain,
% 0.23/0.51      (![X1 : $i, X3 : $i]:
% 0.23/0.51         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.23/0.51      inference('cnf', [status(esa)], [d3_tarski])).
% 0.23/0.51  thf('3', plain,
% 0.23/0.51      ((m1_subset_1 @ sk_C_1 @ 
% 0.23/0.51        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf(t4_subset, axiom,
% 0.23/0.51    (![A:$i,B:$i,C:$i]:
% 0.23/0.51     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.23/0.51       ( m1_subset_1 @ A @ C ) ))).
% 0.23/0.51  thf('4', plain,
% 0.23/0.51      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.23/0.51         (~ (r2_hidden @ X15 @ X16)
% 0.23/0.51          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 0.23/0.51          | (m1_subset_1 @ X15 @ X17))),
% 0.23/0.51      inference('cnf', [status(esa)], [t4_subset])).
% 0.23/0.51  thf('5', plain,
% 0.23/0.51      (![X0 : $i]:
% 0.23/0.51         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.23/0.51          | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.23/0.51      inference('sup-', [status(thm)], ['3', '4'])).
% 0.23/0.51  thf('6', plain,
% 0.23/0.51      (![X0 : $i]:
% 0.23/0.51         ((r1_tarski @ sk_C_1 @ X0)
% 0.23/0.51          | (m1_subset_1 @ (sk_C @ X0 @ sk_C_1) @ 
% 0.23/0.51             (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.23/0.51      inference('sup-', [status(thm)], ['2', '5'])).
% 0.23/0.51  thf(t39_pre_topc, axiom,
% 0.23/0.51    (![A:$i]:
% 0.23/0.51     ( ( l1_pre_topc @ A ) =>
% 0.23/0.51       ( ![B:$i]:
% 0.23/0.51         ( ( m1_pre_topc @ B @ A ) =>
% 0.23/0.51           ( ![C:$i]:
% 0.23/0.51             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.23/0.51               ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ))).
% 0.23/0.51  thf('7', plain,
% 0.23/0.51      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.23/0.51         (~ (m1_pre_topc @ X19 @ X20)
% 0.23/0.51          | (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.23/0.51          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.23/0.51          | ~ (l1_pre_topc @ X20))),
% 0.23/0.51      inference('cnf', [status(esa)], [t39_pre_topc])).
% 0.23/0.51  thf('8', plain,
% 0.23/0.51      (![X0 : $i, X1 : $i]:
% 0.23/0.51         ((r1_tarski @ sk_C_1 @ X0)
% 0.23/0.51          | ~ (l1_pre_topc @ X1)
% 0.23/0.51          | (m1_subset_1 @ (sk_C @ X0 @ sk_C_1) @ 
% 0.23/0.51             (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.23/0.51          | ~ (m1_pre_topc @ sk_B @ X1))),
% 0.23/0.51      inference('sup-', [status(thm)], ['6', '7'])).
% 0.23/0.51  thf('9', plain,
% 0.23/0.51      (![X0 : $i]:
% 0.23/0.51         ((m1_subset_1 @ (sk_C @ X0 @ sk_C_1) @ 
% 0.23/0.51           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.23/0.51          | ~ (l1_pre_topc @ sk_A)
% 0.23/0.51          | (r1_tarski @ sk_C_1 @ X0))),
% 0.23/0.51      inference('sup-', [status(thm)], ['1', '8'])).
% 0.23/0.51  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('11', plain,
% 0.23/0.51      (![X0 : $i]:
% 0.23/0.51         ((m1_subset_1 @ (sk_C @ X0 @ sk_C_1) @ 
% 0.23/0.51           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.23/0.51          | (r1_tarski @ sk_C_1 @ X0))),
% 0.23/0.51      inference('demod', [status(thm)], ['9', '10'])).
% 0.23/0.51  thf(t2_subset, axiom,
% 0.23/0.51    (![A:$i,B:$i]:
% 0.23/0.51     ( ( m1_subset_1 @ A @ B ) =>
% 0.23/0.51       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.23/0.51  thf('12', plain,
% 0.23/0.51      (![X10 : $i, X11 : $i]:
% 0.23/0.51         ((r2_hidden @ X10 @ X11)
% 0.23/0.51          | (v1_xboole_0 @ X11)
% 0.23/0.51          | ~ (m1_subset_1 @ X10 @ X11))),
% 0.23/0.51      inference('cnf', [status(esa)], [t2_subset])).
% 0.23/0.51  thf('13', plain,
% 0.23/0.51      (![X0 : $i]:
% 0.23/0.51         ((r1_tarski @ sk_C_1 @ X0)
% 0.23/0.51          | (v1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.23/0.51          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ 
% 0.23/0.51             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.23/0.51      inference('sup-', [status(thm)], ['11', '12'])).
% 0.23/0.51  thf(t61_setfam_1, axiom,
% 0.23/0.51    (![A:$i]:
% 0.23/0.51     ( m1_subset_1 @
% 0.23/0.51       ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.23/0.51  thf('14', plain,
% 0.23/0.51      (![X18 : $i]:
% 0.23/0.51         (m1_subset_1 @ (k1_tarski @ k1_xboole_0) @ 
% 0.23/0.51          (k1_zfmisc_1 @ (k1_zfmisc_1 @ X18)))),
% 0.23/0.51      inference('cnf', [status(esa)], [t61_setfam_1])).
% 0.23/0.51  thf(cc1_subset_1, axiom,
% 0.23/0.51    (![A:$i]:
% 0.23/0.51     ( ( v1_xboole_0 @ A ) =>
% 0.23/0.51       ( ![B:$i]:
% 0.23/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.23/0.51  thf('15', plain,
% 0.23/0.51      (![X8 : $i, X9 : $i]:
% 0.23/0.51         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 0.23/0.51          | (v1_xboole_0 @ X8)
% 0.23/0.51          | ~ (v1_xboole_0 @ X9))),
% 0.23/0.51      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.23/0.51  thf('16', plain,
% 0.23/0.51      (![X0 : $i]:
% 0.23/0.51         (~ (v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 0.23/0.51          | (v1_xboole_0 @ (k1_tarski @ k1_xboole_0)))),
% 0.23/0.51      inference('sup-', [status(thm)], ['14', '15'])).
% 0.23/0.51  thf(fc2_xboole_0, axiom, (![A:$i]: ( ~( v1_xboole_0 @ ( k1_tarski @ A ) ) ))).
% 0.23/0.51  thf('17', plain, (![X7 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X7))),
% 0.23/0.51      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 0.23/0.51  thf('18', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.23/0.51      inference('clc', [status(thm)], ['16', '17'])).
% 0.23/0.51  thf('19', plain,
% 0.23/0.51      (![X0 : $i]:
% 0.23/0.51         ((r2_hidden @ (sk_C @ X0 @ sk_C_1) @ 
% 0.23/0.51           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.23/0.51          | (r1_tarski @ sk_C_1 @ X0))),
% 0.23/0.51      inference('clc', [status(thm)], ['13', '18'])).
% 0.23/0.51  thf('20', plain,
% 0.23/0.51      (![X1 : $i, X3 : $i]:
% 0.23/0.51         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.23/0.51      inference('cnf', [status(esa)], [d3_tarski])).
% 0.23/0.51  thf('21', plain,
% 0.23/0.51      (((r1_tarski @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.23/0.51        | (r1_tarski @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.23/0.51      inference('sup-', [status(thm)], ['19', '20'])).
% 0.23/0.51  thf('22', plain,
% 0.23/0.51      ((r1_tarski @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.51      inference('simplify', [status(thm)], ['21'])).
% 0.23/0.51  thf(t3_subset, axiom,
% 0.23/0.51    (![A:$i,B:$i]:
% 0.23/0.51     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.23/0.51  thf('23', plain,
% 0.23/0.51      (![X12 : $i, X14 : $i]:
% 0.23/0.51         ((m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X14)) | ~ (r1_tarski @ X12 @ X14))),
% 0.23/0.51      inference('cnf', [status(esa)], [t3_subset])).
% 0.23/0.51  thf('24', plain,
% 0.23/0.51      ((m1_subset_1 @ sk_C_1 @ 
% 0.23/0.51        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.23/0.51      inference('sup-', [status(thm)], ['22', '23'])).
% 0.23/0.51  thf('25', plain, ($false), inference('demod', [status(thm)], ['0', '24'])).
% 0.23/0.51  
% 0.23/0.51  % SZS output end Refutation
% 0.23/0.51  
% 0.23/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
