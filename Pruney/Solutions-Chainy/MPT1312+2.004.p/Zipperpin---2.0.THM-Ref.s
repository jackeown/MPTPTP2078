%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RM4s0aBXyT

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:29 EST 2020

% Result     : Theorem 3.96s
% Output     : Refutation 3.96s
% Verified   : 
% Statistics : Number of formulae       :   60 (  67 expanded)
%              Number of leaves         :   28 (  32 expanded)
%              Depth                    :   13
%              Number of atoms          :  351 ( 462 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('3',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('4',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) )
      | ( m1_subset_1 @ X20 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_1 @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) ) ) ),
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
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_pre_topc @ X23 @ X24 )
      | ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t39_pre_topc])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_C_1 @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ sk_B_1 @ X1 ) ) ),
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
    ! [X15: $i,X16: $i] :
      ( ( r2_hidden @ X15 @ X16 )
      | ( v1_xboole_0 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_1 @ X0 )
      | ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t100_zfmisc_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ A @ ( k1_zfmisc_1 @ ( k3_tarski @ A ) ) ) )).

thf('14',plain,(
    ! [X14: $i] :
      ( r1_tarski @ X14 @ ( k1_zfmisc_1 @ ( k3_tarski @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t100_zfmisc_1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('15',plain,(
    ! [X8: $i] :
      ( ( k2_tarski @ X8 @ X8 )
      = ( k1_tarski @ X8 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('16',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r2_hidden @ X9 @ X10 )
      | ~ ( r1_tarski @ ( k1_tarski @ X9 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_tarski @ X0 @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ ( k3_tarski @ ( k2_tarski @ X0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('19',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X12 @ X13 ) )
      = ( k2_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('20',plain,(
    ! [X7: $i] :
      ( ( k2_xboole_0 @ X7 @ X7 )
      = X7 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('23',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ sk_C_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['13','23'])).

thf('25',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('26',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( r1_tarski @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    r1_tarski @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('28',plain,(
    ! [X17: $i,X19: $i] :
      ( ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X19 ) )
      | ~ ( r1_tarski @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('29',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    $false ),
    inference(demod,[status(thm)],['0','29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RM4s0aBXyT
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:19:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 3.96/4.17  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.96/4.17  % Solved by: fo/fo7.sh
% 3.96/4.17  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.96/4.17  % done 5948 iterations in 3.721s
% 3.96/4.17  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.96/4.17  % SZS output start Refutation
% 3.96/4.17  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 3.96/4.17  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.96/4.17  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.96/4.17  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 3.96/4.17  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 3.96/4.17  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.96/4.17  thf(sk_B_1_type, type, sk_B_1: $i).
% 3.96/4.17  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.96/4.17  thf(sk_C_1_type, type, sk_C_1: $i).
% 3.96/4.17  thf(sk_A_type, type, sk_A: $i).
% 3.96/4.17  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 3.96/4.17  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 3.96/4.17  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.96/4.17  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 3.96/4.17  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 3.96/4.17  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 3.96/4.17  thf(t31_tops_2, conjecture,
% 3.96/4.17    (![A:$i]:
% 3.96/4.17     ( ( l1_pre_topc @ A ) =>
% 3.96/4.17       ( ![B:$i]:
% 3.96/4.17         ( ( m1_pre_topc @ B @ A ) =>
% 3.96/4.17           ( ![C:$i]:
% 3.96/4.17             ( ( m1_subset_1 @
% 3.96/4.17                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) =>
% 3.96/4.17               ( m1_subset_1 @
% 3.96/4.17                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 3.96/4.17  thf(zf_stmt_0, negated_conjecture,
% 3.96/4.17    (~( ![A:$i]:
% 3.96/4.17        ( ( l1_pre_topc @ A ) =>
% 3.96/4.17          ( ![B:$i]:
% 3.96/4.17            ( ( m1_pre_topc @ B @ A ) =>
% 3.96/4.17              ( ![C:$i]:
% 3.96/4.17                ( ( m1_subset_1 @
% 3.96/4.17                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) =>
% 3.96/4.17                  ( m1_subset_1 @
% 3.96/4.17                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 3.96/4.17    inference('cnf.neg', [status(esa)], [t31_tops_2])).
% 3.96/4.17  thf('0', plain,
% 3.96/4.17      (~ (m1_subset_1 @ sk_C_1 @ 
% 3.96/4.17          (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 3.96/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.96/4.17  thf('1', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 3.96/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.96/4.17  thf(d3_tarski, axiom,
% 3.96/4.17    (![A:$i,B:$i]:
% 3.96/4.17     ( ( r1_tarski @ A @ B ) <=>
% 3.96/4.17       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 3.96/4.17  thf('2', plain,
% 3.96/4.17      (![X4 : $i, X6 : $i]:
% 3.96/4.17         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 3.96/4.17      inference('cnf', [status(esa)], [d3_tarski])).
% 3.96/4.17  thf('3', plain,
% 3.96/4.17      ((m1_subset_1 @ sk_C_1 @ 
% 3.96/4.17        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1))))),
% 3.96/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.96/4.17  thf(t4_subset, axiom,
% 3.96/4.17    (![A:$i,B:$i,C:$i]:
% 3.96/4.17     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 3.96/4.17       ( m1_subset_1 @ A @ C ) ))).
% 3.96/4.17  thf('4', plain,
% 3.96/4.17      (![X20 : $i, X21 : $i, X22 : $i]:
% 3.96/4.17         (~ (r2_hidden @ X20 @ X21)
% 3.96/4.17          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22))
% 3.96/4.17          | (m1_subset_1 @ X20 @ X22))),
% 3.96/4.17      inference('cnf', [status(esa)], [t4_subset])).
% 3.96/4.17  thf('5', plain,
% 3.96/4.17      (![X0 : $i]:
% 3.96/4.17         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1)))
% 3.96/4.17          | ~ (r2_hidden @ X0 @ sk_C_1))),
% 3.96/4.17      inference('sup-', [status(thm)], ['3', '4'])).
% 3.96/4.17  thf('6', plain,
% 3.96/4.17      (![X0 : $i]:
% 3.96/4.17         ((r1_tarski @ sk_C_1 @ X0)
% 3.96/4.17          | (m1_subset_1 @ (sk_C @ X0 @ sk_C_1) @ 
% 3.96/4.17             (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1))))),
% 3.96/4.17      inference('sup-', [status(thm)], ['2', '5'])).
% 3.96/4.17  thf(t39_pre_topc, axiom,
% 3.96/4.17    (![A:$i]:
% 3.96/4.17     ( ( l1_pre_topc @ A ) =>
% 3.96/4.17       ( ![B:$i]:
% 3.96/4.17         ( ( m1_pre_topc @ B @ A ) =>
% 3.96/4.17           ( ![C:$i]:
% 3.96/4.17             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 3.96/4.17               ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ))).
% 3.96/4.17  thf('7', plain,
% 3.96/4.17      (![X23 : $i, X24 : $i, X25 : $i]:
% 3.96/4.17         (~ (m1_pre_topc @ X23 @ X24)
% 3.96/4.17          | (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 3.96/4.17          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 3.96/4.17          | ~ (l1_pre_topc @ X24))),
% 3.96/4.17      inference('cnf', [status(esa)], [t39_pre_topc])).
% 3.96/4.17  thf('8', plain,
% 3.96/4.17      (![X0 : $i, X1 : $i]:
% 3.96/4.17         ((r1_tarski @ sk_C_1 @ X0)
% 3.96/4.17          | ~ (l1_pre_topc @ X1)
% 3.96/4.17          | (m1_subset_1 @ (sk_C @ X0 @ sk_C_1) @ 
% 3.96/4.17             (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 3.96/4.17          | ~ (m1_pre_topc @ sk_B_1 @ X1))),
% 3.96/4.17      inference('sup-', [status(thm)], ['6', '7'])).
% 3.96/4.17  thf('9', plain,
% 3.96/4.17      (![X0 : $i]:
% 3.96/4.17         ((m1_subset_1 @ (sk_C @ X0 @ sk_C_1) @ 
% 3.96/4.17           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.96/4.17          | ~ (l1_pre_topc @ sk_A)
% 3.96/4.17          | (r1_tarski @ sk_C_1 @ X0))),
% 3.96/4.17      inference('sup-', [status(thm)], ['1', '8'])).
% 3.96/4.17  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 3.96/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.96/4.17  thf('11', plain,
% 3.96/4.17      (![X0 : $i]:
% 3.96/4.17         ((m1_subset_1 @ (sk_C @ X0 @ sk_C_1) @ 
% 3.96/4.17           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.96/4.17          | (r1_tarski @ sk_C_1 @ X0))),
% 3.96/4.17      inference('demod', [status(thm)], ['9', '10'])).
% 3.96/4.17  thf(t2_subset, axiom,
% 3.96/4.17    (![A:$i,B:$i]:
% 3.96/4.17     ( ( m1_subset_1 @ A @ B ) =>
% 3.96/4.17       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 3.96/4.17  thf('12', plain,
% 3.96/4.17      (![X15 : $i, X16 : $i]:
% 3.96/4.17         ((r2_hidden @ X15 @ X16)
% 3.96/4.17          | (v1_xboole_0 @ X16)
% 3.96/4.17          | ~ (m1_subset_1 @ X15 @ X16))),
% 3.96/4.17      inference('cnf', [status(esa)], [t2_subset])).
% 3.96/4.17  thf('13', plain,
% 3.96/4.17      (![X0 : $i]:
% 3.96/4.17         ((r1_tarski @ sk_C_1 @ X0)
% 3.96/4.17          | (v1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.96/4.17          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ 
% 3.96/4.17             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 3.96/4.17      inference('sup-', [status(thm)], ['11', '12'])).
% 3.96/4.17  thf(t100_zfmisc_1, axiom,
% 3.96/4.17    (![A:$i]: ( r1_tarski @ A @ ( k1_zfmisc_1 @ ( k3_tarski @ A ) ) ))).
% 3.96/4.17  thf('14', plain,
% 3.96/4.17      (![X14 : $i]: (r1_tarski @ X14 @ (k1_zfmisc_1 @ (k3_tarski @ X14)))),
% 3.96/4.17      inference('cnf', [status(esa)], [t100_zfmisc_1])).
% 3.96/4.17  thf(t69_enumset1, axiom,
% 3.96/4.17    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 3.96/4.17  thf('15', plain, (![X8 : $i]: ((k2_tarski @ X8 @ X8) = (k1_tarski @ X8))),
% 3.96/4.17      inference('cnf', [status(esa)], [t69_enumset1])).
% 3.96/4.17  thf(l1_zfmisc_1, axiom,
% 3.96/4.17    (![A:$i,B:$i]:
% 3.96/4.17     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 3.96/4.17  thf('16', plain,
% 3.96/4.17      (![X9 : $i, X10 : $i]:
% 3.96/4.17         ((r2_hidden @ X9 @ X10) | ~ (r1_tarski @ (k1_tarski @ X9) @ X10))),
% 3.96/4.17      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 3.96/4.17  thf('17', plain,
% 3.96/4.17      (![X0 : $i, X1 : $i]:
% 3.96/4.17         (~ (r1_tarski @ (k2_tarski @ X0 @ X0) @ X1) | (r2_hidden @ X0 @ X1))),
% 3.96/4.17      inference('sup-', [status(thm)], ['15', '16'])).
% 3.96/4.17  thf('18', plain,
% 3.96/4.17      (![X0 : $i]:
% 3.96/4.17         (r2_hidden @ X0 @ (k1_zfmisc_1 @ (k3_tarski @ (k2_tarski @ X0 @ X0))))),
% 3.96/4.17      inference('sup-', [status(thm)], ['14', '17'])).
% 3.96/4.17  thf(l51_zfmisc_1, axiom,
% 3.96/4.17    (![A:$i,B:$i]:
% 3.96/4.17     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 3.96/4.17  thf('19', plain,
% 3.96/4.17      (![X12 : $i, X13 : $i]:
% 3.96/4.17         ((k3_tarski @ (k2_tarski @ X12 @ X13)) = (k2_xboole_0 @ X12 @ X13))),
% 3.96/4.17      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 3.96/4.17  thf(idempotence_k2_xboole_0, axiom,
% 3.96/4.17    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 3.96/4.17  thf('20', plain, (![X7 : $i]: ((k2_xboole_0 @ X7 @ X7) = (X7))),
% 3.96/4.17      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 3.96/4.17  thf('21', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 3.96/4.17      inference('demod', [status(thm)], ['18', '19', '20'])).
% 3.96/4.17  thf(d1_xboole_0, axiom,
% 3.96/4.17    (![A:$i]:
% 3.96/4.17     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 3.96/4.17  thf('22', plain,
% 3.96/4.17      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 3.96/4.17      inference('cnf', [status(esa)], [d1_xboole_0])).
% 3.96/4.17  thf('23', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 3.96/4.17      inference('sup-', [status(thm)], ['21', '22'])).
% 3.96/4.17  thf('24', plain,
% 3.96/4.17      (![X0 : $i]:
% 3.96/4.17         ((r2_hidden @ (sk_C @ X0 @ sk_C_1) @ 
% 3.96/4.17           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.96/4.17          | (r1_tarski @ sk_C_1 @ X0))),
% 3.96/4.17      inference('clc', [status(thm)], ['13', '23'])).
% 3.96/4.17  thf('25', plain,
% 3.96/4.17      (![X4 : $i, X6 : $i]:
% 3.96/4.17         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 3.96/4.17      inference('cnf', [status(esa)], [d3_tarski])).
% 3.96/4.17  thf('26', plain,
% 3.96/4.17      (((r1_tarski @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.96/4.17        | (r1_tarski @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 3.96/4.17      inference('sup-', [status(thm)], ['24', '25'])).
% 3.96/4.17  thf('27', plain,
% 3.96/4.17      ((r1_tarski @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.96/4.17      inference('simplify', [status(thm)], ['26'])).
% 3.96/4.17  thf(t3_subset, axiom,
% 3.96/4.17    (![A:$i,B:$i]:
% 3.96/4.17     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 3.96/4.17  thf('28', plain,
% 3.96/4.17      (![X17 : $i, X19 : $i]:
% 3.96/4.17         ((m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X19)) | ~ (r1_tarski @ X17 @ X19))),
% 3.96/4.17      inference('cnf', [status(esa)], [t3_subset])).
% 3.96/4.17  thf('29', plain,
% 3.96/4.17      ((m1_subset_1 @ sk_C_1 @ 
% 3.96/4.17        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 3.96/4.17      inference('sup-', [status(thm)], ['27', '28'])).
% 3.96/4.17  thf('30', plain, ($false), inference('demod', [status(thm)], ['0', '29'])).
% 3.96/4.17  
% 3.96/4.17  % SZS output end Refutation
% 3.96/4.17  
% 4.03/4.18  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
