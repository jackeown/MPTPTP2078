%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xhSfjPwGWI

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:16 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 106 expanded)
%              Number of leaves         :   28 (  44 expanded)
%              Depth                    :   12
%              Number of atoms          :  423 ( 773 expanded)
%              Number of equality atoms :   11 (  16 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(m2_connsp_2_type,type,(
    m2_connsp_2: $i > $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(t35_connsp_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( m2_connsp_2 @ ( k2_struct_0 @ A ) @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( m2_connsp_2 @ ( k2_struct_0 @ A ) @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t35_connsp_2])).

thf('0',plain,(
    ~ ( m2_connsp_2 @ ( k2_struct_0 @ sk_A ) @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X14: $i] :
      ( ( ( k2_struct_0 @ X14 )
        = ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t43_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( k1_tops_1 @ A @ ( k2_struct_0 @ A ) )
        = ( k2_struct_0 @ A ) ) ) )).

thf('2',plain,(
    ! [X16: $i] :
      ( ( ( k1_tops_1 @ X16 @ ( k2_struct_0 @ X16 ) )
        = ( k2_struct_0 @ X16 ) )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t43_tops_1])).

thf('3',plain,(
    ! [X14: $i] :
      ( ( ( k2_struct_0 @ X14 )
        = ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('4',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X8 ) @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('5',plain,(
    ! [X7: $i] :
      ( ( k2_subset_1 @ X7 )
      = X7 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('6',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( m2_connsp_2 @ C @ A @ B )
              <=> ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('8',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( r1_tarski @ X17 @ ( k1_tops_1 @ X18 @ X19 ) )
      | ( m2_connsp_2 @ X19 @ X18 @ X17 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[d2_connsp_2])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( m2_connsp_2 @ X0 @ sk_A @ sk_B )
      | ~ ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( m2_connsp_2 @ X0 @ sk_A @ sk_B )
      | ~ ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
    | ( m2_connsp_2 @ ( u1_struct_0 @ sk_A ) @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['6','12'])).

thf('14',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( m2_connsp_2 @ ( u1_struct_0 @ sk_A ) @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['3','13'])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('16',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('17',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
    | ( m2_connsp_2 @ ( u1_struct_0 @ sk_A ) @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['14','17'])).

thf('19',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_struct_0 @ sk_A ) )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m2_connsp_2 @ ( u1_struct_0 @ sk_A ) @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['2','18'])).

thf('20',plain,(
    ! [X14: $i] :
      ( ( ( k2_struct_0 @ X14 )
        = ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('21',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('22',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r2_hidden @ X9 @ X10 )
      | ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('23',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('25',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ( X4
       != ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('26',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r2_hidden @ X2 @ ( k1_zfmisc_1 @ X3 ) )
      | ~ ( r1_tarski @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','26'])).

thf('28',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('29',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ~ ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['23','31'])).

thf('33',plain,
    ( ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['20','32'])).

thf('34',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['15','16'])).

thf('35',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X5 @ X4 )
      | ( r1_tarski @ X5 @ X3 )
      | ( X4
       != ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('37',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X5 @ X3 )
      | ~ ( r2_hidden @ X5 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    r1_tarski @ sk_B @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    m2_connsp_2 @ ( u1_struct_0 @ sk_A ) @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['19','38','39','40'])).

thf('42',plain,
    ( ( m2_connsp_2 @ ( k2_struct_0 @ sk_A ) @ sk_A @ sk_B )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['1','41'])).

thf('43',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['15','16'])).

thf('44',plain,(
    m2_connsp_2 @ ( k2_struct_0 @ sk_A ) @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    $false ),
    inference(demod,[status(thm)],['0','44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xhSfjPwGWI
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:28:40 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 61 iterations in 0.032s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.21/0.50  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.50  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.50  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.50  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.50  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.21/0.50  thf(m2_connsp_2_type, type, m2_connsp_2: $i > $i > $i > $o).
% 0.21/0.50  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.21/0.50  thf(t35_connsp_2, conjecture,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.50           ( m2_connsp_2 @ ( k2_struct_0 @ A ) @ A @ B ) ) ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i]:
% 0.21/0.50        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.50            ( l1_pre_topc @ A ) ) =>
% 0.21/0.50          ( ![B:$i]:
% 0.21/0.50            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.50              ( m2_connsp_2 @ ( k2_struct_0 @ A ) @ A @ B ) ) ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t35_connsp_2])).
% 0.21/0.50  thf('0', plain, (~ (m2_connsp_2 @ (k2_struct_0 @ sk_A) @ sk_A @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(d3_struct_0, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.21/0.50  thf('1', plain,
% 0.21/0.50      (![X14 : $i]:
% 0.21/0.50         (((k2_struct_0 @ X14) = (u1_struct_0 @ X14)) | ~ (l1_struct_0 @ X14))),
% 0.21/0.50      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.50  thf(t43_tops_1, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.50       ( ( k1_tops_1 @ A @ ( k2_struct_0 @ A ) ) = ( k2_struct_0 @ A ) ) ))).
% 0.21/0.50  thf('2', plain,
% 0.21/0.50      (![X16 : $i]:
% 0.21/0.50         (((k1_tops_1 @ X16 @ (k2_struct_0 @ X16)) = (k2_struct_0 @ X16))
% 0.21/0.50          | ~ (l1_pre_topc @ X16)
% 0.21/0.50          | ~ (v2_pre_topc @ X16))),
% 0.21/0.50      inference('cnf', [status(esa)], [t43_tops_1])).
% 0.21/0.50  thf('3', plain,
% 0.21/0.50      (![X14 : $i]:
% 0.21/0.50         (((k2_struct_0 @ X14) = (u1_struct_0 @ X14)) | ~ (l1_struct_0 @ X14))),
% 0.21/0.50      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.50  thf(dt_k2_subset_1, axiom,
% 0.21/0.50    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.21/0.50  thf('4', plain,
% 0.21/0.50      (![X8 : $i]: (m1_subset_1 @ (k2_subset_1 @ X8) @ (k1_zfmisc_1 @ X8))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.21/0.50  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.21/0.50  thf('5', plain, (![X7 : $i]: ((k2_subset_1 @ X7) = (X7))),
% 0.21/0.50      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.21/0.50  thf('6', plain, (![X8 : $i]: (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X8))),
% 0.21/0.50      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.50  thf('7', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(d2_connsp_2, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.50           ( ![C:$i]:
% 0.21/0.50             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.50               ( ( m2_connsp_2 @ C @ A @ B ) <=>
% 0.21/0.50                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.21/0.50  thf('8', plain,
% 0.21/0.50      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.21/0.50          | ~ (r1_tarski @ X17 @ (k1_tops_1 @ X18 @ X19))
% 0.21/0.50          | (m2_connsp_2 @ X19 @ X18 @ X17)
% 0.21/0.50          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.21/0.50          | ~ (l1_pre_topc @ X18)
% 0.21/0.50          | ~ (v2_pre_topc @ X18))),
% 0.21/0.50      inference('cnf', [status(esa)], [d2_connsp_2])).
% 0.21/0.50  thf('9', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (v2_pre_topc @ sk_A)
% 0.21/0.50          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.50          | (m2_connsp_2 @ X0 @ sk_A @ sk_B)
% 0.21/0.50          | ~ (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.50  thf('10', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('12', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.50          | (m2_connsp_2 @ X0 @ sk_A @ sk_B)
% 0.21/0.50          | ~ (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0)))),
% 0.21/0.50      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.21/0.50  thf('13', plain,
% 0.21/0.50      ((~ (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ (u1_struct_0 @ sk_A)))
% 0.21/0.50        | (m2_connsp_2 @ (u1_struct_0 @ sk_A) @ sk_A @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['6', '12'])).
% 0.21/0.50  thf('14', plain,
% 0.21/0.50      ((~ (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ (k2_struct_0 @ sk_A)))
% 0.21/0.50        | ~ (l1_struct_0 @ sk_A)
% 0.21/0.50        | (m2_connsp_2 @ (u1_struct_0 @ sk_A) @ sk_A @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['3', '13'])).
% 0.21/0.50  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(dt_l1_pre_topc, axiom,
% 0.21/0.50    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.50  thf('16', plain,
% 0.21/0.50      (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.50  thf('17', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.50      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.50  thf('18', plain,
% 0.21/0.50      ((~ (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ (k2_struct_0 @ sk_A)))
% 0.21/0.50        | (m2_connsp_2 @ (u1_struct_0 @ sk_A) @ sk_A @ sk_B))),
% 0.21/0.50      inference('demod', [status(thm)], ['14', '17'])).
% 0.21/0.50  thf('19', plain,
% 0.21/0.50      ((~ (r1_tarski @ sk_B @ (k2_struct_0 @ sk_A))
% 0.21/0.50        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.50        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.50        | (m2_connsp_2 @ (u1_struct_0 @ sk_A) @ sk_A @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['2', '18'])).
% 0.21/0.50  thf('20', plain,
% 0.21/0.50      (![X14 : $i]:
% 0.21/0.50         (((k2_struct_0 @ X14) = (u1_struct_0 @ X14)) | ~ (l1_struct_0 @ X14))),
% 0.21/0.50      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.50  thf('21', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(t2_subset, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ A @ B ) =>
% 0.21/0.50       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.21/0.50  thf('22', plain,
% 0.21/0.50      (![X9 : $i, X10 : $i]:
% 0.21/0.50         ((r2_hidden @ X9 @ X10)
% 0.21/0.50          | (v1_xboole_0 @ X10)
% 0.21/0.50          | ~ (m1_subset_1 @ X9 @ X10))),
% 0.21/0.50      inference('cnf', [status(esa)], [t2_subset])).
% 0.21/0.50  thf('23', plain,
% 0.21/0.50      (((v1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.50        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.50  thf(t36_xboole_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.21/0.50  thf('24', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 0.21/0.50      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.21/0.50  thf(d1_zfmisc_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.21/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.21/0.50  thf('25', plain,
% 0.21/0.50      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.50         (~ (r1_tarski @ X2 @ X3)
% 0.21/0.50          | (r2_hidden @ X2 @ X4)
% 0.21/0.50          | ((X4) != (k1_zfmisc_1 @ X3)))),
% 0.21/0.50      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.21/0.50  thf('26', plain,
% 0.21/0.50      (![X2 : $i, X3 : $i]:
% 0.21/0.50         ((r2_hidden @ X2 @ (k1_zfmisc_1 @ X3)) | ~ (r1_tarski @ X2 @ X3))),
% 0.21/0.50      inference('simplify', [status(thm)], ['25'])).
% 0.21/0.50  thf('27', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (r2_hidden @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['24', '26'])).
% 0.21/0.50  thf('28', plain, (![X8 : $i]: (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X8))),
% 0.21/0.50      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.50  thf(t5_subset, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.21/0.50          ( v1_xboole_0 @ C ) ) ))).
% 0.21/0.50  thf('29', plain,
% 0.21/0.50      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X11 @ X12)
% 0.21/0.50          | ~ (v1_xboole_0 @ X13)
% 0.21/0.50          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t5_subset])).
% 0.21/0.50  thf('30', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.50  thf('31', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['27', '30'])).
% 0.21/0.50  thf('32', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.50      inference('clc', [status(thm)], ['23', '31'])).
% 0.21/0.50  thf('33', plain,
% 0.21/0.50      (((r2_hidden @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.21/0.50        | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.50      inference('sup+', [status(thm)], ['20', '32'])).
% 0.21/0.50  thf('34', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.50      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.50  thf('35', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.21/0.50      inference('demod', [status(thm)], ['33', '34'])).
% 0.21/0.50  thf('36', plain,
% 0.21/0.50      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X5 @ X4)
% 0.21/0.50          | (r1_tarski @ X5 @ X3)
% 0.21/0.50          | ((X4) != (k1_zfmisc_1 @ X3)))),
% 0.21/0.50      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.21/0.50  thf('37', plain,
% 0.21/0.50      (![X3 : $i, X5 : $i]:
% 0.21/0.50         ((r1_tarski @ X5 @ X3) | ~ (r2_hidden @ X5 @ (k1_zfmisc_1 @ X3)))),
% 0.21/0.50      inference('simplify', [status(thm)], ['36'])).
% 0.21/0.50  thf('38', plain, ((r1_tarski @ sk_B @ (k2_struct_0 @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['35', '37'])).
% 0.21/0.50  thf('39', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('41', plain, ((m2_connsp_2 @ (u1_struct_0 @ sk_A) @ sk_A @ sk_B)),
% 0.21/0.50      inference('demod', [status(thm)], ['19', '38', '39', '40'])).
% 0.21/0.50  thf('42', plain,
% 0.21/0.50      (((m2_connsp_2 @ (k2_struct_0 @ sk_A) @ sk_A @ sk_B)
% 0.21/0.50        | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.50      inference('sup+', [status(thm)], ['1', '41'])).
% 0.21/0.50  thf('43', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.50      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.50  thf('44', plain, ((m2_connsp_2 @ (k2_struct_0 @ sk_A) @ sk_A @ sk_B)),
% 0.21/0.50      inference('demod', [status(thm)], ['42', '43'])).
% 0.21/0.50  thf('45', plain, ($false), inference('demod', [status(thm)], ['0', '44'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
