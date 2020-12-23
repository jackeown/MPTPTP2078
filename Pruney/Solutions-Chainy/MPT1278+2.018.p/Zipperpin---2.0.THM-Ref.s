%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1245gnuqRx

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:42 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   51 (  70 expanded)
%              Number of leaves         :   20 (  30 expanded)
%              Depth                    :    9
%              Number of atoms          :  303 ( 636 expanded)
%              Number of equality atoms :   12 (  31 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v3_tops_1_type,type,(
    v3_tops_1: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(t97_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v3_pre_topc @ B @ A )
              & ( v3_tops_1 @ B @ A ) )
           => ( B = k1_xboole_0 ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( ( v3_pre_topc @ B @ A )
                & ( v3_tops_1 @ B @ A ) )
             => ( B = k1_xboole_0 ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t97_tops_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t56_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v3_pre_topc @ B @ A )
                  & ( r1_tarski @ B @ C ) )
               => ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( v3_pre_topc @ X10 @ X11 )
      | ~ ( r1_tarski @ X10 @ X12 )
      | ( r1_tarski @ X10 @ ( k1_tops_1 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t56_tops_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 )
      | ~ ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v3_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_B )
    | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('9',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t84_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( ( k1_tops_1 @ A @ B )
              = k1_xboole_0 ) ) ) ) )).

thf('11',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v2_tops_1 @ X13 @ X14 )
      | ( ( k1_tops_1 @ X14 @ X13 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('12',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t92_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tops_1 @ B @ A )
           => ( v2_tops_1 @ B @ A ) ) ) ) )).

thf('15',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( v2_tops_1 @ X15 @ X16 )
      | ~ ( v3_tops_1 @ X15 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t92_tops_1])).

thf('16',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_tops_1 @ sk_B @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v3_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v2_tops_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('20',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['12','13','19'])).

thf('21',plain,(
    r1_tarski @ sk_B @ k1_xboole_0 ),
    inference(demod,[status(thm)],['7','9','20'])).

thf('22',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('23',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_B )
    | ( k1_xboole_0 = sk_B ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('24',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('25',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('26',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    k1_xboole_0 = sk_B ),
    inference(demod,[status(thm)],['23','26'])).

thf('28',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['27','28'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1245gnuqRx
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:08:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.44  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.44  % Solved by: fo/fo7.sh
% 0.20/0.44  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.44  % done 40 iterations in 0.021s
% 0.20/0.44  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.44  % SZS output start Refutation
% 0.20/0.44  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.44  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 0.20/0.44  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.44  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.44  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.20/0.44  thf(v3_tops_1_type, type, v3_tops_1: $i > $i > $o).
% 0.20/0.44  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.20/0.44  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.44  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.44  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.44  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.44  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.44  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.44  thf(t97_tops_1, conjecture,
% 0.20/0.44    (![A:$i]:
% 0.20/0.44     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.44       ( ![B:$i]:
% 0.20/0.44         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.44           ( ( ( v3_pre_topc @ B @ A ) & ( v3_tops_1 @ B @ A ) ) =>
% 0.20/0.44             ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.20/0.44  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.44    (~( ![A:$i]:
% 0.20/0.44        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.44          ( ![B:$i]:
% 0.20/0.44            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.44              ( ( ( v3_pre_topc @ B @ A ) & ( v3_tops_1 @ B @ A ) ) =>
% 0.20/0.44                ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.20/0.44    inference('cnf.neg', [status(esa)], [t97_tops_1])).
% 0.20/0.44  thf('0', plain,
% 0.20/0.44      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf('1', plain,
% 0.20/0.44      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf(t56_tops_1, axiom,
% 0.20/0.44    (![A:$i]:
% 0.20/0.44     ( ( l1_pre_topc @ A ) =>
% 0.20/0.44       ( ![B:$i]:
% 0.20/0.44         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.44           ( ![C:$i]:
% 0.20/0.44             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.44               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.20/0.44                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.20/0.44  thf('2', plain,
% 0.20/0.44      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.44         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.20/0.44          | ~ (v3_pre_topc @ X10 @ X11)
% 0.20/0.44          | ~ (r1_tarski @ X10 @ X12)
% 0.20/0.44          | (r1_tarski @ X10 @ (k1_tops_1 @ X11 @ X12))
% 0.20/0.44          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.20/0.44          | ~ (l1_pre_topc @ X11))),
% 0.20/0.44      inference('cnf', [status(esa)], [t56_tops_1])).
% 0.20/0.44  thf('3', plain,
% 0.20/0.44      (![X0 : $i]:
% 0.20/0.44         (~ (l1_pre_topc @ sk_A)
% 0.20/0.44          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.44          | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0))
% 0.20/0.44          | ~ (r1_tarski @ sk_B @ X0)
% 0.20/0.44          | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.20/0.44      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.44  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf('5', plain, ((v3_pre_topc @ sk_B @ sk_A)),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf('6', plain,
% 0.20/0.44      (![X0 : $i]:
% 0.20/0.44         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.44          | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0))
% 0.20/0.44          | ~ (r1_tarski @ sk_B @ X0))),
% 0.20/0.44      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.20/0.44  thf('7', plain,
% 0.20/0.44      ((~ (r1_tarski @ sk_B @ sk_B)
% 0.20/0.44        | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.20/0.44      inference('sup-', [status(thm)], ['0', '6'])).
% 0.20/0.44  thf(d10_xboole_0, axiom,
% 0.20/0.44    (![A:$i,B:$i]:
% 0.20/0.44     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.44  thf('8', plain,
% 0.20/0.44      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.20/0.44      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.44  thf('9', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.20/0.44      inference('simplify', [status(thm)], ['8'])).
% 0.20/0.44  thf('10', plain,
% 0.20/0.44      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf(t84_tops_1, axiom,
% 0.20/0.44    (![A:$i]:
% 0.20/0.44     ( ( l1_pre_topc @ A ) =>
% 0.20/0.44       ( ![B:$i]:
% 0.20/0.44         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.44           ( ( v2_tops_1 @ B @ A ) <=>
% 0.20/0.44             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.20/0.44  thf('11', plain,
% 0.20/0.44      (![X13 : $i, X14 : $i]:
% 0.20/0.44         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.20/0.44          | ~ (v2_tops_1 @ X13 @ X14)
% 0.20/0.44          | ((k1_tops_1 @ X14 @ X13) = (k1_xboole_0))
% 0.20/0.44          | ~ (l1_pre_topc @ X14))),
% 0.20/0.44      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.20/0.44  thf('12', plain,
% 0.20/0.44      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.44        | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.20/0.44        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.20/0.44      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.44  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf('14', plain,
% 0.20/0.44      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf(t92_tops_1, axiom,
% 0.20/0.44    (![A:$i]:
% 0.20/0.44     ( ( l1_pre_topc @ A ) =>
% 0.20/0.44       ( ![B:$i]:
% 0.20/0.44         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.44           ( ( v3_tops_1 @ B @ A ) => ( v2_tops_1 @ B @ A ) ) ) ) ))).
% 0.20/0.44  thf('15', plain,
% 0.20/0.44      (![X15 : $i, X16 : $i]:
% 0.20/0.44         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.20/0.44          | (v2_tops_1 @ X15 @ X16)
% 0.20/0.44          | ~ (v3_tops_1 @ X15 @ X16)
% 0.20/0.44          | ~ (l1_pre_topc @ X16))),
% 0.20/0.44      inference('cnf', [status(esa)], [t92_tops_1])).
% 0.20/0.44  thf('16', plain,
% 0.20/0.44      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.44        | ~ (v3_tops_1 @ sk_B @ sk_A)
% 0.20/0.44        | (v2_tops_1 @ sk_B @ sk_A))),
% 0.20/0.44      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.44  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf('18', plain, ((v3_tops_1 @ sk_B @ sk_A)),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf('19', plain, ((v2_tops_1 @ sk_B @ sk_A)),
% 0.20/0.44      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.20/0.44  thf('20', plain, (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.20/0.44      inference('demod', [status(thm)], ['12', '13', '19'])).
% 0.20/0.44  thf('21', plain, ((r1_tarski @ sk_B @ k1_xboole_0)),
% 0.20/0.44      inference('demod', [status(thm)], ['7', '9', '20'])).
% 0.20/0.44  thf('22', plain,
% 0.20/0.44      (![X0 : $i, X2 : $i]:
% 0.20/0.44         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.44      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.44  thf('23', plain,
% 0.20/0.44      ((~ (r1_tarski @ k1_xboole_0 @ sk_B) | ((k1_xboole_0) = (sk_B)))),
% 0.20/0.44      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.44  thf(t4_subset_1, axiom,
% 0.20/0.44    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.20/0.44  thf('24', plain,
% 0.20/0.44      (![X3 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X3))),
% 0.20/0.44      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.20/0.44  thf(t3_subset, axiom,
% 0.20/0.44    (![A:$i,B:$i]:
% 0.20/0.44     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.44  thf('25', plain,
% 0.20/0.44      (![X4 : $i, X5 : $i]:
% 0.20/0.44         ((r1_tarski @ X4 @ X5) | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.20/0.44      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.44  thf('26', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.20/0.44      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.44  thf('27', plain, (((k1_xboole_0) = (sk_B))),
% 0.20/0.44      inference('demod', [status(thm)], ['23', '26'])).
% 0.20/0.44  thf('28', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf('29', plain, ($false),
% 0.20/0.44      inference('simplify_reflect-', [status(thm)], ['27', '28'])).
% 0.20/0.44  
% 0.20/0.44  % SZS output end Refutation
% 0.20/0.44  
% 0.20/0.45  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
