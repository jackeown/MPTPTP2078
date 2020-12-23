%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0GEZjJjAyg

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:41 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   50 (  68 expanded)
%              Number of leaves         :   21 (  30 expanded)
%              Depth                    :    9
%              Number of atoms          :  298 ( 622 expanded)
%              Number of equality atoms :   15 (  33 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v3_tops_1_type,type,(
    v3_tops_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( v3_pre_topc @ X9 @ X10 )
      | ~ ( r1_tarski @ X9 @ X11 )
      | ( r1_tarski @ X9 @ ( k1_tops_1 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
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
    r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['7','9'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('11',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k3_xboole_0 @ X3 @ X4 )
        = X3 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('12',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
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

thf('14',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( v2_tops_1 @ X12 @ X13 )
      | ( ( k1_tops_1 @ X13 @ X12 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('15',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t92_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tops_1 @ B @ A )
           => ( v2_tops_1 @ B @ A ) ) ) ) )).

thf('18',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( v2_tops_1 @ X14 @ X15 )
      | ~ ( v3_tops_1 @ X14 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t92_tops_1])).

thf('19',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_tops_1 @ sk_B @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v3_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v2_tops_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['15','16','22'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('24',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('25',plain,(
    k1_xboole_0 = sk_B ),
    inference(demod,[status(thm)],['12','23','24'])).

thf('26',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['25','26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0GEZjJjAyg
% 0.15/0.39  % Computer   : n008.cluster.edu
% 0.15/0.39  % Model      : x86_64 x86_64
% 0.15/0.39  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.39  % Memory     : 8042.1875MB
% 0.15/0.39  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.39  % CPULimit   : 60
% 0.15/0.39  % DateTime   : Tue Dec  1 12:33:15 EST 2020
% 0.15/0.39  % CPUTime    : 
% 0.15/0.39  % Running portfolio for 600 s
% 0.15/0.39  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.39  % Number of cores: 8
% 0.15/0.40  % Python version: Python 3.6.8
% 0.15/0.40  % Running in FO mode
% 0.24/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.53  % Solved by: fo/fo7.sh
% 0.24/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.53  % done 50 iterations in 0.022s
% 0.24/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.53  % SZS output start Refutation
% 0.24/0.53  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.24/0.53  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.24/0.53  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 0.24/0.53  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.24/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.24/0.53  thf(v3_tops_1_type, type, v3_tops_1: $i > $i > $o).
% 0.24/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.53  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.24/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.24/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.24/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.24/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.24/0.53  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.24/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.24/0.53  thf(t97_tops_1, conjecture,
% 0.24/0.53    (![A:$i]:
% 0.24/0.53     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.24/0.53       ( ![B:$i]:
% 0.24/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.24/0.53           ( ( ( v3_pre_topc @ B @ A ) & ( v3_tops_1 @ B @ A ) ) =>
% 0.24/0.53             ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.24/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.53    (~( ![A:$i]:
% 0.24/0.53        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.24/0.53          ( ![B:$i]:
% 0.24/0.53            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.24/0.53              ( ( ( v3_pre_topc @ B @ A ) & ( v3_tops_1 @ B @ A ) ) =>
% 0.24/0.53                ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.24/0.53    inference('cnf.neg', [status(esa)], [t97_tops_1])).
% 0.24/0.53  thf('0', plain,
% 0.24/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.53  thf('1', plain,
% 0.24/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.53  thf(t56_tops_1, axiom,
% 0.24/0.53    (![A:$i]:
% 0.24/0.53     ( ( l1_pre_topc @ A ) =>
% 0.24/0.53       ( ![B:$i]:
% 0.24/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.24/0.53           ( ![C:$i]:
% 0.24/0.53             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.24/0.53               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.24/0.53                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.24/0.53  thf('2', plain,
% 0.24/0.53      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.24/0.53         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.24/0.53          | ~ (v3_pre_topc @ X9 @ X10)
% 0.24/0.53          | ~ (r1_tarski @ X9 @ X11)
% 0.24/0.53          | (r1_tarski @ X9 @ (k1_tops_1 @ X10 @ X11))
% 0.24/0.53          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.24/0.53          | ~ (l1_pre_topc @ X10))),
% 0.24/0.53      inference('cnf', [status(esa)], [t56_tops_1])).
% 0.24/0.53  thf('3', plain,
% 0.24/0.53      (![X0 : $i]:
% 0.24/0.53         (~ (l1_pre_topc @ sk_A)
% 0.24/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.24/0.53          | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0))
% 0.24/0.53          | ~ (r1_tarski @ sk_B @ X0)
% 0.24/0.53          | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.24/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.24/0.53  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.53  thf('5', plain, ((v3_pre_topc @ sk_B @ sk_A)),
% 0.24/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.53  thf('6', plain,
% 0.24/0.53      (![X0 : $i]:
% 0.24/0.53         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.24/0.53          | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0))
% 0.24/0.53          | ~ (r1_tarski @ sk_B @ X0))),
% 0.24/0.53      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.24/0.53  thf('7', plain,
% 0.24/0.53      ((~ (r1_tarski @ sk_B @ sk_B)
% 0.24/0.53        | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.24/0.53      inference('sup-', [status(thm)], ['0', '6'])).
% 0.24/0.53  thf(d10_xboole_0, axiom,
% 0.24/0.53    (![A:$i,B:$i]:
% 0.24/0.53     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.24/0.53  thf('8', plain,
% 0.24/0.53      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.24/0.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.24/0.53  thf('9', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.24/0.53      inference('simplify', [status(thm)], ['8'])).
% 0.24/0.53  thf('10', plain, ((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))),
% 0.24/0.53      inference('demod', [status(thm)], ['7', '9'])).
% 0.24/0.53  thf(t28_xboole_1, axiom,
% 0.24/0.53    (![A:$i,B:$i]:
% 0.24/0.53     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.24/0.53  thf('11', plain,
% 0.24/0.53      (![X3 : $i, X4 : $i]:
% 0.24/0.53         (((k3_xboole_0 @ X3 @ X4) = (X3)) | ~ (r1_tarski @ X3 @ X4))),
% 0.24/0.53      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.24/0.53  thf('12', plain,
% 0.24/0.53      (((k3_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.24/0.53      inference('sup-', [status(thm)], ['10', '11'])).
% 0.24/0.53  thf('13', plain,
% 0.24/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.53  thf(t84_tops_1, axiom,
% 0.24/0.53    (![A:$i]:
% 0.24/0.53     ( ( l1_pre_topc @ A ) =>
% 0.24/0.53       ( ![B:$i]:
% 0.24/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.24/0.53           ( ( v2_tops_1 @ B @ A ) <=>
% 0.24/0.53             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.24/0.53  thf('14', plain,
% 0.24/0.53      (![X12 : $i, X13 : $i]:
% 0.24/0.53         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.24/0.53          | ~ (v2_tops_1 @ X12 @ X13)
% 0.24/0.53          | ((k1_tops_1 @ X13 @ X12) = (k1_xboole_0))
% 0.24/0.53          | ~ (l1_pre_topc @ X13))),
% 0.24/0.53      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.24/0.53  thf('15', plain,
% 0.24/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.24/0.53        | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.24/0.53        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.24/0.53      inference('sup-', [status(thm)], ['13', '14'])).
% 0.24/0.53  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.53  thf('17', plain,
% 0.24/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.53  thf(t92_tops_1, axiom,
% 0.24/0.53    (![A:$i]:
% 0.24/0.53     ( ( l1_pre_topc @ A ) =>
% 0.24/0.53       ( ![B:$i]:
% 0.24/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.24/0.53           ( ( v3_tops_1 @ B @ A ) => ( v2_tops_1 @ B @ A ) ) ) ) ))).
% 0.24/0.53  thf('18', plain,
% 0.24/0.53      (![X14 : $i, X15 : $i]:
% 0.24/0.53         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.24/0.53          | (v2_tops_1 @ X14 @ X15)
% 0.24/0.53          | ~ (v3_tops_1 @ X14 @ X15)
% 0.24/0.53          | ~ (l1_pre_topc @ X15))),
% 0.24/0.53      inference('cnf', [status(esa)], [t92_tops_1])).
% 0.24/0.53  thf('19', plain,
% 0.24/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.24/0.53        | ~ (v3_tops_1 @ sk_B @ sk_A)
% 0.24/0.53        | (v2_tops_1 @ sk_B @ sk_A))),
% 0.24/0.53      inference('sup-', [status(thm)], ['17', '18'])).
% 0.24/0.53  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.53  thf('21', plain, ((v3_tops_1 @ sk_B @ sk_A)),
% 0.24/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.53  thf('22', plain, ((v2_tops_1 @ sk_B @ sk_A)),
% 0.24/0.53      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.24/0.53  thf('23', plain, (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.24/0.53      inference('demod', [status(thm)], ['15', '16', '22'])).
% 0.24/0.53  thf(t2_boole, axiom,
% 0.24/0.53    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.24/0.53  thf('24', plain,
% 0.24/0.53      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.24/0.53      inference('cnf', [status(esa)], [t2_boole])).
% 0.24/0.53  thf('25', plain, (((k1_xboole_0) = (sk_B))),
% 0.24/0.53      inference('demod', [status(thm)], ['12', '23', '24'])).
% 0.24/0.53  thf('26', plain, (((sk_B) != (k1_xboole_0))),
% 0.24/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.53  thf('27', plain, ($false),
% 0.24/0.53      inference('simplify_reflect-', [status(thm)], ['25', '26'])).
% 0.24/0.53  
% 0.24/0.53  % SZS output end Refutation
% 0.24/0.53  
% 0.24/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
