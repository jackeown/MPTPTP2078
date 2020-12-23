%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.T7nxRP2GSh

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:16 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   52 (  74 expanded)
%              Number of leaves         :   18 (  30 expanded)
%              Depth                    :    8
%              Number of atoms          :  342 ( 846 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v1_tops_2_type,type,(
    v1_tops_2: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t18_tops_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
             => ( ( ( r1_tarski @ B @ C )
                  & ( v1_tops_2 @ C @ A ) )
               => ( v1_tops_2 @ B @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
               => ( ( ( r1_tarski @ B @ C )
                    & ( v1_tops_2 @ C @ A ) )
                 => ( v1_tops_2 @ B @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t18_tops_2])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v1_tops_2 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( r2_hidden @ C @ B )
                 => ( v3_pre_topc @ C @ A ) ) ) ) ) ) )).

thf('1',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) ) )
      | ~ ( v3_pre_topc @ ( sk_C @ X11 @ X12 ) @ X12 )
      | ( v1_tops_2 @ X11 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_2])).

thf('2',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_2 @ sk_B @ sk_A )
    | ~ ( v3_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( v1_tops_2 @ sk_B @ sk_A )
    | ~ ( v3_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ~ ( v1_tops_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ~ ( v3_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) ) )
      | ( r2_hidden @ ( sk_C @ X11 @ X12 ) @ X11 )
      | ( v1_tops_2 @ X11 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_2])).

thf('9',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_2 @ sk_B @ sk_A )
    | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( v1_tops_2 @ sk_B @ sk_A )
    | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ~ ( v1_tops_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_B ),
    inference(clc,[status(thm)],['11','12'])).

thf('14',plain,(
    r1_tarski @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('15',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('16',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
    = sk_B ),
    inference('sup-',[status(thm)],['14','15'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('17',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('18',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_C_1 ),
    inference('sup-',[status(thm)],['13','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) ) )
      | ~ ( v1_tops_2 @ X11 @ X12 )
      | ~ ( r2_hidden @ X13 @ X11 )
      | ( v3_pre_topc @ X13 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_2])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( v1_tops_2 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_tops_2 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('28',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( m1_subset_1 @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_C_1 )
      | ( v3_pre_topc @ X0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['26','29'])).

thf('31',plain,(
    v3_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A ),
    inference('sup-',[status(thm)],['20','30'])).

thf('32',plain,(
    $false ),
    inference(demod,[status(thm)],['6','31'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.T7nxRP2GSh
% 0.16/0.38  % Computer   : n011.cluster.edu
% 0.16/0.38  % Model      : x86_64 x86_64
% 0.16/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.38  % Memory     : 8042.1875MB
% 0.16/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.38  % CPULimit   : 60
% 0.16/0.38  % DateTime   : Tue Dec  1 16:25:57 EST 2020
% 0.16/0.38  % CPUTime    : 
% 0.16/0.38  % Running portfolio for 600 s
% 0.16/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.25/0.39  % Number of cores: 8
% 0.25/0.39  % Python version: Python 3.6.8
% 0.25/0.39  % Running in FO mode
% 0.37/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.58  % Solved by: fo/fo7.sh
% 0.37/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.58  % done 96 iterations in 0.080s
% 0.37/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.58  % SZS output start Refutation
% 0.37/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.58  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.37/0.58  thf(v1_tops_2_type, type, v1_tops_2: $i > $i > $o).
% 0.37/0.58  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.37/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.58  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.37/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.58  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.37/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.58  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.37/0.58  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.37/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.58  thf(t18_tops_2, conjecture,
% 0.37/0.58    (![A:$i]:
% 0.37/0.58     ( ( l1_pre_topc @ A ) =>
% 0.37/0.58       ( ![B:$i]:
% 0.37/0.58         ( ( m1_subset_1 @
% 0.37/0.58             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.37/0.58           ( ![C:$i]:
% 0.37/0.58             ( ( m1_subset_1 @
% 0.37/0.58                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.37/0.58               ( ( ( r1_tarski @ B @ C ) & ( v1_tops_2 @ C @ A ) ) =>
% 0.37/0.58                 ( v1_tops_2 @ B @ A ) ) ) ) ) ) ))).
% 0.37/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.58    (~( ![A:$i]:
% 0.37/0.58        ( ( l1_pre_topc @ A ) =>
% 0.37/0.58          ( ![B:$i]:
% 0.37/0.58            ( ( m1_subset_1 @
% 0.37/0.58                B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.37/0.58              ( ![C:$i]:
% 0.37/0.58                ( ( m1_subset_1 @
% 0.37/0.58                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.37/0.58                  ( ( ( r1_tarski @ B @ C ) & ( v1_tops_2 @ C @ A ) ) =>
% 0.37/0.58                    ( v1_tops_2 @ B @ A ) ) ) ) ) ) ) )),
% 0.37/0.58    inference('cnf.neg', [status(esa)], [t18_tops_2])).
% 0.37/0.58  thf('0', plain,
% 0.37/0.58      ((m1_subset_1 @ sk_B @ 
% 0.37/0.58        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf(d1_tops_2, axiom,
% 0.37/0.58    (![A:$i]:
% 0.37/0.58     ( ( l1_pre_topc @ A ) =>
% 0.37/0.58       ( ![B:$i]:
% 0.37/0.58         ( ( m1_subset_1 @
% 0.37/0.58             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.37/0.58           ( ( v1_tops_2 @ B @ A ) <=>
% 0.37/0.58             ( ![C:$i]:
% 0.37/0.58               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.58                 ( ( r2_hidden @ C @ B ) => ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.37/0.58  thf('1', plain,
% 0.37/0.58      (![X11 : $i, X12 : $i]:
% 0.37/0.58         (~ (m1_subset_1 @ X11 @ 
% 0.37/0.58             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12))))
% 0.37/0.58          | ~ (v3_pre_topc @ (sk_C @ X11 @ X12) @ X12)
% 0.37/0.58          | (v1_tops_2 @ X11 @ X12)
% 0.37/0.58          | ~ (l1_pre_topc @ X12))),
% 0.37/0.58      inference('cnf', [status(esa)], [d1_tops_2])).
% 0.37/0.58  thf('2', plain,
% 0.37/0.58      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.58        | (v1_tops_2 @ sk_B @ sk_A)
% 0.37/0.58        | ~ (v3_pre_topc @ (sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.37/0.58      inference('sup-', [status(thm)], ['0', '1'])).
% 0.37/0.58  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('4', plain,
% 0.37/0.58      (((v1_tops_2 @ sk_B @ sk_A)
% 0.37/0.58        | ~ (v3_pre_topc @ (sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.37/0.58      inference('demod', [status(thm)], ['2', '3'])).
% 0.37/0.58  thf('5', plain, (~ (v1_tops_2 @ sk_B @ sk_A)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('6', plain, (~ (v3_pre_topc @ (sk_C @ sk_B @ sk_A) @ sk_A)),
% 0.37/0.58      inference('clc', [status(thm)], ['4', '5'])).
% 0.37/0.58  thf('7', plain,
% 0.37/0.58      ((m1_subset_1 @ sk_B @ 
% 0.37/0.58        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('8', plain,
% 0.37/0.58      (![X11 : $i, X12 : $i]:
% 0.37/0.58         (~ (m1_subset_1 @ X11 @ 
% 0.37/0.58             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12))))
% 0.37/0.58          | (r2_hidden @ (sk_C @ X11 @ X12) @ X11)
% 0.37/0.58          | (v1_tops_2 @ X11 @ X12)
% 0.37/0.58          | ~ (l1_pre_topc @ X12))),
% 0.37/0.58      inference('cnf', [status(esa)], [d1_tops_2])).
% 0.37/0.58  thf('9', plain,
% 0.37/0.58      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.58        | (v1_tops_2 @ sk_B @ sk_A)
% 0.37/0.58        | (r2_hidden @ (sk_C @ sk_B @ sk_A) @ sk_B))),
% 0.37/0.58      inference('sup-', [status(thm)], ['7', '8'])).
% 0.37/0.58  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('11', plain,
% 0.37/0.58      (((v1_tops_2 @ sk_B @ sk_A) | (r2_hidden @ (sk_C @ sk_B @ sk_A) @ sk_B))),
% 0.37/0.58      inference('demod', [status(thm)], ['9', '10'])).
% 0.37/0.58  thf('12', plain, (~ (v1_tops_2 @ sk_B @ sk_A)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('13', plain, ((r2_hidden @ (sk_C @ sk_B @ sk_A) @ sk_B)),
% 0.37/0.58      inference('clc', [status(thm)], ['11', '12'])).
% 0.37/0.58  thf('14', plain, ((r1_tarski @ sk_B @ sk_C_1)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf(t28_xboole_1, axiom,
% 0.37/0.58    (![A:$i,B:$i]:
% 0.37/0.58     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.37/0.58  thf('15', plain,
% 0.37/0.58      (![X6 : $i, X7 : $i]:
% 0.37/0.58         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 0.37/0.58      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.37/0.58  thf('16', plain, (((k3_xboole_0 @ sk_B @ sk_C_1) = (sk_B))),
% 0.37/0.58      inference('sup-', [status(thm)], ['14', '15'])).
% 0.37/0.58  thf(d4_xboole_0, axiom,
% 0.37/0.58    (![A:$i,B:$i,C:$i]:
% 0.37/0.58     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.37/0.58       ( ![D:$i]:
% 0.37/0.58         ( ( r2_hidden @ D @ C ) <=>
% 0.37/0.58           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.37/0.58  thf('17', plain,
% 0.37/0.58      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.37/0.58         (~ (r2_hidden @ X4 @ X3)
% 0.37/0.58          | (r2_hidden @ X4 @ X2)
% 0.37/0.58          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.37/0.58      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.37/0.58  thf('18', plain,
% 0.37/0.58      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.37/0.58         ((r2_hidden @ X4 @ X2) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.37/0.58      inference('simplify', [status(thm)], ['17'])).
% 0.37/0.58  thf('19', plain,
% 0.37/0.58      (![X0 : $i]: (~ (r2_hidden @ X0 @ sk_B) | (r2_hidden @ X0 @ sk_C_1))),
% 0.37/0.58      inference('sup-', [status(thm)], ['16', '18'])).
% 0.37/0.58  thf('20', plain, ((r2_hidden @ (sk_C @ sk_B @ sk_A) @ sk_C_1)),
% 0.37/0.58      inference('sup-', [status(thm)], ['13', '19'])).
% 0.37/0.58  thf('21', plain,
% 0.37/0.58      ((m1_subset_1 @ sk_C_1 @ 
% 0.37/0.58        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('22', plain,
% 0.37/0.58      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.37/0.58         (~ (m1_subset_1 @ X11 @ 
% 0.37/0.58             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12))))
% 0.37/0.58          | ~ (v1_tops_2 @ X11 @ X12)
% 0.37/0.58          | ~ (r2_hidden @ X13 @ X11)
% 0.37/0.58          | (v3_pre_topc @ X13 @ X12)
% 0.37/0.58          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.37/0.58          | ~ (l1_pre_topc @ X12))),
% 0.37/0.58      inference('cnf', [status(esa)], [d1_tops_2])).
% 0.37/0.58  thf('23', plain,
% 0.37/0.58      (![X0 : $i]:
% 0.37/0.58         (~ (l1_pre_topc @ sk_A)
% 0.37/0.58          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.58          | (v3_pre_topc @ X0 @ sk_A)
% 0.37/0.58          | ~ (r2_hidden @ X0 @ sk_C_1)
% 0.37/0.58          | ~ (v1_tops_2 @ sk_C_1 @ sk_A))),
% 0.37/0.58      inference('sup-', [status(thm)], ['21', '22'])).
% 0.37/0.58  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('25', plain, ((v1_tops_2 @ sk_C_1 @ sk_A)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('26', plain,
% 0.37/0.58      (![X0 : $i]:
% 0.37/0.58         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.58          | (v3_pre_topc @ X0 @ sk_A)
% 0.37/0.58          | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.37/0.58      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.37/0.58  thf('27', plain,
% 0.37/0.58      ((m1_subset_1 @ sk_C_1 @ 
% 0.37/0.58        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf(t4_subset, axiom,
% 0.37/0.58    (![A:$i,B:$i,C:$i]:
% 0.37/0.58     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.37/0.58       ( m1_subset_1 @ A @ C ) ))).
% 0.37/0.58  thf('28', plain,
% 0.37/0.58      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.37/0.58         (~ (r2_hidden @ X8 @ X9)
% 0.37/0.58          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 0.37/0.58          | (m1_subset_1 @ X8 @ X10))),
% 0.37/0.58      inference('cnf', [status(esa)], [t4_subset])).
% 0.37/0.58  thf('29', plain,
% 0.37/0.58      (![X0 : $i]:
% 0.37/0.58         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.58          | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.37/0.58      inference('sup-', [status(thm)], ['27', '28'])).
% 0.37/0.58  thf('30', plain,
% 0.37/0.58      (![X0 : $i]: (~ (r2_hidden @ X0 @ sk_C_1) | (v3_pre_topc @ X0 @ sk_A))),
% 0.37/0.58      inference('clc', [status(thm)], ['26', '29'])).
% 0.37/0.58  thf('31', plain, ((v3_pre_topc @ (sk_C @ sk_B @ sk_A) @ sk_A)),
% 0.37/0.58      inference('sup-', [status(thm)], ['20', '30'])).
% 0.37/0.58  thf('32', plain, ($false), inference('demod', [status(thm)], ['6', '31'])).
% 0.37/0.58  
% 0.37/0.58  % SZS output end Refutation
% 0.37/0.58  
% 0.37/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
