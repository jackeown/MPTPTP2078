%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MA6D4V1YbM

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:21 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   52 (  96 expanded)
%              Number of leaves         :   20 (  38 expanded)
%              Depth                    :    9
%              Number of atoms          :  431 (1197 expanded)
%              Number of equality atoms :   20 (  48 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(t75_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) )
            = ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) )
              = ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t75_tops_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( l1_pre_topc @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X4 @ X5 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('2',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( l1_pre_topc @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X4 @ X5 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('6',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('9',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( ( k2_tops_1 @ X7 @ X6 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X7 ) @ ( k2_pre_topc @ X7 @ X6 ) @ ( k1_tops_1 @ X7 @ X6 ) ) )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('10',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) @ ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(l79_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ ( k2_tops_1 @ A @ B ) )
            = ( k2_tops_1 @ A @ B ) ) ) ) )).

thf('13',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( ( k2_pre_topc @ X9 @ ( k2_tops_1 @ X9 @ X8 ) )
        = ( k2_tops_1 @ X9 @ X8 ) )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[l79_tops_1])).

thf('14',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    = ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l80_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) )
            = k1_xboole_0 ) ) ) )).

thf('19',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( ( k1_tops_1 @ X11 @ ( k2_tops_1 @ X11 @ ( k2_tops_1 @ X11 @ X10 ) ) )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[l80_tops_1])).

thf('20',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('25',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) )
      | ( ( k7_subset_1 @ X2 @ X1 @ X3 )
        = ( k4_xboole_0 @ X1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ X0 )
      = ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('28',plain,
    ( ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    = ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['10','11','17','23','26','27'])).

thf('29',plain,(
    ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
 != ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['28','29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MA6D4V1YbM
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:25:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.22/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.49  % Solved by: fo/fo7.sh
% 0.22/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.49  % done 30 iterations in 0.024s
% 0.22/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.49  % SZS output start Refutation
% 0.22/0.49  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.22/0.49  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.22/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.49  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.49  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.22/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.49  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.22/0.49  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.22/0.49  thf(t75_tops_1, conjecture,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.49       ( ![B:$i]:
% 0.22/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.49           ( ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) ) =
% 0.22/0.49             ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.22/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.49    (~( ![A:$i]:
% 0.22/0.49        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.49          ( ![B:$i]:
% 0.22/0.49            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.49              ( ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) ) =
% 0.22/0.49                ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) ) ) ) ) )),
% 0.22/0.49    inference('cnf.neg', [status(esa)], [t75_tops_1])).
% 0.22/0.49  thf('0', plain,
% 0.22/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(dt_k2_tops_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( ( l1_pre_topc @ A ) & 
% 0.22/0.49         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.22/0.49       ( m1_subset_1 @
% 0.22/0.49         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.22/0.49  thf('1', plain,
% 0.22/0.49      (![X4 : $i, X5 : $i]:
% 0.22/0.49         (~ (l1_pre_topc @ X4)
% 0.22/0.49          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.22/0.49          | (m1_subset_1 @ (k2_tops_1 @ X4 @ X5) @ 
% 0.22/0.49             (k1_zfmisc_1 @ (u1_struct_0 @ X4))))),
% 0.22/0.49      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.22/0.49  thf('2', plain,
% 0.22/0.49      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.22/0.49         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.49        | ~ (l1_pre_topc @ sk_A))),
% 0.22/0.49      inference('sup-', [status(thm)], ['0', '1'])).
% 0.22/0.49  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('4', plain,
% 0.22/0.49      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.22/0.49        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.49      inference('demod', [status(thm)], ['2', '3'])).
% 0.22/0.49  thf('5', plain,
% 0.22/0.49      (![X4 : $i, X5 : $i]:
% 0.22/0.49         (~ (l1_pre_topc @ X4)
% 0.22/0.49          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.22/0.49          | (m1_subset_1 @ (k2_tops_1 @ X4 @ X5) @ 
% 0.22/0.49             (k1_zfmisc_1 @ (u1_struct_0 @ X4))))),
% 0.22/0.49      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.22/0.49  thf('6', plain,
% 0.22/0.49      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 0.22/0.49         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.49        | ~ (l1_pre_topc @ sk_A))),
% 0.22/0.49      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.49  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('8', plain,
% 0.22/0.49      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 0.22/0.49        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.49      inference('demod', [status(thm)], ['6', '7'])).
% 0.22/0.49  thf(l78_tops_1, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( l1_pre_topc @ A ) =>
% 0.22/0.49       ( ![B:$i]:
% 0.22/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.49           ( ( k2_tops_1 @ A @ B ) =
% 0.22/0.49             ( k7_subset_1 @
% 0.22/0.49               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.22/0.49               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.22/0.49  thf('9', plain,
% 0.22/0.49      (![X6 : $i, X7 : $i]:
% 0.22/0.49         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.22/0.49          | ((k2_tops_1 @ X7 @ X6)
% 0.22/0.49              = (k7_subset_1 @ (u1_struct_0 @ X7) @ (k2_pre_topc @ X7 @ X6) @ 
% 0.22/0.49                 (k1_tops_1 @ X7 @ X6)))
% 0.22/0.49          | ~ (l1_pre_topc @ X7))),
% 0.22/0.49      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.22/0.49  thf('10', plain,
% 0.22/0.49      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.49        | ((k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.22/0.49            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.49               (k2_pre_topc @ sk_A @ 
% 0.22/0.49                (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B))) @ 
% 0.22/0.49               (k1_tops_1 @ sk_A @ 
% 0.22/0.49                (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B))))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['8', '9'])).
% 0.22/0.49  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('12', plain,
% 0.22/0.49      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.22/0.49        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.49      inference('demod', [status(thm)], ['2', '3'])).
% 0.22/0.49  thf(l79_tops_1, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.49       ( ![B:$i]:
% 0.22/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.49           ( ( k2_pre_topc @ A @ ( k2_tops_1 @ A @ B ) ) =
% 0.22/0.49             ( k2_tops_1 @ A @ B ) ) ) ) ))).
% 0.22/0.49  thf('13', plain,
% 0.22/0.49      (![X8 : $i, X9 : $i]:
% 0.22/0.49         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.22/0.49          | ((k2_pre_topc @ X9 @ (k2_tops_1 @ X9 @ X8)) = (k2_tops_1 @ X9 @ X8))
% 0.22/0.49          | ~ (l1_pre_topc @ X9)
% 0.22/0.49          | ~ (v2_pre_topc @ X9))),
% 0.22/0.49      inference('cnf', [status(esa)], [l79_tops_1])).
% 0.22/0.49  thf('14', plain,
% 0.22/0.49      ((~ (v2_pre_topc @ sk_A)
% 0.22/0.49        | ~ (l1_pre_topc @ sk_A)
% 0.22/0.49        | ((k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.22/0.49            = (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['12', '13'])).
% 0.22/0.49  thf('15', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('17', plain,
% 0.22/0.49      (((k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.22/0.49         = (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.22/0.49      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.22/0.49  thf('18', plain,
% 0.22/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(l80_tops_1, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.49       ( ![B:$i]:
% 0.22/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.49           ( ( k1_tops_1 @ A @ ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) ) =
% 0.22/0.49             ( k1_xboole_0 ) ) ) ) ))).
% 0.22/0.49  thf('19', plain,
% 0.22/0.49      (![X10 : $i, X11 : $i]:
% 0.22/0.49         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.22/0.49          | ((k1_tops_1 @ X11 @ (k2_tops_1 @ X11 @ (k2_tops_1 @ X11 @ X10)))
% 0.22/0.49              = (k1_xboole_0))
% 0.22/0.49          | ~ (l1_pre_topc @ X11)
% 0.22/0.49          | ~ (v2_pre_topc @ X11))),
% 0.22/0.49      inference('cnf', [status(esa)], [l80_tops_1])).
% 0.22/0.49  thf('20', plain,
% 0.22/0.49      ((~ (v2_pre_topc @ sk_A)
% 0.22/0.49        | ~ (l1_pre_topc @ sk_A)
% 0.22/0.49        | ((k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.22/0.49            = (k1_xboole_0)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['18', '19'])).
% 0.22/0.49  thf('21', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('23', plain,
% 0.22/0.49      (((k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.22/0.49         = (k1_xboole_0))),
% 0.22/0.49      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.22/0.49  thf('24', plain,
% 0.22/0.49      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 0.22/0.49        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.49      inference('demod', [status(thm)], ['6', '7'])).
% 0.22/0.49  thf(redefinition_k7_subset_1, axiom,
% 0.22/0.49    (![A:$i,B:$i,C:$i]:
% 0.22/0.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.49       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.22/0.49  thf('25', plain,
% 0.22/0.49      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.49         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2))
% 0.22/0.49          | ((k7_subset_1 @ X2 @ X1 @ X3) = (k4_xboole_0 @ X1 @ X3)))),
% 0.22/0.49      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.22/0.49  thf('26', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.49           (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ X0)
% 0.22/0.49           = (k4_xboole_0 @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ X0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['24', '25'])).
% 0.22/0.49  thf(t3_boole, axiom,
% 0.22/0.49    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.22/0.49  thf('27', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.22/0.49      inference('cnf', [status(esa)], [t3_boole])).
% 0.22/0.49  thf('28', plain,
% 0.22/0.49      (((k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.22/0.49         = (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.22/0.49      inference('demod', [status(thm)], ['10', '11', '17', '23', '26', '27'])).
% 0.22/0.49  thf('29', plain,
% 0.22/0.49      (((k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.22/0.49         != (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('30', plain, ($false),
% 0.22/0.49      inference('simplify_reflect-', [status(thm)], ['28', '29'])).
% 0.22/0.49  
% 0.22/0.49  % SZS output end Refutation
% 0.22/0.49  
% 0.22/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
