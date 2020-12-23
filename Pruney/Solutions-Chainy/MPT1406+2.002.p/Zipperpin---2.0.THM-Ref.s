%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jd0t4hY4T6

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:18 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   52 (  86 expanded)
%              Number of leaves         :   20 (  34 expanded)
%              Depth                    :   11
%              Number of atoms          :  334 ( 873 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m2_connsp_2_type,type,(
    m2_connsp_2: $i > $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(t36_connsp_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m2_connsp_2 @ C @ A @ B )
             => ( r1_tarski @ B @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m2_connsp_2 @ C @ A @ B )
               => ( r1_tarski @ B @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t36_connsp_2])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m2_connsp_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m2_connsp_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ! [C: $i] :
          ( ( m2_connsp_2 @ C @ A @ B )
         => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('3',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( m2_connsp_2 @ X14 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_connsp_2])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( m2_connsp_2 @ X0 @ sk_A @ sk_B )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( m2_connsp_2 @ X0 @ sk_A @ sk_B )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf('9',plain,(
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

thf('10',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( m2_connsp_2 @ X11 @ X10 @ X9 )
      | ( r1_tarski @ X9 @ ( k1_tops_1 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[d2_connsp_2])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( m2_connsp_2 @ X0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( m2_connsp_2 @ X0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,
    ( ~ ( m2_connsp_2 @ sk_C @ sk_A @ sk_B )
    | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['8','14'])).

thf('16',plain,(
    m2_connsp_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('18',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_xboole_0 @ X5 @ X6 )
        = X5 )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('19',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
    = sk_B ),
    inference('sup-',[status(thm)],['17','18'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('21',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('22',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X8 @ X7 ) @ X7 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('23',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C ),
    inference(demod,[status(thm)],['23','24'])).

thf(t108_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ B ) ) )).

thf('26',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ( r1_tarski @ ( k3_xboole_0 @ X2 @ X4 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t108_xboole_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C ) @ X0 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) ) @ sk_C ) ),
    inference('sup+',[status(thm)],['20','27'])).

thf('29',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference('sup+',[status(thm)],['19','28'])).

thf('30',plain,(
    $false ),
    inference(demod,[status(thm)],['0','29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jd0t4hY4T6
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:48:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.21/0.35  % Python version: Python 3.6.8
% 0.21/0.36  % Running in FO mode
% 0.22/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.50  % Solved by: fo/fo7.sh
% 0.22/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.50  % done 47 iterations in 0.027s
% 0.22/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.50  % SZS output start Refutation
% 0.22/0.50  thf(m2_connsp_2_type, type, m2_connsp_2: $i > $i > $i > $o).
% 0.22/0.50  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.50  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.22/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.50  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.22/0.50  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.22/0.50  thf(t36_connsp_2, conjecture,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.50       ( ![B:$i]:
% 0.22/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.50           ( ![C:$i]: ( ( m2_connsp_2 @ C @ A @ B ) => ( r1_tarski @ B @ C ) ) ) ) ) ))).
% 0.22/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.50    (~( ![A:$i]:
% 0.22/0.50        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.22/0.50            ( l1_pre_topc @ A ) ) =>
% 0.22/0.50          ( ![B:$i]:
% 0.22/0.50            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.50              ( ![C:$i]:
% 0.22/0.50                ( ( m2_connsp_2 @ C @ A @ B ) => ( r1_tarski @ B @ C ) ) ) ) ) ) )),
% 0.22/0.50    inference('cnf.neg', [status(esa)], [t36_connsp_2])).
% 0.22/0.50  thf('0', plain, (~ (r1_tarski @ sk_B @ sk_C)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('1', plain, ((m2_connsp_2 @ sk_C @ sk_A @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('2', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(dt_m2_connsp_2, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.22/0.50         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.22/0.50       ( ![C:$i]:
% 0.22/0.50         ( ( m2_connsp_2 @ C @ A @ B ) =>
% 0.22/0.50           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.22/0.50  thf('3', plain,
% 0.22/0.50      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.22/0.50         (~ (l1_pre_topc @ X12)
% 0.22/0.50          | ~ (v2_pre_topc @ X12)
% 0.22/0.50          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.22/0.50          | (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.22/0.50          | ~ (m2_connsp_2 @ X14 @ X12 @ X13))),
% 0.22/0.50      inference('cnf', [status(esa)], [dt_m2_connsp_2])).
% 0.22/0.50  thf('4', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (~ (m2_connsp_2 @ X0 @ sk_A @ sk_B)
% 0.22/0.50          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.50          | ~ (v2_pre_topc @ sk_A)
% 0.22/0.50          | ~ (l1_pre_topc @ sk_A))),
% 0.22/0.50      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.50  thf('5', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('7', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (~ (m2_connsp_2 @ X0 @ sk_A @ sk_B)
% 0.22/0.50          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.50      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.22/0.50  thf('8', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['1', '7'])).
% 0.22/0.50  thf('9', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(d2_connsp_2, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.50       ( ![B:$i]:
% 0.22/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.50           ( ![C:$i]:
% 0.22/0.50             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.50               ( ( m2_connsp_2 @ C @ A @ B ) <=>
% 0.22/0.50                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.22/0.50  thf('10', plain,
% 0.22/0.50      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.22/0.50         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.22/0.50          | ~ (m2_connsp_2 @ X11 @ X10 @ X9)
% 0.22/0.50          | (r1_tarski @ X9 @ (k1_tops_1 @ X10 @ X11))
% 0.22/0.50          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.22/0.50          | ~ (l1_pre_topc @ X10)
% 0.22/0.50          | ~ (v2_pre_topc @ X10))),
% 0.22/0.50      inference('cnf', [status(esa)], [d2_connsp_2])).
% 0.22/0.50  thf('11', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (~ (v2_pre_topc @ sk_A)
% 0.22/0.50          | ~ (l1_pre_topc @ sk_A)
% 0.22/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.50          | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0))
% 0.22/0.50          | ~ (m2_connsp_2 @ X0 @ sk_A @ sk_B))),
% 0.22/0.50      inference('sup-', [status(thm)], ['9', '10'])).
% 0.22/0.50  thf('12', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('14', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.50          | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0))
% 0.22/0.50          | ~ (m2_connsp_2 @ X0 @ sk_A @ sk_B))),
% 0.22/0.50      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.22/0.50  thf('15', plain,
% 0.22/0.50      ((~ (m2_connsp_2 @ sk_C @ sk_A @ sk_B)
% 0.22/0.50        | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['8', '14'])).
% 0.22/0.50  thf('16', plain, ((m2_connsp_2 @ sk_C @ sk_A @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('17', plain, ((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))),
% 0.22/0.50      inference('demod', [status(thm)], ['15', '16'])).
% 0.22/0.50  thf(t28_xboole_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.22/0.50  thf('18', plain,
% 0.22/0.50      (![X5 : $i, X6 : $i]:
% 0.22/0.50         (((k3_xboole_0 @ X5 @ X6) = (X5)) | ~ (r1_tarski @ X5 @ X6))),
% 0.22/0.50      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.22/0.50  thf('19', plain,
% 0.22/0.50      (((k3_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)) = (sk_B))),
% 0.22/0.50      inference('sup-', [status(thm)], ['17', '18'])).
% 0.22/0.50  thf(commutativity_k3_xboole_0, axiom,
% 0.22/0.50    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.22/0.50  thf('20', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.22/0.50      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.22/0.50  thf('21', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['1', '7'])).
% 0.22/0.50  thf(t44_tops_1, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( l1_pre_topc @ A ) =>
% 0.22/0.50       ( ![B:$i]:
% 0.22/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.50           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.22/0.50  thf('22', plain,
% 0.22/0.50      (![X7 : $i, X8 : $i]:
% 0.22/0.50         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.22/0.50          | (r1_tarski @ (k1_tops_1 @ X8 @ X7) @ X7)
% 0.22/0.50          | ~ (l1_pre_topc @ X8))),
% 0.22/0.50      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.22/0.50  thf('23', plain,
% 0.22/0.50      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C))),
% 0.22/0.50      inference('sup-', [status(thm)], ['21', '22'])).
% 0.22/0.50  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('25', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C)),
% 0.22/0.50      inference('demod', [status(thm)], ['23', '24'])).
% 0.22/0.50  thf(t108_xboole_1, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ B ) ))).
% 0.22/0.50  thf('26', plain,
% 0.22/0.50      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.22/0.50         (~ (r1_tarski @ X2 @ X3) | (r1_tarski @ (k3_xboole_0 @ X2 @ X4) @ X3))),
% 0.22/0.50      inference('cnf', [status(esa)], [t108_xboole_1])).
% 0.22/0.50  thf('27', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (r1_tarski @ (k3_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C) @ X0) @ sk_C)),
% 0.22/0.50      inference('sup-', [status(thm)], ['25', '26'])).
% 0.22/0.50  thf('28', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (r1_tarski @ (k3_xboole_0 @ X0 @ (k1_tops_1 @ sk_A @ sk_C)) @ sk_C)),
% 0.22/0.50      inference('sup+', [status(thm)], ['20', '27'])).
% 0.22/0.50  thf('29', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.22/0.50      inference('sup+', [status(thm)], ['19', '28'])).
% 0.22/0.50  thf('30', plain, ($false), inference('demod', [status(thm)], ['0', '29'])).
% 0.22/0.50  
% 0.22/0.50  % SZS output end Refutation
% 0.22/0.50  
% 0.22/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
