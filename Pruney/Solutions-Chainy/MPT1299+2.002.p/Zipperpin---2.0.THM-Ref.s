%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8t4eLD5Erg

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:15 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   43 (  76 expanded)
%              Number of leaves         :   13 (  27 expanded)
%              Depth                    :    8
%              Number of atoms          :  346 ( 833 expanded)
%              Number of equality atoms :    4 (   6 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_tops_2_type,type,(
    v2_tops_2: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_tops_2_type,type,(
    v1_tops_2: $i > $i > $o )).

thf(k7_setfam_1_type,type,(
    k7_setfam_1: $i > $i > $i )).

thf(t17_tops_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v1_tops_2 @ B @ A )
          <=> ( v2_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ( ( v1_tops_2 @ B @ A )
            <=> ( v2_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t17_tops_2])).

thf('0',plain,
    ( ~ ( v2_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v1_tops_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v2_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v1_tops_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( v2_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v1_tops_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v1_tops_2 @ sk_B @ sk_A )
   <= ( v1_tops_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k7_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k7_setfam_1 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_setfam_1])).

thf('6',plain,(
    m1_subset_1 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t16_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v2_tops_2 @ B @ A )
          <=> ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('7',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) ) )
      | ~ ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ X5 ) @ X4 ) @ X5 )
      | ( v2_tops_2 @ X4 @ X5 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[t16_tops_2])).

thf('8',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k7_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) )
        = B ) ) )).

thf('11',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k7_setfam_1 @ X3 @ ( k7_setfam_1 @ X3 @ X2 ) )
        = X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k7_setfam_1])).

thf('12',plain,
    ( ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( v2_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v1_tops_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['8','9','12'])).

thf('14',plain,
    ( ( v2_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v1_tops_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['3','13'])).

thf('15',plain,
    ( ~ ( v2_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ~ ( v2_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('16',plain,
    ( ( v2_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v1_tops_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( v2_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v1_tops_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('18',plain,
    ( ( v2_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v2_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('19',plain,(
    m1_subset_1 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('20',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) ) )
      | ~ ( v2_tops_2 @ X4 @ X5 )
      | ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ X5 ) @ X4 ) @ X5 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[t16_tops_2])).

thf('21',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ sk_A )
    | ~ ( v2_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['10','11'])).

thf('24',plain,
    ( ( v1_tops_2 @ sk_B @ sk_A )
    | ~ ( v2_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,
    ( ( v1_tops_2 @ sk_B @ sk_A )
   <= ( v2_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['18','24'])).

thf('26',plain,
    ( ~ ( v1_tops_2 @ sk_B @ sk_A )
   <= ~ ( v1_tops_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('27',plain,
    ( ~ ( v2_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v1_tops_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','16','17','27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8t4eLD5Erg
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:41:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 23 iterations in 0.014s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.47  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.47  thf(v2_tops_2_type, type, v2_tops_2: $i > $i > $o).
% 0.21/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.47  thf(v1_tops_2_type, type, v1_tops_2: $i > $i > $o).
% 0.21/0.47  thf(k7_setfam_1_type, type, k7_setfam_1: $i > $i > $i).
% 0.21/0.47  thf(t17_tops_2, conjecture,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( l1_pre_topc @ A ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( m1_subset_1 @
% 0.21/0.47             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.47           ( ( v1_tops_2 @ B @ A ) <=>
% 0.21/0.47             ( v2_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i]:
% 0.21/0.47        ( ( l1_pre_topc @ A ) =>
% 0.21/0.47          ( ![B:$i]:
% 0.21/0.47            ( ( m1_subset_1 @
% 0.21/0.47                B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.47              ( ( v1_tops_2 @ B @ A ) <=>
% 0.21/0.47                ( v2_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t17_tops_2])).
% 0.21/0.47  thf('0', plain,
% 0.21/0.47      ((~ (v2_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.21/0.47        | ~ (v1_tops_2 @ sk_B @ sk_A))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('1', plain,
% 0.21/0.47      (~ ((v2_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)) | 
% 0.21/0.47       ~ ((v1_tops_2 @ sk_B @ sk_A))),
% 0.21/0.47      inference('split', [status(esa)], ['0'])).
% 0.21/0.47  thf('2', plain,
% 0.21/0.47      (((v2_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.21/0.47        | (v1_tops_2 @ sk_B @ sk_A))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('3', plain,
% 0.21/0.47      (((v1_tops_2 @ sk_B @ sk_A)) <= (((v1_tops_2 @ sk_B @ sk_A)))),
% 0.21/0.47      inference('split', [status(esa)], ['2'])).
% 0.21/0.47  thf('4', plain,
% 0.21/0.47      ((m1_subset_1 @ sk_B @ 
% 0.21/0.47        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(dt_k7_setfam_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.47       ( m1_subset_1 @
% 0.21/0.47         ( k7_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.21/0.47  thf('5', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         ((m1_subset_1 @ (k7_setfam_1 @ X0 @ X1) @ 
% 0.21/0.47           (k1_zfmisc_1 @ (k1_zfmisc_1 @ X0)))
% 0.21/0.47          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X0))))),
% 0.21/0.47      inference('cnf', [status(esa)], [dt_k7_setfam_1])).
% 0.21/0.47  thf('6', plain,
% 0.21/0.47      ((m1_subset_1 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.47        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.47  thf(t16_tops_2, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( l1_pre_topc @ A ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( m1_subset_1 @
% 0.21/0.47             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.47           ( ( v2_tops_2 @ B @ A ) <=>
% 0.21/0.47             ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.21/0.47  thf('7', plain,
% 0.21/0.47      (![X4 : $i, X5 : $i]:
% 0.21/0.47         (~ (m1_subset_1 @ X4 @ 
% 0.21/0.47             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5))))
% 0.21/0.47          | ~ (v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ X5) @ X4) @ X5)
% 0.21/0.47          | (v2_tops_2 @ X4 @ X5)
% 0.21/0.47          | ~ (l1_pre_topc @ X5))),
% 0.21/0.47      inference('cnf', [status(esa)], [t16_tops_2])).
% 0.21/0.47  thf('8', plain,
% 0.21/0.47      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.47        | (v2_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.21/0.47        | ~ (v1_tops_2 @ 
% 0.21/0.47             (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.47              (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.21/0.47             sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.47  thf('9', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('10', plain,
% 0.21/0.47      ((m1_subset_1 @ sk_B @ 
% 0.21/0.47        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(involutiveness_k7_setfam_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.47       ( ( k7_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) ) = ( B ) ) ))).
% 0.21/0.47  thf('11', plain,
% 0.21/0.47      (![X2 : $i, X3 : $i]:
% 0.21/0.47         (((k7_setfam_1 @ X3 @ (k7_setfam_1 @ X3 @ X2)) = (X2))
% 0.21/0.47          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X3))))),
% 0.21/0.47      inference('cnf', [status(esa)], [involutiveness_k7_setfam_1])).
% 0.21/0.47  thf('12', plain,
% 0.21/0.47      (((k7_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.47         (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 0.21/0.47      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.47  thf('13', plain,
% 0.21/0.47      (((v2_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.21/0.47        | ~ (v1_tops_2 @ sk_B @ sk_A))),
% 0.21/0.47      inference('demod', [status(thm)], ['8', '9', '12'])).
% 0.21/0.47  thf('14', plain,
% 0.21/0.47      (((v2_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 0.21/0.47         <= (((v1_tops_2 @ sk_B @ sk_A)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['3', '13'])).
% 0.21/0.47  thf('15', plain,
% 0.21/0.47      ((~ (v2_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 0.21/0.47         <= (~
% 0.21/0.47             ((v2_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 0.21/0.47      inference('split', [status(esa)], ['0'])).
% 0.21/0.47  thf('16', plain,
% 0.21/0.47      (((v2_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)) | 
% 0.21/0.47       ~ ((v1_tops_2 @ sk_B @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.47  thf('17', plain,
% 0.21/0.47      (((v2_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)) | 
% 0.21/0.47       ((v1_tops_2 @ sk_B @ sk_A))),
% 0.21/0.47      inference('split', [status(esa)], ['2'])).
% 0.21/0.47  thf('18', plain,
% 0.21/0.47      (((v2_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 0.21/0.47         <= (((v2_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 0.21/0.47      inference('split', [status(esa)], ['2'])).
% 0.21/0.47  thf('19', plain,
% 0.21/0.47      ((m1_subset_1 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.47        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.47  thf('20', plain,
% 0.21/0.47      (![X4 : $i, X5 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ X4 @ 
% 0.21/0.48             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5))))
% 0.21/0.48          | ~ (v2_tops_2 @ X4 @ X5)
% 0.21/0.48          | (v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ X5) @ X4) @ X5)
% 0.21/0.48          | ~ (l1_pre_topc @ X5))),
% 0.21/0.48      inference('cnf', [status(esa)], [t16_tops_2])).
% 0.21/0.48  thf('21', plain,
% 0.21/0.48      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.48        | (v1_tops_2 @ 
% 0.21/0.48           (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.48            (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.21/0.48           sk_A)
% 0.21/0.48        | ~ (v2_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.48  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('23', plain,
% 0.21/0.48      (((k7_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.48         (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 0.21/0.48      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.48  thf('24', plain,
% 0.21/0.48      (((v1_tops_2 @ sk_B @ sk_A)
% 0.21/0.48        | ~ (v2_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.21/0.48  thf('25', plain,
% 0.21/0.48      (((v1_tops_2 @ sk_B @ sk_A))
% 0.21/0.48         <= (((v2_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['18', '24'])).
% 0.21/0.48  thf('26', plain,
% 0.21/0.48      ((~ (v1_tops_2 @ sk_B @ sk_A)) <= (~ ((v1_tops_2 @ sk_B @ sk_A)))),
% 0.21/0.48      inference('split', [status(esa)], ['0'])).
% 0.21/0.48  thf('27', plain,
% 0.21/0.48      (~ ((v2_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)) | 
% 0.21/0.48       ((v1_tops_2 @ sk_B @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['25', '26'])).
% 0.21/0.48  thf('28', plain, ($false),
% 0.21/0.48      inference('sat_resolution*', [status(thm)], ['1', '16', '17', '27'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
