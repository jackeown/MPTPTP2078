%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dWXpgy0YaF

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:18 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   64 (  98 expanded)
%              Number of leaves         :   25 (  41 expanded)
%              Depth                    :   10
%              Number of atoms          :  431 ( 829 expanded)
%              Number of equality atoms :   16 (  18 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m2_connsp_2_type,type,(
    m2_connsp_2: $i > $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(t43_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( k1_tops_1 @ A @ ( k2_struct_0 @ A ) )
        = ( k2_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X13: $i] :
      ( ( ( k1_tops_1 @ X13 @ ( k2_struct_0 @ X13 ) )
        = ( k2_struct_0 @ X13 ) )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t43_tops_1])).

thf(dt_k2_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( m1_subset_1 @ ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X9: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X9 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

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

thf('2',plain,(
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

thf('3',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( r1_tarski @ X14 @ ( k1_tops_1 @ X15 @ X16 ) )
      | ( m2_connsp_2 @ X16 @ X15 @ X14 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[d2_connsp_2])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( m2_connsp_2 @ X0 @ sk_A @ sk_B )
      | ~ ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( m2_connsp_2 @ X0 @ sk_A @ sk_B )
      | ~ ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ~ ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
    | ( m2_connsp_2 @ ( k2_struct_0 @ sk_A ) @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf('9',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('10',plain,(
    ! [X10: $i] :
      ( ( l1_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('11',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
    | ( m2_connsp_2 @ ( k2_struct_0 @ sk_A ) @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('13',plain,(
    ~ ( m2_connsp_2 @ ( k2_struct_0 @ sk_A ) @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ~ ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['12','13'])).

thf('15',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_struct_0 @ sk_A ) )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['0','14'])).

thf('16',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ~ ( r1_tarski @ sk_B @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,(
    ! [X9: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X9 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('20',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( ( k7_subset_1 @ X5 @ X4 @ X6 )
        = ( k4_xboole_0 @ X4 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) @ X1 )
        = ( k4_xboole_0 @ ( k2_struct_0 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) @ X1 )
        = ( k4_xboole_0 @ ( k2_struct_0 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('23',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t22_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) )
            = B ) ) ) )).

thf('24',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ X12 ) @ ( k2_struct_0 @ X12 ) @ ( k7_subset_1 @ ( u1_struct_0 @ X12 ) @ ( k2_struct_0 @ X12 ) @ X11 ) )
        = X11 )
      | ~ ( l1_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t22_pre_topc])).

thf('25',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = sk_B ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['9','10'])).

thf('27',plain,
    ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = sk_B )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['22','27'])).

thf('29',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['9','10'])).

thf('30',plain,
    ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = sk_B )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['21','30'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('32',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X2 @ X3 ) )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('33',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['9','10'])).

thf('34',plain,
    ( ( k3_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['31','32','33'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('36',plain,(
    r1_tarski @ sk_B @ ( k2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    $false ),
    inference(demod,[status(thm)],['18','36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dWXpgy0YaF
% 0.14/0.35  % Computer   : n012.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:26:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.48  % Solved by: fo/fo7.sh
% 0.22/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.48  % done 28 iterations in 0.017s
% 0.22/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.48  % SZS output start Refutation
% 0.22/0.48  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.22/0.48  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.48  thf(m2_connsp_2_type, type, m2_connsp_2: $i > $i > $i > $o).
% 0.22/0.48  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.48  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.22/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.48  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.22/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.48  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.22/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.48  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.22/0.48  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.48  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.22/0.48  thf(t43_tops_1, axiom,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.48       ( ( k1_tops_1 @ A @ ( k2_struct_0 @ A ) ) = ( k2_struct_0 @ A ) ) ))).
% 0.22/0.48  thf('0', plain,
% 0.22/0.48      (![X13 : $i]:
% 0.22/0.48         (((k1_tops_1 @ X13 @ (k2_struct_0 @ X13)) = (k2_struct_0 @ X13))
% 0.22/0.48          | ~ (l1_pre_topc @ X13)
% 0.22/0.48          | ~ (v2_pre_topc @ X13))),
% 0.22/0.48      inference('cnf', [status(esa)], [t43_tops_1])).
% 0.22/0.48  thf(dt_k2_struct_0, axiom,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ( l1_struct_0 @ A ) =>
% 0.22/0.48       ( m1_subset_1 @
% 0.22/0.48         ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.22/0.48  thf('1', plain,
% 0.22/0.48      (![X9 : $i]:
% 0.22/0.48         ((m1_subset_1 @ (k2_struct_0 @ X9) @ 
% 0.22/0.48           (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.22/0.48          | ~ (l1_struct_0 @ X9))),
% 0.22/0.48      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.22/0.48  thf(t35_connsp_2, conjecture,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.48       ( ![B:$i]:
% 0.22/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.48           ( m2_connsp_2 @ ( k2_struct_0 @ A ) @ A @ B ) ) ) ))).
% 0.22/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.48    (~( ![A:$i]:
% 0.22/0.48        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.22/0.48            ( l1_pre_topc @ A ) ) =>
% 0.22/0.48          ( ![B:$i]:
% 0.22/0.48            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.48              ( m2_connsp_2 @ ( k2_struct_0 @ A ) @ A @ B ) ) ) ) )),
% 0.22/0.48    inference('cnf.neg', [status(esa)], [t35_connsp_2])).
% 0.22/0.48  thf('2', plain,
% 0.22/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf(d2_connsp_2, axiom,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.48       ( ![B:$i]:
% 0.22/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.48           ( ![C:$i]:
% 0.22/0.48             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.48               ( ( m2_connsp_2 @ C @ A @ B ) <=>
% 0.22/0.48                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.22/0.48  thf('3', plain,
% 0.22/0.48      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.22/0.48         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.22/0.48          | ~ (r1_tarski @ X14 @ (k1_tops_1 @ X15 @ X16))
% 0.22/0.48          | (m2_connsp_2 @ X16 @ X15 @ X14)
% 0.22/0.48          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.22/0.48          | ~ (l1_pre_topc @ X15)
% 0.22/0.48          | ~ (v2_pre_topc @ X15))),
% 0.22/0.48      inference('cnf', [status(esa)], [d2_connsp_2])).
% 0.22/0.48  thf('4', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         (~ (v2_pre_topc @ sk_A)
% 0.22/0.48          | ~ (l1_pre_topc @ sk_A)
% 0.22/0.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.48          | (m2_connsp_2 @ X0 @ sk_A @ sk_B)
% 0.22/0.48          | ~ (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0)))),
% 0.22/0.48      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.48  thf('5', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('7', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.48          | (m2_connsp_2 @ X0 @ sk_A @ sk_B)
% 0.22/0.48          | ~ (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0)))),
% 0.22/0.48      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.22/0.48  thf('8', plain,
% 0.22/0.48      ((~ (l1_struct_0 @ sk_A)
% 0.22/0.48        | ~ (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ (k2_struct_0 @ sk_A)))
% 0.22/0.48        | (m2_connsp_2 @ (k2_struct_0 @ sk_A) @ sk_A @ sk_B))),
% 0.22/0.48      inference('sup-', [status(thm)], ['1', '7'])).
% 0.22/0.48  thf('9', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf(dt_l1_pre_topc, axiom,
% 0.22/0.48    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.22/0.48  thf('10', plain,
% 0.22/0.48      (![X10 : $i]: ((l1_struct_0 @ X10) | ~ (l1_pre_topc @ X10))),
% 0.22/0.48      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.22/0.48  thf('11', plain, ((l1_struct_0 @ sk_A)),
% 0.22/0.48      inference('sup-', [status(thm)], ['9', '10'])).
% 0.22/0.48  thf('12', plain,
% 0.22/0.48      ((~ (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ (k2_struct_0 @ sk_A)))
% 0.22/0.48        | (m2_connsp_2 @ (k2_struct_0 @ sk_A) @ sk_A @ sk_B))),
% 0.22/0.48      inference('demod', [status(thm)], ['8', '11'])).
% 0.22/0.48  thf('13', plain, (~ (m2_connsp_2 @ (k2_struct_0 @ sk_A) @ sk_A @ sk_B)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('14', plain,
% 0.22/0.48      (~ (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ (k2_struct_0 @ sk_A)))),
% 0.22/0.48      inference('clc', [status(thm)], ['12', '13'])).
% 0.22/0.48  thf('15', plain,
% 0.22/0.48      ((~ (r1_tarski @ sk_B @ (k2_struct_0 @ sk_A))
% 0.22/0.48        | ~ (v2_pre_topc @ sk_A)
% 0.22/0.48        | ~ (l1_pre_topc @ sk_A))),
% 0.22/0.48      inference('sup-', [status(thm)], ['0', '14'])).
% 0.22/0.48  thf('16', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('18', plain, (~ (r1_tarski @ sk_B @ (k2_struct_0 @ sk_A))),
% 0.22/0.48      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.22/0.48  thf('19', plain,
% 0.22/0.48      (![X9 : $i]:
% 0.22/0.48         ((m1_subset_1 @ (k2_struct_0 @ X9) @ 
% 0.22/0.48           (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.22/0.48          | ~ (l1_struct_0 @ X9))),
% 0.22/0.48      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.22/0.48  thf(redefinition_k7_subset_1, axiom,
% 0.22/0.48    (![A:$i,B:$i,C:$i]:
% 0.22/0.48     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.48       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.22/0.48  thf('20', plain,
% 0.22/0.48      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.22/0.48         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.22/0.48          | ((k7_subset_1 @ X5 @ X4 @ X6) = (k4_xboole_0 @ X4 @ X6)))),
% 0.22/0.48      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.22/0.48  thf('21', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i]:
% 0.22/0.48         (~ (l1_struct_0 @ X0)
% 0.22/0.48          | ((k7_subset_1 @ (u1_struct_0 @ X0) @ (k2_struct_0 @ X0) @ X1)
% 0.22/0.48              = (k4_xboole_0 @ (k2_struct_0 @ X0) @ X1)))),
% 0.22/0.48      inference('sup-', [status(thm)], ['19', '20'])).
% 0.22/0.48  thf('22', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i]:
% 0.22/0.48         (~ (l1_struct_0 @ X0)
% 0.22/0.48          | ((k7_subset_1 @ (u1_struct_0 @ X0) @ (k2_struct_0 @ X0) @ X1)
% 0.22/0.48              = (k4_xboole_0 @ (k2_struct_0 @ X0) @ X1)))),
% 0.22/0.48      inference('sup-', [status(thm)], ['19', '20'])).
% 0.22/0.48  thf('23', plain,
% 0.22/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf(t22_pre_topc, axiom,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ( l1_struct_0 @ A ) =>
% 0.22/0.48       ( ![B:$i]:
% 0.22/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.48           ( ( k7_subset_1 @
% 0.22/0.48               ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ 
% 0.22/0.48               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) ) =
% 0.22/0.48             ( B ) ) ) ) ))).
% 0.22/0.48  thf('24', plain,
% 0.22/0.48      (![X11 : $i, X12 : $i]:
% 0.22/0.48         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.22/0.48          | ((k7_subset_1 @ (u1_struct_0 @ X12) @ (k2_struct_0 @ X12) @ 
% 0.22/0.48              (k7_subset_1 @ (u1_struct_0 @ X12) @ (k2_struct_0 @ X12) @ X11))
% 0.22/0.48              = (X11))
% 0.22/0.48          | ~ (l1_struct_0 @ X12))),
% 0.22/0.48      inference('cnf', [status(esa)], [t22_pre_topc])).
% 0.22/0.48  thf('25', plain,
% 0.22/0.48      ((~ (l1_struct_0 @ sk_A)
% 0.22/0.48        | ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ 
% 0.22/0.48            (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.22/0.48            = (sk_B)))),
% 0.22/0.48      inference('sup-', [status(thm)], ['23', '24'])).
% 0.22/0.48  thf('26', plain, ((l1_struct_0 @ sk_A)),
% 0.22/0.48      inference('sup-', [status(thm)], ['9', '10'])).
% 0.22/0.48  thf('27', plain,
% 0.22/0.48      (((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ 
% 0.22/0.48         (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.22/0.48         = (sk_B))),
% 0.22/0.48      inference('demod', [status(thm)], ['25', '26'])).
% 0.22/0.48  thf('28', plain,
% 0.22/0.48      ((((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ 
% 0.22/0.48          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.22/0.48          = (sk_B))
% 0.22/0.48        | ~ (l1_struct_0 @ sk_A))),
% 0.22/0.48      inference('sup+', [status(thm)], ['22', '27'])).
% 0.22/0.48  thf('29', plain, ((l1_struct_0 @ sk_A)),
% 0.22/0.48      inference('sup-', [status(thm)], ['9', '10'])).
% 0.22/0.48  thf('30', plain,
% 0.22/0.48      (((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ 
% 0.22/0.48         (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.22/0.48         = (sk_B))),
% 0.22/0.48      inference('demod', [status(thm)], ['28', '29'])).
% 0.22/0.48  thf('31', plain,
% 0.22/0.48      ((((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ 
% 0.22/0.48          (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) = (sk_B))
% 0.22/0.48        | ~ (l1_struct_0 @ sk_A))),
% 0.22/0.48      inference('sup+', [status(thm)], ['21', '30'])).
% 0.22/0.48  thf(t48_xboole_1, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.22/0.48  thf('32', plain,
% 0.22/0.48      (![X2 : $i, X3 : $i]:
% 0.22/0.48         ((k4_xboole_0 @ X2 @ (k4_xboole_0 @ X2 @ X3))
% 0.22/0.48           = (k3_xboole_0 @ X2 @ X3))),
% 0.22/0.48      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.22/0.48  thf('33', plain, ((l1_struct_0 @ sk_A)),
% 0.22/0.48      inference('sup-', [status(thm)], ['9', '10'])).
% 0.22/0.48  thf('34', plain, (((k3_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) = (sk_B))),
% 0.22/0.48      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.22/0.48  thf(t17_xboole_1, axiom,
% 0.22/0.48    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.22/0.48  thf('35', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.22/0.48      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.22/0.48  thf('36', plain, ((r1_tarski @ sk_B @ (k2_struct_0 @ sk_A))),
% 0.22/0.48      inference('sup+', [status(thm)], ['34', '35'])).
% 0.22/0.48  thf('37', plain, ($false), inference('demod', [status(thm)], ['18', '36'])).
% 0.22/0.48  
% 0.22/0.48  % SZS output end Refutation
% 0.22/0.48  
% 0.22/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
