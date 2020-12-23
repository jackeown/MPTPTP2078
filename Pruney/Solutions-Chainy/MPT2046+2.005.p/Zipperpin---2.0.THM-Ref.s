%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xo872lyTQS

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:39 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 154 expanded)
%              Number of leaves         :   24 (  57 expanded)
%              Depth                    :   14
%              Number of atoms          :  561 (1773 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_yellow19_type,type,(
    k1_yellow19: $i > $i > $i )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_waybel_7_type,type,(
    r2_waybel_7: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(t5_yellow19,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( r2_waybel_7 @ A @ ( k1_yellow19 @ A @ B ) @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ( r2_waybel_7 @ A @ ( k1_yellow19 @ A @ B ) @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t5_yellow19])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_yellow19,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( m1_subset_1 @ ( k1_yellow19 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( l1_pre_topc @ X3 )
      | ~ ( v2_pre_topc @ X3 )
      | ( v2_struct_0 @ X3 )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X3 ) )
      | ( m1_subset_1 @ ( k1_yellow19 @ X3 @ X4 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X3 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow19])).

thf('3',plain,
    ( ( m1_subset_1 @ ( k1_yellow19 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( m1_subset_1 @ ( k1_yellow19 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ ( k1_yellow19 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ ( k1_yellow19 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf(t7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ! [D: $i] :
                ( ( m1_subset_1 @ D @ A )
               => ( ( r2_hidden @ D @ B )
                 => ( r2_hidden @ D @ C ) ) )
           => ( r1_tarski @ B @ C ) ) ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( r1_tarski @ X2 @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X2 @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      | ( r2_hidden @ ( sk_D @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) @ X0 )
      | ( r1_tarski @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ ( k1_yellow19 @ sk_A @ sk_B ) )
    | ( r2_hidden @ ( sk_D @ ( k1_yellow19 @ sk_A @ sk_B ) @ ( k1_yellow19 @ sk_A @ sk_B ) @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) @ ( k1_yellow19 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    m1_subset_1 @ ( k1_yellow19 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( r1_tarski @ X2 @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X2 @ X1 ) @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      | ~ ( r2_hidden @ ( sk_D @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) @ ( k1_yellow19 @ sk_A @ sk_B ) )
      | ( r1_tarski @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ ( k1_yellow19 @ sk_A @ sk_B ) )
    | ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ ( k1_yellow19 @ sk_A @ sk_B ) )
    | ~ ( m1_subset_1 @ ( k1_yellow19 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    m1_subset_1 @ ( k1_yellow19 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('18',plain,
    ( ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ ( k1_yellow19 @ sk_A @ sk_B ) )
    | ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ ( k1_yellow19 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ ( k1_yellow19 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    m1_subset_1 @ ( k1_yellow19 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf(t4_yellow19,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( ( v13_waybel_0 @ C @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) )
             => ( ( r2_waybel_7 @ A @ C @ B )
              <=> ( r1_tarski @ ( k1_yellow19 @ A @ B ) @ C ) ) ) ) ) )).

thf('21',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X8 ) )
      | ~ ( r1_tarski @ ( k1_yellow19 @ X8 @ X7 ) @ X9 )
      | ( r2_waybel_7 @ X8 @ X9 @ X7 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X8 ) ) ) ) )
      | ~ ( v13_waybel_0 @ X9 @ ( k3_yellow_1 @ ( k2_struct_0 @ X8 ) ) )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_yellow19])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v13_waybel_0 @ ( k1_yellow19 @ sk_A @ sk_B ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ( r2_waybel_7 @ sk_A @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 )
      | ~ ( r1_tarski @ ( k1_yellow19 @ sk_A @ X0 ) @ ( k1_yellow19 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_yellow19,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( ~ ( v1_xboole_0 @ ( k1_yellow19 @ A @ B ) )
        & ( v1_subset_1 @ ( k1_yellow19 @ A @ B ) @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) )
        & ( v2_waybel_0 @ ( k1_yellow19 @ A @ B ) @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) )
        & ( v13_waybel_0 @ ( k1_yellow19 @ A @ B ) @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) )).

thf('26',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X5 ) )
      | ( v13_waybel_0 @ ( k1_yellow19 @ X5 @ X6 ) @ ( k3_yellow_1 @ ( k2_struct_0 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[fc1_yellow19])).

thf('27',plain,
    ( ( v13_waybel_0 @ ( k1_yellow19 @ sk_A @ sk_B ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( v13_waybel_0 @ ( k1_yellow19 @ sk_A @ sk_B ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v13_waybel_0 @ ( k1_yellow19 @ sk_A @ sk_B ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_waybel_7 @ sk_A @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 )
      | ~ ( r1_tarski @ ( k1_yellow19 @ sk_A @ X0 ) @ ( k1_yellow19 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['22','23','24','32'])).

thf('34',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r2_waybel_7 @ sk_A @ ( k1_yellow19 @ sk_A @ sk_B ) @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['19','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( r2_waybel_7 @ sk_A @ ( k1_yellow19 @ sk_A @ sk_B ) @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ~ ( r2_waybel_7 @ sk_A @ ( k1_yellow19 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,(
    $false ),
    inference(demod,[status(thm)],['0','38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xo872lyTQS
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:06:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 25 iterations in 0.020s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.21/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.48  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.21/0.48  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.48  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.21/0.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.48  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.48  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.21/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.48  thf(k1_yellow19_type, type, k1_yellow19: $i > $i > $i).
% 0.21/0.48  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.21/0.48  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(r2_waybel_7_type, type, r2_waybel_7: $i > $i > $i > $o).
% 0.21/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.48  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.48  thf(t5_yellow19, conjecture,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.48           ( r2_waybel_7 @ A @ ( k1_yellow19 @ A @ B ) @ B ) ) ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i]:
% 0.21/0.48        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.48            ( l1_pre_topc @ A ) ) =>
% 0.21/0.48          ( ![B:$i]:
% 0.21/0.48            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.48              ( r2_waybel_7 @ A @ ( k1_yellow19 @ A @ B ) @ B ) ) ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t5_yellow19])).
% 0.21/0.48  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('1', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(dt_k1_yellow19, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.48         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.48       ( m1_subset_1 @
% 0.21/0.48         ( k1_yellow19 @ A @ B ) @ 
% 0.21/0.48         ( k1_zfmisc_1 @
% 0.21/0.48           ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ))).
% 0.21/0.48  thf('2', plain,
% 0.21/0.48      (![X3 : $i, X4 : $i]:
% 0.21/0.48         (~ (l1_pre_topc @ X3)
% 0.21/0.48          | ~ (v2_pre_topc @ X3)
% 0.21/0.48          | (v2_struct_0 @ X3)
% 0.21/0.48          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X3))
% 0.21/0.48          | (m1_subset_1 @ (k1_yellow19 @ X3 @ X4) @ 
% 0.21/0.48             (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X3))))))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_k1_yellow19])).
% 0.21/0.48  thf('3', plain,
% 0.21/0.48      (((m1_subset_1 @ (k1_yellow19 @ sk_A @ sk_B) @ 
% 0.21/0.48         (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.21/0.48        | (v2_struct_0 @ sk_A)
% 0.21/0.48        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.48        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.48  thf('4', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('6', plain,
% 0.21/0.48      (((m1_subset_1 @ (k1_yellow19 @ sk_A @ sk_B) @ 
% 0.21/0.48         (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.21/0.48        | (v2_struct_0 @ sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.21/0.48  thf('7', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('8', plain,
% 0.21/0.48      ((m1_subset_1 @ (k1_yellow19 @ sk_A @ sk_B) @ 
% 0.21/0.48        (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.21/0.48      inference('clc', [status(thm)], ['6', '7'])).
% 0.21/0.48  thf('9', plain,
% 0.21/0.48      ((m1_subset_1 @ (k1_yellow19 @ sk_A @ sk_B) @ 
% 0.21/0.48        (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.21/0.48      inference('clc', [status(thm)], ['6', '7'])).
% 0.21/0.48  thf(t7_subset_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.48       ( ![C:$i]:
% 0.21/0.48         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.48           ( ( ![D:$i]:
% 0.21/0.48               ( ( m1_subset_1 @ D @ A ) =>
% 0.21/0.48                 ( ( r2_hidden @ D @ B ) => ( r2_hidden @ D @ C ) ) ) ) =>
% 0.21/0.48             ( r1_tarski @ B @ C ) ) ) ) ))).
% 0.21/0.48  thf('10', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.21/0.48          | (r1_tarski @ X2 @ X0)
% 0.21/0.48          | (r2_hidden @ (sk_D @ X0 @ X2 @ X1) @ X2)
% 0.21/0.48          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X1)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t7_subset_1])).
% 0.21/0.48  thf('11', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ X0 @ 
% 0.21/0.48             (k1_zfmisc_1 @ 
% 0.21/0.48              (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.21/0.48          | (r2_hidden @ 
% 0.21/0.48             (sk_D @ (k1_yellow19 @ sk_A @ sk_B) @ X0 @ 
% 0.21/0.48              (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) @ 
% 0.21/0.48             X0)
% 0.21/0.48          | (r1_tarski @ X0 @ (k1_yellow19 @ sk_A @ sk_B)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.48  thf('12', plain,
% 0.21/0.48      (((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ (k1_yellow19 @ sk_A @ sk_B))
% 0.21/0.48        | (r2_hidden @ 
% 0.21/0.48           (sk_D @ (k1_yellow19 @ sk_A @ sk_B) @ (k1_yellow19 @ sk_A @ sk_B) @ 
% 0.21/0.48            (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) @ 
% 0.21/0.48           (k1_yellow19 @ sk_A @ sk_B)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['8', '11'])).
% 0.21/0.48  thf('13', plain,
% 0.21/0.48      ((m1_subset_1 @ (k1_yellow19 @ sk_A @ sk_B) @ 
% 0.21/0.48        (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.21/0.48      inference('clc', [status(thm)], ['6', '7'])).
% 0.21/0.48  thf('14', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.21/0.48          | (r1_tarski @ X2 @ X0)
% 0.21/0.48          | ~ (r2_hidden @ (sk_D @ X0 @ X2 @ X1) @ X0)
% 0.21/0.48          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X1)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t7_subset_1])).
% 0.21/0.48  thf('15', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ X0 @ 
% 0.21/0.48             (k1_zfmisc_1 @ 
% 0.21/0.48              (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.21/0.48          | ~ (r2_hidden @ 
% 0.21/0.48               (sk_D @ (k1_yellow19 @ sk_A @ sk_B) @ X0 @ 
% 0.21/0.48                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) @ 
% 0.21/0.48               (k1_yellow19 @ sk_A @ sk_B))
% 0.21/0.48          | (r1_tarski @ X0 @ (k1_yellow19 @ sk_A @ sk_B)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.48  thf('16', plain,
% 0.21/0.48      (((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ (k1_yellow19 @ sk_A @ sk_B))
% 0.21/0.48        | (r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ 
% 0.21/0.48           (k1_yellow19 @ sk_A @ sk_B))
% 0.21/0.48        | ~ (m1_subset_1 @ (k1_yellow19 @ sk_A @ sk_B) @ 
% 0.21/0.48             (k1_zfmisc_1 @ 
% 0.21/0.48              (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['12', '15'])).
% 0.21/0.48  thf('17', plain,
% 0.21/0.48      ((m1_subset_1 @ (k1_yellow19 @ sk_A @ sk_B) @ 
% 0.21/0.48        (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.21/0.48      inference('clc', [status(thm)], ['6', '7'])).
% 0.21/0.48  thf('18', plain,
% 0.21/0.48      (((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ (k1_yellow19 @ sk_A @ sk_B))
% 0.21/0.48        | (r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ 
% 0.21/0.48           (k1_yellow19 @ sk_A @ sk_B)))),
% 0.21/0.48      inference('demod', [status(thm)], ['16', '17'])).
% 0.21/0.48  thf('19', plain,
% 0.21/0.48      ((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ (k1_yellow19 @ sk_A @ sk_B))),
% 0.21/0.48      inference('simplify', [status(thm)], ['18'])).
% 0.21/0.48  thf('20', plain,
% 0.21/0.48      ((m1_subset_1 @ (k1_yellow19 @ sk_A @ sk_B) @ 
% 0.21/0.48        (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.21/0.48      inference('clc', [status(thm)], ['6', '7'])).
% 0.21/0.48  thf(t4_yellow19, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.48           ( ![C:$i]:
% 0.21/0.48             ( ( ( v13_waybel_0 @ C @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.21/0.48                 ( m1_subset_1 @
% 0.21/0.48                   C @ 
% 0.21/0.48                   ( k1_zfmisc_1 @
% 0.21/0.48                     ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.21/0.48               ( ( r2_waybel_7 @ A @ C @ B ) <=>
% 0.21/0.48                 ( r1_tarski @ ( k1_yellow19 @ A @ B ) @ C ) ) ) ) ) ) ))).
% 0.21/0.48  thf('21', plain,
% 0.21/0.48      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X8))
% 0.21/0.48          | ~ (r1_tarski @ (k1_yellow19 @ X8 @ X7) @ X9)
% 0.21/0.48          | (r2_waybel_7 @ X8 @ X9 @ X7)
% 0.21/0.48          | ~ (m1_subset_1 @ X9 @ 
% 0.21/0.48               (k1_zfmisc_1 @ 
% 0.21/0.48                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X8)))))
% 0.21/0.48          | ~ (v13_waybel_0 @ X9 @ (k3_yellow_1 @ (k2_struct_0 @ X8)))
% 0.21/0.48          | ~ (l1_pre_topc @ X8)
% 0.21/0.48          | ~ (v2_pre_topc @ X8)
% 0.21/0.48          | (v2_struct_0 @ X8))),
% 0.21/0.48      inference('cnf', [status(esa)], [t4_yellow19])).
% 0.21/0.48  thf('22', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((v2_struct_0 @ sk_A)
% 0.21/0.48          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.48          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.48          | ~ (v13_waybel_0 @ (k1_yellow19 @ sk_A @ sk_B) @ 
% 0.21/0.48               (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.21/0.48          | (r2_waybel_7 @ sk_A @ (k1_yellow19 @ sk_A @ sk_B) @ X0)
% 0.21/0.48          | ~ (r1_tarski @ (k1_yellow19 @ sk_A @ X0) @ 
% 0.21/0.48               (k1_yellow19 @ sk_A @ sk_B))
% 0.21/0.48          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.48  thf('23', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('25', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(fc1_yellow19, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.48         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.48       ( ( ~( v1_xboole_0 @ ( k1_yellow19 @ A @ B ) ) ) & 
% 0.21/0.48         ( v1_subset_1 @
% 0.21/0.48           ( k1_yellow19 @ A @ B ) @ 
% 0.21/0.48           ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.21/0.48         ( v2_waybel_0 @
% 0.21/0.48           ( k1_yellow19 @ A @ B ) @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.21/0.48         ( v13_waybel_0 @
% 0.21/0.48           ( k1_yellow19 @ A @ B ) @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ))).
% 0.21/0.48  thf('26', plain,
% 0.21/0.48      (![X5 : $i, X6 : $i]:
% 0.21/0.48         (~ (l1_pre_topc @ X5)
% 0.21/0.48          | ~ (v2_pre_topc @ X5)
% 0.21/0.48          | (v2_struct_0 @ X5)
% 0.21/0.48          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X5))
% 0.21/0.48          | (v13_waybel_0 @ (k1_yellow19 @ X5 @ X6) @ 
% 0.21/0.48             (k3_yellow_1 @ (k2_struct_0 @ X5))))),
% 0.21/0.48      inference('cnf', [status(esa)], [fc1_yellow19])).
% 0.21/0.48  thf('27', plain,
% 0.21/0.48      (((v13_waybel_0 @ (k1_yellow19 @ sk_A @ sk_B) @ 
% 0.21/0.48         (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.21/0.48        | (v2_struct_0 @ sk_A)
% 0.21/0.48        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.48        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['25', '26'])).
% 0.21/0.48  thf('28', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('30', plain,
% 0.21/0.48      (((v13_waybel_0 @ (k1_yellow19 @ sk_A @ sk_B) @ 
% 0.21/0.48         (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.21/0.48        | (v2_struct_0 @ sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.21/0.48  thf('31', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('32', plain,
% 0.21/0.48      ((v13_waybel_0 @ (k1_yellow19 @ sk_A @ sk_B) @ 
% 0.21/0.48        (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.21/0.48      inference('clc', [status(thm)], ['30', '31'])).
% 0.21/0.48  thf('33', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((v2_struct_0 @ sk_A)
% 0.21/0.48          | (r2_waybel_7 @ sk_A @ (k1_yellow19 @ sk_A @ sk_B) @ X0)
% 0.21/0.48          | ~ (r1_tarski @ (k1_yellow19 @ sk_A @ X0) @ 
% 0.21/0.48               (k1_yellow19 @ sk_A @ sk_B))
% 0.21/0.48          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.48      inference('demod', [status(thm)], ['22', '23', '24', '32'])).
% 0.21/0.48  thf('34', plain,
% 0.21/0.48      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.21/0.48        | (r2_waybel_7 @ sk_A @ (k1_yellow19 @ sk_A @ sk_B) @ sk_B)
% 0.21/0.48        | (v2_struct_0 @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['19', '33'])).
% 0.21/0.48  thf('35', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('36', plain,
% 0.21/0.48      (((r2_waybel_7 @ sk_A @ (k1_yellow19 @ sk_A @ sk_B) @ sk_B)
% 0.21/0.48        | (v2_struct_0 @ sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['34', '35'])).
% 0.21/0.48  thf('37', plain,
% 0.21/0.48      (~ (r2_waybel_7 @ sk_A @ (k1_yellow19 @ sk_A @ sk_B) @ sk_B)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('38', plain, ((v2_struct_0 @ sk_A)),
% 0.21/0.48      inference('clc', [status(thm)], ['36', '37'])).
% 0.21/0.48  thf('39', plain, ($false), inference('demod', [status(thm)], ['0', '38'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
