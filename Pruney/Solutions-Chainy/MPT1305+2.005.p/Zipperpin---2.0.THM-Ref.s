%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.L8YFjVsyvG

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:23 EST 2020

% Result     : Theorem 1.64s
% Output     : Refutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :   60 (  91 expanded)
%              Number of leaves         :   17 (  34 expanded)
%              Depth                    :    9
%              Number of atoms          :  645 (1475 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_setfam_1_type,type,(
    k7_setfam_1: $i > $i > $i )).

thf(v1_tops_2_type,type,(
    v1_tops_2: $i > $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_tops_2_type,type,(
    v2_tops_2: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t23_tops_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
             => ( ( ( v2_tops_2 @ B @ A )
                  & ( v2_tops_2 @ C @ A ) )
               => ( v2_tops_2 @ ( k4_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
               => ( ( ( v2_tops_2 @ B @ A )
                    & ( v2_tops_2 @ C @ A ) )
                 => ( v2_tops_2 @ ( k4_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t23_tops_2])).

thf('0',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X1 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X1 @ X0 @ X2 ) @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ ( k4_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf(t16_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v2_tops_2 @ B @ A )
          <=> ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('5',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ X9 ) @ X8 ) @ X9 )
      | ( v2_tops_2 @ X8 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[t16_tops_2])).

thf('6',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_2 @ ( k4_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_C ) @ sk_A )
    | ~ ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_C ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( v2_tops_2 @ ( k4_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_C ) @ sk_A )
    | ~ ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_C ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ~ ( v2_tops_2 @ ( k4_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_C ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ~ ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_C ) ) @ sk_A ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k7_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ) )).

thf('12',plain,(
    ! [X3: $i,X4: $i] :
      ( ( m1_subset_1 @ ( k7_setfam_1 @ X3 @ X4 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X3 ) ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_setfam_1])).

thf('13',plain,(
    m1_subset_1 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X3: $i,X4: $i] :
      ( ( m1_subset_1 @ ( k7_setfam_1 @ X3 @ X4 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X3 ) ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_setfam_1])).

thf('16',plain,(
    m1_subset_1 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t20_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
             => ( ( ( v1_tops_2 @ B @ A )
                  & ( v1_tops_2 @ C @ A ) )
               => ( v1_tops_2 @ ( k4_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) @ A ) ) ) ) ) )).

thf('17',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) ) )
      | ~ ( v1_tops_2 @ X10 @ X11 )
      | ~ ( v1_tops_2 @ X12 @ X11 )
      | ( v1_tops_2 @ ( k4_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) @ X10 @ X12 ) @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) ) )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t20_tops_2])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v1_tops_2 @ ( k4_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ X0 ) @ sk_A )
      | ~ ( v1_tops_2 @ X0 @ sk_A )
      | ~ ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( v2_tops_2 @ X8 @ X9 )
      | ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ X9 ) @ X8 ) @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[t16_tops_2])).

thf('22',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v2_tops_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v2_tops_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v1_tops_2 @ ( k4_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ X0 ) @ sk_A )
      | ~ ( v1_tops_2 @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','19','25'])).

thf('27',plain,
    ( ~ ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ sk_A )
    | ( v1_tops_2 @ ( k4_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['13','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( v2_tops_2 @ X8 @ X9 )
      | ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ X9 ) @ X8 ) @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[t16_tops_2])).

thf('30',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ sk_A )
    | ~ ( v2_tops_2 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v2_tops_2 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,(
    v1_tops_2 @ ( k4_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) @ sk_A ),
    inference(demod,[status(thm)],['27','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t54_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
         => ( ( k7_setfam_1 @ A @ ( k4_subset_1 @ ( k1_zfmisc_1 @ A ) @ B @ C ) )
            = ( k4_subset_1 @ ( k1_zfmisc_1 @ A ) @ ( k7_setfam_1 @ A @ B ) @ ( k7_setfam_1 @ A @ C ) ) ) ) ) )).

thf('37',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X6 ) ) )
      | ( ( k7_setfam_1 @ X6 @ ( k4_subset_1 @ ( k1_zfmisc_1 @ X6 ) @ X7 @ X5 ) )
        = ( k4_subset_1 @ ( k1_zfmisc_1 @ X6 ) @ ( k7_setfam_1 @ X6 @ X7 ) @ ( k7_setfam_1 @ X6 @ X5 ) ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[t54_setfam_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 @ sk_C ) )
        = ( k4_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_C ) )
    = ( k4_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,(
    v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_C ) ) @ sk_A ),
    inference(demod,[status(thm)],['34','39'])).

thf('41',plain,(
    $false ),
    inference(demod,[status(thm)],['10','40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.L8YFjVsyvG
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:56:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 1.64/1.90  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.64/1.90  % Solved by: fo/fo7.sh
% 1.64/1.90  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.64/1.90  % done 559 iterations in 1.423s
% 1.64/1.90  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.64/1.90  % SZS output start Refutation
% 1.64/1.90  thf(k7_setfam_1_type, type, k7_setfam_1: $i > $i > $i).
% 1.64/1.90  thf(v1_tops_2_type, type, v1_tops_2: $i > $i > $o).
% 1.64/1.90  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 1.64/1.90  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.64/1.90  thf(v2_tops_2_type, type, v2_tops_2: $i > $i > $o).
% 1.64/1.90  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.64/1.90  thf(sk_A_type, type, sk_A: $i).
% 1.64/1.90  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.64/1.90  thf(sk_C_type, type, sk_C: $i).
% 1.64/1.90  thf(sk_B_type, type, sk_B: $i).
% 1.64/1.90  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.64/1.90  thf(t23_tops_2, conjecture,
% 1.64/1.90    (![A:$i]:
% 1.64/1.90     ( ( l1_pre_topc @ A ) =>
% 1.64/1.90       ( ![B:$i]:
% 1.64/1.90         ( ( m1_subset_1 @
% 1.64/1.90             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.64/1.90           ( ![C:$i]:
% 1.64/1.90             ( ( m1_subset_1 @
% 1.64/1.90                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.64/1.90               ( ( ( v2_tops_2 @ B @ A ) & ( v2_tops_2 @ C @ A ) ) =>
% 1.64/1.90                 ( v2_tops_2 @
% 1.64/1.90                   ( k4_subset_1 @
% 1.64/1.90                     ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) @ 
% 1.64/1.90                   A ) ) ) ) ) ) ))).
% 1.64/1.90  thf(zf_stmt_0, negated_conjecture,
% 1.64/1.90    (~( ![A:$i]:
% 1.64/1.90        ( ( l1_pre_topc @ A ) =>
% 1.64/1.90          ( ![B:$i]:
% 1.64/1.90            ( ( m1_subset_1 @
% 1.64/1.90                B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.64/1.90              ( ![C:$i]:
% 1.64/1.90                ( ( m1_subset_1 @
% 1.64/1.90                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.64/1.90                  ( ( ( v2_tops_2 @ B @ A ) & ( v2_tops_2 @ C @ A ) ) =>
% 1.64/1.90                    ( v2_tops_2 @
% 1.64/1.90                      ( k4_subset_1 @
% 1.64/1.90                        ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) @ 
% 1.64/1.90                      A ) ) ) ) ) ) ) )),
% 1.64/1.90    inference('cnf.neg', [status(esa)], [t23_tops_2])).
% 1.64/1.90  thf('0', plain,
% 1.64/1.90      ((m1_subset_1 @ sk_C @ 
% 1.64/1.90        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.64/1.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.90  thf('1', plain,
% 1.64/1.90      ((m1_subset_1 @ sk_B @ 
% 1.64/1.90        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.64/1.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.90  thf(dt_k4_subset_1, axiom,
% 1.64/1.90    (![A:$i,B:$i,C:$i]:
% 1.64/1.90     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 1.64/1.90         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.64/1.90       ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.64/1.90  thf('2', plain,
% 1.64/1.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.64/1.90         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 1.64/1.90          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X1))
% 1.64/1.90          | (m1_subset_1 @ (k4_subset_1 @ X1 @ X0 @ X2) @ (k1_zfmisc_1 @ X1)))),
% 1.64/1.90      inference('cnf', [status(esa)], [dt_k4_subset_1])).
% 1.64/1.90  thf('3', plain,
% 1.64/1.90      (![X0 : $i]:
% 1.64/1.90         ((m1_subset_1 @ 
% 1.64/1.90           (k4_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ X0) @ 
% 1.64/1.90           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 1.64/1.90          | ~ (m1_subset_1 @ X0 @ 
% 1.64/1.90               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 1.64/1.90      inference('sup-', [status(thm)], ['1', '2'])).
% 1.64/1.90  thf('4', plain,
% 1.64/1.90      ((m1_subset_1 @ 
% 1.64/1.90        (k4_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_C) @ 
% 1.64/1.90        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.64/1.90      inference('sup-', [status(thm)], ['0', '3'])).
% 1.64/1.90  thf(t16_tops_2, axiom,
% 1.64/1.90    (![A:$i]:
% 1.64/1.90     ( ( l1_pre_topc @ A ) =>
% 1.64/1.90       ( ![B:$i]:
% 1.64/1.90         ( ( m1_subset_1 @
% 1.64/1.90             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.64/1.90           ( ( v2_tops_2 @ B @ A ) <=>
% 1.64/1.90             ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 1.64/1.90  thf('5', plain,
% 1.64/1.90      (![X8 : $i, X9 : $i]:
% 1.64/1.90         (~ (m1_subset_1 @ X8 @ 
% 1.64/1.90             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9))))
% 1.64/1.90          | ~ (v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ X9) @ X8) @ X9)
% 1.64/1.90          | (v2_tops_2 @ X8 @ X9)
% 1.64/1.90          | ~ (l1_pre_topc @ X9))),
% 1.64/1.90      inference('cnf', [status(esa)], [t16_tops_2])).
% 1.64/1.90  thf('6', plain,
% 1.64/1.90      ((~ (l1_pre_topc @ sk_A)
% 1.64/1.90        | (v2_tops_2 @ 
% 1.64/1.90           (k4_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_C) @ 
% 1.64/1.90           sk_A)
% 1.64/1.90        | ~ (v1_tops_2 @ 
% 1.64/1.90             (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 1.64/1.90              (k4_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_C)) @ 
% 1.64/1.90             sk_A))),
% 1.64/1.90      inference('sup-', [status(thm)], ['4', '5'])).
% 1.64/1.90  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 1.64/1.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.90  thf('8', plain,
% 1.64/1.90      (((v2_tops_2 @ 
% 1.64/1.90         (k4_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_C) @ 
% 1.64/1.90         sk_A)
% 1.64/1.90        | ~ (v1_tops_2 @ 
% 1.64/1.90             (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 1.64/1.90              (k4_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_C)) @ 
% 1.64/1.90             sk_A))),
% 1.64/1.90      inference('demod', [status(thm)], ['6', '7'])).
% 1.64/1.90  thf('9', plain,
% 1.64/1.90      (~ (v2_tops_2 @ 
% 1.64/1.90          (k4_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_C) @ 
% 1.64/1.90          sk_A)),
% 1.64/1.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.90  thf('10', plain,
% 1.64/1.90      (~ (v1_tops_2 @ 
% 1.64/1.90          (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 1.64/1.90           (k4_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_C)) @ 
% 1.64/1.90          sk_A)),
% 1.64/1.90      inference('clc', [status(thm)], ['8', '9'])).
% 1.64/1.90  thf('11', plain,
% 1.64/1.90      ((m1_subset_1 @ sk_C @ 
% 1.64/1.90        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.64/1.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.90  thf(dt_k7_setfam_1, axiom,
% 1.64/1.90    (![A:$i,B:$i]:
% 1.64/1.90     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.64/1.90       ( m1_subset_1 @
% 1.64/1.90         ( k7_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 1.64/1.90  thf('12', plain,
% 1.64/1.90      (![X3 : $i, X4 : $i]:
% 1.64/1.90         ((m1_subset_1 @ (k7_setfam_1 @ X3 @ X4) @ 
% 1.64/1.90           (k1_zfmisc_1 @ (k1_zfmisc_1 @ X3)))
% 1.64/1.90          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X3))))),
% 1.64/1.90      inference('cnf', [status(esa)], [dt_k7_setfam_1])).
% 1.64/1.90  thf('13', plain,
% 1.64/1.90      ((m1_subset_1 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ 
% 1.64/1.90        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.64/1.90      inference('sup-', [status(thm)], ['11', '12'])).
% 1.64/1.90  thf('14', plain,
% 1.64/1.90      ((m1_subset_1 @ sk_B @ 
% 1.64/1.90        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.64/1.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.90  thf('15', plain,
% 1.64/1.90      (![X3 : $i, X4 : $i]:
% 1.64/1.90         ((m1_subset_1 @ (k7_setfam_1 @ X3 @ X4) @ 
% 1.64/1.90           (k1_zfmisc_1 @ (k1_zfmisc_1 @ X3)))
% 1.64/1.90          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X3))))),
% 1.64/1.90      inference('cnf', [status(esa)], [dt_k7_setfam_1])).
% 1.64/1.90  thf('16', plain,
% 1.64/1.90      ((m1_subset_1 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 1.64/1.90        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.64/1.90      inference('sup-', [status(thm)], ['14', '15'])).
% 1.64/1.90  thf(t20_tops_2, axiom,
% 1.64/1.90    (![A:$i]:
% 1.64/1.90     ( ( l1_pre_topc @ A ) =>
% 1.64/1.90       ( ![B:$i]:
% 1.64/1.90         ( ( m1_subset_1 @
% 1.64/1.90             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.64/1.90           ( ![C:$i]:
% 1.64/1.90             ( ( m1_subset_1 @
% 1.64/1.90                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.64/1.90               ( ( ( v1_tops_2 @ B @ A ) & ( v1_tops_2 @ C @ A ) ) =>
% 1.64/1.90                 ( v1_tops_2 @
% 1.64/1.90                   ( k4_subset_1 @
% 1.64/1.90                     ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) @ 
% 1.64/1.90                   A ) ) ) ) ) ) ))).
% 1.64/1.90  thf('17', plain,
% 1.64/1.90      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.64/1.90         (~ (m1_subset_1 @ X10 @ 
% 1.64/1.90             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11))))
% 1.64/1.90          | ~ (v1_tops_2 @ X10 @ X11)
% 1.64/1.90          | ~ (v1_tops_2 @ X12 @ X11)
% 1.64/1.90          | (v1_tops_2 @ 
% 1.64/1.90             (k4_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)) @ X10 @ X12) @ 
% 1.64/1.90             X11)
% 1.64/1.90          | ~ (m1_subset_1 @ X12 @ 
% 1.64/1.90               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11))))
% 1.64/1.90          | ~ (l1_pre_topc @ X11))),
% 1.64/1.90      inference('cnf', [status(esa)], [t20_tops_2])).
% 1.64/1.90  thf('18', plain,
% 1.64/1.90      (![X0 : $i]:
% 1.64/1.90         (~ (l1_pre_topc @ sk_A)
% 1.64/1.90          | ~ (m1_subset_1 @ X0 @ 
% 1.64/1.90               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 1.64/1.90          | (v1_tops_2 @ 
% 1.64/1.90             (k4_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ 
% 1.64/1.90              (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ X0) @ 
% 1.64/1.90             sk_A)
% 1.64/1.90          | ~ (v1_tops_2 @ X0 @ sk_A)
% 1.64/1.90          | ~ (v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 1.64/1.90      inference('sup-', [status(thm)], ['16', '17'])).
% 1.64/1.90  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 1.64/1.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.90  thf('20', plain,
% 1.64/1.90      ((m1_subset_1 @ sk_B @ 
% 1.64/1.90        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.64/1.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.90  thf('21', plain,
% 1.64/1.90      (![X8 : $i, X9 : $i]:
% 1.64/1.90         (~ (m1_subset_1 @ X8 @ 
% 1.64/1.90             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9))))
% 1.64/1.90          | ~ (v2_tops_2 @ X8 @ X9)
% 1.64/1.90          | (v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ X9) @ X8) @ X9)
% 1.64/1.90          | ~ (l1_pre_topc @ X9))),
% 1.64/1.90      inference('cnf', [status(esa)], [t16_tops_2])).
% 1.64/1.90  thf('22', plain,
% 1.64/1.90      ((~ (l1_pre_topc @ sk_A)
% 1.64/1.90        | (v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 1.64/1.90        | ~ (v2_tops_2 @ sk_B @ sk_A))),
% 1.64/1.90      inference('sup-', [status(thm)], ['20', '21'])).
% 1.64/1.90  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 1.64/1.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.90  thf('24', plain, ((v2_tops_2 @ sk_B @ sk_A)),
% 1.64/1.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.90  thf('25', plain,
% 1.64/1.90      ((v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)),
% 1.64/1.90      inference('demod', [status(thm)], ['22', '23', '24'])).
% 1.64/1.90  thf('26', plain,
% 1.64/1.90      (![X0 : $i]:
% 1.64/1.90         (~ (m1_subset_1 @ X0 @ 
% 1.64/1.90             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 1.64/1.90          | (v1_tops_2 @ 
% 1.64/1.90             (k4_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ 
% 1.64/1.90              (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ X0) @ 
% 1.64/1.90             sk_A)
% 1.64/1.90          | ~ (v1_tops_2 @ X0 @ sk_A))),
% 1.64/1.90      inference('demod', [status(thm)], ['18', '19', '25'])).
% 1.64/1.90  thf('27', plain,
% 1.64/1.90      ((~ (v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ sk_A)
% 1.64/1.90        | (v1_tops_2 @ 
% 1.64/1.90           (k4_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ 
% 1.64/1.90            (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 1.64/1.90            (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C)) @ 
% 1.64/1.90           sk_A))),
% 1.64/1.90      inference('sup-', [status(thm)], ['13', '26'])).
% 1.64/1.90  thf('28', plain,
% 1.64/1.90      ((m1_subset_1 @ sk_C @ 
% 1.64/1.90        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.64/1.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.90  thf('29', plain,
% 1.64/1.90      (![X8 : $i, X9 : $i]:
% 1.64/1.90         (~ (m1_subset_1 @ X8 @ 
% 1.64/1.90             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9))))
% 1.64/1.90          | ~ (v2_tops_2 @ X8 @ X9)
% 1.64/1.90          | (v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ X9) @ X8) @ X9)
% 1.64/1.90          | ~ (l1_pre_topc @ X9))),
% 1.64/1.90      inference('cnf', [status(esa)], [t16_tops_2])).
% 1.64/1.90  thf('30', plain,
% 1.64/1.90      ((~ (l1_pre_topc @ sk_A)
% 1.64/1.90        | (v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ sk_A)
% 1.64/1.90        | ~ (v2_tops_2 @ sk_C @ sk_A))),
% 1.64/1.90      inference('sup-', [status(thm)], ['28', '29'])).
% 1.64/1.90  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 1.64/1.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.90  thf('32', plain, ((v2_tops_2 @ sk_C @ sk_A)),
% 1.64/1.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.90  thf('33', plain,
% 1.64/1.90      ((v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ sk_A)),
% 1.64/1.90      inference('demod', [status(thm)], ['30', '31', '32'])).
% 1.64/1.90  thf('34', plain,
% 1.64/1.90      ((v1_tops_2 @ 
% 1.64/1.90        (k4_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ 
% 1.64/1.90         (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 1.64/1.90         (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C)) @ 
% 1.64/1.90        sk_A)),
% 1.64/1.90      inference('demod', [status(thm)], ['27', '33'])).
% 1.64/1.90  thf('35', plain,
% 1.64/1.90      ((m1_subset_1 @ sk_B @ 
% 1.64/1.90        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.64/1.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.90  thf('36', plain,
% 1.64/1.90      ((m1_subset_1 @ sk_C @ 
% 1.64/1.90        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.64/1.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.90  thf(t54_setfam_1, axiom,
% 1.64/1.90    (![A:$i,B:$i]:
% 1.64/1.90     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.64/1.90       ( ![C:$i]:
% 1.64/1.90         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.64/1.90           ( ( k7_setfam_1 @ A @ ( k4_subset_1 @ ( k1_zfmisc_1 @ A ) @ B @ C ) ) =
% 1.64/1.90             ( k4_subset_1 @
% 1.64/1.90               ( k1_zfmisc_1 @ A ) @ ( k7_setfam_1 @ A @ B ) @ 
% 1.64/1.90               ( k7_setfam_1 @ A @ C ) ) ) ) ) ))).
% 1.64/1.90  thf('37', plain,
% 1.64/1.90      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.64/1.90         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X6)))
% 1.64/1.90          | ((k7_setfam_1 @ X6 @ (k4_subset_1 @ (k1_zfmisc_1 @ X6) @ X7 @ X5))
% 1.64/1.90              = (k4_subset_1 @ (k1_zfmisc_1 @ X6) @ (k7_setfam_1 @ X6 @ X7) @ 
% 1.64/1.90                 (k7_setfam_1 @ X6 @ X5)))
% 1.64/1.90          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X6))))),
% 1.64/1.90      inference('cnf', [status(esa)], [t54_setfam_1])).
% 1.64/1.90  thf('38', plain,
% 1.64/1.90      (![X0 : $i]:
% 1.64/1.90         (~ (m1_subset_1 @ X0 @ 
% 1.64/1.90             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 1.64/1.90          | ((k7_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 1.64/1.90              (k4_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ X0 @ sk_C))
% 1.64/1.90              = (k4_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ 
% 1.64/1.90                 (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 1.64/1.90                 (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C))))),
% 1.64/1.90      inference('sup-', [status(thm)], ['36', '37'])).
% 1.64/1.90  thf('39', plain,
% 1.64/1.90      (((k7_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 1.64/1.90         (k4_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_C))
% 1.64/1.90         = (k4_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ 
% 1.64/1.90            (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 1.64/1.90            (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C)))),
% 1.64/1.90      inference('sup-', [status(thm)], ['35', '38'])).
% 1.64/1.90  thf('40', plain,
% 1.64/1.90      ((v1_tops_2 @ 
% 1.64/1.90        (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 1.64/1.90         (k4_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_C)) @ 
% 1.64/1.90        sk_A)),
% 1.64/1.90      inference('demod', [status(thm)], ['34', '39'])).
% 1.64/1.90  thf('41', plain, ($false), inference('demod', [status(thm)], ['10', '40'])).
% 1.64/1.90  
% 1.64/1.90  % SZS output end Refutation
% 1.64/1.90  
% 1.64/1.91  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
