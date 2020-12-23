%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zhUikgHDVl

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:33 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 116 expanded)
%              Number of leaves         :   17 (  39 expanded)
%              Depth                    :    9
%              Number of atoms          :  670 (1413 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_tops_2_type,type,(
    v2_tops_2: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_tops_2_type,type,(
    v1_tops_2: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k7_setfam_1_type,type,(
    k7_setfam_1: $i > $i > $i )).

thf(t79_tops_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v2_tops_2 @ B @ A )
          <=> ( r1_tarski @ B @ ( k7_setfam_1 @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ( ( v2_tops_2 @ B @ A )
            <=> ( r1_tarski @ B @ ( k7_setfam_1 @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t79_tops_2])).

thf('0',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( v2_tops_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( v2_tops_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r1_tarski @ sk_B @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ( v2_tops_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v2_tops_2 @ sk_B @ sk_A )
   <= ( v2_tops_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t16_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v2_tops_2 @ B @ A )
          <=> ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('5',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) ) )
      | ~ ( v2_tops_2 @ X6 @ X7 )
      | ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ X7 ) @ X6 ) @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[t16_tops_2])).

thf('6',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v2_tops_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v2_tops_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v2_tops_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k7_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k7_setfam_1 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_setfam_1])).

thf('12',plain,(
    m1_subset_1 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t78_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v1_tops_2 @ B @ A )
          <=> ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('13',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( v1_tops_2 @ X8 @ X9 )
      | ( r1_tarski @ X8 @ ( u1_pre_topc @ X9 ) )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[t78_tops_2])).

thf('14',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( r1_tarski @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( r1_tarski @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
   <= ( v2_tops_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['9','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('19',plain,(
    ! [X5: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X5 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) ) )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(t52_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
         => ( ( r1_tarski @ ( k7_setfam_1 @ A @ B ) @ C )
          <=> ( r1_tarski @ B @ ( k7_setfam_1 @ A @ C ) ) ) ) ) )).

thf('20',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X3 ) ) )
      | ~ ( r1_tarski @ ( k7_setfam_1 @ X3 @ X4 ) @ X2 )
      | ( r1_tarski @ X4 @ ( k7_setfam_1 @ X3 @ X2 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[t52_setfam_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) )
      | ( r1_tarski @ X1 @ ( k7_setfam_1 @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( r1_tarski @ ( k7_setfam_1 @ ( u1_struct_0 @ X0 ) @ X1 ) @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ~ ( r1_tarski @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
    | ( r1_tarski @ sk_B @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ~ ( r1_tarski @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
    | ( r1_tarski @ sk_B @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( r1_tarski @ sk_B @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ( v2_tops_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['17','24'])).

thf('26',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ~ ( r1_tarski @ sk_B @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('27',plain,
    ( ( r1_tarski @ sk_B @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( v2_tops_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( r1_tarski @ sk_B @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ( v2_tops_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('29',plain,
    ( ( r1_tarski @ sk_B @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ( r1_tarski @ sk_B @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf('30',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X5: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X5 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) ) )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('32',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X3 ) ) )
      | ~ ( r1_tarski @ X4 @ ( k7_setfam_1 @ X3 @ X2 ) )
      | ( r1_tarski @ ( k7_setfam_1 @ X3 @ X4 ) @ X2 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[t52_setfam_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) )
      | ( r1_tarski @ ( k7_setfam_1 @ ( u1_struct_0 @ X0 ) @ X1 ) @ ( u1_pre_topc @ X0 ) )
      | ~ ( r1_tarski @ X1 @ ( k7_setfam_1 @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ( r1_tarski @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ( r1_tarski @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( r1_tarski @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
   <= ( r1_tarski @ sk_B @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['29','36'])).

thf('38',plain,(
    m1_subset_1 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('39',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( r1_tarski @ X8 @ ( u1_pre_topc @ X9 ) )
      | ( v1_tops_2 @ X8 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[t78_tops_2])).

thf('40',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( r1_tarski @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( r1_tarski @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( r1_tarski @ sk_B @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['37','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) ) )
      | ~ ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ X7 ) @ X6 ) @ X7 )
      | ( v2_tops_2 @ X6 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[t16_tops_2])).

thf('46',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_2 @ sk_B @ sk_A )
    | ~ ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( v2_tops_2 @ sk_B @ sk_A )
    | ~ ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( v2_tops_2 @ sk_B @ sk_A )
   <= ( r1_tarski @ sk_B @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['43','48'])).

thf('50',plain,
    ( ~ ( v2_tops_2 @ sk_B @ sk_A )
   <= ~ ( v2_tops_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('51',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ( v2_tops_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','27','28','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zhUikgHDVl
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:44:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.20/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.51  % Solved by: fo/fo7.sh
% 0.20/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.51  % done 79 iterations in 0.060s
% 0.20/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.51  % SZS output start Refutation
% 0.20/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.51  thf(v2_tops_2_type, type, v2_tops_2: $i > $i > $o).
% 0.20/0.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.51  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.20/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.51  thf(v1_tops_2_type, type, v1_tops_2: $i > $i > $o).
% 0.20/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.51  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.51  thf(k7_setfam_1_type, type, k7_setfam_1: $i > $i > $i).
% 0.20/0.51  thf(t79_tops_2, conjecture,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( l1_pre_topc @ A ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( m1_subset_1 @
% 0.20/0.51             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.51           ( ( v2_tops_2 @ B @ A ) <=>
% 0.20/0.51             ( r1_tarski @
% 0.20/0.51               B @ ( k7_setfam_1 @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ))).
% 0.20/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.51    (~( ![A:$i]:
% 0.20/0.51        ( ( l1_pre_topc @ A ) =>
% 0.20/0.51          ( ![B:$i]:
% 0.20/0.51            ( ( m1_subset_1 @
% 0.20/0.51                B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.51              ( ( v2_tops_2 @ B @ A ) <=>
% 0.20/0.51                ( r1_tarski @
% 0.20/0.51                  B @ 
% 0.20/0.51                  ( k7_setfam_1 @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ) )),
% 0.20/0.51    inference('cnf.neg', [status(esa)], [t79_tops_2])).
% 0.20/0.51  thf('0', plain,
% 0.20/0.51      ((~ (r1_tarski @ sk_B @ 
% 0.20/0.51           (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.20/0.51        | ~ (v2_tops_2 @ sk_B @ sk_A))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('1', plain,
% 0.20/0.51      (~
% 0.20/0.51       ((r1_tarski @ sk_B @ 
% 0.20/0.51         (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) | 
% 0.20/0.51       ~ ((v2_tops_2 @ sk_B @ sk_A))),
% 0.20/0.51      inference('split', [status(esa)], ['0'])).
% 0.20/0.51  thf('2', plain,
% 0.20/0.51      (((r1_tarski @ sk_B @ 
% 0.20/0.51         (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.20/0.51        | (v2_tops_2 @ sk_B @ sk_A))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('3', plain,
% 0.20/0.51      (((v2_tops_2 @ sk_B @ sk_A)) <= (((v2_tops_2 @ sk_B @ sk_A)))),
% 0.20/0.51      inference('split', [status(esa)], ['2'])).
% 0.20/0.51  thf('4', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_B @ 
% 0.20/0.51        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(t16_tops_2, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( l1_pre_topc @ A ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( m1_subset_1 @
% 0.20/0.51             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.51           ( ( v2_tops_2 @ B @ A ) <=>
% 0.20/0.51             ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.20/0.51  thf('5', plain,
% 0.20/0.51      (![X6 : $i, X7 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X6 @ 
% 0.20/0.51             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7))))
% 0.20/0.51          | ~ (v2_tops_2 @ X6 @ X7)
% 0.20/0.51          | (v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ X7) @ X6) @ X7)
% 0.20/0.51          | ~ (l1_pre_topc @ X7))),
% 0.20/0.51      inference('cnf', [status(esa)], [t16_tops_2])).
% 0.20/0.51  thf('6', plain,
% 0.20/0.51      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.51        | (v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.20/0.51        | ~ (v2_tops_2 @ sk_B @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.51  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('8', plain,
% 0.20/0.51      (((v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.20/0.51        | ~ (v2_tops_2 @ sk_B @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.51  thf('9', plain,
% 0.20/0.51      (((v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 0.20/0.51         <= (((v2_tops_2 @ sk_B @ sk_A)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['3', '8'])).
% 0.20/0.51  thf('10', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_B @ 
% 0.20/0.51        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(dt_k7_setfam_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.51       ( m1_subset_1 @
% 0.20/0.51         ( k7_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.20/0.51  thf('11', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((m1_subset_1 @ (k7_setfam_1 @ X0 @ X1) @ 
% 0.20/0.51           (k1_zfmisc_1 @ (k1_zfmisc_1 @ X0)))
% 0.20/0.51          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X0))))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_k7_setfam_1])).
% 0.20/0.51  thf('12', plain,
% 0.20/0.51      ((m1_subset_1 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.51        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.51  thf(t78_tops_2, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( l1_pre_topc @ A ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( m1_subset_1 @
% 0.20/0.51             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.51           ( ( v1_tops_2 @ B @ A ) <=> ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 0.20/0.51  thf('13', plain,
% 0.20/0.51      (![X8 : $i, X9 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X8 @ 
% 0.20/0.51             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9))))
% 0.20/0.51          | ~ (v1_tops_2 @ X8 @ X9)
% 0.20/0.51          | (r1_tarski @ X8 @ (u1_pre_topc @ X9))
% 0.20/0.51          | ~ (l1_pre_topc @ X9))),
% 0.20/0.51      inference('cnf', [status(esa)], [t78_tops_2])).
% 0.20/0.51  thf('14', plain,
% 0.20/0.51      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.51        | (r1_tarski @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.51           (u1_pre_topc @ sk_A))
% 0.20/0.51        | ~ (v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.51  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('16', plain,
% 0.20/0.51      (((r1_tarski @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.51         (u1_pre_topc @ sk_A))
% 0.20/0.51        | ~ (v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.51  thf('17', plain,
% 0.20/0.51      (((r1_tarski @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.51         (u1_pre_topc @ sk_A))) <= (((v2_tops_2 @ sk_B @ sk_A)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['9', '16'])).
% 0.20/0.51  thf('18', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_B @ 
% 0.20/0.51        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(dt_u1_pre_topc, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( l1_pre_topc @ A ) =>
% 0.20/0.51       ( m1_subset_1 @
% 0.20/0.51         ( u1_pre_topc @ A ) @ 
% 0.20/0.51         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.20/0.51  thf('19', plain,
% 0.20/0.51      (![X5 : $i]:
% 0.20/0.51         ((m1_subset_1 @ (u1_pre_topc @ X5) @ 
% 0.20/0.51           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5))))
% 0.20/0.51          | ~ (l1_pre_topc @ X5))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.20/0.51  thf(t52_setfam_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.51       ( ![C:$i]:
% 0.20/0.51         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.51           ( ( r1_tarski @ ( k7_setfam_1 @ A @ B ) @ C ) <=>
% 0.20/0.51             ( r1_tarski @ B @ ( k7_setfam_1 @ A @ C ) ) ) ) ) ))).
% 0.20/0.51  thf('20', plain,
% 0.20/0.51      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X3)))
% 0.20/0.51          | ~ (r1_tarski @ (k7_setfam_1 @ X3 @ X4) @ X2)
% 0.20/0.51          | (r1_tarski @ X4 @ (k7_setfam_1 @ X3 @ X2))
% 0.20/0.51          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X3))))),
% 0.20/0.51      inference('cnf', [status(esa)], [t52_setfam_1])).
% 0.20/0.51  thf('21', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (~ (l1_pre_topc @ X0)
% 0.20/0.51          | ~ (m1_subset_1 @ X1 @ 
% 0.20/0.51               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))
% 0.20/0.51          | (r1_tarski @ X1 @ 
% 0.20/0.51             (k7_setfam_1 @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.20/0.51          | ~ (r1_tarski @ (k7_setfam_1 @ (u1_struct_0 @ X0) @ X1) @ 
% 0.20/0.51               (u1_pre_topc @ X0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.51  thf('22', plain,
% 0.20/0.51      ((~ (r1_tarski @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.51           (u1_pre_topc @ sk_A))
% 0.20/0.51        | (r1_tarski @ sk_B @ 
% 0.20/0.51           (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.20/0.51        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['18', '21'])).
% 0.20/0.51  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('24', plain,
% 0.20/0.51      ((~ (r1_tarski @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.51           (u1_pre_topc @ sk_A))
% 0.20/0.51        | (r1_tarski @ sk_B @ 
% 0.20/0.51           (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))),
% 0.20/0.51      inference('demod', [status(thm)], ['22', '23'])).
% 0.20/0.51  thf('25', plain,
% 0.20/0.51      (((r1_tarski @ sk_B @ 
% 0.20/0.51         (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 0.20/0.51         <= (((v2_tops_2 @ sk_B @ sk_A)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['17', '24'])).
% 0.20/0.51  thf('26', plain,
% 0.20/0.51      ((~ (r1_tarski @ sk_B @ 
% 0.20/0.51           (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 0.20/0.51         <= (~
% 0.20/0.51             ((r1_tarski @ sk_B @ 
% 0.20/0.51               (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))),
% 0.20/0.51      inference('split', [status(esa)], ['0'])).
% 0.20/0.51  thf('27', plain,
% 0.20/0.51      (((r1_tarski @ sk_B @ 
% 0.20/0.51         (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) | 
% 0.20/0.51       ~ ((v2_tops_2 @ sk_B @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.51  thf('28', plain,
% 0.20/0.51      (((r1_tarski @ sk_B @ 
% 0.20/0.51         (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) | 
% 0.20/0.51       ((v2_tops_2 @ sk_B @ sk_A))),
% 0.20/0.51      inference('split', [status(esa)], ['2'])).
% 0.20/0.51  thf('29', plain,
% 0.20/0.51      (((r1_tarski @ sk_B @ 
% 0.20/0.51         (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 0.20/0.51         <= (((r1_tarski @ sk_B @ 
% 0.20/0.51               (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))),
% 0.20/0.51      inference('split', [status(esa)], ['2'])).
% 0.20/0.51  thf('30', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_B @ 
% 0.20/0.51        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('31', plain,
% 0.20/0.51      (![X5 : $i]:
% 0.20/0.51         ((m1_subset_1 @ (u1_pre_topc @ X5) @ 
% 0.20/0.51           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5))))
% 0.20/0.51          | ~ (l1_pre_topc @ X5))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.20/0.51  thf('32', plain,
% 0.20/0.51      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X3)))
% 0.20/0.51          | ~ (r1_tarski @ X4 @ (k7_setfam_1 @ X3 @ X2))
% 0.20/0.51          | (r1_tarski @ (k7_setfam_1 @ X3 @ X4) @ X2)
% 0.20/0.51          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X3))))),
% 0.20/0.51      inference('cnf', [status(esa)], [t52_setfam_1])).
% 0.20/0.51  thf('33', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (~ (l1_pre_topc @ X0)
% 0.20/0.51          | ~ (m1_subset_1 @ X1 @ 
% 0.20/0.51               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))
% 0.20/0.51          | (r1_tarski @ (k7_setfam_1 @ (u1_struct_0 @ X0) @ X1) @ 
% 0.20/0.51             (u1_pre_topc @ X0))
% 0.20/0.51          | ~ (r1_tarski @ X1 @ 
% 0.20/0.51               (k7_setfam_1 @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.51  thf('34', plain,
% 0.20/0.51      ((~ (r1_tarski @ sk_B @ 
% 0.20/0.51           (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.20/0.51        | (r1_tarski @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.51           (u1_pre_topc @ sk_A))
% 0.20/0.51        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['30', '33'])).
% 0.20/0.51  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('36', plain,
% 0.20/0.51      ((~ (r1_tarski @ sk_B @ 
% 0.20/0.51           (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.20/0.51        | (r1_tarski @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.51           (u1_pre_topc @ sk_A)))),
% 0.20/0.51      inference('demod', [status(thm)], ['34', '35'])).
% 0.20/0.51  thf('37', plain,
% 0.20/0.51      (((r1_tarski @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.51         (u1_pre_topc @ sk_A)))
% 0.20/0.51         <= (((r1_tarski @ sk_B @ 
% 0.20/0.51               (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['29', '36'])).
% 0.20/0.51  thf('38', plain,
% 0.20/0.51      ((m1_subset_1 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.51        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.51  thf('39', plain,
% 0.20/0.51      (![X8 : $i, X9 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X8 @ 
% 0.20/0.51             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9))))
% 0.20/0.51          | ~ (r1_tarski @ X8 @ (u1_pre_topc @ X9))
% 0.20/0.51          | (v1_tops_2 @ X8 @ X9)
% 0.20/0.51          | ~ (l1_pre_topc @ X9))),
% 0.20/0.51      inference('cnf', [status(esa)], [t78_tops_2])).
% 0.20/0.51  thf('40', plain,
% 0.20/0.51      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.51        | (v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.20/0.51        | ~ (r1_tarski @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.51             (u1_pre_topc @ sk_A)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['38', '39'])).
% 0.20/0.51  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('42', plain,
% 0.20/0.51      (((v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.20/0.51        | ~ (r1_tarski @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.51             (u1_pre_topc @ sk_A)))),
% 0.20/0.51      inference('demod', [status(thm)], ['40', '41'])).
% 0.20/0.51  thf('43', plain,
% 0.20/0.51      (((v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 0.20/0.51         <= (((r1_tarski @ sk_B @ 
% 0.20/0.51               (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['37', '42'])).
% 0.20/0.51  thf('44', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_B @ 
% 0.20/0.51        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('45', plain,
% 0.20/0.51      (![X6 : $i, X7 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X6 @ 
% 0.20/0.51             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7))))
% 0.20/0.51          | ~ (v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ X7) @ X6) @ X7)
% 0.20/0.51          | (v2_tops_2 @ X6 @ X7)
% 0.20/0.51          | ~ (l1_pre_topc @ X7))),
% 0.20/0.51      inference('cnf', [status(esa)], [t16_tops_2])).
% 0.20/0.51  thf('46', plain,
% 0.20/0.51      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.51        | (v2_tops_2 @ sk_B @ sk_A)
% 0.20/0.51        | ~ (v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['44', '45'])).
% 0.20/0.51  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('48', plain,
% 0.20/0.51      (((v2_tops_2 @ sk_B @ sk_A)
% 0.20/0.51        | ~ (v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['46', '47'])).
% 0.20/0.51  thf('49', plain,
% 0.20/0.51      (((v2_tops_2 @ sk_B @ sk_A))
% 0.20/0.51         <= (((r1_tarski @ sk_B @ 
% 0.20/0.51               (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['43', '48'])).
% 0.20/0.51  thf('50', plain,
% 0.20/0.51      ((~ (v2_tops_2 @ sk_B @ sk_A)) <= (~ ((v2_tops_2 @ sk_B @ sk_A)))),
% 0.20/0.51      inference('split', [status(esa)], ['0'])).
% 0.20/0.51  thf('51', plain,
% 0.20/0.51      (~
% 0.20/0.51       ((r1_tarski @ sk_B @ 
% 0.20/0.51         (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) | 
% 0.20/0.51       ((v2_tops_2 @ sk_B @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['49', '50'])).
% 0.20/0.51  thf('52', plain, ($false),
% 0.20/0.51      inference('sat_resolution*', [status(thm)], ['1', '27', '28', '51'])).
% 0.20/0.51  
% 0.20/0.51  % SZS output end Refutation
% 0.20/0.51  
% 0.20/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
