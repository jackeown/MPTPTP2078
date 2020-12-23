%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZtpLlo34bC

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:35 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 332 expanded)
%              Number of leaves         :   27 ( 103 expanded)
%              Depth                    :   17
%              Number of atoms          :  776 (4640 expanded)
%              Number of equality atoms :   20 (  44 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t61_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v3_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ~ ( ( ( v3_pre_topc @ B @ A )
                | ( v4_pre_topc @ B @ A ) )
              & ( v3_tex_2 @ B @ A )
              & ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( v3_tdlat_3 @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ~ ( ( ( v3_pre_topc @ B @ A )
                  | ( v4_pre_topc @ B @ A ) )
                & ( v3_tex_2 @ B @ A )
                & ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t61_tex_2])).

thf('0',plain,(
    v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( v3_pre_topc @ sk_B_2 @ sk_A )
    | ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v4_pre_topc @ sk_B_2 @ sk_A )
   <= ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t31_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v4_pre_topc @ B @ A )
                  & ( r1_tarski @ C @ B ) )
               => ( r1_tarski @ ( k2_pre_topc @ A @ C ) @ B ) ) ) ) ) )).

thf('5',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( v4_pre_topc @ X7 @ X8 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ( r1_tarski @ ( k2_pre_topc @ X8 @ X9 ) @ X7 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[t31_tops_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ X0 ) @ sk_B_2 )
      | ~ ( r1_tarski @ X0 @ sk_B_2 )
      | ~ ( v4_pre_topc @ sk_B_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ X0 ) @ sk_B_2 )
      | ~ ( r1_tarski @ X0 @ sk_B_2 )
      | ~ ( v4_pre_topc @ sk_B_2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ X0 @ sk_B_2 )
        | ( r1_tarski @ ( k2_pre_topc @ sk_A @ X0 ) @ sk_B_2 )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,
    ( ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B_2 ) @ sk_B_2 )
      | ~ ( r1_tarski @ sk_B_2 @ sk_B_2 ) )
   <= ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','9'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('12',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,
    ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B_2 ) @ sk_B_2 )
   <= ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['10','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) )).

thf('15',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ( r1_tarski @ X5 @ ( k2_pre_topc @ X6 @ X5 ) )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('16',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ sk_B_2 @ ( k2_pre_topc @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    r1_tarski @ sk_B_2 @ ( k2_pre_topc @ sk_A @ sk_B_2 ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('20',plain,
    ( ~ ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B_2 ) @ sk_B_2 )
    | ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = sk_B_2 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = sk_B_2 )
   <= ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['13','20'])).

thf('22',plain,
    ( ( v3_pre_topc @ sk_B_2 @ sk_A )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('23',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t47_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v3_pre_topc @ B @ A )
              & ( v3_tex_2 @ B @ A ) )
           => ( v1_tops_1 @ B @ A ) ) ) ) )).

thf('24',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( v1_tops_1 @ X16 @ X17 )
      | ~ ( v3_tex_2 @ X16 @ X17 )
      | ~ ( v3_pre_topc @ X16 @ X17 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t47_tex_2])).

thf('25',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_2 @ sk_A )
    | ~ ( v3_tex_2 @ sk_B_2 @ sk_A )
    | ( v1_tops_1 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v3_tex_2 @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_2 @ sk_A )
    | ( v1_tops_1 @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['25','26','27','28'])).

thf('30',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( v1_tops_1 @ sk_B_2 @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( v1_tops_1 @ sk_B_2 @ sk_A )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['22','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_tops_3,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( u1_struct_0 @ A ) ) ) ) ) )).

thf('34',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( v1_tops_1 @ X10 @ X11 )
      | ( ( k2_pre_topc @ X11 @ X10 )
        = ( u1_struct_0 @ X11 ) )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_3])).

thf('35',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = ( u1_struct_0 @ sk_A ) )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['32','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( v3_pre_topc @ sk_B_2 @ sk_A )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('41',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t23_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v3_tdlat_3 @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v3_pre_topc @ B @ A )
             => ( v4_pre_topc @ B @ A ) ) ) ) ) )).

thf('42',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v3_tdlat_3 @ X12 )
      | ~ ( v3_pre_topc @ X13 @ X12 )
      | ( v4_pre_topc @ X13 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t23_tdlat_3])).

thf('43',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B_2 @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_2 @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( v4_pre_topc @ sk_B_2 @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['43','44','45','46'])).

thf('48',plain,
    ( ( v4_pre_topc @ sk_B_2 @ sk_A )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['40','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ X0 ) @ sk_B_2 )
      | ~ ( r1_tarski @ X0 @ sk_B_2 )
      | ~ ( v4_pre_topc @ sk_B_2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('50',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ X0 @ sk_B_2 )
        | ( r1_tarski @ ( k2_pre_topc @ sk_A @ X0 ) @ sk_B_2 )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B_2 ) @ sk_B_2 )
      | ~ ( r1_tarski @ sk_B_2 @ sk_B_2 ) )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['39','50'])).

thf('52',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['11'])).

thf('53',plain,
    ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B_2 ) @ sk_B_2 )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ~ ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B_2 ) @ sk_B_2 )
    | ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = sk_B_2 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('55',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = sk_B_2 )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_2 )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup+',[status(thm)],['38','55'])).

thf('57',plain,(
    v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( v1_subset_1 @ sk_B_2 @ sk_B_2 )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf(fc14_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_subset_1 @ ( k2_subset_1 @ A ) @ A ) )).

thf('59',plain,(
    ! [X4: $i] :
      ~ ( v1_subset_1 @ ( k2_subset_1 @ X4 ) @ X4 ) ),
    inference(cnf,[status(esa)],[fc14_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('60',plain,(
    ! [X3: $i] :
      ( ( k2_subset_1 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('61',plain,(
    ! [X4: $i] :
      ~ ( v1_subset_1 @ X4 @ X4 ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ~ ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['58','61'])).

thf('63',plain,
    ( ( v4_pre_topc @ sk_B_2 @ sk_A )
    | ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('64',plain,(
    v4_pre_topc @ sk_B_2 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_2 )
    = sk_B_2 ),
    inference(simpl_trail,[status(thm)],['21','64'])).

thf('66',plain,
    ( ( v4_pre_topc @ sk_B_2 @ sk_A )
   <= ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('67',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t24_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v3_tdlat_3 @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v4_pre_topc @ B @ A )
             => ( v3_pre_topc @ B @ A ) ) ) ) ) )).

thf('68',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v3_tdlat_3 @ X14 )
      | ~ ( v4_pre_topc @ X15 @ X14 )
      | ( v3_pre_topc @ X15 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t24_tdlat_3])).

thf('69',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ sk_B_2 @ sk_A )
    | ~ ( v4_pre_topc @ sk_B_2 @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( v3_pre_topc @ sk_B_2 @ sk_A )
    | ~ ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['69','70','71','72'])).

thf('74',plain,
    ( ( v3_pre_topc @ sk_B_2 @ sk_A )
   <= ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['66','73'])).

thf('75',plain,
    ( ( v1_tops_1 @ sk_B_2 @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('76',plain,
    ( ( v1_tops_1 @ sk_B_2 @ sk_A )
   <= ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('78',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = ( u1_struct_0 @ sk_A ) )
   <= ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    v4_pre_topc @ sk_B_2 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['62','63'])).

thf('80',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_2 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['78','79'])).

thf('81',plain,
    ( sk_B_2
    = ( u1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['65','80'])).

thf('82',plain,(
    v1_subset_1 @ sk_B_2 @ sk_B_2 ),
    inference(demod,[status(thm)],['0','81'])).

thf('83',plain,(
    ! [X4: $i] :
      ~ ( v1_subset_1 @ X4 @ X4 ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('84',plain,(
    $false ),
    inference('sup-',[status(thm)],['82','83'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZtpLlo34bC
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:33:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.45  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.45  % Solved by: fo/fo7.sh
% 0.21/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.45  % done 89 iterations in 0.027s
% 0.21/0.45  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.45  % SZS output start Refutation
% 0.21/0.45  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.21/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.45  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.21/0.45  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.21/0.45  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.45  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.45  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.45  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.45  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.45  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.21/0.45  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.45  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.21/0.45  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.21/0.45  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.21/0.45  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.21/0.45  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.21/0.45  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.45  thf(t61_tex_2, conjecture,
% 0.21/0.45    (![A:$i]:
% 0.21/0.45     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.21/0.45         ( l1_pre_topc @ A ) ) =>
% 0.21/0.45       ( ![B:$i]:
% 0.21/0.45         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.45           ( ~( ( ( v3_pre_topc @ B @ A ) | ( v4_pre_topc @ B @ A ) ) & 
% 0.21/0.45                ( v3_tex_2 @ B @ A ) & 
% 0.21/0.45                ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.21/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.45    (~( ![A:$i]:
% 0.21/0.45        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.45            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.45          ( ![B:$i]:
% 0.21/0.45            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.45              ( ~( ( ( v3_pre_topc @ B @ A ) | ( v4_pre_topc @ B @ A ) ) & 
% 0.21/0.45                   ( v3_tex_2 @ B @ A ) & 
% 0.21/0.45                   ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )),
% 0.21/0.45    inference('cnf.neg', [status(esa)], [t61_tex_2])).
% 0.21/0.45  thf('0', plain, ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('1', plain,
% 0.21/0.45      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('2', plain,
% 0.21/0.45      (((v3_pre_topc @ sk_B_2 @ sk_A) | (v4_pre_topc @ sk_B_2 @ sk_A))),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('3', plain,
% 0.21/0.45      (((v4_pre_topc @ sk_B_2 @ sk_A)) <= (((v4_pre_topc @ sk_B_2 @ sk_A)))),
% 0.21/0.45      inference('split', [status(esa)], ['2'])).
% 0.21/0.45  thf('4', plain,
% 0.21/0.45      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf(t31_tops_1, axiom,
% 0.21/0.45    (![A:$i]:
% 0.21/0.45     ( ( l1_pre_topc @ A ) =>
% 0.21/0.45       ( ![B:$i]:
% 0.21/0.45         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.45           ( ![C:$i]:
% 0.21/0.45             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.45               ( ( ( v4_pre_topc @ B @ A ) & ( r1_tarski @ C @ B ) ) =>
% 0.21/0.45                 ( r1_tarski @ ( k2_pre_topc @ A @ C ) @ B ) ) ) ) ) ) ))).
% 0.21/0.45  thf('5', plain,
% 0.21/0.45      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.45         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.21/0.45          | ~ (v4_pre_topc @ X7 @ X8)
% 0.21/0.45          | ~ (r1_tarski @ X9 @ X7)
% 0.21/0.45          | (r1_tarski @ (k2_pre_topc @ X8 @ X9) @ X7)
% 0.21/0.45          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.21/0.45          | ~ (l1_pre_topc @ X8))),
% 0.21/0.45      inference('cnf', [status(esa)], [t31_tops_1])).
% 0.21/0.45  thf('6', plain,
% 0.21/0.45      (![X0 : $i]:
% 0.21/0.45         (~ (l1_pre_topc @ sk_A)
% 0.21/0.45          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.45          | (r1_tarski @ (k2_pre_topc @ sk_A @ X0) @ sk_B_2)
% 0.21/0.45          | ~ (r1_tarski @ X0 @ sk_B_2)
% 0.21/0.45          | ~ (v4_pre_topc @ sk_B_2 @ sk_A))),
% 0.21/0.45      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.45  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('8', plain,
% 0.21/0.45      (![X0 : $i]:
% 0.21/0.45         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.45          | (r1_tarski @ (k2_pre_topc @ sk_A @ X0) @ sk_B_2)
% 0.21/0.45          | ~ (r1_tarski @ X0 @ sk_B_2)
% 0.21/0.45          | ~ (v4_pre_topc @ sk_B_2 @ sk_A))),
% 0.21/0.45      inference('demod', [status(thm)], ['6', '7'])).
% 0.21/0.45  thf('9', plain,
% 0.21/0.45      ((![X0 : $i]:
% 0.21/0.45          (~ (r1_tarski @ X0 @ sk_B_2)
% 0.21/0.45           | (r1_tarski @ (k2_pre_topc @ sk_A @ X0) @ sk_B_2)
% 0.21/0.45           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.21/0.45         <= (((v4_pre_topc @ sk_B_2 @ sk_A)))),
% 0.21/0.45      inference('sup-', [status(thm)], ['3', '8'])).
% 0.21/0.45  thf('10', plain,
% 0.21/0.45      ((((r1_tarski @ (k2_pre_topc @ sk_A @ sk_B_2) @ sk_B_2)
% 0.21/0.45         | ~ (r1_tarski @ sk_B_2 @ sk_B_2)))
% 0.21/0.45         <= (((v4_pre_topc @ sk_B_2 @ sk_A)))),
% 0.21/0.45      inference('sup-', [status(thm)], ['1', '9'])).
% 0.21/0.45  thf(d10_xboole_0, axiom,
% 0.21/0.45    (![A:$i,B:$i]:
% 0.21/0.45     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.45  thf('11', plain,
% 0.21/0.45      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.21/0.45      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.45  thf('12', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.21/0.45      inference('simplify', [status(thm)], ['11'])).
% 0.21/0.45  thf('13', plain,
% 0.21/0.45      (((r1_tarski @ (k2_pre_topc @ sk_A @ sk_B_2) @ sk_B_2))
% 0.21/0.45         <= (((v4_pre_topc @ sk_B_2 @ sk_A)))),
% 0.21/0.45      inference('demod', [status(thm)], ['10', '12'])).
% 0.21/0.45  thf('14', plain,
% 0.21/0.45      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf(t48_pre_topc, axiom,
% 0.21/0.45    (![A:$i]:
% 0.21/0.45     ( ( l1_pre_topc @ A ) =>
% 0.21/0.45       ( ![B:$i]:
% 0.21/0.45         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.45           ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) ))).
% 0.21/0.45  thf('15', plain,
% 0.21/0.45      (![X5 : $i, X6 : $i]:
% 0.21/0.45         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.21/0.45          | (r1_tarski @ X5 @ (k2_pre_topc @ X6 @ X5))
% 0.21/0.45          | ~ (l1_pre_topc @ X6))),
% 0.21/0.45      inference('cnf', [status(esa)], [t48_pre_topc])).
% 0.21/0.45  thf('16', plain,
% 0.21/0.45      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.45        | (r1_tarski @ sk_B_2 @ (k2_pre_topc @ sk_A @ sk_B_2)))),
% 0.21/0.45      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.45  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('18', plain, ((r1_tarski @ sk_B_2 @ (k2_pre_topc @ sk_A @ sk_B_2))),
% 0.21/0.45      inference('demod', [status(thm)], ['16', '17'])).
% 0.21/0.45  thf('19', plain,
% 0.21/0.45      (![X0 : $i, X2 : $i]:
% 0.21/0.45         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.21/0.45      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.45  thf('20', plain,
% 0.21/0.45      ((~ (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B_2) @ sk_B_2)
% 0.21/0.45        | ((k2_pre_topc @ sk_A @ sk_B_2) = (sk_B_2)))),
% 0.21/0.45      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.45  thf('21', plain,
% 0.21/0.45      ((((k2_pre_topc @ sk_A @ sk_B_2) = (sk_B_2)))
% 0.21/0.45         <= (((v4_pre_topc @ sk_B_2 @ sk_A)))),
% 0.21/0.45      inference('sup-', [status(thm)], ['13', '20'])).
% 0.21/0.45  thf('22', plain,
% 0.21/0.45      (((v3_pre_topc @ sk_B_2 @ sk_A)) <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.21/0.45      inference('split', [status(esa)], ['2'])).
% 0.21/0.45  thf('23', plain,
% 0.21/0.45      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf(t47_tex_2, axiom,
% 0.21/0.45    (![A:$i]:
% 0.21/0.45     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.45       ( ![B:$i]:
% 0.21/0.45         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.45           ( ( ( v3_pre_topc @ B @ A ) & ( v3_tex_2 @ B @ A ) ) =>
% 0.21/0.45             ( v1_tops_1 @ B @ A ) ) ) ) ))).
% 0.21/0.45  thf('24', plain,
% 0.21/0.45      (![X16 : $i, X17 : $i]:
% 0.21/0.45         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.21/0.45          | (v1_tops_1 @ X16 @ X17)
% 0.21/0.45          | ~ (v3_tex_2 @ X16 @ X17)
% 0.21/0.45          | ~ (v3_pre_topc @ X16 @ X17)
% 0.21/0.45          | ~ (l1_pre_topc @ X17)
% 0.21/0.45          | ~ (v2_pre_topc @ X17)
% 0.21/0.45          | (v2_struct_0 @ X17))),
% 0.21/0.45      inference('cnf', [status(esa)], [t47_tex_2])).
% 0.21/0.45  thf('25', plain,
% 0.21/0.45      (((v2_struct_0 @ sk_A)
% 0.21/0.45        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.45        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.45        | ~ (v3_pre_topc @ sk_B_2 @ sk_A)
% 0.21/0.45        | ~ (v3_tex_2 @ sk_B_2 @ sk_A)
% 0.21/0.45        | (v1_tops_1 @ sk_B_2 @ sk_A))),
% 0.21/0.45      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.45  thf('26', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('28', plain, ((v3_tex_2 @ sk_B_2 @ sk_A)),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('29', plain,
% 0.21/0.45      (((v2_struct_0 @ sk_A)
% 0.21/0.45        | ~ (v3_pre_topc @ sk_B_2 @ sk_A)
% 0.21/0.45        | (v1_tops_1 @ sk_B_2 @ sk_A))),
% 0.21/0.45      inference('demod', [status(thm)], ['25', '26', '27', '28'])).
% 0.21/0.45  thf('30', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('31', plain,
% 0.21/0.45      (((v1_tops_1 @ sk_B_2 @ sk_A) | ~ (v3_pre_topc @ sk_B_2 @ sk_A))),
% 0.21/0.45      inference('clc', [status(thm)], ['29', '30'])).
% 0.21/0.45  thf('32', plain,
% 0.21/0.45      (((v1_tops_1 @ sk_B_2 @ sk_A)) <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.21/0.45      inference('sup-', [status(thm)], ['22', '31'])).
% 0.21/0.45  thf('33', plain,
% 0.21/0.45      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf(d2_tops_3, axiom,
% 0.21/0.45    (![A:$i]:
% 0.21/0.45     ( ( l1_pre_topc @ A ) =>
% 0.21/0.45       ( ![B:$i]:
% 0.21/0.45         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.45           ( ( v1_tops_1 @ B @ A ) <=>
% 0.21/0.45             ( ( k2_pre_topc @ A @ B ) = ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.21/0.45  thf('34', plain,
% 0.21/0.45      (![X10 : $i, X11 : $i]:
% 0.21/0.45         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.21/0.45          | ~ (v1_tops_1 @ X10 @ X11)
% 0.21/0.45          | ((k2_pre_topc @ X11 @ X10) = (u1_struct_0 @ X11))
% 0.21/0.45          | ~ (l1_pre_topc @ X11))),
% 0.21/0.45      inference('cnf', [status(esa)], [d2_tops_3])).
% 0.21/0.45  thf('35', plain,
% 0.21/0.45      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.45        | ((k2_pre_topc @ sk_A @ sk_B_2) = (u1_struct_0 @ sk_A))
% 0.21/0.45        | ~ (v1_tops_1 @ sk_B_2 @ sk_A))),
% 0.21/0.45      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.45  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('37', plain,
% 0.21/0.45      ((((k2_pre_topc @ sk_A @ sk_B_2) = (u1_struct_0 @ sk_A))
% 0.21/0.45        | ~ (v1_tops_1 @ sk_B_2 @ sk_A))),
% 0.21/0.45      inference('demod', [status(thm)], ['35', '36'])).
% 0.21/0.45  thf('38', plain,
% 0.21/0.45      ((((k2_pre_topc @ sk_A @ sk_B_2) = (u1_struct_0 @ sk_A)))
% 0.21/0.45         <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.21/0.45      inference('sup-', [status(thm)], ['32', '37'])).
% 0.21/0.45  thf('39', plain,
% 0.21/0.45      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('40', plain,
% 0.21/0.45      (((v3_pre_topc @ sk_B_2 @ sk_A)) <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.21/0.45      inference('split', [status(esa)], ['2'])).
% 0.21/0.45  thf('41', plain,
% 0.21/0.45      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf(t23_tdlat_3, axiom,
% 0.21/0.45    (![A:$i]:
% 0.21/0.45     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.45       ( ( v3_tdlat_3 @ A ) <=>
% 0.21/0.45         ( ![B:$i]:
% 0.21/0.45           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.45             ( ( v3_pre_topc @ B @ A ) => ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.21/0.45  thf('42', plain,
% 0.21/0.45      (![X12 : $i, X13 : $i]:
% 0.21/0.45         (~ (v3_tdlat_3 @ X12)
% 0.21/0.45          | ~ (v3_pre_topc @ X13 @ X12)
% 0.21/0.45          | (v4_pre_topc @ X13 @ X12)
% 0.21/0.45          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.21/0.45          | ~ (l1_pre_topc @ X12)
% 0.21/0.45          | ~ (v2_pre_topc @ X12))),
% 0.21/0.45      inference('cnf', [status(esa)], [t23_tdlat_3])).
% 0.21/0.45  thf('43', plain,
% 0.21/0.45      ((~ (v2_pre_topc @ sk_A)
% 0.21/0.45        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.45        | (v4_pre_topc @ sk_B_2 @ sk_A)
% 0.21/0.45        | ~ (v3_pre_topc @ sk_B_2 @ sk_A)
% 0.21/0.45        | ~ (v3_tdlat_3 @ sk_A))),
% 0.21/0.45      inference('sup-', [status(thm)], ['41', '42'])).
% 0.21/0.45  thf('44', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('46', plain, ((v3_tdlat_3 @ sk_A)),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('47', plain,
% 0.21/0.45      (((v4_pre_topc @ sk_B_2 @ sk_A) | ~ (v3_pre_topc @ sk_B_2 @ sk_A))),
% 0.21/0.45      inference('demod', [status(thm)], ['43', '44', '45', '46'])).
% 0.21/0.45  thf('48', plain,
% 0.21/0.45      (((v4_pre_topc @ sk_B_2 @ sk_A)) <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.21/0.45      inference('sup-', [status(thm)], ['40', '47'])).
% 0.21/0.45  thf('49', plain,
% 0.21/0.45      (![X0 : $i]:
% 0.21/0.45         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.45          | (r1_tarski @ (k2_pre_topc @ sk_A @ X0) @ sk_B_2)
% 0.21/0.45          | ~ (r1_tarski @ X0 @ sk_B_2)
% 0.21/0.45          | ~ (v4_pre_topc @ sk_B_2 @ sk_A))),
% 0.21/0.45      inference('demod', [status(thm)], ['6', '7'])).
% 0.21/0.45  thf('50', plain,
% 0.21/0.45      ((![X0 : $i]:
% 0.21/0.45          (~ (r1_tarski @ X0 @ sk_B_2)
% 0.21/0.45           | (r1_tarski @ (k2_pre_topc @ sk_A @ X0) @ sk_B_2)
% 0.21/0.45           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.21/0.45         <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.21/0.45      inference('sup-', [status(thm)], ['48', '49'])).
% 0.21/0.45  thf('51', plain,
% 0.21/0.45      ((((r1_tarski @ (k2_pre_topc @ sk_A @ sk_B_2) @ sk_B_2)
% 0.21/0.45         | ~ (r1_tarski @ sk_B_2 @ sk_B_2)))
% 0.21/0.45         <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.21/0.45      inference('sup-', [status(thm)], ['39', '50'])).
% 0.21/0.45  thf('52', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.21/0.45      inference('simplify', [status(thm)], ['11'])).
% 0.21/0.45  thf('53', plain,
% 0.21/0.45      (((r1_tarski @ (k2_pre_topc @ sk_A @ sk_B_2) @ sk_B_2))
% 0.21/0.45         <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.21/0.45      inference('demod', [status(thm)], ['51', '52'])).
% 0.21/0.45  thf('54', plain,
% 0.21/0.45      ((~ (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B_2) @ sk_B_2)
% 0.21/0.45        | ((k2_pre_topc @ sk_A @ sk_B_2) = (sk_B_2)))),
% 0.21/0.45      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.45  thf('55', plain,
% 0.21/0.45      ((((k2_pre_topc @ sk_A @ sk_B_2) = (sk_B_2)))
% 0.21/0.45         <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.21/0.45      inference('sup-', [status(thm)], ['53', '54'])).
% 0.21/0.45  thf('56', plain,
% 0.21/0.45      ((((u1_struct_0 @ sk_A) = (sk_B_2))) <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.21/0.45      inference('sup+', [status(thm)], ['38', '55'])).
% 0.21/0.45  thf('57', plain, ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('58', plain,
% 0.21/0.45      (((v1_subset_1 @ sk_B_2 @ sk_B_2)) <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.21/0.45      inference('sup+', [status(thm)], ['56', '57'])).
% 0.21/0.45  thf(fc14_subset_1, axiom,
% 0.21/0.45    (![A:$i]: ( ~( v1_subset_1 @ ( k2_subset_1 @ A ) @ A ) ))).
% 0.21/0.45  thf('59', plain, (![X4 : $i]: ~ (v1_subset_1 @ (k2_subset_1 @ X4) @ X4)),
% 0.21/0.45      inference('cnf', [status(esa)], [fc14_subset_1])).
% 0.21/0.45  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.21/0.45  thf('60', plain, (![X3 : $i]: ((k2_subset_1 @ X3) = (X3))),
% 0.21/0.45      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.21/0.45  thf('61', plain, (![X4 : $i]: ~ (v1_subset_1 @ X4 @ X4)),
% 0.21/0.45      inference('demod', [status(thm)], ['59', '60'])).
% 0.21/0.45  thf('62', plain, (~ ((v3_pre_topc @ sk_B_2 @ sk_A))),
% 0.21/0.45      inference('sup-', [status(thm)], ['58', '61'])).
% 0.21/0.45  thf('63', plain,
% 0.21/0.45      (((v4_pre_topc @ sk_B_2 @ sk_A)) | ((v3_pre_topc @ sk_B_2 @ sk_A))),
% 0.21/0.45      inference('split', [status(esa)], ['2'])).
% 0.21/0.45  thf('64', plain, (((v4_pre_topc @ sk_B_2 @ sk_A))),
% 0.21/0.45      inference('sat_resolution*', [status(thm)], ['62', '63'])).
% 0.21/0.45  thf('65', plain, (((k2_pre_topc @ sk_A @ sk_B_2) = (sk_B_2))),
% 0.21/0.45      inference('simpl_trail', [status(thm)], ['21', '64'])).
% 0.21/0.45  thf('66', plain,
% 0.21/0.45      (((v4_pre_topc @ sk_B_2 @ sk_A)) <= (((v4_pre_topc @ sk_B_2 @ sk_A)))),
% 0.21/0.45      inference('split', [status(esa)], ['2'])).
% 0.21/0.45  thf('67', plain,
% 0.21/0.45      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf(t24_tdlat_3, axiom,
% 0.21/0.45    (![A:$i]:
% 0.21/0.45     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.45       ( ( v3_tdlat_3 @ A ) <=>
% 0.21/0.45         ( ![B:$i]:
% 0.21/0.45           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.45             ( ( v4_pre_topc @ B @ A ) => ( v3_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.21/0.45  thf('68', plain,
% 0.21/0.45      (![X14 : $i, X15 : $i]:
% 0.21/0.45         (~ (v3_tdlat_3 @ X14)
% 0.21/0.45          | ~ (v4_pre_topc @ X15 @ X14)
% 0.21/0.45          | (v3_pre_topc @ X15 @ X14)
% 0.21/0.45          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.21/0.45          | ~ (l1_pre_topc @ X14)
% 0.21/0.45          | ~ (v2_pre_topc @ X14))),
% 0.21/0.45      inference('cnf', [status(esa)], [t24_tdlat_3])).
% 0.21/0.45  thf('69', plain,
% 0.21/0.45      ((~ (v2_pre_topc @ sk_A)
% 0.21/0.45        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.45        | (v3_pre_topc @ sk_B_2 @ sk_A)
% 0.21/0.45        | ~ (v4_pre_topc @ sk_B_2 @ sk_A)
% 0.21/0.45        | ~ (v3_tdlat_3 @ sk_A))),
% 0.21/0.45      inference('sup-', [status(thm)], ['67', '68'])).
% 0.21/0.45  thf('70', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('71', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('72', plain, ((v3_tdlat_3 @ sk_A)),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('73', plain,
% 0.21/0.45      (((v3_pre_topc @ sk_B_2 @ sk_A) | ~ (v4_pre_topc @ sk_B_2 @ sk_A))),
% 0.21/0.45      inference('demod', [status(thm)], ['69', '70', '71', '72'])).
% 0.21/0.45  thf('74', plain,
% 0.21/0.45      (((v3_pre_topc @ sk_B_2 @ sk_A)) <= (((v4_pre_topc @ sk_B_2 @ sk_A)))),
% 0.21/0.45      inference('sup-', [status(thm)], ['66', '73'])).
% 0.21/0.45  thf('75', plain,
% 0.21/0.45      (((v1_tops_1 @ sk_B_2 @ sk_A) | ~ (v3_pre_topc @ sk_B_2 @ sk_A))),
% 0.21/0.45      inference('clc', [status(thm)], ['29', '30'])).
% 0.21/0.45  thf('76', plain,
% 0.21/0.45      (((v1_tops_1 @ sk_B_2 @ sk_A)) <= (((v4_pre_topc @ sk_B_2 @ sk_A)))),
% 0.21/0.45      inference('sup-', [status(thm)], ['74', '75'])).
% 0.21/0.45  thf('77', plain,
% 0.21/0.45      ((((k2_pre_topc @ sk_A @ sk_B_2) = (u1_struct_0 @ sk_A))
% 0.21/0.45        | ~ (v1_tops_1 @ sk_B_2 @ sk_A))),
% 0.21/0.45      inference('demod', [status(thm)], ['35', '36'])).
% 0.21/0.45  thf('78', plain,
% 0.21/0.45      ((((k2_pre_topc @ sk_A @ sk_B_2) = (u1_struct_0 @ sk_A)))
% 0.21/0.45         <= (((v4_pre_topc @ sk_B_2 @ sk_A)))),
% 0.21/0.45      inference('sup-', [status(thm)], ['76', '77'])).
% 0.21/0.45  thf('79', plain, (((v4_pre_topc @ sk_B_2 @ sk_A))),
% 0.21/0.45      inference('sat_resolution*', [status(thm)], ['62', '63'])).
% 0.21/0.45  thf('80', plain, (((k2_pre_topc @ sk_A @ sk_B_2) = (u1_struct_0 @ sk_A))),
% 0.21/0.45      inference('simpl_trail', [status(thm)], ['78', '79'])).
% 0.21/0.45  thf('81', plain, (((sk_B_2) = (u1_struct_0 @ sk_A))),
% 0.21/0.45      inference('sup+', [status(thm)], ['65', '80'])).
% 0.21/0.45  thf('82', plain, ((v1_subset_1 @ sk_B_2 @ sk_B_2)),
% 0.21/0.45      inference('demod', [status(thm)], ['0', '81'])).
% 0.21/0.45  thf('83', plain, (![X4 : $i]: ~ (v1_subset_1 @ X4 @ X4)),
% 0.21/0.45      inference('demod', [status(thm)], ['59', '60'])).
% 0.21/0.45  thf('84', plain, ($false), inference('sup-', [status(thm)], ['82', '83'])).
% 0.21/0.45  
% 0.21/0.45  % SZS output end Refutation
% 0.21/0.45  
% 0.21/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
