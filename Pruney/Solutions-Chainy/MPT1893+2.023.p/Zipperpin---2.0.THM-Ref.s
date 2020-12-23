%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.oXZPy3MuQA

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:36 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 300 expanded)
%              Number of leaves         :   27 (  95 expanded)
%              Depth                    :   15
%              Number of atoms          :  761 (4225 expanded)
%              Number of equality atoms :   24 (  47 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( v3_pre_topc @ sk_B_1 @ sk_A )
    | ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( v4_pre_topc @ sk_B_1 @ sk_A )
   <= ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['1'])).

thf('3',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t52_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v4_pre_topc @ B @ A )
             => ( ( k2_pre_topc @ A @ B )
                = B ) )
            & ( ( ( v2_pre_topc @ A )
                & ( ( k2_pre_topc @ A @ B )
                  = B ) )
             => ( v4_pre_topc @ B @ A ) ) ) ) ) )).

thf('4',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( v4_pre_topc @ X6 @ X7 )
      | ( ( k2_pre_topc @ X7 @ X6 )
        = X6 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('5',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = sk_B_1 )
    | ~ ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = sk_B_1 )
    | ~ ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = sk_B_1 )
   <= ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf('9',plain,
    ( ( v3_pre_topc @ sk_B_1 @ sk_A )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['1'])).

thf('10',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('11',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( v1_tops_1 @ X14 @ X15 )
      | ~ ( v3_tex_2 @ X14 @ X15 )
      | ~ ( v3_pre_topc @ X14 @ X15 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t47_tex_2])).

thf('12',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_tops_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v3_tex_2 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_1 @ sk_A )
    | ( v1_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['12','13','14','15'])).

thf('17',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( v1_tops_1 @ sk_B_1 @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( v1_tops_1 @ sk_B_1 @ sk_A )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['9','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_tops_3,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( u1_struct_0 @ A ) ) ) ) ) )).

thf('21',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( v1_tops_1 @ X10 @ X11 )
      | ( ( k2_pre_topc @ X11 @ X10 )
        = ( u1_struct_0 @ X11 ) )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_3])).

thf('22',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = ( u1_struct_0 @ sk_A ) )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['19','24'])).

thf('26',plain,
    ( ( v3_pre_topc @ sk_B_1 @ sk_A )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['1'])).

thf('27',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('28',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v3_tdlat_3 @ X12 )
      | ~ ( v3_pre_topc @ X13 @ X12 )
      | ( v4_pre_topc @ X13 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t23_tdlat_3])).

thf('29',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( v4_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['29','30','31','32'])).

thf('34',plain,
    ( ( v4_pre_topc @ sk_B_1 @ sk_A )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['26','33'])).

thf('35',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = sk_B_1 )
    | ~ ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('36',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = sk_B_1 )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_1 )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['25','36'])).

thf('38',plain,(
    v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( v1_subset_1 @ sk_B_1 @ sk_B_1 )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf(fc14_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_subset_1 @ ( k2_subset_1 @ A ) @ A ) )).

thf('40',plain,(
    ! [X5: $i] :
      ~ ( v1_subset_1 @ ( k2_subset_1 @ X5 ) @ X5 ) ),
    inference(cnf,[status(esa)],[fc14_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k2_subset_1 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('42',plain,(
    ! [X5: $i] :
      ~ ( v1_subset_1 @ X5 @ X5 ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,
    ( ( v4_pre_topc @ sk_B_1 @ sk_A )
    | ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['1'])).

thf('45',plain,(
    v4_pre_topc @ sk_B_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_1 )
    = sk_B_1 ),
    inference(simpl_trail,[status(thm)],['8','45'])).

thf('47',plain,
    ( ( v4_pre_topc @ sk_B_1 @ sk_A )
   <= ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['1'])).

thf('48',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('49',plain,(
    ! [X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X1 @ X2 ) @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('50',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf(t30_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('51',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X9 ) @ X8 ) @ X9 )
      | ( v3_pre_topc @ X8 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[t30_tops_1])).

thf('52',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
    | ~ ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('55',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k3_subset_1 @ X4 @ ( k3_subset_1 @ X4 @ X3 ) )
        = X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('56',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
    | ~ ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['52','53','56'])).

thf('58',plain,
    ( ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
   <= ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['47','57'])).

thf('59',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('60',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v3_tdlat_3 @ X12 )
      | ~ ( v3_pre_topc @ X13 @ X12 )
      | ( v4_pre_topc @ X13 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t23_tdlat_3])).

thf('61',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
    | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
    | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['61','62','63','64'])).

thf('66',plain,
    ( ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
   <= ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['58','65'])).

thf('67',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X9 ) @ X8 ) @ X9 )
      | ( v3_pre_topc @ X8 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[t30_tops_1])).

thf('69',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( v3_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( v3_pre_topc @ sk_B_1 @ sk_A )
   <= ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['66','71'])).

thf('73',plain,
    ( ( v1_tops_1 @ sk_B_1 @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('74',plain,
    ( ( v1_tops_1 @ sk_B_1 @ sk_A )
   <= ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('76',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = ( u1_struct_0 @ sk_A ) )
   <= ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    v4_pre_topc @ sk_B_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['43','44'])).

thf('78',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['76','77'])).

thf('79',plain,
    ( sk_B_1
    = ( u1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['46','78'])).

thf('80',plain,(
    v1_subset_1 @ sk_B_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['0','79'])).

thf('81',plain,(
    ! [X5: $i] :
      ~ ( v1_subset_1 @ X5 @ X5 ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('82',plain,(
    $false ),
    inference('sup-',[status(thm)],['80','81'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.oXZPy3MuQA
% 0.14/0.36  % Computer   : n016.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 13:57:34 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 0.22/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.56  % Solved by: fo/fo7.sh
% 0.22/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.56  % done 117 iterations in 0.085s
% 0.22/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.56  % SZS output start Refutation
% 0.22/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.56  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.22/0.56  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.56  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.22/0.56  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.22/0.56  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.22/0.56  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.22/0.56  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.22/0.56  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.22/0.56  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.22/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.56  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.56  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.22/0.56  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.22/0.56  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.22/0.56  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.22/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.56  thf(t61_tex_2, conjecture,
% 0.22/0.56    (![A:$i]:
% 0.22/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.22/0.56         ( l1_pre_topc @ A ) ) =>
% 0.22/0.56       ( ![B:$i]:
% 0.22/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.56           ( ~( ( ( v3_pre_topc @ B @ A ) | ( v4_pre_topc @ B @ A ) ) & 
% 0.22/0.56                ( v3_tex_2 @ B @ A ) & 
% 0.22/0.56                ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.22/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.56    (~( ![A:$i]:
% 0.22/0.56        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.22/0.56            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.56          ( ![B:$i]:
% 0.22/0.56            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.56              ( ~( ( ( v3_pre_topc @ B @ A ) | ( v4_pre_topc @ B @ A ) ) & 
% 0.22/0.56                   ( v3_tex_2 @ B @ A ) & 
% 0.22/0.56                   ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )),
% 0.22/0.56    inference('cnf.neg', [status(esa)], [t61_tex_2])).
% 0.22/0.56  thf('0', plain, ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('1', plain,
% 0.22/0.56      (((v3_pre_topc @ sk_B_1 @ sk_A) | (v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('2', plain,
% 0.22/0.56      (((v4_pre_topc @ sk_B_1 @ sk_A)) <= (((v4_pre_topc @ sk_B_1 @ sk_A)))),
% 0.22/0.56      inference('split', [status(esa)], ['1'])).
% 0.22/0.56  thf('3', plain,
% 0.22/0.56      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf(t52_pre_topc, axiom,
% 0.22/0.56    (![A:$i]:
% 0.22/0.56     ( ( l1_pre_topc @ A ) =>
% 0.22/0.56       ( ![B:$i]:
% 0.22/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.56           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.22/0.56             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.22/0.56               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.22/0.56  thf('4', plain,
% 0.22/0.56      (![X6 : $i, X7 : $i]:
% 0.22/0.56         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.22/0.56          | ~ (v4_pre_topc @ X6 @ X7)
% 0.22/0.56          | ((k2_pre_topc @ X7 @ X6) = (X6))
% 0.22/0.56          | ~ (l1_pre_topc @ X7))),
% 0.22/0.56      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.22/0.56  thf('5', plain,
% 0.22/0.56      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.56        | ((k2_pre_topc @ sk_A @ sk_B_1) = (sk_B_1))
% 0.22/0.56        | ~ (v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.22/0.56      inference('sup-', [status(thm)], ['3', '4'])).
% 0.22/0.56  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('7', plain,
% 0.22/0.56      ((((k2_pre_topc @ sk_A @ sk_B_1) = (sk_B_1))
% 0.22/0.56        | ~ (v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.22/0.56      inference('demod', [status(thm)], ['5', '6'])).
% 0.22/0.56  thf('8', plain,
% 0.22/0.56      ((((k2_pre_topc @ sk_A @ sk_B_1) = (sk_B_1)))
% 0.22/0.56         <= (((v4_pre_topc @ sk_B_1 @ sk_A)))),
% 0.22/0.56      inference('sup-', [status(thm)], ['2', '7'])).
% 0.22/0.56  thf('9', plain,
% 0.22/0.56      (((v3_pre_topc @ sk_B_1 @ sk_A)) <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.22/0.56      inference('split', [status(esa)], ['1'])).
% 0.22/0.56  thf('10', plain,
% 0.22/0.56      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf(t47_tex_2, axiom,
% 0.22/0.56    (![A:$i]:
% 0.22/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.56       ( ![B:$i]:
% 0.22/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.56           ( ( ( v3_pre_topc @ B @ A ) & ( v3_tex_2 @ B @ A ) ) =>
% 0.22/0.56             ( v1_tops_1 @ B @ A ) ) ) ) ))).
% 0.22/0.56  thf('11', plain,
% 0.22/0.56      (![X14 : $i, X15 : $i]:
% 0.22/0.56         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.22/0.56          | (v1_tops_1 @ X14 @ X15)
% 0.22/0.56          | ~ (v3_tex_2 @ X14 @ X15)
% 0.22/0.56          | ~ (v3_pre_topc @ X14 @ X15)
% 0.22/0.56          | ~ (l1_pre_topc @ X15)
% 0.22/0.56          | ~ (v2_pre_topc @ X15)
% 0.22/0.56          | (v2_struct_0 @ X15))),
% 0.22/0.56      inference('cnf', [status(esa)], [t47_tex_2])).
% 0.22/0.56  thf('12', plain,
% 0.22/0.56      (((v2_struct_0 @ sk_A)
% 0.22/0.56        | ~ (v2_pre_topc @ sk_A)
% 0.22/0.56        | ~ (l1_pre_topc @ sk_A)
% 0.22/0.56        | ~ (v3_pre_topc @ sk_B_1 @ sk_A)
% 0.22/0.56        | ~ (v3_tex_2 @ sk_B_1 @ sk_A)
% 0.22/0.56        | (v1_tops_1 @ sk_B_1 @ sk_A))),
% 0.22/0.56      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.56  thf('13', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('15', plain, ((v3_tex_2 @ sk_B_1 @ sk_A)),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('16', plain,
% 0.22/0.56      (((v2_struct_0 @ sk_A)
% 0.22/0.56        | ~ (v3_pre_topc @ sk_B_1 @ sk_A)
% 0.22/0.56        | (v1_tops_1 @ sk_B_1 @ sk_A))),
% 0.22/0.56      inference('demod', [status(thm)], ['12', '13', '14', '15'])).
% 0.22/0.56  thf('17', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('18', plain,
% 0.22/0.56      (((v1_tops_1 @ sk_B_1 @ sk_A) | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.22/0.56      inference('clc', [status(thm)], ['16', '17'])).
% 0.22/0.56  thf('19', plain,
% 0.22/0.56      (((v1_tops_1 @ sk_B_1 @ sk_A)) <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.22/0.56      inference('sup-', [status(thm)], ['9', '18'])).
% 0.22/0.56  thf('20', plain,
% 0.22/0.56      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf(d2_tops_3, axiom,
% 0.22/0.56    (![A:$i]:
% 0.22/0.56     ( ( l1_pre_topc @ A ) =>
% 0.22/0.56       ( ![B:$i]:
% 0.22/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.56           ( ( v1_tops_1 @ B @ A ) <=>
% 0.22/0.56             ( ( k2_pre_topc @ A @ B ) = ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.22/0.56  thf('21', plain,
% 0.22/0.56      (![X10 : $i, X11 : $i]:
% 0.22/0.56         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.22/0.56          | ~ (v1_tops_1 @ X10 @ X11)
% 0.22/0.56          | ((k2_pre_topc @ X11 @ X10) = (u1_struct_0 @ X11))
% 0.22/0.56          | ~ (l1_pre_topc @ X11))),
% 0.22/0.56      inference('cnf', [status(esa)], [d2_tops_3])).
% 0.22/0.56  thf('22', plain,
% 0.22/0.56      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.56        | ((k2_pre_topc @ sk_A @ sk_B_1) = (u1_struct_0 @ sk_A))
% 0.22/0.56        | ~ (v1_tops_1 @ sk_B_1 @ sk_A))),
% 0.22/0.56      inference('sup-', [status(thm)], ['20', '21'])).
% 0.22/0.56  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('24', plain,
% 0.22/0.56      ((((k2_pre_topc @ sk_A @ sk_B_1) = (u1_struct_0 @ sk_A))
% 0.22/0.56        | ~ (v1_tops_1 @ sk_B_1 @ sk_A))),
% 0.22/0.56      inference('demod', [status(thm)], ['22', '23'])).
% 0.22/0.56  thf('25', plain,
% 0.22/0.56      ((((k2_pre_topc @ sk_A @ sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.22/0.56         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.22/0.56      inference('sup-', [status(thm)], ['19', '24'])).
% 0.22/0.56  thf('26', plain,
% 0.22/0.56      (((v3_pre_topc @ sk_B_1 @ sk_A)) <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.22/0.56      inference('split', [status(esa)], ['1'])).
% 0.22/0.56  thf('27', plain,
% 0.22/0.56      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf(t23_tdlat_3, axiom,
% 0.22/0.56    (![A:$i]:
% 0.22/0.56     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.56       ( ( v3_tdlat_3 @ A ) <=>
% 0.22/0.56         ( ![B:$i]:
% 0.22/0.56           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.56             ( ( v3_pre_topc @ B @ A ) => ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.22/0.56  thf('28', plain,
% 0.22/0.56      (![X12 : $i, X13 : $i]:
% 0.22/0.56         (~ (v3_tdlat_3 @ X12)
% 0.22/0.56          | ~ (v3_pre_topc @ X13 @ X12)
% 0.22/0.56          | (v4_pre_topc @ X13 @ X12)
% 0.22/0.56          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.22/0.56          | ~ (l1_pre_topc @ X12)
% 0.22/0.56          | ~ (v2_pre_topc @ X12))),
% 0.22/0.56      inference('cnf', [status(esa)], [t23_tdlat_3])).
% 0.22/0.56  thf('29', plain,
% 0.22/0.56      ((~ (v2_pre_topc @ sk_A)
% 0.22/0.56        | ~ (l1_pre_topc @ sk_A)
% 0.22/0.56        | (v4_pre_topc @ sk_B_1 @ sk_A)
% 0.22/0.56        | ~ (v3_pre_topc @ sk_B_1 @ sk_A)
% 0.22/0.56        | ~ (v3_tdlat_3 @ sk_A))),
% 0.22/0.56      inference('sup-', [status(thm)], ['27', '28'])).
% 0.22/0.56  thf('30', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('32', plain, ((v3_tdlat_3 @ sk_A)),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('33', plain,
% 0.22/0.56      (((v4_pre_topc @ sk_B_1 @ sk_A) | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.22/0.56      inference('demod', [status(thm)], ['29', '30', '31', '32'])).
% 0.22/0.56  thf('34', plain,
% 0.22/0.56      (((v4_pre_topc @ sk_B_1 @ sk_A)) <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.22/0.56      inference('sup-', [status(thm)], ['26', '33'])).
% 0.22/0.56  thf('35', plain,
% 0.22/0.56      ((((k2_pre_topc @ sk_A @ sk_B_1) = (sk_B_1))
% 0.22/0.56        | ~ (v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.22/0.56      inference('demod', [status(thm)], ['5', '6'])).
% 0.22/0.56  thf('36', plain,
% 0.22/0.56      ((((k2_pre_topc @ sk_A @ sk_B_1) = (sk_B_1)))
% 0.22/0.56         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.22/0.56      inference('sup-', [status(thm)], ['34', '35'])).
% 0.22/0.56  thf('37', plain,
% 0.22/0.56      ((((u1_struct_0 @ sk_A) = (sk_B_1))) <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.22/0.56      inference('sup+', [status(thm)], ['25', '36'])).
% 0.22/0.56  thf('38', plain, ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('39', plain,
% 0.22/0.56      (((v1_subset_1 @ sk_B_1 @ sk_B_1)) <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.22/0.56      inference('sup+', [status(thm)], ['37', '38'])).
% 0.22/0.56  thf(fc14_subset_1, axiom,
% 0.22/0.56    (![A:$i]: ( ~( v1_subset_1 @ ( k2_subset_1 @ A ) @ A ) ))).
% 0.22/0.56  thf('40', plain, (![X5 : $i]: ~ (v1_subset_1 @ (k2_subset_1 @ X5) @ X5)),
% 0.22/0.56      inference('cnf', [status(esa)], [fc14_subset_1])).
% 0.22/0.56  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.22/0.56  thf('41', plain, (![X0 : $i]: ((k2_subset_1 @ X0) = (X0))),
% 0.22/0.56      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.22/0.56  thf('42', plain, (![X5 : $i]: ~ (v1_subset_1 @ X5 @ X5)),
% 0.22/0.56      inference('demod', [status(thm)], ['40', '41'])).
% 0.22/0.56  thf('43', plain, (~ ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.22/0.56      inference('sup-', [status(thm)], ['39', '42'])).
% 0.22/0.56  thf('44', plain,
% 0.22/0.56      (((v4_pre_topc @ sk_B_1 @ sk_A)) | ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.22/0.56      inference('split', [status(esa)], ['1'])).
% 0.22/0.56  thf('45', plain, (((v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.22/0.56      inference('sat_resolution*', [status(thm)], ['43', '44'])).
% 0.22/0.56  thf('46', plain, (((k2_pre_topc @ sk_A @ sk_B_1) = (sk_B_1))),
% 0.22/0.56      inference('simpl_trail', [status(thm)], ['8', '45'])).
% 0.22/0.56  thf('47', plain,
% 0.22/0.56      (((v4_pre_topc @ sk_B_1 @ sk_A)) <= (((v4_pre_topc @ sk_B_1 @ sk_A)))),
% 0.22/0.56      inference('split', [status(esa)], ['1'])).
% 0.22/0.56  thf('48', plain,
% 0.22/0.56      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf(dt_k3_subset_1, axiom,
% 0.22/0.56    (![A:$i,B:$i]:
% 0.22/0.56     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.56       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.22/0.56  thf('49', plain,
% 0.22/0.56      (![X1 : $i, X2 : $i]:
% 0.22/0.56         ((m1_subset_1 @ (k3_subset_1 @ X1 @ X2) @ (k1_zfmisc_1 @ X1))
% 0.22/0.56          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X1)))),
% 0.22/0.56      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.22/0.56  thf('50', plain,
% 0.22/0.56      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.22/0.56        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.56      inference('sup-', [status(thm)], ['48', '49'])).
% 0.22/0.56  thf(t30_tops_1, axiom,
% 0.22/0.56    (![A:$i]:
% 0.22/0.56     ( ( l1_pre_topc @ A ) =>
% 0.22/0.56       ( ![B:$i]:
% 0.22/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.56           ( ( v3_pre_topc @ B @ A ) <=>
% 0.22/0.56             ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.22/0.56  thf('51', plain,
% 0.22/0.56      (![X8 : $i, X9 : $i]:
% 0.22/0.56         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.22/0.56          | ~ (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X9) @ X8) @ X9)
% 0.22/0.56          | (v3_pre_topc @ X8 @ X9)
% 0.22/0.56          | ~ (l1_pre_topc @ X9))),
% 0.22/0.56      inference('cnf', [status(esa)], [t30_tops_1])).
% 0.22/0.56  thf('52', plain,
% 0.22/0.56      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.56        | (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 0.22/0.56        | ~ (v4_pre_topc @ 
% 0.22/0.56             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.56              (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)) @ 
% 0.22/0.56             sk_A))),
% 0.22/0.56      inference('sup-', [status(thm)], ['50', '51'])).
% 0.22/0.56  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('54', plain,
% 0.22/0.56      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf(involutiveness_k3_subset_1, axiom,
% 0.22/0.56    (![A:$i,B:$i]:
% 0.22/0.56     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.56       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.22/0.56  thf('55', plain,
% 0.22/0.56      (![X3 : $i, X4 : $i]:
% 0.22/0.56         (((k3_subset_1 @ X4 @ (k3_subset_1 @ X4 @ X3)) = (X3))
% 0.22/0.56          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.22/0.56      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.22/0.56  thf('56', plain,
% 0.22/0.56      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.56         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)) = (sk_B_1))),
% 0.22/0.56      inference('sup-', [status(thm)], ['54', '55'])).
% 0.22/0.56  thf('57', plain,
% 0.22/0.56      (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 0.22/0.56        | ~ (v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.22/0.56      inference('demod', [status(thm)], ['52', '53', '56'])).
% 0.22/0.56  thf('58', plain,
% 0.22/0.56      (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A))
% 0.22/0.56         <= (((v4_pre_topc @ sk_B_1 @ sk_A)))),
% 0.22/0.56      inference('sup-', [status(thm)], ['47', '57'])).
% 0.22/0.56  thf('59', plain,
% 0.22/0.56      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.22/0.56        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.56      inference('sup-', [status(thm)], ['48', '49'])).
% 0.22/0.56  thf('60', plain,
% 0.22/0.56      (![X12 : $i, X13 : $i]:
% 0.22/0.56         (~ (v3_tdlat_3 @ X12)
% 0.22/0.56          | ~ (v3_pre_topc @ X13 @ X12)
% 0.22/0.56          | (v4_pre_topc @ X13 @ X12)
% 0.22/0.56          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.22/0.56          | ~ (l1_pre_topc @ X12)
% 0.22/0.56          | ~ (v2_pre_topc @ X12))),
% 0.22/0.56      inference('cnf', [status(esa)], [t23_tdlat_3])).
% 0.22/0.56  thf('61', plain,
% 0.22/0.56      ((~ (v2_pre_topc @ sk_A)
% 0.22/0.56        | ~ (l1_pre_topc @ sk_A)
% 0.22/0.56        | (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 0.22/0.56        | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 0.22/0.56        | ~ (v3_tdlat_3 @ sk_A))),
% 0.22/0.56      inference('sup-', [status(thm)], ['59', '60'])).
% 0.22/0.56  thf('62', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('63', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('64', plain, ((v3_tdlat_3 @ sk_A)),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('65', plain,
% 0.22/0.56      (((v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 0.22/0.56        | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A))),
% 0.22/0.56      inference('demod', [status(thm)], ['61', '62', '63', '64'])).
% 0.22/0.56  thf('66', plain,
% 0.22/0.56      (((v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A))
% 0.22/0.56         <= (((v4_pre_topc @ sk_B_1 @ sk_A)))),
% 0.22/0.56      inference('sup-', [status(thm)], ['58', '65'])).
% 0.22/0.56  thf('67', plain,
% 0.22/0.56      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('68', plain,
% 0.22/0.56      (![X8 : $i, X9 : $i]:
% 0.22/0.56         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.22/0.56          | ~ (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X9) @ X8) @ X9)
% 0.22/0.56          | (v3_pre_topc @ X8 @ X9)
% 0.22/0.56          | ~ (l1_pre_topc @ X9))),
% 0.22/0.56      inference('cnf', [status(esa)], [t30_tops_1])).
% 0.22/0.56  thf('69', plain,
% 0.22/0.56      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.56        | (v3_pre_topc @ sk_B_1 @ sk_A)
% 0.22/0.56        | ~ (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A))),
% 0.22/0.56      inference('sup-', [status(thm)], ['67', '68'])).
% 0.22/0.56  thf('70', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('71', plain,
% 0.22/0.56      (((v3_pre_topc @ sk_B_1 @ sk_A)
% 0.22/0.56        | ~ (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A))),
% 0.22/0.56      inference('demod', [status(thm)], ['69', '70'])).
% 0.22/0.56  thf('72', plain,
% 0.22/0.56      (((v3_pre_topc @ sk_B_1 @ sk_A)) <= (((v4_pre_topc @ sk_B_1 @ sk_A)))),
% 0.22/0.56      inference('sup-', [status(thm)], ['66', '71'])).
% 0.22/0.56  thf('73', plain,
% 0.22/0.56      (((v1_tops_1 @ sk_B_1 @ sk_A) | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.22/0.56      inference('clc', [status(thm)], ['16', '17'])).
% 0.22/0.56  thf('74', plain,
% 0.22/0.56      (((v1_tops_1 @ sk_B_1 @ sk_A)) <= (((v4_pre_topc @ sk_B_1 @ sk_A)))),
% 0.22/0.56      inference('sup-', [status(thm)], ['72', '73'])).
% 0.22/0.56  thf('75', plain,
% 0.22/0.56      ((((k2_pre_topc @ sk_A @ sk_B_1) = (u1_struct_0 @ sk_A))
% 0.22/0.56        | ~ (v1_tops_1 @ sk_B_1 @ sk_A))),
% 0.22/0.56      inference('demod', [status(thm)], ['22', '23'])).
% 0.22/0.56  thf('76', plain,
% 0.22/0.56      ((((k2_pre_topc @ sk_A @ sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.22/0.56         <= (((v4_pre_topc @ sk_B_1 @ sk_A)))),
% 0.22/0.56      inference('sup-', [status(thm)], ['74', '75'])).
% 0.22/0.56  thf('77', plain, (((v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.22/0.56      inference('sat_resolution*', [status(thm)], ['43', '44'])).
% 0.22/0.56  thf('78', plain, (((k2_pre_topc @ sk_A @ sk_B_1) = (u1_struct_0 @ sk_A))),
% 0.22/0.56      inference('simpl_trail', [status(thm)], ['76', '77'])).
% 0.22/0.56  thf('79', plain, (((sk_B_1) = (u1_struct_0 @ sk_A))),
% 0.22/0.56      inference('sup+', [status(thm)], ['46', '78'])).
% 0.22/0.56  thf('80', plain, ((v1_subset_1 @ sk_B_1 @ sk_B_1)),
% 0.22/0.56      inference('demod', [status(thm)], ['0', '79'])).
% 0.22/0.56  thf('81', plain, (![X5 : $i]: ~ (v1_subset_1 @ X5 @ X5)),
% 0.22/0.56      inference('demod', [status(thm)], ['40', '41'])).
% 0.22/0.56  thf('82', plain, ($false), inference('sup-', [status(thm)], ['80', '81'])).
% 0.22/0.56  
% 0.22/0.56  % SZS output end Refutation
% 0.22/0.56  
% 0.39/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
