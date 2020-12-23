%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.eC5QlHGCaZ

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:37 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 794 expanded)
%              Number of leaves         :   22 ( 224 expanded)
%              Depth                    :   17
%              Number of atoms          :  626 (12183 expanded)
%              Number of equality atoms :   23 ( 134 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

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
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( v3_pre_topc @ sk_B_2 @ sk_A )
    | ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( v4_pre_topc @ sk_B_2 @ sk_A )
   <= ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['1'])).

thf('3',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( v4_pre_topc @ X0 @ X1 )
      | ( ( k2_pre_topc @ X1 @ X0 )
        = X0 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('5',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = sk_B_2 )
    | ~ ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = sk_B_2 )
    | ~ ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = sk_B_2 )
   <= ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf('9',plain,
    ( ( v3_pre_topc @ sk_B_2 @ sk_A )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['1'])).

thf('10',plain,(
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

thf('11',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( v1_tops_1 @ X10 @ X11 )
      | ~ ( v3_tex_2 @ X10 @ X11 )
      | ~ ( v3_pre_topc @ X10 @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t47_tex_2])).

thf('12',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_2 @ sk_A )
    | ~ ( v3_tex_2 @ sk_B_2 @ sk_A )
    | ( v1_tops_1 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v3_tex_2 @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_2 @ sk_A )
    | ( v1_tops_1 @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['12','13','14','15'])).

thf('17',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( v1_tops_1 @ sk_B_2 @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( v1_tops_1 @ sk_B_2 @ sk_A )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['9','18'])).

thf('20',plain,(
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

thf('21',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ~ ( v1_tops_1 @ X2 @ X3 )
      | ( ( k2_pre_topc @ X3 @ X2 )
        = ( u1_struct_0 @ X3 ) )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_3])).

thf('22',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = ( u1_struct_0 @ sk_A ) )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['19','24'])).

thf('26',plain,
    ( ( v3_pre_topc @ sk_B_2 @ sk_A )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['1'])).

thf('27',plain,(
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

thf('28',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v3_tdlat_3 @ X6 )
      | ~ ( v3_pre_topc @ X7 @ X6 )
      | ( v4_pre_topc @ X7 @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( l1_pre_topc @ X6 )
      | ~ ( v2_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[t23_tdlat_3])).

thf('29',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B_2 @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_2 @ sk_A )
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
    ( ( v4_pre_topc @ sk_B_2 @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['29','30','31','32'])).

thf('34',plain,
    ( ( v4_pre_topc @ sk_B_2 @ sk_A )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['26','33'])).

thf('35',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = sk_B_2 )
    | ~ ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('36',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = sk_B_2 )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_2 )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup+',[status(thm)],['25','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ sk_B_2 ) )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('40',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_subset_1 @ X5 @ X4 )
      | ( X5 != X4 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('41',plain,(
    ! [X4: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X4 ) )
      | ~ ( v1_subset_1 @ X4 @ X4 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,
    ( ~ ( v1_subset_1 @ sk_B_2 @ sk_B_2 )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['39','41'])).

thf('43',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_2 )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup+',[status(thm)],['25','36'])).

thf('44',plain,(
    v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( v1_subset_1 @ sk_B_2 @ sk_B_2 )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ~ ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['42','45'])).

thf('47',plain,
    ( ( v4_pre_topc @ sk_B_2 @ sk_A )
    | ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['1'])).

thf('48',plain,(
    v4_pre_topc @ sk_B_2 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_2 )
    = sk_B_2 ),
    inference(simpl_trail,[status(thm)],['8','48'])).

thf('50',plain,
    ( ( v4_pre_topc @ sk_B_2 @ sk_A )
   <= ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['1'])).

thf('51',plain,(
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

thf('52',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v3_tdlat_3 @ X8 )
      | ~ ( v4_pre_topc @ X9 @ X8 )
      | ( v3_pre_topc @ X9 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[t24_tdlat_3])).

thf('53',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ sk_B_2 @ sk_A )
    | ~ ( v4_pre_topc @ sk_B_2 @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( v3_pre_topc @ sk_B_2 @ sk_A )
    | ~ ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['53','54','55','56'])).

thf('58',plain,
    ( ( v3_pre_topc @ sk_B_2 @ sk_A )
   <= ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['50','57'])).

thf('59',plain,
    ( ( v1_tops_1 @ sk_B_2 @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('60',plain,
    ( ( v1_tops_1 @ sk_B_2 @ sk_A )
   <= ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('62',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = ( u1_struct_0 @ sk_A ) )
   <= ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v4_pre_topc @ sk_B_2 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['46','47'])).

thf('64',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_2 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['62','63'])).

thf('65',plain,
    ( sk_B_2
    = ( u1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['49','64'])).

thf('66',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['0','65'])).

thf('67',plain,(
    ! [X4: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X4 ) )
      | ~ ( v1_subset_1 @ X4 @ X4 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('68',plain,(
    ~ ( v1_subset_1 @ sk_B_2 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( sk_B_2
    = ( u1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['49','64'])).

thf('71',plain,(
    v1_subset_1 @ sk_B_2 @ sk_B_2 ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    $false ),
    inference(demod,[status(thm)],['68','71'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.eC5QlHGCaZ
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:52:02 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 78 iterations in 0.047s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.50  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.20/0.50  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.20/0.50  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.20/0.50  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.50  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.20/0.50  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.20/0.50  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.20/0.50  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.50  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.20/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.50  thf(t61_tex_2, conjecture,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.20/0.50         ( l1_pre_topc @ A ) ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.50           ( ~( ( ( v3_pre_topc @ B @ A ) | ( v4_pre_topc @ B @ A ) ) & 
% 0.20/0.50                ( v3_tex_2 @ B @ A ) & 
% 0.20/0.50                ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i]:
% 0.20/0.50        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.50            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.50          ( ![B:$i]:
% 0.20/0.50            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.50              ( ~( ( ( v3_pre_topc @ B @ A ) | ( v4_pre_topc @ B @ A ) ) & 
% 0.20/0.50                   ( v3_tex_2 @ B @ A ) & 
% 0.20/0.50                   ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t61_tex_2])).
% 0.20/0.50  thf('0', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('1', plain,
% 0.20/0.50      (((v3_pre_topc @ sk_B_2 @ sk_A) | (v4_pre_topc @ sk_B_2 @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('2', plain,
% 0.20/0.50      (((v4_pre_topc @ sk_B_2 @ sk_A)) <= (((v4_pre_topc @ sk_B_2 @ sk_A)))),
% 0.20/0.50      inference('split', [status(esa)], ['1'])).
% 0.20/0.50  thf('3', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t52_pre_topc, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( l1_pre_topc @ A ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.50           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.20/0.50             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.20/0.50               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.20/0.50  thf('4', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.20/0.50          | ~ (v4_pre_topc @ X0 @ X1)
% 0.20/0.50          | ((k2_pre_topc @ X1 @ X0) = (X0))
% 0.20/0.50          | ~ (l1_pre_topc @ X1))),
% 0.20/0.50      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.20/0.50  thf('5', plain,
% 0.20/0.50      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.50        | ((k2_pre_topc @ sk_A @ sk_B_2) = (sk_B_2))
% 0.20/0.50        | ~ (v4_pre_topc @ sk_B_2 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.50  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('7', plain,
% 0.20/0.50      ((((k2_pre_topc @ sk_A @ sk_B_2) = (sk_B_2))
% 0.20/0.50        | ~ (v4_pre_topc @ sk_B_2 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['5', '6'])).
% 0.20/0.50  thf('8', plain,
% 0.20/0.50      ((((k2_pre_topc @ sk_A @ sk_B_2) = (sk_B_2)))
% 0.20/0.50         <= (((v4_pre_topc @ sk_B_2 @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['2', '7'])).
% 0.20/0.50  thf('9', plain,
% 0.20/0.50      (((v3_pre_topc @ sk_B_2 @ sk_A)) <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.20/0.50      inference('split', [status(esa)], ['1'])).
% 0.20/0.50  thf('10', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t47_tex_2, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.50           ( ( ( v3_pre_topc @ B @ A ) & ( v3_tex_2 @ B @ A ) ) =>
% 0.20/0.50             ( v1_tops_1 @ B @ A ) ) ) ) ))).
% 0.20/0.50  thf('11', plain,
% 0.20/0.50      (![X10 : $i, X11 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.20/0.50          | (v1_tops_1 @ X10 @ X11)
% 0.20/0.50          | ~ (v3_tex_2 @ X10 @ X11)
% 0.20/0.50          | ~ (v3_pre_topc @ X10 @ X11)
% 0.20/0.50          | ~ (l1_pre_topc @ X11)
% 0.20/0.50          | ~ (v2_pre_topc @ X11)
% 0.20/0.50          | (v2_struct_0 @ X11))),
% 0.20/0.50      inference('cnf', [status(esa)], [t47_tex_2])).
% 0.20/0.50  thf('12', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_A)
% 0.20/0.50        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.50        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.50        | ~ (v3_pre_topc @ sk_B_2 @ sk_A)
% 0.20/0.50        | ~ (v3_tex_2 @ sk_B_2 @ sk_A)
% 0.20/0.50        | (v1_tops_1 @ sk_B_2 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.50  thf('13', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('15', plain, ((v3_tex_2 @ sk_B_2 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('16', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_A)
% 0.20/0.50        | ~ (v3_pre_topc @ sk_B_2 @ sk_A)
% 0.20/0.50        | (v1_tops_1 @ sk_B_2 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['12', '13', '14', '15'])).
% 0.20/0.50  thf('17', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('18', plain,
% 0.20/0.50      (((v1_tops_1 @ sk_B_2 @ sk_A) | ~ (v3_pre_topc @ sk_B_2 @ sk_A))),
% 0.20/0.50      inference('clc', [status(thm)], ['16', '17'])).
% 0.20/0.50  thf('19', plain,
% 0.20/0.50      (((v1_tops_1 @ sk_B_2 @ sk_A)) <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['9', '18'])).
% 0.20/0.50  thf('20', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(d2_tops_3, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( l1_pre_topc @ A ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.50           ( ( v1_tops_1 @ B @ A ) <=>
% 0.20/0.50             ( ( k2_pre_topc @ A @ B ) = ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.20/0.50  thf('21', plain,
% 0.20/0.50      (![X2 : $i, X3 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 0.20/0.50          | ~ (v1_tops_1 @ X2 @ X3)
% 0.20/0.50          | ((k2_pre_topc @ X3 @ X2) = (u1_struct_0 @ X3))
% 0.20/0.50          | ~ (l1_pre_topc @ X3))),
% 0.20/0.50      inference('cnf', [status(esa)], [d2_tops_3])).
% 0.20/0.50  thf('22', plain,
% 0.20/0.50      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.50        | ((k2_pre_topc @ sk_A @ sk_B_2) = (u1_struct_0 @ sk_A))
% 0.20/0.50        | ~ (v1_tops_1 @ sk_B_2 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.50  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('24', plain,
% 0.20/0.50      ((((k2_pre_topc @ sk_A @ sk_B_2) = (u1_struct_0 @ sk_A))
% 0.20/0.50        | ~ (v1_tops_1 @ sk_B_2 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['22', '23'])).
% 0.20/0.50  thf('25', plain,
% 0.20/0.50      ((((k2_pre_topc @ sk_A @ sk_B_2) = (u1_struct_0 @ sk_A)))
% 0.20/0.50         <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['19', '24'])).
% 0.20/0.50  thf('26', plain,
% 0.20/0.50      (((v3_pre_topc @ sk_B_2 @ sk_A)) <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.20/0.50      inference('split', [status(esa)], ['1'])).
% 0.20/0.50  thf('27', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t23_tdlat_3, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.50       ( ( v3_tdlat_3 @ A ) <=>
% 0.20/0.50         ( ![B:$i]:
% 0.20/0.50           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.50             ( ( v3_pre_topc @ B @ A ) => ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.20/0.50  thf('28', plain,
% 0.20/0.50      (![X6 : $i, X7 : $i]:
% 0.20/0.50         (~ (v3_tdlat_3 @ X6)
% 0.20/0.50          | ~ (v3_pre_topc @ X7 @ X6)
% 0.20/0.50          | (v4_pre_topc @ X7 @ X6)
% 0.20/0.50          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.20/0.50          | ~ (l1_pre_topc @ X6)
% 0.20/0.50          | ~ (v2_pre_topc @ X6))),
% 0.20/0.50      inference('cnf', [status(esa)], [t23_tdlat_3])).
% 0.20/0.50  thf('29', plain,
% 0.20/0.50      ((~ (v2_pre_topc @ sk_A)
% 0.20/0.50        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.50        | (v4_pre_topc @ sk_B_2 @ sk_A)
% 0.20/0.50        | ~ (v3_pre_topc @ sk_B_2 @ sk_A)
% 0.20/0.50        | ~ (v3_tdlat_3 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.50  thf('30', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('32', plain, ((v3_tdlat_3 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('33', plain,
% 0.20/0.50      (((v4_pre_topc @ sk_B_2 @ sk_A) | ~ (v3_pre_topc @ sk_B_2 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['29', '30', '31', '32'])).
% 0.20/0.50  thf('34', plain,
% 0.20/0.50      (((v4_pre_topc @ sk_B_2 @ sk_A)) <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['26', '33'])).
% 0.20/0.50  thf('35', plain,
% 0.20/0.50      ((((k2_pre_topc @ sk_A @ sk_B_2) = (sk_B_2))
% 0.20/0.50        | ~ (v4_pre_topc @ sk_B_2 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['5', '6'])).
% 0.20/0.50  thf('36', plain,
% 0.20/0.50      ((((k2_pre_topc @ sk_A @ sk_B_2) = (sk_B_2)))
% 0.20/0.50         <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['34', '35'])).
% 0.20/0.50  thf('37', plain,
% 0.20/0.50      ((((u1_struct_0 @ sk_A) = (sk_B_2))) <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.20/0.50      inference('sup+', [status(thm)], ['25', '36'])).
% 0.20/0.50  thf('38', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('39', plain,
% 0.20/0.50      (((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ sk_B_2)))
% 0.20/0.50         <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.20/0.50      inference('sup+', [status(thm)], ['37', '38'])).
% 0.20/0.50  thf(d7_subset_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.50       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.20/0.50  thf('40', plain,
% 0.20/0.50      (![X4 : $i, X5 : $i]:
% 0.20/0.50         (~ (v1_subset_1 @ X5 @ X4)
% 0.20/0.50          | ((X5) != (X4))
% 0.20/0.50          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X4)))),
% 0.20/0.50      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.20/0.50  thf('41', plain,
% 0.20/0.50      (![X4 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X4)) | ~ (v1_subset_1 @ X4 @ X4))),
% 0.20/0.50      inference('simplify', [status(thm)], ['40'])).
% 0.20/0.50  thf('42', plain,
% 0.20/0.50      ((~ (v1_subset_1 @ sk_B_2 @ sk_B_2)) <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['39', '41'])).
% 0.20/0.50  thf('43', plain,
% 0.20/0.50      ((((u1_struct_0 @ sk_A) = (sk_B_2))) <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.20/0.50      inference('sup+', [status(thm)], ['25', '36'])).
% 0.20/0.50  thf('44', plain, ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('45', plain,
% 0.20/0.50      (((v1_subset_1 @ sk_B_2 @ sk_B_2)) <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.20/0.50      inference('sup+', [status(thm)], ['43', '44'])).
% 0.20/0.50  thf('46', plain, (~ ((v3_pre_topc @ sk_B_2 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['42', '45'])).
% 0.20/0.50  thf('47', plain,
% 0.20/0.50      (((v4_pre_topc @ sk_B_2 @ sk_A)) | ((v3_pre_topc @ sk_B_2 @ sk_A))),
% 0.20/0.50      inference('split', [status(esa)], ['1'])).
% 0.20/0.50  thf('48', plain, (((v4_pre_topc @ sk_B_2 @ sk_A))),
% 0.20/0.50      inference('sat_resolution*', [status(thm)], ['46', '47'])).
% 0.20/0.50  thf('49', plain, (((k2_pre_topc @ sk_A @ sk_B_2) = (sk_B_2))),
% 0.20/0.50      inference('simpl_trail', [status(thm)], ['8', '48'])).
% 0.20/0.50  thf('50', plain,
% 0.20/0.50      (((v4_pre_topc @ sk_B_2 @ sk_A)) <= (((v4_pre_topc @ sk_B_2 @ sk_A)))),
% 0.20/0.50      inference('split', [status(esa)], ['1'])).
% 0.20/0.50  thf('51', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t24_tdlat_3, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.50       ( ( v3_tdlat_3 @ A ) <=>
% 0.20/0.50         ( ![B:$i]:
% 0.20/0.50           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.50             ( ( v4_pre_topc @ B @ A ) => ( v3_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.20/0.50  thf('52', plain,
% 0.20/0.50      (![X8 : $i, X9 : $i]:
% 0.20/0.50         (~ (v3_tdlat_3 @ X8)
% 0.20/0.50          | ~ (v4_pre_topc @ X9 @ X8)
% 0.20/0.50          | (v3_pre_topc @ X9 @ X8)
% 0.20/0.50          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.20/0.50          | ~ (l1_pre_topc @ X8)
% 0.20/0.50          | ~ (v2_pre_topc @ X8))),
% 0.20/0.50      inference('cnf', [status(esa)], [t24_tdlat_3])).
% 0.20/0.50  thf('53', plain,
% 0.20/0.50      ((~ (v2_pre_topc @ sk_A)
% 0.20/0.50        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.50        | (v3_pre_topc @ sk_B_2 @ sk_A)
% 0.20/0.50        | ~ (v4_pre_topc @ sk_B_2 @ sk_A)
% 0.20/0.50        | ~ (v3_tdlat_3 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['51', '52'])).
% 0.20/0.50  thf('54', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('56', plain, ((v3_tdlat_3 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('57', plain,
% 0.20/0.50      (((v3_pre_topc @ sk_B_2 @ sk_A) | ~ (v4_pre_topc @ sk_B_2 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['53', '54', '55', '56'])).
% 0.20/0.50  thf('58', plain,
% 0.20/0.50      (((v3_pre_topc @ sk_B_2 @ sk_A)) <= (((v4_pre_topc @ sk_B_2 @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['50', '57'])).
% 0.20/0.50  thf('59', plain,
% 0.20/0.50      (((v1_tops_1 @ sk_B_2 @ sk_A) | ~ (v3_pre_topc @ sk_B_2 @ sk_A))),
% 0.20/0.50      inference('clc', [status(thm)], ['16', '17'])).
% 0.20/0.50  thf('60', plain,
% 0.20/0.50      (((v1_tops_1 @ sk_B_2 @ sk_A)) <= (((v4_pre_topc @ sk_B_2 @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['58', '59'])).
% 0.20/0.50  thf('61', plain,
% 0.20/0.50      ((((k2_pre_topc @ sk_A @ sk_B_2) = (u1_struct_0 @ sk_A))
% 0.20/0.50        | ~ (v1_tops_1 @ sk_B_2 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['22', '23'])).
% 0.20/0.50  thf('62', plain,
% 0.20/0.50      ((((k2_pre_topc @ sk_A @ sk_B_2) = (u1_struct_0 @ sk_A)))
% 0.20/0.50         <= (((v4_pre_topc @ sk_B_2 @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['60', '61'])).
% 0.20/0.50  thf('63', plain, (((v4_pre_topc @ sk_B_2 @ sk_A))),
% 0.20/0.50      inference('sat_resolution*', [status(thm)], ['46', '47'])).
% 0.20/0.50  thf('64', plain, (((k2_pre_topc @ sk_A @ sk_B_2) = (u1_struct_0 @ sk_A))),
% 0.20/0.50      inference('simpl_trail', [status(thm)], ['62', '63'])).
% 0.20/0.50  thf('65', plain, (((sk_B_2) = (u1_struct_0 @ sk_A))),
% 0.20/0.50      inference('sup+', [status(thm)], ['49', '64'])).
% 0.20/0.50  thf('66', plain, ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ sk_B_2))),
% 0.20/0.50      inference('demod', [status(thm)], ['0', '65'])).
% 0.20/0.50  thf('67', plain,
% 0.20/0.50      (![X4 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X4)) | ~ (v1_subset_1 @ X4 @ X4))),
% 0.20/0.50      inference('simplify', [status(thm)], ['40'])).
% 0.20/0.50  thf('68', plain, (~ (v1_subset_1 @ sk_B_2 @ sk_B_2)),
% 0.20/0.50      inference('sup-', [status(thm)], ['66', '67'])).
% 0.20/0.50  thf('69', plain, ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('70', plain, (((sk_B_2) = (u1_struct_0 @ sk_A))),
% 0.20/0.50      inference('sup+', [status(thm)], ['49', '64'])).
% 0.20/0.50  thf('71', plain, ((v1_subset_1 @ sk_B_2 @ sk_B_2)),
% 0.20/0.50      inference('demod', [status(thm)], ['69', '70'])).
% 0.20/0.50  thf('72', plain, ($false), inference('demod', [status(thm)], ['68', '71'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
