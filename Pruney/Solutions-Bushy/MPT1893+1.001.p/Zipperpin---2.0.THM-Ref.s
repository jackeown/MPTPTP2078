%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1893+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Twb1lOOUxe

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:54:32 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 794 expanded)
%              Number of leaves         :   22 ( 224 expanded)
%              Depth                    :   17
%              Number of atoms          :  626 (12183 expanded)
%              Number of equality atoms :   23 ( 134 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

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
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( v4_pre_topc @ X10 @ X11 )
      | ( ( k2_pre_topc @ X11 @ X10 )
        = X10 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
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
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( v1_tops_1 @ X8 @ X9 )
      | ~ ( v3_tex_2 @ X8 @ X9 )
      | ~ ( v3_pre_topc @ X8 @ X9 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
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
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( v1_tops_1 @ X0 @ X1 )
      | ( ( k2_pre_topc @ X1 @ X0 )
        = ( u1_struct_0 @ X1 ) )
      | ~ ( l1_pre_topc @ X1 ) ) ),
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
    ! [X4: $i,X5: $i] :
      ( ~ ( v3_tdlat_3 @ X4 )
      | ~ ( v3_pre_topc @ X5 @ X4 )
      | ( v4_pre_topc @ X5 @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( v2_pre_topc @ X4 ) ) ),
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
    ! [X2: $i,X3: $i] :
      ( ~ ( v1_subset_1 @ X3 @ X2 )
      | ( X3 != X2 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('41',plain,(
    ! [X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X2 ) )
      | ~ ( v1_subset_1 @ X2 @ X2 ) ) ),
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
    ! [X6: $i,X7: $i] :
      ( ~ ( v3_tdlat_3 @ X6 )
      | ~ ( v4_pre_topc @ X7 @ X6 )
      | ( v3_pre_topc @ X7 @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( l1_pre_topc @ X6 )
      | ~ ( v2_pre_topc @ X6 ) ) ),
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
    ! [X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X2 ) )
      | ~ ( v1_subset_1 @ X2 @ X2 ) ) ),
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
