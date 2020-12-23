%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.eW6cUtjjqa

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:35 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  114 (1761 expanded)
%              Number of leaves         :   26 ( 495 expanded)
%              Depth                    :   19
%              Number of atoms          :  707 (26228 expanded)
%              Number of equality atoms :   31 ( 322 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

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

thf('0',plain,
    ( ( v3_pre_topc @ sk_B_2 @ sk_A )
    | ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( v4_pre_topc @ sk_B_2 @ sk_A )
   <= ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
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

thf('3',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( v4_pre_topc @ X3 @ X4 )
      | ( ( k2_pre_topc @ X4 @ X3 )
        = X3 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('4',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = sk_B_2 )
    | ~ ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = sk_B_2 )
    | ~ ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = sk_B_2 )
   <= ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('8',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('9',plain,
    ( ( v3_pre_topc @ sk_B_2 @ sk_A )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

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
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( v1_tops_1 @ X11 @ X12 )
      | ~ ( v3_tex_2 @ X11 @ X12 )
      | ~ ( v3_pre_topc @ X11 @ X12 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
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
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( v1_tops_1 @ X5 @ X6 )
      | ( ( k2_pre_topc @ X6 @ X5 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_pre_topc @ X6 ) ) ),
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
    inference(split,[status(esa)],['0'])).

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
    ! [X7: $i,X8: $i] :
      ( ~ ( v3_tdlat_3 @ X7 )
      | ~ ( v3_pre_topc @ X8 @ X7 )
      | ( v4_pre_topc @ X8 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 ) ) ),
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
    inference(demod,[status(thm)],['4','5'])).

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

thf('38',plain,
    ( ( ( ( k2_struct_0 @ sk_A )
        = sk_B_2 )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup+',[status(thm)],['8','37'])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('40',plain,(
    ! [X1: $i] :
      ( ( l1_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('41',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = sk_B_2 )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(fc12_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ~ ( v1_subset_1 @ ( k2_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) )).

thf('44',plain,(
    ! [X2: $i] :
      ( ~ ( v1_subset_1 @ ( k2_struct_0 @ X2 ) @ ( u1_struct_0 @ X2 ) )
      | ~ ( l1_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc12_struct_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v1_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,
    ( ( ~ ( v1_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B_2 )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['42','46'])).

thf('48',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = sk_B_2 )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['38','41'])).

thf('49',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['39','40'])).

thf('50',plain,
    ( ~ ( v1_subset_1 @ sk_B_2 @ sk_B_2 )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_2 )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup+',[status(thm)],['25','36'])).

thf('52',plain,(
    v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( v1_subset_1 @ sk_B_2 @ sk_B_2 )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ~ ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['50','53'])).

thf('55',plain,
    ( ( v4_pre_topc @ sk_B_2 @ sk_A )
    | ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('56',plain,(
    v4_pre_topc @ sk_B_2 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_2 )
    = sk_B_2 ),
    inference(simpl_trail,[status(thm)],['7','56'])).

thf('58',plain,
    ( ( v4_pre_topc @ sk_B_2 @ sk_A )
   <= ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('59',plain,(
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

thf('60',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v3_tdlat_3 @ X9 )
      | ~ ( v4_pre_topc @ X10 @ X9 )
      | ( v3_pre_topc @ X10 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[t24_tdlat_3])).

thf('61',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ sk_B_2 @ sk_A )
    | ~ ( v4_pre_topc @ sk_B_2 @ sk_A )
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
    ( ( v3_pre_topc @ sk_B_2 @ sk_A )
    | ~ ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['61','62','63','64'])).

thf('66',plain,
    ( ( v3_pre_topc @ sk_B_2 @ sk_A )
   <= ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['58','65'])).

thf('67',plain,
    ( ( v1_tops_1 @ sk_B_2 @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('68',plain,
    ( ( v1_tops_1 @ sk_B_2 @ sk_A )
   <= ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('70',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = ( u1_struct_0 @ sk_A ) )
   <= ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v4_pre_topc @ sk_B_2 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['54','55'])).

thf('72',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_2 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['70','71'])).

thf('73',plain,
    ( sk_B_2
    = ( u1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['57','72'])).

thf('74',plain,(
    ! [X2: $i] :
      ( ~ ( v1_subset_1 @ ( k2_struct_0 @ X2 ) @ ( u1_struct_0 @ X2 ) )
      | ~ ( l1_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc12_struct_0])).

thf('75',plain,
    ( ~ ( v1_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B_2 )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['39','40'])).

thf('77',plain,(
    ~ ( v1_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('79',plain,
    ( sk_B_2
    = ( u1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['57','72'])).

thf('80',plain,
    ( ( sk_B_2
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['39','40'])).

thf('82',plain,
    ( sk_B_2
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( sk_B_2
    = ( u1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['57','72'])).

thf('85',plain,(
    v1_subset_1 @ sk_B_2 @ sk_B_2 ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,(
    $false ),
    inference(demod,[status(thm)],['77','82','85'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.eW6cUtjjqa
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:43:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.55  % Solved by: fo/fo7.sh
% 0.21/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.55  % done 118 iterations in 0.063s
% 0.21/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.55  % SZS output start Refutation
% 0.21/0.55  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.55  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.21/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.55  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.55  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.55  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.21/0.55  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.21/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.55  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.21/0.55  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.21/0.55  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.21/0.55  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.55  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.21/0.55  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.21/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.55  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.21/0.55  thf(t61_tex_2, conjecture,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.21/0.55         ( l1_pre_topc @ A ) ) =>
% 0.21/0.55       ( ![B:$i]:
% 0.21/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.55           ( ~( ( ( v3_pre_topc @ B @ A ) | ( v4_pre_topc @ B @ A ) ) & 
% 0.21/0.55                ( v3_tex_2 @ B @ A ) & 
% 0.21/0.55                ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.21/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.55    (~( ![A:$i]:
% 0.21/0.55        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.55            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.55          ( ![B:$i]:
% 0.21/0.55            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.55              ( ~( ( ( v3_pre_topc @ B @ A ) | ( v4_pre_topc @ B @ A ) ) & 
% 0.21/0.55                   ( v3_tex_2 @ B @ A ) & 
% 0.21/0.55                   ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )),
% 0.21/0.55    inference('cnf.neg', [status(esa)], [t61_tex_2])).
% 0.21/0.55  thf('0', plain,
% 0.21/0.55      (((v3_pre_topc @ sk_B_2 @ sk_A) | (v4_pre_topc @ sk_B_2 @ sk_A))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('1', plain,
% 0.21/0.55      (((v4_pre_topc @ sk_B_2 @ sk_A)) <= (((v4_pre_topc @ sk_B_2 @ sk_A)))),
% 0.21/0.55      inference('split', [status(esa)], ['0'])).
% 0.21/0.55  thf('2', plain,
% 0.21/0.55      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(t52_pre_topc, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( l1_pre_topc @ A ) =>
% 0.21/0.55       ( ![B:$i]:
% 0.21/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.55           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.21/0.55             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.21/0.55               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.21/0.55  thf('3', plain,
% 0.21/0.55      (![X3 : $i, X4 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.21/0.55          | ~ (v4_pre_topc @ X3 @ X4)
% 0.21/0.55          | ((k2_pre_topc @ X4 @ X3) = (X3))
% 0.21/0.55          | ~ (l1_pre_topc @ X4))),
% 0.21/0.55      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.21/0.55  thf('4', plain,
% 0.21/0.55      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.55        | ((k2_pre_topc @ sk_A @ sk_B_2) = (sk_B_2))
% 0.21/0.55        | ~ (v4_pre_topc @ sk_B_2 @ sk_A))),
% 0.21/0.55      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.55  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('6', plain,
% 0.21/0.55      ((((k2_pre_topc @ sk_A @ sk_B_2) = (sk_B_2))
% 0.21/0.55        | ~ (v4_pre_topc @ sk_B_2 @ sk_A))),
% 0.21/0.55      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.55  thf('7', plain,
% 0.21/0.55      ((((k2_pre_topc @ sk_A @ sk_B_2) = (sk_B_2)))
% 0.21/0.55         <= (((v4_pre_topc @ sk_B_2 @ sk_A)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['1', '6'])).
% 0.21/0.55  thf(d3_struct_0, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.21/0.55  thf('8', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (((k2_struct_0 @ X0) = (u1_struct_0 @ X0)) | ~ (l1_struct_0 @ X0))),
% 0.21/0.55      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.55  thf('9', plain,
% 0.21/0.55      (((v3_pre_topc @ sk_B_2 @ sk_A)) <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.21/0.55      inference('split', [status(esa)], ['0'])).
% 0.21/0.55  thf('10', plain,
% 0.21/0.55      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(t47_tex_2, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.55       ( ![B:$i]:
% 0.21/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.55           ( ( ( v3_pre_topc @ B @ A ) & ( v3_tex_2 @ B @ A ) ) =>
% 0.21/0.55             ( v1_tops_1 @ B @ A ) ) ) ) ))).
% 0.21/0.55  thf('11', plain,
% 0.21/0.55      (![X11 : $i, X12 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.21/0.55          | (v1_tops_1 @ X11 @ X12)
% 0.21/0.55          | ~ (v3_tex_2 @ X11 @ X12)
% 0.21/0.55          | ~ (v3_pre_topc @ X11 @ X12)
% 0.21/0.55          | ~ (l1_pre_topc @ X12)
% 0.21/0.55          | ~ (v2_pre_topc @ X12)
% 0.21/0.55          | (v2_struct_0 @ X12))),
% 0.21/0.55      inference('cnf', [status(esa)], [t47_tex_2])).
% 0.21/0.55  thf('12', plain,
% 0.21/0.55      (((v2_struct_0 @ sk_A)
% 0.21/0.55        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.55        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.55        | ~ (v3_pre_topc @ sk_B_2 @ sk_A)
% 0.21/0.55        | ~ (v3_tex_2 @ sk_B_2 @ sk_A)
% 0.21/0.55        | (v1_tops_1 @ sk_B_2 @ sk_A))),
% 0.21/0.55      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.55  thf('13', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('15', plain, ((v3_tex_2 @ sk_B_2 @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('16', plain,
% 0.21/0.55      (((v2_struct_0 @ sk_A)
% 0.21/0.55        | ~ (v3_pre_topc @ sk_B_2 @ sk_A)
% 0.21/0.55        | (v1_tops_1 @ sk_B_2 @ sk_A))),
% 0.21/0.55      inference('demod', [status(thm)], ['12', '13', '14', '15'])).
% 0.21/0.55  thf('17', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('18', plain,
% 0.21/0.55      (((v1_tops_1 @ sk_B_2 @ sk_A) | ~ (v3_pre_topc @ sk_B_2 @ sk_A))),
% 0.21/0.55      inference('clc', [status(thm)], ['16', '17'])).
% 0.21/0.55  thf('19', plain,
% 0.21/0.55      (((v1_tops_1 @ sk_B_2 @ sk_A)) <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['9', '18'])).
% 0.21/0.55  thf('20', plain,
% 0.21/0.55      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(d2_tops_3, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( l1_pre_topc @ A ) =>
% 0.21/0.55       ( ![B:$i]:
% 0.21/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.55           ( ( v1_tops_1 @ B @ A ) <=>
% 0.21/0.55             ( ( k2_pre_topc @ A @ B ) = ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.21/0.55  thf('21', plain,
% 0.21/0.55      (![X5 : $i, X6 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.21/0.55          | ~ (v1_tops_1 @ X5 @ X6)
% 0.21/0.55          | ((k2_pre_topc @ X6 @ X5) = (u1_struct_0 @ X6))
% 0.21/0.55          | ~ (l1_pre_topc @ X6))),
% 0.21/0.55      inference('cnf', [status(esa)], [d2_tops_3])).
% 0.21/0.55  thf('22', plain,
% 0.21/0.55      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.55        | ((k2_pre_topc @ sk_A @ sk_B_2) = (u1_struct_0 @ sk_A))
% 0.21/0.55        | ~ (v1_tops_1 @ sk_B_2 @ sk_A))),
% 0.21/0.55      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.55  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('24', plain,
% 0.21/0.55      ((((k2_pre_topc @ sk_A @ sk_B_2) = (u1_struct_0 @ sk_A))
% 0.21/0.55        | ~ (v1_tops_1 @ sk_B_2 @ sk_A))),
% 0.21/0.55      inference('demod', [status(thm)], ['22', '23'])).
% 0.21/0.55  thf('25', plain,
% 0.21/0.55      ((((k2_pre_topc @ sk_A @ sk_B_2) = (u1_struct_0 @ sk_A)))
% 0.21/0.55         <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['19', '24'])).
% 0.21/0.55  thf('26', plain,
% 0.21/0.55      (((v3_pre_topc @ sk_B_2 @ sk_A)) <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.21/0.55      inference('split', [status(esa)], ['0'])).
% 0.21/0.55  thf('27', plain,
% 0.21/0.55      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(t23_tdlat_3, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.55       ( ( v3_tdlat_3 @ A ) <=>
% 0.21/0.55         ( ![B:$i]:
% 0.21/0.55           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.55             ( ( v3_pre_topc @ B @ A ) => ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.21/0.55  thf('28', plain,
% 0.21/0.55      (![X7 : $i, X8 : $i]:
% 0.21/0.55         (~ (v3_tdlat_3 @ X7)
% 0.21/0.55          | ~ (v3_pre_topc @ X8 @ X7)
% 0.21/0.55          | (v4_pre_topc @ X8 @ X7)
% 0.21/0.55          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.21/0.55          | ~ (l1_pre_topc @ X7)
% 0.21/0.55          | ~ (v2_pre_topc @ X7))),
% 0.21/0.55      inference('cnf', [status(esa)], [t23_tdlat_3])).
% 0.21/0.55  thf('29', plain,
% 0.21/0.55      ((~ (v2_pre_topc @ sk_A)
% 0.21/0.55        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.55        | (v4_pre_topc @ sk_B_2 @ sk_A)
% 0.21/0.55        | ~ (v3_pre_topc @ sk_B_2 @ sk_A)
% 0.21/0.55        | ~ (v3_tdlat_3 @ sk_A))),
% 0.21/0.55      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.55  thf('30', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('32', plain, ((v3_tdlat_3 @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('33', plain,
% 0.21/0.55      (((v4_pre_topc @ sk_B_2 @ sk_A) | ~ (v3_pre_topc @ sk_B_2 @ sk_A))),
% 0.21/0.55      inference('demod', [status(thm)], ['29', '30', '31', '32'])).
% 0.21/0.55  thf('34', plain,
% 0.21/0.55      (((v4_pre_topc @ sk_B_2 @ sk_A)) <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['26', '33'])).
% 0.21/0.55  thf('35', plain,
% 0.21/0.55      ((((k2_pre_topc @ sk_A @ sk_B_2) = (sk_B_2))
% 0.21/0.55        | ~ (v4_pre_topc @ sk_B_2 @ sk_A))),
% 0.21/0.55      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.55  thf('36', plain,
% 0.21/0.55      ((((k2_pre_topc @ sk_A @ sk_B_2) = (sk_B_2)))
% 0.21/0.55         <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['34', '35'])).
% 0.21/0.55  thf('37', plain,
% 0.21/0.55      ((((u1_struct_0 @ sk_A) = (sk_B_2))) <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.21/0.55      inference('sup+', [status(thm)], ['25', '36'])).
% 0.21/0.55  thf('38', plain,
% 0.21/0.55      (((((k2_struct_0 @ sk_A) = (sk_B_2)) | ~ (l1_struct_0 @ sk_A)))
% 0.21/0.55         <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.21/0.55      inference('sup+', [status(thm)], ['8', '37'])).
% 0.21/0.55  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(dt_l1_pre_topc, axiom,
% 0.21/0.55    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.55  thf('40', plain, (![X1 : $i]: ((l1_struct_0 @ X1) | ~ (l1_pre_topc @ X1))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.55  thf('41', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.55      inference('sup-', [status(thm)], ['39', '40'])).
% 0.21/0.55  thf('42', plain,
% 0.21/0.55      ((((k2_struct_0 @ sk_A) = (sk_B_2))) <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.21/0.55      inference('demod', [status(thm)], ['38', '41'])).
% 0.21/0.55  thf('43', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (((k2_struct_0 @ X0) = (u1_struct_0 @ X0)) | ~ (l1_struct_0 @ X0))),
% 0.21/0.55      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.55  thf(fc12_struct_0, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( l1_struct_0 @ A ) =>
% 0.21/0.55       ( ~( v1_subset_1 @ ( k2_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.55  thf('44', plain,
% 0.21/0.55      (![X2 : $i]:
% 0.21/0.55         (~ (v1_subset_1 @ (k2_struct_0 @ X2) @ (u1_struct_0 @ X2))
% 0.21/0.55          | ~ (l1_struct_0 @ X2))),
% 0.21/0.55      inference('cnf', [status(esa)], [fc12_struct_0])).
% 0.21/0.55  thf('45', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (v1_subset_1 @ (k2_struct_0 @ X0) @ (k2_struct_0 @ X0))
% 0.21/0.55          | ~ (l1_struct_0 @ X0)
% 0.21/0.55          | ~ (l1_struct_0 @ X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['43', '44'])).
% 0.21/0.55  thf('46', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (l1_struct_0 @ X0)
% 0.21/0.55          | ~ (v1_subset_1 @ (k2_struct_0 @ X0) @ (k2_struct_0 @ X0)))),
% 0.21/0.55      inference('simplify', [status(thm)], ['45'])).
% 0.21/0.55  thf('47', plain,
% 0.21/0.55      (((~ (v1_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B_2)
% 0.21/0.55         | ~ (l1_struct_0 @ sk_A))) <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['42', '46'])).
% 0.21/0.55  thf('48', plain,
% 0.21/0.55      ((((k2_struct_0 @ sk_A) = (sk_B_2))) <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.21/0.55      inference('demod', [status(thm)], ['38', '41'])).
% 0.21/0.55  thf('49', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.55      inference('sup-', [status(thm)], ['39', '40'])).
% 0.21/0.55  thf('50', plain,
% 0.21/0.55      ((~ (v1_subset_1 @ sk_B_2 @ sk_B_2)) <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.21/0.55      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.21/0.55  thf('51', plain,
% 0.21/0.55      ((((u1_struct_0 @ sk_A) = (sk_B_2))) <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.21/0.55      inference('sup+', [status(thm)], ['25', '36'])).
% 0.21/0.55  thf('52', plain, ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('53', plain,
% 0.21/0.55      (((v1_subset_1 @ sk_B_2 @ sk_B_2)) <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.21/0.55      inference('sup+', [status(thm)], ['51', '52'])).
% 0.21/0.55  thf('54', plain, (~ ((v3_pre_topc @ sk_B_2 @ sk_A))),
% 0.21/0.55      inference('demod', [status(thm)], ['50', '53'])).
% 0.21/0.55  thf('55', plain,
% 0.21/0.55      (((v4_pre_topc @ sk_B_2 @ sk_A)) | ((v3_pre_topc @ sk_B_2 @ sk_A))),
% 0.21/0.55      inference('split', [status(esa)], ['0'])).
% 0.21/0.55  thf('56', plain, (((v4_pre_topc @ sk_B_2 @ sk_A))),
% 0.21/0.55      inference('sat_resolution*', [status(thm)], ['54', '55'])).
% 0.21/0.55  thf('57', plain, (((k2_pre_topc @ sk_A @ sk_B_2) = (sk_B_2))),
% 0.21/0.55      inference('simpl_trail', [status(thm)], ['7', '56'])).
% 0.21/0.55  thf('58', plain,
% 0.21/0.55      (((v4_pre_topc @ sk_B_2 @ sk_A)) <= (((v4_pre_topc @ sk_B_2 @ sk_A)))),
% 0.21/0.55      inference('split', [status(esa)], ['0'])).
% 0.21/0.55  thf('59', plain,
% 0.21/0.55      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(t24_tdlat_3, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.55       ( ( v3_tdlat_3 @ A ) <=>
% 0.21/0.55         ( ![B:$i]:
% 0.21/0.55           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.55             ( ( v4_pre_topc @ B @ A ) => ( v3_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.21/0.55  thf('60', plain,
% 0.21/0.55      (![X9 : $i, X10 : $i]:
% 0.21/0.55         (~ (v3_tdlat_3 @ X9)
% 0.21/0.55          | ~ (v4_pre_topc @ X10 @ X9)
% 0.21/0.55          | (v3_pre_topc @ X10 @ X9)
% 0.21/0.55          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.21/0.55          | ~ (l1_pre_topc @ X9)
% 0.21/0.55          | ~ (v2_pre_topc @ X9))),
% 0.21/0.55      inference('cnf', [status(esa)], [t24_tdlat_3])).
% 0.21/0.55  thf('61', plain,
% 0.21/0.55      ((~ (v2_pre_topc @ sk_A)
% 0.21/0.55        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.55        | (v3_pre_topc @ sk_B_2 @ sk_A)
% 0.21/0.55        | ~ (v4_pre_topc @ sk_B_2 @ sk_A)
% 0.21/0.55        | ~ (v3_tdlat_3 @ sk_A))),
% 0.21/0.55      inference('sup-', [status(thm)], ['59', '60'])).
% 0.21/0.55  thf('62', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('63', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('64', plain, ((v3_tdlat_3 @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('65', plain,
% 0.21/0.55      (((v3_pre_topc @ sk_B_2 @ sk_A) | ~ (v4_pre_topc @ sk_B_2 @ sk_A))),
% 0.21/0.55      inference('demod', [status(thm)], ['61', '62', '63', '64'])).
% 0.21/0.55  thf('66', plain,
% 0.21/0.55      (((v3_pre_topc @ sk_B_2 @ sk_A)) <= (((v4_pre_topc @ sk_B_2 @ sk_A)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['58', '65'])).
% 0.21/0.55  thf('67', plain,
% 0.21/0.55      (((v1_tops_1 @ sk_B_2 @ sk_A) | ~ (v3_pre_topc @ sk_B_2 @ sk_A))),
% 0.21/0.55      inference('clc', [status(thm)], ['16', '17'])).
% 0.21/0.55  thf('68', plain,
% 0.21/0.55      (((v1_tops_1 @ sk_B_2 @ sk_A)) <= (((v4_pre_topc @ sk_B_2 @ sk_A)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['66', '67'])).
% 0.21/0.55  thf('69', plain,
% 0.21/0.55      ((((k2_pre_topc @ sk_A @ sk_B_2) = (u1_struct_0 @ sk_A))
% 0.21/0.55        | ~ (v1_tops_1 @ sk_B_2 @ sk_A))),
% 0.21/0.55      inference('demod', [status(thm)], ['22', '23'])).
% 0.21/0.55  thf('70', plain,
% 0.21/0.55      ((((k2_pre_topc @ sk_A @ sk_B_2) = (u1_struct_0 @ sk_A)))
% 0.21/0.55         <= (((v4_pre_topc @ sk_B_2 @ sk_A)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['68', '69'])).
% 0.21/0.55  thf('71', plain, (((v4_pre_topc @ sk_B_2 @ sk_A))),
% 0.21/0.55      inference('sat_resolution*', [status(thm)], ['54', '55'])).
% 0.21/0.55  thf('72', plain, (((k2_pre_topc @ sk_A @ sk_B_2) = (u1_struct_0 @ sk_A))),
% 0.21/0.55      inference('simpl_trail', [status(thm)], ['70', '71'])).
% 0.21/0.55  thf('73', plain, (((sk_B_2) = (u1_struct_0 @ sk_A))),
% 0.21/0.55      inference('sup+', [status(thm)], ['57', '72'])).
% 0.21/0.55  thf('74', plain,
% 0.21/0.55      (![X2 : $i]:
% 0.21/0.55         (~ (v1_subset_1 @ (k2_struct_0 @ X2) @ (u1_struct_0 @ X2))
% 0.21/0.55          | ~ (l1_struct_0 @ X2))),
% 0.21/0.55      inference('cnf', [status(esa)], [fc12_struct_0])).
% 0.21/0.55  thf('75', plain,
% 0.21/0.55      ((~ (v1_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B_2)
% 0.21/0.55        | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.55      inference('sup-', [status(thm)], ['73', '74'])).
% 0.21/0.55  thf('76', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.55      inference('sup-', [status(thm)], ['39', '40'])).
% 0.21/0.55  thf('77', plain, (~ (v1_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B_2)),
% 0.21/0.55      inference('demod', [status(thm)], ['75', '76'])).
% 0.21/0.55  thf('78', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (((k2_struct_0 @ X0) = (u1_struct_0 @ X0)) | ~ (l1_struct_0 @ X0))),
% 0.21/0.55      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.55  thf('79', plain, (((sk_B_2) = (u1_struct_0 @ sk_A))),
% 0.21/0.55      inference('sup+', [status(thm)], ['57', '72'])).
% 0.21/0.55  thf('80', plain,
% 0.21/0.55      ((((sk_B_2) = (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.55      inference('sup+', [status(thm)], ['78', '79'])).
% 0.21/0.55  thf('81', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.55      inference('sup-', [status(thm)], ['39', '40'])).
% 0.21/0.55  thf('82', plain, (((sk_B_2) = (k2_struct_0 @ sk_A))),
% 0.21/0.55      inference('demod', [status(thm)], ['80', '81'])).
% 0.21/0.55  thf('83', plain, ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('84', plain, (((sk_B_2) = (u1_struct_0 @ sk_A))),
% 0.21/0.55      inference('sup+', [status(thm)], ['57', '72'])).
% 0.21/0.55  thf('85', plain, ((v1_subset_1 @ sk_B_2 @ sk_B_2)),
% 0.21/0.55      inference('demod', [status(thm)], ['83', '84'])).
% 0.21/0.55  thf('86', plain, ($false),
% 0.21/0.55      inference('demod', [status(thm)], ['77', '82', '85'])).
% 0.21/0.55  
% 0.21/0.55  % SZS output end Refutation
% 0.21/0.55  
% 0.21/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
