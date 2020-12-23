%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ug1lTDo2dp

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:37 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 542 expanded)
%              Number of leaves         :   26 ( 160 expanded)
%              Depth                    :   15
%              Number of atoms          :  691 (7816 expanded)
%              Number of equality atoms :   24 (  90 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

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

thf(t24_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v3_tdlat_3 @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v4_pre_topc @ B @ A )
             => ( v3_pre_topc @ B @ A ) ) ) ) ) )).

thf('3',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v3_tdlat_3 @ X10 )
      | ~ ( v4_pre_topc @ X11 @ X10 )
      | ( v3_pre_topc @ X11 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[t24_tdlat_3])).

thf('4',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ sk_B_2 @ sk_A )
    | ~ ( v4_pre_topc @ sk_B_2 @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( v3_pre_topc @ sk_B_2 @ sk_A )
    | ~ ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('9',plain,
    ( ( v3_pre_topc @ sk_B_2 @ sk_A )
   <= ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','8'])).

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
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( v1_tops_1 @ X12 @ X13 )
      | ~ ( v3_tex_2 @ X12 @ X13 )
      | ~ ( v3_pre_topc @ X12 @ X13 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
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
   <= ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['9','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( k2_struct_0 @ A ) ) ) ) ) )).

thf('21',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( v1_tops_1 @ X4 @ X5 )
      | ( ( k2_pre_topc @ X5 @ X4 )
        = ( k2_struct_0 @ X5 ) )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('22',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = ( k2_struct_0 @ sk_A ) )
   <= ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['19','24'])).

thf('26',plain,
    ( ( v4_pre_topc @ sk_B_2 @ sk_A )
   <= ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('27',plain,(
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

thf('28',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ~ ( v4_pre_topc @ X2 @ X3 )
      | ( ( k2_pre_topc @ X3 @ X2 )
        = X2 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('29',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = sk_B_2 )
    | ~ ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = sk_B_2 )
    | ~ ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = sk_B_2 )
   <= ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['26','31'])).

thf('33',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = sk_B_2 )
   <= ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup+',[status(thm)],['25','32'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('34',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('35',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('38',plain,(
    ! [X1: $i] :
      ( ( l1_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('39',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['36','39'])).

thf('41',plain,
    ( ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ sk_B_2 ) )
   <= ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup+',[status(thm)],['33','40'])).

thf('42',plain,
    ( ( v3_pre_topc @ sk_B_2 @ sk_A )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('43',plain,
    ( ( v1_tops_1 @ sk_B_2 @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('44',plain,
    ( ( v1_tops_1 @ sk_B_2 @ sk_A )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('46',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = ( k2_struct_0 @ sk_A ) )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( v3_pre_topc @ sk_B_2 @ sk_A )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('48',plain,(
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

thf('49',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v3_tdlat_3 @ X8 )
      | ~ ( v3_pre_topc @ X9 @ X8 )
      | ( v4_pre_topc @ X9 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[t23_tdlat_3])).

thf('50',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B_2 @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_2 @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( v4_pre_topc @ sk_B_2 @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['50','51','52','53'])).

thf('55',plain,
    ( ( v4_pre_topc @ sk_B_2 @ sk_A )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['47','54'])).

thf('56',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = sk_B_2 )
    | ~ ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('57',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = sk_B_2 )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = sk_B_2 )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup+',[status(thm)],['46','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['36','39'])).

thf('60',plain,
    ( ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ sk_B_2 ) )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('61',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_subset_1 @ X7 @ X6 )
      | ( X7 != X6 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('62',plain,(
    ! [X6: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( v1_subset_1 @ X6 @ X6 ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,
    ( ~ ( v1_subset_1 @ sk_B_2 @ sk_B_2 )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['60','62'])).

thf('64',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = sk_B_2 )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup+',[status(thm)],['46','57'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('66',plain,(
    v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( v1_subset_1 @ sk_B_2 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['37','38'])).

thf('69',plain,(
    v1_subset_1 @ sk_B_2 @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( v1_subset_1 @ sk_B_2 @ sk_B_2 )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup+',[status(thm)],['64','69'])).

thf('71',plain,(
    ~ ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['63','70'])).

thf('72',plain,
    ( ( v4_pre_topc @ sk_B_2 @ sk_A )
    | ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('73',plain,(
    v4_pre_topc @ sk_B_2 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['71','72'])).

thf('74',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ sk_B_2 ) ),
    inference(simpl_trail,[status(thm)],['41','73'])).

thf('75',plain,(
    ! [X6: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( v1_subset_1 @ X6 @ X6 ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('76',plain,(
    ~ ( v1_subset_1 @ sk_B_2 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = sk_B_2 )
   <= ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup+',[status(thm)],['25','32'])).

thf('78',plain,(
    v1_subset_1 @ sk_B_2 @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('79',plain,
    ( ( v1_subset_1 @ sk_B_2 @ sk_B_2 )
   <= ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,(
    v4_pre_topc @ sk_B_2 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['71','72'])).

thf('81',plain,(
    v1_subset_1 @ sk_B_2 @ sk_B_2 ),
    inference(simpl_trail,[status(thm)],['79','80'])).

thf('82',plain,(
    $false ),
    inference(demod,[status(thm)],['76','81'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ug1lTDo2dp
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:18:27 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.33  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.18/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.18/0.51  % Solved by: fo/fo7.sh
% 0.18/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.18/0.51  % done 113 iterations in 0.061s
% 0.18/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.18/0.51  % SZS output start Refutation
% 0.18/0.51  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.18/0.51  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.18/0.51  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.18/0.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.18/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.18/0.51  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.18/0.51  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.18/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.18/0.51  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.18/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.18/0.51  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.18/0.51  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.18/0.51  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.18/0.51  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.18/0.51  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.18/0.51  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.18/0.51  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.18/0.51  thf(t61_tex_2, conjecture,
% 0.18/0.51    (![A:$i]:
% 0.18/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.18/0.51         ( l1_pre_topc @ A ) ) =>
% 0.18/0.51       ( ![B:$i]:
% 0.18/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.18/0.51           ( ~( ( ( v3_pre_topc @ B @ A ) | ( v4_pre_topc @ B @ A ) ) & 
% 0.18/0.51                ( v3_tex_2 @ B @ A ) & 
% 0.18/0.51                ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.18/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.18/0.51    (~( ![A:$i]:
% 0.18/0.51        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.18/0.51            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.18/0.51          ( ![B:$i]:
% 0.18/0.51            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.18/0.51              ( ~( ( ( v3_pre_topc @ B @ A ) | ( v4_pre_topc @ B @ A ) ) & 
% 0.18/0.51                   ( v3_tex_2 @ B @ A ) & 
% 0.18/0.51                   ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )),
% 0.18/0.51    inference('cnf.neg', [status(esa)], [t61_tex_2])).
% 0.18/0.51  thf('0', plain,
% 0.18/0.51      (((v3_pre_topc @ sk_B_2 @ sk_A) | (v4_pre_topc @ sk_B_2 @ sk_A))),
% 0.18/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.51  thf('1', plain,
% 0.18/0.51      (((v4_pre_topc @ sk_B_2 @ sk_A)) <= (((v4_pre_topc @ sk_B_2 @ sk_A)))),
% 0.18/0.51      inference('split', [status(esa)], ['0'])).
% 0.18/0.51  thf('2', plain,
% 0.18/0.51      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.18/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.51  thf(t24_tdlat_3, axiom,
% 0.18/0.51    (![A:$i]:
% 0.18/0.51     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.18/0.51       ( ( v3_tdlat_3 @ A ) <=>
% 0.18/0.51         ( ![B:$i]:
% 0.18/0.51           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.18/0.51             ( ( v4_pre_topc @ B @ A ) => ( v3_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.18/0.51  thf('3', plain,
% 0.18/0.51      (![X10 : $i, X11 : $i]:
% 0.18/0.51         (~ (v3_tdlat_3 @ X10)
% 0.18/0.51          | ~ (v4_pre_topc @ X11 @ X10)
% 0.18/0.51          | (v3_pre_topc @ X11 @ X10)
% 0.18/0.51          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.18/0.51          | ~ (l1_pre_topc @ X10)
% 0.18/0.51          | ~ (v2_pre_topc @ X10))),
% 0.18/0.51      inference('cnf', [status(esa)], [t24_tdlat_3])).
% 0.18/0.51  thf('4', plain,
% 0.18/0.51      ((~ (v2_pre_topc @ sk_A)
% 0.18/0.51        | ~ (l1_pre_topc @ sk_A)
% 0.18/0.51        | (v3_pre_topc @ sk_B_2 @ sk_A)
% 0.18/0.51        | ~ (v4_pre_topc @ sk_B_2 @ sk_A)
% 0.18/0.51        | ~ (v3_tdlat_3 @ sk_A))),
% 0.18/0.51      inference('sup-', [status(thm)], ['2', '3'])).
% 0.18/0.51  thf('5', plain, ((v2_pre_topc @ sk_A)),
% 0.18/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.51  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 0.18/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.51  thf('7', plain, ((v3_tdlat_3 @ sk_A)),
% 0.18/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.51  thf('8', plain,
% 0.18/0.51      (((v3_pre_topc @ sk_B_2 @ sk_A) | ~ (v4_pre_topc @ sk_B_2 @ sk_A))),
% 0.18/0.51      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 0.18/0.51  thf('9', plain,
% 0.18/0.51      (((v3_pre_topc @ sk_B_2 @ sk_A)) <= (((v4_pre_topc @ sk_B_2 @ sk_A)))),
% 0.18/0.51      inference('sup-', [status(thm)], ['1', '8'])).
% 0.18/0.51  thf('10', plain,
% 0.18/0.51      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.18/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.51  thf(t47_tex_2, axiom,
% 0.18/0.51    (![A:$i]:
% 0.18/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.18/0.51       ( ![B:$i]:
% 0.18/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.18/0.51           ( ( ( v3_pre_topc @ B @ A ) & ( v3_tex_2 @ B @ A ) ) =>
% 0.18/0.51             ( v1_tops_1 @ B @ A ) ) ) ) ))).
% 0.18/0.51  thf('11', plain,
% 0.18/0.51      (![X12 : $i, X13 : $i]:
% 0.18/0.51         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.18/0.51          | (v1_tops_1 @ X12 @ X13)
% 0.18/0.51          | ~ (v3_tex_2 @ X12 @ X13)
% 0.18/0.51          | ~ (v3_pre_topc @ X12 @ X13)
% 0.18/0.51          | ~ (l1_pre_topc @ X13)
% 0.18/0.51          | ~ (v2_pre_topc @ X13)
% 0.18/0.51          | (v2_struct_0 @ X13))),
% 0.18/0.51      inference('cnf', [status(esa)], [t47_tex_2])).
% 0.18/0.51  thf('12', plain,
% 0.18/0.51      (((v2_struct_0 @ sk_A)
% 0.18/0.51        | ~ (v2_pre_topc @ sk_A)
% 0.18/0.51        | ~ (l1_pre_topc @ sk_A)
% 0.18/0.51        | ~ (v3_pre_topc @ sk_B_2 @ sk_A)
% 0.18/0.51        | ~ (v3_tex_2 @ sk_B_2 @ sk_A)
% 0.18/0.51        | (v1_tops_1 @ sk_B_2 @ sk_A))),
% 0.18/0.51      inference('sup-', [status(thm)], ['10', '11'])).
% 0.18/0.51  thf('13', plain, ((v2_pre_topc @ sk_A)),
% 0.18/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.51  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.18/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.51  thf('15', plain, ((v3_tex_2 @ sk_B_2 @ sk_A)),
% 0.18/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.51  thf('16', plain,
% 0.18/0.51      (((v2_struct_0 @ sk_A)
% 0.18/0.51        | ~ (v3_pre_topc @ sk_B_2 @ sk_A)
% 0.18/0.51        | (v1_tops_1 @ sk_B_2 @ sk_A))),
% 0.18/0.51      inference('demod', [status(thm)], ['12', '13', '14', '15'])).
% 0.18/0.51  thf('17', plain, (~ (v2_struct_0 @ sk_A)),
% 0.18/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.51  thf('18', plain,
% 0.18/0.51      (((v1_tops_1 @ sk_B_2 @ sk_A) | ~ (v3_pre_topc @ sk_B_2 @ sk_A))),
% 0.18/0.51      inference('clc', [status(thm)], ['16', '17'])).
% 0.18/0.51  thf('19', plain,
% 0.18/0.51      (((v1_tops_1 @ sk_B_2 @ sk_A)) <= (((v4_pre_topc @ sk_B_2 @ sk_A)))),
% 0.18/0.51      inference('sup-', [status(thm)], ['9', '18'])).
% 0.18/0.51  thf('20', plain,
% 0.18/0.51      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.18/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.51  thf(d3_tops_1, axiom,
% 0.18/0.51    (![A:$i]:
% 0.18/0.51     ( ( l1_pre_topc @ A ) =>
% 0.18/0.51       ( ![B:$i]:
% 0.18/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.18/0.51           ( ( v1_tops_1 @ B @ A ) <=>
% 0.18/0.51             ( ( k2_pre_topc @ A @ B ) = ( k2_struct_0 @ A ) ) ) ) ) ))).
% 0.18/0.51  thf('21', plain,
% 0.18/0.51      (![X4 : $i, X5 : $i]:
% 0.18/0.51         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.18/0.51          | ~ (v1_tops_1 @ X4 @ X5)
% 0.18/0.51          | ((k2_pre_topc @ X5 @ X4) = (k2_struct_0 @ X5))
% 0.18/0.51          | ~ (l1_pre_topc @ X5))),
% 0.18/0.51      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.18/0.51  thf('22', plain,
% 0.18/0.51      ((~ (l1_pre_topc @ sk_A)
% 0.18/0.51        | ((k2_pre_topc @ sk_A @ sk_B_2) = (k2_struct_0 @ sk_A))
% 0.18/0.51        | ~ (v1_tops_1 @ sk_B_2 @ sk_A))),
% 0.18/0.51      inference('sup-', [status(thm)], ['20', '21'])).
% 0.18/0.51  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.18/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.51  thf('24', plain,
% 0.18/0.51      ((((k2_pre_topc @ sk_A @ sk_B_2) = (k2_struct_0 @ sk_A))
% 0.18/0.51        | ~ (v1_tops_1 @ sk_B_2 @ sk_A))),
% 0.18/0.51      inference('demod', [status(thm)], ['22', '23'])).
% 0.18/0.51  thf('25', plain,
% 0.18/0.51      ((((k2_pre_topc @ sk_A @ sk_B_2) = (k2_struct_0 @ sk_A)))
% 0.18/0.51         <= (((v4_pre_topc @ sk_B_2 @ sk_A)))),
% 0.18/0.51      inference('sup-', [status(thm)], ['19', '24'])).
% 0.18/0.51  thf('26', plain,
% 0.18/0.51      (((v4_pre_topc @ sk_B_2 @ sk_A)) <= (((v4_pre_topc @ sk_B_2 @ sk_A)))),
% 0.18/0.51      inference('split', [status(esa)], ['0'])).
% 0.18/0.51  thf('27', plain,
% 0.18/0.51      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.18/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.51  thf(t52_pre_topc, axiom,
% 0.18/0.51    (![A:$i]:
% 0.18/0.51     ( ( l1_pre_topc @ A ) =>
% 0.18/0.51       ( ![B:$i]:
% 0.18/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.18/0.51           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.18/0.51             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.18/0.51               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.18/0.51  thf('28', plain,
% 0.18/0.51      (![X2 : $i, X3 : $i]:
% 0.18/0.51         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 0.18/0.51          | ~ (v4_pre_topc @ X2 @ X3)
% 0.18/0.51          | ((k2_pre_topc @ X3 @ X2) = (X2))
% 0.18/0.51          | ~ (l1_pre_topc @ X3))),
% 0.18/0.51      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.18/0.51  thf('29', plain,
% 0.18/0.51      ((~ (l1_pre_topc @ sk_A)
% 0.18/0.51        | ((k2_pre_topc @ sk_A @ sk_B_2) = (sk_B_2))
% 0.18/0.51        | ~ (v4_pre_topc @ sk_B_2 @ sk_A))),
% 0.18/0.51      inference('sup-', [status(thm)], ['27', '28'])).
% 0.18/0.51  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.18/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.51  thf('31', plain,
% 0.18/0.51      ((((k2_pre_topc @ sk_A @ sk_B_2) = (sk_B_2))
% 0.18/0.51        | ~ (v4_pre_topc @ sk_B_2 @ sk_A))),
% 0.18/0.51      inference('demod', [status(thm)], ['29', '30'])).
% 0.18/0.51  thf('32', plain,
% 0.18/0.51      ((((k2_pre_topc @ sk_A @ sk_B_2) = (sk_B_2)))
% 0.18/0.51         <= (((v4_pre_topc @ sk_B_2 @ sk_A)))),
% 0.18/0.51      inference('sup-', [status(thm)], ['26', '31'])).
% 0.18/0.51  thf('33', plain,
% 0.18/0.51      ((((k2_struct_0 @ sk_A) = (sk_B_2))) <= (((v4_pre_topc @ sk_B_2 @ sk_A)))),
% 0.18/0.51      inference('sup+', [status(thm)], ['25', '32'])).
% 0.18/0.51  thf(d3_struct_0, axiom,
% 0.18/0.51    (![A:$i]:
% 0.18/0.51     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.18/0.51  thf('34', plain,
% 0.18/0.51      (![X0 : $i]:
% 0.18/0.51         (((k2_struct_0 @ X0) = (u1_struct_0 @ X0)) | ~ (l1_struct_0 @ X0))),
% 0.18/0.51      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.18/0.51  thf('35', plain,
% 0.18/0.51      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.18/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.51  thf('36', plain,
% 0.18/0.51      (((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.18/0.51        | ~ (l1_struct_0 @ sk_A))),
% 0.18/0.51      inference('sup+', [status(thm)], ['34', '35'])).
% 0.18/0.51  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 0.18/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.51  thf(dt_l1_pre_topc, axiom,
% 0.18/0.51    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.18/0.51  thf('38', plain, (![X1 : $i]: ((l1_struct_0 @ X1) | ~ (l1_pre_topc @ X1))),
% 0.18/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.18/0.51  thf('39', plain, ((l1_struct_0 @ sk_A)),
% 0.18/0.51      inference('sup-', [status(thm)], ['37', '38'])).
% 0.18/0.51  thf('40', plain,
% 0.18/0.51      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.18/0.51      inference('demod', [status(thm)], ['36', '39'])).
% 0.18/0.51  thf('41', plain,
% 0.18/0.51      (((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ sk_B_2)))
% 0.18/0.51         <= (((v4_pre_topc @ sk_B_2 @ sk_A)))),
% 0.18/0.51      inference('sup+', [status(thm)], ['33', '40'])).
% 0.18/0.51  thf('42', plain,
% 0.18/0.51      (((v3_pre_topc @ sk_B_2 @ sk_A)) <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.18/0.51      inference('split', [status(esa)], ['0'])).
% 0.18/0.51  thf('43', plain,
% 0.18/0.51      (((v1_tops_1 @ sk_B_2 @ sk_A) | ~ (v3_pre_topc @ sk_B_2 @ sk_A))),
% 0.18/0.51      inference('clc', [status(thm)], ['16', '17'])).
% 0.18/0.51  thf('44', plain,
% 0.18/0.51      (((v1_tops_1 @ sk_B_2 @ sk_A)) <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.18/0.51      inference('sup-', [status(thm)], ['42', '43'])).
% 0.18/0.51  thf('45', plain,
% 0.18/0.51      ((((k2_pre_topc @ sk_A @ sk_B_2) = (k2_struct_0 @ sk_A))
% 0.18/0.51        | ~ (v1_tops_1 @ sk_B_2 @ sk_A))),
% 0.18/0.51      inference('demod', [status(thm)], ['22', '23'])).
% 0.18/0.51  thf('46', plain,
% 0.18/0.51      ((((k2_pre_topc @ sk_A @ sk_B_2) = (k2_struct_0 @ sk_A)))
% 0.18/0.51         <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.18/0.51      inference('sup-', [status(thm)], ['44', '45'])).
% 0.18/0.51  thf('47', plain,
% 0.18/0.51      (((v3_pre_topc @ sk_B_2 @ sk_A)) <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.18/0.51      inference('split', [status(esa)], ['0'])).
% 0.18/0.51  thf('48', plain,
% 0.18/0.51      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.18/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.51  thf(t23_tdlat_3, axiom,
% 0.18/0.51    (![A:$i]:
% 0.18/0.51     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.18/0.51       ( ( v3_tdlat_3 @ A ) <=>
% 0.18/0.51         ( ![B:$i]:
% 0.18/0.51           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.18/0.51             ( ( v3_pre_topc @ B @ A ) => ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.18/0.51  thf('49', plain,
% 0.18/0.51      (![X8 : $i, X9 : $i]:
% 0.18/0.51         (~ (v3_tdlat_3 @ X8)
% 0.18/0.51          | ~ (v3_pre_topc @ X9 @ X8)
% 0.18/0.51          | (v4_pre_topc @ X9 @ X8)
% 0.18/0.51          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.18/0.51          | ~ (l1_pre_topc @ X8)
% 0.18/0.51          | ~ (v2_pre_topc @ X8))),
% 0.18/0.51      inference('cnf', [status(esa)], [t23_tdlat_3])).
% 0.18/0.51  thf('50', plain,
% 0.18/0.51      ((~ (v2_pre_topc @ sk_A)
% 0.18/0.51        | ~ (l1_pre_topc @ sk_A)
% 0.18/0.51        | (v4_pre_topc @ sk_B_2 @ sk_A)
% 0.18/0.51        | ~ (v3_pre_topc @ sk_B_2 @ sk_A)
% 0.18/0.51        | ~ (v3_tdlat_3 @ sk_A))),
% 0.18/0.51      inference('sup-', [status(thm)], ['48', '49'])).
% 0.18/0.51  thf('51', plain, ((v2_pre_topc @ sk_A)),
% 0.18/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.51  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 0.18/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.51  thf('53', plain, ((v3_tdlat_3 @ sk_A)),
% 0.18/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.51  thf('54', plain,
% 0.18/0.51      (((v4_pre_topc @ sk_B_2 @ sk_A) | ~ (v3_pre_topc @ sk_B_2 @ sk_A))),
% 0.18/0.51      inference('demod', [status(thm)], ['50', '51', '52', '53'])).
% 0.18/0.51  thf('55', plain,
% 0.18/0.51      (((v4_pre_topc @ sk_B_2 @ sk_A)) <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.18/0.51      inference('sup-', [status(thm)], ['47', '54'])).
% 0.18/0.51  thf('56', plain,
% 0.18/0.51      ((((k2_pre_topc @ sk_A @ sk_B_2) = (sk_B_2))
% 0.18/0.51        | ~ (v4_pre_topc @ sk_B_2 @ sk_A))),
% 0.18/0.51      inference('demod', [status(thm)], ['29', '30'])).
% 0.18/0.51  thf('57', plain,
% 0.18/0.51      ((((k2_pre_topc @ sk_A @ sk_B_2) = (sk_B_2)))
% 0.18/0.51         <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.18/0.51      inference('sup-', [status(thm)], ['55', '56'])).
% 0.18/0.51  thf('58', plain,
% 0.18/0.51      ((((k2_struct_0 @ sk_A) = (sk_B_2))) <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.18/0.51      inference('sup+', [status(thm)], ['46', '57'])).
% 0.18/0.51  thf('59', plain,
% 0.18/0.51      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.18/0.51      inference('demod', [status(thm)], ['36', '39'])).
% 0.18/0.51  thf('60', plain,
% 0.18/0.51      (((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ sk_B_2)))
% 0.18/0.51         <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.18/0.51      inference('sup+', [status(thm)], ['58', '59'])).
% 0.18/0.51  thf(d7_subset_1, axiom,
% 0.18/0.51    (![A:$i,B:$i]:
% 0.18/0.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.18/0.51       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.18/0.51  thf('61', plain,
% 0.18/0.51      (![X6 : $i, X7 : $i]:
% 0.18/0.51         (~ (v1_subset_1 @ X7 @ X6)
% 0.18/0.51          | ((X7) != (X6))
% 0.18/0.51          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6)))),
% 0.18/0.51      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.18/0.51  thf('62', plain,
% 0.18/0.51      (![X6 : $i]:
% 0.18/0.51         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X6)) | ~ (v1_subset_1 @ X6 @ X6))),
% 0.18/0.51      inference('simplify', [status(thm)], ['61'])).
% 0.18/0.51  thf('63', plain,
% 0.18/0.51      ((~ (v1_subset_1 @ sk_B_2 @ sk_B_2)) <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.18/0.51      inference('sup-', [status(thm)], ['60', '62'])).
% 0.18/0.51  thf('64', plain,
% 0.18/0.51      ((((k2_struct_0 @ sk_A) = (sk_B_2))) <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.18/0.51      inference('sup+', [status(thm)], ['46', '57'])).
% 0.18/0.51  thf('65', plain,
% 0.18/0.51      (![X0 : $i]:
% 0.18/0.51         (((k2_struct_0 @ X0) = (u1_struct_0 @ X0)) | ~ (l1_struct_0 @ X0))),
% 0.18/0.51      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.18/0.51  thf('66', plain, ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.18/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.51  thf('67', plain,
% 0.18/0.51      (((v1_subset_1 @ sk_B_2 @ (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.18/0.51      inference('sup+', [status(thm)], ['65', '66'])).
% 0.18/0.51  thf('68', plain, ((l1_struct_0 @ sk_A)),
% 0.18/0.51      inference('sup-', [status(thm)], ['37', '38'])).
% 0.18/0.51  thf('69', plain, ((v1_subset_1 @ sk_B_2 @ (k2_struct_0 @ sk_A))),
% 0.18/0.51      inference('demod', [status(thm)], ['67', '68'])).
% 0.18/0.51  thf('70', plain,
% 0.18/0.51      (((v1_subset_1 @ sk_B_2 @ sk_B_2)) <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.18/0.51      inference('sup+', [status(thm)], ['64', '69'])).
% 0.18/0.51  thf('71', plain, (~ ((v3_pre_topc @ sk_B_2 @ sk_A))),
% 0.18/0.51      inference('demod', [status(thm)], ['63', '70'])).
% 0.18/0.51  thf('72', plain,
% 0.18/0.51      (((v4_pre_topc @ sk_B_2 @ sk_A)) | ((v3_pre_topc @ sk_B_2 @ sk_A))),
% 0.18/0.51      inference('split', [status(esa)], ['0'])).
% 0.18/0.51  thf('73', plain, (((v4_pre_topc @ sk_B_2 @ sk_A))),
% 0.18/0.51      inference('sat_resolution*', [status(thm)], ['71', '72'])).
% 0.18/0.51  thf('74', plain, ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ sk_B_2))),
% 0.18/0.51      inference('simpl_trail', [status(thm)], ['41', '73'])).
% 0.18/0.51  thf('75', plain,
% 0.18/0.51      (![X6 : $i]:
% 0.18/0.51         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X6)) | ~ (v1_subset_1 @ X6 @ X6))),
% 0.18/0.51      inference('simplify', [status(thm)], ['61'])).
% 0.18/0.51  thf('76', plain, (~ (v1_subset_1 @ sk_B_2 @ sk_B_2)),
% 0.18/0.51      inference('sup-', [status(thm)], ['74', '75'])).
% 0.18/0.51  thf('77', plain,
% 0.18/0.51      ((((k2_struct_0 @ sk_A) = (sk_B_2))) <= (((v4_pre_topc @ sk_B_2 @ sk_A)))),
% 0.18/0.51      inference('sup+', [status(thm)], ['25', '32'])).
% 0.18/0.51  thf('78', plain, ((v1_subset_1 @ sk_B_2 @ (k2_struct_0 @ sk_A))),
% 0.18/0.51      inference('demod', [status(thm)], ['67', '68'])).
% 0.18/0.51  thf('79', plain,
% 0.18/0.51      (((v1_subset_1 @ sk_B_2 @ sk_B_2)) <= (((v4_pre_topc @ sk_B_2 @ sk_A)))),
% 0.18/0.51      inference('sup+', [status(thm)], ['77', '78'])).
% 0.18/0.51  thf('80', plain, (((v4_pre_topc @ sk_B_2 @ sk_A))),
% 0.18/0.51      inference('sat_resolution*', [status(thm)], ['71', '72'])).
% 0.18/0.51  thf('81', plain, ((v1_subset_1 @ sk_B_2 @ sk_B_2)),
% 0.18/0.51      inference('simpl_trail', [status(thm)], ['79', '80'])).
% 0.18/0.51  thf('82', plain, ($false), inference('demod', [status(thm)], ['76', '81'])).
% 0.18/0.51  
% 0.18/0.51  % SZS output end Refutation
% 0.18/0.51  
% 0.18/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
