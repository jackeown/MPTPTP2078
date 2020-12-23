%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QmTxBFQuKB

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:17 EST 2020

% Result     : Theorem 0.49s
% Output     : Refutation 0.49s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 717 expanded)
%              Number of leaves         :   30 ( 217 expanded)
%              Depth                    :   18
%              Number of atoms          :  991 (8995 expanded)
%              Number of equality atoms :   34 ( 141 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(t49_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v1_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tex_2 @ B @ A )
          <=> ~ ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( v1_tdlat_3 @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v3_tex_2 @ B @ A )
            <=> ~ ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t49_tex_2])).

thf('0',plain,
    ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
   <= ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( v3_tex_2 @ sk_B_1 @ sk_A )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('5',plain,(
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

thf('6',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ( v1_tops_1 @ X33 @ X34 )
      | ~ ( v3_tex_2 @ X33 @ X34 )
      | ~ ( v3_pre_topc @ X33 @ X34 )
      | ~ ( l1_pre_topc @ X34 )
      | ~ ( v2_pre_topc @ X34 )
      | ( v2_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t47_tex_2])).

thf('7',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_tops_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t17_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v1_tdlat_3 @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( v3_pre_topc @ B @ A ) ) ) ) )).

thf('11',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( v1_tdlat_3 @ X29 )
      | ( v3_pre_topc @ X30 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[t17_tdlat_3])).

thf('12',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v3_pre_topc @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['12','13','14','15'])).

thf('17',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['7','8','9','16'])).

thf('18',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( v1_tops_1 @ sk_B_1 @ sk_A )
    | ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( v1_tops_1 @ sk_B_1 @ sk_A )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','19'])).

thf('21',plain,(
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

thf('22',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( v1_tops_1 @ X23 @ X24 )
      | ( ( k2_pre_topc @ X24 @ X23 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_3])).

thf('23',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
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

thf('27',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( v4_pre_topc @ X8 @ X9 )
      | ( ( k2_pre_topc @ X9 @ X8 )
        = X8 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('28',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = sk_B_1 )
    | ~ ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = sk_B_1 )
    | ~ ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('32',plain,(
    ! [X2: $i,X3: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X2 @ X3 ) @ ( k1_zfmisc_1 @ X2 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('33',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_subset_1 @ X0 @ X1 )
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('36',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','36'])).

thf(fc3_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( v3_pre_topc @ B @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) )).

thf('38',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ~ ( v3_pre_topc @ X19 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X18 ) @ X19 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc3_tops_1])).

thf('39',plain,
    ( ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) @ sk_A )
    | ~ ( v3_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('41',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_subset_1 @ X5 @ ( k3_subset_1 @ X5 @ X4 ) )
        = X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('42',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('44',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
    = sk_B_1 ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','36'])).

thf('46',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( v1_tdlat_3 @ X29 )
      | ( v3_pre_topc @ X30 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[t17_tdlat_3])).

thf('47',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v3_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['47','48','49','50'])).

thf('52',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v4_pre_topc @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['39','44','51','52','53'])).

thf('55',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_1 )
    = sk_B_1 ),
    inference(demod,[status(thm)],['30','54'])).

thf('56',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['25','55'])).

thf('57',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','56'])).

thf('58',plain,
    ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('59',plain,
    ( ( v1_subset_1 @ sk_B_1 @ sk_B_1 )
   <= ( ( v3_tex_2 @ sk_B_1 @ sk_A )
      & ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','56'])).

thf('61',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_B_1 ) )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('63',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v1_subset_1 @ X26 @ X25 )
      | ( X26 != X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('64',plain,(
    ! [X25: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X25 ) )
      | ~ ( v1_subset_1 @ X25 @ X25 ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,
    ( ~ ( v1_subset_1 @ sk_B_1 @ sk_B_1 )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['62','64'])).

thf('66',plain,
    ( ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['59','65'])).

thf('67',plain,
    ( ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('68',plain,(
    ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['3','66','67'])).

thf('69',plain,(
    ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','68'])).

thf('70',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v1_tops_1 @ B @ A )
              & ( v2_tex_2 @ B @ A ) )
           => ( v3_tex_2 @ B @ A ) ) ) ) )).

thf('71',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ( v3_tex_2 @ X35 @ X36 )
      | ~ ( v2_tex_2 @ X35 @ X36 )
      | ~ ( v1_tops_1 @ X35 @ X36 )
      | ~ ( l1_pre_topc @ X36 )
      | ~ ( v2_pre_topc @ X36 )
      | ( v2_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t48_tex_2])).

thf('72',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_tops_1 @ sk_B_1 @ sk_A )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t43_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v1_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( v2_tex_2 @ B @ A ) ) ) )).

thf('76',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ( v2_tex_2 @ X31 @ X32 )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( v1_tdlat_3 @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t43_tex_2])).

thf('77',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['77','78','79','80'])).

thf('82',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(clc,[status(thm)],['81','82'])).

thf('84',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v1_tops_1 @ sk_B_1 @ sk_A )
    | ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['72','73','74','83'])).

thf('85',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_1 )
    = sk_B_1 ),
    inference(demod,[status(thm)],['30','54'])).

thf('86',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X25: $i,X26: $i] :
      ( ( X26 = X25 )
      | ( v1_subset_1 @ X26 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('88',plain,
    ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B_1
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,
    ( ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('90',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_B_1 ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('94',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( ( k2_pre_topc @ X24 @ X23 )
       != ( u1_struct_0 @ X24 ) )
      | ( v1_tops_1 @ X23 @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_3])).

thf('95',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_1 ) )
        | ~ ( l1_pre_topc @ sk_A )
        | ( v1_tops_1 @ X0 @ sk_A )
        | ( ( k2_pre_topc @ sk_A @ X0 )
         != ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('98',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_1 ) )
        | ( v1_tops_1 @ X0 @ sk_A )
        | ( ( k2_pre_topc @ sk_A @ X0 )
         != sk_B_1 ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['95','96','97'])).

thf('99',plain,
    ( ( ( ( k2_pre_topc @ sk_A @ sk_B_1 )
       != sk_B_1 )
      | ( v1_tops_1 @ sk_B_1 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['92','98'])).

thf('100',plain,
    ( ( ( sk_B_1 != sk_B_1 )
      | ( v1_tops_1 @ sk_B_1 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['85','99'])).

thf('101',plain,
    ( ( v1_tops_1 @ sk_B_1 @ sk_A )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,(
    ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['3','66'])).

thf('103',plain,(
    v1_tops_1 @ sk_B_1 @ sk_A ),
    inference(simpl_trail,[status(thm)],['101','102'])).

thf('104',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['84','103'])).

thf('105',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v3_tex_2 @ sk_B_1 @ sk_A ),
    inference(clc,[status(thm)],['104','105'])).

thf('107',plain,(
    $false ),
    inference(demod,[status(thm)],['69','106'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QmTxBFQuKB
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:25:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.49/0.67  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.49/0.67  % Solved by: fo/fo7.sh
% 0.49/0.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.49/0.67  % done 342 iterations in 0.214s
% 0.49/0.67  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.49/0.67  % SZS output start Refutation
% 0.49/0.67  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.49/0.67  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.49/0.67  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.49/0.67  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.49/0.67  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.49/0.67  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.49/0.67  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.49/0.67  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.49/0.67  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.49/0.67  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.49/0.67  thf(sk_A_type, type, sk_A: $i).
% 0.49/0.67  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.49/0.67  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.49/0.67  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.49/0.67  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.49/0.67  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.49/0.67  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.49/0.67  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.49/0.67  thf(t49_tex_2, conjecture,
% 0.49/0.67    (![A:$i]:
% 0.49/0.67     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 0.49/0.67         ( l1_pre_topc @ A ) ) =>
% 0.49/0.67       ( ![B:$i]:
% 0.49/0.67         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.49/0.67           ( ( v3_tex_2 @ B @ A ) <=>
% 0.49/0.67             ( ~( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.49/0.67  thf(zf_stmt_0, negated_conjecture,
% 0.49/0.67    (~( ![A:$i]:
% 0.49/0.67        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.49/0.67            ( v1_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.49/0.67          ( ![B:$i]:
% 0.49/0.67            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.49/0.67              ( ( v3_tex_2 @ B @ A ) <=>
% 0.49/0.67                ( ~( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )),
% 0.49/0.67    inference('cnf.neg', [status(esa)], [t49_tex_2])).
% 0.49/0.67  thf('0', plain,
% 0.49/0.67      (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.49/0.67        | ~ (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.67  thf('1', plain,
% 0.49/0.67      ((~ (v3_tex_2 @ sk_B_1 @ sk_A)) <= (~ ((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.49/0.67      inference('split', [status(esa)], ['0'])).
% 0.49/0.67  thf('2', plain,
% 0.49/0.67      ((~ (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.49/0.67        | (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.67  thf('3', plain,
% 0.49/0.67      (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))) | 
% 0.49/0.67       ((v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.49/0.67      inference('split', [status(esa)], ['2'])).
% 0.49/0.67  thf('4', plain,
% 0.49/0.67      (((v3_tex_2 @ sk_B_1 @ sk_A)) <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.49/0.67      inference('split', [status(esa)], ['2'])).
% 0.49/0.67  thf('5', plain,
% 0.49/0.67      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.67  thf(t47_tex_2, axiom,
% 0.49/0.67    (![A:$i]:
% 0.49/0.67     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.49/0.67       ( ![B:$i]:
% 0.49/0.67         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.49/0.67           ( ( ( v3_pre_topc @ B @ A ) & ( v3_tex_2 @ B @ A ) ) =>
% 0.49/0.67             ( v1_tops_1 @ B @ A ) ) ) ) ))).
% 0.49/0.67  thf('6', plain,
% 0.49/0.67      (![X33 : $i, X34 : $i]:
% 0.49/0.67         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 0.49/0.67          | (v1_tops_1 @ X33 @ X34)
% 0.49/0.67          | ~ (v3_tex_2 @ X33 @ X34)
% 0.49/0.67          | ~ (v3_pre_topc @ X33 @ X34)
% 0.49/0.67          | ~ (l1_pre_topc @ X34)
% 0.49/0.67          | ~ (v2_pre_topc @ X34)
% 0.49/0.67          | (v2_struct_0 @ X34))),
% 0.49/0.67      inference('cnf', [status(esa)], [t47_tex_2])).
% 0.49/0.67  thf('7', plain,
% 0.49/0.67      (((v2_struct_0 @ sk_A)
% 0.49/0.67        | ~ (v2_pre_topc @ sk_A)
% 0.49/0.67        | ~ (l1_pre_topc @ sk_A)
% 0.49/0.67        | ~ (v3_pre_topc @ sk_B_1 @ sk_A)
% 0.49/0.67        | ~ (v3_tex_2 @ sk_B_1 @ sk_A)
% 0.49/0.67        | (v1_tops_1 @ sk_B_1 @ sk_A))),
% 0.49/0.67      inference('sup-', [status(thm)], ['5', '6'])).
% 0.49/0.67  thf('8', plain, ((v2_pre_topc @ sk_A)),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.67  thf('9', plain, ((l1_pre_topc @ sk_A)),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.67  thf('10', plain,
% 0.49/0.67      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.67  thf(t17_tdlat_3, axiom,
% 0.49/0.67    (![A:$i]:
% 0.49/0.67     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.49/0.67       ( ( v1_tdlat_3 @ A ) <=>
% 0.49/0.67         ( ![B:$i]:
% 0.49/0.67           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.49/0.67             ( v3_pre_topc @ B @ A ) ) ) ) ))).
% 0.49/0.67  thf('11', plain,
% 0.49/0.67      (![X29 : $i, X30 : $i]:
% 0.49/0.67         (~ (v1_tdlat_3 @ X29)
% 0.49/0.67          | (v3_pre_topc @ X30 @ X29)
% 0.49/0.67          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.49/0.67          | ~ (l1_pre_topc @ X29)
% 0.49/0.67          | ~ (v2_pre_topc @ X29))),
% 0.49/0.67      inference('cnf', [status(esa)], [t17_tdlat_3])).
% 0.49/0.67  thf('12', plain,
% 0.49/0.67      ((~ (v2_pre_topc @ sk_A)
% 0.49/0.67        | ~ (l1_pre_topc @ sk_A)
% 0.49/0.67        | (v3_pre_topc @ sk_B_1 @ sk_A)
% 0.49/0.67        | ~ (v1_tdlat_3 @ sk_A))),
% 0.49/0.67      inference('sup-', [status(thm)], ['10', '11'])).
% 0.49/0.67  thf('13', plain, ((v2_pre_topc @ sk_A)),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.67  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.67  thf('15', plain, ((v1_tdlat_3 @ sk_A)),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.67  thf('16', plain, ((v3_pre_topc @ sk_B_1 @ sk_A)),
% 0.49/0.67      inference('demod', [status(thm)], ['12', '13', '14', '15'])).
% 0.49/0.67  thf('17', plain,
% 0.49/0.67      (((v2_struct_0 @ sk_A)
% 0.49/0.67        | ~ (v3_tex_2 @ sk_B_1 @ sk_A)
% 0.49/0.67        | (v1_tops_1 @ sk_B_1 @ sk_A))),
% 0.49/0.67      inference('demod', [status(thm)], ['7', '8', '9', '16'])).
% 0.49/0.67  thf('18', plain, (~ (v2_struct_0 @ sk_A)),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.67  thf('19', plain,
% 0.49/0.67      (((v1_tops_1 @ sk_B_1 @ sk_A) | ~ (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.49/0.67      inference('clc', [status(thm)], ['17', '18'])).
% 0.49/0.67  thf('20', plain,
% 0.49/0.67      (((v1_tops_1 @ sk_B_1 @ sk_A)) <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.49/0.67      inference('sup-', [status(thm)], ['4', '19'])).
% 0.49/0.67  thf('21', plain,
% 0.49/0.67      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.67  thf(d2_tops_3, axiom,
% 0.49/0.67    (![A:$i]:
% 0.49/0.67     ( ( l1_pre_topc @ A ) =>
% 0.49/0.67       ( ![B:$i]:
% 0.49/0.67         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.49/0.67           ( ( v1_tops_1 @ B @ A ) <=>
% 0.49/0.67             ( ( k2_pre_topc @ A @ B ) = ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.49/0.67  thf('22', plain,
% 0.49/0.67      (![X23 : $i, X24 : $i]:
% 0.49/0.67         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.49/0.67          | ~ (v1_tops_1 @ X23 @ X24)
% 0.49/0.67          | ((k2_pre_topc @ X24 @ X23) = (u1_struct_0 @ X24))
% 0.49/0.67          | ~ (l1_pre_topc @ X24))),
% 0.49/0.67      inference('cnf', [status(esa)], [d2_tops_3])).
% 0.49/0.67  thf('23', plain,
% 0.49/0.67      ((~ (l1_pre_topc @ sk_A)
% 0.49/0.67        | ((k2_pre_topc @ sk_A @ sk_B_1) = (u1_struct_0 @ sk_A))
% 0.49/0.67        | ~ (v1_tops_1 @ sk_B_1 @ sk_A))),
% 0.49/0.67      inference('sup-', [status(thm)], ['21', '22'])).
% 0.49/0.67  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.67  thf('25', plain,
% 0.49/0.67      ((((k2_pre_topc @ sk_A @ sk_B_1) = (u1_struct_0 @ sk_A))
% 0.49/0.67        | ~ (v1_tops_1 @ sk_B_1 @ sk_A))),
% 0.49/0.67      inference('demod', [status(thm)], ['23', '24'])).
% 0.49/0.67  thf('26', plain,
% 0.49/0.67      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.67  thf(t52_pre_topc, axiom,
% 0.49/0.67    (![A:$i]:
% 0.49/0.67     ( ( l1_pre_topc @ A ) =>
% 0.49/0.67       ( ![B:$i]:
% 0.49/0.67         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.49/0.67           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.49/0.67             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.49/0.67               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.49/0.67  thf('27', plain,
% 0.49/0.67      (![X8 : $i, X9 : $i]:
% 0.49/0.67         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.49/0.67          | ~ (v4_pre_topc @ X8 @ X9)
% 0.49/0.67          | ((k2_pre_topc @ X9 @ X8) = (X8))
% 0.49/0.67          | ~ (l1_pre_topc @ X9))),
% 0.49/0.67      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.49/0.67  thf('28', plain,
% 0.49/0.67      ((~ (l1_pre_topc @ sk_A)
% 0.49/0.67        | ((k2_pre_topc @ sk_A @ sk_B_1) = (sk_B_1))
% 0.49/0.67        | ~ (v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.49/0.67      inference('sup-', [status(thm)], ['26', '27'])).
% 0.49/0.67  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.67  thf('30', plain,
% 0.49/0.67      ((((k2_pre_topc @ sk_A @ sk_B_1) = (sk_B_1))
% 0.49/0.67        | ~ (v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.49/0.67      inference('demod', [status(thm)], ['28', '29'])).
% 0.49/0.67  thf('31', plain,
% 0.49/0.67      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.67  thf(dt_k3_subset_1, axiom,
% 0.49/0.67    (![A:$i,B:$i]:
% 0.49/0.67     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.49/0.67       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.49/0.67  thf('32', plain,
% 0.49/0.67      (![X2 : $i, X3 : $i]:
% 0.49/0.67         ((m1_subset_1 @ (k3_subset_1 @ X2 @ X3) @ (k1_zfmisc_1 @ X2))
% 0.49/0.67          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X2)))),
% 0.49/0.67      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.49/0.67  thf('33', plain,
% 0.49/0.67      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.49/0.67        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.49/0.67      inference('sup-', [status(thm)], ['31', '32'])).
% 0.49/0.67  thf('34', plain,
% 0.49/0.67      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.67  thf(d5_subset_1, axiom,
% 0.49/0.67    (![A:$i,B:$i]:
% 0.49/0.67     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.49/0.67       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.49/0.67  thf('35', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i]:
% 0.49/0.67         (((k3_subset_1 @ X0 @ X1) = (k4_xboole_0 @ X0 @ X1))
% 0.49/0.67          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 0.49/0.67      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.49/0.67  thf('36', plain,
% 0.49/0.67      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)
% 0.49/0.67         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1))),
% 0.49/0.67      inference('sup-', [status(thm)], ['34', '35'])).
% 0.49/0.67  thf('37', plain,
% 0.49/0.67      ((m1_subset_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.49/0.67        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.49/0.67      inference('demod', [status(thm)], ['33', '36'])).
% 0.49/0.67  thf(fc3_tops_1, axiom,
% 0.49/0.67    (![A:$i,B:$i]:
% 0.49/0.67     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & ( v3_pre_topc @ B @ A ) & 
% 0.49/0.67         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.49/0.67       ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ))).
% 0.49/0.67  thf('38', plain,
% 0.49/0.67      (![X18 : $i, X19 : $i]:
% 0.49/0.67         (~ (l1_pre_topc @ X18)
% 0.49/0.67          | ~ (v2_pre_topc @ X18)
% 0.49/0.67          | ~ (v3_pre_topc @ X19 @ X18)
% 0.49/0.67          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.49/0.67          | (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X18) @ X19) @ X18))),
% 0.49/0.67      inference('cnf', [status(esa)], [fc3_tops_1])).
% 0.49/0.67  thf('39', plain,
% 0.49/0.67      (((v4_pre_topc @ 
% 0.49/0.67         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.49/0.67          (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1)) @ 
% 0.49/0.67         sk_A)
% 0.49/0.67        | ~ (v3_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 0.49/0.67        | ~ (v2_pre_topc @ sk_A)
% 0.49/0.67        | ~ (l1_pre_topc @ sk_A))),
% 0.49/0.67      inference('sup-', [status(thm)], ['37', '38'])).
% 0.49/0.67  thf('40', plain,
% 0.49/0.67      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.67  thf(involutiveness_k3_subset_1, axiom,
% 0.49/0.67    (![A:$i,B:$i]:
% 0.49/0.67     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.49/0.67       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.49/0.67  thf('41', plain,
% 0.49/0.67      (![X4 : $i, X5 : $i]:
% 0.49/0.67         (((k3_subset_1 @ X5 @ (k3_subset_1 @ X5 @ X4)) = (X4))
% 0.49/0.67          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.49/0.67      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.49/0.68  thf('42', plain,
% 0.49/0.68      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.49/0.68         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)) = (sk_B_1))),
% 0.49/0.68      inference('sup-', [status(thm)], ['40', '41'])).
% 0.49/0.68  thf('43', plain,
% 0.49/0.68      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)
% 0.49/0.68         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1))),
% 0.49/0.68      inference('sup-', [status(thm)], ['34', '35'])).
% 0.49/0.68  thf('44', plain,
% 0.49/0.68      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.49/0.68         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1)) = (sk_B_1))),
% 0.49/0.68      inference('demod', [status(thm)], ['42', '43'])).
% 0.49/0.68  thf('45', plain,
% 0.49/0.68      ((m1_subset_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.49/0.68        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.49/0.68      inference('demod', [status(thm)], ['33', '36'])).
% 0.49/0.68  thf('46', plain,
% 0.49/0.68      (![X29 : $i, X30 : $i]:
% 0.49/0.68         (~ (v1_tdlat_3 @ X29)
% 0.49/0.68          | (v3_pre_topc @ X30 @ X29)
% 0.49/0.68          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.49/0.68          | ~ (l1_pre_topc @ X29)
% 0.49/0.68          | ~ (v2_pre_topc @ X29))),
% 0.49/0.68      inference('cnf', [status(esa)], [t17_tdlat_3])).
% 0.49/0.68  thf('47', plain,
% 0.49/0.68      ((~ (v2_pre_topc @ sk_A)
% 0.49/0.68        | ~ (l1_pre_topc @ sk_A)
% 0.49/0.68        | (v3_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 0.49/0.68        | ~ (v1_tdlat_3 @ sk_A))),
% 0.49/0.68      inference('sup-', [status(thm)], ['45', '46'])).
% 0.49/0.68  thf('48', plain, ((v2_pre_topc @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('49', plain, ((l1_pre_topc @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('50', plain, ((v1_tdlat_3 @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('51', plain,
% 0.49/0.68      ((v3_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)),
% 0.49/0.68      inference('demod', [status(thm)], ['47', '48', '49', '50'])).
% 0.49/0.68  thf('52', plain, ((v2_pre_topc @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('54', plain, ((v4_pre_topc @ sk_B_1 @ sk_A)),
% 0.49/0.68      inference('demod', [status(thm)], ['39', '44', '51', '52', '53'])).
% 0.49/0.68  thf('55', plain, (((k2_pre_topc @ sk_A @ sk_B_1) = (sk_B_1))),
% 0.49/0.68      inference('demod', [status(thm)], ['30', '54'])).
% 0.49/0.68  thf('56', plain,
% 0.49/0.68      ((((sk_B_1) = (u1_struct_0 @ sk_A)) | ~ (v1_tops_1 @ sk_B_1 @ sk_A))),
% 0.49/0.68      inference('demod', [status(thm)], ['25', '55'])).
% 0.49/0.68  thf('57', plain,
% 0.49/0.68      ((((sk_B_1) = (u1_struct_0 @ sk_A))) <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.49/0.68      inference('sup-', [status(thm)], ['20', '56'])).
% 0.49/0.68  thf('58', plain,
% 0.49/0.68      (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.49/0.68         <= (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.49/0.68      inference('split', [status(esa)], ['0'])).
% 0.49/0.68  thf('59', plain,
% 0.49/0.68      (((v1_subset_1 @ sk_B_1 @ sk_B_1))
% 0.49/0.68         <= (((v3_tex_2 @ sk_B_1 @ sk_A)) & 
% 0.49/0.68             ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.49/0.68      inference('sup+', [status(thm)], ['57', '58'])).
% 0.49/0.68  thf('60', plain,
% 0.49/0.68      ((((sk_B_1) = (u1_struct_0 @ sk_A))) <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.49/0.68      inference('sup-', [status(thm)], ['20', '56'])).
% 0.49/0.68  thf('61', plain,
% 0.49/0.68      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('62', plain,
% 0.49/0.68      (((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_B_1)))
% 0.49/0.68         <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.49/0.68      inference('sup+', [status(thm)], ['60', '61'])).
% 0.49/0.68  thf(d7_subset_1, axiom,
% 0.49/0.68    (![A:$i,B:$i]:
% 0.49/0.68     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.49/0.68       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.49/0.68  thf('63', plain,
% 0.49/0.68      (![X25 : $i, X26 : $i]:
% 0.49/0.68         (~ (v1_subset_1 @ X26 @ X25)
% 0.49/0.68          | ((X26) != (X25))
% 0.49/0.68          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X25)))),
% 0.49/0.68      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.49/0.68  thf('64', plain,
% 0.49/0.68      (![X25 : $i]:
% 0.49/0.68         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X25))
% 0.49/0.68          | ~ (v1_subset_1 @ X25 @ X25))),
% 0.49/0.68      inference('simplify', [status(thm)], ['63'])).
% 0.49/0.68  thf('65', plain,
% 0.49/0.68      ((~ (v1_subset_1 @ sk_B_1 @ sk_B_1)) <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.49/0.68      inference('sup-', [status(thm)], ['62', '64'])).
% 0.49/0.68  thf('66', plain,
% 0.49/0.68      (~ ((v3_tex_2 @ sk_B_1 @ sk_A)) | 
% 0.49/0.68       ~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.49/0.68      inference('sup-', [status(thm)], ['59', '65'])).
% 0.49/0.68  thf('67', plain,
% 0.49/0.68      (~ ((v3_tex_2 @ sk_B_1 @ sk_A)) | 
% 0.49/0.68       ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.49/0.68      inference('split', [status(esa)], ['0'])).
% 0.49/0.68  thf('68', plain, (~ ((v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.49/0.68      inference('sat_resolution*', [status(thm)], ['3', '66', '67'])).
% 0.49/0.68  thf('69', plain, (~ (v3_tex_2 @ sk_B_1 @ sk_A)),
% 0.49/0.68      inference('simpl_trail', [status(thm)], ['1', '68'])).
% 0.49/0.68  thf('70', plain,
% 0.49/0.68      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf(t48_tex_2, axiom,
% 0.49/0.68    (![A:$i]:
% 0.49/0.68     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.49/0.68       ( ![B:$i]:
% 0.49/0.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.49/0.68           ( ( ( v1_tops_1 @ B @ A ) & ( v2_tex_2 @ B @ A ) ) =>
% 0.49/0.68             ( v3_tex_2 @ B @ A ) ) ) ) ))).
% 0.49/0.68  thf('71', plain,
% 0.49/0.68      (![X35 : $i, X36 : $i]:
% 0.49/0.68         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 0.49/0.68          | (v3_tex_2 @ X35 @ X36)
% 0.49/0.68          | ~ (v2_tex_2 @ X35 @ X36)
% 0.49/0.68          | ~ (v1_tops_1 @ X35 @ X36)
% 0.49/0.68          | ~ (l1_pre_topc @ X36)
% 0.49/0.68          | ~ (v2_pre_topc @ X36)
% 0.49/0.68          | (v2_struct_0 @ X36))),
% 0.49/0.68      inference('cnf', [status(esa)], [t48_tex_2])).
% 0.49/0.68  thf('72', plain,
% 0.49/0.68      (((v2_struct_0 @ sk_A)
% 0.49/0.68        | ~ (v2_pre_topc @ sk_A)
% 0.49/0.68        | ~ (l1_pre_topc @ sk_A)
% 0.49/0.68        | ~ (v1_tops_1 @ sk_B_1 @ sk_A)
% 0.49/0.68        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.49/0.68        | (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.49/0.68      inference('sup-', [status(thm)], ['70', '71'])).
% 0.49/0.68  thf('73', plain, ((v2_pre_topc @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('74', plain, ((l1_pre_topc @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('75', plain,
% 0.49/0.68      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf(t43_tex_2, axiom,
% 0.49/0.68    (![A:$i]:
% 0.49/0.68     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 0.49/0.68         ( l1_pre_topc @ A ) ) =>
% 0.49/0.68       ( ![B:$i]:
% 0.49/0.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.49/0.68           ( v2_tex_2 @ B @ A ) ) ) ))).
% 0.49/0.68  thf('76', plain,
% 0.49/0.68      (![X31 : $i, X32 : $i]:
% 0.49/0.68         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.49/0.68          | (v2_tex_2 @ X31 @ X32)
% 0.49/0.68          | ~ (l1_pre_topc @ X32)
% 0.49/0.68          | ~ (v1_tdlat_3 @ X32)
% 0.49/0.68          | ~ (v2_pre_topc @ X32)
% 0.49/0.68          | (v2_struct_0 @ X32))),
% 0.49/0.68      inference('cnf', [status(esa)], [t43_tex_2])).
% 0.49/0.68  thf('77', plain,
% 0.49/0.68      (((v2_struct_0 @ sk_A)
% 0.49/0.68        | ~ (v2_pre_topc @ sk_A)
% 0.49/0.68        | ~ (v1_tdlat_3 @ sk_A)
% 0.49/0.68        | ~ (l1_pre_topc @ sk_A)
% 0.49/0.68        | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.49/0.68      inference('sup-', [status(thm)], ['75', '76'])).
% 0.49/0.68  thf('78', plain, ((v2_pre_topc @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('79', plain, ((v1_tdlat_3 @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('80', plain, ((l1_pre_topc @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('81', plain, (((v2_struct_0 @ sk_A) | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.49/0.68      inference('demod', [status(thm)], ['77', '78', '79', '80'])).
% 0.49/0.68  thf('82', plain, (~ (v2_struct_0 @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('83', plain, ((v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.49/0.68      inference('clc', [status(thm)], ['81', '82'])).
% 0.49/0.68  thf('84', plain,
% 0.49/0.68      (((v2_struct_0 @ sk_A)
% 0.49/0.68        | ~ (v1_tops_1 @ sk_B_1 @ sk_A)
% 0.49/0.68        | (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.49/0.68      inference('demod', [status(thm)], ['72', '73', '74', '83'])).
% 0.49/0.68  thf('85', plain, (((k2_pre_topc @ sk_A @ sk_B_1) = (sk_B_1))),
% 0.49/0.68      inference('demod', [status(thm)], ['30', '54'])).
% 0.49/0.68  thf('86', plain,
% 0.49/0.68      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('87', plain,
% 0.49/0.68      (![X25 : $i, X26 : $i]:
% 0.49/0.68         (((X26) = (X25))
% 0.49/0.68          | (v1_subset_1 @ X26 @ X25)
% 0.49/0.68          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X25)))),
% 0.49/0.68      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.49/0.68  thf('88', plain,
% 0.49/0.68      (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.49/0.68        | ((sk_B_1) = (u1_struct_0 @ sk_A)))),
% 0.49/0.68      inference('sup-', [status(thm)], ['86', '87'])).
% 0.49/0.68  thf('89', plain,
% 0.49/0.68      ((~ (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.49/0.68         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.49/0.68      inference('split', [status(esa)], ['2'])).
% 0.49/0.68  thf('90', plain,
% 0.49/0.68      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.49/0.68         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.49/0.68      inference('sup-', [status(thm)], ['88', '89'])).
% 0.49/0.68  thf('91', plain,
% 0.49/0.68      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('92', plain,
% 0.49/0.68      (((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_B_1)))
% 0.49/0.68         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.49/0.68      inference('sup+', [status(thm)], ['90', '91'])).
% 0.49/0.68  thf('93', plain,
% 0.49/0.68      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.49/0.68         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.49/0.68      inference('sup-', [status(thm)], ['88', '89'])).
% 0.49/0.68  thf('94', plain,
% 0.49/0.68      (![X23 : $i, X24 : $i]:
% 0.49/0.68         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.49/0.68          | ((k2_pre_topc @ X24 @ X23) != (u1_struct_0 @ X24))
% 0.49/0.68          | (v1_tops_1 @ X23 @ X24)
% 0.49/0.68          | ~ (l1_pre_topc @ X24))),
% 0.49/0.68      inference('cnf', [status(esa)], [d2_tops_3])).
% 0.49/0.68  thf('95', plain,
% 0.49/0.68      ((![X0 : $i]:
% 0.49/0.68          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_1))
% 0.49/0.68           | ~ (l1_pre_topc @ sk_A)
% 0.49/0.68           | (v1_tops_1 @ X0 @ sk_A)
% 0.49/0.68           | ((k2_pre_topc @ sk_A @ X0) != (u1_struct_0 @ sk_A))))
% 0.49/0.68         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.49/0.68      inference('sup-', [status(thm)], ['93', '94'])).
% 0.49/0.68  thf('96', plain, ((l1_pre_topc @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('97', plain,
% 0.49/0.68      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.49/0.68         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.49/0.68      inference('sup-', [status(thm)], ['88', '89'])).
% 0.49/0.68  thf('98', plain,
% 0.49/0.68      ((![X0 : $i]:
% 0.49/0.68          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_1))
% 0.49/0.68           | (v1_tops_1 @ X0 @ sk_A)
% 0.49/0.68           | ((k2_pre_topc @ sk_A @ X0) != (sk_B_1))))
% 0.49/0.68         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.49/0.68      inference('demod', [status(thm)], ['95', '96', '97'])).
% 0.49/0.68  thf('99', plain,
% 0.49/0.68      (((((k2_pre_topc @ sk_A @ sk_B_1) != (sk_B_1))
% 0.49/0.68         | (v1_tops_1 @ sk_B_1 @ sk_A)))
% 0.49/0.68         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.49/0.68      inference('sup-', [status(thm)], ['92', '98'])).
% 0.49/0.68  thf('100', plain,
% 0.49/0.68      (((((sk_B_1) != (sk_B_1)) | (v1_tops_1 @ sk_B_1 @ sk_A)))
% 0.49/0.68         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.49/0.68      inference('sup-', [status(thm)], ['85', '99'])).
% 0.49/0.68  thf('101', plain,
% 0.49/0.68      (((v1_tops_1 @ sk_B_1 @ sk_A))
% 0.49/0.68         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.49/0.68      inference('simplify', [status(thm)], ['100'])).
% 0.49/0.68  thf('102', plain, (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.49/0.68      inference('sat_resolution*', [status(thm)], ['3', '66'])).
% 0.49/0.68  thf('103', plain, ((v1_tops_1 @ sk_B_1 @ sk_A)),
% 0.49/0.68      inference('simpl_trail', [status(thm)], ['101', '102'])).
% 0.49/0.68  thf('104', plain, (((v2_struct_0 @ sk_A) | (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.49/0.68      inference('demod', [status(thm)], ['84', '103'])).
% 0.49/0.68  thf('105', plain, (~ (v2_struct_0 @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('106', plain, ((v3_tex_2 @ sk_B_1 @ sk_A)),
% 0.49/0.68      inference('clc', [status(thm)], ['104', '105'])).
% 0.49/0.68  thf('107', plain, ($false), inference('demod', [status(thm)], ['69', '106'])).
% 0.49/0.68  
% 0.49/0.68  % SZS output end Refutation
% 0.49/0.68  
% 0.49/0.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
