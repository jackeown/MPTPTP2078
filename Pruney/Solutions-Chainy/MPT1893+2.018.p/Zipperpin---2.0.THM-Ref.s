%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.66fcCyt9AF

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:35 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  144 (1046 expanded)
%              Number of leaves         :   35 ( 309 expanded)
%              Depth                    :   18
%              Number of atoms          :  955 (15304 expanded)
%              Number of equality atoms :   35 ( 188 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

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
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t46_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v1_xboole_0 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ~ ( v3_tex_2 @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_xboole_0 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( v3_tex_2 @ X21 @ X22 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t46_tex_2])).

thf('2',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v3_tex_2 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['2','3','4','5'])).

thf('7',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_tex_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_subset_1 @ B @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) )
     => ~ ( v1_xboole_0 @ ( k3_subset_1 @ A @ B ) ) ) )).

thf('10',plain,(
    ! [X17: $i,X18: $i] :
      ( ( v1_xboole_0 @ X17 )
      | ~ ( v1_subset_1 @ X18 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( v1_xboole_0 @ ( k3_subset_1 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[fc1_tex_2])).

thf('11',plain,
    ( ~ ( v1_xboole_0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
    | ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ~ ( v1_xboole_0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
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

thf('15',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( v4_pre_topc @ X11 @ X12 )
      | ( ( k2_pre_topc @ X12 @ X11 )
        = X11 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('16',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = sk_B_1 )
    | ~ ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = sk_B_1 )
    | ~ ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( v3_pre_topc @ sk_B_1 @ sk_A )
    | ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( v3_pre_topc @ sk_B_1 @ sk_A )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['19'])).

thf('21',plain,(
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

thf('22',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( v1_tops_1 @ X23 @ X24 )
      | ~ ( v3_tex_2 @ X23 @ X24 )
      | ~ ( v3_pre_topc @ X23 @ X24 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t47_tex_2])).

thf('23',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_tops_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v3_tex_2 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_1 @ sk_A )
    | ( v1_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['23','24','25','26'])).

thf('28',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( v1_tops_1 @ sk_B_1 @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( v1_tops_1 @ sk_B_1 @ sk_A )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','29'])).

thf('31',plain,(
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

thf('32',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v1_tops_1 @ X15 @ X16 )
      | ( ( k2_pre_topc @ X16 @ X15 )
        = ( u1_struct_0 @ X16 ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_3])).

thf('33',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = ( u1_struct_0 @ sk_A ) )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['30','35'])).

thf('37',plain,
    ( ( v4_pre_topc @ sk_B_1 @ sk_A )
   <= ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['19'])).

thf('38',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('39',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v3_tdlat_3 @ X19 )
      | ~ ( v4_pre_topc @ X20 @ X19 )
      | ( v3_pre_topc @ X20 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t24_tdlat_3])).

thf('40',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( v4_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( v3_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['40','41','42','43'])).

thf('45',plain,
    ( ( v3_pre_topc @ sk_B_1 @ sk_A )
   <= ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['37','44'])).

thf('46',plain,
    ( ( v1_tops_1 @ sk_B_1 @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('47',plain,
    ( ( v1_tops_1 @ sk_B_1 @ sk_A )
   <= ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('49',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = ( u1_struct_0 @ sk_A ) )
   <= ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( v4_pre_topc @ sk_B_1 @ sk_A )
   <= ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['19'])).

thf('51',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = sk_B_1 )
    | ~ ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('52',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = sk_B_1 )
   <= ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_1 )
   <= ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['49','52'])).

thf('54',plain,
    ( ~ ( v1_xboole_0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('55',plain,
    ( ( ~ ( v1_xboole_0 @ ( k3_subset_1 @ sk_B_1 @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('56',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('57',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_subset_1 @ X5 @ ( k3_subset_1 @ X5 @ X4 ) )
        = X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k1_subset_1 @ X0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf(t22_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ) )).

thf('60',plain,(
    ! [X6: $i] :
      ( ( k2_subset_1 @ X6 )
      = ( k3_subset_1 @ X6 @ ( k1_subset_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t22_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('61',plain,(
    ! [X1: $i] :
      ( ( k2_subset_1 @ X1 )
      = X1 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('62',plain,(
    ! [X6: $i] :
      ( X6
      = ( k3_subset_1 @ X6 @ ( k1_subset_1 @ X6 ) ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['59','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['58','63'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('65',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('66',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_1 )
   <= ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['49','52'])).

thf('67',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
   <= ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['55','64','65','66'])).

thf('68',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('69',plain,(
    ~ ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( v3_pre_topc @ sk_B_1 @ sk_A )
    | ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['19'])).

thf('71',plain,(
    v3_pre_topc @ sk_B_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['36','71'])).

thf('73',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_1 )
    | ~ ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['18','72'])).

thf('74',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t29_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('75',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X14 ) @ X13 ) @ X14 )
      | ( v4_pre_topc @ X13 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t29_tops_1])).

thf('76',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( v4_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('80',plain,(
    ! [X2: $i,X3: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X2 @ X3 ) @ ( k1_zfmisc_1 @ X2 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('81',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v3_tdlat_3 @ X19 )
      | ~ ( v4_pre_topc @ X20 @ X19 )
      | ( v3_pre_topc @ X20 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t24_tdlat_3])).

thf('83',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
    | ~ ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
    | ~ ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['83','84','85','86'])).

thf('88',plain,
    ( ( v3_pre_topc @ sk_B_1 @ sk_A )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['19'])).

thf('89',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('90',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X14 ) @ X13 ) @ X14 )
      | ( v4_pre_topc @ X13 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t29_tops_1])).

thf('91',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
    | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_subset_1 @ X5 @ ( k3_subset_1 @ X5 @ X4 ) )
        = X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('95',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,
    ( ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['91','92','95'])).

thf('97',plain,
    ( ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['88','96'])).

thf('98',plain,(
    v3_pre_topc @ sk_B_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['69','70'])).

thf('99',plain,(
    v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ),
    inference(simpl_trail,[status(thm)],['97','98'])).

thf('100',plain,(
    v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['87','99'])).

thf('101',plain,(
    v4_pre_topc @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['78','100'])).

thf('102',plain,
    ( ( u1_struct_0 @ sk_A )
    = sk_B_1 ),
    inference(demod,[status(thm)],['73','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['58','63'])).

thf('104',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('105',plain,
    ( ( u1_struct_0 @ sk_A )
    = sk_B_1 ),
    inference(demod,[status(thm)],['73','101'])).

thf('106',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(demod,[status(thm)],['13','102','103','104','105'])).

thf('107',plain,(
    $false ),
    inference(demod,[status(thm)],['8','106'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.66fcCyt9AF
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:40:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.34  % Running portfolio for 600 s
% 0.19/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.19/0.34  % Number of cores: 8
% 0.19/0.34  % Python version: Python 3.6.8
% 0.19/0.34  % Running in FO mode
% 0.19/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.53  % Solved by: fo/fo7.sh
% 0.19/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.53  % done 249 iterations in 0.080s
% 0.19/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.53  % SZS output start Refutation
% 0.19/0.53  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.19/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.19/0.53  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.19/0.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.53  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.19/0.53  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.19/0.53  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.19/0.53  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.19/0.53  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.19/0.53  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.19/0.53  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.19/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.53  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.19/0.53  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.19/0.53  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.19/0.53  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.19/0.53  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.19/0.53  thf(t61_tex_2, conjecture,
% 0.19/0.53    (![A:$i]:
% 0.19/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.19/0.53         ( l1_pre_topc @ A ) ) =>
% 0.19/0.53       ( ![B:$i]:
% 0.19/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.53           ( ~( ( ( v3_pre_topc @ B @ A ) | ( v4_pre_topc @ B @ A ) ) & 
% 0.19/0.53                ( v3_tex_2 @ B @ A ) & 
% 0.19/0.53                ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.19/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.53    (~( ![A:$i]:
% 0.19/0.53        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.19/0.53            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.53          ( ![B:$i]:
% 0.19/0.53            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.53              ( ~( ( ( v3_pre_topc @ B @ A ) | ( v4_pre_topc @ B @ A ) ) & 
% 0.19/0.53                   ( v3_tex_2 @ B @ A ) & 
% 0.19/0.53                   ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )),
% 0.19/0.53    inference('cnf.neg', [status(esa)], [t61_tex_2])).
% 0.19/0.53  thf('0', plain,
% 0.19/0.53      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf(t46_tex_2, axiom,
% 0.19/0.53    (![A:$i]:
% 0.19/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.53       ( ![B:$i]:
% 0.19/0.53         ( ( ( v1_xboole_0 @ B ) & 
% 0.19/0.53             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.19/0.53           ( ~( v3_tex_2 @ B @ A ) ) ) ) ))).
% 0.19/0.53  thf('1', plain,
% 0.19/0.53      (![X21 : $i, X22 : $i]:
% 0.19/0.53         (~ (v1_xboole_0 @ X21)
% 0.19/0.53          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.19/0.53          | ~ (v3_tex_2 @ X21 @ X22)
% 0.19/0.53          | ~ (l1_pre_topc @ X22)
% 0.19/0.53          | ~ (v2_pre_topc @ X22)
% 0.19/0.53          | (v2_struct_0 @ X22))),
% 0.19/0.53      inference('cnf', [status(esa)], [t46_tex_2])).
% 0.19/0.53  thf('2', plain,
% 0.19/0.53      (((v2_struct_0 @ sk_A)
% 0.19/0.53        | ~ (v2_pre_topc @ sk_A)
% 0.19/0.53        | ~ (l1_pre_topc @ sk_A)
% 0.19/0.53        | ~ (v3_tex_2 @ sk_B_1 @ sk_A)
% 0.19/0.53        | ~ (v1_xboole_0 @ sk_B_1))),
% 0.19/0.53      inference('sup-', [status(thm)], ['0', '1'])).
% 0.19/0.53  thf('3', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('5', plain, ((v3_tex_2 @ sk_B_1 @ sk_A)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('6', plain, (((v2_struct_0 @ sk_A) | ~ (v1_xboole_0 @ sk_B_1))),
% 0.19/0.53      inference('demod', [status(thm)], ['2', '3', '4', '5'])).
% 0.19/0.53  thf('7', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('8', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.19/0.53      inference('clc', [status(thm)], ['6', '7'])).
% 0.19/0.53  thf('9', plain,
% 0.19/0.53      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf(fc1_tex_2, axiom,
% 0.19/0.53    (![A:$i,B:$i]:
% 0.19/0.53     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_subset_1 @ B @ A ) & 
% 0.19/0.53         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.19/0.53       ( ~( v1_xboole_0 @ ( k3_subset_1 @ A @ B ) ) ) ))).
% 0.19/0.53  thf('10', plain,
% 0.19/0.53      (![X17 : $i, X18 : $i]:
% 0.19/0.53         ((v1_xboole_0 @ X17)
% 0.19/0.53          | ~ (v1_subset_1 @ X18 @ X17)
% 0.19/0.53          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X17))
% 0.19/0.53          | ~ (v1_xboole_0 @ (k3_subset_1 @ X17 @ X18)))),
% 0.19/0.53      inference('cnf', [status(esa)], [fc1_tex_2])).
% 0.19/0.53  thf('11', plain,
% 0.19/0.53      ((~ (v1_xboole_0 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))
% 0.19/0.53        | ~ (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.19/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['9', '10'])).
% 0.19/0.53  thf('12', plain, ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('13', plain,
% 0.19/0.53      ((~ (v1_xboole_0 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))
% 0.19/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.53      inference('demod', [status(thm)], ['11', '12'])).
% 0.19/0.53  thf('14', plain,
% 0.19/0.53      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf(t52_pre_topc, axiom,
% 0.19/0.53    (![A:$i]:
% 0.19/0.53     ( ( l1_pre_topc @ A ) =>
% 0.19/0.53       ( ![B:$i]:
% 0.19/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.53           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.19/0.53             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.19/0.53               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.19/0.53  thf('15', plain,
% 0.19/0.53      (![X11 : $i, X12 : $i]:
% 0.19/0.53         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.19/0.53          | ~ (v4_pre_topc @ X11 @ X12)
% 0.19/0.53          | ((k2_pre_topc @ X12 @ X11) = (X11))
% 0.19/0.53          | ~ (l1_pre_topc @ X12))),
% 0.19/0.53      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.19/0.53  thf('16', plain,
% 0.19/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.19/0.53        | ((k2_pre_topc @ sk_A @ sk_B_1) = (sk_B_1))
% 0.19/0.53        | ~ (v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.19/0.53      inference('sup-', [status(thm)], ['14', '15'])).
% 0.19/0.53  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('18', plain,
% 0.19/0.53      ((((k2_pre_topc @ sk_A @ sk_B_1) = (sk_B_1))
% 0.19/0.53        | ~ (v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.19/0.53      inference('demod', [status(thm)], ['16', '17'])).
% 0.19/0.53  thf('19', plain,
% 0.19/0.53      (((v3_pre_topc @ sk_B_1 @ sk_A) | (v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('20', plain,
% 0.19/0.53      (((v3_pre_topc @ sk_B_1 @ sk_A)) <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.19/0.53      inference('split', [status(esa)], ['19'])).
% 0.19/0.53  thf('21', plain,
% 0.19/0.53      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf(t47_tex_2, axiom,
% 0.19/0.53    (![A:$i]:
% 0.19/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.53       ( ![B:$i]:
% 0.19/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.53           ( ( ( v3_pre_topc @ B @ A ) & ( v3_tex_2 @ B @ A ) ) =>
% 0.19/0.53             ( v1_tops_1 @ B @ A ) ) ) ) ))).
% 0.19/0.53  thf('22', plain,
% 0.19/0.53      (![X23 : $i, X24 : $i]:
% 0.19/0.53         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.19/0.53          | (v1_tops_1 @ X23 @ X24)
% 0.19/0.53          | ~ (v3_tex_2 @ X23 @ X24)
% 0.19/0.53          | ~ (v3_pre_topc @ X23 @ X24)
% 0.19/0.53          | ~ (l1_pre_topc @ X24)
% 0.19/0.53          | ~ (v2_pre_topc @ X24)
% 0.19/0.53          | (v2_struct_0 @ X24))),
% 0.19/0.53      inference('cnf', [status(esa)], [t47_tex_2])).
% 0.19/0.53  thf('23', plain,
% 0.19/0.53      (((v2_struct_0 @ sk_A)
% 0.19/0.53        | ~ (v2_pre_topc @ sk_A)
% 0.19/0.53        | ~ (l1_pre_topc @ sk_A)
% 0.19/0.53        | ~ (v3_pre_topc @ sk_B_1 @ sk_A)
% 0.19/0.53        | ~ (v3_tex_2 @ sk_B_1 @ sk_A)
% 0.19/0.53        | (v1_tops_1 @ sk_B_1 @ sk_A))),
% 0.19/0.53      inference('sup-', [status(thm)], ['21', '22'])).
% 0.19/0.53  thf('24', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('26', plain, ((v3_tex_2 @ sk_B_1 @ sk_A)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('27', plain,
% 0.19/0.53      (((v2_struct_0 @ sk_A)
% 0.19/0.53        | ~ (v3_pre_topc @ sk_B_1 @ sk_A)
% 0.19/0.53        | (v1_tops_1 @ sk_B_1 @ sk_A))),
% 0.19/0.53      inference('demod', [status(thm)], ['23', '24', '25', '26'])).
% 0.19/0.53  thf('28', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('29', plain,
% 0.19/0.53      (((v1_tops_1 @ sk_B_1 @ sk_A) | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.19/0.53      inference('clc', [status(thm)], ['27', '28'])).
% 0.19/0.53  thf('30', plain,
% 0.19/0.53      (((v1_tops_1 @ sk_B_1 @ sk_A)) <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['20', '29'])).
% 0.19/0.53  thf('31', plain,
% 0.19/0.53      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf(d2_tops_3, axiom,
% 0.19/0.53    (![A:$i]:
% 0.19/0.53     ( ( l1_pre_topc @ A ) =>
% 0.19/0.53       ( ![B:$i]:
% 0.19/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.53           ( ( v1_tops_1 @ B @ A ) <=>
% 0.19/0.53             ( ( k2_pre_topc @ A @ B ) = ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.19/0.53  thf('32', plain,
% 0.19/0.53      (![X15 : $i, X16 : $i]:
% 0.19/0.53         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.19/0.53          | ~ (v1_tops_1 @ X15 @ X16)
% 0.19/0.53          | ((k2_pre_topc @ X16 @ X15) = (u1_struct_0 @ X16))
% 0.19/0.53          | ~ (l1_pre_topc @ X16))),
% 0.19/0.53      inference('cnf', [status(esa)], [d2_tops_3])).
% 0.19/0.53  thf('33', plain,
% 0.19/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.19/0.53        | ((k2_pre_topc @ sk_A @ sk_B_1) = (u1_struct_0 @ sk_A))
% 0.19/0.53        | ~ (v1_tops_1 @ sk_B_1 @ sk_A))),
% 0.19/0.53      inference('sup-', [status(thm)], ['31', '32'])).
% 0.19/0.53  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('35', plain,
% 0.19/0.53      ((((k2_pre_topc @ sk_A @ sk_B_1) = (u1_struct_0 @ sk_A))
% 0.19/0.53        | ~ (v1_tops_1 @ sk_B_1 @ sk_A))),
% 0.19/0.53      inference('demod', [status(thm)], ['33', '34'])).
% 0.19/0.53  thf('36', plain,
% 0.19/0.53      ((((k2_pre_topc @ sk_A @ sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.19/0.53         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['30', '35'])).
% 0.19/0.53  thf('37', plain,
% 0.19/0.53      (((v4_pre_topc @ sk_B_1 @ sk_A)) <= (((v4_pre_topc @ sk_B_1 @ sk_A)))),
% 0.19/0.53      inference('split', [status(esa)], ['19'])).
% 0.19/0.53  thf('38', plain,
% 0.19/0.53      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf(t24_tdlat_3, axiom,
% 0.19/0.53    (![A:$i]:
% 0.19/0.53     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.53       ( ( v3_tdlat_3 @ A ) <=>
% 0.19/0.53         ( ![B:$i]:
% 0.19/0.53           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.53             ( ( v4_pre_topc @ B @ A ) => ( v3_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.19/0.53  thf('39', plain,
% 0.19/0.53      (![X19 : $i, X20 : $i]:
% 0.19/0.53         (~ (v3_tdlat_3 @ X19)
% 0.19/0.53          | ~ (v4_pre_topc @ X20 @ X19)
% 0.19/0.53          | (v3_pre_topc @ X20 @ X19)
% 0.19/0.53          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.19/0.53          | ~ (l1_pre_topc @ X19)
% 0.19/0.53          | ~ (v2_pre_topc @ X19))),
% 0.19/0.53      inference('cnf', [status(esa)], [t24_tdlat_3])).
% 0.19/0.53  thf('40', plain,
% 0.19/0.53      ((~ (v2_pre_topc @ sk_A)
% 0.19/0.53        | ~ (l1_pre_topc @ sk_A)
% 0.19/0.53        | (v3_pre_topc @ sk_B_1 @ sk_A)
% 0.19/0.53        | ~ (v4_pre_topc @ sk_B_1 @ sk_A)
% 0.19/0.53        | ~ (v3_tdlat_3 @ sk_A))),
% 0.19/0.53      inference('sup-', [status(thm)], ['38', '39'])).
% 0.19/0.53  thf('41', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('43', plain, ((v3_tdlat_3 @ sk_A)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('44', plain,
% 0.19/0.53      (((v3_pre_topc @ sk_B_1 @ sk_A) | ~ (v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.19/0.53      inference('demod', [status(thm)], ['40', '41', '42', '43'])).
% 0.19/0.53  thf('45', plain,
% 0.19/0.53      (((v3_pre_topc @ sk_B_1 @ sk_A)) <= (((v4_pre_topc @ sk_B_1 @ sk_A)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['37', '44'])).
% 0.19/0.53  thf('46', plain,
% 0.19/0.53      (((v1_tops_1 @ sk_B_1 @ sk_A) | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.19/0.53      inference('clc', [status(thm)], ['27', '28'])).
% 0.19/0.53  thf('47', plain,
% 0.19/0.53      (((v1_tops_1 @ sk_B_1 @ sk_A)) <= (((v4_pre_topc @ sk_B_1 @ sk_A)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['45', '46'])).
% 0.19/0.53  thf('48', plain,
% 0.19/0.53      ((((k2_pre_topc @ sk_A @ sk_B_1) = (u1_struct_0 @ sk_A))
% 0.19/0.53        | ~ (v1_tops_1 @ sk_B_1 @ sk_A))),
% 0.19/0.53      inference('demod', [status(thm)], ['33', '34'])).
% 0.19/0.53  thf('49', plain,
% 0.19/0.53      ((((k2_pre_topc @ sk_A @ sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.19/0.53         <= (((v4_pre_topc @ sk_B_1 @ sk_A)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['47', '48'])).
% 0.19/0.53  thf('50', plain,
% 0.19/0.53      (((v4_pre_topc @ sk_B_1 @ sk_A)) <= (((v4_pre_topc @ sk_B_1 @ sk_A)))),
% 0.19/0.53      inference('split', [status(esa)], ['19'])).
% 0.19/0.53  thf('51', plain,
% 0.19/0.53      ((((k2_pre_topc @ sk_A @ sk_B_1) = (sk_B_1))
% 0.19/0.53        | ~ (v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.19/0.53      inference('demod', [status(thm)], ['16', '17'])).
% 0.19/0.53  thf('52', plain,
% 0.19/0.53      ((((k2_pre_topc @ sk_A @ sk_B_1) = (sk_B_1)))
% 0.19/0.53         <= (((v4_pre_topc @ sk_B_1 @ sk_A)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['50', '51'])).
% 0.19/0.53  thf('53', plain,
% 0.19/0.53      ((((u1_struct_0 @ sk_A) = (sk_B_1))) <= (((v4_pre_topc @ sk_B_1 @ sk_A)))),
% 0.19/0.53      inference('sup+', [status(thm)], ['49', '52'])).
% 0.19/0.53  thf('54', plain,
% 0.19/0.53      ((~ (v1_xboole_0 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))
% 0.19/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.53      inference('demod', [status(thm)], ['11', '12'])).
% 0.19/0.53  thf('55', plain,
% 0.19/0.53      (((~ (v1_xboole_0 @ (k3_subset_1 @ sk_B_1 @ sk_B_1))
% 0.19/0.53         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.19/0.53         <= (((v4_pre_topc @ sk_B_1 @ sk_A)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['53', '54'])).
% 0.19/0.53  thf(t4_subset_1, axiom,
% 0.19/0.53    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.19/0.53  thf('56', plain,
% 0.19/0.53      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 0.19/0.53      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.19/0.53  thf(involutiveness_k3_subset_1, axiom,
% 0.19/0.53    (![A:$i,B:$i]:
% 0.19/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.53       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.19/0.53  thf('57', plain,
% 0.19/0.53      (![X4 : $i, X5 : $i]:
% 0.19/0.53         (((k3_subset_1 @ X5 @ (k3_subset_1 @ X5 @ X4)) = (X4))
% 0.19/0.53          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.19/0.53      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.19/0.53  thf('58', plain,
% 0.19/0.53      (![X0 : $i]:
% 0.19/0.53         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.19/0.53      inference('sup-', [status(thm)], ['56', '57'])).
% 0.19/0.53  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.19/0.53  thf('59', plain, (![X0 : $i]: ((k1_subset_1 @ X0) = (k1_xboole_0))),
% 0.19/0.53      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.19/0.53  thf(t22_subset_1, axiom,
% 0.19/0.53    (![A:$i]:
% 0.19/0.53     ( ( k2_subset_1 @ A ) = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ))).
% 0.19/0.53  thf('60', plain,
% 0.19/0.53      (![X6 : $i]:
% 0.19/0.53         ((k2_subset_1 @ X6) = (k3_subset_1 @ X6 @ (k1_subset_1 @ X6)))),
% 0.19/0.53      inference('cnf', [status(esa)], [t22_subset_1])).
% 0.19/0.53  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.19/0.53  thf('61', plain, (![X1 : $i]: ((k2_subset_1 @ X1) = (X1))),
% 0.19/0.53      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.19/0.53  thf('62', plain,
% 0.19/0.53      (![X6 : $i]: ((X6) = (k3_subset_1 @ X6 @ (k1_subset_1 @ X6)))),
% 0.19/0.53      inference('demod', [status(thm)], ['60', '61'])).
% 0.19/0.53  thf('63', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 0.19/0.53      inference('sup+', [status(thm)], ['59', '62'])).
% 0.19/0.53  thf('64', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.19/0.53      inference('demod', [status(thm)], ['58', '63'])).
% 0.19/0.53  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.19/0.53  thf('65', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.19/0.53      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.19/0.53  thf('66', plain,
% 0.19/0.53      ((((u1_struct_0 @ sk_A) = (sk_B_1))) <= (((v4_pre_topc @ sk_B_1 @ sk_A)))),
% 0.19/0.53      inference('sup+', [status(thm)], ['49', '52'])).
% 0.19/0.53  thf('67', plain,
% 0.19/0.53      (((v1_xboole_0 @ sk_B_1)) <= (((v4_pre_topc @ sk_B_1 @ sk_A)))),
% 0.19/0.53      inference('demod', [status(thm)], ['55', '64', '65', '66'])).
% 0.19/0.53  thf('68', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.19/0.53      inference('clc', [status(thm)], ['6', '7'])).
% 0.19/0.53  thf('69', plain, (~ ((v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.19/0.53      inference('sup-', [status(thm)], ['67', '68'])).
% 0.19/0.53  thf('70', plain,
% 0.19/0.53      (((v3_pre_topc @ sk_B_1 @ sk_A)) | ((v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.19/0.53      inference('split', [status(esa)], ['19'])).
% 0.19/0.53  thf('71', plain, (((v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.19/0.53      inference('sat_resolution*', [status(thm)], ['69', '70'])).
% 0.19/0.53  thf('72', plain, (((k2_pre_topc @ sk_A @ sk_B_1) = (u1_struct_0 @ sk_A))),
% 0.19/0.53      inference('simpl_trail', [status(thm)], ['36', '71'])).
% 0.19/0.53  thf('73', plain,
% 0.19/0.53      ((((u1_struct_0 @ sk_A) = (sk_B_1)) | ~ (v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.19/0.53      inference('demod', [status(thm)], ['18', '72'])).
% 0.19/0.53  thf('74', plain,
% 0.19/0.53      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf(t29_tops_1, axiom,
% 0.19/0.53    (![A:$i]:
% 0.19/0.53     ( ( l1_pre_topc @ A ) =>
% 0.19/0.53       ( ![B:$i]:
% 0.19/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.53           ( ( v4_pre_topc @ B @ A ) <=>
% 0.19/0.53             ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.19/0.53  thf('75', plain,
% 0.19/0.53      (![X13 : $i, X14 : $i]:
% 0.19/0.53         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.19/0.53          | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X14) @ X13) @ X14)
% 0.19/0.53          | (v4_pre_topc @ X13 @ X14)
% 0.19/0.53          | ~ (l1_pre_topc @ X14))),
% 0.19/0.53      inference('cnf', [status(esa)], [t29_tops_1])).
% 0.19/0.53  thf('76', plain,
% 0.19/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.19/0.53        | (v4_pre_topc @ sk_B_1 @ sk_A)
% 0.19/0.53        | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A))),
% 0.19/0.53      inference('sup-', [status(thm)], ['74', '75'])).
% 0.19/0.53  thf('77', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('78', plain,
% 0.19/0.53      (((v4_pre_topc @ sk_B_1 @ sk_A)
% 0.19/0.53        | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A))),
% 0.19/0.53      inference('demod', [status(thm)], ['76', '77'])).
% 0.19/0.53  thf('79', plain,
% 0.19/0.53      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf(dt_k3_subset_1, axiom,
% 0.19/0.53    (![A:$i,B:$i]:
% 0.19/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.53       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.19/0.53  thf('80', plain,
% 0.19/0.53      (![X2 : $i, X3 : $i]:
% 0.19/0.53         ((m1_subset_1 @ (k3_subset_1 @ X2 @ X3) @ (k1_zfmisc_1 @ X2))
% 0.19/0.53          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X2)))),
% 0.19/0.53      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.19/0.53  thf('81', plain,
% 0.19/0.53      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.19/0.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['79', '80'])).
% 0.19/0.53  thf('82', plain,
% 0.19/0.53      (![X19 : $i, X20 : $i]:
% 0.19/0.53         (~ (v3_tdlat_3 @ X19)
% 0.19/0.53          | ~ (v4_pre_topc @ X20 @ X19)
% 0.19/0.53          | (v3_pre_topc @ X20 @ X19)
% 0.19/0.53          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.19/0.53          | ~ (l1_pre_topc @ X19)
% 0.19/0.53          | ~ (v2_pre_topc @ X19))),
% 0.19/0.53      inference('cnf', [status(esa)], [t24_tdlat_3])).
% 0.19/0.53  thf('83', plain,
% 0.19/0.53      ((~ (v2_pre_topc @ sk_A)
% 0.19/0.53        | ~ (l1_pre_topc @ sk_A)
% 0.19/0.53        | (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 0.19/0.53        | ~ (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 0.19/0.53        | ~ (v3_tdlat_3 @ sk_A))),
% 0.19/0.53      inference('sup-', [status(thm)], ['81', '82'])).
% 0.19/0.53  thf('84', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('85', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('86', plain, ((v3_tdlat_3 @ sk_A)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('87', plain,
% 0.19/0.53      (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 0.19/0.53        | ~ (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A))),
% 0.19/0.53      inference('demod', [status(thm)], ['83', '84', '85', '86'])).
% 0.19/0.53  thf('88', plain,
% 0.19/0.53      (((v3_pre_topc @ sk_B_1 @ sk_A)) <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.19/0.53      inference('split', [status(esa)], ['19'])).
% 0.19/0.53  thf('89', plain,
% 0.19/0.53      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.19/0.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['79', '80'])).
% 0.19/0.53  thf('90', plain,
% 0.19/0.53      (![X13 : $i, X14 : $i]:
% 0.19/0.53         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.19/0.53          | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X14) @ X13) @ X14)
% 0.19/0.53          | (v4_pre_topc @ X13 @ X14)
% 0.19/0.53          | ~ (l1_pre_topc @ X14))),
% 0.19/0.53      inference('cnf', [status(esa)], [t29_tops_1])).
% 0.19/0.53  thf('91', plain,
% 0.19/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.19/0.53        | (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 0.19/0.53        | ~ (v3_pre_topc @ 
% 0.19/0.53             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.53              (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)) @ 
% 0.19/0.53             sk_A))),
% 0.19/0.53      inference('sup-', [status(thm)], ['89', '90'])).
% 0.19/0.53  thf('92', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('93', plain,
% 0.19/0.53      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('94', plain,
% 0.19/0.53      (![X4 : $i, X5 : $i]:
% 0.19/0.53         (((k3_subset_1 @ X5 @ (k3_subset_1 @ X5 @ X4)) = (X4))
% 0.19/0.53          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.19/0.53      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.19/0.53  thf('95', plain,
% 0.19/0.53      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.53         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)) = (sk_B_1))),
% 0.19/0.53      inference('sup-', [status(thm)], ['93', '94'])).
% 0.19/0.53  thf('96', plain,
% 0.19/0.53      (((v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 0.19/0.53        | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.19/0.53      inference('demod', [status(thm)], ['91', '92', '95'])).
% 0.19/0.53  thf('97', plain,
% 0.19/0.53      (((v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A))
% 0.19/0.53         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['88', '96'])).
% 0.19/0.53  thf('98', plain, (((v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.19/0.53      inference('sat_resolution*', [status(thm)], ['69', '70'])).
% 0.19/0.53  thf('99', plain,
% 0.19/0.53      ((v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)),
% 0.19/0.53      inference('simpl_trail', [status(thm)], ['97', '98'])).
% 0.19/0.53  thf('100', plain,
% 0.19/0.53      ((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)),
% 0.19/0.53      inference('demod', [status(thm)], ['87', '99'])).
% 0.19/0.53  thf('101', plain, ((v4_pre_topc @ sk_B_1 @ sk_A)),
% 0.19/0.53      inference('demod', [status(thm)], ['78', '100'])).
% 0.19/0.53  thf('102', plain, (((u1_struct_0 @ sk_A) = (sk_B_1))),
% 0.19/0.53      inference('demod', [status(thm)], ['73', '101'])).
% 0.19/0.53  thf('103', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.19/0.53      inference('demod', [status(thm)], ['58', '63'])).
% 0.19/0.53  thf('104', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.19/0.53      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.19/0.53  thf('105', plain, (((u1_struct_0 @ sk_A) = (sk_B_1))),
% 0.19/0.53      inference('demod', [status(thm)], ['73', '101'])).
% 0.19/0.53  thf('106', plain, ((v1_xboole_0 @ sk_B_1)),
% 0.19/0.53      inference('demod', [status(thm)], ['13', '102', '103', '104', '105'])).
% 0.19/0.53  thf('107', plain, ($false), inference('demod', [status(thm)], ['8', '106'])).
% 0.19/0.53  
% 0.19/0.53  % SZS output end Refutation
% 0.19/0.53  
% 0.19/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
