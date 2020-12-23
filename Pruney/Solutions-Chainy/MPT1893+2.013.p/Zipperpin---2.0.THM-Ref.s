%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MUvZmR5lF4

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:35 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  156 ( 472 expanded)
%              Number of leaves         :   35 ( 153 expanded)
%              Depth                    :   18
%              Number of atoms          : 1070 (5914 expanded)
%              Number of equality atoms :   44 ( 111 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

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

thf(fc1_tex_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_subset_1 @ B @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) )
     => ~ ( v1_xboole_0 @ ( k3_subset_1 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X22: $i,X23: $i] :
      ( ( v1_xboole_0 @ X22 )
      | ~ ( v1_subset_1 @ X23 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X22 ) )
      | ~ ( v1_xboole_0 @ ( k3_subset_1 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[fc1_tex_2])).

thf('2',plain,
    ( ~ ( v1_xboole_0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
    | ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k3_subset_1 @ X3 @ X4 )
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('5',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ~ ( v1_xboole_0 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc4_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ~ ( v1_subset_1 @ B @ A ) ) ) )).

thf('9',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( v1_subset_1 @ X8 @ X9 )
      | ~ ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc4_subset_1])).

thf('10',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ~ ( v1_xboole_0 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['7','12'])).

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
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v4_pre_topc @ X16 @ X17 )
      | ( ( k2_pre_topc @ X17 @ X16 )
        = X16 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
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
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( v1_tops_1 @ X26 @ X27 )
      | ~ ( v3_tex_2 @ X26 @ X27 )
      | ~ ( v3_pre_topc @ X26 @ X27 )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
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
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v1_tops_1 @ X20 @ X21 )
      | ( ( k2_pre_topc @ X21 @ X20 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
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
    ! [X24: $i,X25: $i] :
      ( ~ ( v3_tdlat_3 @ X24 )
      | ~ ( v4_pre_topc @ X25 @ X24 )
      | ( v3_pre_topc @ X25 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 ) ) ),
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

thf('54',plain,(
    ~ ( v1_xboole_0 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['7','12'])).

thf('55',plain,
    ( ~ ( v1_xboole_0 @ ( k4_xboole_0 @ sk_B_1 @ sk_B_1 ) )
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
    ! [X5: $i,X6: $i] :
      ( ( ( k3_subset_1 @ X6 @ ( k3_subset_1 @ X6 @ X5 ) )
        = X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('60',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k3_subset_1 @ X3 @ X4 )
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('62',plain,(
    ! [X2: $i] :
      ( ( k4_xboole_0 @ X2 @ k1_xboole_0 )
      = X2 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['58','63'])).

thf('65',plain,(
    ! [X2: $i] :
      ( ( k4_xboole_0 @ X2 @ k1_xboole_0 )
      = X2 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('67',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('68',plain,(
    ! [X10: $i,X12: $i] :
      ( ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('69',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k3_subset_1 @ X3 @ X4 )
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['64','71'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('73',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('74',plain,(
    ~ ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['55','72','73'])).

thf('75',plain,
    ( ( v3_pre_topc @ sk_B_1 @ sk_A )
    | ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['19'])).

thf('76',plain,(
    v3_pre_topc @ sk_B_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['36','76'])).

thf('78',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_1 )
    | ~ ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['18','77'])).

thf('79',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t29_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('80',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X19 ) @ X18 ) @ X19 )
      | ( v4_pre_topc @ X18 @ X19 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t29_tops_1])).

thf('81',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('84',plain,
    ( ( v4_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( v3_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['81','82','83'])).

thf('85',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_subset_1 @ X6 @ ( k3_subset_1 @ X6 @ X5 ) )
        = X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('87',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('89',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
    = sk_B_1 ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('91',plain,(
    ! [X10: $i,X12: $i] :
      ( ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k3_subset_1 @ X3 @ X4 )
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
    = sk_B_1 ),
    inference(demod,[status(thm)],['89','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('97',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X19 ) @ X18 ) @ X19 )
      | ( v4_pre_topc @ X18 @ X19 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t29_tops_1])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) @ X0 )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) @ X0 )
      | ~ ( v3_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,
    ( ~ ( v3_pre_topc @ sk_B_1 @ sk_A )
    | ( v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['95','100'])).

thf('102',plain,
    ( ( v3_pre_topc @ sk_B_1 @ sk_A )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['19'])).

thf('103',plain,(
    v3_pre_topc @ sk_B_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['74','75'])).

thf('104',plain,(
    v3_pre_topc @ sk_B_1 @ sk_A ),
    inference(simpl_trail,[status(thm)],['102','103'])).

thf('105',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['101','104','105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('108',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v3_tdlat_3 @ X24 )
      | ~ ( v4_pre_topc @ X25 @ X24 )
      | ( v3_pre_topc @ X25 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t24_tdlat_3])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) @ X0 )
      | ~ ( v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) @ X0 )
      | ~ ( v3_tdlat_3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,
    ( ~ ( v3_tdlat_3 @ sk_A )
    | ( v3_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['106','109'])).

thf('111',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    v3_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['110','111','112','113'])).

thf('115',plain,(
    v4_pre_topc @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['84','114'])).

thf('116',plain,
    ( ( u1_struct_0 @ sk_A )
    = sk_B_1 ),
    inference(demod,[status(thm)],['78','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['64','71'])).

thf('118',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('119',plain,(
    $false ),
    inference(demod,[status(thm)],['13','116','117','118'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MUvZmR5lF4
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:46:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.36/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.57  % Solved by: fo/fo7.sh
% 0.36/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.57  % done 384 iterations in 0.111s
% 0.36/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.57  % SZS output start Refutation
% 0.36/0.57  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.36/0.57  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.36/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.57  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.36/0.57  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.36/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.57  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.36/0.57  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.36/0.57  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.36/0.57  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.36/0.57  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.36/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.57  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.36/0.57  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.36/0.57  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.36/0.57  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.36/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.57  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.36/0.57  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.36/0.57  thf(t61_tex_2, conjecture,
% 0.36/0.57    (![A:$i]:
% 0.36/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.36/0.57         ( l1_pre_topc @ A ) ) =>
% 0.36/0.57       ( ![B:$i]:
% 0.36/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.57           ( ~( ( ( v3_pre_topc @ B @ A ) | ( v4_pre_topc @ B @ A ) ) & 
% 0.36/0.57                ( v3_tex_2 @ B @ A ) & 
% 0.36/0.57                ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.36/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.57    (~( ![A:$i]:
% 0.36/0.57        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.36/0.57            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.57          ( ![B:$i]:
% 0.36/0.57            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.57              ( ~( ( ( v3_pre_topc @ B @ A ) | ( v4_pre_topc @ B @ A ) ) & 
% 0.36/0.57                   ( v3_tex_2 @ B @ A ) & 
% 0.36/0.57                   ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )),
% 0.36/0.57    inference('cnf.neg', [status(esa)], [t61_tex_2])).
% 0.36/0.57  thf('0', plain,
% 0.36/0.57      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf(fc1_tex_2, axiom,
% 0.36/0.57    (![A:$i,B:$i]:
% 0.36/0.57     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_subset_1 @ B @ A ) & 
% 0.36/0.57         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.36/0.57       ( ~( v1_xboole_0 @ ( k3_subset_1 @ A @ B ) ) ) ))).
% 0.36/0.57  thf('1', plain,
% 0.36/0.57      (![X22 : $i, X23 : $i]:
% 0.36/0.57         ((v1_xboole_0 @ X22)
% 0.36/0.57          | ~ (v1_subset_1 @ X23 @ X22)
% 0.36/0.57          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X22))
% 0.36/0.57          | ~ (v1_xboole_0 @ (k3_subset_1 @ X22 @ X23)))),
% 0.36/0.57      inference('cnf', [status(esa)], [fc1_tex_2])).
% 0.36/0.57  thf('2', plain,
% 0.36/0.57      ((~ (v1_xboole_0 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))
% 0.36/0.57        | ~ (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.36/0.57        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.57      inference('sup-', [status(thm)], ['0', '1'])).
% 0.36/0.57  thf('3', plain,
% 0.36/0.57      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf(d5_subset_1, axiom,
% 0.36/0.57    (![A:$i,B:$i]:
% 0.36/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.36/0.57       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.36/0.57  thf('4', plain,
% 0.36/0.57      (![X3 : $i, X4 : $i]:
% 0.36/0.57         (((k3_subset_1 @ X3 @ X4) = (k4_xboole_0 @ X3 @ X4))
% 0.36/0.57          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X3)))),
% 0.36/0.57      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.36/0.57  thf('5', plain,
% 0.36/0.57      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)
% 0.36/0.57         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1))),
% 0.36/0.57      inference('sup-', [status(thm)], ['3', '4'])).
% 0.36/0.57  thf('6', plain, ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('7', plain,
% 0.36/0.57      ((~ (v1_xboole_0 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1))
% 0.36/0.57        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.57      inference('demod', [status(thm)], ['2', '5', '6'])).
% 0.36/0.57  thf('8', plain,
% 0.36/0.57      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf(cc4_subset_1, axiom,
% 0.36/0.57    (![A:$i]:
% 0.36/0.57     ( ( v1_xboole_0 @ A ) =>
% 0.36/0.57       ( ![B:$i]:
% 0.36/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.36/0.57           ( ~( v1_subset_1 @ B @ A ) ) ) ) ))).
% 0.36/0.57  thf('9', plain,
% 0.36/0.57      (![X8 : $i, X9 : $i]:
% 0.36/0.57         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 0.36/0.57          | ~ (v1_subset_1 @ X8 @ X9)
% 0.36/0.57          | ~ (v1_xboole_0 @ X9))),
% 0.36/0.57      inference('cnf', [status(esa)], [cc4_subset_1])).
% 0.36/0.57  thf('10', plain,
% 0.36/0.57      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.36/0.57        | ~ (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.57      inference('sup-', [status(thm)], ['8', '9'])).
% 0.36/0.57  thf('11', plain, ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('12', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.36/0.57      inference('demod', [status(thm)], ['10', '11'])).
% 0.36/0.57  thf('13', plain,
% 0.36/0.57      (~ (v1_xboole_0 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1))),
% 0.36/0.57      inference('clc', [status(thm)], ['7', '12'])).
% 0.36/0.57  thf('14', plain,
% 0.36/0.57      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf(t52_pre_topc, axiom,
% 0.36/0.57    (![A:$i]:
% 0.36/0.57     ( ( l1_pre_topc @ A ) =>
% 0.36/0.57       ( ![B:$i]:
% 0.36/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.57           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.36/0.57             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.36/0.57               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.36/0.57  thf('15', plain,
% 0.36/0.57      (![X16 : $i, X17 : $i]:
% 0.36/0.57         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.36/0.57          | ~ (v4_pre_topc @ X16 @ X17)
% 0.36/0.57          | ((k2_pre_topc @ X17 @ X16) = (X16))
% 0.36/0.57          | ~ (l1_pre_topc @ X17))),
% 0.36/0.57      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.36/0.57  thf('16', plain,
% 0.36/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.36/0.57        | ((k2_pre_topc @ sk_A @ sk_B_1) = (sk_B_1))
% 0.36/0.57        | ~ (v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.36/0.57      inference('sup-', [status(thm)], ['14', '15'])).
% 0.36/0.57  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('18', plain,
% 0.36/0.57      ((((k2_pre_topc @ sk_A @ sk_B_1) = (sk_B_1))
% 0.36/0.57        | ~ (v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.36/0.57      inference('demod', [status(thm)], ['16', '17'])).
% 0.36/0.57  thf('19', plain,
% 0.36/0.57      (((v3_pre_topc @ sk_B_1 @ sk_A) | (v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('20', plain,
% 0.36/0.57      (((v3_pre_topc @ sk_B_1 @ sk_A)) <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.36/0.57      inference('split', [status(esa)], ['19'])).
% 0.36/0.57  thf('21', plain,
% 0.36/0.57      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf(t47_tex_2, axiom,
% 0.36/0.57    (![A:$i]:
% 0.36/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.57       ( ![B:$i]:
% 0.36/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.57           ( ( ( v3_pre_topc @ B @ A ) & ( v3_tex_2 @ B @ A ) ) =>
% 0.36/0.57             ( v1_tops_1 @ B @ A ) ) ) ) ))).
% 0.36/0.57  thf('22', plain,
% 0.36/0.57      (![X26 : $i, X27 : $i]:
% 0.36/0.57         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.36/0.57          | (v1_tops_1 @ X26 @ X27)
% 0.36/0.57          | ~ (v3_tex_2 @ X26 @ X27)
% 0.36/0.57          | ~ (v3_pre_topc @ X26 @ X27)
% 0.36/0.57          | ~ (l1_pre_topc @ X27)
% 0.36/0.57          | ~ (v2_pre_topc @ X27)
% 0.36/0.57          | (v2_struct_0 @ X27))),
% 0.36/0.57      inference('cnf', [status(esa)], [t47_tex_2])).
% 0.36/0.57  thf('23', plain,
% 0.36/0.57      (((v2_struct_0 @ sk_A)
% 0.36/0.57        | ~ (v2_pre_topc @ sk_A)
% 0.36/0.57        | ~ (l1_pre_topc @ sk_A)
% 0.36/0.57        | ~ (v3_pre_topc @ sk_B_1 @ sk_A)
% 0.36/0.57        | ~ (v3_tex_2 @ sk_B_1 @ sk_A)
% 0.36/0.57        | (v1_tops_1 @ sk_B_1 @ sk_A))),
% 0.36/0.57      inference('sup-', [status(thm)], ['21', '22'])).
% 0.36/0.57  thf('24', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('26', plain, ((v3_tex_2 @ sk_B_1 @ sk_A)),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('27', plain,
% 0.36/0.57      (((v2_struct_0 @ sk_A)
% 0.36/0.57        | ~ (v3_pre_topc @ sk_B_1 @ sk_A)
% 0.36/0.57        | (v1_tops_1 @ sk_B_1 @ sk_A))),
% 0.36/0.57      inference('demod', [status(thm)], ['23', '24', '25', '26'])).
% 0.36/0.57  thf('28', plain, (~ (v2_struct_0 @ sk_A)),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('29', plain,
% 0.36/0.57      (((v1_tops_1 @ sk_B_1 @ sk_A) | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.36/0.57      inference('clc', [status(thm)], ['27', '28'])).
% 0.36/0.57  thf('30', plain,
% 0.36/0.57      (((v1_tops_1 @ sk_B_1 @ sk_A)) <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.36/0.57      inference('sup-', [status(thm)], ['20', '29'])).
% 0.36/0.57  thf('31', plain,
% 0.36/0.57      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf(d2_tops_3, axiom,
% 0.36/0.57    (![A:$i]:
% 0.36/0.57     ( ( l1_pre_topc @ A ) =>
% 0.36/0.57       ( ![B:$i]:
% 0.36/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.57           ( ( v1_tops_1 @ B @ A ) <=>
% 0.36/0.57             ( ( k2_pre_topc @ A @ B ) = ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.36/0.57  thf('32', plain,
% 0.36/0.57      (![X20 : $i, X21 : $i]:
% 0.36/0.57         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.36/0.57          | ~ (v1_tops_1 @ X20 @ X21)
% 0.36/0.57          | ((k2_pre_topc @ X21 @ X20) = (u1_struct_0 @ X21))
% 0.36/0.57          | ~ (l1_pre_topc @ X21))),
% 0.36/0.57      inference('cnf', [status(esa)], [d2_tops_3])).
% 0.36/0.57  thf('33', plain,
% 0.36/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.36/0.57        | ((k2_pre_topc @ sk_A @ sk_B_1) = (u1_struct_0 @ sk_A))
% 0.36/0.57        | ~ (v1_tops_1 @ sk_B_1 @ sk_A))),
% 0.36/0.57      inference('sup-', [status(thm)], ['31', '32'])).
% 0.36/0.57  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('35', plain,
% 0.36/0.57      ((((k2_pre_topc @ sk_A @ sk_B_1) = (u1_struct_0 @ sk_A))
% 0.36/0.57        | ~ (v1_tops_1 @ sk_B_1 @ sk_A))),
% 0.36/0.57      inference('demod', [status(thm)], ['33', '34'])).
% 0.36/0.57  thf('36', plain,
% 0.36/0.57      ((((k2_pre_topc @ sk_A @ sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.36/0.57         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.36/0.57      inference('sup-', [status(thm)], ['30', '35'])).
% 0.36/0.57  thf('37', plain,
% 0.36/0.57      (((v4_pre_topc @ sk_B_1 @ sk_A)) <= (((v4_pre_topc @ sk_B_1 @ sk_A)))),
% 0.36/0.57      inference('split', [status(esa)], ['19'])).
% 0.36/0.57  thf('38', plain,
% 0.36/0.57      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf(t24_tdlat_3, axiom,
% 0.36/0.57    (![A:$i]:
% 0.36/0.57     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.57       ( ( v3_tdlat_3 @ A ) <=>
% 0.36/0.57         ( ![B:$i]:
% 0.36/0.57           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.57             ( ( v4_pre_topc @ B @ A ) => ( v3_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.36/0.57  thf('39', plain,
% 0.36/0.57      (![X24 : $i, X25 : $i]:
% 0.36/0.57         (~ (v3_tdlat_3 @ X24)
% 0.36/0.57          | ~ (v4_pre_topc @ X25 @ X24)
% 0.36/0.57          | (v3_pre_topc @ X25 @ X24)
% 0.36/0.57          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.36/0.57          | ~ (l1_pre_topc @ X24)
% 0.36/0.57          | ~ (v2_pre_topc @ X24))),
% 0.36/0.57      inference('cnf', [status(esa)], [t24_tdlat_3])).
% 0.36/0.57  thf('40', plain,
% 0.36/0.57      ((~ (v2_pre_topc @ sk_A)
% 0.36/0.57        | ~ (l1_pre_topc @ sk_A)
% 0.36/0.57        | (v3_pre_topc @ sk_B_1 @ sk_A)
% 0.36/0.57        | ~ (v4_pre_topc @ sk_B_1 @ sk_A)
% 0.36/0.57        | ~ (v3_tdlat_3 @ sk_A))),
% 0.36/0.57      inference('sup-', [status(thm)], ['38', '39'])).
% 0.36/0.57  thf('41', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('43', plain, ((v3_tdlat_3 @ sk_A)),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('44', plain,
% 0.36/0.57      (((v3_pre_topc @ sk_B_1 @ sk_A) | ~ (v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.36/0.57      inference('demod', [status(thm)], ['40', '41', '42', '43'])).
% 0.36/0.57  thf('45', plain,
% 0.36/0.57      (((v3_pre_topc @ sk_B_1 @ sk_A)) <= (((v4_pre_topc @ sk_B_1 @ sk_A)))),
% 0.36/0.57      inference('sup-', [status(thm)], ['37', '44'])).
% 0.36/0.57  thf('46', plain,
% 0.36/0.57      (((v1_tops_1 @ sk_B_1 @ sk_A) | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.36/0.57      inference('clc', [status(thm)], ['27', '28'])).
% 0.36/0.57  thf('47', plain,
% 0.36/0.57      (((v1_tops_1 @ sk_B_1 @ sk_A)) <= (((v4_pre_topc @ sk_B_1 @ sk_A)))),
% 0.36/0.57      inference('sup-', [status(thm)], ['45', '46'])).
% 0.36/0.57  thf('48', plain,
% 0.36/0.57      ((((k2_pre_topc @ sk_A @ sk_B_1) = (u1_struct_0 @ sk_A))
% 0.36/0.57        | ~ (v1_tops_1 @ sk_B_1 @ sk_A))),
% 0.36/0.57      inference('demod', [status(thm)], ['33', '34'])).
% 0.36/0.57  thf('49', plain,
% 0.36/0.57      ((((k2_pre_topc @ sk_A @ sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.36/0.57         <= (((v4_pre_topc @ sk_B_1 @ sk_A)))),
% 0.36/0.57      inference('sup-', [status(thm)], ['47', '48'])).
% 0.36/0.57  thf('50', plain,
% 0.36/0.57      (((v4_pre_topc @ sk_B_1 @ sk_A)) <= (((v4_pre_topc @ sk_B_1 @ sk_A)))),
% 0.36/0.57      inference('split', [status(esa)], ['19'])).
% 0.36/0.57  thf('51', plain,
% 0.36/0.57      ((((k2_pre_topc @ sk_A @ sk_B_1) = (sk_B_1))
% 0.36/0.57        | ~ (v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.36/0.57      inference('demod', [status(thm)], ['16', '17'])).
% 0.36/0.57  thf('52', plain,
% 0.36/0.57      ((((k2_pre_topc @ sk_A @ sk_B_1) = (sk_B_1)))
% 0.36/0.57         <= (((v4_pre_topc @ sk_B_1 @ sk_A)))),
% 0.36/0.57      inference('sup-', [status(thm)], ['50', '51'])).
% 0.36/0.57  thf('53', plain,
% 0.36/0.57      ((((u1_struct_0 @ sk_A) = (sk_B_1))) <= (((v4_pre_topc @ sk_B_1 @ sk_A)))),
% 0.36/0.57      inference('sup+', [status(thm)], ['49', '52'])).
% 0.36/0.57  thf('54', plain,
% 0.36/0.57      (~ (v1_xboole_0 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1))),
% 0.36/0.57      inference('clc', [status(thm)], ['7', '12'])).
% 0.36/0.57  thf('55', plain,
% 0.36/0.57      ((~ (v1_xboole_0 @ (k4_xboole_0 @ sk_B_1 @ sk_B_1)))
% 0.36/0.57         <= (((v4_pre_topc @ sk_B_1 @ sk_A)))),
% 0.36/0.57      inference('sup-', [status(thm)], ['53', '54'])).
% 0.36/0.57  thf(t4_subset_1, axiom,
% 0.36/0.57    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.36/0.57  thf('56', plain,
% 0.36/0.57      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 0.36/0.57      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.36/0.57  thf(involutiveness_k3_subset_1, axiom,
% 0.36/0.57    (![A:$i,B:$i]:
% 0.36/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.36/0.57       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.36/0.57  thf('57', plain,
% 0.36/0.57      (![X5 : $i, X6 : $i]:
% 0.36/0.57         (((k3_subset_1 @ X6 @ (k3_subset_1 @ X6 @ X5)) = (X5))
% 0.36/0.57          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.36/0.57      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.36/0.57  thf('58', plain,
% 0.36/0.57      (![X0 : $i]:
% 0.36/0.57         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.36/0.57      inference('sup-', [status(thm)], ['56', '57'])).
% 0.36/0.57  thf('59', plain,
% 0.36/0.57      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 0.36/0.57      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.36/0.57  thf('60', plain,
% 0.36/0.57      (![X3 : $i, X4 : $i]:
% 0.36/0.57         (((k3_subset_1 @ X3 @ X4) = (k4_xboole_0 @ X3 @ X4))
% 0.36/0.57          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X3)))),
% 0.36/0.57      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.36/0.57  thf('61', plain,
% 0.36/0.57      (![X0 : $i]:
% 0.36/0.57         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.36/0.57      inference('sup-', [status(thm)], ['59', '60'])).
% 0.36/0.57  thf(t3_boole, axiom,
% 0.36/0.57    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.36/0.57  thf('62', plain, (![X2 : $i]: ((k4_xboole_0 @ X2 @ k1_xboole_0) = (X2))),
% 0.36/0.57      inference('cnf', [status(esa)], [t3_boole])).
% 0.36/0.57  thf('63', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.36/0.57      inference('demod', [status(thm)], ['61', '62'])).
% 0.36/0.57  thf('64', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.36/0.57      inference('demod', [status(thm)], ['58', '63'])).
% 0.36/0.57  thf('65', plain, (![X2 : $i]: ((k4_xboole_0 @ X2 @ k1_xboole_0) = (X2))),
% 0.36/0.57      inference('cnf', [status(esa)], [t3_boole])).
% 0.36/0.57  thf(t36_xboole_1, axiom,
% 0.36/0.57    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.36/0.57  thf('66', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 0.36/0.57      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.36/0.57  thf('67', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.36/0.57      inference('sup+', [status(thm)], ['65', '66'])).
% 0.36/0.57  thf(t3_subset, axiom,
% 0.36/0.57    (![A:$i,B:$i]:
% 0.36/0.57     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.36/0.57  thf('68', plain,
% 0.36/0.57      (![X10 : $i, X12 : $i]:
% 0.36/0.57         ((m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X12)) | ~ (r1_tarski @ X10 @ X12))),
% 0.36/0.57      inference('cnf', [status(esa)], [t3_subset])).
% 0.36/0.57  thf('69', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.36/0.57      inference('sup-', [status(thm)], ['67', '68'])).
% 0.36/0.57  thf('70', plain,
% 0.36/0.57      (![X3 : $i, X4 : $i]:
% 0.36/0.57         (((k3_subset_1 @ X3 @ X4) = (k4_xboole_0 @ X3 @ X4))
% 0.36/0.57          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X3)))),
% 0.36/0.57      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.36/0.57  thf('71', plain,
% 0.36/0.57      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.36/0.57      inference('sup-', [status(thm)], ['69', '70'])).
% 0.36/0.57  thf('72', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.36/0.57      inference('demod', [status(thm)], ['64', '71'])).
% 0.36/0.57  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.36/0.57  thf('73', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.36/0.57      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.36/0.57  thf('74', plain, (~ ((v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.36/0.57      inference('demod', [status(thm)], ['55', '72', '73'])).
% 0.36/0.57  thf('75', plain,
% 0.36/0.57      (((v3_pre_topc @ sk_B_1 @ sk_A)) | ((v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.36/0.57      inference('split', [status(esa)], ['19'])).
% 0.36/0.57  thf('76', plain, (((v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.36/0.57      inference('sat_resolution*', [status(thm)], ['74', '75'])).
% 0.36/0.57  thf('77', plain, (((k2_pre_topc @ sk_A @ sk_B_1) = (u1_struct_0 @ sk_A))),
% 0.36/0.57      inference('simpl_trail', [status(thm)], ['36', '76'])).
% 0.36/0.57  thf('78', plain,
% 0.36/0.57      ((((u1_struct_0 @ sk_A) = (sk_B_1)) | ~ (v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.36/0.57      inference('demod', [status(thm)], ['18', '77'])).
% 0.36/0.57  thf('79', plain,
% 0.36/0.57      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf(t29_tops_1, axiom,
% 0.36/0.57    (![A:$i]:
% 0.36/0.57     ( ( l1_pre_topc @ A ) =>
% 0.36/0.57       ( ![B:$i]:
% 0.36/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.57           ( ( v4_pre_topc @ B @ A ) <=>
% 0.36/0.57             ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.36/0.57  thf('80', plain,
% 0.36/0.57      (![X18 : $i, X19 : $i]:
% 0.36/0.57         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.36/0.57          | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X19) @ X18) @ X19)
% 0.36/0.57          | (v4_pre_topc @ X18 @ X19)
% 0.36/0.57          | ~ (l1_pre_topc @ X19))),
% 0.36/0.57      inference('cnf', [status(esa)], [t29_tops_1])).
% 0.36/0.57  thf('81', plain,
% 0.36/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.36/0.57        | (v4_pre_topc @ sk_B_1 @ sk_A)
% 0.36/0.57        | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A))),
% 0.36/0.57      inference('sup-', [status(thm)], ['79', '80'])).
% 0.36/0.57  thf('82', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('83', plain,
% 0.36/0.57      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)
% 0.36/0.57         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1))),
% 0.36/0.57      inference('sup-', [status(thm)], ['3', '4'])).
% 0.36/0.57  thf('84', plain,
% 0.36/0.57      (((v4_pre_topc @ sk_B_1 @ sk_A)
% 0.36/0.57        | ~ (v3_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A))),
% 0.36/0.57      inference('demod', [status(thm)], ['81', '82', '83'])).
% 0.36/0.57  thf('85', plain,
% 0.36/0.57      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('86', plain,
% 0.36/0.57      (![X5 : $i, X6 : $i]:
% 0.36/0.57         (((k3_subset_1 @ X6 @ (k3_subset_1 @ X6 @ X5)) = (X5))
% 0.36/0.57          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.36/0.57      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.36/0.57  thf('87', plain,
% 0.36/0.57      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.57         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)) = (sk_B_1))),
% 0.36/0.57      inference('sup-', [status(thm)], ['85', '86'])).
% 0.36/0.57  thf('88', plain,
% 0.36/0.57      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)
% 0.36/0.57         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1))),
% 0.36/0.57      inference('sup-', [status(thm)], ['3', '4'])).
% 0.36/0.57  thf('89', plain,
% 0.36/0.57      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.57         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1)) = (sk_B_1))),
% 0.36/0.57      inference('demod', [status(thm)], ['87', '88'])).
% 0.36/0.57  thf('90', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 0.36/0.57      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.36/0.57  thf('91', plain,
% 0.36/0.57      (![X10 : $i, X12 : $i]:
% 0.36/0.57         ((m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X12)) | ~ (r1_tarski @ X10 @ X12))),
% 0.36/0.57      inference('cnf', [status(esa)], [t3_subset])).
% 0.36/0.57  thf('92', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i]:
% 0.36/0.57         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.36/0.57      inference('sup-', [status(thm)], ['90', '91'])).
% 0.36/0.57  thf('93', plain,
% 0.36/0.57      (![X3 : $i, X4 : $i]:
% 0.36/0.57         (((k3_subset_1 @ X3 @ X4) = (k4_xboole_0 @ X3 @ X4))
% 0.36/0.57          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X3)))),
% 0.36/0.57      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.36/0.57  thf('94', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i]:
% 0.36/0.57         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.36/0.57           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.36/0.57      inference('sup-', [status(thm)], ['92', '93'])).
% 0.36/0.57  thf('95', plain,
% 0.36/0.57      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.57         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1)) = (sk_B_1))),
% 0.36/0.57      inference('demod', [status(thm)], ['89', '94'])).
% 0.36/0.57  thf('96', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i]:
% 0.36/0.57         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.36/0.57      inference('sup-', [status(thm)], ['90', '91'])).
% 0.36/0.57  thf('97', plain,
% 0.36/0.57      (![X18 : $i, X19 : $i]:
% 0.36/0.57         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.36/0.57          | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X19) @ X18) @ X19)
% 0.36/0.57          | (v4_pre_topc @ X18 @ X19)
% 0.36/0.57          | ~ (l1_pre_topc @ X19))),
% 0.36/0.57      inference('cnf', [status(esa)], [t29_tops_1])).
% 0.36/0.57  thf('98', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i]:
% 0.36/0.57         (~ (l1_pre_topc @ X0)
% 0.36/0.57          | (v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1) @ X0)
% 0.36/0.57          | ~ (v3_pre_topc @ 
% 0.36/0.57               (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.36/0.57                (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1)) @ 
% 0.36/0.57               X0))),
% 0.36/0.57      inference('sup-', [status(thm)], ['96', '97'])).
% 0.36/0.57  thf('99', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i]:
% 0.36/0.57         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.36/0.57           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.36/0.57      inference('sup-', [status(thm)], ['92', '93'])).
% 0.36/0.57  thf('100', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i]:
% 0.36/0.57         (~ (l1_pre_topc @ X0)
% 0.36/0.57          | (v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1) @ X0)
% 0.36/0.57          | ~ (v3_pre_topc @ 
% 0.36/0.57               (k4_xboole_0 @ (u1_struct_0 @ X0) @ 
% 0.36/0.57                (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1)) @ 
% 0.36/0.57               X0))),
% 0.36/0.57      inference('demod', [status(thm)], ['98', '99'])).
% 0.36/0.57  thf('101', plain,
% 0.36/0.57      ((~ (v3_pre_topc @ sk_B_1 @ sk_A)
% 0.36/0.57        | (v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 0.36/0.57        | ~ (l1_pre_topc @ sk_A))),
% 0.36/0.57      inference('sup-', [status(thm)], ['95', '100'])).
% 0.36/0.57  thf('102', plain,
% 0.36/0.57      (((v3_pre_topc @ sk_B_1 @ sk_A)) <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.36/0.57      inference('split', [status(esa)], ['19'])).
% 0.36/0.57  thf('103', plain, (((v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.36/0.57      inference('sat_resolution*', [status(thm)], ['74', '75'])).
% 0.36/0.57  thf('104', plain, ((v3_pre_topc @ sk_B_1 @ sk_A)),
% 0.36/0.57      inference('simpl_trail', [status(thm)], ['102', '103'])).
% 0.36/0.57  thf('105', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('106', plain,
% 0.36/0.57      ((v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)),
% 0.36/0.57      inference('demod', [status(thm)], ['101', '104', '105'])).
% 0.36/0.57  thf('107', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i]:
% 0.36/0.57         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.36/0.57      inference('sup-', [status(thm)], ['90', '91'])).
% 0.36/0.57  thf('108', plain,
% 0.36/0.57      (![X24 : $i, X25 : $i]:
% 0.36/0.57         (~ (v3_tdlat_3 @ X24)
% 0.36/0.57          | ~ (v4_pre_topc @ X25 @ X24)
% 0.36/0.57          | (v3_pre_topc @ X25 @ X24)
% 0.36/0.57          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.36/0.57          | ~ (l1_pre_topc @ X24)
% 0.36/0.57          | ~ (v2_pre_topc @ X24))),
% 0.36/0.57      inference('cnf', [status(esa)], [t24_tdlat_3])).
% 0.36/0.57  thf('109', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i]:
% 0.36/0.57         (~ (v2_pre_topc @ X0)
% 0.36/0.57          | ~ (l1_pre_topc @ X0)
% 0.36/0.57          | (v3_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1) @ X0)
% 0.36/0.57          | ~ (v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1) @ X0)
% 0.36/0.57          | ~ (v3_tdlat_3 @ X0))),
% 0.36/0.57      inference('sup-', [status(thm)], ['107', '108'])).
% 0.36/0.57  thf('110', plain,
% 0.36/0.57      ((~ (v3_tdlat_3 @ sk_A)
% 0.36/0.57        | (v3_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 0.36/0.57        | ~ (l1_pre_topc @ sk_A)
% 0.36/0.57        | ~ (v2_pre_topc @ sk_A))),
% 0.36/0.57      inference('sup-', [status(thm)], ['106', '109'])).
% 0.36/0.57  thf('111', plain, ((v3_tdlat_3 @ sk_A)),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('112', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('113', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('114', plain,
% 0.36/0.57      ((v3_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)),
% 0.36/0.57      inference('demod', [status(thm)], ['110', '111', '112', '113'])).
% 0.36/0.57  thf('115', plain, ((v4_pre_topc @ sk_B_1 @ sk_A)),
% 0.36/0.57      inference('demod', [status(thm)], ['84', '114'])).
% 0.36/0.57  thf('116', plain, (((u1_struct_0 @ sk_A) = (sk_B_1))),
% 0.36/0.57      inference('demod', [status(thm)], ['78', '115'])).
% 0.36/0.57  thf('117', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.36/0.57      inference('demod', [status(thm)], ['64', '71'])).
% 0.36/0.57  thf('118', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.36/0.57      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.36/0.57  thf('119', plain, ($false),
% 0.36/0.57      inference('demod', [status(thm)], ['13', '116', '117', '118'])).
% 0.36/0.57  
% 0.36/0.57  % SZS output end Refutation
% 0.36/0.57  
% 0.36/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
