%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.O2sBYsVmBo

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:34 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  172 ( 510 expanded)
%              Number of leaves         :   39 ( 169 expanded)
%              Depth                    :   18
%              Number of atoms          : 1151 (5716 expanded)
%              Number of equality atoms :   50 ( 157 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

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
    ! [X24: $i,X25: $i] :
      ( ( v1_xboole_0 @ X24 )
      | ~ ( v1_subset_1 @ X25 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X24 ) )
      | ~ ( v1_xboole_0 @ ( k3_subset_1 @ X24 @ X25 ) ) ) ),
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
    ! [X4: $i,X5: $i] :
      ( ( ( k3_subset_1 @ X4 @ X5 )
        = ( k4_xboole_0 @ X4 @ X5 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
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
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( v1_subset_1 @ X10 @ X11 )
      | ~ ( v1_xboole_0 @ X11 ) ) ),
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
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v4_pre_topc @ X18 @ X19 )
      | ( ( k2_pre_topc @ X19 @ X18 )
        = X18 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
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
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( v1_tops_1 @ X28 @ X29 )
      | ~ ( v3_tex_2 @ X28 @ X29 )
      | ~ ( v3_pre_topc @ X28 @ X29 )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
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
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( v1_tops_1 @ X22 @ X23 )
      | ( ( k2_pre_topc @ X23 @ X22 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_pre_topc @ X23 ) ) ),
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
    ! [X26: $i,X27: $i] :
      ( ~ ( v3_tdlat_3 @ X26 )
      | ~ ( v4_pre_topc @ X27 @ X26 )
      | ( v3_pre_topc @ X27 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 ) ) ),
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
    v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( v1_subset_1 @ sk_B_1 @ sk_B_1 )
   <= ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('56',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('57',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_subset_1 @ X4 @ X5 )
        = ( k4_xboole_0 @ X4 @ X5 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('59',plain,(
    ! [X2: $i] :
      ( ( k1_subset_1 @ X2 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf(t22_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ) )).

thf('60',plain,(
    ! [X8: $i] :
      ( ( k2_subset_1 @ X8 )
      = ( k3_subset_1 @ X8 @ ( k1_subset_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t22_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('61',plain,(
    ! [X3: $i] :
      ( ( k2_subset_1 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('62',plain,(
    ! [X8: $i] :
      ( X8
      = ( k3_subset_1 @ X8 @ ( k1_subset_1 @ X8 ) ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['59','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['58','63'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('67',plain,(
    ! [X12: $i,X14: $i] :
      ( ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('68',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X24: $i,X25: $i] :
      ( ( v1_xboole_0 @ X24 )
      | ~ ( v1_subset_1 @ X25 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X24 ) )
      | ~ ( v1_xboole_0 @ ( k3_subset_1 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[fc1_tex_2])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k3_subset_1 @ X0 @ X0 ) )
      | ~ ( v1_subset_1 @ X0 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('72',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_subset_1 @ X7 @ ( k3_subset_1 @ X7 @ X6 ) )
        = X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['59','62'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['73','74'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('76',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( v1_subset_1 @ X0 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['70','75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('79',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( v1_subset_1 @ X10 @ X11 )
      | ~ ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc4_subset_1])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_subset_1 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ~ ( v1_subset_1 @ X0 @ X0 ) ),
    inference(clc,[status(thm)],['77','80'])).

thf('82',plain,(
    ~ ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['55','81'])).

thf('83',plain,
    ( ( v3_pre_topc @ sk_B_1 @ sk_A )
    | ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['19'])).

thf('84',plain,(
    v3_pre_topc @ sk_B_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['36','84'])).

thf('86',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_1 )
    | ~ ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['18','85'])).

thf('87',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t29_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('88',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X21 ) @ X20 ) @ X21 )
      | ( v4_pre_topc @ X20 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t29_tops_1])).

thf('89',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('92',plain,
    ( ( v4_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( v3_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['89','90','91'])).

thf('93',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_subset_1 @ X7 @ ( k3_subset_1 @ X7 @ X6 ) )
        = X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('95',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('97',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
    = sk_B_1 ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('99',plain,(
    ! [X12: $i,X14: $i] :
      ( ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_subset_1 @ X4 @ X5 )
        = ( k4_xboole_0 @ X4 @ X5 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
    = sk_B_1 ),
    inference(demod,[status(thm)],['97','102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('105',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X21 ) @ X20 ) @ X21 )
      | ( v4_pre_topc @ X20 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t29_tops_1])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) @ X0 )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) @ X0 )
      | ~ ( v3_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,
    ( ~ ( v3_pre_topc @ sk_B_1 @ sk_A )
    | ( v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['103','108'])).

thf('110',plain,
    ( ( v3_pre_topc @ sk_B_1 @ sk_A )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['19'])).

thf('111',plain,(
    v3_pre_topc @ sk_B_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['82','83'])).

thf('112',plain,(
    v3_pre_topc @ sk_B_1 @ sk_A ),
    inference(simpl_trail,[status(thm)],['110','111'])).

thf('113',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['109','112','113'])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('116',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( v3_tdlat_3 @ X26 )
      | ~ ( v4_pre_topc @ X27 @ X26 )
      | ( v3_pre_topc @ X27 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t24_tdlat_3])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) @ X0 )
      | ~ ( v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) @ X0 )
      | ~ ( v3_tdlat_3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,
    ( ~ ( v3_tdlat_3 @ sk_A )
    | ( v3_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['114','117'])).

thf('119',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    v3_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['118','119','120','121'])).

thf('123',plain,(
    v4_pre_topc @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['92','122'])).

thf('124',plain,
    ( ( u1_struct_0 @ sk_A )
    = sk_B_1 ),
    inference(demod,[status(thm)],['86','123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('126',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_subset_1 @ X4 @ X5 )
        = ( k4_xboole_0 @ X4 @ X5 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['127','128'])).

thf('130',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('131',plain,(
    $false ),
    inference(demod,[status(thm)],['13','124','129','130'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.O2sBYsVmBo
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:05:03 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.66  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.66  % Solved by: fo/fo7.sh
% 0.20/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.66  % done 629 iterations in 0.176s
% 0.20/0.66  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.66  % SZS output start Refutation
% 0.20/0.66  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.20/0.66  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.66  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.20/0.66  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.66  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.66  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.20/0.66  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.66  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.20/0.66  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.66  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.20/0.66  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.66  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.20/0.66  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.20/0.66  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.20/0.66  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.20/0.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.66  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.66  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.66  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.66  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.66  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.20/0.66  thf(t61_tex_2, conjecture,
% 0.20/0.66    (![A:$i]:
% 0.20/0.66     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.20/0.66         ( l1_pre_topc @ A ) ) =>
% 0.20/0.66       ( ![B:$i]:
% 0.20/0.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.66           ( ~( ( ( v3_pre_topc @ B @ A ) | ( v4_pre_topc @ B @ A ) ) & 
% 0.20/0.66                ( v3_tex_2 @ B @ A ) & 
% 0.20/0.66                ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.20/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.66    (~( ![A:$i]:
% 0.20/0.66        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.66            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.66          ( ![B:$i]:
% 0.20/0.66            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.66              ( ~( ( ( v3_pre_topc @ B @ A ) | ( v4_pre_topc @ B @ A ) ) & 
% 0.20/0.66                   ( v3_tex_2 @ B @ A ) & 
% 0.20/0.66                   ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )),
% 0.20/0.66    inference('cnf.neg', [status(esa)], [t61_tex_2])).
% 0.20/0.66  thf('0', plain,
% 0.20/0.66      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.66  thf(fc1_tex_2, axiom,
% 0.20/0.66    (![A:$i,B:$i]:
% 0.20/0.66     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_subset_1 @ B @ A ) & 
% 0.20/0.66         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.66       ( ~( v1_xboole_0 @ ( k3_subset_1 @ A @ B ) ) ) ))).
% 0.20/0.66  thf('1', plain,
% 0.20/0.66      (![X24 : $i, X25 : $i]:
% 0.20/0.66         ((v1_xboole_0 @ X24)
% 0.20/0.66          | ~ (v1_subset_1 @ X25 @ X24)
% 0.20/0.66          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X24))
% 0.20/0.66          | ~ (v1_xboole_0 @ (k3_subset_1 @ X24 @ X25)))),
% 0.20/0.66      inference('cnf', [status(esa)], [fc1_tex_2])).
% 0.20/0.66  thf('2', plain,
% 0.20/0.66      ((~ (v1_xboole_0 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))
% 0.20/0.66        | ~ (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.20/0.66        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.66      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.66  thf('3', plain,
% 0.20/0.66      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.66  thf(d5_subset_1, axiom,
% 0.20/0.66    (![A:$i,B:$i]:
% 0.20/0.66     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.66       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.20/0.66  thf('4', plain,
% 0.20/0.66      (![X4 : $i, X5 : $i]:
% 0.20/0.66         (((k3_subset_1 @ X4 @ X5) = (k4_xboole_0 @ X4 @ X5))
% 0.20/0.66          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X4)))),
% 0.20/0.66      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.20/0.66  thf('5', plain,
% 0.20/0.66      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)
% 0.20/0.66         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1))),
% 0.20/0.66      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.66  thf('6', plain, ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.20/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.66  thf('7', plain,
% 0.20/0.66      ((~ (v1_xboole_0 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1))
% 0.20/0.66        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.66      inference('demod', [status(thm)], ['2', '5', '6'])).
% 0.20/0.66  thf('8', plain,
% 0.20/0.66      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.66  thf(cc4_subset_1, axiom,
% 0.20/0.66    (![A:$i]:
% 0.20/0.66     ( ( v1_xboole_0 @ A ) =>
% 0.20/0.66       ( ![B:$i]:
% 0.20/0.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.66           ( ~( v1_subset_1 @ B @ A ) ) ) ) ))).
% 0.20/0.66  thf('9', plain,
% 0.20/0.66      (![X10 : $i, X11 : $i]:
% 0.20/0.66         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 0.20/0.66          | ~ (v1_subset_1 @ X10 @ X11)
% 0.20/0.66          | ~ (v1_xboole_0 @ X11))),
% 0.20/0.66      inference('cnf', [status(esa)], [cc4_subset_1])).
% 0.20/0.66  thf('10', plain,
% 0.20/0.66      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.66        | ~ (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.66      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.66  thf('11', plain, ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.20/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.66  thf('12', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.20/0.66      inference('demod', [status(thm)], ['10', '11'])).
% 0.20/0.66  thf('13', plain,
% 0.20/0.66      (~ (v1_xboole_0 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1))),
% 0.20/0.66      inference('clc', [status(thm)], ['7', '12'])).
% 0.20/0.66  thf('14', plain,
% 0.20/0.66      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.66  thf(t52_pre_topc, axiom,
% 0.20/0.66    (![A:$i]:
% 0.20/0.66     ( ( l1_pre_topc @ A ) =>
% 0.20/0.66       ( ![B:$i]:
% 0.20/0.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.66           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.20/0.66             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.20/0.66               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.20/0.66  thf('15', plain,
% 0.20/0.66      (![X18 : $i, X19 : $i]:
% 0.20/0.66         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.20/0.66          | ~ (v4_pre_topc @ X18 @ X19)
% 0.20/0.66          | ((k2_pre_topc @ X19 @ X18) = (X18))
% 0.20/0.66          | ~ (l1_pre_topc @ X19))),
% 0.20/0.66      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.20/0.66  thf('16', plain,
% 0.20/0.66      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.66        | ((k2_pre_topc @ sk_A @ sk_B_1) = (sk_B_1))
% 0.20/0.66        | ~ (v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.20/0.66      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.66  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.66  thf('18', plain,
% 0.20/0.66      ((((k2_pre_topc @ sk_A @ sk_B_1) = (sk_B_1))
% 0.20/0.66        | ~ (v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.20/0.66      inference('demod', [status(thm)], ['16', '17'])).
% 0.20/0.66  thf('19', plain,
% 0.20/0.66      (((v3_pre_topc @ sk_B_1 @ sk_A) | (v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.20/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.66  thf('20', plain,
% 0.20/0.66      (((v3_pre_topc @ sk_B_1 @ sk_A)) <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.20/0.66      inference('split', [status(esa)], ['19'])).
% 0.20/0.66  thf('21', plain,
% 0.20/0.66      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.66  thf(t47_tex_2, axiom,
% 0.20/0.66    (![A:$i]:
% 0.20/0.66     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.66       ( ![B:$i]:
% 0.20/0.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.66           ( ( ( v3_pre_topc @ B @ A ) & ( v3_tex_2 @ B @ A ) ) =>
% 0.20/0.66             ( v1_tops_1 @ B @ A ) ) ) ) ))).
% 0.20/0.66  thf('22', plain,
% 0.20/0.66      (![X28 : $i, X29 : $i]:
% 0.20/0.66         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.20/0.66          | (v1_tops_1 @ X28 @ X29)
% 0.20/0.66          | ~ (v3_tex_2 @ X28 @ X29)
% 0.20/0.66          | ~ (v3_pre_topc @ X28 @ X29)
% 0.20/0.66          | ~ (l1_pre_topc @ X29)
% 0.20/0.66          | ~ (v2_pre_topc @ X29)
% 0.20/0.66          | (v2_struct_0 @ X29))),
% 0.20/0.66      inference('cnf', [status(esa)], [t47_tex_2])).
% 0.20/0.66  thf('23', plain,
% 0.20/0.66      (((v2_struct_0 @ sk_A)
% 0.20/0.66        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.66        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.66        | ~ (v3_pre_topc @ sk_B_1 @ sk_A)
% 0.20/0.66        | ~ (v3_tex_2 @ sk_B_1 @ sk_A)
% 0.20/0.66        | (v1_tops_1 @ sk_B_1 @ sk_A))),
% 0.20/0.66      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.66  thf('24', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.66  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.66  thf('26', plain, ((v3_tex_2 @ sk_B_1 @ sk_A)),
% 0.20/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.66  thf('27', plain,
% 0.20/0.66      (((v2_struct_0 @ sk_A)
% 0.20/0.66        | ~ (v3_pre_topc @ sk_B_1 @ sk_A)
% 0.20/0.66        | (v1_tops_1 @ sk_B_1 @ sk_A))),
% 0.20/0.66      inference('demod', [status(thm)], ['23', '24', '25', '26'])).
% 0.20/0.66  thf('28', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.66  thf('29', plain,
% 0.20/0.66      (((v1_tops_1 @ sk_B_1 @ sk_A) | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.20/0.66      inference('clc', [status(thm)], ['27', '28'])).
% 0.20/0.66  thf('30', plain,
% 0.20/0.66      (((v1_tops_1 @ sk_B_1 @ sk_A)) <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.20/0.66      inference('sup-', [status(thm)], ['20', '29'])).
% 0.20/0.66  thf('31', plain,
% 0.20/0.66      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.66  thf(d2_tops_3, axiom,
% 0.20/0.66    (![A:$i]:
% 0.20/0.66     ( ( l1_pre_topc @ A ) =>
% 0.20/0.66       ( ![B:$i]:
% 0.20/0.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.66           ( ( v1_tops_1 @ B @ A ) <=>
% 0.20/0.66             ( ( k2_pre_topc @ A @ B ) = ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.20/0.66  thf('32', plain,
% 0.20/0.66      (![X22 : $i, X23 : $i]:
% 0.20/0.66         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.20/0.66          | ~ (v1_tops_1 @ X22 @ X23)
% 0.20/0.66          | ((k2_pre_topc @ X23 @ X22) = (u1_struct_0 @ X23))
% 0.20/0.66          | ~ (l1_pre_topc @ X23))),
% 0.20/0.66      inference('cnf', [status(esa)], [d2_tops_3])).
% 0.20/0.66  thf('33', plain,
% 0.20/0.66      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.66        | ((k2_pre_topc @ sk_A @ sk_B_1) = (u1_struct_0 @ sk_A))
% 0.20/0.66        | ~ (v1_tops_1 @ sk_B_1 @ sk_A))),
% 0.20/0.66      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.66  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.66  thf('35', plain,
% 0.20/0.66      ((((k2_pre_topc @ sk_A @ sk_B_1) = (u1_struct_0 @ sk_A))
% 0.20/0.66        | ~ (v1_tops_1 @ sk_B_1 @ sk_A))),
% 0.20/0.66      inference('demod', [status(thm)], ['33', '34'])).
% 0.20/0.66  thf('36', plain,
% 0.20/0.66      ((((k2_pre_topc @ sk_A @ sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.20/0.66         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.20/0.66      inference('sup-', [status(thm)], ['30', '35'])).
% 0.20/0.66  thf('37', plain,
% 0.20/0.66      (((v4_pre_topc @ sk_B_1 @ sk_A)) <= (((v4_pre_topc @ sk_B_1 @ sk_A)))),
% 0.20/0.66      inference('split', [status(esa)], ['19'])).
% 0.20/0.66  thf('38', plain,
% 0.20/0.66      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.66  thf(t24_tdlat_3, axiom,
% 0.20/0.66    (![A:$i]:
% 0.20/0.66     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.66       ( ( v3_tdlat_3 @ A ) <=>
% 0.20/0.66         ( ![B:$i]:
% 0.20/0.66           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.66             ( ( v4_pre_topc @ B @ A ) => ( v3_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.20/0.66  thf('39', plain,
% 0.20/0.66      (![X26 : $i, X27 : $i]:
% 0.20/0.66         (~ (v3_tdlat_3 @ X26)
% 0.20/0.66          | ~ (v4_pre_topc @ X27 @ X26)
% 0.20/0.66          | (v3_pre_topc @ X27 @ X26)
% 0.20/0.66          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.20/0.66          | ~ (l1_pre_topc @ X26)
% 0.20/0.66          | ~ (v2_pre_topc @ X26))),
% 0.20/0.66      inference('cnf', [status(esa)], [t24_tdlat_3])).
% 0.20/0.66  thf('40', plain,
% 0.20/0.66      ((~ (v2_pre_topc @ sk_A)
% 0.20/0.66        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.66        | (v3_pre_topc @ sk_B_1 @ sk_A)
% 0.20/0.66        | ~ (v4_pre_topc @ sk_B_1 @ sk_A)
% 0.20/0.66        | ~ (v3_tdlat_3 @ sk_A))),
% 0.20/0.66      inference('sup-', [status(thm)], ['38', '39'])).
% 0.20/0.66  thf('41', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.66  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.66  thf('43', plain, ((v3_tdlat_3 @ sk_A)),
% 0.20/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.66  thf('44', plain,
% 0.20/0.66      (((v3_pre_topc @ sk_B_1 @ sk_A) | ~ (v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.20/0.66      inference('demod', [status(thm)], ['40', '41', '42', '43'])).
% 0.20/0.66  thf('45', plain,
% 0.20/0.66      (((v3_pre_topc @ sk_B_1 @ sk_A)) <= (((v4_pre_topc @ sk_B_1 @ sk_A)))),
% 0.20/0.66      inference('sup-', [status(thm)], ['37', '44'])).
% 0.20/0.66  thf('46', plain,
% 0.20/0.66      (((v1_tops_1 @ sk_B_1 @ sk_A) | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.20/0.66      inference('clc', [status(thm)], ['27', '28'])).
% 0.20/0.66  thf('47', plain,
% 0.20/0.66      (((v1_tops_1 @ sk_B_1 @ sk_A)) <= (((v4_pre_topc @ sk_B_1 @ sk_A)))),
% 0.20/0.66      inference('sup-', [status(thm)], ['45', '46'])).
% 0.20/0.66  thf('48', plain,
% 0.20/0.66      ((((k2_pre_topc @ sk_A @ sk_B_1) = (u1_struct_0 @ sk_A))
% 0.20/0.66        | ~ (v1_tops_1 @ sk_B_1 @ sk_A))),
% 0.20/0.66      inference('demod', [status(thm)], ['33', '34'])).
% 0.20/0.66  thf('49', plain,
% 0.20/0.66      ((((k2_pre_topc @ sk_A @ sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.20/0.66         <= (((v4_pre_topc @ sk_B_1 @ sk_A)))),
% 0.20/0.66      inference('sup-', [status(thm)], ['47', '48'])).
% 0.20/0.66  thf('50', plain,
% 0.20/0.66      (((v4_pre_topc @ sk_B_1 @ sk_A)) <= (((v4_pre_topc @ sk_B_1 @ sk_A)))),
% 0.20/0.66      inference('split', [status(esa)], ['19'])).
% 0.20/0.66  thf('51', plain,
% 0.20/0.66      ((((k2_pre_topc @ sk_A @ sk_B_1) = (sk_B_1))
% 0.20/0.66        | ~ (v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.20/0.66      inference('demod', [status(thm)], ['16', '17'])).
% 0.20/0.66  thf('52', plain,
% 0.20/0.66      ((((k2_pre_topc @ sk_A @ sk_B_1) = (sk_B_1)))
% 0.20/0.66         <= (((v4_pre_topc @ sk_B_1 @ sk_A)))),
% 0.20/0.66      inference('sup-', [status(thm)], ['50', '51'])).
% 0.20/0.66  thf('53', plain,
% 0.20/0.66      ((((u1_struct_0 @ sk_A) = (sk_B_1))) <= (((v4_pre_topc @ sk_B_1 @ sk_A)))),
% 0.20/0.66      inference('sup+', [status(thm)], ['49', '52'])).
% 0.20/0.66  thf('54', plain, ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.20/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.66  thf('55', plain,
% 0.20/0.66      (((v1_subset_1 @ sk_B_1 @ sk_B_1)) <= (((v4_pre_topc @ sk_B_1 @ sk_A)))),
% 0.20/0.66      inference('sup+', [status(thm)], ['53', '54'])).
% 0.20/0.66  thf(t4_subset_1, axiom,
% 0.20/0.66    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.20/0.66  thf('56', plain,
% 0.20/0.66      (![X9 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X9))),
% 0.20/0.66      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.20/0.66  thf('57', plain,
% 0.20/0.66      (![X4 : $i, X5 : $i]:
% 0.20/0.66         (((k3_subset_1 @ X4 @ X5) = (k4_xboole_0 @ X4 @ X5))
% 0.20/0.66          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X4)))),
% 0.20/0.66      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.20/0.66  thf('58', plain,
% 0.20/0.66      (![X0 : $i]:
% 0.20/0.66         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.66      inference('sup-', [status(thm)], ['56', '57'])).
% 0.20/0.66  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.20/0.66  thf('59', plain, (![X2 : $i]: ((k1_subset_1 @ X2) = (k1_xboole_0))),
% 0.20/0.66      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.20/0.66  thf(t22_subset_1, axiom,
% 0.20/0.66    (![A:$i]:
% 0.20/0.66     ( ( k2_subset_1 @ A ) = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ))).
% 0.20/0.66  thf('60', plain,
% 0.20/0.66      (![X8 : $i]:
% 0.20/0.66         ((k2_subset_1 @ X8) = (k3_subset_1 @ X8 @ (k1_subset_1 @ X8)))),
% 0.20/0.66      inference('cnf', [status(esa)], [t22_subset_1])).
% 0.20/0.66  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.20/0.66  thf('61', plain, (![X3 : $i]: ((k2_subset_1 @ X3) = (X3))),
% 0.20/0.66      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.20/0.66  thf('62', plain,
% 0.20/0.66      (![X8 : $i]: ((X8) = (k3_subset_1 @ X8 @ (k1_subset_1 @ X8)))),
% 0.20/0.66      inference('demod', [status(thm)], ['60', '61'])).
% 0.20/0.66  thf('63', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 0.20/0.66      inference('sup+', [status(thm)], ['59', '62'])).
% 0.20/0.66  thf('64', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.66      inference('sup+', [status(thm)], ['58', '63'])).
% 0.20/0.66  thf(t36_xboole_1, axiom,
% 0.20/0.66    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.20/0.66  thf('65', plain,
% 0.20/0.66      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 0.20/0.66      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.20/0.66  thf('66', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.20/0.66      inference('sup+', [status(thm)], ['64', '65'])).
% 0.20/0.66  thf(t3_subset, axiom,
% 0.20/0.66    (![A:$i,B:$i]:
% 0.20/0.66     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.66  thf('67', plain,
% 0.20/0.66      (![X12 : $i, X14 : $i]:
% 0.20/0.66         ((m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X14)) | ~ (r1_tarski @ X12 @ X14))),
% 0.20/0.66      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.66  thf('68', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.20/0.66      inference('sup-', [status(thm)], ['66', '67'])).
% 0.20/0.66  thf('69', plain,
% 0.20/0.66      (![X24 : $i, X25 : $i]:
% 0.20/0.66         ((v1_xboole_0 @ X24)
% 0.20/0.66          | ~ (v1_subset_1 @ X25 @ X24)
% 0.20/0.66          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X24))
% 0.20/0.66          | ~ (v1_xboole_0 @ (k3_subset_1 @ X24 @ X25)))),
% 0.20/0.66      inference('cnf', [status(esa)], [fc1_tex_2])).
% 0.20/0.66  thf('70', plain,
% 0.20/0.66      (![X0 : $i]:
% 0.20/0.66         (~ (v1_xboole_0 @ (k3_subset_1 @ X0 @ X0))
% 0.20/0.66          | ~ (v1_subset_1 @ X0 @ X0)
% 0.20/0.66          | (v1_xboole_0 @ X0))),
% 0.20/0.66      inference('sup-', [status(thm)], ['68', '69'])).
% 0.20/0.66  thf('71', plain,
% 0.20/0.66      (![X9 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X9))),
% 0.20/0.66      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.20/0.66  thf(involutiveness_k3_subset_1, axiom,
% 0.20/0.66    (![A:$i,B:$i]:
% 0.20/0.66     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.66       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.20/0.66  thf('72', plain,
% 0.20/0.66      (![X6 : $i, X7 : $i]:
% 0.20/0.66         (((k3_subset_1 @ X7 @ (k3_subset_1 @ X7 @ X6)) = (X6))
% 0.20/0.66          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.20/0.66      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.20/0.66  thf('73', plain,
% 0.20/0.66      (![X0 : $i]:
% 0.20/0.66         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.20/0.66      inference('sup-', [status(thm)], ['71', '72'])).
% 0.20/0.66  thf('74', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 0.20/0.66      inference('sup+', [status(thm)], ['59', '62'])).
% 0.20/0.66  thf('75', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.66      inference('demod', [status(thm)], ['73', '74'])).
% 0.20/0.66  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.20/0.66  thf('76', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.66      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.66  thf('77', plain,
% 0.20/0.66      (![X0 : $i]: (~ (v1_subset_1 @ X0 @ X0) | (v1_xboole_0 @ X0))),
% 0.20/0.66      inference('demod', [status(thm)], ['70', '75', '76'])).
% 0.20/0.66  thf('78', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.20/0.66      inference('sup-', [status(thm)], ['66', '67'])).
% 0.20/0.66  thf('79', plain,
% 0.20/0.66      (![X10 : $i, X11 : $i]:
% 0.20/0.66         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 0.20/0.66          | ~ (v1_subset_1 @ X10 @ X11)
% 0.20/0.66          | ~ (v1_xboole_0 @ X11))),
% 0.20/0.66      inference('cnf', [status(esa)], [cc4_subset_1])).
% 0.20/0.66  thf('80', plain,
% 0.20/0.66      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ~ (v1_subset_1 @ X0 @ X0))),
% 0.20/0.66      inference('sup-', [status(thm)], ['78', '79'])).
% 0.20/0.66  thf('81', plain, (![X0 : $i]: ~ (v1_subset_1 @ X0 @ X0)),
% 0.20/0.66      inference('clc', [status(thm)], ['77', '80'])).
% 0.20/0.66  thf('82', plain, (~ ((v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.20/0.66      inference('sup-', [status(thm)], ['55', '81'])).
% 0.20/0.66  thf('83', plain,
% 0.20/0.66      (((v3_pre_topc @ sk_B_1 @ sk_A)) | ((v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.20/0.66      inference('split', [status(esa)], ['19'])).
% 0.20/0.66  thf('84', plain, (((v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.20/0.66      inference('sat_resolution*', [status(thm)], ['82', '83'])).
% 0.20/0.66  thf('85', plain, (((k2_pre_topc @ sk_A @ sk_B_1) = (u1_struct_0 @ sk_A))),
% 0.20/0.66      inference('simpl_trail', [status(thm)], ['36', '84'])).
% 0.20/0.66  thf('86', plain,
% 0.20/0.66      ((((u1_struct_0 @ sk_A) = (sk_B_1)) | ~ (v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.20/0.66      inference('demod', [status(thm)], ['18', '85'])).
% 0.20/0.66  thf('87', plain,
% 0.20/0.66      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.66  thf(t29_tops_1, axiom,
% 0.20/0.66    (![A:$i]:
% 0.20/0.66     ( ( l1_pre_topc @ A ) =>
% 0.20/0.66       ( ![B:$i]:
% 0.20/0.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.66           ( ( v4_pre_topc @ B @ A ) <=>
% 0.20/0.66             ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.20/0.66  thf('88', plain,
% 0.20/0.66      (![X20 : $i, X21 : $i]:
% 0.20/0.66         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.20/0.66          | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X21) @ X20) @ X21)
% 0.20/0.66          | (v4_pre_topc @ X20 @ X21)
% 0.20/0.66          | ~ (l1_pre_topc @ X21))),
% 0.20/0.66      inference('cnf', [status(esa)], [t29_tops_1])).
% 0.20/0.66  thf('89', plain,
% 0.20/0.66      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.66        | (v4_pre_topc @ sk_B_1 @ sk_A)
% 0.20/0.66        | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A))),
% 0.20/0.66      inference('sup-', [status(thm)], ['87', '88'])).
% 0.20/0.66  thf('90', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.66  thf('91', plain,
% 0.20/0.66      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)
% 0.20/0.66         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1))),
% 0.20/0.66      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.66  thf('92', plain,
% 0.20/0.66      (((v4_pre_topc @ sk_B_1 @ sk_A)
% 0.20/0.66        | ~ (v3_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A))),
% 0.20/0.66      inference('demod', [status(thm)], ['89', '90', '91'])).
% 0.20/0.66  thf('93', plain,
% 0.20/0.66      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.66  thf('94', plain,
% 0.20/0.66      (![X6 : $i, X7 : $i]:
% 0.20/0.66         (((k3_subset_1 @ X7 @ (k3_subset_1 @ X7 @ X6)) = (X6))
% 0.20/0.66          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.20/0.66      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.20/0.66  thf('95', plain,
% 0.20/0.66      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.66         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)) = (sk_B_1))),
% 0.20/0.66      inference('sup-', [status(thm)], ['93', '94'])).
% 0.20/0.66  thf('96', plain,
% 0.20/0.66      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)
% 0.20/0.66         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1))),
% 0.20/0.66      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.66  thf('97', plain,
% 0.20/0.66      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.66         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1)) = (sk_B_1))),
% 0.20/0.66      inference('demod', [status(thm)], ['95', '96'])).
% 0.20/0.66  thf('98', plain,
% 0.20/0.66      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 0.20/0.66      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.20/0.66  thf('99', plain,
% 0.20/0.66      (![X12 : $i, X14 : $i]:
% 0.20/0.66         ((m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X14)) | ~ (r1_tarski @ X12 @ X14))),
% 0.20/0.66      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.66  thf('100', plain,
% 0.20/0.66      (![X0 : $i, X1 : $i]:
% 0.20/0.66         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.20/0.66      inference('sup-', [status(thm)], ['98', '99'])).
% 0.20/0.66  thf('101', plain,
% 0.20/0.66      (![X4 : $i, X5 : $i]:
% 0.20/0.66         (((k3_subset_1 @ X4 @ X5) = (k4_xboole_0 @ X4 @ X5))
% 0.20/0.66          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X4)))),
% 0.20/0.66      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.20/0.66  thf('102', plain,
% 0.20/0.66      (![X0 : $i, X1 : $i]:
% 0.20/0.66         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.20/0.66           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.20/0.66      inference('sup-', [status(thm)], ['100', '101'])).
% 0.20/0.66  thf('103', plain,
% 0.20/0.66      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.66         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1)) = (sk_B_1))),
% 0.20/0.66      inference('demod', [status(thm)], ['97', '102'])).
% 0.20/0.66  thf('104', plain,
% 0.20/0.66      (![X0 : $i, X1 : $i]:
% 0.20/0.66         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.20/0.66      inference('sup-', [status(thm)], ['98', '99'])).
% 0.20/0.66  thf('105', plain,
% 0.20/0.66      (![X20 : $i, X21 : $i]:
% 0.20/0.66         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.20/0.66          | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X21) @ X20) @ X21)
% 0.20/0.66          | (v4_pre_topc @ X20 @ X21)
% 0.20/0.66          | ~ (l1_pre_topc @ X21))),
% 0.20/0.66      inference('cnf', [status(esa)], [t29_tops_1])).
% 0.20/0.66  thf('106', plain,
% 0.20/0.66      (![X0 : $i, X1 : $i]:
% 0.20/0.66         (~ (l1_pre_topc @ X0)
% 0.20/0.66          | (v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1) @ X0)
% 0.20/0.66          | ~ (v3_pre_topc @ 
% 0.20/0.66               (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.20/0.66                (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1)) @ 
% 0.20/0.66               X0))),
% 0.20/0.66      inference('sup-', [status(thm)], ['104', '105'])).
% 0.20/0.66  thf('107', plain,
% 0.20/0.66      (![X0 : $i, X1 : $i]:
% 0.20/0.66         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.20/0.66           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.20/0.66      inference('sup-', [status(thm)], ['100', '101'])).
% 0.20/0.66  thf('108', plain,
% 0.20/0.66      (![X0 : $i, X1 : $i]:
% 0.20/0.66         (~ (l1_pre_topc @ X0)
% 0.20/0.66          | (v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1) @ X0)
% 0.20/0.66          | ~ (v3_pre_topc @ 
% 0.20/0.66               (k4_xboole_0 @ (u1_struct_0 @ X0) @ 
% 0.20/0.66                (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1)) @ 
% 0.20/0.66               X0))),
% 0.20/0.66      inference('demod', [status(thm)], ['106', '107'])).
% 0.20/0.66  thf('109', plain,
% 0.20/0.66      ((~ (v3_pre_topc @ sk_B_1 @ sk_A)
% 0.20/0.66        | (v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 0.20/0.66        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.66      inference('sup-', [status(thm)], ['103', '108'])).
% 0.20/0.66  thf('110', plain,
% 0.20/0.66      (((v3_pre_topc @ sk_B_1 @ sk_A)) <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.20/0.66      inference('split', [status(esa)], ['19'])).
% 0.20/0.66  thf('111', plain, (((v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.20/0.66      inference('sat_resolution*', [status(thm)], ['82', '83'])).
% 0.20/0.66  thf('112', plain, ((v3_pre_topc @ sk_B_1 @ sk_A)),
% 0.20/0.66      inference('simpl_trail', [status(thm)], ['110', '111'])).
% 0.20/0.66  thf('113', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.66  thf('114', plain,
% 0.20/0.66      ((v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)),
% 0.20/0.66      inference('demod', [status(thm)], ['109', '112', '113'])).
% 0.20/0.66  thf('115', plain,
% 0.20/0.66      (![X0 : $i, X1 : $i]:
% 0.20/0.66         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.20/0.66      inference('sup-', [status(thm)], ['98', '99'])).
% 0.20/0.66  thf('116', plain,
% 0.20/0.66      (![X26 : $i, X27 : $i]:
% 0.20/0.66         (~ (v3_tdlat_3 @ X26)
% 0.20/0.66          | ~ (v4_pre_topc @ X27 @ X26)
% 0.20/0.66          | (v3_pre_topc @ X27 @ X26)
% 0.20/0.66          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.20/0.66          | ~ (l1_pre_topc @ X26)
% 0.20/0.66          | ~ (v2_pre_topc @ X26))),
% 0.20/0.66      inference('cnf', [status(esa)], [t24_tdlat_3])).
% 0.20/0.66  thf('117', plain,
% 0.20/0.66      (![X0 : $i, X1 : $i]:
% 0.20/0.66         (~ (v2_pre_topc @ X0)
% 0.20/0.66          | ~ (l1_pre_topc @ X0)
% 0.20/0.66          | (v3_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1) @ X0)
% 0.20/0.66          | ~ (v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1) @ X0)
% 0.20/0.66          | ~ (v3_tdlat_3 @ X0))),
% 0.20/0.66      inference('sup-', [status(thm)], ['115', '116'])).
% 0.20/0.66  thf('118', plain,
% 0.20/0.66      ((~ (v3_tdlat_3 @ sk_A)
% 0.20/0.66        | (v3_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 0.20/0.66        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.66        | ~ (v2_pre_topc @ sk_A))),
% 0.20/0.66      inference('sup-', [status(thm)], ['114', '117'])).
% 0.20/0.66  thf('119', plain, ((v3_tdlat_3 @ sk_A)),
% 0.20/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.66  thf('120', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.66  thf('121', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.66  thf('122', plain,
% 0.20/0.66      ((v3_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)),
% 0.20/0.66      inference('demod', [status(thm)], ['118', '119', '120', '121'])).
% 0.20/0.66  thf('123', plain, ((v4_pre_topc @ sk_B_1 @ sk_A)),
% 0.20/0.66      inference('demod', [status(thm)], ['92', '122'])).
% 0.20/0.66  thf('124', plain, (((u1_struct_0 @ sk_A) = (sk_B_1))),
% 0.20/0.66      inference('demod', [status(thm)], ['86', '123'])).
% 0.20/0.66  thf('125', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.20/0.66      inference('sup-', [status(thm)], ['66', '67'])).
% 0.20/0.66  thf('126', plain,
% 0.20/0.66      (![X4 : $i, X5 : $i]:
% 0.20/0.66         (((k3_subset_1 @ X4 @ X5) = (k4_xboole_0 @ X4 @ X5))
% 0.20/0.66          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X4)))),
% 0.20/0.66      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.20/0.66  thf('127', plain,
% 0.20/0.66      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.20/0.66      inference('sup-', [status(thm)], ['125', '126'])).
% 0.20/0.66  thf('128', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.66      inference('demod', [status(thm)], ['73', '74'])).
% 0.20/0.66  thf('129', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.66      inference('sup+', [status(thm)], ['127', '128'])).
% 0.20/0.66  thf('130', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.66      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.66  thf('131', plain, ($false),
% 0.20/0.66      inference('demod', [status(thm)], ['13', '124', '129', '130'])).
% 0.20/0.66  
% 0.20/0.66  % SZS output end Refutation
% 0.20/0.66  
% 0.20/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
