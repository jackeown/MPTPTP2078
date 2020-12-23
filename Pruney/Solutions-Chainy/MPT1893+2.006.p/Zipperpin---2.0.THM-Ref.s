%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Z8gOFrgJtk

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:34 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 469 expanded)
%              Number of leaves         :   38 ( 150 expanded)
%              Depth                    :   16
%              Number of atoms          : 1037 (6077 expanded)
%              Number of equality atoms :   45 ( 128 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

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
    ! [X27: $i,X28: $i] :
      ( ( v1_xboole_0 @ X27 )
      | ~ ( v1_subset_1 @ X28 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X27 ) )
      | ~ ( v1_xboole_0 @ ( k3_subset_1 @ X27 @ X28 ) ) ) ),
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
    ! [X10: $i,X11: $i] :
      ( ( ( k3_subset_1 @ X10 @ X11 )
        = ( k4_xboole_0 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
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
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( v1_subset_1 @ X16 @ X17 )
      | ~ ( v1_xboole_0 @ X17 ) ) ),
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
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( v4_pre_topc @ X21 @ X22 )
      | ( ( k2_pre_topc @ X22 @ X21 )
        = X21 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
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
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ( v1_tops_1 @ X31 @ X32 )
      | ~ ( v3_tex_2 @ X31 @ X32 )
      | ~ ( v3_pre_topc @ X31 @ X32 )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
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
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( v1_tops_1 @ X25 @ X26 )
      | ( ( k2_pre_topc @ X26 @ X25 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_pre_topc @ X26 ) ) ),
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
    ! [X29: $i,X30: $i] :
      ( ~ ( v3_tdlat_3 @ X29 )
      | ~ ( v4_pre_topc @ X30 @ X29 )
      | ( v3_pre_topc @ X30 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 ) ) ),
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

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('57',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['56'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('58',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('60',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['56'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('63',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('68',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('69',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('70',plain,(
    ~ ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['55','61','68','69'])).

thf('71',plain,
    ( ( v3_pre_topc @ sk_B_1 @ sk_A )
    | ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['19'])).

thf('72',plain,(
    v3_pre_topc @ sk_B_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['36','72'])).

thf('74',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_1 )
    | ~ ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['18','73'])).

thf('75',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t29_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('76',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X24 ) @ X23 ) @ X24 )
      | ( v4_pre_topc @ X23 @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t29_tops_1])).

thf('77',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('80',plain,
    ( ( v4_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( v3_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('81',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('82',plain,(
    ! [X12: $i,X13: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X12 @ X13 ) @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('83',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('85',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( v3_tdlat_3 @ X29 )
      | ~ ( v4_pre_topc @ X30 @ X29 )
      | ( v3_pre_topc @ X30 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[t24_tdlat_3])).

thf('87',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
    | ~ ( v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( v3_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
    | ~ ( v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['87','88','89','90'])).

thf('92',plain,
    ( ( v3_pre_topc @ sk_B_1 @ sk_A )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['19'])).

thf('93',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('94',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X24 ) @ X23 ) @ X24 )
      | ( v4_pre_topc @ X23 @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t29_tops_1])).

thf('95',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
    | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('98',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_subset_1 @ X15 @ ( k3_subset_1 @ X15 @ X14 ) )
        = X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('99',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('101',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
    = sk_B_1 ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,
    ( ( v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['95','96','101'])).

thf('103',plain,
    ( ( v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['92','102'])).

thf('104',plain,(
    v3_pre_topc @ sk_B_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['70','71'])).

thf('105',plain,(
    v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ),
    inference(simpl_trail,[status(thm)],['103','104'])).

thf('106',plain,(
    v3_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['91','105'])).

thf('107',plain,(
    v4_pre_topc @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['80','106'])).

thf('108',plain,
    ( ( u1_struct_0 @ sk_A )
    = sk_B_1 ),
    inference(demod,[status(thm)],['74','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('110',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('111',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('112',plain,(
    $false ),
    inference(demod,[status(thm)],['13','108','109','110','111'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Z8gOFrgJtk
% 0.16/0.39  % Computer   : n023.cluster.edu
% 0.16/0.39  % Model      : x86_64 x86_64
% 0.16/0.39  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.39  % Memory     : 8042.1875MB
% 0.16/0.39  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.39  % CPULimit   : 60
% 0.16/0.39  % DateTime   : Tue Dec  1 14:14:51 EST 2020
% 0.16/0.39  % CPUTime    : 
% 0.16/0.39  % Running portfolio for 600 s
% 0.16/0.39  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.39  % Number of cores: 8
% 0.16/0.39  % Python version: Python 3.6.8
% 0.16/0.40  % Running in FO mode
% 0.37/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.58  % Solved by: fo/fo7.sh
% 0.37/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.58  % done 254 iterations in 0.101s
% 0.37/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.58  % SZS output start Refutation
% 0.37/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.58  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.37/0.58  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.37/0.58  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.37/0.58  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.37/0.58  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.37/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.58  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.37/0.58  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.37/0.58  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.37/0.58  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.37/0.58  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.37/0.58  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.37/0.58  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.37/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.58  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.37/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.58  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.37/0.58  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.37/0.58  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.37/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.58  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.37/0.58  thf(t61_tex_2, conjecture,
% 0.37/0.58    (![A:$i]:
% 0.37/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.37/0.58         ( l1_pre_topc @ A ) ) =>
% 0.37/0.58       ( ![B:$i]:
% 0.37/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.58           ( ~( ( ( v3_pre_topc @ B @ A ) | ( v4_pre_topc @ B @ A ) ) & 
% 0.37/0.58                ( v3_tex_2 @ B @ A ) & 
% 0.37/0.58                ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.37/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.58    (~( ![A:$i]:
% 0.37/0.58        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.37/0.58            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.37/0.58          ( ![B:$i]:
% 0.37/0.58            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.58              ( ~( ( ( v3_pre_topc @ B @ A ) | ( v4_pre_topc @ B @ A ) ) & 
% 0.37/0.58                   ( v3_tex_2 @ B @ A ) & 
% 0.37/0.58                   ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )),
% 0.37/0.58    inference('cnf.neg', [status(esa)], [t61_tex_2])).
% 0.37/0.58  thf('0', plain,
% 0.37/0.58      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf(fc1_tex_2, axiom,
% 0.37/0.58    (![A:$i,B:$i]:
% 0.37/0.58     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_subset_1 @ B @ A ) & 
% 0.37/0.58         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.37/0.58       ( ~( v1_xboole_0 @ ( k3_subset_1 @ A @ B ) ) ) ))).
% 0.37/0.58  thf('1', plain,
% 0.37/0.58      (![X27 : $i, X28 : $i]:
% 0.37/0.58         ((v1_xboole_0 @ X27)
% 0.37/0.58          | ~ (v1_subset_1 @ X28 @ X27)
% 0.37/0.58          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X27))
% 0.37/0.58          | ~ (v1_xboole_0 @ (k3_subset_1 @ X27 @ X28)))),
% 0.37/0.58      inference('cnf', [status(esa)], [fc1_tex_2])).
% 0.37/0.58  thf('2', plain,
% 0.37/0.58      ((~ (v1_xboole_0 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))
% 0.37/0.58        | ~ (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.37/0.58        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['0', '1'])).
% 0.37/0.58  thf('3', plain,
% 0.37/0.58      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf(d5_subset_1, axiom,
% 0.37/0.58    (![A:$i,B:$i]:
% 0.37/0.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.37/0.58       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.37/0.58  thf('4', plain,
% 0.37/0.58      (![X10 : $i, X11 : $i]:
% 0.37/0.58         (((k3_subset_1 @ X10 @ X11) = (k4_xboole_0 @ X10 @ X11))
% 0.37/0.58          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X10)))),
% 0.37/0.58      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.37/0.58  thf('5', plain,
% 0.37/0.58      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)
% 0.37/0.58         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1))),
% 0.37/0.58      inference('sup-', [status(thm)], ['3', '4'])).
% 0.37/0.58  thf('6', plain, ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('7', plain,
% 0.37/0.58      ((~ (v1_xboole_0 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1))
% 0.37/0.58        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.58      inference('demod', [status(thm)], ['2', '5', '6'])).
% 0.37/0.58  thf('8', plain,
% 0.37/0.58      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf(cc4_subset_1, axiom,
% 0.37/0.58    (![A:$i]:
% 0.37/0.58     ( ( v1_xboole_0 @ A ) =>
% 0.37/0.58       ( ![B:$i]:
% 0.37/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.37/0.58           ( ~( v1_subset_1 @ B @ A ) ) ) ) ))).
% 0.37/0.58  thf('9', plain,
% 0.37/0.58      (![X16 : $i, X17 : $i]:
% 0.37/0.58         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 0.37/0.58          | ~ (v1_subset_1 @ X16 @ X17)
% 0.37/0.58          | ~ (v1_xboole_0 @ X17))),
% 0.37/0.58      inference('cnf', [status(esa)], [cc4_subset_1])).
% 0.37/0.58  thf('10', plain,
% 0.37/0.58      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.58        | ~ (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['8', '9'])).
% 0.37/0.58  thf('11', plain, ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('12', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.37/0.58      inference('demod', [status(thm)], ['10', '11'])).
% 0.37/0.58  thf('13', plain,
% 0.37/0.58      (~ (v1_xboole_0 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1))),
% 0.37/0.58      inference('clc', [status(thm)], ['7', '12'])).
% 0.37/0.58  thf('14', plain,
% 0.37/0.58      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf(t52_pre_topc, axiom,
% 0.37/0.58    (![A:$i]:
% 0.37/0.58     ( ( l1_pre_topc @ A ) =>
% 0.37/0.58       ( ![B:$i]:
% 0.37/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.58           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.37/0.58             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.37/0.58               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.37/0.58  thf('15', plain,
% 0.37/0.58      (![X21 : $i, X22 : $i]:
% 0.37/0.58         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.37/0.58          | ~ (v4_pre_topc @ X21 @ X22)
% 0.37/0.58          | ((k2_pre_topc @ X22 @ X21) = (X21))
% 0.37/0.58          | ~ (l1_pre_topc @ X22))),
% 0.37/0.58      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.37/0.58  thf('16', plain,
% 0.37/0.58      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.58        | ((k2_pre_topc @ sk_A @ sk_B_1) = (sk_B_1))
% 0.37/0.58        | ~ (v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.37/0.58      inference('sup-', [status(thm)], ['14', '15'])).
% 0.37/0.58  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('18', plain,
% 0.37/0.58      ((((k2_pre_topc @ sk_A @ sk_B_1) = (sk_B_1))
% 0.37/0.58        | ~ (v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.37/0.58      inference('demod', [status(thm)], ['16', '17'])).
% 0.37/0.58  thf('19', plain,
% 0.37/0.58      (((v3_pre_topc @ sk_B_1 @ sk_A) | (v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('20', plain,
% 0.37/0.58      (((v3_pre_topc @ sk_B_1 @ sk_A)) <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.37/0.58      inference('split', [status(esa)], ['19'])).
% 0.37/0.58  thf('21', plain,
% 0.37/0.58      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf(t47_tex_2, axiom,
% 0.37/0.58    (![A:$i]:
% 0.37/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.37/0.58       ( ![B:$i]:
% 0.37/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.58           ( ( ( v3_pre_topc @ B @ A ) & ( v3_tex_2 @ B @ A ) ) =>
% 0.37/0.58             ( v1_tops_1 @ B @ A ) ) ) ) ))).
% 0.37/0.58  thf('22', plain,
% 0.37/0.58      (![X31 : $i, X32 : $i]:
% 0.37/0.58         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.37/0.58          | (v1_tops_1 @ X31 @ X32)
% 0.37/0.58          | ~ (v3_tex_2 @ X31 @ X32)
% 0.37/0.58          | ~ (v3_pre_topc @ X31 @ X32)
% 0.37/0.58          | ~ (l1_pre_topc @ X32)
% 0.37/0.58          | ~ (v2_pre_topc @ X32)
% 0.37/0.58          | (v2_struct_0 @ X32))),
% 0.37/0.58      inference('cnf', [status(esa)], [t47_tex_2])).
% 0.37/0.58  thf('23', plain,
% 0.37/0.58      (((v2_struct_0 @ sk_A)
% 0.37/0.58        | ~ (v2_pre_topc @ sk_A)
% 0.37/0.58        | ~ (l1_pre_topc @ sk_A)
% 0.37/0.58        | ~ (v3_pre_topc @ sk_B_1 @ sk_A)
% 0.37/0.58        | ~ (v3_tex_2 @ sk_B_1 @ sk_A)
% 0.37/0.58        | (v1_tops_1 @ sk_B_1 @ sk_A))),
% 0.37/0.58      inference('sup-', [status(thm)], ['21', '22'])).
% 0.37/0.58  thf('24', plain, ((v2_pre_topc @ sk_A)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('26', plain, ((v3_tex_2 @ sk_B_1 @ sk_A)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('27', plain,
% 0.37/0.58      (((v2_struct_0 @ sk_A)
% 0.37/0.58        | ~ (v3_pre_topc @ sk_B_1 @ sk_A)
% 0.37/0.58        | (v1_tops_1 @ sk_B_1 @ sk_A))),
% 0.37/0.58      inference('demod', [status(thm)], ['23', '24', '25', '26'])).
% 0.37/0.58  thf('28', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('29', plain,
% 0.37/0.58      (((v1_tops_1 @ sk_B_1 @ sk_A) | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.37/0.58      inference('clc', [status(thm)], ['27', '28'])).
% 0.37/0.58  thf('30', plain,
% 0.37/0.58      (((v1_tops_1 @ sk_B_1 @ sk_A)) <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['20', '29'])).
% 0.37/0.58  thf('31', plain,
% 0.37/0.58      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf(d2_tops_3, axiom,
% 0.37/0.58    (![A:$i]:
% 0.37/0.58     ( ( l1_pre_topc @ A ) =>
% 0.37/0.58       ( ![B:$i]:
% 0.37/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.58           ( ( v1_tops_1 @ B @ A ) <=>
% 0.37/0.58             ( ( k2_pre_topc @ A @ B ) = ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.37/0.58  thf('32', plain,
% 0.37/0.58      (![X25 : $i, X26 : $i]:
% 0.37/0.58         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.37/0.58          | ~ (v1_tops_1 @ X25 @ X26)
% 0.37/0.58          | ((k2_pre_topc @ X26 @ X25) = (u1_struct_0 @ X26))
% 0.37/0.58          | ~ (l1_pre_topc @ X26))),
% 0.37/0.58      inference('cnf', [status(esa)], [d2_tops_3])).
% 0.37/0.58  thf('33', plain,
% 0.37/0.58      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.58        | ((k2_pre_topc @ sk_A @ sk_B_1) = (u1_struct_0 @ sk_A))
% 0.37/0.58        | ~ (v1_tops_1 @ sk_B_1 @ sk_A))),
% 0.37/0.58      inference('sup-', [status(thm)], ['31', '32'])).
% 0.37/0.58  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('35', plain,
% 0.37/0.58      ((((k2_pre_topc @ sk_A @ sk_B_1) = (u1_struct_0 @ sk_A))
% 0.37/0.58        | ~ (v1_tops_1 @ sk_B_1 @ sk_A))),
% 0.37/0.58      inference('demod', [status(thm)], ['33', '34'])).
% 0.37/0.58  thf('36', plain,
% 0.37/0.58      ((((k2_pre_topc @ sk_A @ sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.37/0.58         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['30', '35'])).
% 0.37/0.58  thf('37', plain,
% 0.37/0.58      (((v4_pre_topc @ sk_B_1 @ sk_A)) <= (((v4_pre_topc @ sk_B_1 @ sk_A)))),
% 0.37/0.58      inference('split', [status(esa)], ['19'])).
% 0.37/0.58  thf('38', plain,
% 0.37/0.58      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf(t24_tdlat_3, axiom,
% 0.37/0.58    (![A:$i]:
% 0.37/0.58     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.37/0.58       ( ( v3_tdlat_3 @ A ) <=>
% 0.37/0.58         ( ![B:$i]:
% 0.37/0.58           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.58             ( ( v4_pre_topc @ B @ A ) => ( v3_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.37/0.58  thf('39', plain,
% 0.37/0.58      (![X29 : $i, X30 : $i]:
% 0.37/0.58         (~ (v3_tdlat_3 @ X29)
% 0.37/0.58          | ~ (v4_pre_topc @ X30 @ X29)
% 0.37/0.58          | (v3_pre_topc @ X30 @ X29)
% 0.37/0.58          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.37/0.58          | ~ (l1_pre_topc @ X29)
% 0.37/0.58          | ~ (v2_pre_topc @ X29))),
% 0.37/0.58      inference('cnf', [status(esa)], [t24_tdlat_3])).
% 0.37/0.58  thf('40', plain,
% 0.37/0.58      ((~ (v2_pre_topc @ sk_A)
% 0.37/0.58        | ~ (l1_pre_topc @ sk_A)
% 0.37/0.58        | (v3_pre_topc @ sk_B_1 @ sk_A)
% 0.37/0.58        | ~ (v4_pre_topc @ sk_B_1 @ sk_A)
% 0.37/0.58        | ~ (v3_tdlat_3 @ sk_A))),
% 0.37/0.58      inference('sup-', [status(thm)], ['38', '39'])).
% 0.37/0.58  thf('41', plain, ((v2_pre_topc @ sk_A)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('43', plain, ((v3_tdlat_3 @ sk_A)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('44', plain,
% 0.37/0.58      (((v3_pre_topc @ sk_B_1 @ sk_A) | ~ (v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.37/0.58      inference('demod', [status(thm)], ['40', '41', '42', '43'])).
% 0.37/0.58  thf('45', plain,
% 0.37/0.58      (((v3_pre_topc @ sk_B_1 @ sk_A)) <= (((v4_pre_topc @ sk_B_1 @ sk_A)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['37', '44'])).
% 0.37/0.58  thf('46', plain,
% 0.37/0.58      (((v1_tops_1 @ sk_B_1 @ sk_A) | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.37/0.58      inference('clc', [status(thm)], ['27', '28'])).
% 0.37/0.58  thf('47', plain,
% 0.37/0.58      (((v1_tops_1 @ sk_B_1 @ sk_A)) <= (((v4_pre_topc @ sk_B_1 @ sk_A)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['45', '46'])).
% 0.37/0.58  thf('48', plain,
% 0.37/0.58      ((((k2_pre_topc @ sk_A @ sk_B_1) = (u1_struct_0 @ sk_A))
% 0.37/0.58        | ~ (v1_tops_1 @ sk_B_1 @ sk_A))),
% 0.37/0.58      inference('demod', [status(thm)], ['33', '34'])).
% 0.37/0.58  thf('49', plain,
% 0.37/0.58      ((((k2_pre_topc @ sk_A @ sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.37/0.58         <= (((v4_pre_topc @ sk_B_1 @ sk_A)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['47', '48'])).
% 0.37/0.58  thf('50', plain,
% 0.37/0.58      (((v4_pre_topc @ sk_B_1 @ sk_A)) <= (((v4_pre_topc @ sk_B_1 @ sk_A)))),
% 0.37/0.58      inference('split', [status(esa)], ['19'])).
% 0.37/0.58  thf('51', plain,
% 0.37/0.58      ((((k2_pre_topc @ sk_A @ sk_B_1) = (sk_B_1))
% 0.37/0.58        | ~ (v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.37/0.58      inference('demod', [status(thm)], ['16', '17'])).
% 0.37/0.58  thf('52', plain,
% 0.37/0.58      ((((k2_pre_topc @ sk_A @ sk_B_1) = (sk_B_1)))
% 0.37/0.58         <= (((v4_pre_topc @ sk_B_1 @ sk_A)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['50', '51'])).
% 0.37/0.58  thf('53', plain,
% 0.37/0.58      ((((u1_struct_0 @ sk_A) = (sk_B_1))) <= (((v4_pre_topc @ sk_B_1 @ sk_A)))),
% 0.37/0.58      inference('sup+', [status(thm)], ['49', '52'])).
% 0.37/0.58  thf('54', plain,
% 0.37/0.58      (~ (v1_xboole_0 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1))),
% 0.37/0.58      inference('clc', [status(thm)], ['7', '12'])).
% 0.37/0.58  thf('55', plain,
% 0.37/0.58      ((~ (v1_xboole_0 @ (k4_xboole_0 @ sk_B_1 @ sk_B_1)))
% 0.37/0.58         <= (((v4_pre_topc @ sk_B_1 @ sk_A)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['53', '54'])).
% 0.37/0.58  thf(d10_xboole_0, axiom,
% 0.37/0.58    (![A:$i,B:$i]:
% 0.37/0.58     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.37/0.58  thf('56', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.37/0.58      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.37/0.58  thf('57', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.37/0.58      inference('simplify', [status(thm)], ['56'])).
% 0.37/0.58  thf(t28_xboole_1, axiom,
% 0.37/0.58    (![A:$i,B:$i]:
% 0.37/0.58     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.37/0.58  thf('58', plain,
% 0.37/0.58      (![X8 : $i, X9 : $i]:
% 0.37/0.58         (((k3_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_tarski @ X8 @ X9))),
% 0.37/0.58      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.37/0.58  thf('59', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.37/0.58      inference('sup-', [status(thm)], ['57', '58'])).
% 0.37/0.58  thf(t100_xboole_1, axiom,
% 0.37/0.58    (![A:$i,B:$i]:
% 0.37/0.58     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.37/0.58  thf('60', plain,
% 0.37/0.58      (![X6 : $i, X7 : $i]:
% 0.37/0.58         ((k4_xboole_0 @ X6 @ X7)
% 0.37/0.58           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.37/0.58      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.58  thf('61', plain,
% 0.37/0.58      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.37/0.58      inference('sup+', [status(thm)], ['59', '60'])).
% 0.37/0.58  thf('62', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.37/0.58      inference('simplify', [status(thm)], ['56'])).
% 0.37/0.58  thf(l32_xboole_1, axiom,
% 0.37/0.58    (![A:$i,B:$i]:
% 0.37/0.58     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.37/0.58  thf('63', plain,
% 0.37/0.58      (![X3 : $i, X5 : $i]:
% 0.37/0.58         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.37/0.58      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.37/0.58  thf('64', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.37/0.58      inference('sup-', [status(thm)], ['62', '63'])).
% 0.37/0.58  thf('65', plain,
% 0.37/0.58      (![X6 : $i, X7 : $i]:
% 0.37/0.58         ((k4_xboole_0 @ X6 @ X7)
% 0.37/0.58           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.37/0.58      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.58  thf('66', plain,
% 0.37/0.58      (![X0 : $i]:
% 0.37/0.58         ((k1_xboole_0) = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X0)))),
% 0.37/0.58      inference('sup+', [status(thm)], ['64', '65'])).
% 0.37/0.58  thf('67', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.37/0.58      inference('sup-', [status(thm)], ['57', '58'])).
% 0.37/0.58  thf('68', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.37/0.58      inference('demod', [status(thm)], ['66', '67'])).
% 0.37/0.58  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.37/0.58  thf('69', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.37/0.58      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.37/0.58  thf('70', plain, (~ ((v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.37/0.58      inference('demod', [status(thm)], ['55', '61', '68', '69'])).
% 0.37/0.58  thf('71', plain,
% 0.37/0.58      (((v3_pre_topc @ sk_B_1 @ sk_A)) | ((v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.37/0.58      inference('split', [status(esa)], ['19'])).
% 0.37/0.58  thf('72', plain, (((v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.37/0.58      inference('sat_resolution*', [status(thm)], ['70', '71'])).
% 0.37/0.58  thf('73', plain, (((k2_pre_topc @ sk_A @ sk_B_1) = (u1_struct_0 @ sk_A))),
% 0.37/0.58      inference('simpl_trail', [status(thm)], ['36', '72'])).
% 0.37/0.58  thf('74', plain,
% 0.37/0.58      ((((u1_struct_0 @ sk_A) = (sk_B_1)) | ~ (v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.37/0.58      inference('demod', [status(thm)], ['18', '73'])).
% 0.37/0.58  thf('75', plain,
% 0.37/0.58      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf(t29_tops_1, axiom,
% 0.37/0.58    (![A:$i]:
% 0.37/0.58     ( ( l1_pre_topc @ A ) =>
% 0.37/0.58       ( ![B:$i]:
% 0.37/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.58           ( ( v4_pre_topc @ B @ A ) <=>
% 0.37/0.58             ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.37/0.58  thf('76', plain,
% 0.37/0.58      (![X23 : $i, X24 : $i]:
% 0.37/0.58         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.37/0.58          | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X24) @ X23) @ X24)
% 0.37/0.58          | (v4_pre_topc @ X23 @ X24)
% 0.37/0.58          | ~ (l1_pre_topc @ X24))),
% 0.37/0.58      inference('cnf', [status(esa)], [t29_tops_1])).
% 0.37/0.58  thf('77', plain,
% 0.37/0.58      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.58        | (v4_pre_topc @ sk_B_1 @ sk_A)
% 0.37/0.58        | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A))),
% 0.37/0.58      inference('sup-', [status(thm)], ['75', '76'])).
% 0.37/0.58  thf('78', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('79', plain,
% 0.37/0.58      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)
% 0.37/0.58         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1))),
% 0.37/0.58      inference('sup-', [status(thm)], ['3', '4'])).
% 0.37/0.58  thf('80', plain,
% 0.37/0.58      (((v4_pre_topc @ sk_B_1 @ sk_A)
% 0.37/0.58        | ~ (v3_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A))),
% 0.37/0.58      inference('demod', [status(thm)], ['77', '78', '79'])).
% 0.37/0.58  thf('81', plain,
% 0.37/0.58      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf(dt_k3_subset_1, axiom,
% 0.37/0.58    (![A:$i,B:$i]:
% 0.37/0.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.37/0.58       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.37/0.58  thf('82', plain,
% 0.37/0.58      (![X12 : $i, X13 : $i]:
% 0.37/0.58         ((m1_subset_1 @ (k3_subset_1 @ X12 @ X13) @ (k1_zfmisc_1 @ X12))
% 0.37/0.58          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12)))),
% 0.37/0.58      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.37/0.58  thf('83', plain,
% 0.37/0.58      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.37/0.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['81', '82'])).
% 0.37/0.58  thf('84', plain,
% 0.37/0.58      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)
% 0.37/0.58         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1))),
% 0.37/0.58      inference('sup-', [status(thm)], ['3', '4'])).
% 0.37/0.58  thf('85', plain,
% 0.37/0.58      ((m1_subset_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.37/0.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.58      inference('demod', [status(thm)], ['83', '84'])).
% 0.37/0.58  thf('86', plain,
% 0.37/0.58      (![X29 : $i, X30 : $i]:
% 0.37/0.58         (~ (v3_tdlat_3 @ X29)
% 0.37/0.58          | ~ (v4_pre_topc @ X30 @ X29)
% 0.37/0.58          | (v3_pre_topc @ X30 @ X29)
% 0.37/0.58          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.37/0.58          | ~ (l1_pre_topc @ X29)
% 0.37/0.58          | ~ (v2_pre_topc @ X29))),
% 0.37/0.58      inference('cnf', [status(esa)], [t24_tdlat_3])).
% 0.37/0.58  thf('87', plain,
% 0.37/0.58      ((~ (v2_pre_topc @ sk_A)
% 0.37/0.58        | ~ (l1_pre_topc @ sk_A)
% 0.37/0.58        | (v3_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 0.37/0.58        | ~ (v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 0.37/0.58        | ~ (v3_tdlat_3 @ sk_A))),
% 0.37/0.58      inference('sup-', [status(thm)], ['85', '86'])).
% 0.37/0.58  thf('88', plain, ((v2_pre_topc @ sk_A)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('89', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('90', plain, ((v3_tdlat_3 @ sk_A)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('91', plain,
% 0.37/0.58      (((v3_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 0.37/0.58        | ~ (v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A))),
% 0.37/0.58      inference('demod', [status(thm)], ['87', '88', '89', '90'])).
% 0.37/0.58  thf('92', plain,
% 0.37/0.58      (((v3_pre_topc @ sk_B_1 @ sk_A)) <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.37/0.58      inference('split', [status(esa)], ['19'])).
% 0.37/0.58  thf('93', plain,
% 0.37/0.58      ((m1_subset_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.37/0.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.58      inference('demod', [status(thm)], ['83', '84'])).
% 0.37/0.58  thf('94', plain,
% 0.37/0.58      (![X23 : $i, X24 : $i]:
% 0.37/0.58         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.37/0.58          | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X24) @ X23) @ X24)
% 0.37/0.58          | (v4_pre_topc @ X23 @ X24)
% 0.37/0.58          | ~ (l1_pre_topc @ X24))),
% 0.37/0.58      inference('cnf', [status(esa)], [t29_tops_1])).
% 0.37/0.58  thf('95', plain,
% 0.37/0.58      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.58        | (v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 0.37/0.58        | ~ (v3_pre_topc @ 
% 0.37/0.58             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.58              (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1)) @ 
% 0.37/0.58             sk_A))),
% 0.37/0.58      inference('sup-', [status(thm)], ['93', '94'])).
% 0.37/0.58  thf('96', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('97', plain,
% 0.37/0.58      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf(involutiveness_k3_subset_1, axiom,
% 0.37/0.58    (![A:$i,B:$i]:
% 0.37/0.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.37/0.58       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.37/0.58  thf('98', plain,
% 0.37/0.58      (![X14 : $i, X15 : $i]:
% 0.37/0.58         (((k3_subset_1 @ X15 @ (k3_subset_1 @ X15 @ X14)) = (X14))
% 0.37/0.58          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 0.37/0.58      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.37/0.58  thf('99', plain,
% 0.37/0.58      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.58         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)) = (sk_B_1))),
% 0.37/0.58      inference('sup-', [status(thm)], ['97', '98'])).
% 0.37/0.58  thf('100', plain,
% 0.37/0.58      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)
% 0.37/0.58         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1))),
% 0.37/0.58      inference('sup-', [status(thm)], ['3', '4'])).
% 0.37/0.58  thf('101', plain,
% 0.37/0.58      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.58         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1)) = (sk_B_1))),
% 0.37/0.58      inference('demod', [status(thm)], ['99', '100'])).
% 0.37/0.58  thf('102', plain,
% 0.37/0.58      (((v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 0.37/0.58        | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.37/0.58      inference('demod', [status(thm)], ['95', '96', '101'])).
% 0.37/0.58  thf('103', plain,
% 0.37/0.58      (((v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A))
% 0.37/0.58         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['92', '102'])).
% 0.37/0.58  thf('104', plain, (((v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.37/0.58      inference('sat_resolution*', [status(thm)], ['70', '71'])).
% 0.37/0.58  thf('105', plain,
% 0.37/0.58      ((v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)),
% 0.37/0.58      inference('simpl_trail', [status(thm)], ['103', '104'])).
% 0.37/0.58  thf('106', plain,
% 0.37/0.58      ((v3_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)),
% 0.37/0.58      inference('demod', [status(thm)], ['91', '105'])).
% 0.37/0.58  thf('107', plain, ((v4_pre_topc @ sk_B_1 @ sk_A)),
% 0.37/0.58      inference('demod', [status(thm)], ['80', '106'])).
% 0.37/0.58  thf('108', plain, (((u1_struct_0 @ sk_A) = (sk_B_1))),
% 0.37/0.58      inference('demod', [status(thm)], ['74', '107'])).
% 0.37/0.58  thf('109', plain,
% 0.37/0.58      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.37/0.58      inference('sup+', [status(thm)], ['59', '60'])).
% 0.37/0.58  thf('110', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.37/0.58      inference('demod', [status(thm)], ['66', '67'])).
% 0.37/0.58  thf('111', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.37/0.58      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.37/0.58  thf('112', plain, ($false),
% 0.37/0.58      inference('demod', [status(thm)], ['13', '108', '109', '110', '111'])).
% 0.37/0.58  
% 0.37/0.58  % SZS output end Refutation
% 0.37/0.58  
% 0.37/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
