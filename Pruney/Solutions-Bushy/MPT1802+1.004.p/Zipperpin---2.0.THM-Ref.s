%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1802+1.004 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lKi2U2kQqO

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:54:17 EST 2020

% Result     : Theorem 0.96s
% Output     : Refutation 0.96s
% Verified   : 
% Statistics : Number of formulae       :  328 (3247 expanded)
%              Number of leaves         :   53 ( 948 expanded)
%              Depth                    :   28
%              Number of atoms          : 3321 (68171 expanded)
%              Number of equality atoms :   95 ( 593 expanded)
%              Maximal formula depth    :   23 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k9_tmap_1_type,type,(
    k9_tmap_1: $i > $i > $i )).

thf(k6_tmap_1_type,type,(
    k6_tmap_1: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_funct_2_type,type,(
    r1_funct_2: $i > $i > $i > $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(r1_tsep_1_type,type,(
    r1_tsep_1: $i > $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k8_tmap_1_type,type,(
    k8_tmap_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k7_tmap_1_type,type,(
    k7_tmap_1: $i > $i > $i )).

thf(k5_tmap_1_type,type,(
    k5_tmap_1: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(t118_tmap_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ( ( r1_tsep_1 @ B @ C )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ C ) )
                   => ( r1_tmap_1 @ C @ ( k8_tmap_1 @ A @ B ) @ ( k2_tmap_1 @ A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ C ) @ D ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( m1_pre_topc @ B @ A ) )
           => ! [C: $i] :
                ( ( ~ ( v2_struct_0 @ C )
                  & ( m1_pre_topc @ C @ A ) )
               => ( ( r1_tsep_1 @ B @ C )
                 => ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ C ) )
                     => ( r1_tmap_1 @ C @ ( k8_tmap_1 @ A @ B ) @ ( k2_tmap_1 @ A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ C ) @ D ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t118_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    r1_tsep_1 @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_tsep_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_struct_0 @ A )
        & ( l1_struct_0 @ B ) )
     => ( ( r1_tsep_1 @ A @ B )
       => ( r1_tsep_1 @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X51: $i,X52: $i] :
      ( ~ ( l1_struct_0 @ X51 )
      | ~ ( l1_struct_0 @ X52 )
      | ( r1_tsep_1 @ X52 @ X51 )
      | ~ ( r1_tsep_1 @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('4',plain,
    ( ( r1_tsep_1 @ sk_C @ sk_B )
    | ~ ( l1_struct_0 @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('6',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_pre_topc @ X24 @ X25 )
      | ( l1_pre_topc @ X24 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('7',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['7','8'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('10',plain,(
    ! [X23: $i] :
      ( ( l1_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('11',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_pre_topc @ X24 @ X25 )
      | ( l1_pre_topc @ X24 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('14',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X23: $i] :
      ( ( l1_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('18',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    r1_tsep_1 @ sk_C @ sk_B ),
    inference(demod,[status(thm)],['4','11','18'])).

thf(d3_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_struct_0 @ B )
         => ( ( r1_tsep_1 @ A @ B )
          <=> ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) )).

thf('20',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( l1_struct_0 @ X5 )
      | ~ ( r1_tsep_1 @ X6 @ X5 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('21',plain,
    ( ~ ( l1_struct_0 @ sk_C )
    | ( r1_xboole_0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['9','10'])).

thf('23',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['16','17'])).

thf('24',plain,(
    r1_xboole_0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('26',plain,(
    ! [X60: $i,X61: $i] :
      ( ~ ( m1_pre_topc @ X60 @ X61 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X60 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X61 ) ) )
      | ~ ( l1_pre_topc @ X61 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('27',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf(t109_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ( ( r1_xboole_0 @ ( u1_struct_0 @ C ) @ B )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ C ) )
                   => ( r1_tmap_1 @ C @ ( k6_tmap_1 @ A @ B ) @ ( k2_tmap_1 @ A @ ( k6_tmap_1 @ A @ B ) @ ( k7_tmap_1 @ A @ B ) @ C ) @ D ) ) ) ) ) ) )).

thf('30',plain,(
    ! [X53: $i,X54: $i,X55: $i,X56: $i] :
      ( ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X54 ) ) )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X55 ) @ X53 )
      | ~ ( m1_subset_1 @ X56 @ ( u1_struct_0 @ X55 ) )
      | ( r1_tmap_1 @ X55 @ ( k6_tmap_1 @ X54 @ X53 ) @ ( k2_tmap_1 @ X54 @ ( k6_tmap_1 @ X54 @ X53 ) @ ( k7_tmap_1 @ X54 @ X53 ) @ X55 ) @ X56 )
      | ~ ( m1_pre_topc @ X55 @ X54 )
      | ( v2_struct_0 @ X55 )
      | ~ ( l1_pre_topc @ X54 )
      | ~ ( v2_pre_topc @ X54 )
      | ( v2_struct_0 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t109_tmap_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tmap_1 @ X0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( k2_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ X0 ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tmap_1 @ X0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( k2_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ X0 ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf(abstractness_v1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v1_pre_topc @ A )
       => ( A
          = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_pre_topc @ X0 )
      | ( X0
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf('36',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf(dt_k5_tmap_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k5_tmap_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('37',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( m1_subset_1 @ ( k5_tmap_1 @ X13 @ X14 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_tmap_1])).

thf('38',plain,
    ( ( m1_subset_1 @ ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( m1_subset_1 @ ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    m1_subset_1 @ ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf(free_g1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i,D: $i] :
          ( ( ( g1_pre_topc @ A @ B )
            = ( g1_pre_topc @ C @ D ) )
         => ( ( A = C )
            & ( B = D ) ) ) ) )).

thf('44',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( ( g1_pre_topc @ X33 @ X34 )
       != ( g1_pre_topc @ X31 @ X32 ) )
      | ( X34 = X32 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
        = X0 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
       != ( g1_pre_topc @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf(d9_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k6_tmap_1 @ A @ B )
            = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( k5_tmap_1 @ A @ B ) ) ) ) ) )).

thf('47',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( ( k6_tmap_1 @ X12 @ X11 )
        = ( g1_pre_topc @ ( u1_struct_0 @ X12 ) @ ( k5_tmap_1 @ X12 @ X11 ) ) )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d9_tmap_1])).

thf('48',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
        = X0 )
      | ( ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
       != ( g1_pre_topc @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['45','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
       != X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ( ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
        = ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['35','54'])).

thf('56',plain,
    ( ( ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
      = ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf(dt_k6_tmap_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( v1_pre_topc @ ( k6_tmap_1 @ A @ B ) )
        & ( v2_pre_topc @ ( k6_tmap_1 @ A @ B ) )
        & ( l1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) ) ) )).

thf('58',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( l1_pre_topc @ ( k6_tmap_1 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_tmap_1])).

thf('59',plain,
    ( ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    l1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('65',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('66',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( v1_pre_topc @ ( k6_tmap_1 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_tmap_1])).

thf('67',plain,
    ( ( v1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( v1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
    = ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('simplify_reflect+',[status(thm)],['56','64','72'])).

thf('74',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf(t114_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ( ( ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) )
              = ( u1_struct_0 @ A ) )
            & ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( C
                    = ( u1_struct_0 @ B ) )
                 => ( ( u1_pre_topc @ ( k8_tmap_1 @ A @ B ) )
                    = ( k5_tmap_1 @ A @ C ) ) ) ) ) ) ) )).

thf('75',plain,(
    ! [X57: $i,X58: $i,X59: $i] :
      ( ( v2_struct_0 @ X57 )
      | ~ ( m1_pre_topc @ X57 @ X58 )
      | ~ ( m1_subset_1 @ X59 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X58 ) ) )
      | ( ( u1_pre_topc @ ( k8_tmap_1 @ X58 @ X57 ) )
        = ( k5_tmap_1 @ X58 @ X59 ) )
      | ( X59
       != ( u1_struct_0 @ X57 ) )
      | ~ ( l1_pre_topc @ X58 )
      | ~ ( v2_pre_topc @ X58 )
      | ( v2_struct_0 @ X58 ) ) ),
    inference(cnf,[status(esa)],[t114_tmap_1])).

thf('76',plain,(
    ! [X57: $i,X58: $i] :
      ( ( v2_struct_0 @ X58 )
      | ~ ( v2_pre_topc @ X58 )
      | ~ ( l1_pre_topc @ X58 )
      | ( ( u1_pre_topc @ ( k8_tmap_1 @ X58 @ X57 ) )
        = ( k5_tmap_1 @ X58 @ ( u1_struct_0 @ X57 ) ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X57 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X58 ) ) )
      | ~ ( m1_pre_topc @ X57 @ X58 )
      | ( v2_struct_0 @ X57 ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['74','76'])).

thf('78',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['77','78','79','80'])).

thf('82',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['81','82'])).

thf('84',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['83','84'])).

thf('86',plain,
    ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['73','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( v1_pre_topc @ X0 )
      | ( X0
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf('88',plain,
    ( ( ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
      = ( g1_pre_topc @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) @ ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) )
    | ~ ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( v1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( v1_pre_topc @ X0 )
      | ( X0
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf('90',plain,(
    m1_subset_1 @ ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('91',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( ( g1_pre_topc @ X33 @ X34 )
       != ( g1_pre_topc @ X31 @ X32 ) )
      | ( X33 = X31 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( u1_struct_0 @ sk_A )
        = X0 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
       != ( g1_pre_topc @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,
    ( ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( u1_struct_0 @ sk_A )
        = X0 )
      | ( ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
       != ( g1_pre_topc @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
       != X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ sk_A )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['89','94'])).

thf('96',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    l1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('98',plain,(
    v1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('99',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('simplify_reflect+',[status(thm)],['96','97','98'])).

thf('100',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    ! [X57: $i,X58: $i] :
      ( ( v2_struct_0 @ X57 )
      | ~ ( m1_pre_topc @ X57 @ X58 )
      | ( ( u1_struct_0 @ ( k8_tmap_1 @ X58 @ X57 ) )
        = ( u1_struct_0 @ X58 ) )
      | ~ ( l1_pre_topc @ X58 )
      | ~ ( v2_pre_topc @ X58 )
      | ( v2_struct_0 @ X58 ) ) ),
    inference(cnf,[status(esa)],[t114_tmap_1])).

thf('102',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['102','103','104'])).

thf('106',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['105','106'])).

thf('108',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ~ ( v1_pre_topc @ X0 )
      | ( X0
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf('111',plain,
    ( ( ( k8_tmap_1 @ sk_A @ sk_B )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) )
    | ~ ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['109','110'])).

thf('112',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k8_tmap_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_pre_topc @ B @ A ) )
     => ( ( v1_pre_topc @ ( k8_tmap_1 @ A @ B ) )
        & ( v2_pre_topc @ ( k8_tmap_1 @ A @ B ) )
        & ( l1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) ) ) )).

thf('113',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 )
      | ~ ( m1_pre_topc @ X20 @ X19 )
      | ( l1_pre_topc @ ( k8_tmap_1 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('114',plain,
    ( ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['114','115','116'])).

thf('118',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['117','118'])).

thf('120',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 )
      | ~ ( m1_pre_topc @ X20 @ X19 )
      | ( v1_pre_topc @ ( k8_tmap_1 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('122',plain,
    ( ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,
    ( ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['122','123','124'])).

thf('126',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['125','126'])).

thf('128',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['111','119','127'])).

thf('129',plain,(
    l1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('130',plain,(
    v1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('131',plain,
    ( ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
    = ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['88','99','128','129','130'])).

thf('132',plain,
    ( ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
    = ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['88','99','128','129','130'])).

thf('133',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['107','108'])).

thf(d12_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) ) ) )
             => ( ( C
                  = ( k9_tmap_1 @ A @ B ) )
              <=> ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                   => ( ( D
                        = ( u1_struct_0 @ B ) )
                     => ( r1_funct_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ D ) ) @ C @ ( k7_tmap_1 @ A @ D ) ) ) ) ) ) ) ) )).

thf('134',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_pre_topc @ X1 @ X2 )
      | ( X3
       != ( k9_tmap_1 @ X2 @ X1 ) )
      | ( X4
       != ( u1_struct_0 @ X1 ) )
      | ( r1_funct_2 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X2 @ X1 ) ) @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X2 @ X4 ) ) @ X3 @ ( k7_tmap_1 @ X2 @ X4 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X2 @ X1 ) ) ) ) )
      | ~ ( v1_funct_2 @ X3 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d12_tmap_1])).

thf('135',plain,(
    ! [X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v1_funct_1 @ ( k9_tmap_1 @ X2 @ X1 ) )
      | ~ ( v1_funct_2 @ ( k9_tmap_1 @ X2 @ X1 ) @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X2 @ X1 ) ) )
      | ~ ( m1_subset_1 @ ( k9_tmap_1 @ X2 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X2 @ X1 ) ) ) ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ( r1_funct_2 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X2 @ X1 ) ) @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X2 @ ( u1_struct_0 @ X1 ) ) ) @ ( k9_tmap_1 @ X2 @ X1 ) @ ( k7_tmap_1 @ X2 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ X2 ) ) ),
    inference(simplify,[status(thm)],['134'])).

thf('136',plain,
    ( ~ ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['133','135'])).

thf('137',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['107','108'])).

thf('139',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('140',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['107','108'])).

thf('141',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k9_tmap_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_pre_topc @ B @ A ) )
     => ( ( v1_funct_1 @ ( k9_tmap_1 @ A @ B ) )
        & ( v1_funct_2 @ ( k9_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) )
        & ( m1_subset_1 @ ( k9_tmap_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) ) ) ) ) )).

thf('142',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_pre_topc @ X22 @ X21 )
      | ( v1_funct_1 @ ( k9_tmap_1 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_tmap_1])).

thf('143',plain,
    ( ( v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,
    ( ( v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['143','144','145'])).

thf('147',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['146','147'])).

thf('149',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,
    ( ~ ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['136','137','138','139','140','148','149','150'])).

thf('152',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_pre_topc @ X22 @ X21 )
      | ( m1_subset_1 @ ( k9_tmap_1 @ X21 @ X22 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X21 @ X22 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_tmap_1])).

thf('154',plain,
    ( ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['107','108'])).

thf('156',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,
    ( ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['154','155','156','157'])).

thf('159',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['158','159'])).

thf('161',plain,
    ( ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
    = ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['88','99','128','129','130'])).

thf('162',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['107','108'])).

thf('163',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_pre_topc @ X22 @ X21 )
      | ( v1_funct_2 @ ( k9_tmap_1 @ X21 @ X22 ) @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_tmap_1])).

thf('165',plain,
    ( ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['107','108'])).

thf('167',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,
    ( ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['165','166','167','168'])).

thf('170',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,(
    v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['169','170'])).

thf('172',plain,
    ( ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['151','160','161','162','171'])).

thf('173',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,(
    r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['172','173'])).

thf('175',plain,(
    m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['158','159'])).

thf(redefinition_r1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ~ ( v1_xboole_0 @ B )
        & ~ ( v1_xboole_0 @ D )
        & ( v1_funct_1 @ E )
        & ( v1_funct_2 @ E @ A @ B )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( v1_funct_2 @ F @ C @ D )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( r1_funct_2 @ A @ B @ C @ D @ E @ F )
      <=> ( E = F ) ) ) )).

thf('176',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ~ ( v1_funct_2 @ X39 @ X40 @ X41 )
      | ~ ( v1_funct_1 @ X39 )
      | ( v1_xboole_0 @ X42 )
      | ( v1_xboole_0 @ X41 )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_2 @ X43 @ X44 @ X42 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X42 ) ) )
      | ( X39 = X43 )
      | ~ ( r1_funct_2 @ X40 @ X41 @ X44 @ X42 @ X39 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_funct_2])).

thf('177',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ X2 @ X1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 )
      | ( ( k9_tmap_1 @ sk_A @ sk_B )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_2 @ X0 @ X2 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ X1 )
      | ~ ( v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['175','176'])).

thf('178',plain,(
    v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['146','147'])).

thf('179',plain,(
    v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['169','170'])).

thf('180',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ X2 @ X1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 )
      | ( ( k9_tmap_1 @ sk_A @ sk_B )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_2 @ X0 @ X2 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['177','178','179'])).

thf('181',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( v1_funct_2 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k9_tmap_1 @ sk_A @ sk_B )
      = ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['174','180'])).

thf('182',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf(dt_k7_tmap_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( v1_funct_1 @ ( k7_tmap_1 @ A @ B ) )
        & ( v1_funct_2 @ ( k7_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) )
        & ( m1_subset_1 @ ( k7_tmap_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) ) ) ) ) )).

thf('183',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( v1_funct_1 @ ( k7_tmap_1 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_tmap_1])).

thf('184',plain,
    ( ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['182','183'])).

thf('185',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,
    ( ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['184','185','186'])).

thf('188',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,(
    v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['187','188'])).

thf('190',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('191',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( v1_funct_2 @ ( k7_tmap_1 @ X17 @ X18 ) @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_tmap_1])).

thf('192',plain,
    ( ( v1_funct_2 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['190','191'])).

thf('193',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('simplify_reflect+',[status(thm)],['96','97','98'])).

thf('194',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,
    ( ( v1_funct_2 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['192','193','194','195'])).

thf('197',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,(
    v1_funct_2 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['196','197'])).

thf('199',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('200',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( m1_subset_1 @ ( k7_tmap_1 @ X17 @ X18 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X17 @ X18 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_tmap_1])).

thf('201',plain,
    ( ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['199','200'])).

thf('202',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('simplify_reflect+',[status(thm)],['96','97','98'])).

thf('203',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('205',plain,
    ( ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['201','202','203','204'])).

thf('206',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,(
    m1_subset_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['205','206'])).

thf('208',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k9_tmap_1 @ sk_A @ sk_B )
      = ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['181','189','198','207'])).

thf('209',plain,
    ( ( ( k9_tmap_1 @ sk_A @ sk_B )
      = ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['208'])).

thf('210',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('simplify_reflect+',[status(thm)],['96','97','98'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('211',plain,(
    ! [X26: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('212',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['210','211'])).

thf('213',plain,(
    l1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('214',plain,(
    ! [X23: $i] :
      ( ( l1_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('215',plain,(
    l1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['213','214'])).

thf('216',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['212','215'])).

thf('217',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf(fc4_tmap_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ~ ( v2_struct_0 @ ( k6_tmap_1 @ A @ B ) )
        & ( v1_pre_topc @ ( k6_tmap_1 @ A @ B ) )
        & ( v2_pre_topc @ ( k6_tmap_1 @ A @ B ) ) ) ) )).

thf('218',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( v2_struct_0 @ ( k6_tmap_1 @ X27 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_tmap_1])).

thf('219',plain,
    ( ~ ( v2_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['217','218'])).

thf('220',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('221',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('222',plain,
    ( ~ ( v2_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['219','220','221'])).

thf('223',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('224',plain,(
    ~ ( v2_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['222','223'])).

thf('225',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['216','224'])).

thf('226',plain,
    ( ( k9_tmap_1 @ sk_A @ sk_B )
    = ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['209','225'])).

thf('227',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tmap_1 @ X0 @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['34','131','132','226'])).

thf('228',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ( r1_tmap_1 @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) @ X0 )
      | ~ ( m1_pre_topc @ sk_C @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','227'])).

thf('229',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('230',plain,(
    m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['158','159'])).

thf('231',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['107','108'])).

thf(d4_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ! [D: $i] :
                  ( ( m1_pre_topc @ D @ A )
                 => ( ( k2_tmap_1 @ A @ B @ C @ D )
                    = ( k2_partfun1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ ( u1_struct_0 @ D ) ) ) ) ) ) ) )).

thf('232',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( v2_struct_0 @ X7 )
      | ~ ( v2_pre_topc @ X7 )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( m1_pre_topc @ X8 @ X9 )
      | ( ( k2_tmap_1 @ X9 @ X7 @ X10 @ X8 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X9 ) @ ( u1_struct_0 @ X7 ) @ X10 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X9 ) @ ( u1_struct_0 @ X7 ) ) ) )
      | ~ ( v1_funct_2 @ X10 @ ( u1_struct_0 @ X9 ) @ ( u1_struct_0 @ X7 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('233',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
      | ( ( k2_tmap_1 @ X0 @ ( k8_tmap_1 @ sk_A @ sk_B ) @ X1 @ X2 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) @ X1 @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( m1_pre_topc @ X2 @ X0 )
      | ~ ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['231','232'])).

thf('234',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['107','108'])).

thf('235',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['107','108'])).

thf('236',plain,(
    l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['117','118'])).

thf('237',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('238',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 )
      | ~ ( m1_pre_topc @ X20 @ X19 )
      | ( v2_pre_topc @ ( k8_tmap_1 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('239',plain,
    ( ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['237','238'])).

thf('240',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('241',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('242',plain,
    ( ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['239','240','241'])).

thf('243',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('244',plain,(
    v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['242','243'])).

thf('245',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_tmap_1 @ X0 @ ( k8_tmap_1 @ sk_A @ sk_B ) @ X1 @ X2 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ X1 @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( m1_pre_topc @ X2 @ X0 )
      | ( v2_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['233','234','235','236','244'])).

thf('246',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['230','245'])).

thf('247',plain,(
    m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['158','159'])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('248',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ~ ( v1_funct_1 @ X35 )
      | ( ( k2_partfun1 @ X36 @ X37 @ X35 @ X38 )
        = ( k7_relat_1 @ X35 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('249',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 )
        = ( k7_relat_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 ) )
      | ~ ( v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['247','248'])).

thf('250',plain,(
    v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['146','147'])).

thf('251',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 )
      = ( k7_relat_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['249','250'])).

thf('252',plain,(
    v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['169','170'])).

thf('253',plain,(
    v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['146','147'])).

thf('254',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('255',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('256',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 )
        = ( k7_relat_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['246','251','252','253','254','255'])).

thf('257',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C )
      = ( k7_relat_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['229','256'])).

thf('258',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('259',plain,
    ( ( v2_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C )
      = ( k7_relat_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['257','258'])).

thf('260',plain,(
    ~ ( v2_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['222','223'])).

thf('261',plain,
    ( ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
    = ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['88','99','128','129','130'])).

thf('262',plain,(
    ~ ( v2_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['260','261'])).

thf('263',plain,
    ( ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C )
    = ( k7_relat_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['259','262'])).

thf('264',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('265',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ( r1_tmap_1 @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k7_relat_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) @ X0 )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['228','263','264'])).

thf('266',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k7_relat_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['1','265'])).

thf('267',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('268',plain,
    ( ( r1_tmap_1 @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k7_relat_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) @ sk_D_1 )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['266','267'])).

thf('269',plain,(
    ~ ( r1_tmap_1 @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('270',plain,
    ( ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C )
    = ( k7_relat_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['259','262'])).

thf('271',plain,(
    ~ ( r1_tmap_1 @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k7_relat_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) @ sk_D_1 ) ),
    inference(demod,[status(thm)],['269','270'])).

thf('272',plain,(
    v2_struct_0 @ sk_C ),
    inference(clc,[status(thm)],['268','271'])).

thf('273',plain,(
    $false ),
    inference(demod,[status(thm)],['0','272'])).


%------------------------------------------------------------------------------
