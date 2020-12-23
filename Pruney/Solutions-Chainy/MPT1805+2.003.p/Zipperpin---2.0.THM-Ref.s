%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.azEeahNsuW

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:01 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  279 (8983 expanded)
%              Number of leaves         :   38 (2600 expanded)
%              Depth                    :   32
%              Number of atoms          : 3458 (313909 expanded)
%              Number of equality atoms :   87 (1470 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k8_tmap_1_type,type,(
    k8_tmap_1: $i > $i > $i )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_funct_2_type,type,(
    r1_funct_2: $i > $i > $i > $i > $i > $i > $o )).

thf(k7_tmap_1_type,type,(
    k7_tmap_1: $i > $i > $i )).

thf(k6_tmap_1_type,type,(
    k6_tmap_1: $i > $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k5_tmap_1_type,type,(
    k5_tmap_1: $i > $i > $i )).

thf(k9_tmap_1_type,type,(
    k9_tmap_1: $i > $i > $i )).

thf(t121_tmap_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ B ) )
            & ( v1_funct_2 @ ( k2_tmap_1 @ A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ B ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) )
            & ( v5_pre_topc @ ( k2_tmap_1 @ A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ B ) @ B @ ( k8_tmap_1 @ A @ B ) )
            & ( m1_subset_1 @ ( k2_tmap_1 @ A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( m1_pre_topc @ B @ A ) )
           => ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ B ) )
              & ( v1_funct_2 @ ( k2_tmap_1 @ A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ B ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) )
              & ( v5_pre_topc @ ( k2_tmap_1 @ A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ B ) @ B @ ( k8_tmap_1 @ A @ B ) )
              & ( m1_subset_1 @ ( k2_tmap_1 @ A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t121_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('2',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_pre_topc @ X28 @ X29 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X28 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('3',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(dt_k7_tmap_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( v1_funct_1 @ ( k7_tmap_1 @ A @ B ) )
        & ( v1_funct_2 @ ( k7_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) )
        & ( m1_subset_1 @ ( k7_tmap_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) ) ) ) ) )).

thf('6',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( m1_subset_1 @ ( k7_tmap_1 @ X19 @ X20 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X19 @ X20 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_tmap_1])).

thf('7',plain,
    ( ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(d10_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k7_tmap_1 @ A @ B )
            = ( k6_partfun1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('9',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( ( k7_tmap_1 @ X10 @ X9 )
        = ( k6_partfun1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_tmap_1])).

thf('10',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
      = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
      = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('14',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t104_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) )
              = ( u1_struct_0 @ A ) )
            & ( ( u1_pre_topc @ ( k6_tmap_1 @ A @ B ) )
              = ( k5_tmap_1 @ A @ B ) ) ) ) ) )).

thf('17',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( ( u1_struct_0 @ ( k6_tmap_1 @ X24 @ X23 ) )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t104_tmap_1])).

thf('18',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('24',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( m1_subset_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['7','15','23','24','25'])).

thf('27',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_subset_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['26','27'])).

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

thf('30',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) )
      | ~ ( v1_funct_2 @ X3 @ X4 @ X5 )
      | ~ ( v1_funct_1 @ X3 )
      | ( v1_xboole_0 @ X6 )
      | ( v1_xboole_0 @ X5 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_funct_2 @ X7 @ X8 @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X6 ) ) )
      | ( r1_funct_2 @ X4 @ X5 @ X8 @ X6 @ X3 @ X7 )
      | ( X3 != X7 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_funct_2])).

thf('31',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( r1_funct_2 @ X4 @ X5 @ X8 @ X6 @ X7 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X6 ) ) )
      | ~ ( v1_funct_2 @ X7 @ X8 @ X6 )
      | ( v1_xboole_0 @ X5 )
      | ( v1_xboole_0 @ X6 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_funct_2 @ X7 @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ X1 @ X0 )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_funct_2 @ X1 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['29','31'])).

thf('33',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('34',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( v1_funct_1 @ ( k7_tmap_1 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_tmap_1])).

thf('35',plain,
    ( ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('42',plain,(
    v1_funct_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('44',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( v1_funct_2 @ ( k7_tmap_1 @ X19 @ X20 ) @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_tmap_1])).

thf('45',plain,
    ( ( v1_funct_2 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('47',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('48',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['45','46','47','48','49'])).

thf('51',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ X1 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ( r1_funct_2 @ X1 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['32','42','52'])).

thf('54',plain,
    ( ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','53'])).

thf('55',plain,(
    v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('56',plain,
    ( ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    m1_subset_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('59',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('60',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(d11_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( ( v1_pre_topc @ C )
                & ( v2_pre_topc @ C )
                & ( l1_pre_topc @ C ) )
             => ( ( C
                  = ( k8_tmap_1 @ A @ B ) )
              <=> ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                   => ( ( D
                        = ( u1_struct_0 @ B ) )
                     => ( C
                        = ( k6_tmap_1 @ A @ D ) ) ) ) ) ) ) ) )).

thf('61',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ( X13
       != ( k8_tmap_1 @ X12 @ X11 ) )
      | ( X14
       != ( u1_struct_0 @ X11 ) )
      | ( X13
        = ( k6_tmap_1 @ X12 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ~ ( v1_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d11_tmap_1])).

thf('62',plain,(
    ! [X11: $i,X12: $i] :
      ( ( v2_struct_0 @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v1_pre_topc @ ( k8_tmap_1 @ X12 @ X11 ) )
      | ~ ( v2_pre_topc @ ( k8_tmap_1 @ X12 @ X11 ) )
      | ~ ( l1_pre_topc @ ( k8_tmap_1 @ X12 @ X11 ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X11 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( ( k8_tmap_1 @ X12 @ X11 )
        = ( k6_tmap_1 @ X12 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( m1_pre_topc @ X11 @ X12 ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( ( k8_tmap_1 @ sk_A @ sk_B )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['60','62'])).

thf('64',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
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

thf('66',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_pre_topc @ X22 @ X21 )
      | ( l1_pre_topc @ ( k8_tmap_1 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('67',plain,
    ( ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
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
    ( ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('73',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_pre_topc @ X22 @ X21 )
      | ( v2_pre_topc @ ( k8_tmap_1 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('75',plain,
    ( ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('79',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['78','79'])).

thf('81',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_pre_topc @ X22 @ X21 )
      | ( v1_pre_topc @ ( k8_tmap_1 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('83',plain,
    ( ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('87',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['86','87'])).

thf('89',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( ( k8_tmap_1 @ sk_A @ sk_B )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['63','64','72','80','88','89','90'])).

thf('92',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['91','92'])).

thf('94',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['59','93'])).

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

thf('95',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X15 @ X16 )
      | ( ( sk_D_1 @ X17 @ X15 @ X16 )
        = ( u1_struct_0 @ X15 ) )
      | ( X17
        = ( k9_tmap_1 @ X16 @ X15 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X16 @ X15 ) ) ) ) )
      | ~ ( v1_funct_2 @ X17 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X16 @ X15 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d12_tmap_1])).

thf('96',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
      | ( X0
        = ( k9_tmap_1 @ sk_A @ sk_B ) )
      | ( ( sk_D_1 @ X0 @ sk_B @ sk_A )
        = ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['59','93'])).

thf('100',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( X0
        = ( k9_tmap_1 @ sk_A @ sk_B ) )
      | ( ( sk_D_1 @ X0 @ sk_B @ sk_A )
        = ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['96','97','98','99','100'])).

thf('102',plain,
    ( ( ( sk_D_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_A )
      = ( u1_struct_0 @ sk_B ) )
    | ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['58','101'])).

thf('103',plain,(
    v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('104',plain,(
    v1_funct_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('105',plain,
    ( ( ( sk_D_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_A )
      = ( u1_struct_0 @ sk_B ) )
    | ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['102','103','104'])).

thf('106',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ( ( sk_D_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_A )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['105','106'])).

thf('108',plain,
    ( ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ( ( sk_D_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_A )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['105','106'])).

thf('109',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X15 @ X16 )
      | ~ ( r1_funct_2 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X16 @ X15 ) ) @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X16 @ ( sk_D_1 @ X17 @ X15 @ X16 ) ) ) @ X17 @ ( k7_tmap_1 @ X16 @ ( sk_D_1 @ X17 @ X15 @ X16 ) ) )
      | ( X17
        = ( k9_tmap_1 @ X16 @ X15 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X16 @ X15 ) ) ) ) )
      | ~ ( v1_funct_2 @ X17 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X16 @ X15 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d12_tmap_1])).

thf('110',plain,
    ( ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k7_tmap_1 @ sk_A @ ( sk_D_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_A ) ) )
    | ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
    | ~ ( m1_subset_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) )
    | ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['59','93'])).

thf('112',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['91','92'])).

thf('113',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['59','93'])).

thf('114',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    v1_funct_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('117',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['59','93'])).

thf('118',plain,(
    v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('119',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['59','93'])).

thf('120',plain,(
    m1_subset_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('121',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k7_tmap_1 @ sk_A @ ( sk_D_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_A ) ) )
    | ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['110','111','112','113','114','115','116','117','118','119','120','121'])).

thf('123',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k7_tmap_1 @ sk_A @ ( sk_D_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['122'])).

thf('124',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,
    ( ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k7_tmap_1 @ sk_A @ ( sk_D_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_A ) ) )
    | ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['123','124'])).

thf('126',plain,
    ( ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['107','125'])).

thf('127',plain,
    ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('128',plain,
    ( ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,
    ( ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['128'])).

thf('130',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['57','129'])).

thf('131',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['59','93'])).

thf('132',plain,
    ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,
    ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) )
   <= ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(split,[status(esa)],['132'])).

thf('134',plain,
    ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['131','133'])).

thf('135',plain,
    ( ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['130','134'])).

thf('136',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t112_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ( ( ( u1_struct_0 @ C )
                  = B )
               => ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ ( k6_tmap_1 @ A @ B ) @ ( k7_tmap_1 @ A @ B ) @ C ) )
                  & ( v1_funct_2 @ ( k2_tmap_1 @ A @ ( k6_tmap_1 @ A @ B ) @ ( k7_tmap_1 @ A @ B ) @ C ) @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) )
                  & ( v5_pre_topc @ ( k2_tmap_1 @ A @ ( k6_tmap_1 @ A @ B ) @ ( k7_tmap_1 @ A @ B ) @ C ) @ C @ ( k6_tmap_1 @ A @ B ) )
                  & ( m1_subset_1 @ ( k2_tmap_1 @ A @ ( k6_tmap_1 @ A @ B ) @ ( k7_tmap_1 @ A @ B ) @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) ) ) ) ) ) ) ) )).

thf('137',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( ( u1_struct_0 @ X27 )
       != X25 )
      | ( v1_funct_2 @ ( k2_tmap_1 @ X26 @ ( k6_tmap_1 @ X26 @ X25 ) @ ( k7_tmap_1 @ X26 @ X25 ) @ X27 ) @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X26 @ X25 ) ) )
      | ~ ( m1_pre_topc @ X27 @ X26 )
      | ( v2_struct_0 @ X27 )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t112_tmap_1])).

thf('138',plain,(
    ! [X26: $i,X27: $i] :
      ( ( v2_struct_0 @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ~ ( l1_pre_topc @ X26 )
      | ( v2_struct_0 @ X27 )
      | ~ ( m1_pre_topc @ X27 @ X26 )
      | ( v1_funct_2 @ ( k2_tmap_1 @ X26 @ ( k6_tmap_1 @ X26 @ ( u1_struct_0 @ X27 ) ) @ ( k7_tmap_1 @ X26 @ ( u1_struct_0 @ X27 ) ) @ X27 ) @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X26 @ ( u1_struct_0 @ X27 ) ) ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X27 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) ) ) ),
    inference(simplify,[status(thm)],['137'])).

thf('139',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['136','138'])).

thf('140',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['91','92'])).

thf('141',plain,
    ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('142',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['91','92'])).

thf('143',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['59','93'])).

thf('144',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['139','140','141','142','143','144','145','146'])).

thf('148',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['147','148'])).

thf('150',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['149','150'])).

thf('152',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['57','129'])).

thf('153',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['59','93'])).

thf('154',plain,
    ( ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
   <= ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['132'])).

thf('155',plain,
    ( ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,
    ( ( ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['152','155'])).

thf('157',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['151','156'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('158',plain,(
    ! [X2: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X2 ) )
      | ~ ( l1_struct_0 @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('159',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('161',plain,(
    ! [X0: $i] :
      ( ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('162',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['159','162'])).

thf('164',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('167',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( ( u1_struct_0 @ X27 )
       != X25 )
      | ( v1_funct_1 @ ( k2_tmap_1 @ X26 @ ( k6_tmap_1 @ X26 @ X25 ) @ ( k7_tmap_1 @ X26 @ X25 ) @ X27 ) )
      | ~ ( m1_pre_topc @ X27 @ X26 )
      | ( v2_struct_0 @ X27 )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t112_tmap_1])).

thf('168',plain,(
    ! [X26: $i,X27: $i] :
      ( ( v2_struct_0 @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ~ ( l1_pre_topc @ X26 )
      | ( v2_struct_0 @ X27 )
      | ~ ( m1_pre_topc @ X27 @ X26 )
      | ( v1_funct_1 @ ( k2_tmap_1 @ X26 @ ( k6_tmap_1 @ X26 @ ( u1_struct_0 @ X27 ) ) @ ( k7_tmap_1 @ X26 @ ( u1_struct_0 @ X27 ) ) @ X27 ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X27 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) ) ) ),
    inference(simplify,[status(thm)],['167'])).

thf('169',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['166','168'])).

thf('170',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['91','92'])).

thf('171',plain,
    ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('172',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['169','170','171','172','173','174'])).

thf('176',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['175','176'])).

thf('178',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B ) ),
    inference(clc,[status(thm)],['177','178'])).

thf('180',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['57','129'])).

thf('181',plain,
    ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) )
   <= ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['132'])).

thf('182',plain,
    ( ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['180','181'])).

thf('183',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['179','182'])).

thf('184',plain,(
    ! [X2: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X2 ) )
      | ~ ( l1_struct_0 @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('185',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['183','184'])).

thf('186',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['160','161'])).

thf('187',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['185','186'])).

thf('188',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['187','188'])).

thf('190',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('191',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( ( u1_struct_0 @ X27 )
       != X25 )
      | ( v5_pre_topc @ ( k2_tmap_1 @ X26 @ ( k6_tmap_1 @ X26 @ X25 ) @ ( k7_tmap_1 @ X26 @ X25 ) @ X27 ) @ X27 @ ( k6_tmap_1 @ X26 @ X25 ) )
      | ~ ( m1_pre_topc @ X27 @ X26 )
      | ( v2_struct_0 @ X27 )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t112_tmap_1])).

thf('192',plain,(
    ! [X26: $i,X27: $i] :
      ( ( v2_struct_0 @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ~ ( l1_pre_topc @ X26 )
      | ( v2_struct_0 @ X27 )
      | ~ ( m1_pre_topc @ X27 @ X26 )
      | ( v5_pre_topc @ ( k2_tmap_1 @ X26 @ ( k6_tmap_1 @ X26 @ ( u1_struct_0 @ X27 ) ) @ ( k7_tmap_1 @ X26 @ ( u1_struct_0 @ X27 ) ) @ X27 ) @ X27 @ ( k6_tmap_1 @ X26 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X27 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) ) ) ),
    inference(simplify,[status(thm)],['191'])).

thf('193',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_B ) @ sk_B @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['190','192'])).

thf('194',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['91','92'])).

thf('195',plain,
    ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('196',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['91','92'])).

thf('197',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B ) @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['193','194','195','196','197','198','199'])).

thf('201',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('202',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B ) @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['200','201'])).

thf('203',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,(
    v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B ) @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['202','203'])).

thf('205',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['57','129'])).

thf('206',plain,
    ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['132'])).

thf('207',plain,
    ( ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B ) @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['205','206'])).

thf('208',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['204','207'])).

thf('209',plain,(
    ! [X2: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X2 ) )
      | ~ ( l1_struct_0 @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('210',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['208','209'])).

thf('211',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['160','161'])).

thf('212',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['210','211'])).

thf('213',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('214',plain,(
    v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['212','213'])).

thf('215',plain,
    ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['132'])).

thf('216',plain,(
    ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sat_resolution*',[status(thm)],['165','189','214','215'])).

thf('217',plain,
    ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['135','216'])).

thf('218',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('219',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( ( u1_struct_0 @ X27 )
       != X25 )
      | ( m1_subset_1 @ ( k2_tmap_1 @ X26 @ ( k6_tmap_1 @ X26 @ X25 ) @ ( k7_tmap_1 @ X26 @ X25 ) @ X27 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X26 @ X25 ) ) ) ) )
      | ~ ( m1_pre_topc @ X27 @ X26 )
      | ( v2_struct_0 @ X27 )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t112_tmap_1])).

thf('220',plain,(
    ! [X26: $i,X27: $i] :
      ( ( v2_struct_0 @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ~ ( l1_pre_topc @ X26 )
      | ( v2_struct_0 @ X27 )
      | ~ ( m1_pre_topc @ X27 @ X26 )
      | ( m1_subset_1 @ ( k2_tmap_1 @ X26 @ ( k6_tmap_1 @ X26 @ ( u1_struct_0 @ X27 ) ) @ ( k7_tmap_1 @ X26 @ ( u1_struct_0 @ X27 ) ) @ X27 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X26 @ ( u1_struct_0 @ X27 ) ) ) ) ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X27 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) ) ) ),
    inference(simplify,[status(thm)],['219'])).

thf('221',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ) ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['218','220'])).

thf('222',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['91','92'])).

thf('223',plain,
    ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('224',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['91','92'])).

thf('225',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['59','93'])).

thf('226',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('227',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('228',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('229',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['221','222','223','224','225','226','227','228'])).

thf('230',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('231',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['229','230'])).

thf('232',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('233',plain,(
    m1_subset_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['231','232'])).

thf('234',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['217','233'])).

thf('235',plain,(
    ! [X2: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X2 ) )
      | ~ ( l1_struct_0 @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('236',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['234','235'])).

thf('237',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['160','161'])).

thf('238',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['236','237'])).

thf('239',plain,(
    $false ),
    inference(demod,[status(thm)],['0','238'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.azEeahNsuW
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:33:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.45/0.67  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.67  % Solved by: fo/fo7.sh
% 0.45/0.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.67  % done 230 iterations in 0.210s
% 0.45/0.67  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.67  % SZS output start Refutation
% 0.45/0.67  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.45/0.67  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.45/0.67  thf(k8_tmap_1_type, type, k8_tmap_1: $i > $i > $i).
% 0.45/0.67  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.45/0.67  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.45/0.67  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.45/0.67  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.67  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.45/0.67  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.45/0.67  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.67  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.45/0.67  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.45/0.67  thf(r1_funct_2_type, type, r1_funct_2: $i > $i > $i > $i > $i > $i > $o).
% 0.45/0.67  thf(k7_tmap_1_type, type, k7_tmap_1: $i > $i > $i).
% 0.45/0.67  thf(k6_tmap_1_type, type, k6_tmap_1: $i > $i > $i).
% 0.45/0.67  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.45/0.67  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.45/0.67  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.67  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.45/0.67  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.45/0.67  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.45/0.67  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.45/0.67  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.45/0.67  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.67  thf(k5_tmap_1_type, type, k5_tmap_1: $i > $i > $i).
% 0.45/0.67  thf(k9_tmap_1_type, type, k9_tmap_1: $i > $i > $i).
% 0.45/0.67  thf(t121_tmap_1, conjecture,
% 0.45/0.67    (![A:$i]:
% 0.45/0.67     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.67       ( ![B:$i]:
% 0.45/0.67         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.45/0.67           ( ( v1_funct_1 @
% 0.45/0.67               ( k2_tmap_1 @
% 0.45/0.67                 A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ B ) ) & 
% 0.45/0.67             ( v1_funct_2 @
% 0.45/0.67               ( k2_tmap_1 @
% 0.45/0.67                 A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ B ) @ 
% 0.45/0.67               ( u1_struct_0 @ B ) @ ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) & 
% 0.45/0.67             ( v5_pre_topc @
% 0.45/0.67               ( k2_tmap_1 @
% 0.45/0.67                 A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ B ) @ 
% 0.45/0.67               B @ ( k8_tmap_1 @ A @ B ) ) & 
% 0.45/0.67             ( m1_subset_1 @
% 0.45/0.67               ( k2_tmap_1 @
% 0.45/0.67                 A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ B ) @ 
% 0.45/0.67               ( k1_zfmisc_1 @
% 0.45/0.67                 ( k2_zfmisc_1 @
% 0.45/0.67                   ( u1_struct_0 @ B ) @ 
% 0.45/0.67                   ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) ) ) ) ) ) ))).
% 0.45/0.67  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.67    (~( ![A:$i]:
% 0.45/0.67        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.45/0.67            ( l1_pre_topc @ A ) ) =>
% 0.45/0.67          ( ![B:$i]:
% 0.45/0.67            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.45/0.67              ( ( v1_funct_1 @
% 0.45/0.67                  ( k2_tmap_1 @
% 0.45/0.67                    A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ B ) ) & 
% 0.45/0.67                ( v1_funct_2 @
% 0.45/0.67                  ( k2_tmap_1 @
% 0.45/0.67                    A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ B ) @ 
% 0.45/0.67                  ( u1_struct_0 @ B ) @ ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) & 
% 0.45/0.67                ( v5_pre_topc @
% 0.45/0.67                  ( k2_tmap_1 @
% 0.45/0.67                    A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ B ) @ 
% 0.45/0.67                  B @ ( k8_tmap_1 @ A @ B ) ) & 
% 0.45/0.67                ( m1_subset_1 @
% 0.45/0.67                  ( k2_tmap_1 @
% 0.45/0.67                    A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ B ) @ 
% 0.45/0.67                  ( k1_zfmisc_1 @
% 0.45/0.67                    ( k2_zfmisc_1 @
% 0.45/0.67                      ( u1_struct_0 @ B ) @ 
% 0.45/0.67                      ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) ) ) ) ) ) ) )),
% 0.45/0.67    inference('cnf.neg', [status(esa)], [t121_tmap_1])).
% 0.45/0.67  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('1', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf(t1_tsep_1, axiom,
% 0.45/0.67    (![A:$i]:
% 0.45/0.67     ( ( l1_pre_topc @ A ) =>
% 0.45/0.67       ( ![B:$i]:
% 0.45/0.67         ( ( m1_pre_topc @ B @ A ) =>
% 0.45/0.67           ( m1_subset_1 @
% 0.45/0.67             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.45/0.67  thf('2', plain,
% 0.45/0.67      (![X28 : $i, X29 : $i]:
% 0.45/0.67         (~ (m1_pre_topc @ X28 @ X29)
% 0.45/0.67          | (m1_subset_1 @ (u1_struct_0 @ X28) @ 
% 0.45/0.67             (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.45/0.67          | ~ (l1_pre_topc @ X29))),
% 0.45/0.67      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.45/0.67  thf('3', plain,
% 0.45/0.67      ((~ (l1_pre_topc @ sk_A)
% 0.45/0.67        | (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.67           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.45/0.67      inference('sup-', [status(thm)], ['1', '2'])).
% 0.45/0.67  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('5', plain,
% 0.45/0.67      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.67        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.67      inference('demod', [status(thm)], ['3', '4'])).
% 0.45/0.67  thf(dt_k7_tmap_1, axiom,
% 0.45/0.67    (![A:$i,B:$i]:
% 0.45/0.67     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.45/0.67         ( l1_pre_topc @ A ) & 
% 0.45/0.67         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.45/0.68       ( ( v1_funct_1 @ ( k7_tmap_1 @ A @ B ) ) & 
% 0.45/0.68         ( v1_funct_2 @
% 0.45/0.68           ( k7_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.45/0.68           ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) & 
% 0.45/0.68         ( m1_subset_1 @
% 0.45/0.68           ( k7_tmap_1 @ A @ B ) @ 
% 0.45/0.68           ( k1_zfmisc_1 @
% 0.45/0.68             ( k2_zfmisc_1 @
% 0.45/0.68               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) ) ) ) ))).
% 0.45/0.68  thf('6', plain,
% 0.45/0.68      (![X19 : $i, X20 : $i]:
% 0.45/0.68         (~ (l1_pre_topc @ X19)
% 0.45/0.68          | ~ (v2_pre_topc @ X19)
% 0.45/0.68          | (v2_struct_0 @ X19)
% 0.45/0.68          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.45/0.68          | (m1_subset_1 @ (k7_tmap_1 @ X19 @ X20) @ 
% 0.45/0.68             (k1_zfmisc_1 @ 
% 0.45/0.68              (k2_zfmisc_1 @ (u1_struct_0 @ X19) @ 
% 0.45/0.68               (u1_struct_0 @ (k6_tmap_1 @ X19 @ X20))))))),
% 0.45/0.68      inference('cnf', [status(esa)], [dt_k7_tmap_1])).
% 0.45/0.68  thf('7', plain,
% 0.45/0.68      (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.45/0.68         (k1_zfmisc_1 @ 
% 0.45/0.68          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.68           (u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))))
% 0.45/0.68        | (v2_struct_0 @ sk_A)
% 0.45/0.68        | ~ (v2_pre_topc @ sk_A)
% 0.45/0.68        | ~ (l1_pre_topc @ sk_A))),
% 0.45/0.68      inference('sup-', [status(thm)], ['5', '6'])).
% 0.45/0.68  thf('8', plain,
% 0.45/0.68      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.68        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.68      inference('demod', [status(thm)], ['3', '4'])).
% 0.45/0.68  thf(d10_tmap_1, axiom,
% 0.45/0.68    (![A:$i]:
% 0.45/0.68     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.68       ( ![B:$i]:
% 0.45/0.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.68           ( ( k7_tmap_1 @ A @ B ) = ( k6_partfun1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.45/0.68  thf('9', plain,
% 0.45/0.68      (![X9 : $i, X10 : $i]:
% 0.45/0.68         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.45/0.68          | ((k7_tmap_1 @ X10 @ X9) = (k6_partfun1 @ (u1_struct_0 @ X10)))
% 0.45/0.68          | ~ (l1_pre_topc @ X10)
% 0.45/0.68          | ~ (v2_pre_topc @ X10)
% 0.45/0.68          | (v2_struct_0 @ X10))),
% 0.45/0.68      inference('cnf', [status(esa)], [d10_tmap_1])).
% 0.45/0.68  thf('10', plain,
% 0.45/0.68      (((v2_struct_0 @ sk_A)
% 0.45/0.68        | ~ (v2_pre_topc @ sk_A)
% 0.45/0.68        | ~ (l1_pre_topc @ sk_A)
% 0.45/0.68        | ((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))
% 0.45/0.68            = (k6_partfun1 @ (u1_struct_0 @ sk_A))))),
% 0.45/0.68      inference('sup-', [status(thm)], ['8', '9'])).
% 0.45/0.68  thf('11', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('13', plain,
% 0.45/0.68      (((v2_struct_0 @ sk_A)
% 0.45/0.68        | ((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))
% 0.45/0.68            = (k6_partfun1 @ (u1_struct_0 @ sk_A))))),
% 0.45/0.68      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.45/0.68  thf('14', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('15', plain,
% 0.45/0.68      (((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))
% 0.45/0.68         = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.68      inference('clc', [status(thm)], ['13', '14'])).
% 0.45/0.68  thf('16', plain,
% 0.45/0.68      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.68        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.68      inference('demod', [status(thm)], ['3', '4'])).
% 0.45/0.68  thf(t104_tmap_1, axiom,
% 0.45/0.68    (![A:$i]:
% 0.45/0.68     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.68       ( ![B:$i]:
% 0.45/0.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.68           ( ( ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) = ( u1_struct_0 @ A ) ) & 
% 0.45/0.68             ( ( u1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) = ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.45/0.68  thf('17', plain,
% 0.45/0.68      (![X23 : $i, X24 : $i]:
% 0.45/0.68         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.45/0.68          | ((u1_struct_0 @ (k6_tmap_1 @ X24 @ X23)) = (u1_struct_0 @ X24))
% 0.45/0.68          | ~ (l1_pre_topc @ X24)
% 0.45/0.68          | ~ (v2_pre_topc @ X24)
% 0.45/0.68          | (v2_struct_0 @ X24))),
% 0.45/0.68      inference('cnf', [status(esa)], [t104_tmap_1])).
% 0.45/0.68  thf('18', plain,
% 0.45/0.68      (((v2_struct_0 @ sk_A)
% 0.45/0.68        | ~ (v2_pre_topc @ sk_A)
% 0.45/0.68        | ~ (l1_pre_topc @ sk_A)
% 0.45/0.68        | ((u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.45/0.68            = (u1_struct_0 @ sk_A)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['16', '17'])).
% 0.45/0.68  thf('19', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('21', plain,
% 0.45/0.68      (((v2_struct_0 @ sk_A)
% 0.45/0.68        | ((u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.45/0.68            = (u1_struct_0 @ sk_A)))),
% 0.45/0.68      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.45/0.68  thf('22', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('23', plain,
% 0.45/0.68      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.45/0.68         = (u1_struct_0 @ sk_A))),
% 0.45/0.68      inference('clc', [status(thm)], ['21', '22'])).
% 0.45/0.68  thf('24', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('26', plain,
% 0.45/0.68      (((m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.45/0.68         (k1_zfmisc_1 @ 
% 0.45/0.68          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 0.45/0.68        | (v2_struct_0 @ sk_A))),
% 0.45/0.68      inference('demod', [status(thm)], ['7', '15', '23', '24', '25'])).
% 0.45/0.68  thf('27', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('28', plain,
% 0.45/0.68      ((m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.45/0.68        (k1_zfmisc_1 @ 
% 0.45/0.68         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))),
% 0.45/0.68      inference('clc', [status(thm)], ['26', '27'])).
% 0.45/0.68  thf('29', plain,
% 0.45/0.68      ((m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.45/0.68        (k1_zfmisc_1 @ 
% 0.45/0.68         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))),
% 0.45/0.68      inference('clc', [status(thm)], ['26', '27'])).
% 0.45/0.68  thf(redefinition_r1_funct_2, axiom,
% 0.45/0.68    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.45/0.68     ( ( ( ~( v1_xboole_0 @ B ) ) & ( ~( v1_xboole_0 @ D ) ) & 
% 0.45/0.68         ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ B ) & 
% 0.45/0.68         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.45/0.68         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ C @ D ) & 
% 0.45/0.68         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.45/0.68       ( ( r1_funct_2 @ A @ B @ C @ D @ E @ F ) <=> ( ( E ) = ( F ) ) ) ))).
% 0.45/0.68  thf('30', plain,
% 0.45/0.68      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.45/0.68         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5)))
% 0.45/0.68          | ~ (v1_funct_2 @ X3 @ X4 @ X5)
% 0.45/0.68          | ~ (v1_funct_1 @ X3)
% 0.45/0.68          | (v1_xboole_0 @ X6)
% 0.45/0.68          | (v1_xboole_0 @ X5)
% 0.45/0.68          | ~ (v1_funct_1 @ X7)
% 0.45/0.68          | ~ (v1_funct_2 @ X7 @ X8 @ X6)
% 0.45/0.68          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X6)))
% 0.45/0.68          | (r1_funct_2 @ X4 @ X5 @ X8 @ X6 @ X3 @ X7)
% 0.45/0.68          | ((X3) != (X7)))),
% 0.45/0.68      inference('cnf', [status(esa)], [redefinition_r1_funct_2])).
% 0.45/0.68  thf('31', plain,
% 0.45/0.68      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.45/0.68         ((r1_funct_2 @ X4 @ X5 @ X8 @ X6 @ X7 @ X7)
% 0.45/0.68          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X6)))
% 0.45/0.68          | ~ (v1_funct_2 @ X7 @ X8 @ X6)
% 0.45/0.68          | (v1_xboole_0 @ X5)
% 0.45/0.68          | (v1_xboole_0 @ X6)
% 0.45/0.68          | ~ (v1_funct_1 @ X7)
% 0.45/0.68          | ~ (v1_funct_2 @ X7 @ X4 @ X5)
% 0.45/0.68          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5))))),
% 0.45/0.68      inference('simplify', [status(thm)], ['30'])).
% 0.45/0.68  thf('32', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i]:
% 0.45/0.68         (~ (m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.45/0.68             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 0.45/0.68          | ~ (v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ X1 @ X0)
% 0.45/0.68          | ~ (v1_funct_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)))
% 0.45/0.68          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.45/0.68          | (v1_xboole_0 @ X0)
% 0.45/0.68          | ~ (v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.45/0.68               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.45/0.68          | (r1_funct_2 @ X1 @ X0 @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.68             (u1_struct_0 @ sk_A) @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.45/0.68             (k6_partfun1 @ (u1_struct_0 @ sk_A))))),
% 0.45/0.68      inference('sup-', [status(thm)], ['29', '31'])).
% 0.45/0.68  thf('33', plain,
% 0.45/0.68      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.68        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.68      inference('demod', [status(thm)], ['3', '4'])).
% 0.45/0.68  thf('34', plain,
% 0.45/0.68      (![X19 : $i, X20 : $i]:
% 0.45/0.68         (~ (l1_pre_topc @ X19)
% 0.45/0.68          | ~ (v2_pre_topc @ X19)
% 0.45/0.68          | (v2_struct_0 @ X19)
% 0.45/0.68          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.45/0.68          | (v1_funct_1 @ (k7_tmap_1 @ X19 @ X20)))),
% 0.45/0.68      inference('cnf', [status(esa)], [dt_k7_tmap_1])).
% 0.45/0.68  thf('35', plain,
% 0.45/0.68      (((v1_funct_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.45/0.68        | (v2_struct_0 @ sk_A)
% 0.45/0.68        | ~ (v2_pre_topc @ sk_A)
% 0.45/0.68        | ~ (l1_pre_topc @ sk_A))),
% 0.45/0.68      inference('sup-', [status(thm)], ['33', '34'])).
% 0.45/0.68  thf('36', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('38', plain,
% 0.45/0.68      (((v1_funct_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.45/0.68        | (v2_struct_0 @ sk_A))),
% 0.45/0.68      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.45/0.68  thf('39', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('40', plain, ((v1_funct_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.45/0.68      inference('clc', [status(thm)], ['38', '39'])).
% 0.45/0.68  thf('41', plain,
% 0.45/0.68      (((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))
% 0.45/0.68         = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.68      inference('clc', [status(thm)], ['13', '14'])).
% 0.45/0.68  thf('42', plain, ((v1_funct_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.68      inference('demod', [status(thm)], ['40', '41'])).
% 0.45/0.68  thf('43', plain,
% 0.45/0.68      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.68        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.68      inference('demod', [status(thm)], ['3', '4'])).
% 0.45/0.68  thf('44', plain,
% 0.45/0.68      (![X19 : $i, X20 : $i]:
% 0.45/0.68         (~ (l1_pre_topc @ X19)
% 0.45/0.68          | ~ (v2_pre_topc @ X19)
% 0.45/0.68          | (v2_struct_0 @ X19)
% 0.45/0.68          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.45/0.68          | (v1_funct_2 @ (k7_tmap_1 @ X19 @ X20) @ (u1_struct_0 @ X19) @ 
% 0.45/0.68             (u1_struct_0 @ (k6_tmap_1 @ X19 @ X20))))),
% 0.45/0.68      inference('cnf', [status(esa)], [dt_k7_tmap_1])).
% 0.45/0.68  thf('45', plain,
% 0.45/0.68      (((v1_funct_2 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.45/0.68         (u1_struct_0 @ sk_A) @ 
% 0.45/0.68         (u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))
% 0.45/0.68        | (v2_struct_0 @ sk_A)
% 0.45/0.68        | ~ (v2_pre_topc @ sk_A)
% 0.45/0.68        | ~ (l1_pre_topc @ sk_A))),
% 0.45/0.68      inference('sup-', [status(thm)], ['43', '44'])).
% 0.45/0.68  thf('46', plain,
% 0.45/0.68      (((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))
% 0.45/0.68         = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.68      inference('clc', [status(thm)], ['13', '14'])).
% 0.45/0.68  thf('47', plain,
% 0.45/0.68      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.45/0.68         = (u1_struct_0 @ sk_A))),
% 0.45/0.68      inference('clc', [status(thm)], ['21', '22'])).
% 0.45/0.68  thf('48', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('49', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('50', plain,
% 0.45/0.68      (((v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.45/0.68         (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.45/0.68        | (v2_struct_0 @ sk_A))),
% 0.45/0.68      inference('demod', [status(thm)], ['45', '46', '47', '48', '49'])).
% 0.45/0.68  thf('51', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('52', plain,
% 0.45/0.68      ((v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.45/0.68        (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.45/0.68      inference('clc', [status(thm)], ['50', '51'])).
% 0.45/0.68  thf('53', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i]:
% 0.45/0.68         (~ (m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.45/0.68             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 0.45/0.68          | ~ (v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ X1 @ X0)
% 0.45/0.68          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.45/0.68          | (v1_xboole_0 @ X0)
% 0.45/0.68          | (r1_funct_2 @ X1 @ X0 @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.68             (u1_struct_0 @ sk_A) @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.45/0.68             (k6_partfun1 @ (u1_struct_0 @ sk_A))))),
% 0.45/0.68      inference('demod', [status(thm)], ['32', '42', '52'])).
% 0.45/0.68  thf('54', plain,
% 0.45/0.68      (((r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.68         (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.68         (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.45/0.68         (k6_partfun1 @ (u1_struct_0 @ sk_A)))
% 0.45/0.68        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.45/0.68        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.45/0.68        | ~ (v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.45/0.68             (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['28', '53'])).
% 0.45/0.68  thf('55', plain,
% 0.45/0.68      ((v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.45/0.68        (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.45/0.68      inference('clc', [status(thm)], ['50', '51'])).
% 0.45/0.68  thf('56', plain,
% 0.45/0.68      (((r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.68         (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.68         (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.45/0.68         (k6_partfun1 @ (u1_struct_0 @ sk_A)))
% 0.45/0.68        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.45/0.68        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.68      inference('demod', [status(thm)], ['54', '55'])).
% 0.45/0.68  thf('57', plain,
% 0.45/0.68      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.45/0.68        | (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.68           (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.68           (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.45/0.68           (k6_partfun1 @ (u1_struct_0 @ sk_A))))),
% 0.45/0.68      inference('simplify', [status(thm)], ['56'])).
% 0.45/0.68  thf('58', plain,
% 0.45/0.68      ((m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.45/0.68        (k1_zfmisc_1 @ 
% 0.45/0.68         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))),
% 0.45/0.68      inference('clc', [status(thm)], ['26', '27'])).
% 0.45/0.68  thf('59', plain,
% 0.45/0.68      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.45/0.68         = (u1_struct_0 @ sk_A))),
% 0.45/0.68      inference('clc', [status(thm)], ['21', '22'])).
% 0.45/0.68  thf('60', plain,
% 0.45/0.68      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.68        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.68      inference('demod', [status(thm)], ['3', '4'])).
% 0.45/0.68  thf(d11_tmap_1, axiom,
% 0.45/0.68    (![A:$i]:
% 0.45/0.68     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.68       ( ![B:$i]:
% 0.45/0.68         ( ( m1_pre_topc @ B @ A ) =>
% 0.45/0.68           ( ![C:$i]:
% 0.45/0.68             ( ( ( v1_pre_topc @ C ) & ( v2_pre_topc @ C ) & 
% 0.45/0.68                 ( l1_pre_topc @ C ) ) =>
% 0.45/0.68               ( ( ( C ) = ( k8_tmap_1 @ A @ B ) ) <=>
% 0.45/0.68                 ( ![D:$i]:
% 0.45/0.68                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.68                     ( ( ( D ) = ( u1_struct_0 @ B ) ) =>
% 0.45/0.68                       ( ( C ) = ( k6_tmap_1 @ A @ D ) ) ) ) ) ) ) ) ) ) ))).
% 0.45/0.68  thf('61', plain,
% 0.45/0.68      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.45/0.68         (~ (m1_pre_topc @ X11 @ X12)
% 0.45/0.68          | ((X13) != (k8_tmap_1 @ X12 @ X11))
% 0.45/0.68          | ((X14) != (u1_struct_0 @ X11))
% 0.45/0.68          | ((X13) = (k6_tmap_1 @ X12 @ X14))
% 0.45/0.68          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.45/0.68          | ~ (l1_pre_topc @ X13)
% 0.45/0.68          | ~ (v2_pre_topc @ X13)
% 0.45/0.68          | ~ (v1_pre_topc @ X13)
% 0.45/0.68          | ~ (l1_pre_topc @ X12)
% 0.45/0.68          | ~ (v2_pre_topc @ X12)
% 0.45/0.68          | (v2_struct_0 @ X12))),
% 0.45/0.68      inference('cnf', [status(esa)], [d11_tmap_1])).
% 0.45/0.68  thf('62', plain,
% 0.45/0.68      (![X11 : $i, X12 : $i]:
% 0.45/0.68         ((v2_struct_0 @ X12)
% 0.45/0.68          | ~ (v2_pre_topc @ X12)
% 0.45/0.68          | ~ (l1_pre_topc @ X12)
% 0.45/0.68          | ~ (v1_pre_topc @ (k8_tmap_1 @ X12 @ X11))
% 0.45/0.68          | ~ (v2_pre_topc @ (k8_tmap_1 @ X12 @ X11))
% 0.45/0.68          | ~ (l1_pre_topc @ (k8_tmap_1 @ X12 @ X11))
% 0.45/0.68          | ~ (m1_subset_1 @ (u1_struct_0 @ X11) @ 
% 0.45/0.68               (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.45/0.68          | ((k8_tmap_1 @ X12 @ X11) = (k6_tmap_1 @ X12 @ (u1_struct_0 @ X11)))
% 0.45/0.68          | ~ (m1_pre_topc @ X11 @ X12))),
% 0.45/0.68      inference('simplify', [status(thm)], ['61'])).
% 0.45/0.68  thf('63', plain,
% 0.45/0.68      ((~ (m1_pre_topc @ sk_B @ sk_A)
% 0.45/0.68        | ((k8_tmap_1 @ sk_A @ sk_B)
% 0.45/0.68            = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.45/0.68        | ~ (l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.45/0.68        | ~ (v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.45/0.68        | ~ (v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.45/0.68        | ~ (l1_pre_topc @ sk_A)
% 0.45/0.68        | ~ (v2_pre_topc @ sk_A)
% 0.45/0.68        | (v2_struct_0 @ sk_A))),
% 0.45/0.68      inference('sup-', [status(thm)], ['60', '62'])).
% 0.45/0.68  thf('64', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('65', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf(dt_k8_tmap_1, axiom,
% 0.45/0.68    (![A:$i,B:$i]:
% 0.45/0.68     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.45/0.68         ( l1_pre_topc @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.45/0.68       ( ( v1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) & 
% 0.45/0.68         ( v2_pre_topc @ ( k8_tmap_1 @ A @ B ) ) & 
% 0.45/0.68         ( l1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) ) ))).
% 0.45/0.68  thf('66', plain,
% 0.45/0.68      (![X21 : $i, X22 : $i]:
% 0.45/0.68         (~ (l1_pre_topc @ X21)
% 0.45/0.68          | ~ (v2_pre_topc @ X21)
% 0.45/0.68          | (v2_struct_0 @ X21)
% 0.45/0.68          | ~ (m1_pre_topc @ X22 @ X21)
% 0.45/0.68          | (l1_pre_topc @ (k8_tmap_1 @ X21 @ X22)))),
% 0.45/0.68      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 0.45/0.68  thf('67', plain,
% 0.45/0.68      (((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.45/0.68        | (v2_struct_0 @ sk_A)
% 0.45/0.68        | ~ (v2_pre_topc @ sk_A)
% 0.45/0.68        | ~ (l1_pre_topc @ sk_A))),
% 0.45/0.68      inference('sup-', [status(thm)], ['65', '66'])).
% 0.45/0.68  thf('68', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('69', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('70', plain,
% 0.45/0.68      (((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.45/0.68      inference('demod', [status(thm)], ['67', '68', '69'])).
% 0.45/0.68  thf('71', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('72', plain, ((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.45/0.68      inference('clc', [status(thm)], ['70', '71'])).
% 0.45/0.68  thf('73', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('74', plain,
% 0.45/0.68      (![X21 : $i, X22 : $i]:
% 0.45/0.68         (~ (l1_pre_topc @ X21)
% 0.45/0.68          | ~ (v2_pre_topc @ X21)
% 0.45/0.68          | (v2_struct_0 @ X21)
% 0.45/0.68          | ~ (m1_pre_topc @ X22 @ X21)
% 0.45/0.68          | (v2_pre_topc @ (k8_tmap_1 @ X21 @ X22)))),
% 0.45/0.68      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 0.45/0.68  thf('75', plain,
% 0.45/0.68      (((v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.45/0.68        | (v2_struct_0 @ sk_A)
% 0.45/0.68        | ~ (v2_pre_topc @ sk_A)
% 0.45/0.68        | ~ (l1_pre_topc @ sk_A))),
% 0.45/0.68      inference('sup-', [status(thm)], ['73', '74'])).
% 0.45/0.68  thf('76', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('77', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('78', plain,
% 0.45/0.68      (((v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.45/0.68      inference('demod', [status(thm)], ['75', '76', '77'])).
% 0.45/0.68  thf('79', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('80', plain, ((v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.45/0.68      inference('clc', [status(thm)], ['78', '79'])).
% 0.45/0.68  thf('81', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('82', plain,
% 0.45/0.68      (![X21 : $i, X22 : $i]:
% 0.45/0.68         (~ (l1_pre_topc @ X21)
% 0.45/0.68          | ~ (v2_pre_topc @ X21)
% 0.45/0.68          | (v2_struct_0 @ X21)
% 0.45/0.68          | ~ (m1_pre_topc @ X22 @ X21)
% 0.45/0.68          | (v1_pre_topc @ (k8_tmap_1 @ X21 @ X22)))),
% 0.45/0.68      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 0.45/0.68  thf('83', plain,
% 0.45/0.68      (((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.45/0.68        | (v2_struct_0 @ sk_A)
% 0.45/0.68        | ~ (v2_pre_topc @ sk_A)
% 0.45/0.68        | ~ (l1_pre_topc @ sk_A))),
% 0.45/0.68      inference('sup-', [status(thm)], ['81', '82'])).
% 0.45/0.68  thf('84', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('85', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('86', plain,
% 0.45/0.68      (((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.45/0.68      inference('demod', [status(thm)], ['83', '84', '85'])).
% 0.45/0.68  thf('87', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('88', plain, ((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.45/0.68      inference('clc', [status(thm)], ['86', '87'])).
% 0.45/0.68  thf('89', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('90', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('91', plain,
% 0.45/0.68      ((((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.45/0.68        | (v2_struct_0 @ sk_A))),
% 0.45/0.68      inference('demod', [status(thm)],
% 0.45/0.68                ['63', '64', '72', '80', '88', '89', '90'])).
% 0.45/0.68  thf('92', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('93', plain,
% 0.45/0.68      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.45/0.68      inference('clc', [status(thm)], ['91', '92'])).
% 0.45/0.68  thf('94', plain,
% 0.45/0.68      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.45/0.68      inference('demod', [status(thm)], ['59', '93'])).
% 0.45/0.68  thf(d12_tmap_1, axiom,
% 0.45/0.68    (![A:$i]:
% 0.45/0.68     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.68       ( ![B:$i]:
% 0.45/0.68         ( ( m1_pre_topc @ B @ A ) =>
% 0.45/0.68           ( ![C:$i]:
% 0.45/0.68             ( ( ( v1_funct_1 @ C ) & 
% 0.45/0.68                 ( v1_funct_2 @
% 0.45/0.68                   C @ ( u1_struct_0 @ A ) @ 
% 0.45/0.68                   ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) & 
% 0.45/0.68                 ( m1_subset_1 @
% 0.45/0.68                   C @ 
% 0.45/0.68                   ( k1_zfmisc_1 @
% 0.45/0.68                     ( k2_zfmisc_1 @
% 0.45/0.68                       ( u1_struct_0 @ A ) @ 
% 0.45/0.68                       ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) ) ) ) =>
% 0.45/0.68               ( ( ( C ) = ( k9_tmap_1 @ A @ B ) ) <=>
% 0.45/0.68                 ( ![D:$i]:
% 0.45/0.68                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.68                     ( ( ( D ) = ( u1_struct_0 @ B ) ) =>
% 0.45/0.68                       ( r1_funct_2 @
% 0.45/0.68                         ( u1_struct_0 @ A ) @ 
% 0.45/0.68                         ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) @ 
% 0.45/0.68                         ( u1_struct_0 @ A ) @ 
% 0.45/0.68                         ( u1_struct_0 @ ( k6_tmap_1 @ A @ D ) ) @ C @ 
% 0.45/0.68                         ( k7_tmap_1 @ A @ D ) ) ) ) ) ) ) ) ) ) ))).
% 0.45/0.68  thf('95', plain,
% 0.45/0.68      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.45/0.68         (~ (m1_pre_topc @ X15 @ X16)
% 0.45/0.68          | ((sk_D_1 @ X17 @ X15 @ X16) = (u1_struct_0 @ X15))
% 0.45/0.68          | ((X17) = (k9_tmap_1 @ X16 @ X15))
% 0.45/0.68          | ~ (m1_subset_1 @ X17 @ 
% 0.45/0.68               (k1_zfmisc_1 @ 
% 0.45/0.68                (k2_zfmisc_1 @ (u1_struct_0 @ X16) @ 
% 0.45/0.68                 (u1_struct_0 @ (k8_tmap_1 @ X16 @ X15)))))
% 0.45/0.68          | ~ (v1_funct_2 @ X17 @ (u1_struct_0 @ X16) @ 
% 0.45/0.68               (u1_struct_0 @ (k8_tmap_1 @ X16 @ X15)))
% 0.45/0.68          | ~ (v1_funct_1 @ X17)
% 0.45/0.68          | ~ (l1_pre_topc @ X16)
% 0.45/0.68          | ~ (v2_pre_topc @ X16)
% 0.45/0.68          | (v2_struct_0 @ X16))),
% 0.45/0.68      inference('cnf', [status(esa)], [d12_tmap_1])).
% 0.45/0.68  thf('96', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         (~ (m1_subset_1 @ X0 @ 
% 0.45/0.68             (k1_zfmisc_1 @ 
% 0.45/0.68              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 0.45/0.68          | (v2_struct_0 @ sk_A)
% 0.45/0.68          | ~ (v2_pre_topc @ sk_A)
% 0.45/0.68          | ~ (l1_pre_topc @ sk_A)
% 0.45/0.68          | ~ (v1_funct_1 @ X0)
% 0.45/0.68          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.68               (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.45/0.68          | ((X0) = (k9_tmap_1 @ sk_A @ sk_B))
% 0.45/0.68          | ((sk_D_1 @ X0 @ sk_B @ sk_A) = (u1_struct_0 @ sk_B))
% 0.45/0.68          | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 0.45/0.68      inference('sup-', [status(thm)], ['94', '95'])).
% 0.45/0.68  thf('97', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('98', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('99', plain,
% 0.45/0.68      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.45/0.68      inference('demod', [status(thm)], ['59', '93'])).
% 0.45/0.68  thf('100', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('101', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         (~ (m1_subset_1 @ X0 @ 
% 0.45/0.68             (k1_zfmisc_1 @ 
% 0.45/0.68              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 0.45/0.68          | (v2_struct_0 @ sk_A)
% 0.45/0.68          | ~ (v1_funct_1 @ X0)
% 0.45/0.68          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.45/0.68          | ((X0) = (k9_tmap_1 @ sk_A @ sk_B))
% 0.45/0.68          | ((sk_D_1 @ X0 @ sk_B @ sk_A) = (u1_struct_0 @ sk_B)))),
% 0.45/0.68      inference('demod', [status(thm)], ['96', '97', '98', '99', '100'])).
% 0.45/0.68  thf('102', plain,
% 0.45/0.68      ((((sk_D_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_A)
% 0.45/0.68          = (u1_struct_0 @ sk_B))
% 0.45/0.68        | ((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B))
% 0.45/0.68        | ~ (v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.45/0.68             (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.45/0.68        | ~ (v1_funct_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)))
% 0.45/0.68        | (v2_struct_0 @ sk_A))),
% 0.45/0.68      inference('sup-', [status(thm)], ['58', '101'])).
% 0.45/0.68  thf('103', plain,
% 0.45/0.68      ((v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.45/0.68        (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.45/0.68      inference('clc', [status(thm)], ['50', '51'])).
% 0.45/0.68  thf('104', plain, ((v1_funct_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.68      inference('demod', [status(thm)], ['40', '41'])).
% 0.45/0.68  thf('105', plain,
% 0.45/0.68      ((((sk_D_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_A)
% 0.45/0.68          = (u1_struct_0 @ sk_B))
% 0.45/0.68        | ((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B))
% 0.45/0.68        | (v2_struct_0 @ sk_A))),
% 0.45/0.68      inference('demod', [status(thm)], ['102', '103', '104'])).
% 0.45/0.68  thf('106', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('107', plain,
% 0.45/0.68      ((((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B))
% 0.45/0.68        | ((sk_D_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_A)
% 0.45/0.68            = (u1_struct_0 @ sk_B)))),
% 0.45/0.68      inference('clc', [status(thm)], ['105', '106'])).
% 0.45/0.68  thf('108', plain,
% 0.45/0.68      ((((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B))
% 0.45/0.68        | ((sk_D_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_A)
% 0.45/0.68            = (u1_struct_0 @ sk_B)))),
% 0.45/0.68      inference('clc', [status(thm)], ['105', '106'])).
% 0.45/0.68  thf('109', plain,
% 0.45/0.68      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.45/0.68         (~ (m1_pre_topc @ X15 @ X16)
% 0.45/0.68          | ~ (r1_funct_2 @ (u1_struct_0 @ X16) @ 
% 0.45/0.68               (u1_struct_0 @ (k8_tmap_1 @ X16 @ X15)) @ (u1_struct_0 @ X16) @ 
% 0.45/0.68               (u1_struct_0 @ (k6_tmap_1 @ X16 @ (sk_D_1 @ X17 @ X15 @ X16))) @ 
% 0.45/0.68               X17 @ (k7_tmap_1 @ X16 @ (sk_D_1 @ X17 @ X15 @ X16)))
% 0.45/0.68          | ((X17) = (k9_tmap_1 @ X16 @ X15))
% 0.45/0.68          | ~ (m1_subset_1 @ X17 @ 
% 0.45/0.68               (k1_zfmisc_1 @ 
% 0.45/0.68                (k2_zfmisc_1 @ (u1_struct_0 @ X16) @ 
% 0.45/0.68                 (u1_struct_0 @ (k8_tmap_1 @ X16 @ X15)))))
% 0.45/0.68          | ~ (v1_funct_2 @ X17 @ (u1_struct_0 @ X16) @ 
% 0.45/0.68               (u1_struct_0 @ (k8_tmap_1 @ X16 @ X15)))
% 0.45/0.68          | ~ (v1_funct_1 @ X17)
% 0.45/0.68          | ~ (l1_pre_topc @ X16)
% 0.45/0.68          | ~ (v2_pre_topc @ X16)
% 0.45/0.68          | (v2_struct_0 @ X16))),
% 0.45/0.68      inference('cnf', [status(esa)], [d12_tmap_1])).
% 0.45/0.68  thf('110', plain,
% 0.45/0.68      ((~ (r1_funct_2 @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.68           (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.68           (u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))) @ 
% 0.45/0.68           (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.45/0.68           (k7_tmap_1 @ sk_A @ 
% 0.45/0.68            (sk_D_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_A)))
% 0.45/0.68        | ((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B))
% 0.45/0.68        | (v2_struct_0 @ sk_A)
% 0.45/0.68        | ~ (v2_pre_topc @ sk_A)
% 0.45/0.68        | ~ (l1_pre_topc @ sk_A)
% 0.45/0.68        | ~ (v1_funct_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)))
% 0.45/0.68        | ~ (v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.45/0.68             (u1_struct_0 @ sk_A) @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.45/0.68        | ~ (m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.45/0.68             (k1_zfmisc_1 @ 
% 0.45/0.68              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.68               (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))
% 0.45/0.68        | ((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B))
% 0.45/0.68        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 0.45/0.68      inference('sup-', [status(thm)], ['108', '109'])).
% 0.45/0.68  thf('111', plain,
% 0.45/0.68      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.45/0.68      inference('demod', [status(thm)], ['59', '93'])).
% 0.45/0.68  thf('112', plain,
% 0.45/0.68      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.45/0.68      inference('clc', [status(thm)], ['91', '92'])).
% 0.45/0.68  thf('113', plain,
% 0.45/0.68      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.45/0.68      inference('demod', [status(thm)], ['59', '93'])).
% 0.45/0.68  thf('114', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('115', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('116', plain, ((v1_funct_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.68      inference('demod', [status(thm)], ['40', '41'])).
% 0.45/0.68  thf('117', plain,
% 0.45/0.68      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.45/0.68      inference('demod', [status(thm)], ['59', '93'])).
% 0.45/0.68  thf('118', plain,
% 0.45/0.68      ((v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.45/0.68        (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.45/0.68      inference('clc', [status(thm)], ['50', '51'])).
% 0.45/0.68  thf('119', plain,
% 0.45/0.68      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.45/0.68      inference('demod', [status(thm)], ['59', '93'])).
% 0.45/0.68  thf('120', plain,
% 0.45/0.68      ((m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.45/0.68        (k1_zfmisc_1 @ 
% 0.45/0.68         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))),
% 0.45/0.68      inference('clc', [status(thm)], ['26', '27'])).
% 0.45/0.68  thf('121', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('122', plain,
% 0.45/0.68      ((~ (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.68           (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.68           (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.45/0.68           (k7_tmap_1 @ sk_A @ 
% 0.45/0.68            (sk_D_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_A)))
% 0.45/0.68        | ((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B))
% 0.45/0.68        | (v2_struct_0 @ sk_A)
% 0.45/0.68        | ((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B)))),
% 0.45/0.68      inference('demod', [status(thm)],
% 0.45/0.68                ['110', '111', '112', '113', '114', '115', '116', '117', 
% 0.45/0.68                 '118', '119', '120', '121'])).
% 0.45/0.68  thf('123', plain,
% 0.45/0.68      (((v2_struct_0 @ sk_A)
% 0.45/0.68        | ((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B))
% 0.45/0.68        | ~ (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.68             (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.68             (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.45/0.68             (k7_tmap_1 @ sk_A @ 
% 0.45/0.68              (sk_D_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_A))))),
% 0.45/0.68      inference('simplify', [status(thm)], ['122'])).
% 0.45/0.68  thf('124', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('125', plain,
% 0.45/0.68      ((~ (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.68           (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.68           (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.45/0.68           (k7_tmap_1 @ sk_A @ 
% 0.45/0.68            (sk_D_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_A)))
% 0.45/0.68        | ((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B)))),
% 0.45/0.68      inference('clc', [status(thm)], ['123', '124'])).
% 0.45/0.68  thf('126', plain,
% 0.45/0.68      ((~ (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.68           (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.68           (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.45/0.68           (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.45/0.68        | ((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B))
% 0.45/0.68        | ((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['107', '125'])).
% 0.45/0.68  thf('127', plain,
% 0.45/0.68      (((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))
% 0.45/0.68         = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.68      inference('clc', [status(thm)], ['13', '14'])).
% 0.45/0.68  thf('128', plain,
% 0.45/0.68      ((~ (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.68           (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.68           (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.45/0.68           (k6_partfun1 @ (u1_struct_0 @ sk_A)))
% 0.45/0.68        | ((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B))
% 0.45/0.68        | ((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B)))),
% 0.45/0.68      inference('demod', [status(thm)], ['126', '127'])).
% 0.45/0.68  thf('129', plain,
% 0.45/0.68      ((((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B))
% 0.45/0.68        | ~ (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.68             (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.68             (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.45/0.68             (k6_partfun1 @ (u1_struct_0 @ sk_A))))),
% 0.45/0.68      inference('simplify', [status(thm)], ['128'])).
% 0.45/0.68  thf('130', plain,
% 0.45/0.68      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.45/0.68        | ((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['57', '129'])).
% 0.45/0.68  thf('131', plain,
% 0.45/0.68      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.45/0.68      inference('demod', [status(thm)], ['59', '93'])).
% 0.45/0.68  thf('132', plain,
% 0.45/0.68      ((~ (v1_funct_1 @ 
% 0.45/0.68           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.68            (k9_tmap_1 @ sk_A @ sk_B) @ sk_B))
% 0.45/0.68        | ~ (v1_funct_2 @ 
% 0.45/0.68             (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.68              (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.45/0.68             (u1_struct_0 @ sk_B) @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.45/0.68        | ~ (v5_pre_topc @ 
% 0.45/0.68             (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.68              (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.45/0.68             sk_B @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.45/0.68        | ~ (m1_subset_1 @ 
% 0.45/0.68             (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.68              (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.45/0.68             (k1_zfmisc_1 @ 
% 0.45/0.68              (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.68               (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))))))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('133', plain,
% 0.45/0.68      ((~ (m1_subset_1 @ 
% 0.45/0.68           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.68            (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.45/0.68           (k1_zfmisc_1 @ 
% 0.45/0.68            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.68             (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))))))
% 0.45/0.68         <= (~
% 0.45/0.68             ((m1_subset_1 @ 
% 0.45/0.68               (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.68                (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.45/0.68               (k1_zfmisc_1 @ 
% 0.45/0.68                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.68                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))))),
% 0.45/0.68      inference('split', [status(esa)], ['132'])).
% 0.45/0.68  thf('134', plain,
% 0.45/0.68      ((~ (m1_subset_1 @ 
% 0.45/0.68           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.68            (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.45/0.68           (k1_zfmisc_1 @ 
% 0.45/0.68            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))))
% 0.45/0.68         <= (~
% 0.45/0.68             ((m1_subset_1 @ 
% 0.45/0.68               (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.68                (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.45/0.68               (k1_zfmisc_1 @ 
% 0.45/0.68                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.68                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))))),
% 0.45/0.68      inference('sup-', [status(thm)], ['131', '133'])).
% 0.45/0.68  thf('135', plain,
% 0.45/0.68      (((~ (m1_subset_1 @ 
% 0.45/0.68            (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.68             (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B) @ 
% 0.45/0.68            (k1_zfmisc_1 @ 
% 0.45/0.68             (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 0.45/0.68         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.45/0.68         <= (~
% 0.45/0.68             ((m1_subset_1 @ 
% 0.45/0.68               (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.68                (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.45/0.68               (k1_zfmisc_1 @ 
% 0.45/0.68                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.68                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))))),
% 0.45/0.68      inference('sup-', [status(thm)], ['130', '134'])).
% 0.45/0.68  thf('136', plain,
% 0.45/0.68      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.68        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.68      inference('demod', [status(thm)], ['3', '4'])).
% 0.45/0.68  thf(t112_tmap_1, axiom,
% 0.45/0.68    (![A:$i]:
% 0.45/0.68     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.68       ( ![B:$i]:
% 0.45/0.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.68           ( ![C:$i]:
% 0.45/0.68             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.45/0.68               ( ( ( u1_struct_0 @ C ) = ( B ) ) =>
% 0.45/0.68                 ( ( v1_funct_1 @
% 0.45/0.68                     ( k2_tmap_1 @
% 0.45/0.68                       A @ ( k6_tmap_1 @ A @ B ) @ ( k7_tmap_1 @ A @ B ) @ C ) ) & 
% 0.45/0.68                   ( v1_funct_2 @
% 0.45/0.68                     ( k2_tmap_1 @
% 0.45/0.68                       A @ ( k6_tmap_1 @ A @ B ) @ ( k7_tmap_1 @ A @ B ) @ C ) @ 
% 0.45/0.68                     ( u1_struct_0 @ C ) @ 
% 0.45/0.68                     ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) & 
% 0.45/0.68                   ( v5_pre_topc @
% 0.45/0.68                     ( k2_tmap_1 @
% 0.45/0.68                       A @ ( k6_tmap_1 @ A @ B ) @ ( k7_tmap_1 @ A @ B ) @ C ) @ 
% 0.45/0.68                     C @ ( k6_tmap_1 @ A @ B ) ) & 
% 0.45/0.68                   ( m1_subset_1 @
% 0.45/0.68                     ( k2_tmap_1 @
% 0.45/0.68                       A @ ( k6_tmap_1 @ A @ B ) @ ( k7_tmap_1 @ A @ B ) @ C ) @ 
% 0.45/0.68                     ( k1_zfmisc_1 @
% 0.45/0.68                       ( k2_zfmisc_1 @
% 0.45/0.68                         ( u1_struct_0 @ C ) @ 
% 0.45/0.68                         ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.45/0.68  thf('137', plain,
% 0.45/0.68      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.45/0.68         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.45/0.68          | ((u1_struct_0 @ X27) != (X25))
% 0.45/0.68          | (v1_funct_2 @ 
% 0.45/0.68             (k2_tmap_1 @ X26 @ (k6_tmap_1 @ X26 @ X25) @ 
% 0.45/0.68              (k7_tmap_1 @ X26 @ X25) @ X27) @ 
% 0.45/0.68             (u1_struct_0 @ X27) @ (u1_struct_0 @ (k6_tmap_1 @ X26 @ X25)))
% 0.45/0.68          | ~ (m1_pre_topc @ X27 @ X26)
% 0.45/0.68          | (v2_struct_0 @ X27)
% 0.45/0.68          | ~ (l1_pre_topc @ X26)
% 0.45/0.68          | ~ (v2_pre_topc @ X26)
% 0.45/0.68          | (v2_struct_0 @ X26))),
% 0.45/0.68      inference('cnf', [status(esa)], [t112_tmap_1])).
% 0.45/0.68  thf('138', plain,
% 0.45/0.68      (![X26 : $i, X27 : $i]:
% 0.45/0.68         ((v2_struct_0 @ X26)
% 0.45/0.68          | ~ (v2_pre_topc @ X26)
% 0.45/0.68          | ~ (l1_pre_topc @ X26)
% 0.45/0.68          | (v2_struct_0 @ X27)
% 0.45/0.68          | ~ (m1_pre_topc @ X27 @ X26)
% 0.45/0.68          | (v1_funct_2 @ 
% 0.45/0.68             (k2_tmap_1 @ X26 @ (k6_tmap_1 @ X26 @ (u1_struct_0 @ X27)) @ 
% 0.45/0.68              (k7_tmap_1 @ X26 @ (u1_struct_0 @ X27)) @ X27) @ 
% 0.45/0.68             (u1_struct_0 @ X27) @ 
% 0.45/0.68             (u1_struct_0 @ (k6_tmap_1 @ X26 @ (u1_struct_0 @ X27))))
% 0.45/0.68          | ~ (m1_subset_1 @ (u1_struct_0 @ X27) @ 
% 0.45/0.68               (k1_zfmisc_1 @ (u1_struct_0 @ X26))))),
% 0.45/0.68      inference('simplify', [status(thm)], ['137'])).
% 0.45/0.68  thf('139', plain,
% 0.45/0.68      (((v1_funct_2 @ 
% 0.45/0.68         (k2_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.45/0.68          (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_B) @ 
% 0.45/0.68         (u1_struct_0 @ sk_B) @ 
% 0.45/0.68         (u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))
% 0.45/0.68        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.45/0.68        | (v2_struct_0 @ sk_B)
% 0.45/0.68        | ~ (l1_pre_topc @ sk_A)
% 0.45/0.68        | ~ (v2_pre_topc @ sk_A)
% 0.45/0.68        | (v2_struct_0 @ sk_A))),
% 0.45/0.68      inference('sup-', [status(thm)], ['136', '138'])).
% 0.45/0.68  thf('140', plain,
% 0.45/0.68      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.45/0.68      inference('clc', [status(thm)], ['91', '92'])).
% 0.45/0.68  thf('141', plain,
% 0.45/0.68      (((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))
% 0.45/0.68         = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.68      inference('clc', [status(thm)], ['13', '14'])).
% 0.45/0.68  thf('142', plain,
% 0.45/0.68      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.45/0.68      inference('clc', [status(thm)], ['91', '92'])).
% 0.45/0.68  thf('143', plain,
% 0.45/0.68      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.45/0.68      inference('demod', [status(thm)], ['59', '93'])).
% 0.45/0.68  thf('144', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('145', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('146', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('147', plain,
% 0.45/0.68      (((v1_funct_2 @ 
% 0.45/0.68         (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.68          (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B) @ 
% 0.45/0.68         (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.45/0.68        | (v2_struct_0 @ sk_B)
% 0.45/0.68        | (v2_struct_0 @ sk_A))),
% 0.45/0.68      inference('demod', [status(thm)],
% 0.45/0.68                ['139', '140', '141', '142', '143', '144', '145', '146'])).
% 0.45/0.68  thf('148', plain, (~ (v2_struct_0 @ sk_B)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('149', plain,
% 0.45/0.68      (((v2_struct_0 @ sk_A)
% 0.45/0.68        | (v1_funct_2 @ 
% 0.45/0.68           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.68            (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B) @ 
% 0.45/0.68           (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.45/0.68      inference('clc', [status(thm)], ['147', '148'])).
% 0.45/0.68  thf('150', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('151', plain,
% 0.45/0.68      ((v1_funct_2 @ 
% 0.45/0.68        (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.68         (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B) @ 
% 0.45/0.68        (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.45/0.68      inference('clc', [status(thm)], ['149', '150'])).
% 0.45/0.68  thf('152', plain,
% 0.45/0.68      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.45/0.68        | ((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['57', '129'])).
% 0.45/0.68  thf('153', plain,
% 0.45/0.68      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.45/0.68      inference('demod', [status(thm)], ['59', '93'])).
% 0.45/0.68  thf('154', plain,
% 0.45/0.68      ((~ (v1_funct_2 @ 
% 0.45/0.68           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.68            (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.45/0.68           (u1_struct_0 @ sk_B) @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))))
% 0.45/0.68         <= (~
% 0.45/0.68             ((v1_funct_2 @ 
% 0.45/0.68               (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.68                (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.45/0.68               (u1_struct_0 @ sk_B) @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))),
% 0.45/0.68      inference('split', [status(esa)], ['132'])).
% 0.45/0.68  thf('155', plain,
% 0.45/0.68      ((~ (v1_funct_2 @ 
% 0.45/0.68           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.68            (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.45/0.68           (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))
% 0.45/0.68         <= (~
% 0.45/0.68             ((v1_funct_2 @ 
% 0.45/0.68               (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.68                (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.45/0.68               (u1_struct_0 @ sk_B) @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))),
% 0.45/0.68      inference('sup-', [status(thm)], ['153', '154'])).
% 0.45/0.68  thf('156', plain,
% 0.45/0.68      (((~ (v1_funct_2 @ 
% 0.45/0.68            (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.68             (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B) @ 
% 0.45/0.68            (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.45/0.68         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.45/0.68         <= (~
% 0.45/0.68             ((v1_funct_2 @ 
% 0.45/0.68               (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.68                (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.45/0.68               (u1_struct_0 @ sk_B) @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))),
% 0.45/0.68      inference('sup-', [status(thm)], ['152', '155'])).
% 0.45/0.68  thf('157', plain,
% 0.45/0.68      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.45/0.68         <= (~
% 0.45/0.68             ((v1_funct_2 @ 
% 0.45/0.68               (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.68                (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.45/0.68               (u1_struct_0 @ sk_B) @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))),
% 0.45/0.68      inference('sup-', [status(thm)], ['151', '156'])).
% 0.45/0.68  thf(fc2_struct_0, axiom,
% 0.45/0.68    (![A:$i]:
% 0.45/0.68     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.45/0.68       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.45/0.68  thf('158', plain,
% 0.45/0.68      (![X2 : $i]:
% 0.45/0.68         (~ (v1_xboole_0 @ (u1_struct_0 @ X2))
% 0.45/0.68          | ~ (l1_struct_0 @ X2)
% 0.45/0.68          | (v2_struct_0 @ X2))),
% 0.45/0.68      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.45/0.68  thf('159', plain,
% 0.45/0.68      ((((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 0.45/0.68         <= (~
% 0.45/0.68             ((v1_funct_2 @ 
% 0.45/0.68               (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.68                (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.45/0.68               (u1_struct_0 @ sk_B) @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))),
% 0.45/0.68      inference('sup-', [status(thm)], ['157', '158'])).
% 0.45/0.68  thf('160', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf(dt_l1_pre_topc, axiom,
% 0.45/0.68    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.45/0.68  thf('161', plain, (![X0 : $i]: ((l1_struct_0 @ X0) | ~ (l1_pre_topc @ X0))),
% 0.45/0.68      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.45/0.68  thf('162', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.68      inference('sup-', [status(thm)], ['160', '161'])).
% 0.45/0.68  thf('163', plain,
% 0.45/0.68      (((v2_struct_0 @ sk_A))
% 0.45/0.68         <= (~
% 0.45/0.68             ((v1_funct_2 @ 
% 0.45/0.68               (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.68                (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.45/0.68               (u1_struct_0 @ sk_B) @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))),
% 0.45/0.68      inference('demod', [status(thm)], ['159', '162'])).
% 0.45/0.68  thf('164', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('165', plain,
% 0.45/0.68      (((v1_funct_2 @ 
% 0.45/0.68         (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.68          (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.45/0.68         (u1_struct_0 @ sk_B) @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.45/0.68      inference('sup-', [status(thm)], ['163', '164'])).
% 0.45/0.68  thf('166', plain,
% 0.45/0.68      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.68        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.68      inference('demod', [status(thm)], ['3', '4'])).
% 0.45/0.68  thf('167', plain,
% 0.45/0.68      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.45/0.68         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.45/0.68          | ((u1_struct_0 @ X27) != (X25))
% 0.45/0.68          | (v1_funct_1 @ 
% 0.45/0.68             (k2_tmap_1 @ X26 @ (k6_tmap_1 @ X26 @ X25) @ 
% 0.45/0.68              (k7_tmap_1 @ X26 @ X25) @ X27))
% 0.45/0.68          | ~ (m1_pre_topc @ X27 @ X26)
% 0.45/0.68          | (v2_struct_0 @ X27)
% 0.45/0.68          | ~ (l1_pre_topc @ X26)
% 0.45/0.68          | ~ (v2_pre_topc @ X26)
% 0.45/0.68          | (v2_struct_0 @ X26))),
% 0.45/0.68      inference('cnf', [status(esa)], [t112_tmap_1])).
% 0.45/0.68  thf('168', plain,
% 0.45/0.68      (![X26 : $i, X27 : $i]:
% 0.45/0.68         ((v2_struct_0 @ X26)
% 0.45/0.68          | ~ (v2_pre_topc @ X26)
% 0.45/0.68          | ~ (l1_pre_topc @ X26)
% 0.45/0.68          | (v2_struct_0 @ X27)
% 0.45/0.68          | ~ (m1_pre_topc @ X27 @ X26)
% 0.45/0.68          | (v1_funct_1 @ 
% 0.45/0.68             (k2_tmap_1 @ X26 @ (k6_tmap_1 @ X26 @ (u1_struct_0 @ X27)) @ 
% 0.45/0.68              (k7_tmap_1 @ X26 @ (u1_struct_0 @ X27)) @ X27))
% 0.45/0.68          | ~ (m1_subset_1 @ (u1_struct_0 @ X27) @ 
% 0.45/0.68               (k1_zfmisc_1 @ (u1_struct_0 @ X26))))),
% 0.45/0.68      inference('simplify', [status(thm)], ['167'])).
% 0.45/0.68  thf('169', plain,
% 0.45/0.68      (((v1_funct_1 @ 
% 0.45/0.68         (k2_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.45/0.68          (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_B))
% 0.45/0.68        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.45/0.68        | (v2_struct_0 @ sk_B)
% 0.45/0.68        | ~ (l1_pre_topc @ sk_A)
% 0.45/0.68        | ~ (v2_pre_topc @ sk_A)
% 0.45/0.68        | (v2_struct_0 @ sk_A))),
% 0.45/0.68      inference('sup-', [status(thm)], ['166', '168'])).
% 0.45/0.68  thf('170', plain,
% 0.45/0.68      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.45/0.68      inference('clc', [status(thm)], ['91', '92'])).
% 0.45/0.68  thf('171', plain,
% 0.45/0.68      (((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))
% 0.45/0.68         = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.68      inference('clc', [status(thm)], ['13', '14'])).
% 0.45/0.68  thf('172', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('173', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('174', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('175', plain,
% 0.45/0.68      (((v1_funct_1 @ 
% 0.45/0.68         (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.68          (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B))
% 0.45/0.68        | (v2_struct_0 @ sk_B)
% 0.45/0.68        | (v2_struct_0 @ sk_A))),
% 0.45/0.68      inference('demod', [status(thm)],
% 0.45/0.68                ['169', '170', '171', '172', '173', '174'])).
% 0.45/0.68  thf('176', plain, (~ (v2_struct_0 @ sk_B)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('177', plain,
% 0.45/0.68      (((v2_struct_0 @ sk_A)
% 0.45/0.68        | (v1_funct_1 @ 
% 0.45/0.68           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.68            (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B)))),
% 0.45/0.68      inference('clc', [status(thm)], ['175', '176'])).
% 0.45/0.68  thf('178', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('179', plain,
% 0.45/0.68      ((v1_funct_1 @ 
% 0.45/0.68        (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.68         (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B))),
% 0.45/0.68      inference('clc', [status(thm)], ['177', '178'])).
% 0.45/0.68  thf('180', plain,
% 0.45/0.68      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.45/0.68        | ((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['57', '129'])).
% 0.45/0.68  thf('181', plain,
% 0.45/0.68      ((~ (v1_funct_1 @ 
% 0.45/0.68           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.68            (k9_tmap_1 @ sk_A @ sk_B) @ sk_B)))
% 0.45/0.68         <= (~
% 0.45/0.68             ((v1_funct_1 @ 
% 0.45/0.68               (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.68                (k9_tmap_1 @ sk_A @ sk_B) @ sk_B))))),
% 0.45/0.68      inference('split', [status(esa)], ['132'])).
% 0.45/0.68  thf('182', plain,
% 0.45/0.68      (((~ (v1_funct_1 @ 
% 0.45/0.68            (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.68             (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B))
% 0.45/0.68         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.45/0.68         <= (~
% 0.45/0.68             ((v1_funct_1 @ 
% 0.45/0.68               (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.68                (k9_tmap_1 @ sk_A @ sk_B) @ sk_B))))),
% 0.45/0.68      inference('sup-', [status(thm)], ['180', '181'])).
% 0.45/0.68  thf('183', plain,
% 0.45/0.68      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.45/0.68         <= (~
% 0.45/0.68             ((v1_funct_1 @ 
% 0.45/0.68               (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.68                (k9_tmap_1 @ sk_A @ sk_B) @ sk_B))))),
% 0.45/0.68      inference('sup-', [status(thm)], ['179', '182'])).
% 0.45/0.68  thf('184', plain,
% 0.45/0.68      (![X2 : $i]:
% 0.45/0.68         (~ (v1_xboole_0 @ (u1_struct_0 @ X2))
% 0.45/0.68          | ~ (l1_struct_0 @ X2)
% 0.45/0.68          | (v2_struct_0 @ X2))),
% 0.45/0.68      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.45/0.68  thf('185', plain,
% 0.45/0.68      ((((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 0.45/0.68         <= (~
% 0.45/0.68             ((v1_funct_1 @ 
% 0.45/0.68               (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.68                (k9_tmap_1 @ sk_A @ sk_B) @ sk_B))))),
% 0.45/0.68      inference('sup-', [status(thm)], ['183', '184'])).
% 0.45/0.68  thf('186', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.68      inference('sup-', [status(thm)], ['160', '161'])).
% 0.45/0.68  thf('187', plain,
% 0.45/0.68      (((v2_struct_0 @ sk_A))
% 0.45/0.68         <= (~
% 0.45/0.68             ((v1_funct_1 @ 
% 0.45/0.68               (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.68                (k9_tmap_1 @ sk_A @ sk_B) @ sk_B))))),
% 0.45/0.68      inference('demod', [status(thm)], ['185', '186'])).
% 0.45/0.68  thf('188', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('189', plain,
% 0.45/0.68      (((v1_funct_1 @ 
% 0.45/0.68         (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.68          (k9_tmap_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['187', '188'])).
% 0.45/0.68  thf('190', plain,
% 0.45/0.68      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.68        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.68      inference('demod', [status(thm)], ['3', '4'])).
% 0.45/0.68  thf('191', plain,
% 0.45/0.68      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.45/0.68         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.45/0.68          | ((u1_struct_0 @ X27) != (X25))
% 0.45/0.68          | (v5_pre_topc @ 
% 0.45/0.68             (k2_tmap_1 @ X26 @ (k6_tmap_1 @ X26 @ X25) @ 
% 0.45/0.68              (k7_tmap_1 @ X26 @ X25) @ X27) @ 
% 0.45/0.68             X27 @ (k6_tmap_1 @ X26 @ X25))
% 0.45/0.68          | ~ (m1_pre_topc @ X27 @ X26)
% 0.45/0.68          | (v2_struct_0 @ X27)
% 0.45/0.68          | ~ (l1_pre_topc @ X26)
% 0.45/0.68          | ~ (v2_pre_topc @ X26)
% 0.45/0.68          | (v2_struct_0 @ X26))),
% 0.45/0.68      inference('cnf', [status(esa)], [t112_tmap_1])).
% 0.45/0.68  thf('192', plain,
% 0.45/0.68      (![X26 : $i, X27 : $i]:
% 0.45/0.68         ((v2_struct_0 @ X26)
% 0.45/0.68          | ~ (v2_pre_topc @ X26)
% 0.45/0.68          | ~ (l1_pre_topc @ X26)
% 0.45/0.68          | (v2_struct_0 @ X27)
% 0.45/0.68          | ~ (m1_pre_topc @ X27 @ X26)
% 0.45/0.68          | (v5_pre_topc @ 
% 0.45/0.68             (k2_tmap_1 @ X26 @ (k6_tmap_1 @ X26 @ (u1_struct_0 @ X27)) @ 
% 0.45/0.68              (k7_tmap_1 @ X26 @ (u1_struct_0 @ X27)) @ X27) @ 
% 0.45/0.68             X27 @ (k6_tmap_1 @ X26 @ (u1_struct_0 @ X27)))
% 0.45/0.68          | ~ (m1_subset_1 @ (u1_struct_0 @ X27) @ 
% 0.45/0.68               (k1_zfmisc_1 @ (u1_struct_0 @ X26))))),
% 0.45/0.68      inference('simplify', [status(thm)], ['191'])).
% 0.45/0.68  thf('193', plain,
% 0.45/0.68      (((v5_pre_topc @ 
% 0.45/0.68         (k2_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.45/0.68          (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_B) @ 
% 0.45/0.68         sk_B @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.45/0.68        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.45/0.68        | (v2_struct_0 @ sk_B)
% 0.45/0.68        | ~ (l1_pre_topc @ sk_A)
% 0.45/0.68        | ~ (v2_pre_topc @ sk_A)
% 0.45/0.68        | (v2_struct_0 @ sk_A))),
% 0.45/0.68      inference('sup-', [status(thm)], ['190', '192'])).
% 0.45/0.68  thf('194', plain,
% 0.45/0.68      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.45/0.68      inference('clc', [status(thm)], ['91', '92'])).
% 0.45/0.68  thf('195', plain,
% 0.45/0.68      (((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))
% 0.45/0.68         = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.68      inference('clc', [status(thm)], ['13', '14'])).
% 0.45/0.68  thf('196', plain,
% 0.45/0.68      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.45/0.68      inference('clc', [status(thm)], ['91', '92'])).
% 0.45/0.68  thf('197', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('198', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('199', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('200', plain,
% 0.45/0.68      (((v5_pre_topc @ 
% 0.45/0.68         (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.68          (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B) @ 
% 0.45/0.68         sk_B @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.45/0.68        | (v2_struct_0 @ sk_B)
% 0.45/0.68        | (v2_struct_0 @ sk_A))),
% 0.45/0.68      inference('demod', [status(thm)],
% 0.45/0.68                ['193', '194', '195', '196', '197', '198', '199'])).
% 0.45/0.68  thf('201', plain, (~ (v2_struct_0 @ sk_B)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('202', plain,
% 0.45/0.68      (((v2_struct_0 @ sk_A)
% 0.45/0.68        | (v5_pre_topc @ 
% 0.45/0.68           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.68            (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B) @ 
% 0.45/0.68           sk_B @ (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.45/0.68      inference('clc', [status(thm)], ['200', '201'])).
% 0.45/0.68  thf('203', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('204', plain,
% 0.45/0.68      ((v5_pre_topc @ 
% 0.45/0.68        (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.68         (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B) @ 
% 0.45/0.68        sk_B @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.45/0.68      inference('clc', [status(thm)], ['202', '203'])).
% 0.45/0.68  thf('205', plain,
% 0.45/0.68      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.45/0.68        | ((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['57', '129'])).
% 0.45/0.68  thf('206', plain,
% 0.45/0.68      ((~ (v5_pre_topc @ 
% 0.45/0.68           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.68            (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.45/0.68           sk_B @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.45/0.68         <= (~
% 0.45/0.68             ((v5_pre_topc @ 
% 0.45/0.68               (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.68                (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.45/0.68               sk_B @ (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.45/0.68      inference('split', [status(esa)], ['132'])).
% 0.45/0.68  thf('207', plain,
% 0.45/0.68      (((~ (v5_pre_topc @ 
% 0.45/0.68            (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.68             (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B) @ 
% 0.45/0.68            sk_B @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.45/0.68         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.45/0.68         <= (~
% 0.45/0.68             ((v5_pre_topc @ 
% 0.45/0.68               (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.68                (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.45/0.68               sk_B @ (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.45/0.68      inference('sup-', [status(thm)], ['205', '206'])).
% 0.45/0.68  thf('208', plain,
% 0.45/0.68      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.45/0.68         <= (~
% 0.45/0.68             ((v5_pre_topc @ 
% 0.45/0.68               (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.68                (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.45/0.68               sk_B @ (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.45/0.68      inference('sup-', [status(thm)], ['204', '207'])).
% 0.45/0.68  thf('209', plain,
% 0.45/0.68      (![X2 : $i]:
% 0.45/0.68         (~ (v1_xboole_0 @ (u1_struct_0 @ X2))
% 0.45/0.68          | ~ (l1_struct_0 @ X2)
% 0.45/0.68          | (v2_struct_0 @ X2))),
% 0.45/0.68      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.45/0.68  thf('210', plain,
% 0.45/0.68      ((((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 0.45/0.68         <= (~
% 0.45/0.68             ((v5_pre_topc @ 
% 0.45/0.68               (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.68                (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.45/0.68               sk_B @ (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.45/0.68      inference('sup-', [status(thm)], ['208', '209'])).
% 0.45/0.68  thf('211', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.68      inference('sup-', [status(thm)], ['160', '161'])).
% 0.45/0.68  thf('212', plain,
% 0.45/0.68      (((v2_struct_0 @ sk_A))
% 0.45/0.68         <= (~
% 0.45/0.68             ((v5_pre_topc @ 
% 0.45/0.68               (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.68                (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.45/0.68               sk_B @ (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.45/0.68      inference('demod', [status(thm)], ['210', '211'])).
% 0.45/0.68  thf('213', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('214', plain,
% 0.45/0.68      (((v5_pre_topc @ 
% 0.45/0.68         (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.68          (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.45/0.68         sk_B @ (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['212', '213'])).
% 0.45/0.68  thf('215', plain,
% 0.45/0.68      (~
% 0.45/0.68       ((m1_subset_1 @ 
% 0.45/0.68         (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.68          (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.45/0.68         (k1_zfmisc_1 @ 
% 0.45/0.68          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.68           (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))) | 
% 0.45/0.68       ~
% 0.45/0.68       ((v5_pre_topc @ 
% 0.45/0.68         (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.68          (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.45/0.68         sk_B @ (k8_tmap_1 @ sk_A @ sk_B))) | 
% 0.45/0.68       ~
% 0.45/0.68       ((v1_funct_1 @ 
% 0.45/0.68         (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.68          (k9_tmap_1 @ sk_A @ sk_B) @ sk_B))) | 
% 0.45/0.68       ~
% 0.45/0.68       ((v1_funct_2 @ 
% 0.45/0.68         (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.68          (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.45/0.68         (u1_struct_0 @ sk_B) @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.45/0.68      inference('split', [status(esa)], ['132'])).
% 0.45/0.68  thf('216', plain,
% 0.45/0.68      (~
% 0.45/0.68       ((m1_subset_1 @ 
% 0.45/0.68         (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.68          (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.45/0.68         (k1_zfmisc_1 @ 
% 0.45/0.68          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.68           (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))))))),
% 0.45/0.68      inference('sat_resolution*', [status(thm)], ['165', '189', '214', '215'])).
% 0.45/0.68  thf('217', plain,
% 0.45/0.68      ((~ (m1_subset_1 @ 
% 0.45/0.68           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.68            (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B) @ 
% 0.45/0.68           (k1_zfmisc_1 @ 
% 0.45/0.68            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 0.45/0.68        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.68      inference('simpl_trail', [status(thm)], ['135', '216'])).
% 0.45/0.68  thf('218', plain,
% 0.45/0.68      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.68        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.68      inference('demod', [status(thm)], ['3', '4'])).
% 0.45/0.68  thf('219', plain,
% 0.45/0.68      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.45/0.68         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.45/0.68          | ((u1_struct_0 @ X27) != (X25))
% 0.45/0.68          | (m1_subset_1 @ 
% 0.45/0.68             (k2_tmap_1 @ X26 @ (k6_tmap_1 @ X26 @ X25) @ 
% 0.45/0.68              (k7_tmap_1 @ X26 @ X25) @ X27) @ 
% 0.45/0.68             (k1_zfmisc_1 @ 
% 0.45/0.68              (k2_zfmisc_1 @ (u1_struct_0 @ X27) @ 
% 0.45/0.68               (u1_struct_0 @ (k6_tmap_1 @ X26 @ X25)))))
% 0.45/0.68          | ~ (m1_pre_topc @ X27 @ X26)
% 0.45/0.68          | (v2_struct_0 @ X27)
% 0.45/0.68          | ~ (l1_pre_topc @ X26)
% 0.45/0.68          | ~ (v2_pre_topc @ X26)
% 0.45/0.68          | (v2_struct_0 @ X26))),
% 0.45/0.68      inference('cnf', [status(esa)], [t112_tmap_1])).
% 0.45/0.68  thf('220', plain,
% 0.45/0.68      (![X26 : $i, X27 : $i]:
% 0.45/0.68         ((v2_struct_0 @ X26)
% 0.45/0.68          | ~ (v2_pre_topc @ X26)
% 0.45/0.68          | ~ (l1_pre_topc @ X26)
% 0.45/0.68          | (v2_struct_0 @ X27)
% 0.45/0.68          | ~ (m1_pre_topc @ X27 @ X26)
% 0.45/0.68          | (m1_subset_1 @ 
% 0.45/0.68             (k2_tmap_1 @ X26 @ (k6_tmap_1 @ X26 @ (u1_struct_0 @ X27)) @ 
% 0.45/0.68              (k7_tmap_1 @ X26 @ (u1_struct_0 @ X27)) @ X27) @ 
% 0.45/0.68             (k1_zfmisc_1 @ 
% 0.45/0.68              (k2_zfmisc_1 @ (u1_struct_0 @ X27) @ 
% 0.45/0.68               (u1_struct_0 @ (k6_tmap_1 @ X26 @ (u1_struct_0 @ X27))))))
% 0.45/0.68          | ~ (m1_subset_1 @ (u1_struct_0 @ X27) @ 
% 0.45/0.68               (k1_zfmisc_1 @ (u1_struct_0 @ X26))))),
% 0.45/0.68      inference('simplify', [status(thm)], ['219'])).
% 0.45/0.68  thf('221', plain,
% 0.45/0.68      (((m1_subset_1 @ 
% 0.45/0.68         (k2_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.45/0.68          (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_B) @ 
% 0.45/0.68         (k1_zfmisc_1 @ 
% 0.45/0.68          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.68           (u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))))
% 0.45/0.68        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.45/0.68        | (v2_struct_0 @ sk_B)
% 0.45/0.68        | ~ (l1_pre_topc @ sk_A)
% 0.45/0.68        | ~ (v2_pre_topc @ sk_A)
% 0.45/0.68        | (v2_struct_0 @ sk_A))),
% 0.45/0.68      inference('sup-', [status(thm)], ['218', '220'])).
% 0.45/0.68  thf('222', plain,
% 0.45/0.68      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.45/0.68      inference('clc', [status(thm)], ['91', '92'])).
% 0.45/0.68  thf('223', plain,
% 0.45/0.68      (((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))
% 0.45/0.68         = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.68      inference('clc', [status(thm)], ['13', '14'])).
% 0.45/0.68  thf('224', plain,
% 0.45/0.68      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.45/0.68      inference('clc', [status(thm)], ['91', '92'])).
% 0.45/0.68  thf('225', plain,
% 0.45/0.68      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.45/0.68      inference('demod', [status(thm)], ['59', '93'])).
% 0.45/0.68  thf('226', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('227', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('228', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('229', plain,
% 0.45/0.68      (((m1_subset_1 @ 
% 0.45/0.68         (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.68          (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B) @ 
% 0.45/0.68         (k1_zfmisc_1 @ 
% 0.45/0.68          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 0.45/0.68        | (v2_struct_0 @ sk_B)
% 0.45/0.68        | (v2_struct_0 @ sk_A))),
% 0.45/0.68      inference('demod', [status(thm)],
% 0.45/0.68                ['221', '222', '223', '224', '225', '226', '227', '228'])).
% 0.45/0.68  thf('230', plain, (~ (v2_struct_0 @ sk_B)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('231', plain,
% 0.45/0.68      (((v2_struct_0 @ sk_A)
% 0.45/0.68        | (m1_subset_1 @ 
% 0.45/0.68           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.68            (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B) @ 
% 0.45/0.68           (k1_zfmisc_1 @ 
% 0.45/0.68            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.68      inference('clc', [status(thm)], ['229', '230'])).
% 0.45/0.68  thf('232', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('233', plain,
% 0.45/0.68      ((m1_subset_1 @ 
% 0.45/0.68        (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.45/0.68         (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B) @ 
% 0.45/0.68        (k1_zfmisc_1 @ 
% 0.45/0.68         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.45/0.68      inference('clc', [status(thm)], ['231', '232'])).
% 0.45/0.68  thf('234', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.45/0.68      inference('demod', [status(thm)], ['217', '233'])).
% 0.45/0.68  thf('235', plain,
% 0.45/0.68      (![X2 : $i]:
% 0.45/0.68         (~ (v1_xboole_0 @ (u1_struct_0 @ X2))
% 0.45/0.68          | ~ (l1_struct_0 @ X2)
% 0.45/0.68          | (v2_struct_0 @ X2))),
% 0.45/0.68      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.45/0.68  thf('236', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.45/0.68      inference('sup-', [status(thm)], ['234', '235'])).
% 0.45/0.68  thf('237', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.68      inference('sup-', [status(thm)], ['160', '161'])).
% 0.45/0.68  thf('238', plain, ((v2_struct_0 @ sk_A)),
% 0.45/0.68      inference('demod', [status(thm)], ['236', '237'])).
% 0.45/0.68  thf('239', plain, ($false), inference('demod', [status(thm)], ['0', '238'])).
% 0.45/0.68  
% 0.45/0.68  % SZS output end Refutation
% 0.45/0.68  
% 0.45/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
