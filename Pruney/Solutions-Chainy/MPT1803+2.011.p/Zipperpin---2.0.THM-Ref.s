%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UH5w67B3cB

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:00 EST 2020

% Result     : Theorem 0.80s
% Output     : Refutation 0.80s
% Verified   : 
% Statistics : Number of formulae       :  182 (1793 expanded)
%              Number of leaves         :   37 ( 534 expanded)
%              Depth                    :   25
%              Number of atoms          : 2061 (32872 expanded)
%              Number of equality atoms :   58 ( 271 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_funct_2_type,type,(
    r1_funct_2: $i > $i > $i > $i > $i > $i > $o )).

thf(k6_tmap_1_type,type,(
    k6_tmap_1: $i > $i > $i )).

thf(k5_tmap_1_type,type,(
    k5_tmap_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_tmap_1_type,type,(
    k7_tmap_1: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k9_tmap_1_type,type,(
    k9_tmap_1: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k8_tmap_1_type,type,(
    k8_tmap_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(t119_tmap_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) )
             => ( r1_tmap_1 @ B @ ( k8_tmap_1 @ A @ B ) @ ( k2_tmap_1 @ A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ B ) @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( m1_pre_topc @ B @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) )
               => ( r1_tmap_1 @ B @ ( k8_tmap_1 @ A @ B ) @ ( k2_tmap_1 @ A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ B ) @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t119_tmap_1])).

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
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_pre_topc @ X26 @ X27 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X26 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( l1_pre_topc @ X27 ) ) ),
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
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( m1_subset_1 @ ( k7_tmap_1 @ X16 @ X17 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X16 @ X17 ) ) ) ) ) ) ),
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

thf('9',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( ( u1_struct_0 @ ( k6_tmap_1 @ X21 @ X20 ) )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t104_tmap_1])).

thf('10',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('14',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('16',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['7','15','16','17'])).

thf('19',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_subset_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['18','19'])).

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

thf('22',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) )
      | ~ ( v1_funct_2 @ X2 @ X3 @ X4 )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_xboole_0 @ X5 )
      | ( v1_xboole_0 @ X4 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_funct_2 @ X6 @ X7 @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X5 ) ) )
      | ( r1_funct_2 @ X3 @ X4 @ X7 @ X5 @ X2 @ X6 )
      | ( X2 != X6 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_funct_2])).

thf('23',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( r1_funct_2 @ X3 @ X4 @ X7 @ X5 @ X6 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X5 ) ) )
      | ~ ( v1_funct_2 @ X6 @ X7 @ X5 )
      | ( v1_xboole_0 @ X4 )
      | ( v1_xboole_0 @ X5 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_funct_2 @ X6 @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_2 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ X1 @ X0 )
      | ~ ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_2 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_funct_2 @ X1 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('26',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( v1_funct_1 @ ( k7_tmap_1 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_tmap_1])).

thf('27',plain,
    ( ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('34',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( v1_funct_2 @ ( k7_tmap_1 @ X16 @ X17 ) @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_tmap_1])).

thf('35',plain,
    ( ( v1_funct_2 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('37',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( v1_funct_2 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['35','36','37','38'])).

thf('40',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_funct_2 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_2 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ X1 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ( r1_funct_2 @ X1 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['24','32','41'])).

thf('43',plain,
    ( ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_2 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','42'])).

thf('44',plain,(
    v1_funct_2 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('45',plain,
    ( ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    m1_subset_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['18','19'])).

thf('48',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('49',plain,(
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

thf('50',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( X10
       != ( k8_tmap_1 @ X9 @ X8 ) )
      | ( X11
       != ( u1_struct_0 @ X8 ) )
      | ( X10
        = ( k6_tmap_1 @ X9 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ~ ( v1_pre_topc @ X10 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d11_tmap_1])).

thf('51',plain,(
    ! [X8: $i,X9: $i] :
      ( ( v2_struct_0 @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v1_pre_topc @ ( k8_tmap_1 @ X9 @ X8 ) )
      | ~ ( v2_pre_topc @ ( k8_tmap_1 @ X9 @ X8 ) )
      | ~ ( l1_pre_topc @ ( k8_tmap_1 @ X9 @ X8 ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( ( k8_tmap_1 @ X9 @ X8 )
        = ( k6_tmap_1 @ X9 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( m1_pre_topc @ X8 @ X9 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( ( k8_tmap_1 @ sk_A @ sk_B )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['49','51'])).

thf('53',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
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

thf('55',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 )
      | ~ ( m1_pre_topc @ X19 @ X18 )
      | ( l1_pre_topc @ ( k8_tmap_1 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('56',plain,
    ( ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['59','60'])).

thf('62',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 )
      | ~ ( m1_pre_topc @ X19 @ X18 )
      | ( v2_pre_topc @ ( k8_tmap_1 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('64',plain,
    ( ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('70',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 )
      | ~ ( m1_pre_topc @ X19 @ X18 )
      | ( v1_pre_topc @ ( k8_tmap_1 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('72',plain,
    ( ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('76',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['75','76'])).

thf('78',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( ( k8_tmap_1 @ sk_A @ sk_B )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['52','53','61','69','77','78','79'])).

thf('81',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['80','81'])).

thf('83',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['48','82'])).

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

thf('84',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_pre_topc @ X12 @ X13 )
      | ( ( sk_D_1 @ X14 @ X12 @ X13 )
        = ( u1_struct_0 @ X12 ) )
      | ( X14
        = ( k9_tmap_1 @ X13 @ X12 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X13 @ X12 ) ) ) ) )
      | ~ ( v1_funct_2 @ X14 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X13 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d12_tmap_1])).

thf('85',plain,(
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
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['48','82'])).

thf('89',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( X0
        = ( k9_tmap_1 @ sk_A @ sk_B ) )
      | ( ( sk_D_1 @ X0 @ sk_B @ sk_A )
        = ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['85','86','87','88','89'])).

thf('91',plain,
    ( ( ( sk_D_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_B @ sk_A )
      = ( u1_struct_0 @ sk_B ) )
    | ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['47','90'])).

thf('92',plain,(
    v1_funct_2 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('93',plain,(
    v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('94',plain,
    ( ( ( sk_D_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_B @ sk_A )
      = ( u1_struct_0 @ sk_B ) )
    | ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['91','92','93'])).

thf('95',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ( ( sk_D_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_B @ sk_A )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['94','95'])).

thf('97',plain,
    ( ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ( ( sk_D_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_B @ sk_A )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['94','95'])).

thf('98',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_pre_topc @ X12 @ X13 )
      | ~ ( r1_funct_2 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X13 @ X12 ) ) @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X13 @ ( sk_D_1 @ X14 @ X12 @ X13 ) ) ) @ X14 @ ( k7_tmap_1 @ X13 @ ( sk_D_1 @ X14 @ X12 @ X13 ) ) )
      | ( X14
        = ( k9_tmap_1 @ X13 @ X12 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X13 @ X12 ) ) ) ) )
      | ~ ( v1_funct_2 @ X14 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X13 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d12_tmap_1])).

thf('99',plain,
    ( ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( k7_tmap_1 @ sk_A @ ( sk_D_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_B @ sk_A ) ) )
    | ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( v1_funct_2 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
    | ~ ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) )
    | ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['48','82'])).

thf('101',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['80','81'])).

thf('102',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['48','82'])).

thf('103',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('106',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['48','82'])).

thf('107',plain,(
    v1_funct_2 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('108',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['48','82'])).

thf('109',plain,(
    m1_subset_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['18','19'])).

thf('110',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( k7_tmap_1 @ sk_A @ ( sk_D_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_B @ sk_A ) ) )
    | ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['99','100','101','102','103','104','105','106','107','108','109','110'])).

thf('112',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( k7_tmap_1 @ sk_A @ ( sk_D_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_B @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( k7_tmap_1 @ sk_A @ ( sk_D_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_B @ sk_A ) ) )
    | ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['112','113'])).

thf('115',plain,
    ( ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['96','114'])).

thf('116',plain,
    ( ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['115'])).

thf('117',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['46','116'])).

thf('118',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t110_tmap_1,axiom,(
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
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ C ) )
                   => ( r1_tmap_1 @ C @ ( k6_tmap_1 @ A @ B ) @ ( k2_tmap_1 @ A @ ( k6_tmap_1 @ A @ B ) @ ( k7_tmap_1 @ A @ B ) @ C ) @ D ) ) ) ) ) ) )).

thf('120',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( ( u1_struct_0 @ X24 )
       != X22 )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X24 ) )
      | ( r1_tmap_1 @ X24 @ ( k6_tmap_1 @ X23 @ X22 ) @ ( k2_tmap_1 @ X23 @ ( k6_tmap_1 @ X23 @ X22 ) @ ( k7_tmap_1 @ X23 @ X22 ) @ X24 ) @ X25 )
      | ~ ( m1_pre_topc @ X24 @ X23 )
      | ( v2_struct_0 @ X24 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t110_tmap_1])).

thf('121',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v2_struct_0 @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ~ ( l1_pre_topc @ X23 )
      | ( v2_struct_0 @ X24 )
      | ~ ( m1_pre_topc @ X24 @ X23 )
      | ( r1_tmap_1 @ X24 @ ( k6_tmap_1 @ X23 @ ( u1_struct_0 @ X24 ) ) @ ( k2_tmap_1 @ X23 @ ( k6_tmap_1 @ X23 @ ( u1_struct_0 @ X24 ) ) @ ( k7_tmap_1 @ X23 @ ( u1_struct_0 @ X24 ) ) @ X24 ) @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X24 ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X24 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) ) ) ),
    inference(simplify,[status(thm)],['120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ( r1_tmap_1 @ sk_B @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( k2_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_B ) @ X0 )
      | ~ ( m1_pre_topc @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['119','121'])).

thf('123',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['80','81'])).

thf('124',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['80','81'])).

thf('125',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ( r1_tmap_1 @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_B ) @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['122','123','124','125','126','127'])).

thf('129',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tmap_1 @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['118','128'])).

thf('130',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,
    ( ( r1_tmap_1 @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_B ) @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['129','130'])).

thf('132',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    r1_tmap_1 @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_B ) @ sk_C ),
    inference(clc,[status(thm)],['131','132'])).

thf('134',plain,
    ( ( r1_tmap_1 @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ sk_C )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['117','133'])).

thf('135',plain,(
    ~ ( r1_tmap_1 @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['134','135'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('137',plain,(
    ! [X1: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_struct_0 @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('138',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('140',plain,(
    ! [X0: $i] :
      ( ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('141',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['138','141'])).

thf('143',plain,(
    $false ),
    inference(demod,[status(thm)],['0','142'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UH5w67B3cB
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:06:11 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.80/1.00  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.80/1.00  % Solved by: fo/fo7.sh
% 0.80/1.00  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.80/1.00  % done 209 iterations in 0.551s
% 0.80/1.00  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.80/1.00  % SZS output start Refutation
% 0.80/1.00  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.80/1.00  thf(r1_funct_2_type, type, r1_funct_2: $i > $i > $i > $i > $i > $i > $o).
% 0.80/1.00  thf(k6_tmap_1_type, type, k6_tmap_1: $i > $i > $i).
% 0.80/1.00  thf(k5_tmap_1_type, type, k5_tmap_1: $i > $i > $i).
% 0.80/1.00  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.80/1.00  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.80/1.00  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.80/1.00  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.80/1.00  thf(sk_C_type, type, sk_C: $i).
% 0.80/1.00  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.80/1.00  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.80/1.00  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.80/1.00  thf(sk_B_type, type, sk_B: $i).
% 0.80/1.00  thf(k7_tmap_1_type, type, k7_tmap_1: $i > $i > $i).
% 0.80/1.00  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.80/1.00  thf(k9_tmap_1_type, type, k9_tmap_1: $i > $i > $i).
% 0.80/1.00  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.80/1.00  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.80/1.00  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.80/1.00  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.80/1.00  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.80/1.00  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.80/1.00  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.80/1.00  thf(sk_A_type, type, sk_A: $i).
% 0.80/1.00  thf(k8_tmap_1_type, type, k8_tmap_1: $i > $i > $i).
% 0.80/1.00  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.80/1.00  thf(t119_tmap_1, conjecture,
% 0.80/1.00    (![A:$i]:
% 0.80/1.00     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.80/1.00       ( ![B:$i]:
% 0.80/1.00         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.80/1.00           ( ![C:$i]:
% 0.80/1.00             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) =>
% 0.80/1.00               ( r1_tmap_1 @
% 0.80/1.00                 B @ ( k8_tmap_1 @ A @ B ) @ 
% 0.80/1.00                 ( k2_tmap_1 @
% 0.80/1.00                   A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ B ) @ 
% 0.80/1.00                 C ) ) ) ) ) ))).
% 0.80/1.00  thf(zf_stmt_0, negated_conjecture,
% 0.80/1.00    (~( ![A:$i]:
% 0.80/1.00        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.80/1.00            ( l1_pre_topc @ A ) ) =>
% 0.80/1.00          ( ![B:$i]:
% 0.80/1.00            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.80/1.00              ( ![C:$i]:
% 0.80/1.00                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) =>
% 0.80/1.00                  ( r1_tmap_1 @
% 0.80/1.00                    B @ ( k8_tmap_1 @ A @ B ) @ 
% 0.80/1.00                    ( k2_tmap_1 @
% 0.80/1.00                      A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ B ) @ 
% 0.80/1.00                    C ) ) ) ) ) ) )),
% 0.80/1.00    inference('cnf.neg', [status(esa)], [t119_tmap_1])).
% 0.80/1.00  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('1', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf(t1_tsep_1, axiom,
% 0.80/1.00    (![A:$i]:
% 0.80/1.00     ( ( l1_pre_topc @ A ) =>
% 0.80/1.00       ( ![B:$i]:
% 0.80/1.00         ( ( m1_pre_topc @ B @ A ) =>
% 0.80/1.00           ( m1_subset_1 @
% 0.80/1.00             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.80/1.00  thf('2', plain,
% 0.80/1.00      (![X26 : $i, X27 : $i]:
% 0.80/1.00         (~ (m1_pre_topc @ X26 @ X27)
% 0.80/1.00          | (m1_subset_1 @ (u1_struct_0 @ X26) @ 
% 0.80/1.00             (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.80/1.00          | ~ (l1_pre_topc @ X27))),
% 0.80/1.00      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.80/1.00  thf('3', plain,
% 0.80/1.00      ((~ (l1_pre_topc @ sk_A)
% 0.80/1.00        | (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.80/1.00           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.80/1.00      inference('sup-', [status(thm)], ['1', '2'])).
% 0.80/1.00  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('5', plain,
% 0.80/1.00      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.80/1.00        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.80/1.00      inference('demod', [status(thm)], ['3', '4'])).
% 0.80/1.00  thf(dt_k7_tmap_1, axiom,
% 0.80/1.00    (![A:$i,B:$i]:
% 0.80/1.00     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.80/1.00         ( l1_pre_topc @ A ) & 
% 0.80/1.00         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.80/1.00       ( ( v1_funct_1 @ ( k7_tmap_1 @ A @ B ) ) & 
% 0.80/1.00         ( v1_funct_2 @
% 0.80/1.00           ( k7_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.80/1.00           ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) & 
% 0.80/1.00         ( m1_subset_1 @
% 0.80/1.00           ( k7_tmap_1 @ A @ B ) @ 
% 0.80/1.00           ( k1_zfmisc_1 @
% 0.80/1.00             ( k2_zfmisc_1 @
% 0.80/1.00               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) ) ) ) ))).
% 0.80/1.00  thf('6', plain,
% 0.80/1.00      (![X16 : $i, X17 : $i]:
% 0.80/1.00         (~ (l1_pre_topc @ X16)
% 0.80/1.00          | ~ (v2_pre_topc @ X16)
% 0.80/1.00          | (v2_struct_0 @ X16)
% 0.80/1.00          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.80/1.00          | (m1_subset_1 @ (k7_tmap_1 @ X16 @ X17) @ 
% 0.80/1.00             (k1_zfmisc_1 @ 
% 0.80/1.00              (k2_zfmisc_1 @ (u1_struct_0 @ X16) @ 
% 0.80/1.00               (u1_struct_0 @ (k6_tmap_1 @ X16 @ X17))))))),
% 0.80/1.00      inference('cnf', [status(esa)], [dt_k7_tmap_1])).
% 0.80/1.00  thf('7', plain,
% 0.80/1.00      (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.80/1.00         (k1_zfmisc_1 @ 
% 0.80/1.00          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.80/1.00           (u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))))
% 0.80/1.00        | (v2_struct_0 @ sk_A)
% 0.80/1.00        | ~ (v2_pre_topc @ sk_A)
% 0.80/1.00        | ~ (l1_pre_topc @ sk_A))),
% 0.80/1.00      inference('sup-', [status(thm)], ['5', '6'])).
% 0.80/1.00  thf('8', plain,
% 0.80/1.00      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.80/1.00        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.80/1.00      inference('demod', [status(thm)], ['3', '4'])).
% 0.80/1.00  thf(t104_tmap_1, axiom,
% 0.80/1.00    (![A:$i]:
% 0.80/1.00     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.80/1.00       ( ![B:$i]:
% 0.80/1.00         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.80/1.00           ( ( ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) = ( u1_struct_0 @ A ) ) & 
% 0.80/1.00             ( ( u1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) = ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.80/1.00  thf('9', plain,
% 0.80/1.00      (![X20 : $i, X21 : $i]:
% 0.80/1.00         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.80/1.00          | ((u1_struct_0 @ (k6_tmap_1 @ X21 @ X20)) = (u1_struct_0 @ X21))
% 0.80/1.00          | ~ (l1_pre_topc @ X21)
% 0.80/1.00          | ~ (v2_pre_topc @ X21)
% 0.80/1.00          | (v2_struct_0 @ X21))),
% 0.80/1.00      inference('cnf', [status(esa)], [t104_tmap_1])).
% 0.80/1.00  thf('10', plain,
% 0.80/1.00      (((v2_struct_0 @ sk_A)
% 0.80/1.00        | ~ (v2_pre_topc @ sk_A)
% 0.80/1.00        | ~ (l1_pre_topc @ sk_A)
% 0.80/1.00        | ((u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.80/1.00            = (u1_struct_0 @ sk_A)))),
% 0.80/1.00      inference('sup-', [status(thm)], ['8', '9'])).
% 0.80/1.00  thf('11', plain, ((v2_pre_topc @ sk_A)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('13', plain,
% 0.80/1.00      (((v2_struct_0 @ sk_A)
% 0.80/1.00        | ((u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.80/1.00            = (u1_struct_0 @ sk_A)))),
% 0.80/1.00      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.80/1.00  thf('14', plain, (~ (v2_struct_0 @ sk_A)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('15', plain,
% 0.80/1.00      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.80/1.00         = (u1_struct_0 @ sk_A))),
% 0.80/1.00      inference('clc', [status(thm)], ['13', '14'])).
% 0.80/1.00  thf('16', plain, ((v2_pre_topc @ sk_A)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('18', plain,
% 0.80/1.00      (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.80/1.00         (k1_zfmisc_1 @ 
% 0.80/1.00          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 0.80/1.00        | (v2_struct_0 @ sk_A))),
% 0.80/1.00      inference('demod', [status(thm)], ['7', '15', '16', '17'])).
% 0.80/1.00  thf('19', plain, (~ (v2_struct_0 @ sk_A)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('20', plain,
% 0.80/1.00      ((m1_subset_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.80/1.00        (k1_zfmisc_1 @ 
% 0.80/1.00         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))),
% 0.80/1.00      inference('clc', [status(thm)], ['18', '19'])).
% 0.80/1.00  thf('21', plain,
% 0.80/1.00      ((m1_subset_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.80/1.00        (k1_zfmisc_1 @ 
% 0.80/1.00         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))),
% 0.80/1.00      inference('clc', [status(thm)], ['18', '19'])).
% 0.80/1.00  thf(redefinition_r1_funct_2, axiom,
% 0.80/1.00    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.80/1.00     ( ( ( ~( v1_xboole_0 @ B ) ) & ( ~( v1_xboole_0 @ D ) ) & 
% 0.80/1.00         ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ B ) & 
% 0.80/1.00         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.80/1.00         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ C @ D ) & 
% 0.80/1.00         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.80/1.00       ( ( r1_funct_2 @ A @ B @ C @ D @ E @ F ) <=> ( ( E ) = ( F ) ) ) ))).
% 0.80/1.00  thf('22', plain,
% 0.80/1.00      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.80/1.00         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4)))
% 0.80/1.00          | ~ (v1_funct_2 @ X2 @ X3 @ X4)
% 0.80/1.00          | ~ (v1_funct_1 @ X2)
% 0.80/1.00          | (v1_xboole_0 @ X5)
% 0.80/1.00          | (v1_xboole_0 @ X4)
% 0.80/1.00          | ~ (v1_funct_1 @ X6)
% 0.80/1.00          | ~ (v1_funct_2 @ X6 @ X7 @ X5)
% 0.80/1.00          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X5)))
% 0.80/1.00          | (r1_funct_2 @ X3 @ X4 @ X7 @ X5 @ X2 @ X6)
% 0.80/1.00          | ((X2) != (X6)))),
% 0.80/1.00      inference('cnf', [status(esa)], [redefinition_r1_funct_2])).
% 0.80/1.00  thf('23', plain,
% 0.80/1.00      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.80/1.00         ((r1_funct_2 @ X3 @ X4 @ X7 @ X5 @ X6 @ X6)
% 0.80/1.00          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X5)))
% 0.80/1.00          | ~ (v1_funct_2 @ X6 @ X7 @ X5)
% 0.80/1.00          | (v1_xboole_0 @ X4)
% 0.80/1.00          | (v1_xboole_0 @ X5)
% 0.80/1.00          | ~ (v1_funct_1 @ X6)
% 0.80/1.00          | ~ (v1_funct_2 @ X6 @ X3 @ X4)
% 0.80/1.00          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4))))),
% 0.80/1.00      inference('simplify', [status(thm)], ['22'])).
% 0.80/1.00  thf('24', plain,
% 0.80/1.00      (![X0 : $i, X1 : $i]:
% 0.80/1.00         (~ (m1_subset_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.80/1.00             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 0.80/1.00          | ~ (v1_funct_2 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ X1 @ X0)
% 0.80/1.00          | ~ (v1_funct_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.80/1.00          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.80/1.00          | (v1_xboole_0 @ X0)
% 0.80/1.00          | ~ (v1_funct_2 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.80/1.00               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.80/1.00          | (r1_funct_2 @ X1 @ X0 @ (u1_struct_0 @ sk_A) @ 
% 0.80/1.00             (u1_struct_0 @ sk_A) @ 
% 0.80/1.00             (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.80/1.00             (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))),
% 0.80/1.00      inference('sup-', [status(thm)], ['21', '23'])).
% 0.80/1.00  thf('25', plain,
% 0.80/1.00      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.80/1.00        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.80/1.00      inference('demod', [status(thm)], ['3', '4'])).
% 0.80/1.00  thf('26', plain,
% 0.80/1.00      (![X16 : $i, X17 : $i]:
% 0.80/1.00         (~ (l1_pre_topc @ X16)
% 0.80/1.00          | ~ (v2_pre_topc @ X16)
% 0.80/1.00          | (v2_struct_0 @ X16)
% 0.80/1.00          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.80/1.00          | (v1_funct_1 @ (k7_tmap_1 @ X16 @ X17)))),
% 0.80/1.00      inference('cnf', [status(esa)], [dt_k7_tmap_1])).
% 0.80/1.00  thf('27', plain,
% 0.80/1.00      (((v1_funct_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.80/1.00        | (v2_struct_0 @ sk_A)
% 0.80/1.00        | ~ (v2_pre_topc @ sk_A)
% 0.80/1.00        | ~ (l1_pre_topc @ sk_A))),
% 0.80/1.00      inference('sup-', [status(thm)], ['25', '26'])).
% 0.80/1.00  thf('28', plain, ((v2_pre_topc @ sk_A)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('30', plain,
% 0.80/1.00      (((v1_funct_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.80/1.00        | (v2_struct_0 @ sk_A))),
% 0.80/1.00      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.80/1.00  thf('31', plain, (~ (v2_struct_0 @ sk_A)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('32', plain, ((v1_funct_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.80/1.00      inference('clc', [status(thm)], ['30', '31'])).
% 0.80/1.00  thf('33', plain,
% 0.80/1.00      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.80/1.00        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.80/1.00      inference('demod', [status(thm)], ['3', '4'])).
% 0.80/1.00  thf('34', plain,
% 0.80/1.00      (![X16 : $i, X17 : $i]:
% 0.80/1.00         (~ (l1_pre_topc @ X16)
% 0.80/1.00          | ~ (v2_pre_topc @ X16)
% 0.80/1.00          | (v2_struct_0 @ X16)
% 0.80/1.00          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.80/1.00          | (v1_funct_2 @ (k7_tmap_1 @ X16 @ X17) @ (u1_struct_0 @ X16) @ 
% 0.80/1.00             (u1_struct_0 @ (k6_tmap_1 @ X16 @ X17))))),
% 0.80/1.00      inference('cnf', [status(esa)], [dt_k7_tmap_1])).
% 0.80/1.00  thf('35', plain,
% 0.80/1.00      (((v1_funct_2 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.80/1.00         (u1_struct_0 @ sk_A) @ 
% 0.80/1.00         (u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))
% 0.80/1.00        | (v2_struct_0 @ sk_A)
% 0.80/1.00        | ~ (v2_pre_topc @ sk_A)
% 0.80/1.00        | ~ (l1_pre_topc @ sk_A))),
% 0.80/1.00      inference('sup-', [status(thm)], ['33', '34'])).
% 0.80/1.00  thf('36', plain,
% 0.80/1.00      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.80/1.00         = (u1_struct_0 @ sk_A))),
% 0.80/1.00      inference('clc', [status(thm)], ['13', '14'])).
% 0.80/1.00  thf('37', plain, ((v2_pre_topc @ sk_A)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('39', plain,
% 0.80/1.00      (((v1_funct_2 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.80/1.00         (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.80/1.00        | (v2_struct_0 @ sk_A))),
% 0.80/1.00      inference('demod', [status(thm)], ['35', '36', '37', '38'])).
% 0.80/1.00  thf('40', plain, (~ (v2_struct_0 @ sk_A)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('41', plain,
% 0.80/1.00      ((v1_funct_2 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.80/1.00        (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.80/1.00      inference('clc', [status(thm)], ['39', '40'])).
% 0.80/1.00  thf('42', plain,
% 0.80/1.00      (![X0 : $i, X1 : $i]:
% 0.80/1.00         (~ (m1_subset_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.80/1.00             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 0.80/1.00          | ~ (v1_funct_2 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ X1 @ X0)
% 0.80/1.00          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.80/1.00          | (v1_xboole_0 @ X0)
% 0.80/1.00          | (r1_funct_2 @ X1 @ X0 @ (u1_struct_0 @ sk_A) @ 
% 0.80/1.00             (u1_struct_0 @ sk_A) @ 
% 0.80/1.00             (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.80/1.00             (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))),
% 0.80/1.00      inference('demod', [status(thm)], ['24', '32', '41'])).
% 0.80/1.00  thf('43', plain,
% 0.80/1.00      (((r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.80/1.00         (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.80/1.00         (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.80/1.00         (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.80/1.00        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.80/1.00        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.80/1.00        | ~ (v1_funct_2 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.80/1.00             (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.80/1.00      inference('sup-', [status(thm)], ['20', '42'])).
% 0.80/1.00  thf('44', plain,
% 0.80/1.00      ((v1_funct_2 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.80/1.00        (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.80/1.00      inference('clc', [status(thm)], ['39', '40'])).
% 0.80/1.00  thf('45', plain,
% 0.80/1.00      (((r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.80/1.00         (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.80/1.00         (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.80/1.00         (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.80/1.00        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.80/1.00        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.80/1.00      inference('demod', [status(thm)], ['43', '44'])).
% 0.80/1.00  thf('46', plain,
% 0.80/1.00      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.80/1.00        | (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.80/1.00           (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.80/1.00           (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.80/1.00           (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))),
% 0.80/1.00      inference('simplify', [status(thm)], ['45'])).
% 0.80/1.00  thf('47', plain,
% 0.80/1.00      ((m1_subset_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.80/1.00        (k1_zfmisc_1 @ 
% 0.80/1.00         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))),
% 0.80/1.00      inference('clc', [status(thm)], ['18', '19'])).
% 0.80/1.00  thf('48', plain,
% 0.80/1.00      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.80/1.00         = (u1_struct_0 @ sk_A))),
% 0.80/1.00      inference('clc', [status(thm)], ['13', '14'])).
% 0.80/1.00  thf('49', plain,
% 0.80/1.00      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.80/1.00        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.80/1.00      inference('demod', [status(thm)], ['3', '4'])).
% 0.80/1.00  thf(d11_tmap_1, axiom,
% 0.80/1.00    (![A:$i]:
% 0.80/1.00     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.80/1.00       ( ![B:$i]:
% 0.80/1.00         ( ( m1_pre_topc @ B @ A ) =>
% 0.80/1.00           ( ![C:$i]:
% 0.80/1.00             ( ( ( v1_pre_topc @ C ) & ( v2_pre_topc @ C ) & 
% 0.80/1.00                 ( l1_pre_topc @ C ) ) =>
% 0.80/1.00               ( ( ( C ) = ( k8_tmap_1 @ A @ B ) ) <=>
% 0.80/1.00                 ( ![D:$i]:
% 0.80/1.00                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.80/1.00                     ( ( ( D ) = ( u1_struct_0 @ B ) ) =>
% 0.80/1.00                       ( ( C ) = ( k6_tmap_1 @ A @ D ) ) ) ) ) ) ) ) ) ) ))).
% 0.80/1.00  thf('50', plain,
% 0.80/1.00      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.80/1.00         (~ (m1_pre_topc @ X8 @ X9)
% 0.80/1.00          | ((X10) != (k8_tmap_1 @ X9 @ X8))
% 0.80/1.00          | ((X11) != (u1_struct_0 @ X8))
% 0.80/1.00          | ((X10) = (k6_tmap_1 @ X9 @ X11))
% 0.80/1.00          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.80/1.00          | ~ (l1_pre_topc @ X10)
% 0.80/1.00          | ~ (v2_pre_topc @ X10)
% 0.80/1.00          | ~ (v1_pre_topc @ X10)
% 0.80/1.00          | ~ (l1_pre_topc @ X9)
% 0.80/1.00          | ~ (v2_pre_topc @ X9)
% 0.80/1.00          | (v2_struct_0 @ X9))),
% 0.80/1.00      inference('cnf', [status(esa)], [d11_tmap_1])).
% 0.80/1.00  thf('51', plain,
% 0.80/1.00      (![X8 : $i, X9 : $i]:
% 0.80/1.00         ((v2_struct_0 @ X9)
% 0.80/1.00          | ~ (v2_pre_topc @ X9)
% 0.80/1.00          | ~ (l1_pre_topc @ X9)
% 0.80/1.00          | ~ (v1_pre_topc @ (k8_tmap_1 @ X9 @ X8))
% 0.80/1.00          | ~ (v2_pre_topc @ (k8_tmap_1 @ X9 @ X8))
% 0.80/1.00          | ~ (l1_pre_topc @ (k8_tmap_1 @ X9 @ X8))
% 0.80/1.00          | ~ (m1_subset_1 @ (u1_struct_0 @ X8) @ 
% 0.80/1.00               (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.80/1.00          | ((k8_tmap_1 @ X9 @ X8) = (k6_tmap_1 @ X9 @ (u1_struct_0 @ X8)))
% 0.80/1.00          | ~ (m1_pre_topc @ X8 @ X9))),
% 0.80/1.00      inference('simplify', [status(thm)], ['50'])).
% 0.80/1.00  thf('52', plain,
% 0.80/1.00      ((~ (m1_pre_topc @ sk_B @ sk_A)
% 0.80/1.00        | ((k8_tmap_1 @ sk_A @ sk_B)
% 0.80/1.00            = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.80/1.00        | ~ (l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.80/1.00        | ~ (v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.80/1.00        | ~ (v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.80/1.00        | ~ (l1_pre_topc @ sk_A)
% 0.80/1.00        | ~ (v2_pre_topc @ sk_A)
% 0.80/1.00        | (v2_struct_0 @ sk_A))),
% 0.80/1.00      inference('sup-', [status(thm)], ['49', '51'])).
% 0.80/1.00  thf('53', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('54', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf(dt_k8_tmap_1, axiom,
% 0.80/1.00    (![A:$i,B:$i]:
% 0.80/1.00     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.80/1.00         ( l1_pre_topc @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.80/1.00       ( ( v1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) & 
% 0.80/1.00         ( v2_pre_topc @ ( k8_tmap_1 @ A @ B ) ) & 
% 0.80/1.00         ( l1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) ) ))).
% 0.80/1.00  thf('55', plain,
% 0.80/1.00      (![X18 : $i, X19 : $i]:
% 0.80/1.00         (~ (l1_pre_topc @ X18)
% 0.80/1.00          | ~ (v2_pre_topc @ X18)
% 0.80/1.00          | (v2_struct_0 @ X18)
% 0.80/1.00          | ~ (m1_pre_topc @ X19 @ X18)
% 0.80/1.00          | (l1_pre_topc @ (k8_tmap_1 @ X18 @ X19)))),
% 0.80/1.00      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 0.80/1.00  thf('56', plain,
% 0.80/1.00      (((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.80/1.00        | (v2_struct_0 @ sk_A)
% 0.80/1.00        | ~ (v2_pre_topc @ sk_A)
% 0.80/1.00        | ~ (l1_pre_topc @ sk_A))),
% 0.80/1.00      inference('sup-', [status(thm)], ['54', '55'])).
% 0.80/1.00  thf('57', plain, ((v2_pre_topc @ sk_A)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('58', plain, ((l1_pre_topc @ sk_A)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('59', plain,
% 0.80/1.00      (((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.80/1.00      inference('demod', [status(thm)], ['56', '57', '58'])).
% 0.80/1.00  thf('60', plain, (~ (v2_struct_0 @ sk_A)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('61', plain, ((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.80/1.00      inference('clc', [status(thm)], ['59', '60'])).
% 0.80/1.00  thf('62', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('63', plain,
% 0.80/1.00      (![X18 : $i, X19 : $i]:
% 0.80/1.00         (~ (l1_pre_topc @ X18)
% 0.80/1.00          | ~ (v2_pre_topc @ X18)
% 0.80/1.00          | (v2_struct_0 @ X18)
% 0.80/1.00          | ~ (m1_pre_topc @ X19 @ X18)
% 0.80/1.00          | (v2_pre_topc @ (k8_tmap_1 @ X18 @ X19)))),
% 0.80/1.00      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 0.80/1.00  thf('64', plain,
% 0.80/1.00      (((v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.80/1.00        | (v2_struct_0 @ sk_A)
% 0.80/1.00        | ~ (v2_pre_topc @ sk_A)
% 0.80/1.00        | ~ (l1_pre_topc @ sk_A))),
% 0.80/1.00      inference('sup-', [status(thm)], ['62', '63'])).
% 0.80/1.00  thf('65', plain, ((v2_pre_topc @ sk_A)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('66', plain, ((l1_pre_topc @ sk_A)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('67', plain,
% 0.80/1.00      (((v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.80/1.00      inference('demod', [status(thm)], ['64', '65', '66'])).
% 0.80/1.00  thf('68', plain, (~ (v2_struct_0 @ sk_A)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('69', plain, ((v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.80/1.00      inference('clc', [status(thm)], ['67', '68'])).
% 0.80/1.00  thf('70', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('71', plain,
% 0.80/1.00      (![X18 : $i, X19 : $i]:
% 0.80/1.00         (~ (l1_pre_topc @ X18)
% 0.80/1.00          | ~ (v2_pre_topc @ X18)
% 0.80/1.00          | (v2_struct_0 @ X18)
% 0.80/1.00          | ~ (m1_pre_topc @ X19 @ X18)
% 0.80/1.00          | (v1_pre_topc @ (k8_tmap_1 @ X18 @ X19)))),
% 0.80/1.00      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 0.80/1.00  thf('72', plain,
% 0.80/1.00      (((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.80/1.00        | (v2_struct_0 @ sk_A)
% 0.80/1.00        | ~ (v2_pre_topc @ sk_A)
% 0.80/1.00        | ~ (l1_pre_topc @ sk_A))),
% 0.80/1.00      inference('sup-', [status(thm)], ['70', '71'])).
% 0.80/1.00  thf('73', plain, ((v2_pre_topc @ sk_A)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('74', plain, ((l1_pre_topc @ sk_A)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('75', plain,
% 0.80/1.00      (((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.80/1.00      inference('demod', [status(thm)], ['72', '73', '74'])).
% 0.80/1.00  thf('76', plain, (~ (v2_struct_0 @ sk_A)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('77', plain, ((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.80/1.00      inference('clc', [status(thm)], ['75', '76'])).
% 0.80/1.00  thf('78', plain, ((l1_pre_topc @ sk_A)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('79', plain, ((v2_pre_topc @ sk_A)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('80', plain,
% 0.80/1.00      ((((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.80/1.00        | (v2_struct_0 @ sk_A))),
% 0.80/1.00      inference('demod', [status(thm)],
% 0.80/1.00                ['52', '53', '61', '69', '77', '78', '79'])).
% 0.80/1.00  thf('81', plain, (~ (v2_struct_0 @ sk_A)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('82', plain,
% 0.80/1.00      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.80/1.00      inference('clc', [status(thm)], ['80', '81'])).
% 0.80/1.00  thf('83', plain,
% 0.80/1.00      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.80/1.00      inference('demod', [status(thm)], ['48', '82'])).
% 0.80/1.00  thf(d12_tmap_1, axiom,
% 0.80/1.00    (![A:$i]:
% 0.80/1.00     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.80/1.00       ( ![B:$i]:
% 0.80/1.00         ( ( m1_pre_topc @ B @ A ) =>
% 0.80/1.00           ( ![C:$i]:
% 0.80/1.00             ( ( ( v1_funct_1 @ C ) & 
% 0.80/1.00                 ( v1_funct_2 @
% 0.80/1.00                   C @ ( u1_struct_0 @ A ) @ 
% 0.80/1.00                   ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) & 
% 0.80/1.00                 ( m1_subset_1 @
% 0.80/1.00                   C @ 
% 0.80/1.00                   ( k1_zfmisc_1 @
% 0.80/1.00                     ( k2_zfmisc_1 @
% 0.80/1.00                       ( u1_struct_0 @ A ) @ 
% 0.80/1.00                       ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) ) ) ) =>
% 0.80/1.00               ( ( ( C ) = ( k9_tmap_1 @ A @ B ) ) <=>
% 0.80/1.00                 ( ![D:$i]:
% 0.80/1.00                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.80/1.00                     ( ( ( D ) = ( u1_struct_0 @ B ) ) =>
% 0.80/1.00                       ( r1_funct_2 @
% 0.80/1.00                         ( u1_struct_0 @ A ) @ 
% 0.80/1.00                         ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) @ 
% 0.80/1.00                         ( u1_struct_0 @ A ) @ 
% 0.80/1.00                         ( u1_struct_0 @ ( k6_tmap_1 @ A @ D ) ) @ C @ 
% 0.80/1.00                         ( k7_tmap_1 @ A @ D ) ) ) ) ) ) ) ) ) ) ))).
% 0.80/1.00  thf('84', plain,
% 0.80/1.00      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.80/1.00         (~ (m1_pre_topc @ X12 @ X13)
% 0.80/1.00          | ((sk_D_1 @ X14 @ X12 @ X13) = (u1_struct_0 @ X12))
% 0.80/1.00          | ((X14) = (k9_tmap_1 @ X13 @ X12))
% 0.80/1.00          | ~ (m1_subset_1 @ X14 @ 
% 0.80/1.00               (k1_zfmisc_1 @ 
% 0.80/1.00                (k2_zfmisc_1 @ (u1_struct_0 @ X13) @ 
% 0.80/1.00                 (u1_struct_0 @ (k8_tmap_1 @ X13 @ X12)))))
% 0.80/1.00          | ~ (v1_funct_2 @ X14 @ (u1_struct_0 @ X13) @ 
% 0.80/1.00               (u1_struct_0 @ (k8_tmap_1 @ X13 @ X12)))
% 0.80/1.00          | ~ (v1_funct_1 @ X14)
% 0.80/1.00          | ~ (l1_pre_topc @ X13)
% 0.80/1.00          | ~ (v2_pre_topc @ X13)
% 0.80/1.00          | (v2_struct_0 @ X13))),
% 0.80/1.00      inference('cnf', [status(esa)], [d12_tmap_1])).
% 0.80/1.00  thf('85', plain,
% 0.80/1.00      (![X0 : $i]:
% 0.80/1.00         (~ (m1_subset_1 @ X0 @ 
% 0.80/1.00             (k1_zfmisc_1 @ 
% 0.80/1.00              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 0.80/1.00          | (v2_struct_0 @ sk_A)
% 0.80/1.00          | ~ (v2_pre_topc @ sk_A)
% 0.80/1.00          | ~ (l1_pre_topc @ sk_A)
% 0.80/1.00          | ~ (v1_funct_1 @ X0)
% 0.80/1.00          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ 
% 0.80/1.00               (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.80/1.00          | ((X0) = (k9_tmap_1 @ sk_A @ sk_B))
% 0.80/1.00          | ((sk_D_1 @ X0 @ sk_B @ sk_A) = (u1_struct_0 @ sk_B))
% 0.80/1.00          | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 0.80/1.00      inference('sup-', [status(thm)], ['83', '84'])).
% 0.80/1.00  thf('86', plain, ((v2_pre_topc @ sk_A)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('87', plain, ((l1_pre_topc @ sk_A)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('88', plain,
% 0.80/1.00      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.80/1.00      inference('demod', [status(thm)], ['48', '82'])).
% 0.80/1.00  thf('89', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('90', plain,
% 0.80/1.00      (![X0 : $i]:
% 0.80/1.00         (~ (m1_subset_1 @ X0 @ 
% 0.80/1.00             (k1_zfmisc_1 @ 
% 0.80/1.00              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 0.80/1.00          | (v2_struct_0 @ sk_A)
% 0.80/1.00          | ~ (v1_funct_1 @ X0)
% 0.80/1.00          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.80/1.00          | ((X0) = (k9_tmap_1 @ sk_A @ sk_B))
% 0.80/1.00          | ((sk_D_1 @ X0 @ sk_B @ sk_A) = (u1_struct_0 @ sk_B)))),
% 0.80/1.00      inference('demod', [status(thm)], ['85', '86', '87', '88', '89'])).
% 0.80/1.00  thf('91', plain,
% 0.80/1.00      ((((sk_D_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_B @ sk_A)
% 0.80/1.00          = (u1_struct_0 @ sk_B))
% 0.80/1.00        | ((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))
% 0.80/1.00            = (k9_tmap_1 @ sk_A @ sk_B))
% 0.80/1.00        | ~ (v1_funct_2 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.80/1.00             (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.80/1.00        | ~ (v1_funct_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.80/1.00        | (v2_struct_0 @ sk_A))),
% 0.80/1.00      inference('sup-', [status(thm)], ['47', '90'])).
% 0.80/1.00  thf('92', plain,
% 0.80/1.00      ((v1_funct_2 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.80/1.00        (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.80/1.00      inference('clc', [status(thm)], ['39', '40'])).
% 0.80/1.00  thf('93', plain, ((v1_funct_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.80/1.00      inference('clc', [status(thm)], ['30', '31'])).
% 0.80/1.00  thf('94', plain,
% 0.80/1.00      ((((sk_D_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_B @ sk_A)
% 0.80/1.00          = (u1_struct_0 @ sk_B))
% 0.80/1.00        | ((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))
% 0.80/1.00            = (k9_tmap_1 @ sk_A @ sk_B))
% 0.80/1.00        | (v2_struct_0 @ sk_A))),
% 0.80/1.00      inference('demod', [status(thm)], ['91', '92', '93'])).
% 0.80/1.00  thf('95', plain, (~ (v2_struct_0 @ sk_A)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('96', plain,
% 0.80/1.00      ((((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) = (k9_tmap_1 @ sk_A @ sk_B))
% 0.80/1.00        | ((sk_D_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_B @ sk_A)
% 0.80/1.00            = (u1_struct_0 @ sk_B)))),
% 0.80/1.00      inference('clc', [status(thm)], ['94', '95'])).
% 0.80/1.00  thf('97', plain,
% 0.80/1.00      ((((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) = (k9_tmap_1 @ sk_A @ sk_B))
% 0.80/1.00        | ((sk_D_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_B @ sk_A)
% 0.80/1.00            = (u1_struct_0 @ sk_B)))),
% 0.80/1.00      inference('clc', [status(thm)], ['94', '95'])).
% 0.80/1.00  thf('98', plain,
% 0.80/1.00      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.80/1.00         (~ (m1_pre_topc @ X12 @ X13)
% 0.80/1.00          | ~ (r1_funct_2 @ (u1_struct_0 @ X13) @ 
% 0.80/1.00               (u1_struct_0 @ (k8_tmap_1 @ X13 @ X12)) @ (u1_struct_0 @ X13) @ 
% 0.80/1.00               (u1_struct_0 @ (k6_tmap_1 @ X13 @ (sk_D_1 @ X14 @ X12 @ X13))) @ 
% 0.80/1.00               X14 @ (k7_tmap_1 @ X13 @ (sk_D_1 @ X14 @ X12 @ X13)))
% 0.80/1.00          | ((X14) = (k9_tmap_1 @ X13 @ X12))
% 0.80/1.00          | ~ (m1_subset_1 @ X14 @ 
% 0.80/1.00               (k1_zfmisc_1 @ 
% 0.80/1.00                (k2_zfmisc_1 @ (u1_struct_0 @ X13) @ 
% 0.80/1.00                 (u1_struct_0 @ (k8_tmap_1 @ X13 @ X12)))))
% 0.80/1.00          | ~ (v1_funct_2 @ X14 @ (u1_struct_0 @ X13) @ 
% 0.80/1.00               (u1_struct_0 @ (k8_tmap_1 @ X13 @ X12)))
% 0.80/1.00          | ~ (v1_funct_1 @ X14)
% 0.80/1.00          | ~ (l1_pre_topc @ X13)
% 0.80/1.00          | ~ (v2_pre_topc @ X13)
% 0.80/1.00          | (v2_struct_0 @ X13))),
% 0.80/1.00      inference('cnf', [status(esa)], [d12_tmap_1])).
% 0.80/1.00  thf('99', plain,
% 0.80/1.00      ((~ (r1_funct_2 @ (u1_struct_0 @ sk_A) @ 
% 0.80/1.00           (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) @ (u1_struct_0 @ sk_A) @ 
% 0.80/1.00           (u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))) @ 
% 0.80/1.00           (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.80/1.00           (k7_tmap_1 @ sk_A @ 
% 0.80/1.00            (sk_D_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_B @ sk_A)))
% 0.80/1.00        | ((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))
% 0.80/1.00            = (k9_tmap_1 @ sk_A @ sk_B))
% 0.80/1.00        | (v2_struct_0 @ sk_A)
% 0.80/1.00        | ~ (v2_pre_topc @ sk_A)
% 0.80/1.00        | ~ (l1_pre_topc @ sk_A)
% 0.80/1.00        | ~ (v1_funct_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.80/1.00        | ~ (v1_funct_2 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.80/1.00             (u1_struct_0 @ sk_A) @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.80/1.00        | ~ (m1_subset_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.80/1.00             (k1_zfmisc_1 @ 
% 0.80/1.00              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.80/1.00               (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))
% 0.80/1.00        | ((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))
% 0.80/1.00            = (k9_tmap_1 @ sk_A @ sk_B))
% 0.80/1.00        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 0.80/1.00      inference('sup-', [status(thm)], ['97', '98'])).
% 0.80/1.00  thf('100', plain,
% 0.80/1.00      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.80/1.00      inference('demod', [status(thm)], ['48', '82'])).
% 0.80/1.00  thf('101', plain,
% 0.80/1.00      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.80/1.00      inference('clc', [status(thm)], ['80', '81'])).
% 0.80/1.00  thf('102', plain,
% 0.80/1.00      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.80/1.00      inference('demod', [status(thm)], ['48', '82'])).
% 0.80/1.00  thf('103', plain, ((v2_pre_topc @ sk_A)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('104', plain, ((l1_pre_topc @ sk_A)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('105', plain, ((v1_funct_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.80/1.00      inference('clc', [status(thm)], ['30', '31'])).
% 0.80/1.00  thf('106', plain,
% 0.80/1.00      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.80/1.00      inference('demod', [status(thm)], ['48', '82'])).
% 0.80/1.00  thf('107', plain,
% 0.80/1.00      ((v1_funct_2 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.80/1.00        (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.80/1.00      inference('clc', [status(thm)], ['39', '40'])).
% 0.80/1.00  thf('108', plain,
% 0.80/1.00      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.80/1.00      inference('demod', [status(thm)], ['48', '82'])).
% 0.80/1.00  thf('109', plain,
% 0.80/1.00      ((m1_subset_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.80/1.00        (k1_zfmisc_1 @ 
% 0.80/1.00         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))),
% 0.80/1.00      inference('clc', [status(thm)], ['18', '19'])).
% 0.80/1.00  thf('110', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('111', plain,
% 0.80/1.00      ((~ (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.80/1.00           (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.80/1.00           (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.80/1.00           (k7_tmap_1 @ sk_A @ 
% 0.80/1.00            (sk_D_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_B @ sk_A)))
% 0.80/1.00        | ((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))
% 0.80/1.00            = (k9_tmap_1 @ sk_A @ sk_B))
% 0.80/1.00        | (v2_struct_0 @ sk_A)
% 0.80/1.00        | ((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))
% 0.80/1.00            = (k9_tmap_1 @ sk_A @ sk_B)))),
% 0.80/1.00      inference('demod', [status(thm)],
% 0.80/1.00                ['99', '100', '101', '102', '103', '104', '105', '106', '107', 
% 0.80/1.00                 '108', '109', '110'])).
% 0.80/1.00  thf('112', plain,
% 0.80/1.00      (((v2_struct_0 @ sk_A)
% 0.80/1.00        | ((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))
% 0.80/1.00            = (k9_tmap_1 @ sk_A @ sk_B))
% 0.80/1.00        | ~ (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.80/1.00             (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.80/1.00             (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.80/1.00             (k7_tmap_1 @ sk_A @ 
% 0.80/1.00              (sk_D_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_B @ sk_A))))),
% 0.80/1.00      inference('simplify', [status(thm)], ['111'])).
% 0.80/1.00  thf('113', plain, (~ (v2_struct_0 @ sk_A)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('114', plain,
% 0.80/1.00      ((~ (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.80/1.00           (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.80/1.00           (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.80/1.00           (k7_tmap_1 @ sk_A @ 
% 0.80/1.00            (sk_D_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_B @ sk_A)))
% 0.80/1.00        | ((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))
% 0.80/1.00            = (k9_tmap_1 @ sk_A @ sk_B)))),
% 0.80/1.00      inference('clc', [status(thm)], ['112', '113'])).
% 0.80/1.00  thf('115', plain,
% 0.80/1.00      ((~ (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.80/1.00           (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.80/1.00           (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.80/1.00           (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.80/1.00        | ((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))
% 0.80/1.00            = (k9_tmap_1 @ sk_A @ sk_B))
% 0.80/1.00        | ((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))
% 0.80/1.00            = (k9_tmap_1 @ sk_A @ sk_B)))),
% 0.80/1.00      inference('sup-', [status(thm)], ['96', '114'])).
% 0.80/1.00  thf('116', plain,
% 0.80/1.00      ((((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) = (k9_tmap_1 @ sk_A @ sk_B))
% 0.80/1.00        | ~ (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.80/1.00             (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.80/1.00             (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.80/1.00             (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))),
% 0.80/1.00      inference('simplify', [status(thm)], ['115'])).
% 0.80/1.00  thf('117', plain,
% 0.80/1.00      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.80/1.00        | ((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))
% 0.80/1.00            = (k9_tmap_1 @ sk_A @ sk_B)))),
% 0.80/1.00      inference('sup-', [status(thm)], ['46', '116'])).
% 0.80/1.00  thf('118', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_B))),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('119', plain,
% 0.80/1.00      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.80/1.00        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.80/1.00      inference('demod', [status(thm)], ['3', '4'])).
% 0.80/1.00  thf(t110_tmap_1, axiom,
% 0.80/1.00    (![A:$i]:
% 0.80/1.00     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.80/1.00       ( ![B:$i]:
% 0.80/1.00         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.80/1.00           ( ![C:$i]:
% 0.80/1.00             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.80/1.00               ( ( ( u1_struct_0 @ C ) = ( B ) ) =>
% 0.80/1.00                 ( ![D:$i]:
% 0.80/1.00                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ C ) ) =>
% 0.80/1.00                     ( r1_tmap_1 @
% 0.80/1.00                       C @ ( k6_tmap_1 @ A @ B ) @ 
% 0.80/1.00                       ( k2_tmap_1 @
% 0.80/1.00                         A @ ( k6_tmap_1 @ A @ B ) @ ( k7_tmap_1 @ A @ B ) @ C ) @ 
% 0.80/1.00                       D ) ) ) ) ) ) ) ) ))).
% 0.80/1.00  thf('120', plain,
% 0.80/1.00      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.80/1.00         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.80/1.00          | ((u1_struct_0 @ X24) != (X22))
% 0.80/1.00          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X24))
% 0.80/1.00          | (r1_tmap_1 @ X24 @ (k6_tmap_1 @ X23 @ X22) @ 
% 0.80/1.00             (k2_tmap_1 @ X23 @ (k6_tmap_1 @ X23 @ X22) @ 
% 0.80/1.00              (k7_tmap_1 @ X23 @ X22) @ X24) @ 
% 0.80/1.00             X25)
% 0.80/1.00          | ~ (m1_pre_topc @ X24 @ X23)
% 0.80/1.00          | (v2_struct_0 @ X24)
% 0.80/1.00          | ~ (l1_pre_topc @ X23)
% 0.80/1.00          | ~ (v2_pre_topc @ X23)
% 0.80/1.00          | (v2_struct_0 @ X23))),
% 0.80/1.00      inference('cnf', [status(esa)], [t110_tmap_1])).
% 0.80/1.00  thf('121', plain,
% 0.80/1.00      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.80/1.00         ((v2_struct_0 @ X23)
% 0.80/1.00          | ~ (v2_pre_topc @ X23)
% 0.80/1.00          | ~ (l1_pre_topc @ X23)
% 0.80/1.00          | (v2_struct_0 @ X24)
% 0.80/1.00          | ~ (m1_pre_topc @ X24 @ X23)
% 0.80/1.00          | (r1_tmap_1 @ X24 @ (k6_tmap_1 @ X23 @ (u1_struct_0 @ X24)) @ 
% 0.80/1.00             (k2_tmap_1 @ X23 @ (k6_tmap_1 @ X23 @ (u1_struct_0 @ X24)) @ 
% 0.80/1.00              (k7_tmap_1 @ X23 @ (u1_struct_0 @ X24)) @ X24) @ 
% 0.80/1.00             X25)
% 0.80/1.00          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X24))
% 0.80/1.00          | ~ (m1_subset_1 @ (u1_struct_0 @ X24) @ 
% 0.80/1.00               (k1_zfmisc_1 @ (u1_struct_0 @ X23))))),
% 0.80/1.00      inference('simplify', [status(thm)], ['120'])).
% 0.80/1.00  thf('122', plain,
% 0.80/1.00      (![X0 : $i]:
% 0.80/1.00         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.80/1.00          | (r1_tmap_1 @ sk_B @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.80/1.00             (k2_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.80/1.00              (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_B) @ 
% 0.80/1.00             X0)
% 0.80/1.00          | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.80/1.00          | (v2_struct_0 @ sk_B)
% 0.80/1.00          | ~ (l1_pre_topc @ sk_A)
% 0.80/1.00          | ~ (v2_pre_topc @ sk_A)
% 0.80/1.00          | (v2_struct_0 @ sk_A))),
% 0.80/1.00      inference('sup-', [status(thm)], ['119', '121'])).
% 0.80/1.00  thf('123', plain,
% 0.80/1.00      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.80/1.00      inference('clc', [status(thm)], ['80', '81'])).
% 0.80/1.00  thf('124', plain,
% 0.80/1.00      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.80/1.00      inference('clc', [status(thm)], ['80', '81'])).
% 0.80/1.00  thf('125', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('126', plain, ((l1_pre_topc @ sk_A)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('127', plain, ((v2_pre_topc @ sk_A)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('128', plain,
% 0.80/1.00      (![X0 : $i]:
% 0.80/1.00         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.80/1.00          | (r1_tmap_1 @ sk_B @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.80/1.00             (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.80/1.00              (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_B) @ 
% 0.80/1.00             X0)
% 0.80/1.00          | (v2_struct_0 @ sk_B)
% 0.80/1.00          | (v2_struct_0 @ sk_A))),
% 0.80/1.00      inference('demod', [status(thm)],
% 0.80/1.00                ['122', '123', '124', '125', '126', '127'])).
% 0.80/1.00  thf('129', plain,
% 0.80/1.00      (((v2_struct_0 @ sk_A)
% 0.80/1.00        | (v2_struct_0 @ sk_B)
% 0.80/1.00        | (r1_tmap_1 @ sk_B @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.80/1.00           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.80/1.00            (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_B) @ 
% 0.80/1.00           sk_C))),
% 0.80/1.00      inference('sup-', [status(thm)], ['118', '128'])).
% 0.80/1.00  thf('130', plain, (~ (v2_struct_0 @ sk_A)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('131', plain,
% 0.80/1.00      (((r1_tmap_1 @ sk_B @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.80/1.00         (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.80/1.00          (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_B) @ 
% 0.80/1.00         sk_C)
% 0.80/1.00        | (v2_struct_0 @ sk_B))),
% 0.80/1.00      inference('clc', [status(thm)], ['129', '130'])).
% 0.80/1.00  thf('132', plain, (~ (v2_struct_0 @ sk_B)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('133', plain,
% 0.80/1.00      ((r1_tmap_1 @ sk_B @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.80/1.00        (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.80/1.00         (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_B) @ 
% 0.80/1.00        sk_C)),
% 0.80/1.00      inference('clc', [status(thm)], ['131', '132'])).
% 0.80/1.00  thf('134', plain,
% 0.80/1.00      (((r1_tmap_1 @ sk_B @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.80/1.00         (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.80/1.00          (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.80/1.00         sk_C)
% 0.80/1.00        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.80/1.00      inference('sup+', [status(thm)], ['117', '133'])).
% 0.80/1.00  thf('135', plain,
% 0.80/1.00      (~ (r1_tmap_1 @ sk_B @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.80/1.00          (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.80/1.00           (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.80/1.00          sk_C)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('136', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.80/1.00      inference('clc', [status(thm)], ['134', '135'])).
% 0.80/1.00  thf(fc2_struct_0, axiom,
% 0.80/1.00    (![A:$i]:
% 0.80/1.00     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.80/1.00       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.80/1.00  thf('137', plain,
% 0.80/1.00      (![X1 : $i]:
% 0.80/1.00         (~ (v1_xboole_0 @ (u1_struct_0 @ X1))
% 0.80/1.00          | ~ (l1_struct_0 @ X1)
% 0.80/1.00          | (v2_struct_0 @ X1))),
% 0.80/1.00      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.80/1.00  thf('138', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.80/1.00      inference('sup-', [status(thm)], ['136', '137'])).
% 0.80/1.00  thf('139', plain, ((l1_pre_topc @ sk_A)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf(dt_l1_pre_topc, axiom,
% 0.80/1.00    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.80/1.00  thf('140', plain, (![X0 : $i]: ((l1_struct_0 @ X0) | ~ (l1_pre_topc @ X0))),
% 0.80/1.00      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.80/1.00  thf('141', plain, ((l1_struct_0 @ sk_A)),
% 0.80/1.00      inference('sup-', [status(thm)], ['139', '140'])).
% 0.80/1.00  thf('142', plain, ((v2_struct_0 @ sk_A)),
% 0.80/1.00      inference('demod', [status(thm)], ['138', '141'])).
% 0.80/1.00  thf('143', plain, ($false), inference('demod', [status(thm)], ['0', '142'])).
% 0.80/1.00  
% 0.80/1.00  % SZS output end Refutation
% 0.80/1.00  
% 0.80/1.01  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
