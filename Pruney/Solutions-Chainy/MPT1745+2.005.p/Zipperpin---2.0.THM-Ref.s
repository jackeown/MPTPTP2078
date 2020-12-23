%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FCOWP6cThq

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:36 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 192 expanded)
%              Number of leaves         :   29 (  71 expanded)
%              Depth                    :   17
%              Number of atoms          : 1362 (7868 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   30 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(k1_connsp_2_type,type,(
    k1_connsp_2: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t54_tmap_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( v2_pre_topc @ C )
                & ( l1_pre_topc @ C ) )
             => ! [D: $i] :
                  ( ( ( v1_funct_1 @ D )
                    & ( v1_funct_2 @ D @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) ) ) ) )
                 => ! [E: $i] :
                      ( ( ( v1_funct_1 @ E )
                        & ( v1_funct_2 @ E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
                     => ! [F: $i] :
                          ( ( m1_subset_1 @ F @ ( u1_struct_0 @ C ) )
                         => ( ( ( r1_tmap_1 @ C @ A @ D @ F )
                              & ( v5_pre_topc @ E @ A @ B ) )
                           => ( r1_tmap_1 @ C @ B @ ( k1_partfun1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ D @ E ) @ F ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( v2_pre_topc @ B )
              & ( l1_pre_topc @ B ) )
           => ! [C: $i] :
                ( ( ~ ( v2_struct_0 @ C )
                  & ( v2_pre_topc @ C )
                  & ( l1_pre_topc @ C ) )
               => ! [D: $i] :
                    ( ( ( v1_funct_1 @ D )
                      & ( v1_funct_2 @ D @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) )
                      & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) ) ) ) )
                   => ! [E: $i] :
                        ( ( ( v1_funct_1 @ E )
                          & ( v1_funct_2 @ E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                          & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
                       => ! [F: $i] :
                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ C ) )
                           => ( ( ( r1_tmap_1 @ C @ A @ D @ F )
                                & ( v5_pre_topc @ E @ A @ B ) )
                             => ( r1_tmap_1 @ C @ B @ ( k1_partfun1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ D @ E ) @ F ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t54_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t30_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( r2_hidden @ B @ ( k1_connsp_2 @ A @ B ) ) ) ) )).

thf('2',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ( r2_hidden @ X9 @ ( k1_connsp_2 @ X10 @ X9 ) )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t30_connsp_2])).

thf('3',plain,
    ( ( v2_struct_0 @ sk_C )
    | ~ ( v2_pre_topc @ sk_C )
    | ~ ( l1_pre_topc @ sk_C )
    | ( r2_hidden @ sk_F @ ( k1_connsp_2 @ sk_C @ sk_F ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v2_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    l1_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( r2_hidden @ sk_F @ ( k1_connsp_2 @ sk_C @ sk_F ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    r2_hidden @ sk_F @ ( k1_connsp_2 @ sk_C @ sk_F ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ A ) )
     => ( m1_subset_1 @ ( k3_funct_2 @ A @ B @ C @ D ) @ B ) ) )).

thf('11',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) )
      | ~ ( v1_funct_2 @ X3 @ X4 @ X5 )
      | ~ ( v1_funct_1 @ X3 )
      | ( v1_xboole_0 @ X4 )
      | ~ ( m1_subset_1 @ X6 @ X4 )
      | ( m1_subset_1 @ ( k3_funct_2 @ X4 @ X5 @ X3 @ X6 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_funct_2])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D_1 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
      | ~ ( v1_funct_1 @ sk_D_1 )
      | ~ ( v1_funct_2 @ sk_D_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_funct_2 @ sk_D_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D_1 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( m1_subset_1 @ ( k3_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D_1 @ sk_F ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','15'])).

thf('17',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( m1_subset_1 @ ( k3_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D_1 @ sk_F ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','15'])).

thf('18',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t49_tmap_1,axiom,(
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
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )
             => ( ( v5_pre_topc @ C @ B @ A )
              <=> ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) )
                   => ( r1_tmap_1 @ B @ A @ C @ D ) ) ) ) ) ) )).

thf('19',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( v2_struct_0 @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v5_pre_topc @ X12 @ X11 @ X13 )
      | ( r1_tmap_1 @ X11 @ X13 @ X12 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X11 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X13 ) ) ) )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X13 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t49_tmap_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 )
      | ~ ( v5_pre_topc @ sk_E @ sk_A @ sk_B )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v5_pre_topc @ sk_E @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21','22','23','24','25','26','27'])).

thf('29',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_A @ sk_B @ sk_E @ ( k3_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D_1 @ sk_F ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['17','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t52_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( v2_pre_topc @ C )
                & ( l1_pre_topc @ C ) )
             => ! [D: $i] :
                  ( ( ( v1_funct_1 @ D )
                    & ( v1_funct_2 @ D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) ) ) )
                 => ! [E: $i] :
                      ( ( ( v1_funct_1 @ E )
                        & ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) ) ) ) )
                     => ! [F: $i] :
                          ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) )
                         => ! [G: $i] :
                              ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) )
                             => ( ( ( G
                                    = ( k3_funct_2 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) @ D @ F ) )
                                  & ( r1_tmap_1 @ B @ C @ D @ F )
                                  & ( r1_tmap_1 @ C @ A @ E @ G ) )
                               => ( r1_tmap_1 @ B @ A @ ( k1_partfun1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ D @ E ) @ F ) ) ) ) ) ) ) ) ) )).

thf('31',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( v2_struct_0 @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X17 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X17 ) ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X15 ) )
      | ~ ( r1_tmap_1 @ X15 @ X17 @ X16 @ X18 )
      | ( r1_tmap_1 @ X15 @ X19 @ ( k1_partfun1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X19 ) @ X16 @ X20 ) @ X18 )
      | ( X21
       != ( k3_funct_2 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X17 ) @ X16 @ X18 ) )
      | ~ ( r1_tmap_1 @ X17 @ X19 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X17 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X19 ) ) ) )
      | ~ ( v1_funct_2 @ X20 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X19 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t52_tmap_1])).

thf('32',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( v2_struct_0 @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ~ ( l1_pre_topc @ X19 )
      | ( v2_struct_0 @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_funct_2 @ X20 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X19 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X19 ) ) ) )
      | ~ ( m1_subset_1 @ ( k3_funct_2 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X17 ) @ X16 @ X18 ) @ ( u1_struct_0 @ X17 ) )
      | ~ ( r1_tmap_1 @ X17 @ X19 @ X20 @ ( k3_funct_2 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X17 ) @ X16 @ X18 ) )
      | ( r1_tmap_1 @ X15 @ X19 @ ( k1_partfun1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X19 ) @ X16 @ X20 ) @ X18 )
      | ~ ( r1_tmap_1 @ X15 @ X17 @ X16 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X15 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X17 ) ) ) )
      | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X17 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_tmap_1 @ X0 @ sk_A @ X1 @ X2 )
      | ( r1_tmap_1 @ X0 @ sk_B @ ( k1_partfun1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ X1 @ sk_E ) @ X2 )
      | ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_E @ ( k3_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ ( k3_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ X1 @ X2 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_tmap_1 @ X0 @ sk_A @ X1 @ X2 )
      | ( r1_tmap_1 @ X0 @ sk_B @ ( k1_partfun1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ X1 @ sk_E ) @ X2 )
      | ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_E @ ( k3_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ ( k3_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ X1 @ X2 ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['33','34','35','36','37','38','39'])).

thf('41',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( k3_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D_1 @ sk_F ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_tmap_1 @ sk_C @ sk_B @ ( k1_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_D_1 @ sk_E ) @ sk_F )
    | ~ ( r1_tmap_1 @ sk_C @ sk_A @ sk_D_1 @ sk_F )
    | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) )
    | ~ ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( v1_funct_2 @ sk_D_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ~ ( l1_pre_topc @ sk_C )
    | ~ ( v2_pre_topc @ sk_C )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['29','40'])).

thf('42',plain,(
    r1_tmap_1 @ sk_C @ sk_A @ sk_D_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_funct_2 @ sk_D_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    l1_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v2_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( k3_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D_1 @ sk_F ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_tmap_1 @ sk_C @ sk_B @ ( k1_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_D_1 @ sk_E ) @ sk_F )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['41','42','43','44','45','46','47','48'])).

thf('50',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_C @ sk_B @ ( k1_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_D_1 @ sk_E ) @ sk_F )
    | ~ ( m1_subset_1 @ ( k3_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D_1 @ sk_F ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( r1_tmap_1 @ sk_C @ sk_B @ ( k1_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_D_1 @ sk_E ) @ sk_F )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['16','50'])).

thf('52',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_C @ sk_B @ ( k1_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_D_1 @ sk_E ) @ sk_F )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k1_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_D_1 @ sk_E ) @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_connsp_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( m1_subset_1 @ ( k1_connsp_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('56',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 )
      | ( v2_struct_0 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X7 ) )
      | ( m1_subset_1 @ ( k1_connsp_2 @ X7 @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_connsp_2])).

thf('57',plain,
    ( ( m1_subset_1 @ ( k1_connsp_2 @ sk_C @ sk_F ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C )
    | ~ ( v2_pre_topc @ sk_C )
    | ~ ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    v2_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    l1_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( m1_subset_1 @ ( k1_connsp_2 @ sk_C @ sk_F ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    m1_subset_1 @ ( k1_connsp_2 @ sk_C @ sk_F ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['60','61'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
      | ~ ( r2_hidden @ X0 @ ( k1_connsp_2 @ sk_C @ sk_F ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k1_connsp_2 @ sk_C @ sk_F ) ) ) ),
    inference('sup-',[status(thm)],['54','64'])).

thf('66',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['8','65'])).

thf('67',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['66','67'])).

thf('69',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['68','69'])).

thf('71',plain,(
    $false ),
    inference(demod,[status(thm)],['0','70'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FCOWP6cThq
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:32:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.52  % Solved by: fo/fo7.sh
% 0.21/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.52  % done 65 iterations in 0.056s
% 0.21/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.52  % SZS output start Refutation
% 0.21/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.52  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.21/0.52  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.52  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.52  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.21/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.52  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.21/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.52  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.52  thf(sk_F_type, type, sk_F: $i).
% 0.21/0.52  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.52  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 0.21/0.52  thf(k1_connsp_2_type, type, k1_connsp_2: $i > $i > $i).
% 0.21/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.52  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.21/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.52  thf(sk_E_type, type, sk_E: $i).
% 0.21/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.52  thf(t54_tmap_1, conjecture,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.52             ( l1_pre_topc @ B ) ) =>
% 0.21/0.52           ( ![C:$i]:
% 0.21/0.52             ( ( ( ~( v2_struct_0 @ C ) ) & ( v2_pre_topc @ C ) & 
% 0.21/0.52                 ( l1_pre_topc @ C ) ) =>
% 0.21/0.52               ( ![D:$i]:
% 0.21/0.52                 ( ( ( v1_funct_1 @ D ) & 
% 0.21/0.52                     ( v1_funct_2 @
% 0.21/0.52                       D @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.52                     ( m1_subset_1 @
% 0.21/0.52                       D @ 
% 0.21/0.52                       ( k1_zfmisc_1 @
% 0.21/0.52                         ( k2_zfmisc_1 @
% 0.21/0.52                           ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.21/0.52                   ( ![E:$i]:
% 0.21/0.52                     ( ( ( v1_funct_1 @ E ) & 
% 0.21/0.52                         ( v1_funct_2 @
% 0.21/0.52                           E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.52                         ( m1_subset_1 @
% 0.21/0.52                           E @ 
% 0.21/0.52                           ( k1_zfmisc_1 @
% 0.21/0.52                             ( k2_zfmisc_1 @
% 0.21/0.52                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.52                       ( ![F:$i]:
% 0.21/0.52                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ C ) ) =>
% 0.21/0.52                           ( ( ( r1_tmap_1 @ C @ A @ D @ F ) & 
% 0.21/0.52                               ( v5_pre_topc @ E @ A @ B ) ) =>
% 0.21/0.52                             ( r1_tmap_1 @
% 0.21/0.52                               C @ B @ 
% 0.21/0.52                               ( k1_partfun1 @
% 0.21/0.52                                 ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ 
% 0.21/0.52                                 ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.21/0.52                                 D @ E ) @ 
% 0.21/0.52                               F ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.52    (~( ![A:$i]:
% 0.21/0.52        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.52            ( l1_pre_topc @ A ) ) =>
% 0.21/0.52          ( ![B:$i]:
% 0.21/0.52            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.52                ( l1_pre_topc @ B ) ) =>
% 0.21/0.52              ( ![C:$i]:
% 0.21/0.52                ( ( ( ~( v2_struct_0 @ C ) ) & ( v2_pre_topc @ C ) & 
% 0.21/0.52                    ( l1_pre_topc @ C ) ) =>
% 0.21/0.52                  ( ![D:$i]:
% 0.21/0.52                    ( ( ( v1_funct_1 @ D ) & 
% 0.21/0.52                        ( v1_funct_2 @
% 0.21/0.52                          D @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.52                        ( m1_subset_1 @
% 0.21/0.52                          D @ 
% 0.21/0.52                          ( k1_zfmisc_1 @
% 0.21/0.52                            ( k2_zfmisc_1 @
% 0.21/0.52                              ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.21/0.52                      ( ![E:$i]:
% 0.21/0.52                        ( ( ( v1_funct_1 @ E ) & 
% 0.21/0.52                            ( v1_funct_2 @
% 0.21/0.52                              E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.52                            ( m1_subset_1 @
% 0.21/0.52                              E @ 
% 0.21/0.52                              ( k1_zfmisc_1 @
% 0.21/0.52                                ( k2_zfmisc_1 @
% 0.21/0.52                                  ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.52                          ( ![F:$i]:
% 0.21/0.52                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ C ) ) =>
% 0.21/0.52                              ( ( ( r1_tmap_1 @ C @ A @ D @ F ) & 
% 0.21/0.52                                  ( v5_pre_topc @ E @ A @ B ) ) =>
% 0.21/0.52                                ( r1_tmap_1 @
% 0.21/0.52                                  C @ B @ 
% 0.21/0.52                                  ( k1_partfun1 @
% 0.21/0.52                                    ( u1_struct_0 @ C ) @ 
% 0.21/0.52                                    ( u1_struct_0 @ A ) @ 
% 0.21/0.52                                    ( u1_struct_0 @ A ) @ 
% 0.21/0.52                                    ( u1_struct_0 @ B ) @ D @ E ) @ 
% 0.21/0.52                                  F ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.52    inference('cnf.neg', [status(esa)], [t54_tmap_1])).
% 0.21/0.52  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('1', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(t30_connsp_2, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.52           ( r2_hidden @ B @ ( k1_connsp_2 @ A @ B ) ) ) ) ))).
% 0.21/0.52  thf('2', plain,
% 0.21/0.52      (![X9 : $i, X10 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10))
% 0.21/0.52          | (r2_hidden @ X9 @ (k1_connsp_2 @ X10 @ X9))
% 0.21/0.52          | ~ (l1_pre_topc @ X10)
% 0.21/0.52          | ~ (v2_pre_topc @ X10)
% 0.21/0.52          | (v2_struct_0 @ X10))),
% 0.21/0.52      inference('cnf', [status(esa)], [t30_connsp_2])).
% 0.21/0.52  thf('3', plain,
% 0.21/0.52      (((v2_struct_0 @ sk_C)
% 0.21/0.52        | ~ (v2_pre_topc @ sk_C)
% 0.21/0.52        | ~ (l1_pre_topc @ sk_C)
% 0.21/0.52        | (r2_hidden @ sk_F @ (k1_connsp_2 @ sk_C @ sk_F)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.52  thf('4', plain, ((v2_pre_topc @ sk_C)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('5', plain, ((l1_pre_topc @ sk_C)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('6', plain,
% 0.21/0.52      (((v2_struct_0 @ sk_C) | (r2_hidden @ sk_F @ (k1_connsp_2 @ sk_C @ sk_F)))),
% 0.21/0.52      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.21/0.52  thf('7', plain, (~ (v2_struct_0 @ sk_C)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('8', plain, ((r2_hidden @ sk_F @ (k1_connsp_2 @ sk_C @ sk_F))),
% 0.21/0.52      inference('clc', [status(thm)], ['6', '7'])).
% 0.21/0.52  thf('9', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('10', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_D_1 @ 
% 0.21/0.52        (k1_zfmisc_1 @ 
% 0.21/0.52         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(dt_k3_funct_2, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.52     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 0.21/0.52         ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.52         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.21/0.52         ( m1_subset_1 @ D @ A ) ) =>
% 0.21/0.52       ( m1_subset_1 @ ( k3_funct_2 @ A @ B @ C @ D ) @ B ) ))).
% 0.21/0.52  thf('11', plain,
% 0.21/0.52      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5)))
% 0.21/0.52          | ~ (v1_funct_2 @ X3 @ X4 @ X5)
% 0.21/0.52          | ~ (v1_funct_1 @ X3)
% 0.21/0.52          | (v1_xboole_0 @ X4)
% 0.21/0.52          | ~ (m1_subset_1 @ X6 @ X4)
% 0.21/0.52          | (m1_subset_1 @ (k3_funct_2 @ X4 @ X5 @ X3 @ X6) @ X5))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_k3_funct_2])).
% 0.21/0.52  thf('12', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((m1_subset_1 @ 
% 0.21/0.52           (k3_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.52            sk_D_1 @ X0) @ 
% 0.21/0.52           (u1_struct_0 @ sk_A))
% 0.21/0.52          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C))
% 0.21/0.52          | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.21/0.52          | ~ (v1_funct_1 @ sk_D_1)
% 0.21/0.52          | ~ (v1_funct_2 @ sk_D_1 @ (u1_struct_0 @ sk_C) @ 
% 0.21/0.52               (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.52  thf('13', plain, ((v1_funct_1 @ sk_D_1)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('14', plain,
% 0.21/0.52      ((v1_funct_2 @ sk_D_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('15', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((m1_subset_1 @ 
% 0.21/0.52           (k3_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.52            sk_D_1 @ X0) @ 
% 0.21/0.52           (u1_struct_0 @ sk_A))
% 0.21/0.52          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C))
% 0.21/0.52          | (v1_xboole_0 @ (u1_struct_0 @ sk_C)))),
% 0.21/0.52      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.21/0.52  thf('16', plain,
% 0.21/0.52      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.21/0.52        | (m1_subset_1 @ 
% 0.21/0.52           (k3_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.52            sk_D_1 @ sk_F) @ 
% 0.21/0.52           (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['9', '15'])).
% 0.21/0.52  thf('17', plain,
% 0.21/0.52      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.21/0.52        | (m1_subset_1 @ 
% 0.21/0.52           (k3_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.52            sk_D_1 @ sk_F) @ 
% 0.21/0.52           (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['9', '15'])).
% 0.21/0.52  thf('18', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_E @ 
% 0.21/0.52        (k1_zfmisc_1 @ 
% 0.21/0.52         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(t49_tmap_1, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.52             ( l1_pre_topc @ B ) ) =>
% 0.21/0.52           ( ![C:$i]:
% 0.21/0.52             ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.52                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.52                 ( m1_subset_1 @
% 0.21/0.52                   C @ 
% 0.21/0.52                   ( k1_zfmisc_1 @
% 0.21/0.52                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.21/0.52               ( ( v5_pre_topc @ C @ B @ A ) <=>
% 0.21/0.52                 ( ![D:$i]:
% 0.21/0.52                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.21/0.52                     ( r1_tmap_1 @ B @ A @ C @ D ) ) ) ) ) ) ) ) ))).
% 0.21/0.52  thf('19', plain,
% 0.21/0.52      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.52         ((v2_struct_0 @ X11)
% 0.21/0.52          | ~ (v2_pre_topc @ X11)
% 0.21/0.52          | ~ (l1_pre_topc @ X11)
% 0.21/0.52          | ~ (v5_pre_topc @ X12 @ X11 @ X13)
% 0.21/0.52          | (r1_tmap_1 @ X11 @ X13 @ X12 @ X14)
% 0.21/0.52          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X11))
% 0.21/0.52          | ~ (m1_subset_1 @ X12 @ 
% 0.21/0.52               (k1_zfmisc_1 @ 
% 0.21/0.52                (k2_zfmisc_1 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X13))))
% 0.21/0.52          | ~ (v1_funct_2 @ X12 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X13))
% 0.21/0.52          | ~ (v1_funct_1 @ X12)
% 0.21/0.52          | ~ (l1_pre_topc @ X13)
% 0.21/0.52          | ~ (v2_pre_topc @ X13)
% 0.21/0.52          | (v2_struct_0 @ X13))),
% 0.21/0.52      inference('cnf', [status(esa)], [t49_tmap_1])).
% 0.21/0.52  thf('20', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((v2_struct_0 @ sk_B)
% 0.21/0.52          | ~ (v2_pre_topc @ sk_B)
% 0.21/0.52          | ~ (l1_pre_topc @ sk_B)
% 0.21/0.52          | ~ (v1_funct_1 @ sk_E)
% 0.21/0.52          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.21/0.52          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.52          | (r1_tmap_1 @ sk_A @ sk_B @ sk_E @ X0)
% 0.21/0.52          | ~ (v5_pre_topc @ sk_E @ sk_A @ sk_B)
% 0.21/0.52          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.52          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.52          | (v2_struct_0 @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.52  thf('21', plain, ((v2_pre_topc @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('22', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('23', plain, ((v1_funct_1 @ sk_E)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('24', plain,
% 0.21/0.52      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('25', plain, ((v5_pre_topc @ sk_E @ sk_A @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('27', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('28', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((v2_struct_0 @ sk_B)
% 0.21/0.52          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.52          | (r1_tmap_1 @ sk_A @ sk_B @ sk_E @ X0)
% 0.21/0.52          | (v2_struct_0 @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)],
% 0.21/0.52                ['20', '21', '22', '23', '24', '25', '26', '27'])).
% 0.21/0.52  thf('29', plain,
% 0.21/0.52      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.21/0.52        | (v2_struct_0 @ sk_A)
% 0.21/0.52        | (r1_tmap_1 @ sk_A @ sk_B @ sk_E @ 
% 0.21/0.52           (k3_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.52            sk_D_1 @ sk_F))
% 0.21/0.52        | (v2_struct_0 @ sk_B))),
% 0.21/0.52      inference('sup-', [status(thm)], ['17', '28'])).
% 0.21/0.52  thf('30', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_E @ 
% 0.21/0.52        (k1_zfmisc_1 @ 
% 0.21/0.52         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(t52_tmap_1, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.52             ( l1_pre_topc @ B ) ) =>
% 0.21/0.52           ( ![C:$i]:
% 0.21/0.52             ( ( ( ~( v2_struct_0 @ C ) ) & ( v2_pre_topc @ C ) & 
% 0.21/0.52                 ( l1_pre_topc @ C ) ) =>
% 0.21/0.52               ( ![D:$i]:
% 0.21/0.52                 ( ( ( v1_funct_1 @ D ) & 
% 0.21/0.52                     ( v1_funct_2 @
% 0.21/0.52                       D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) & 
% 0.21/0.52                     ( m1_subset_1 @
% 0.21/0.52                       D @ 
% 0.21/0.52                       ( k1_zfmisc_1 @
% 0.21/0.52                         ( k2_zfmisc_1 @
% 0.21/0.52                           ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) ) ) ) =>
% 0.21/0.52                   ( ![E:$i]:
% 0.21/0.52                     ( ( ( v1_funct_1 @ E ) & 
% 0.21/0.52                         ( v1_funct_2 @
% 0.21/0.52                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.52                         ( m1_subset_1 @
% 0.21/0.52                           E @ 
% 0.21/0.52                           ( k1_zfmisc_1 @
% 0.21/0.52                             ( k2_zfmisc_1 @
% 0.21/0.52                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.21/0.52                       ( ![F:$i]:
% 0.21/0.52                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 0.21/0.52                           ( ![G:$i]:
% 0.21/0.52                             ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.21/0.52                               ( ( ( ( G ) =
% 0.21/0.52                                     ( k3_funct_2 @
% 0.21/0.52                                       ( u1_struct_0 @ B ) @ 
% 0.21/0.52                                       ( u1_struct_0 @ C ) @ D @ F ) ) & 
% 0.21/0.52                                   ( r1_tmap_1 @ B @ C @ D @ F ) & 
% 0.21/0.52                                   ( r1_tmap_1 @ C @ A @ E @ G ) ) =>
% 0.21/0.52                                 ( r1_tmap_1 @
% 0.21/0.52                                   B @ A @ 
% 0.21/0.52                                   ( k1_partfun1 @
% 0.21/0.52                                     ( u1_struct_0 @ B ) @ 
% 0.21/0.52                                     ( u1_struct_0 @ C ) @ 
% 0.21/0.52                                     ( u1_struct_0 @ C ) @ 
% 0.21/0.52                                     ( u1_struct_0 @ A ) @ D @ E ) @ 
% 0.21/0.52                                   F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.52  thf('31', plain,
% 0.21/0.52      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.21/0.52         ((v2_struct_0 @ X15)
% 0.21/0.52          | ~ (v2_pre_topc @ X15)
% 0.21/0.52          | ~ (l1_pre_topc @ X15)
% 0.21/0.52          | ~ (v1_funct_1 @ X16)
% 0.21/0.52          | ~ (v1_funct_2 @ X16 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X17))
% 0.21/0.52          | ~ (m1_subset_1 @ X16 @ 
% 0.21/0.52               (k1_zfmisc_1 @ 
% 0.21/0.52                (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X17))))
% 0.21/0.52          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X15))
% 0.21/0.52          | ~ (r1_tmap_1 @ X15 @ X17 @ X16 @ X18)
% 0.21/0.52          | (r1_tmap_1 @ X15 @ X19 @ 
% 0.21/0.52             (k1_partfun1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X17) @ 
% 0.21/0.52              (u1_struct_0 @ X17) @ (u1_struct_0 @ X19) @ X16 @ X20) @ 
% 0.21/0.52             X18)
% 0.21/0.52          | ((X21)
% 0.21/0.52              != (k3_funct_2 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X17) @ 
% 0.21/0.52                  X16 @ X18))
% 0.21/0.52          | ~ (r1_tmap_1 @ X17 @ X19 @ X20 @ X21)
% 0.21/0.52          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X17))
% 0.21/0.52          | ~ (m1_subset_1 @ X20 @ 
% 0.21/0.52               (k1_zfmisc_1 @ 
% 0.21/0.52                (k2_zfmisc_1 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X19))))
% 0.21/0.52          | ~ (v1_funct_2 @ X20 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X19))
% 0.21/0.52          | ~ (v1_funct_1 @ X20)
% 0.21/0.52          | ~ (l1_pre_topc @ X17)
% 0.21/0.52          | ~ (v2_pre_topc @ X17)
% 0.21/0.52          | (v2_struct_0 @ X17)
% 0.21/0.52          | ~ (l1_pre_topc @ X19)
% 0.21/0.52          | ~ (v2_pre_topc @ X19)
% 0.21/0.52          | (v2_struct_0 @ X19))),
% 0.21/0.52      inference('cnf', [status(esa)], [t52_tmap_1])).
% 0.21/0.52  thf('32', plain,
% 0.21/0.52      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.21/0.52         ((v2_struct_0 @ X19)
% 0.21/0.52          | ~ (v2_pre_topc @ X19)
% 0.21/0.52          | ~ (l1_pre_topc @ X19)
% 0.21/0.52          | (v2_struct_0 @ X17)
% 0.21/0.52          | ~ (v2_pre_topc @ X17)
% 0.21/0.52          | ~ (l1_pre_topc @ X17)
% 0.21/0.52          | ~ (v1_funct_1 @ X20)
% 0.21/0.52          | ~ (v1_funct_2 @ X20 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X19))
% 0.21/0.52          | ~ (m1_subset_1 @ X20 @ 
% 0.21/0.52               (k1_zfmisc_1 @ 
% 0.21/0.52                (k2_zfmisc_1 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X19))))
% 0.21/0.52          | ~ (m1_subset_1 @ 
% 0.21/0.52               (k3_funct_2 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X17) @ X16 @ 
% 0.21/0.52                X18) @ 
% 0.21/0.52               (u1_struct_0 @ X17))
% 0.21/0.52          | ~ (r1_tmap_1 @ X17 @ X19 @ X20 @ 
% 0.21/0.52               (k3_funct_2 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X17) @ X16 @ 
% 0.21/0.52                X18))
% 0.21/0.52          | (r1_tmap_1 @ X15 @ X19 @ 
% 0.21/0.52             (k1_partfun1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X17) @ 
% 0.21/0.52              (u1_struct_0 @ X17) @ (u1_struct_0 @ X19) @ X16 @ X20) @ 
% 0.21/0.52             X18)
% 0.21/0.52          | ~ (r1_tmap_1 @ X15 @ X17 @ X16 @ X18)
% 0.21/0.52          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X15))
% 0.21/0.52          | ~ (m1_subset_1 @ X16 @ 
% 0.21/0.52               (k1_zfmisc_1 @ 
% 0.21/0.52                (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X17))))
% 0.21/0.52          | ~ (v1_funct_2 @ X16 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X17))
% 0.21/0.52          | ~ (v1_funct_1 @ X16)
% 0.21/0.52          | ~ (l1_pre_topc @ X15)
% 0.21/0.52          | ~ (v2_pre_topc @ X15)
% 0.21/0.52          | (v2_struct_0 @ X15))),
% 0.21/0.52      inference('simplify', [status(thm)], ['31'])).
% 0.21/0.52  thf('33', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         ((v2_struct_0 @ X0)
% 0.21/0.52          | ~ (v2_pre_topc @ X0)
% 0.21/0.52          | ~ (l1_pre_topc @ X0)
% 0.21/0.52          | ~ (v1_funct_1 @ X1)
% 0.21/0.52          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 0.21/0.52          | ~ (m1_subset_1 @ X1 @ 
% 0.21/0.52               (k1_zfmisc_1 @ 
% 0.21/0.52                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 0.21/0.52          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.21/0.52          | ~ (r1_tmap_1 @ X0 @ sk_A @ X1 @ X2)
% 0.21/0.52          | (r1_tmap_1 @ X0 @ sk_B @ 
% 0.21/0.52             (k1_partfun1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.52              (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ X1 @ sk_E) @ 
% 0.21/0.52             X2)
% 0.21/0.52          | ~ (r1_tmap_1 @ sk_A @ sk_B @ sk_E @ 
% 0.21/0.52               (k3_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ X1 @ 
% 0.21/0.52                X2))
% 0.21/0.52          | ~ (m1_subset_1 @ 
% 0.21/0.52               (k3_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ X1 @ 
% 0.21/0.52                X2) @ 
% 0.21/0.52               (u1_struct_0 @ sk_A))
% 0.21/0.52          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.21/0.52          | ~ (v1_funct_1 @ sk_E)
% 0.21/0.52          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.52          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.52          | (v2_struct_0 @ sk_A)
% 0.21/0.52          | ~ (l1_pre_topc @ sk_B)
% 0.21/0.52          | ~ (v2_pre_topc @ sk_B)
% 0.21/0.52          | (v2_struct_0 @ sk_B))),
% 0.21/0.52      inference('sup-', [status(thm)], ['30', '32'])).
% 0.21/0.52  thf('34', plain,
% 0.21/0.52      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('35', plain, ((v1_funct_1 @ sk_E)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('37', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('38', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('39', plain, ((v2_pre_topc @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('40', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         ((v2_struct_0 @ X0)
% 0.21/0.52          | ~ (v2_pre_topc @ X0)
% 0.21/0.52          | ~ (l1_pre_topc @ X0)
% 0.21/0.52          | ~ (v1_funct_1 @ X1)
% 0.21/0.52          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 0.21/0.52          | ~ (m1_subset_1 @ X1 @ 
% 0.21/0.52               (k1_zfmisc_1 @ 
% 0.21/0.52                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 0.21/0.52          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.21/0.52          | ~ (r1_tmap_1 @ X0 @ sk_A @ X1 @ X2)
% 0.21/0.52          | (r1_tmap_1 @ X0 @ sk_B @ 
% 0.21/0.52             (k1_partfun1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.52              (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ X1 @ sk_E) @ 
% 0.21/0.52             X2)
% 0.21/0.52          | ~ (r1_tmap_1 @ sk_A @ sk_B @ sk_E @ 
% 0.21/0.52               (k3_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ X1 @ 
% 0.21/0.52                X2))
% 0.21/0.52          | ~ (m1_subset_1 @ 
% 0.21/0.52               (k3_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ X1 @ 
% 0.21/0.52                X2) @ 
% 0.21/0.52               (u1_struct_0 @ sk_A))
% 0.21/0.52          | (v2_struct_0 @ sk_A)
% 0.21/0.52          | (v2_struct_0 @ sk_B))),
% 0.21/0.52      inference('demod', [status(thm)],
% 0.21/0.52                ['33', '34', '35', '36', '37', '38', '39'])).
% 0.21/0.52  thf('41', plain,
% 0.21/0.52      (((v2_struct_0 @ sk_B)
% 0.21/0.52        | (v2_struct_0 @ sk_A)
% 0.21/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.21/0.52        | (v2_struct_0 @ sk_B)
% 0.21/0.52        | (v2_struct_0 @ sk_A)
% 0.21/0.52        | ~ (m1_subset_1 @ 
% 0.21/0.52             (k3_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.52              sk_D_1 @ sk_F) @ 
% 0.21/0.52             (u1_struct_0 @ sk_A))
% 0.21/0.52        | (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.21/0.52           (k1_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.52            (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_D_1 @ sk_E) @ 
% 0.21/0.52           sk_F)
% 0.21/0.52        | ~ (r1_tmap_1 @ sk_C @ sk_A @ sk_D_1 @ sk_F)
% 0.21/0.52        | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))
% 0.21/0.52        | ~ (m1_subset_1 @ sk_D_1 @ 
% 0.21/0.52             (k1_zfmisc_1 @ 
% 0.21/0.52              (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))
% 0.21/0.52        | ~ (v1_funct_2 @ sk_D_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))
% 0.21/0.52        | ~ (v1_funct_1 @ sk_D_1)
% 0.21/0.52        | ~ (l1_pre_topc @ sk_C)
% 0.21/0.52        | ~ (v2_pre_topc @ sk_C)
% 0.21/0.52        | (v2_struct_0 @ sk_C))),
% 0.21/0.52      inference('sup-', [status(thm)], ['29', '40'])).
% 0.21/0.52  thf('42', plain, ((r1_tmap_1 @ sk_C @ sk_A @ sk_D_1 @ sk_F)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('43', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('44', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_D_1 @ 
% 0.21/0.52        (k1_zfmisc_1 @ 
% 0.21/0.52         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('45', plain,
% 0.21/0.52      ((v1_funct_2 @ sk_D_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('46', plain, ((v1_funct_1 @ sk_D_1)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('47', plain, ((l1_pre_topc @ sk_C)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('48', plain, ((v2_pre_topc @ sk_C)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('49', plain,
% 0.21/0.52      (((v2_struct_0 @ sk_B)
% 0.21/0.52        | (v2_struct_0 @ sk_A)
% 0.21/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.21/0.52        | (v2_struct_0 @ sk_B)
% 0.21/0.52        | (v2_struct_0 @ sk_A)
% 0.21/0.52        | ~ (m1_subset_1 @ 
% 0.21/0.52             (k3_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.52              sk_D_1 @ sk_F) @ 
% 0.21/0.52             (u1_struct_0 @ sk_A))
% 0.21/0.52        | (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.21/0.52           (k1_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.52            (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_D_1 @ sk_E) @ 
% 0.21/0.52           sk_F)
% 0.21/0.52        | (v2_struct_0 @ sk_C))),
% 0.21/0.52      inference('demod', [status(thm)],
% 0.21/0.52                ['41', '42', '43', '44', '45', '46', '47', '48'])).
% 0.21/0.52  thf('50', plain,
% 0.21/0.52      (((v2_struct_0 @ sk_C)
% 0.21/0.52        | (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.21/0.52           (k1_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.52            (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_D_1 @ sk_E) @ 
% 0.21/0.52           sk_F)
% 0.21/0.52        | ~ (m1_subset_1 @ 
% 0.21/0.52             (k3_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.52              sk_D_1 @ sk_F) @ 
% 0.21/0.52             (u1_struct_0 @ sk_A))
% 0.21/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.21/0.52        | (v2_struct_0 @ sk_A)
% 0.21/0.52        | (v2_struct_0 @ sk_B))),
% 0.21/0.52      inference('simplify', [status(thm)], ['49'])).
% 0.21/0.52  thf('51', plain,
% 0.21/0.52      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.21/0.52        | (v2_struct_0 @ sk_B)
% 0.21/0.52        | (v2_struct_0 @ sk_A)
% 0.21/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.21/0.52        | (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.21/0.52           (k1_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.52            (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_D_1 @ sk_E) @ 
% 0.21/0.52           sk_F)
% 0.21/0.52        | (v2_struct_0 @ sk_C))),
% 0.21/0.52      inference('sup-', [status(thm)], ['16', '50'])).
% 0.21/0.52  thf('52', plain,
% 0.21/0.52      (((v2_struct_0 @ sk_C)
% 0.21/0.52        | (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.21/0.52           (k1_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.52            (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_D_1 @ sk_E) @ 
% 0.21/0.52           sk_F)
% 0.21/0.52        | (v2_struct_0 @ sk_A)
% 0.21/0.52        | (v2_struct_0 @ sk_B)
% 0.21/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_C)))),
% 0.21/0.52      inference('simplify', [status(thm)], ['51'])).
% 0.21/0.52  thf('53', plain,
% 0.21/0.52      (~ (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.21/0.52          (k1_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.52           (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_D_1 @ sk_E) @ 
% 0.21/0.52          sk_F)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('54', plain,
% 0.21/0.52      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.21/0.52        | (v2_struct_0 @ sk_B)
% 0.21/0.52        | (v2_struct_0 @ sk_A)
% 0.21/0.52        | (v2_struct_0 @ sk_C))),
% 0.21/0.52      inference('sup-', [status(thm)], ['52', '53'])).
% 0.21/0.52  thf('55', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(dt_k1_connsp_2, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.52         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.52       ( m1_subset_1 @
% 0.21/0.52         ( k1_connsp_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.52  thf('56', plain,
% 0.21/0.52      (![X7 : $i, X8 : $i]:
% 0.21/0.52         (~ (l1_pre_topc @ X7)
% 0.21/0.52          | ~ (v2_pre_topc @ X7)
% 0.21/0.52          | (v2_struct_0 @ X7)
% 0.21/0.52          | ~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X7))
% 0.21/0.52          | (m1_subset_1 @ (k1_connsp_2 @ X7 @ X8) @ 
% 0.21/0.52             (k1_zfmisc_1 @ (u1_struct_0 @ X7))))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_k1_connsp_2])).
% 0.21/0.52  thf('57', plain,
% 0.21/0.52      (((m1_subset_1 @ (k1_connsp_2 @ sk_C @ sk_F) @ 
% 0.21/0.52         (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))
% 0.21/0.52        | (v2_struct_0 @ sk_C)
% 0.21/0.52        | ~ (v2_pre_topc @ sk_C)
% 0.21/0.52        | ~ (l1_pre_topc @ sk_C))),
% 0.21/0.52      inference('sup-', [status(thm)], ['55', '56'])).
% 0.21/0.52  thf('58', plain, ((v2_pre_topc @ sk_C)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('59', plain, ((l1_pre_topc @ sk_C)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('60', plain,
% 0.21/0.52      (((m1_subset_1 @ (k1_connsp_2 @ sk_C @ sk_F) @ 
% 0.21/0.52         (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))
% 0.21/0.52        | (v2_struct_0 @ sk_C))),
% 0.21/0.52      inference('demod', [status(thm)], ['57', '58', '59'])).
% 0.21/0.52  thf('61', plain, (~ (v2_struct_0 @ sk_C)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('62', plain,
% 0.21/0.52      ((m1_subset_1 @ (k1_connsp_2 @ sk_C @ sk_F) @ 
% 0.21/0.52        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))),
% 0.21/0.52      inference('clc', [status(thm)], ['60', '61'])).
% 0.21/0.52  thf(t5_subset, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.21/0.52          ( v1_xboole_0 @ C ) ) ))).
% 0.21/0.52  thf('63', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.52          | ~ (v1_xboole_0 @ X2)
% 0.21/0.52          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t5_subset])).
% 0.21/0.52  thf('64', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.21/0.52          | ~ (r2_hidden @ X0 @ (k1_connsp_2 @ sk_C @ sk_F)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['62', '63'])).
% 0.21/0.52  thf('65', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((v2_struct_0 @ sk_C)
% 0.21/0.52          | (v2_struct_0 @ sk_A)
% 0.21/0.52          | (v2_struct_0 @ sk_B)
% 0.21/0.52          | ~ (r2_hidden @ X0 @ (k1_connsp_2 @ sk_C @ sk_F)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['54', '64'])).
% 0.21/0.52  thf('66', plain,
% 0.21/0.52      (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C))),
% 0.21/0.52      inference('sup-', [status(thm)], ['8', '65'])).
% 0.21/0.52  thf('67', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('68', plain, (((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A))),
% 0.21/0.52      inference('clc', [status(thm)], ['66', '67'])).
% 0.21/0.52  thf('69', plain, (~ (v2_struct_0 @ sk_C)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('70', plain, ((v2_struct_0 @ sk_A)),
% 0.21/0.52      inference('clc', [status(thm)], ['68', '69'])).
% 0.21/0.52  thf('71', plain, ($false), inference('demod', [status(thm)], ['0', '70'])).
% 0.21/0.52  
% 0.21/0.52  % SZS output end Refutation
% 0.21/0.52  
% 0.36/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
