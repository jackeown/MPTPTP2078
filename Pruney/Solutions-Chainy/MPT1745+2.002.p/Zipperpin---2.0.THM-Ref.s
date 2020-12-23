%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PmZzYLs8pt

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:36 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 179 expanded)
%              Number of leaves         :   29 (  68 expanded)
%              Depth                    :   21
%              Number of atoms          : 1320 (7221 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   30 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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

thf('2',plain,(
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

thf('3',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) )
      | ~ ( v1_funct_2 @ X2 @ X3 @ X4 )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_xboole_0 @ X3 )
      | ~ ( m1_subset_1 @ X5 @ X3 )
      | ( m1_subset_1 @ ( k3_funct_2 @ X3 @ X4 @ X2 @ X5 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_funct_2])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D_1 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
      | ~ ( v1_funct_1 @ sk_D_1 )
      | ~ ( v1_funct_2 @ sk_D_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_funct_2 @ sk_D_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D_1 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( m1_subset_1 @ ( k3_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D_1 @ sk_F ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf('9',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( m1_subset_1 @ ( k3_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D_1 @ sk_F ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf('10',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
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

thf('11',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( v2_struct_0 @ X7 )
      | ~ ( v2_pre_topc @ X7 )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( v5_pre_topc @ X8 @ X7 @ X9 )
      | ( r1_tmap_1 @ X7 @ X9 @ X8 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X7 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( v1_funct_2 @ X8 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t49_tmap_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( v2_pre_topc @ sk_B_1 )
      | ~ ( l1_pre_topc @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ X0 )
      | ~ ( v5_pre_topc @ sk_E @ sk_A @ sk_B_1 )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v5_pre_topc @ sk_E @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13','14','15','16','17','18','19'])).

thf('21',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ ( k3_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D_1 @ sk_F ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['9','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
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

thf('23',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( v2_struct_0 @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X13 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X13 ) ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X11 ) )
      | ~ ( r1_tmap_1 @ X11 @ X13 @ X12 @ X14 )
      | ( r1_tmap_1 @ X11 @ X15 @ ( k1_partfun1 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X15 ) @ X12 @ X16 ) @ X14 )
      | ( X17
       != ( k3_funct_2 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X13 ) @ X12 @ X14 ) )
      | ~ ( r1_tmap_1 @ X13 @ X15 @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X13 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X15 ) ) ) )
      | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X15 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t52_tmap_1])).

thf('24',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( v2_struct_0 @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ~ ( l1_pre_topc @ X15 )
      | ( v2_struct_0 @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X15 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X15 ) ) ) )
      | ~ ( m1_subset_1 @ ( k3_funct_2 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X13 ) @ X12 @ X14 ) @ ( u1_struct_0 @ X13 ) )
      | ~ ( r1_tmap_1 @ X13 @ X15 @ X16 @ ( k3_funct_2 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X13 ) @ X12 @ X14 ) )
      | ( r1_tmap_1 @ X11 @ X15 @ ( k1_partfun1 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X15 ) @ X12 @ X16 ) @ X14 )
      | ~ ( r1_tmap_1 @ X11 @ X13 @ X12 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X11 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X13 ) ) ) )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X13 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_tmap_1 @ X0 @ sk_A @ X1 @ X2 )
      | ( r1_tmap_1 @ X0 @ sk_B_1 @ ( k1_partfun1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ X1 @ sk_E ) @ X2 )
      | ~ ( r1_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ ( k3_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ ( k3_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ X1 @ X2 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_B_1 )
      | ~ ( v2_pre_topc @ sk_B_1 )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf('26',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_tmap_1 @ X0 @ sk_A @ X1 @ X2 )
      | ( r1_tmap_1 @ X0 @ sk_B_1 @ ( k1_partfun1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ X1 @ sk_E ) @ X2 )
      | ~ ( r1_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ ( k3_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ ( k3_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ X1 @ X2 ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['25','26','27','28','29','30','31'])).

thf('33',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( k3_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D_1 @ sk_F ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_tmap_1 @ sk_C @ sk_B_1 @ ( k1_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_D_1 @ sk_E ) @ sk_F )
    | ~ ( r1_tmap_1 @ sk_C @ sk_A @ sk_D_1 @ sk_F )
    | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) )
    | ~ ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( v1_funct_2 @ sk_D_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ~ ( l1_pre_topc @ sk_C )
    | ~ ( v2_pre_topc @ sk_C )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['21','32'])).

thf('34',plain,(
    r1_tmap_1 @ sk_C @ sk_A @ sk_D_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v1_funct_2 @ sk_D_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    l1_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v2_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( k3_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D_1 @ sk_F ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_tmap_1 @ sk_C @ sk_B_1 @ ( k1_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_D_1 @ sk_E ) @ sk_F )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['33','34','35','36','37','38','39','40'])).

thf('42',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_C @ sk_B_1 @ ( k1_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_D_1 @ sk_E ) @ sk_F )
    | ~ ( m1_subset_1 @ ( k3_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D_1 @ sk_F ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( r1_tmap_1 @ sk_C @ sk_B_1 @ ( k1_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_D_1 @ sk_E ) @ sk_F )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['8','42'])).

thf('44',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_C @ sk_B_1 @ ( k1_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_D_1 @ sk_E ) @ sk_F )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ~ ( r1_tmap_1 @ sk_C @ sk_B_1 @ ( k1_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_D_1 @ sk_E ) @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf(rc3_tops_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ? [B: $i] :
          ( ( v4_pre_topc @ B @ A )
          & ( v3_pre_topc @ B @ A )
          & ~ ( v1_xboole_0 @ B )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('47',plain,(
    ! [X6: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X6 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( l1_pre_topc @ X6 )
      | ~ ( v2_pre_topc @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[rc3_tops_1])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( v1_xboole_0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( sk_B @ sk_C ) )
    | ~ ( l1_pre_topc @ sk_C )
    | ~ ( v2_pre_topc @ sk_C )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,(
    l1_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v2_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,
    ( ( v1_xboole_0 @ ( sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X6: $i] :
      ( ~ ( v1_xboole_0 @ ( sk_B @ X6 ) )
      | ~ ( l1_pre_topc @ X6 )
      | ~ ( v2_pre_topc @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[rc3_tops_1])).

thf('56',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_C )
    | ~ ( v2_pre_topc @ sk_C )
    | ~ ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v2_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    l1_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['60','61'])).

thf('63',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['62','63'])).

thf('65',plain,(
    $false ),
    inference(demod,[status(thm)],['0','64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PmZzYLs8pt
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:57:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.36/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.55  % Solved by: fo/fo7.sh
% 0.36/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.55  % done 51 iterations in 0.047s
% 0.36/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.55  % SZS output start Refutation
% 0.36/0.55  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.36/0.55  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.36/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.36/0.55  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.36/0.55  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.36/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.55  thf(sk_E_type, type, sk_E: $i).
% 0.36/0.55  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.36/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.36/0.55  thf(sk_B_type, type, sk_B: $i > $i).
% 0.36/0.55  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.36/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.55  thf(sk_F_type, type, sk_F: $i).
% 0.36/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.36/0.55  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.36/0.55  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.36/0.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.36/0.55  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.36/0.55  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 0.36/0.55  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.36/0.55  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.36/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.36/0.55  thf(t54_tmap_1, conjecture,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.55       ( ![B:$i]:
% 0.36/0.55         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.36/0.55             ( l1_pre_topc @ B ) ) =>
% 0.36/0.55           ( ![C:$i]:
% 0.36/0.55             ( ( ( ~( v2_struct_0 @ C ) ) & ( v2_pre_topc @ C ) & 
% 0.36/0.55                 ( l1_pre_topc @ C ) ) =>
% 0.36/0.55               ( ![D:$i]:
% 0.36/0.55                 ( ( ( v1_funct_1 @ D ) & 
% 0.36/0.55                     ( v1_funct_2 @
% 0.36/0.55                       D @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) ) & 
% 0.36/0.55                     ( m1_subset_1 @
% 0.36/0.55                       D @ 
% 0.36/0.55                       ( k1_zfmisc_1 @
% 0.36/0.55                         ( k2_zfmisc_1 @
% 0.36/0.55                           ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.36/0.55                   ( ![E:$i]:
% 0.36/0.55                     ( ( ( v1_funct_1 @ E ) & 
% 0.36/0.55                         ( v1_funct_2 @
% 0.36/0.55                           E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.36/0.55                         ( m1_subset_1 @
% 0.36/0.55                           E @ 
% 0.36/0.55                           ( k1_zfmisc_1 @
% 0.36/0.55                             ( k2_zfmisc_1 @
% 0.36/0.55                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.36/0.55                       ( ![F:$i]:
% 0.36/0.55                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ C ) ) =>
% 0.36/0.55                           ( ( ( r1_tmap_1 @ C @ A @ D @ F ) & 
% 0.36/0.55                               ( v5_pre_topc @ E @ A @ B ) ) =>
% 0.36/0.55                             ( r1_tmap_1 @
% 0.36/0.55                               C @ B @ 
% 0.36/0.55                               ( k1_partfun1 @
% 0.36/0.55                                 ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ 
% 0.36/0.55                                 ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.36/0.55                                 D @ E ) @ 
% 0.36/0.55                               F ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.36/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.55    (~( ![A:$i]:
% 0.36/0.55        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.36/0.55            ( l1_pre_topc @ A ) ) =>
% 0.36/0.55          ( ![B:$i]:
% 0.36/0.55            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.36/0.55                ( l1_pre_topc @ B ) ) =>
% 0.36/0.55              ( ![C:$i]:
% 0.36/0.55                ( ( ( ~( v2_struct_0 @ C ) ) & ( v2_pre_topc @ C ) & 
% 0.36/0.55                    ( l1_pre_topc @ C ) ) =>
% 0.36/0.55                  ( ![D:$i]:
% 0.36/0.55                    ( ( ( v1_funct_1 @ D ) & 
% 0.36/0.55                        ( v1_funct_2 @
% 0.36/0.55                          D @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) ) & 
% 0.36/0.55                        ( m1_subset_1 @
% 0.36/0.55                          D @ 
% 0.36/0.55                          ( k1_zfmisc_1 @
% 0.36/0.55                            ( k2_zfmisc_1 @
% 0.36/0.55                              ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.36/0.55                      ( ![E:$i]:
% 0.36/0.55                        ( ( ( v1_funct_1 @ E ) & 
% 0.36/0.55                            ( v1_funct_2 @
% 0.36/0.55                              E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.36/0.55                            ( m1_subset_1 @
% 0.36/0.55                              E @ 
% 0.36/0.55                              ( k1_zfmisc_1 @
% 0.36/0.55                                ( k2_zfmisc_1 @
% 0.36/0.55                                  ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.36/0.55                          ( ![F:$i]:
% 0.36/0.55                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ C ) ) =>
% 0.36/0.55                              ( ( ( r1_tmap_1 @ C @ A @ D @ F ) & 
% 0.36/0.55                                  ( v5_pre_topc @ E @ A @ B ) ) =>
% 0.36/0.55                                ( r1_tmap_1 @
% 0.36/0.55                                  C @ B @ 
% 0.36/0.55                                  ( k1_partfun1 @
% 0.36/0.55                                    ( u1_struct_0 @ C ) @ 
% 0.36/0.55                                    ( u1_struct_0 @ A ) @ 
% 0.36/0.55                                    ( u1_struct_0 @ A ) @ 
% 0.36/0.55                                    ( u1_struct_0 @ B ) @ D @ E ) @ 
% 0.36/0.55                                  F ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.36/0.55    inference('cnf.neg', [status(esa)], [t54_tmap_1])).
% 0.36/0.55  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('1', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('2', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_D_1 @ 
% 0.36/0.55        (k1_zfmisc_1 @ 
% 0.36/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(dt_k3_funct_2, axiom,
% 0.36/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.55     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 0.36/0.55         ( v1_funct_2 @ C @ A @ B ) & 
% 0.36/0.55         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.36/0.55         ( m1_subset_1 @ D @ A ) ) =>
% 0.36/0.55       ( m1_subset_1 @ ( k3_funct_2 @ A @ B @ C @ D ) @ B ) ))).
% 0.36/0.55  thf('3', plain,
% 0.36/0.55      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.36/0.55         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4)))
% 0.36/0.55          | ~ (v1_funct_2 @ X2 @ X3 @ X4)
% 0.36/0.55          | ~ (v1_funct_1 @ X2)
% 0.36/0.55          | (v1_xboole_0 @ X3)
% 0.36/0.55          | ~ (m1_subset_1 @ X5 @ X3)
% 0.36/0.55          | (m1_subset_1 @ (k3_funct_2 @ X3 @ X4 @ X2 @ X5) @ X4))),
% 0.36/0.55      inference('cnf', [status(esa)], [dt_k3_funct_2])).
% 0.36/0.55  thf('4', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         ((m1_subset_1 @ 
% 0.36/0.55           (k3_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.55            sk_D_1 @ X0) @ 
% 0.36/0.55           (u1_struct_0 @ sk_A))
% 0.36/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C))
% 0.36/0.55          | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.36/0.55          | ~ (v1_funct_1 @ sk_D_1)
% 0.36/0.55          | ~ (v1_funct_2 @ sk_D_1 @ (u1_struct_0 @ sk_C) @ 
% 0.36/0.55               (u1_struct_0 @ sk_A)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['2', '3'])).
% 0.36/0.55  thf('5', plain, ((v1_funct_1 @ sk_D_1)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('6', plain,
% 0.36/0.55      ((v1_funct_2 @ sk_D_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('7', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         ((m1_subset_1 @ 
% 0.36/0.55           (k3_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.55            sk_D_1 @ X0) @ 
% 0.36/0.55           (u1_struct_0 @ sk_A))
% 0.36/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C))
% 0.36/0.55          | (v1_xboole_0 @ (u1_struct_0 @ sk_C)))),
% 0.36/0.55      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.36/0.55  thf('8', plain,
% 0.36/0.55      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.36/0.55        | (m1_subset_1 @ 
% 0.36/0.55           (k3_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.55            sk_D_1 @ sk_F) @ 
% 0.36/0.55           (u1_struct_0 @ sk_A)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['1', '7'])).
% 0.36/0.55  thf('9', plain,
% 0.36/0.55      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.36/0.55        | (m1_subset_1 @ 
% 0.36/0.55           (k3_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.55            sk_D_1 @ sk_F) @ 
% 0.36/0.55           (u1_struct_0 @ sk_A)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['1', '7'])).
% 0.36/0.55  thf('10', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_E @ 
% 0.36/0.55        (k1_zfmisc_1 @ 
% 0.36/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(t49_tmap_1, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.55       ( ![B:$i]:
% 0.36/0.55         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.36/0.55             ( l1_pre_topc @ B ) ) =>
% 0.36/0.55           ( ![C:$i]:
% 0.36/0.55             ( ( ( v1_funct_1 @ C ) & 
% 0.36/0.55                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.36/0.55                 ( m1_subset_1 @
% 0.36/0.55                   C @ 
% 0.36/0.55                   ( k1_zfmisc_1 @
% 0.36/0.55                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.36/0.55               ( ( v5_pre_topc @ C @ B @ A ) <=>
% 0.36/0.55                 ( ![D:$i]:
% 0.36/0.55                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.36/0.55                     ( r1_tmap_1 @ B @ A @ C @ D ) ) ) ) ) ) ) ) ))).
% 0.36/0.55  thf('11', plain,
% 0.36/0.55      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.36/0.55         ((v2_struct_0 @ X7)
% 0.36/0.55          | ~ (v2_pre_topc @ X7)
% 0.36/0.55          | ~ (l1_pre_topc @ X7)
% 0.36/0.55          | ~ (v5_pre_topc @ X8 @ X7 @ X9)
% 0.36/0.55          | (r1_tmap_1 @ X7 @ X9 @ X8 @ X10)
% 0.36/0.55          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X7))
% 0.36/0.55          | ~ (m1_subset_1 @ X8 @ 
% 0.36/0.55               (k1_zfmisc_1 @ 
% 0.36/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X9))))
% 0.36/0.55          | ~ (v1_funct_2 @ X8 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X9))
% 0.36/0.55          | ~ (v1_funct_1 @ X8)
% 0.36/0.55          | ~ (l1_pre_topc @ X9)
% 0.36/0.55          | ~ (v2_pre_topc @ X9)
% 0.36/0.55          | (v2_struct_0 @ X9))),
% 0.36/0.55      inference('cnf', [status(esa)], [t49_tmap_1])).
% 0.36/0.55  thf('12', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         ((v2_struct_0 @ sk_B_1)
% 0.36/0.55          | ~ (v2_pre_topc @ sk_B_1)
% 0.36/0.55          | ~ (l1_pre_topc @ sk_B_1)
% 0.36/0.55          | ~ (v1_funct_1 @ sk_E)
% 0.36/0.55          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.55               (u1_struct_0 @ sk_B_1))
% 0.36/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.36/0.55          | (r1_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ X0)
% 0.36/0.55          | ~ (v5_pre_topc @ sk_E @ sk_A @ sk_B_1)
% 0.36/0.55          | ~ (l1_pre_topc @ sk_A)
% 0.36/0.55          | ~ (v2_pre_topc @ sk_A)
% 0.36/0.55          | (v2_struct_0 @ sk_A))),
% 0.36/0.55      inference('sup-', [status(thm)], ['10', '11'])).
% 0.36/0.55  thf('13', plain, ((v2_pre_topc @ sk_B_1)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('14', plain, ((l1_pre_topc @ sk_B_1)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('15', plain, ((v1_funct_1 @ sk_E)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('16', plain,
% 0.36/0.55      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('17', plain, ((v5_pre_topc @ sk_E @ sk_A @ sk_B_1)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('19', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('20', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         ((v2_struct_0 @ sk_B_1)
% 0.36/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.36/0.55          | (r1_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ X0)
% 0.36/0.55          | (v2_struct_0 @ sk_A))),
% 0.36/0.55      inference('demod', [status(thm)],
% 0.36/0.55                ['12', '13', '14', '15', '16', '17', '18', '19'])).
% 0.36/0.55  thf('21', plain,
% 0.36/0.55      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.36/0.55        | (v2_struct_0 @ sk_A)
% 0.36/0.55        | (r1_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ 
% 0.36/0.55           (k3_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.55            sk_D_1 @ sk_F))
% 0.36/0.55        | (v2_struct_0 @ sk_B_1))),
% 0.36/0.55      inference('sup-', [status(thm)], ['9', '20'])).
% 0.36/0.55  thf('22', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_E @ 
% 0.36/0.55        (k1_zfmisc_1 @ 
% 0.36/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(t52_tmap_1, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.55       ( ![B:$i]:
% 0.36/0.55         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.36/0.55             ( l1_pre_topc @ B ) ) =>
% 0.36/0.55           ( ![C:$i]:
% 0.36/0.55             ( ( ( ~( v2_struct_0 @ C ) ) & ( v2_pre_topc @ C ) & 
% 0.36/0.55                 ( l1_pre_topc @ C ) ) =>
% 0.36/0.55               ( ![D:$i]:
% 0.36/0.55                 ( ( ( v1_funct_1 @ D ) & 
% 0.36/0.55                     ( v1_funct_2 @
% 0.36/0.55                       D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) & 
% 0.36/0.55                     ( m1_subset_1 @
% 0.36/0.55                       D @ 
% 0.36/0.55                       ( k1_zfmisc_1 @
% 0.36/0.55                         ( k2_zfmisc_1 @
% 0.36/0.55                           ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) ) ) ) =>
% 0.36/0.55                   ( ![E:$i]:
% 0.36/0.55                     ( ( ( v1_funct_1 @ E ) & 
% 0.36/0.55                         ( v1_funct_2 @
% 0.36/0.55                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) ) & 
% 0.36/0.55                         ( m1_subset_1 @
% 0.36/0.55                           E @ 
% 0.36/0.55                           ( k1_zfmisc_1 @
% 0.36/0.55                             ( k2_zfmisc_1 @
% 0.36/0.55                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.36/0.55                       ( ![F:$i]:
% 0.36/0.55                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 0.36/0.55                           ( ![G:$i]:
% 0.36/0.55                             ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.36/0.55                               ( ( ( ( G ) =
% 0.36/0.55                                     ( k3_funct_2 @
% 0.36/0.55                                       ( u1_struct_0 @ B ) @ 
% 0.36/0.55                                       ( u1_struct_0 @ C ) @ D @ F ) ) & 
% 0.36/0.55                                   ( r1_tmap_1 @ B @ C @ D @ F ) & 
% 0.36/0.55                                   ( r1_tmap_1 @ C @ A @ E @ G ) ) =>
% 0.36/0.55                                 ( r1_tmap_1 @
% 0.36/0.55                                   B @ A @ 
% 0.36/0.55                                   ( k1_partfun1 @
% 0.36/0.55                                     ( u1_struct_0 @ B ) @ 
% 0.36/0.55                                     ( u1_struct_0 @ C ) @ 
% 0.36/0.55                                     ( u1_struct_0 @ C ) @ 
% 0.36/0.55                                     ( u1_struct_0 @ A ) @ D @ E ) @ 
% 0.36/0.55                                   F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.36/0.55  thf('23', plain,
% 0.36/0.55      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.36/0.55         ((v2_struct_0 @ X11)
% 0.36/0.55          | ~ (v2_pre_topc @ X11)
% 0.36/0.55          | ~ (l1_pre_topc @ X11)
% 0.36/0.55          | ~ (v1_funct_1 @ X12)
% 0.36/0.55          | ~ (v1_funct_2 @ X12 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X13))
% 0.36/0.55          | ~ (m1_subset_1 @ X12 @ 
% 0.36/0.55               (k1_zfmisc_1 @ 
% 0.36/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X13))))
% 0.36/0.55          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X11))
% 0.36/0.55          | ~ (r1_tmap_1 @ X11 @ X13 @ X12 @ X14)
% 0.36/0.55          | (r1_tmap_1 @ X11 @ X15 @ 
% 0.36/0.55             (k1_partfun1 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X13) @ 
% 0.36/0.55              (u1_struct_0 @ X13) @ (u1_struct_0 @ X15) @ X12 @ X16) @ 
% 0.36/0.55             X14)
% 0.36/0.55          | ((X17)
% 0.36/0.55              != (k3_funct_2 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X13) @ 
% 0.36/0.55                  X12 @ X14))
% 0.36/0.55          | ~ (r1_tmap_1 @ X13 @ X15 @ X16 @ X17)
% 0.36/0.55          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X13))
% 0.36/0.55          | ~ (m1_subset_1 @ X16 @ 
% 0.36/0.55               (k1_zfmisc_1 @ 
% 0.36/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X15))))
% 0.36/0.55          | ~ (v1_funct_2 @ X16 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X15))
% 0.36/0.55          | ~ (v1_funct_1 @ X16)
% 0.36/0.55          | ~ (l1_pre_topc @ X13)
% 0.36/0.55          | ~ (v2_pre_topc @ X13)
% 0.36/0.55          | (v2_struct_0 @ X13)
% 0.36/0.55          | ~ (l1_pre_topc @ X15)
% 0.36/0.55          | ~ (v2_pre_topc @ X15)
% 0.36/0.55          | (v2_struct_0 @ X15))),
% 0.36/0.55      inference('cnf', [status(esa)], [t52_tmap_1])).
% 0.36/0.55  thf('24', plain,
% 0.36/0.55      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.36/0.55         ((v2_struct_0 @ X15)
% 0.36/0.55          | ~ (v2_pre_topc @ X15)
% 0.36/0.55          | ~ (l1_pre_topc @ X15)
% 0.36/0.55          | (v2_struct_0 @ X13)
% 0.36/0.55          | ~ (v2_pre_topc @ X13)
% 0.36/0.55          | ~ (l1_pre_topc @ X13)
% 0.36/0.55          | ~ (v1_funct_1 @ X16)
% 0.36/0.55          | ~ (v1_funct_2 @ X16 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X15))
% 0.36/0.55          | ~ (m1_subset_1 @ X16 @ 
% 0.36/0.55               (k1_zfmisc_1 @ 
% 0.36/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X15))))
% 0.36/0.55          | ~ (m1_subset_1 @ 
% 0.36/0.55               (k3_funct_2 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X13) @ X12 @ 
% 0.36/0.55                X14) @ 
% 0.36/0.55               (u1_struct_0 @ X13))
% 0.36/0.55          | ~ (r1_tmap_1 @ X13 @ X15 @ X16 @ 
% 0.36/0.55               (k3_funct_2 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X13) @ X12 @ 
% 0.36/0.55                X14))
% 0.36/0.55          | (r1_tmap_1 @ X11 @ X15 @ 
% 0.36/0.55             (k1_partfun1 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X13) @ 
% 0.36/0.55              (u1_struct_0 @ X13) @ (u1_struct_0 @ X15) @ X12 @ X16) @ 
% 0.36/0.55             X14)
% 0.36/0.55          | ~ (r1_tmap_1 @ X11 @ X13 @ X12 @ X14)
% 0.36/0.55          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X11))
% 0.36/0.55          | ~ (m1_subset_1 @ X12 @ 
% 0.36/0.55               (k1_zfmisc_1 @ 
% 0.36/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X13))))
% 0.36/0.55          | ~ (v1_funct_2 @ X12 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X13))
% 0.36/0.55          | ~ (v1_funct_1 @ X12)
% 0.36/0.55          | ~ (l1_pre_topc @ X11)
% 0.36/0.55          | ~ (v2_pre_topc @ X11)
% 0.36/0.55          | (v2_struct_0 @ X11))),
% 0.36/0.55      inference('simplify', [status(thm)], ['23'])).
% 0.36/0.55  thf('25', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.55         ((v2_struct_0 @ X0)
% 0.36/0.55          | ~ (v2_pre_topc @ X0)
% 0.36/0.55          | ~ (l1_pre_topc @ X0)
% 0.36/0.55          | ~ (v1_funct_1 @ X1)
% 0.36/0.55          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 0.36/0.55          | ~ (m1_subset_1 @ X1 @ 
% 0.36/0.55               (k1_zfmisc_1 @ 
% 0.36/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 0.36/0.55          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.36/0.55          | ~ (r1_tmap_1 @ X0 @ sk_A @ X1 @ X2)
% 0.36/0.55          | (r1_tmap_1 @ X0 @ sk_B_1 @ 
% 0.36/0.55             (k1_partfun1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.55              (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ X1 @ sk_E) @ 
% 0.36/0.55             X2)
% 0.36/0.55          | ~ (r1_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ 
% 0.36/0.55               (k3_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ X1 @ 
% 0.36/0.55                X2))
% 0.36/0.55          | ~ (m1_subset_1 @ 
% 0.36/0.55               (k3_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ X1 @ 
% 0.36/0.55                X2) @ 
% 0.36/0.55               (u1_struct_0 @ sk_A))
% 0.36/0.55          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.55               (u1_struct_0 @ sk_B_1))
% 0.36/0.55          | ~ (v1_funct_1 @ sk_E)
% 0.36/0.55          | ~ (l1_pre_topc @ sk_A)
% 0.36/0.55          | ~ (v2_pre_topc @ sk_A)
% 0.36/0.55          | (v2_struct_0 @ sk_A)
% 0.36/0.55          | ~ (l1_pre_topc @ sk_B_1)
% 0.36/0.55          | ~ (v2_pre_topc @ sk_B_1)
% 0.36/0.55          | (v2_struct_0 @ sk_B_1))),
% 0.36/0.55      inference('sup-', [status(thm)], ['22', '24'])).
% 0.36/0.55  thf('26', plain,
% 0.36/0.55      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('27', plain, ((v1_funct_1 @ sk_E)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('29', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('30', plain, ((l1_pre_topc @ sk_B_1)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('31', plain, ((v2_pre_topc @ sk_B_1)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('32', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.55         ((v2_struct_0 @ X0)
% 0.36/0.55          | ~ (v2_pre_topc @ X0)
% 0.36/0.55          | ~ (l1_pre_topc @ X0)
% 0.36/0.55          | ~ (v1_funct_1 @ X1)
% 0.36/0.55          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 0.36/0.55          | ~ (m1_subset_1 @ X1 @ 
% 0.36/0.55               (k1_zfmisc_1 @ 
% 0.36/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 0.36/0.55          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.36/0.55          | ~ (r1_tmap_1 @ X0 @ sk_A @ X1 @ X2)
% 0.36/0.55          | (r1_tmap_1 @ X0 @ sk_B_1 @ 
% 0.36/0.55             (k1_partfun1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.55              (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ X1 @ sk_E) @ 
% 0.36/0.55             X2)
% 0.36/0.55          | ~ (r1_tmap_1 @ sk_A @ sk_B_1 @ sk_E @ 
% 0.36/0.55               (k3_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ X1 @ 
% 0.36/0.55                X2))
% 0.36/0.55          | ~ (m1_subset_1 @ 
% 0.36/0.55               (k3_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ X1 @ 
% 0.36/0.55                X2) @ 
% 0.36/0.55               (u1_struct_0 @ sk_A))
% 0.36/0.55          | (v2_struct_0 @ sk_A)
% 0.36/0.55          | (v2_struct_0 @ sk_B_1))),
% 0.36/0.55      inference('demod', [status(thm)],
% 0.36/0.55                ['25', '26', '27', '28', '29', '30', '31'])).
% 0.36/0.55  thf('33', plain,
% 0.36/0.55      (((v2_struct_0 @ sk_B_1)
% 0.36/0.55        | (v2_struct_0 @ sk_A)
% 0.36/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.36/0.55        | (v2_struct_0 @ sk_B_1)
% 0.36/0.55        | (v2_struct_0 @ sk_A)
% 0.36/0.55        | ~ (m1_subset_1 @ 
% 0.36/0.55             (k3_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.55              sk_D_1 @ sk_F) @ 
% 0.36/0.55             (u1_struct_0 @ sk_A))
% 0.36/0.55        | (r1_tmap_1 @ sk_C @ sk_B_1 @ 
% 0.36/0.55           (k1_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.55            (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_D_1 @ sk_E) @ 
% 0.36/0.55           sk_F)
% 0.36/0.55        | ~ (r1_tmap_1 @ sk_C @ sk_A @ sk_D_1 @ sk_F)
% 0.36/0.55        | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))
% 0.36/0.55        | ~ (m1_subset_1 @ sk_D_1 @ 
% 0.36/0.55             (k1_zfmisc_1 @ 
% 0.36/0.55              (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))
% 0.36/0.55        | ~ (v1_funct_2 @ sk_D_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))
% 0.36/0.55        | ~ (v1_funct_1 @ sk_D_1)
% 0.36/0.55        | ~ (l1_pre_topc @ sk_C)
% 0.36/0.55        | ~ (v2_pre_topc @ sk_C)
% 0.36/0.55        | (v2_struct_0 @ sk_C))),
% 0.36/0.55      inference('sup-', [status(thm)], ['21', '32'])).
% 0.36/0.55  thf('34', plain, ((r1_tmap_1 @ sk_C @ sk_A @ sk_D_1 @ sk_F)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('35', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('36', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_D_1 @ 
% 0.36/0.55        (k1_zfmisc_1 @ 
% 0.36/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('37', plain,
% 0.36/0.55      ((v1_funct_2 @ sk_D_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('38', plain, ((v1_funct_1 @ sk_D_1)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('39', plain, ((l1_pre_topc @ sk_C)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('40', plain, ((v2_pre_topc @ sk_C)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('41', plain,
% 0.36/0.55      (((v2_struct_0 @ sk_B_1)
% 0.36/0.55        | (v2_struct_0 @ sk_A)
% 0.36/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.36/0.55        | (v2_struct_0 @ sk_B_1)
% 0.36/0.55        | (v2_struct_0 @ sk_A)
% 0.36/0.55        | ~ (m1_subset_1 @ 
% 0.36/0.55             (k3_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.55              sk_D_1 @ sk_F) @ 
% 0.36/0.55             (u1_struct_0 @ sk_A))
% 0.36/0.55        | (r1_tmap_1 @ sk_C @ sk_B_1 @ 
% 0.36/0.55           (k1_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.55            (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_D_1 @ sk_E) @ 
% 0.36/0.55           sk_F)
% 0.36/0.55        | (v2_struct_0 @ sk_C))),
% 0.36/0.55      inference('demod', [status(thm)],
% 0.36/0.55                ['33', '34', '35', '36', '37', '38', '39', '40'])).
% 0.36/0.55  thf('42', plain,
% 0.36/0.55      (((v2_struct_0 @ sk_C)
% 0.36/0.55        | (r1_tmap_1 @ sk_C @ sk_B_1 @ 
% 0.36/0.55           (k1_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.55            (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_D_1 @ sk_E) @ 
% 0.36/0.55           sk_F)
% 0.36/0.55        | ~ (m1_subset_1 @ 
% 0.36/0.55             (k3_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.55              sk_D_1 @ sk_F) @ 
% 0.36/0.55             (u1_struct_0 @ sk_A))
% 0.36/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.36/0.55        | (v2_struct_0 @ sk_A)
% 0.36/0.55        | (v2_struct_0 @ sk_B_1))),
% 0.36/0.55      inference('simplify', [status(thm)], ['41'])).
% 0.36/0.55  thf('43', plain,
% 0.36/0.55      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.36/0.55        | (v2_struct_0 @ sk_B_1)
% 0.36/0.55        | (v2_struct_0 @ sk_A)
% 0.36/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.36/0.55        | (r1_tmap_1 @ sk_C @ sk_B_1 @ 
% 0.36/0.55           (k1_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.55            (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_D_1 @ sk_E) @ 
% 0.36/0.55           sk_F)
% 0.36/0.55        | (v2_struct_0 @ sk_C))),
% 0.36/0.55      inference('sup-', [status(thm)], ['8', '42'])).
% 0.36/0.55  thf('44', plain,
% 0.36/0.55      (((v2_struct_0 @ sk_C)
% 0.36/0.55        | (r1_tmap_1 @ sk_C @ sk_B_1 @ 
% 0.36/0.55           (k1_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.55            (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_D_1 @ sk_E) @ 
% 0.36/0.55           sk_F)
% 0.36/0.55        | (v2_struct_0 @ sk_A)
% 0.36/0.55        | (v2_struct_0 @ sk_B_1)
% 0.36/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_C)))),
% 0.36/0.55      inference('simplify', [status(thm)], ['43'])).
% 0.36/0.55  thf('45', plain,
% 0.36/0.55      (~ (r1_tmap_1 @ sk_C @ sk_B_1 @ 
% 0.36/0.55          (k1_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.55           (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_D_1 @ sk_E) @ 
% 0.36/0.55          sk_F)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('46', plain,
% 0.36/0.55      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.36/0.55        | (v2_struct_0 @ sk_B_1)
% 0.36/0.55        | (v2_struct_0 @ sk_A)
% 0.36/0.55        | (v2_struct_0 @ sk_C))),
% 0.36/0.55      inference('sup-', [status(thm)], ['44', '45'])).
% 0.36/0.55  thf(rc3_tops_1, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.55       ( ?[B:$i]:
% 0.36/0.55         ( ( v4_pre_topc @ B @ A ) & ( v3_pre_topc @ B @ A ) & 
% 0.36/0.55           ( ~( v1_xboole_0 @ B ) ) & 
% 0.36/0.55           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.36/0.55  thf('47', plain,
% 0.36/0.55      (![X6 : $i]:
% 0.36/0.55         ((m1_subset_1 @ (sk_B @ X6) @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.36/0.55          | ~ (l1_pre_topc @ X6)
% 0.36/0.55          | ~ (v2_pre_topc @ X6)
% 0.36/0.55          | (v2_struct_0 @ X6))),
% 0.36/0.55      inference('cnf', [status(esa)], [rc3_tops_1])).
% 0.36/0.55  thf(cc1_subset_1, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( v1_xboole_0 @ A ) =>
% 0.36/0.55       ( ![B:$i]:
% 0.36/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.36/0.55  thf('48', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]:
% 0.36/0.55         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.36/0.55          | (v1_xboole_0 @ X0)
% 0.36/0.55          | ~ (v1_xboole_0 @ X1))),
% 0.36/0.55      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.36/0.55  thf('49', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         ((v2_struct_0 @ X0)
% 0.36/0.55          | ~ (v2_pre_topc @ X0)
% 0.36/0.55          | ~ (l1_pre_topc @ X0)
% 0.36/0.55          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.36/0.55          | (v1_xboole_0 @ (sk_B @ X0)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['47', '48'])).
% 0.36/0.55  thf('50', plain,
% 0.36/0.55      (((v2_struct_0 @ sk_C)
% 0.36/0.55        | (v2_struct_0 @ sk_A)
% 0.36/0.55        | (v2_struct_0 @ sk_B_1)
% 0.36/0.55        | (v1_xboole_0 @ (sk_B @ sk_C))
% 0.36/0.55        | ~ (l1_pre_topc @ sk_C)
% 0.36/0.55        | ~ (v2_pre_topc @ sk_C)
% 0.36/0.55        | (v2_struct_0 @ sk_C))),
% 0.36/0.55      inference('sup-', [status(thm)], ['46', '49'])).
% 0.36/0.55  thf('51', plain, ((l1_pre_topc @ sk_C)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('52', plain, ((v2_pre_topc @ sk_C)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('53', plain,
% 0.36/0.55      (((v2_struct_0 @ sk_C)
% 0.36/0.55        | (v2_struct_0 @ sk_A)
% 0.36/0.55        | (v2_struct_0 @ sk_B_1)
% 0.36/0.55        | (v1_xboole_0 @ (sk_B @ sk_C))
% 0.36/0.55        | (v2_struct_0 @ sk_C))),
% 0.36/0.55      inference('demod', [status(thm)], ['50', '51', '52'])).
% 0.36/0.55  thf('54', plain,
% 0.36/0.55      (((v1_xboole_0 @ (sk_B @ sk_C))
% 0.36/0.55        | (v2_struct_0 @ sk_B_1)
% 0.36/0.55        | (v2_struct_0 @ sk_A)
% 0.36/0.55        | (v2_struct_0 @ sk_C))),
% 0.36/0.55      inference('simplify', [status(thm)], ['53'])).
% 0.36/0.55  thf('55', plain,
% 0.36/0.55      (![X6 : $i]:
% 0.36/0.55         (~ (v1_xboole_0 @ (sk_B @ X6))
% 0.36/0.55          | ~ (l1_pre_topc @ X6)
% 0.36/0.55          | ~ (v2_pre_topc @ X6)
% 0.36/0.55          | (v2_struct_0 @ X6))),
% 0.36/0.55      inference('cnf', [status(esa)], [rc3_tops_1])).
% 0.36/0.55  thf('56', plain,
% 0.36/0.55      (((v2_struct_0 @ sk_C)
% 0.36/0.55        | (v2_struct_0 @ sk_A)
% 0.36/0.55        | (v2_struct_0 @ sk_B_1)
% 0.36/0.55        | (v2_struct_0 @ sk_C)
% 0.36/0.55        | ~ (v2_pre_topc @ sk_C)
% 0.36/0.55        | ~ (l1_pre_topc @ sk_C))),
% 0.36/0.55      inference('sup-', [status(thm)], ['54', '55'])).
% 0.36/0.55  thf('57', plain, ((v2_pre_topc @ sk_C)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('58', plain, ((l1_pre_topc @ sk_C)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('59', plain,
% 0.36/0.55      (((v2_struct_0 @ sk_C)
% 0.36/0.55        | (v2_struct_0 @ sk_A)
% 0.36/0.55        | (v2_struct_0 @ sk_B_1)
% 0.36/0.55        | (v2_struct_0 @ sk_C))),
% 0.36/0.55      inference('demod', [status(thm)], ['56', '57', '58'])).
% 0.36/0.55  thf('60', plain,
% 0.36/0.55      (((v2_struct_0 @ sk_B_1) | (v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C))),
% 0.36/0.55      inference('simplify', [status(thm)], ['59'])).
% 0.36/0.55  thf('61', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('62', plain, (((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A))),
% 0.36/0.55      inference('clc', [status(thm)], ['60', '61'])).
% 0.36/0.55  thf('63', plain, (~ (v2_struct_0 @ sk_C)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('64', plain, ((v2_struct_0 @ sk_A)),
% 0.36/0.55      inference('clc', [status(thm)], ['62', '63'])).
% 0.36/0.55  thf('65', plain, ($false), inference('demod', [status(thm)], ['0', '64'])).
% 0.36/0.55  
% 0.36/0.55  % SZS output end Refutation
% 0.36/0.55  
% 0.36/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
