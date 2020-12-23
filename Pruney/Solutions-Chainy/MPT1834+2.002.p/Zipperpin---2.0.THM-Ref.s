%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YUa72bH9HZ

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:13 EST 2020

% Result     : Theorem 2.52s
% Output     : Refutation 2.52s
% Verified   : 
% Statistics : Number of formulae       :  545 (1704 expanded)
%              Number of leaves         :   33 ( 444 expanded)
%              Depth                    :   45
%              Number of atoms          : 23062 (125685 expanded)
%              Number of equality atoms :   15 (  15 expanded)
%              Maximal formula depth    :   35 (  13 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(r4_tsep_1_type,type,(
    r4_tsep_1: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tsep_1_type,type,(
    r1_tsep_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(k10_tmap_1_type,type,(
    k10_tmap_1: $i > $i > $i > $i > $i > $i > $i )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_E_1_type,type,(
    sk_E_1: $i )).

thf(k1_tsep_1_type,type,(
    k1_tsep_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r3_tsep_1_type,type,(
    r3_tsep_1: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t150_tmap_1,conjecture,(
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
             => ( ( r3_tsep_1 @ A @ B @ C )
              <=> ( ( r1_tsep_1 @ B @ C )
                  & ! [D: $i] :
                      ( ( ~ ( v2_struct_0 @ D )
                        & ( v2_pre_topc @ D )
                        & ( l1_pre_topc @ D ) )
                     => ! [E: $i] :
                          ( ( ( v1_funct_1 @ E )
                            & ( v1_funct_2 @ E @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ D ) )
                            & ( v5_pre_topc @ E @ B @ D )
                            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ D ) ) ) ) )
                         => ! [F: $i] :
                              ( ( ( v1_funct_1 @ F )
                                & ( v1_funct_2 @ F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ D ) )
                                & ( v5_pre_topc @ F @ C @ D )
                                & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ D ) ) ) ) )
                             => ( ( v1_funct_1 @ ( k10_tmap_1 @ A @ D @ B @ C @ E @ F ) )
                                & ( v1_funct_2 @ ( k10_tmap_1 @ A @ D @ B @ C @ E @ F ) @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) @ ( u1_struct_0 @ D ) )
                                & ( v5_pre_topc @ ( k10_tmap_1 @ A @ D @ B @ C @ E @ F ) @ ( k1_tsep_1 @ A @ B @ C ) @ D )
                                & ( m1_subset_1 @ ( k10_tmap_1 @ A @ D @ B @ C @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) @ ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ) )).

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
               => ( ( r3_tsep_1 @ A @ B @ C )
                <=> ( ( r1_tsep_1 @ B @ C )
                    & ! [D: $i] :
                        ( ( ~ ( v2_struct_0 @ D )
                          & ( v2_pre_topc @ D )
                          & ( l1_pre_topc @ D ) )
                       => ! [E: $i] :
                            ( ( ( v1_funct_1 @ E )
                              & ( v1_funct_2 @ E @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ D ) )
                              & ( v5_pre_topc @ E @ B @ D )
                              & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ D ) ) ) ) )
                           => ! [F: $i] :
                                ( ( ( v1_funct_1 @ F )
                                  & ( v1_funct_2 @ F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ D ) )
                                  & ( v5_pre_topc @ F @ C @ D )
                                  & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ D ) ) ) ) )
                               => ( ( v1_funct_1 @ ( k10_tmap_1 @ A @ D @ B @ C @ E @ F ) )
                                  & ( v1_funct_2 @ ( k10_tmap_1 @ A @ D @ B @ C @ E @ F ) @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) @ ( u1_struct_0 @ D ) )
                                  & ( v5_pre_topc @ ( k10_tmap_1 @ A @ D @ B @ C @ E @ F ) @ ( k1_tsep_1 @ A @ B @ C ) @ D )
                                  & ( m1_subset_1 @ ( k10_tmap_1 @ A @ D @ B @ C @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) @ ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t150_tmap_1])).

thf('0',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_C )
    | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
   <= ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf(t135_tmap_1,axiom,(
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
             => ( ( r3_tsep_1 @ A @ B @ C )
              <=> ( ( r1_tsep_1 @ B @ C )
                  & ! [D: $i] :
                      ( ( ~ ( v2_struct_0 @ D )
                        & ( v2_pre_topc @ D )
                        & ( l1_pre_topc @ D ) )
                     => ! [E: $i] :
                          ( ( ( v1_funct_1 @ E )
                            & ( v1_funct_2 @ E @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) @ ( u1_struct_0 @ D ) )
                            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) @ ( u1_struct_0 @ D ) ) ) ) )
                         => ( ( ( v1_funct_1 @ ( k3_tmap_1 @ A @ D @ ( k1_tsep_1 @ A @ B @ C ) @ B @ E ) )
                              & ( v1_funct_2 @ ( k3_tmap_1 @ A @ D @ ( k1_tsep_1 @ A @ B @ C ) @ B @ E ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ D ) )
                              & ( v5_pre_topc @ ( k3_tmap_1 @ A @ D @ ( k1_tsep_1 @ A @ B @ C ) @ B @ E ) @ B @ D )
                              & ( m1_subset_1 @ ( k3_tmap_1 @ A @ D @ ( k1_tsep_1 @ A @ B @ C ) @ B @ E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ D ) ) ) )
                              & ( v1_funct_1 @ ( k3_tmap_1 @ A @ D @ ( k1_tsep_1 @ A @ B @ C ) @ C @ E ) )
                              & ( v1_funct_2 @ ( k3_tmap_1 @ A @ D @ ( k1_tsep_1 @ A @ B @ C ) @ C @ E ) @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ D ) )
                              & ( v5_pre_topc @ ( k3_tmap_1 @ A @ D @ ( k1_tsep_1 @ A @ B @ C ) @ C @ E ) @ C @ D )
                              & ( m1_subset_1 @ ( k3_tmap_1 @ A @ D @ ( k1_tsep_1 @ A @ B @ C ) @ C @ E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ D ) ) ) ) )
                           => ( ( v1_funct_1 @ E )
                              & ( v1_funct_2 @ E @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) @ ( u1_struct_0 @ D ) )
                              & ( v5_pre_topc @ E @ ( k1_tsep_1 @ A @ B @ C ) @ D )
                              & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) @ ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v2_struct_0 @ X10 )
      | ~ ( m1_pre_topc @ X10 @ X11 )
      | ~ ( r3_tsep_1 @ X11 @ X10 @ X12 )
      | ( r1_tsep_1 @ X10 @ X12 )
      | ~ ( m1_pre_topc @ X12 @ X11 )
      | ( v2_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t135_tmap_1])).

thf('4',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ sk_A )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ~ ( m1_pre_topc @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['4','5','6','7','8'])).

thf('10',plain,
    ( ( v1_funct_1 @ sk_E_1 )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_C )
   <= ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['10'])).

thf('12',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_tsep_1 @ sk_B @ sk_C )
      & ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ~ ( r1_tsep_1 @ sk_B @ sk_C )
      & ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(clc,[status(thm)],['12','13'])).

thf('15',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( v2_struct_0 @ sk_C )
   <= ( ~ ( r1_tsep_1 @ sk_B @ sk_C )
      & ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(clc,[status(thm)],['14','15'])).

thf('17',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_C )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( v1_funct_1 @ sk_F )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( v1_funct_1 @ sk_F )
   <= ( v1_funct_1 @ sk_F ) ),
    inference(split,[status(esa)],['20'])).

thf('22',plain,
    ( ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
   <= ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(split,[status(esa)],['22'])).

thf('24',plain,
    ( ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
   <= ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ) ),
    inference(split,[status(esa)],['24'])).

thf('26',plain,
    ( ( l1_pre_topc @ sk_D_1 )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( l1_pre_topc @ sk_D_1 )
   <= ( l1_pre_topc @ sk_D_1 ) ),
    inference(split,[status(esa)],['26'])).

thf('28',plain,
    ( ( v2_pre_topc @ sk_D_1 )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( v2_pre_topc @ sk_D_1 )
   <= ( v2_pre_topc @ sk_D_1 ) ),
    inference(split,[status(esa)],['28'])).

thf('30',plain,
    ( ( v1_funct_1 @ sk_E_1 )
   <= ( v1_funct_1 @ sk_E_1 ) ),
    inference(split,[status(esa)],['10'])).

thf('31',plain,
    ( ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
   <= ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(split,[status(esa)],['31'])).

thf('33',plain,
    ( ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
   <= ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ) ),
    inference(split,[status(esa)],['33'])).

thf(dt_k10_tmap_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ~ ( v2_struct_0 @ B )
        & ( v2_pre_topc @ B )
        & ( l1_pre_topc @ B )
        & ~ ( v2_struct_0 @ C )
        & ( m1_pre_topc @ C @ A )
        & ~ ( v2_struct_0 @ D )
        & ( m1_pre_topc @ D @ A )
        & ( v1_funct_1 @ E )
        & ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) )
        & ( v1_funct_1 @ F )
        & ( v1_funct_2 @ F @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) )
     => ( ( v1_funct_1 @ ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) )
        & ( v1_funct_2 @ ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) )
        & ( m1_subset_1 @ ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) ) ) ) ) ) )).

thf('35',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X5 ) @ ( u1_struct_0 @ X6 ) ) ) )
      | ~ ( v1_funct_2 @ X4 @ ( u1_struct_0 @ X5 ) @ ( u1_struct_0 @ X6 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( m1_pre_topc @ X7 @ X8 )
      | ( v2_struct_0 @ X7 )
      | ~ ( m1_pre_topc @ X5 @ X8 )
      | ( v2_struct_0 @ X5 )
      | ~ ( l1_pre_topc @ X6 )
      | ~ ( v2_pre_topc @ X6 )
      | ( v2_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 )
      | ( v2_struct_0 @ X8 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_funct_2 @ X9 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X6 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X6 ) ) ) )
      | ( v1_funct_2 @ ( k10_tmap_1 @ X8 @ X6 @ X5 @ X7 @ X4 @ X9 ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X8 @ X5 @ X7 ) ) @ ( u1_struct_0 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k10_tmap_1])).

thf('36',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( v1_funct_2 @ ( k10_tmap_1 @ X1 @ sk_D_1 @ sk_B @ X0 @ sk_E_1 @ X2 ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X1 @ sk_B @ X0 ) ) @ ( u1_struct_0 @ sk_D_1 ) )
        | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
        | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_D_1 ) )
        | ~ ( v1_funct_1 @ X2 )
        | ( v2_struct_0 @ X1 )
        | ~ ( v2_pre_topc @ X1 )
        | ~ ( l1_pre_topc @ X1 )
        | ( v2_struct_0 @ sk_D_1 )
        | ~ ( v2_pre_topc @ sk_D_1 )
        | ~ ( l1_pre_topc @ sk_D_1 )
        | ( v2_struct_0 @ sk_B )
        | ~ ( m1_pre_topc @ sk_B @ X1 )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ X0 @ X1 )
        | ~ ( v1_funct_1 @ sk_E_1 )
        | ~ ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) )
   <= ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ~ ( v1_funct_1 @ sk_E_1 )
        | ~ ( m1_pre_topc @ X1 @ X0 )
        | ( v2_struct_0 @ X1 )
        | ~ ( m1_pre_topc @ sk_B @ X0 )
        | ( v2_struct_0 @ sk_B )
        | ~ ( l1_pre_topc @ sk_D_1 )
        | ~ ( v2_pre_topc @ sk_D_1 )
        | ( v2_struct_0 @ sk_D_1 )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 )
        | ~ ( v1_funct_1 @ X2 )
        | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_D_1 ) )
        | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
        | ( v1_funct_2 @ ( k10_tmap_1 @ X0 @ sk_D_1 @ sk_B @ X1 @ sk_E_1 @ X2 ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X0 @ sk_B @ X1 ) ) @ ( u1_struct_0 @ sk_D_1 ) ) )
   <= ( ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['32','36'])).

thf('38',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( v1_funct_2 @ ( k10_tmap_1 @ X1 @ sk_D_1 @ sk_B @ X0 @ sk_E_1 @ X2 ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X1 @ sk_B @ X0 ) ) @ ( u1_struct_0 @ sk_D_1 ) )
        | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
        | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_D_1 ) )
        | ~ ( v1_funct_1 @ X2 )
        | ( v2_struct_0 @ X1 )
        | ~ ( v2_pre_topc @ X1 )
        | ~ ( l1_pre_topc @ X1 )
        | ( v2_struct_0 @ sk_D_1 )
        | ~ ( v2_pre_topc @ sk_D_1 )
        | ~ ( l1_pre_topc @ sk_D_1 )
        | ( v2_struct_0 @ sk_B )
        | ~ ( m1_pre_topc @ sk_B @ X1 )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ X0 @ X1 ) )
   <= ( ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['30','37'])).

thf('39',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ~ ( m1_pre_topc @ X1 @ X0 )
        | ( v2_struct_0 @ X1 )
        | ~ ( m1_pre_topc @ sk_B @ X0 )
        | ( v2_struct_0 @ sk_B )
        | ~ ( l1_pre_topc @ sk_D_1 )
        | ( v2_struct_0 @ sk_D_1 )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 )
        | ~ ( v1_funct_1 @ X2 )
        | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_D_1 ) )
        | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
        | ( v1_funct_2 @ ( k10_tmap_1 @ X0 @ sk_D_1 @ sk_B @ X1 @ sk_E_1 @ X2 ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X0 @ sk_B @ X1 ) ) @ ( u1_struct_0 @ sk_D_1 ) ) )
   <= ( ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['29','38'])).

thf('40',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( v1_funct_2 @ ( k10_tmap_1 @ X1 @ sk_D_1 @ sk_B @ X0 @ sk_E_1 @ X2 ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X1 @ sk_B @ X0 ) ) @ ( u1_struct_0 @ sk_D_1 ) )
        | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
        | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_D_1 ) )
        | ~ ( v1_funct_1 @ X2 )
        | ( v2_struct_0 @ X1 )
        | ~ ( v2_pre_topc @ X1 )
        | ~ ( l1_pre_topc @ X1 )
        | ( v2_struct_0 @ sk_D_1 )
        | ( v2_struct_0 @ sk_B )
        | ~ ( m1_pre_topc @ sk_B @ X1 )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ X0 @ X1 ) )
   <= ( ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['27','39'])).

thf('41',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_pre_topc @ sk_C @ X0 )
        | ( v2_struct_0 @ sk_C )
        | ~ ( m1_pre_topc @ sk_B @ X0 )
        | ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_D_1 )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 )
        | ~ ( v1_funct_1 @ sk_F )
        | ~ ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
        | ( v1_funct_2 @ ( k10_tmap_1 @ X0 @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X0 @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_D_1 ) ) )
   <= ( ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['25','40'])).

thf('42',plain,
    ( ! [X0: $i] :
        ( ( v1_funct_2 @ ( k10_tmap_1 @ X0 @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X0 @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_D_1 ) )
        | ~ ( v1_funct_1 @ sk_F )
        | ( v2_struct_0 @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ( v2_struct_0 @ sk_D_1 )
        | ( v2_struct_0 @ sk_B )
        | ~ ( m1_pre_topc @ sk_B @ X0 )
        | ( v2_struct_0 @ sk_C )
        | ~ ( m1_pre_topc @ sk_C @ X0 ) )
   <= ( ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['23','41'])).

thf('43',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_pre_topc @ sk_C @ X0 )
        | ( v2_struct_0 @ sk_C )
        | ~ ( m1_pre_topc @ sk_B @ X0 )
        | ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_D_1 )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 )
        | ( v1_funct_2 @ ( k10_tmap_1 @ X0 @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X0 @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_D_1 ) ) )
   <= ( ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v1_funct_1 @ sk_F )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['21','42'])).

thf('44',plain,
    ( ( ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_D_1 ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v1_funct_1 @ sk_F )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['19','43'])).

thf('45',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_D_1 ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v1_funct_1 @ sk_F )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['44','45','46','47'])).

thf('49',plain,
    ( ~ ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
    | ~ ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D_1 )
    | ~ ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ~ ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ~ ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_D_1 ) )
   <= ~ ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(split,[status(esa)],['49'])).

thf('51',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v1_funct_1 @ sk_F )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['48','50'])).

thf('52',plain,
    ( ~ ( v2_struct_0 @ sk_D_1 )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ~ ( v2_struct_0 @ sk_D_1 )
   <= ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(split,[status(esa)],['52'])).

thf('54',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ~ ( v2_struct_0 @ sk_D_1 )
      & ~ ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v1_funct_1 @ sk_F )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['51','53'])).

thf('55',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( v2_struct_0 @ sk_D_1 )
      & ~ ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v1_funct_1 @ sk_F )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference(clc,[status(thm)],['54','55'])).

thf('57',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( v2_struct_0 @ sk_B )
   <= ( ~ ( v2_struct_0 @ sk_D_1 )
      & ~ ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v1_funct_1 @ sk_F )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference(clc,[status(thm)],['56','57'])).

thf('59',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ~ ( v1_funct_1 @ sk_E_1 )
    | ~ ( v2_pre_topc @ sk_D_1 )
    | ~ ( l1_pre_topc @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_F )
    | ~ ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ~ ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
    | ~ ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
    | ~ ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( v1_funct_1 @ sk_F )
   <= ( v1_funct_1 @ sk_F ) ),
    inference(split,[status(esa)],['20'])).

thf('63',plain,
    ( ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
   <= ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(split,[status(esa)],['22'])).

thf('64',plain,
    ( ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
   <= ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ) ),
    inference(split,[status(esa)],['24'])).

thf('65',plain,
    ( ( l1_pre_topc @ sk_D_1 )
   <= ( l1_pre_topc @ sk_D_1 ) ),
    inference(split,[status(esa)],['26'])).

thf('66',plain,
    ( ( v2_pre_topc @ sk_D_1 )
   <= ( v2_pre_topc @ sk_D_1 ) ),
    inference(split,[status(esa)],['28'])).

thf('67',plain,
    ( ( v1_funct_1 @ sk_E_1 )
   <= ( v1_funct_1 @ sk_E_1 ) ),
    inference(split,[status(esa)],['10'])).

thf('68',plain,
    ( ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
   <= ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(split,[status(esa)],['31'])).

thf('69',plain,
    ( ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
   <= ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ) ),
    inference(split,[status(esa)],['33'])).

thf('70',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X5 ) @ ( u1_struct_0 @ X6 ) ) ) )
      | ~ ( v1_funct_2 @ X4 @ ( u1_struct_0 @ X5 ) @ ( u1_struct_0 @ X6 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( m1_pre_topc @ X7 @ X8 )
      | ( v2_struct_0 @ X7 )
      | ~ ( m1_pre_topc @ X5 @ X8 )
      | ( v2_struct_0 @ X5 )
      | ~ ( l1_pre_topc @ X6 )
      | ~ ( v2_pre_topc @ X6 )
      | ( v2_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 )
      | ( v2_struct_0 @ X8 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_funct_2 @ X9 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X6 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X6 ) ) ) )
      | ( m1_subset_1 @ ( k10_tmap_1 @ X8 @ X6 @ X5 @ X7 @ X4 @ X9 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X8 @ X5 @ X7 ) ) @ ( u1_struct_0 @ X6 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k10_tmap_1])).

thf('71',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( m1_subset_1 @ ( k10_tmap_1 @ X1 @ sk_D_1 @ sk_B @ X0 @ sk_E_1 @ X2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X1 @ sk_B @ X0 ) ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
        | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
        | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_D_1 ) )
        | ~ ( v1_funct_1 @ X2 )
        | ( v2_struct_0 @ X1 )
        | ~ ( v2_pre_topc @ X1 )
        | ~ ( l1_pre_topc @ X1 )
        | ( v2_struct_0 @ sk_D_1 )
        | ~ ( v2_pre_topc @ sk_D_1 )
        | ~ ( l1_pre_topc @ sk_D_1 )
        | ( v2_struct_0 @ sk_B )
        | ~ ( m1_pre_topc @ sk_B @ X1 )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ X0 @ X1 )
        | ~ ( v1_funct_1 @ sk_E_1 )
        | ~ ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) )
   <= ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ~ ( v1_funct_1 @ sk_E_1 )
        | ~ ( m1_pre_topc @ X1 @ X0 )
        | ( v2_struct_0 @ X1 )
        | ~ ( m1_pre_topc @ sk_B @ X0 )
        | ( v2_struct_0 @ sk_B )
        | ~ ( l1_pre_topc @ sk_D_1 )
        | ~ ( v2_pre_topc @ sk_D_1 )
        | ( v2_struct_0 @ sk_D_1 )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 )
        | ~ ( v1_funct_1 @ X2 )
        | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_D_1 ) )
        | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
        | ( m1_subset_1 @ ( k10_tmap_1 @ X0 @ sk_D_1 @ sk_B @ X1 @ sk_E_1 @ X2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X0 @ sk_B @ X1 ) ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ) )
   <= ( ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['68','71'])).

thf('73',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( m1_subset_1 @ ( k10_tmap_1 @ X1 @ sk_D_1 @ sk_B @ X0 @ sk_E_1 @ X2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X1 @ sk_B @ X0 ) ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
        | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
        | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_D_1 ) )
        | ~ ( v1_funct_1 @ X2 )
        | ( v2_struct_0 @ X1 )
        | ~ ( v2_pre_topc @ X1 )
        | ~ ( l1_pre_topc @ X1 )
        | ( v2_struct_0 @ sk_D_1 )
        | ~ ( v2_pre_topc @ sk_D_1 )
        | ~ ( l1_pre_topc @ sk_D_1 )
        | ( v2_struct_0 @ sk_B )
        | ~ ( m1_pre_topc @ sk_B @ X1 )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ X0 @ X1 ) )
   <= ( ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['67','72'])).

thf('74',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ~ ( m1_pre_topc @ X1 @ X0 )
        | ( v2_struct_0 @ X1 )
        | ~ ( m1_pre_topc @ sk_B @ X0 )
        | ( v2_struct_0 @ sk_B )
        | ~ ( l1_pre_topc @ sk_D_1 )
        | ( v2_struct_0 @ sk_D_1 )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 )
        | ~ ( v1_funct_1 @ X2 )
        | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_D_1 ) )
        | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
        | ( m1_subset_1 @ ( k10_tmap_1 @ X0 @ sk_D_1 @ sk_B @ X1 @ sk_E_1 @ X2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X0 @ sk_B @ X1 ) ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ) )
   <= ( ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['66','73'])).

thf('75',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( m1_subset_1 @ ( k10_tmap_1 @ X1 @ sk_D_1 @ sk_B @ X0 @ sk_E_1 @ X2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X1 @ sk_B @ X0 ) ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
        | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
        | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_D_1 ) )
        | ~ ( v1_funct_1 @ X2 )
        | ( v2_struct_0 @ X1 )
        | ~ ( v2_pre_topc @ X1 )
        | ~ ( l1_pre_topc @ X1 )
        | ( v2_struct_0 @ sk_D_1 )
        | ( v2_struct_0 @ sk_B )
        | ~ ( m1_pre_topc @ sk_B @ X1 )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ X0 @ X1 ) )
   <= ( ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['65','74'])).

thf('76',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_pre_topc @ sk_C @ X0 )
        | ( v2_struct_0 @ sk_C )
        | ~ ( m1_pre_topc @ sk_B @ X0 )
        | ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_D_1 )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 )
        | ~ ( v1_funct_1 @ sk_F )
        | ~ ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
        | ( m1_subset_1 @ ( k10_tmap_1 @ X0 @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X0 @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ) )
   <= ( ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['64','75'])).

thf('77',plain,
    ( ! [X0: $i] :
        ( ( m1_subset_1 @ ( k10_tmap_1 @ X0 @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X0 @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
        | ~ ( v1_funct_1 @ sk_F )
        | ( v2_struct_0 @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ( v2_struct_0 @ sk_D_1 )
        | ( v2_struct_0 @ sk_B )
        | ~ ( m1_pre_topc @ sk_B @ X0 )
        | ( v2_struct_0 @ sk_C )
        | ~ ( m1_pre_topc @ sk_C @ X0 ) )
   <= ( ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['63','76'])).

thf('78',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_pre_topc @ sk_C @ X0 )
        | ( v2_struct_0 @ sk_C )
        | ~ ( m1_pre_topc @ sk_B @ X0 )
        | ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_D_1 )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 )
        | ( m1_subset_1 @ ( k10_tmap_1 @ X0 @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X0 @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ) )
   <= ( ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v1_funct_1 @ sk_F )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['62','77'])).

thf('79',plain,
    ( ( ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v1_funct_1 @ sk_F )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['61','78'])).

thf('80',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v1_funct_1 @ sk_F )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['79','80','81','82'])).

thf('84',plain,
    ( ~ ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
   <= ~ ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ) ),
    inference(split,[status(esa)],['49'])).

thf('85',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v1_funct_1 @ sk_F )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ~ ( v2_struct_0 @ sk_D_1 )
   <= ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(split,[status(esa)],['52'])).

thf('87',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ~ ( v2_struct_0 @ sk_D_1 )
      & ~ ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v1_funct_1 @ sk_F )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( v2_struct_0 @ sk_D_1 )
      & ~ ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v1_funct_1 @ sk_F )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference(clc,[status(thm)],['87','88'])).

thf('90',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( v2_struct_0 @ sk_B )
   <= ( ~ ( v2_struct_0 @ sk_D_1 )
      & ~ ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v1_funct_1 @ sk_F )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference(clc,[status(thm)],['89','90'])).

thf('92',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
    | ~ ( v1_funct_1 @ sk_E_1 )
    | ~ ( v2_pre_topc @ sk_D_1 )
    | ~ ( l1_pre_topc @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_F )
    | ~ ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ~ ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
    | ~ ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
    | ~ ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
   <= ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf(t85_tsep_1,axiom,(
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
             => ( ( ( r1_tsep_1 @ B @ C )
                  & ( r4_tsep_1 @ A @ B @ C ) )
              <=> ( r3_tsep_1 @ A @ B @ C ) ) ) ) ) )).

thf('95',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v2_struct_0 @ X26 )
      | ~ ( m1_pre_topc @ X26 @ X27 )
      | ~ ( r3_tsep_1 @ X27 @ X26 @ X28 )
      | ( r4_tsep_1 @ X27 @ X26 @ X28 )
      | ~ ( m1_pre_topc @ X28 @ X27 )
      | ( v2_struct_0 @ X28 )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t85_tsep_1])).

thf('96',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ sk_A )
      | ( r4_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ~ ( m1_pre_topc @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r4_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['96','97','98','99','100'])).

thf('102',plain,
    ( ( v1_funct_1 @ sk_E_1 )
   <= ( v1_funct_1 @ sk_E_1 ) ),
    inference(split,[status(esa)],['10'])).

thf('103',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['4','5','6','7','8'])).

thf('104',plain,
    ( ( v5_pre_topc @ sk_E_1 @ sk_B @ sk_D_1 )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ( v5_pre_topc @ sk_E_1 @ sk_B @ sk_D_1 )
   <= ( v5_pre_topc @ sk_E_1 @ sk_B @ sk_D_1 ) ),
    inference(split,[status(esa)],['104'])).

thf('106',plain,
    ( ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
   <= ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(split,[status(esa)],['31'])).

thf('107',plain,
    ( ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
   <= ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ) ),
    inference(split,[status(esa)],['33'])).

thf('108',plain,
    ( ( l1_pre_topc @ sk_D_1 )
   <= ( l1_pre_topc @ sk_D_1 ) ),
    inference(split,[status(esa)],['26'])).

thf('109',plain,
    ( ( v2_pre_topc @ sk_D_1 )
   <= ( v2_pre_topc @ sk_D_1 ) ),
    inference(split,[status(esa)],['28'])).

thf('110',plain,
    ( ( v1_funct_1 @ sk_F )
   <= ( v1_funct_1 @ sk_F ) ),
    inference(split,[status(esa)],['20'])).

thf('111',plain,
    ( ( v5_pre_topc @ sk_F @ sk_C @ sk_D_1 )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
    ( ( v5_pre_topc @ sk_F @ sk_C @ sk_D_1 )
   <= ( v5_pre_topc @ sk_F @ sk_C @ sk_D_1 ) ),
    inference(split,[status(esa)],['111'])).

thf('113',plain,
    ( ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
   <= ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(split,[status(esa)],['22'])).

thf('114',plain,
    ( ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
   <= ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ) ),
    inference(split,[status(esa)],['24'])).

thf(t145_tmap_1,axiom,(
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
                & ( m1_pre_topc @ C @ A ) )
             => ! [D: $i] :
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( m1_pre_topc @ D @ A ) )
                 => ( ( r1_tsep_1 @ C @ D )
                   => ! [E: $i] :
                        ( ( ( v1_funct_1 @ E )
                          & ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
                          & ( v5_pre_topc @ E @ C @ B )
                          & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) )
                       => ! [F: $i] :
                            ( ( ( v1_funct_1 @ F )
                              & ( v1_funct_2 @ F @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
                              & ( v5_pre_topc @ F @ D @ B )
                              & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) )
                           => ( ( r4_tsep_1 @ A @ C @ D )
                             => ( ( v1_funct_1 @ ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) )
                                & ( v1_funct_2 @ ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) )
                                & ( v5_pre_topc @ ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ ( k1_tsep_1 @ A @ C @ D ) @ B )
                                & ( m1_subset_1 @ ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) ) )).

thf('115',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( v2_struct_0 @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ~ ( l1_pre_topc @ X20 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_pre_topc @ X21 @ X22 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_funct_2 @ X23 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X20 ) )
      | ~ ( v5_pre_topc @ X23 @ X21 @ X20 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X20 ) ) ) )
      | ( v5_pre_topc @ ( k10_tmap_1 @ X22 @ X20 @ X24 @ X21 @ X25 @ X23 ) @ ( k1_tsep_1 @ X22 @ X24 @ X21 ) @ X20 )
      | ~ ( r4_tsep_1 @ X22 @ X24 @ X21 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X20 ) ) ) )
      | ~ ( v5_pre_topc @ X25 @ X24 @ X20 )
      | ~ ( v1_funct_2 @ X25 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X20 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( r1_tsep_1 @ X24 @ X21 )
      | ~ ( m1_pre_topc @ X24 @ X22 )
      | ( v2_struct_0 @ X24 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t145_tmap_1])).

thf('116',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( v2_struct_0 @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ( v2_struct_0 @ X1 )
        | ~ ( m1_pre_topc @ X1 @ X0 )
        | ~ ( r1_tsep_1 @ X1 @ sk_C )
        | ~ ( v1_funct_1 @ X2 )
        | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_D_1 ) )
        | ~ ( v5_pre_topc @ X2 @ X1 @ sk_D_1 )
        | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
        | ~ ( r4_tsep_1 @ X0 @ X1 @ sk_C )
        | ( v5_pre_topc @ ( k10_tmap_1 @ X0 @ sk_D_1 @ X1 @ sk_C @ X2 @ sk_F ) @ ( k1_tsep_1 @ X0 @ X1 @ sk_C ) @ sk_D_1 )
        | ~ ( v5_pre_topc @ sk_F @ sk_C @ sk_D_1 )
        | ~ ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
        | ~ ( v1_funct_1 @ sk_F )
        | ~ ( m1_pre_topc @ sk_C @ X0 )
        | ( v2_struct_0 @ sk_C )
        | ~ ( l1_pre_topc @ sk_D_1 )
        | ~ ( v2_pre_topc @ sk_D_1 )
        | ( v2_struct_0 @ sk_D_1 ) )
   <= ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( v2_struct_0 @ sk_D_1 )
        | ~ ( v2_pre_topc @ sk_D_1 )
        | ~ ( l1_pre_topc @ sk_D_1 )
        | ( v2_struct_0 @ sk_C )
        | ~ ( m1_pre_topc @ sk_C @ X0 )
        | ~ ( v1_funct_1 @ sk_F )
        | ~ ( v5_pre_topc @ sk_F @ sk_C @ sk_D_1 )
        | ( v5_pre_topc @ ( k10_tmap_1 @ X0 @ sk_D_1 @ X1 @ sk_C @ X2 @ sk_F ) @ ( k1_tsep_1 @ X0 @ X1 @ sk_C ) @ sk_D_1 )
        | ~ ( r4_tsep_1 @ X0 @ X1 @ sk_C )
        | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
        | ~ ( v5_pre_topc @ X2 @ X1 @ sk_D_1 )
        | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_D_1 ) )
        | ~ ( v1_funct_1 @ X2 )
        | ~ ( r1_tsep_1 @ X1 @ sk_C )
        | ~ ( m1_pre_topc @ X1 @ X0 )
        | ( v2_struct_0 @ X1 )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 ) )
   <= ( ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['113','116'])).

thf('118',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( v2_struct_0 @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ( v2_struct_0 @ X1 )
        | ~ ( m1_pre_topc @ X1 @ X0 )
        | ~ ( r1_tsep_1 @ X1 @ sk_C )
        | ~ ( v1_funct_1 @ X2 )
        | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_D_1 ) )
        | ~ ( v5_pre_topc @ X2 @ X1 @ sk_D_1 )
        | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
        | ~ ( r4_tsep_1 @ X0 @ X1 @ sk_C )
        | ( v5_pre_topc @ ( k10_tmap_1 @ X0 @ sk_D_1 @ X1 @ sk_C @ X2 @ sk_F ) @ ( k1_tsep_1 @ X0 @ X1 @ sk_C ) @ sk_D_1 )
        | ~ ( v1_funct_1 @ sk_F )
        | ~ ( m1_pre_topc @ sk_C @ X0 )
        | ( v2_struct_0 @ sk_C )
        | ~ ( l1_pre_topc @ sk_D_1 )
        | ~ ( v2_pre_topc @ sk_D_1 )
        | ( v2_struct_0 @ sk_D_1 ) )
   <= ( ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v5_pre_topc @ sk_F @ sk_C @ sk_D_1 )
      & ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['112','117'])).

thf('119',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( v2_struct_0 @ sk_D_1 )
        | ~ ( v2_pre_topc @ sk_D_1 )
        | ~ ( l1_pre_topc @ sk_D_1 )
        | ( v2_struct_0 @ sk_C )
        | ~ ( m1_pre_topc @ sk_C @ X0 )
        | ( v5_pre_topc @ ( k10_tmap_1 @ X0 @ sk_D_1 @ X1 @ sk_C @ X2 @ sk_F ) @ ( k1_tsep_1 @ X0 @ X1 @ sk_C ) @ sk_D_1 )
        | ~ ( r4_tsep_1 @ X0 @ X1 @ sk_C )
        | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
        | ~ ( v5_pre_topc @ X2 @ X1 @ sk_D_1 )
        | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_D_1 ) )
        | ~ ( v1_funct_1 @ X2 )
        | ~ ( r1_tsep_1 @ X1 @ sk_C )
        | ~ ( m1_pre_topc @ X1 @ X0 )
        | ( v2_struct_0 @ X1 )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 ) )
   <= ( ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v5_pre_topc @ sk_F @ sk_C @ sk_D_1 )
      & ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v1_funct_1 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['110','118'])).

thf('120',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( v2_struct_0 @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ( v2_struct_0 @ X1 )
        | ~ ( m1_pre_topc @ X1 @ X0 )
        | ~ ( r1_tsep_1 @ X1 @ sk_C )
        | ~ ( v1_funct_1 @ X2 )
        | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_D_1 ) )
        | ~ ( v5_pre_topc @ X2 @ X1 @ sk_D_1 )
        | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
        | ~ ( r4_tsep_1 @ X0 @ X1 @ sk_C )
        | ( v5_pre_topc @ ( k10_tmap_1 @ X0 @ sk_D_1 @ X1 @ sk_C @ X2 @ sk_F ) @ ( k1_tsep_1 @ X0 @ X1 @ sk_C ) @ sk_D_1 )
        | ~ ( m1_pre_topc @ sk_C @ X0 )
        | ( v2_struct_0 @ sk_C )
        | ~ ( l1_pre_topc @ sk_D_1 )
        | ( v2_struct_0 @ sk_D_1 ) )
   <= ( ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v5_pre_topc @ sk_F @ sk_C @ sk_D_1 )
      & ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v1_funct_1 @ sk_F )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['109','119'])).

thf('121',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( v2_struct_0 @ sk_D_1 )
        | ( v2_struct_0 @ sk_C )
        | ~ ( m1_pre_topc @ sk_C @ X0 )
        | ( v5_pre_topc @ ( k10_tmap_1 @ X0 @ sk_D_1 @ X1 @ sk_C @ X2 @ sk_F ) @ ( k1_tsep_1 @ X0 @ X1 @ sk_C ) @ sk_D_1 )
        | ~ ( r4_tsep_1 @ X0 @ X1 @ sk_C )
        | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
        | ~ ( v5_pre_topc @ X2 @ X1 @ sk_D_1 )
        | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_D_1 ) )
        | ~ ( v1_funct_1 @ X2 )
        | ~ ( r1_tsep_1 @ X1 @ sk_C )
        | ~ ( m1_pre_topc @ X1 @ X0 )
        | ( v2_struct_0 @ X1 )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 ) )
   <= ( ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v5_pre_topc @ sk_F @ sk_C @ sk_D_1 )
      & ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v1_funct_1 @ sk_F )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['108','120'])).

thf('122',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ( v2_struct_0 @ sk_B )
        | ~ ( m1_pre_topc @ sk_B @ X0 )
        | ~ ( r1_tsep_1 @ sk_B @ sk_C )
        | ~ ( v1_funct_1 @ sk_E_1 )
        | ~ ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
        | ~ ( v5_pre_topc @ sk_E_1 @ sk_B @ sk_D_1 )
        | ~ ( r4_tsep_1 @ X0 @ sk_B @ sk_C )
        | ( v5_pre_topc @ ( k10_tmap_1 @ X0 @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( k1_tsep_1 @ X0 @ sk_B @ sk_C ) @ sk_D_1 )
        | ~ ( m1_pre_topc @ sk_C @ X0 )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_D_1 ) )
   <= ( ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v5_pre_topc @ sk_F @ sk_C @ sk_D_1 )
      & ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v1_funct_1 @ sk_F )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['107','121'])).

thf('123',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_D_1 )
        | ( v2_struct_0 @ sk_C )
        | ~ ( m1_pre_topc @ sk_C @ X0 )
        | ( v5_pre_topc @ ( k10_tmap_1 @ X0 @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( k1_tsep_1 @ X0 @ sk_B @ sk_C ) @ sk_D_1 )
        | ~ ( r4_tsep_1 @ X0 @ sk_B @ sk_C )
        | ~ ( v5_pre_topc @ sk_E_1 @ sk_B @ sk_D_1 )
        | ~ ( v1_funct_1 @ sk_E_1 )
        | ~ ( r1_tsep_1 @ sk_B @ sk_C )
        | ~ ( m1_pre_topc @ sk_B @ X0 )
        | ( v2_struct_0 @ sk_B )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 ) )
   <= ( ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v5_pre_topc @ sk_F @ sk_C @ sk_D_1 )
      & ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v1_funct_1 @ sk_F )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['106','122'])).

thf('124',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ( v2_struct_0 @ sk_B )
        | ~ ( m1_pre_topc @ sk_B @ X0 )
        | ~ ( r1_tsep_1 @ sk_B @ sk_C )
        | ~ ( v1_funct_1 @ sk_E_1 )
        | ~ ( r4_tsep_1 @ X0 @ sk_B @ sk_C )
        | ( v5_pre_topc @ ( k10_tmap_1 @ X0 @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( k1_tsep_1 @ X0 @ sk_B @ sk_C ) @ sk_D_1 )
        | ~ ( m1_pre_topc @ sk_C @ X0 )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_D_1 ) )
   <= ( ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v5_pre_topc @ sk_E_1 @ sk_B @ sk_D_1 )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v5_pre_topc @ sk_F @ sk_C @ sk_D_1 )
      & ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v1_funct_1 @ sk_F )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['105','123'])).

thf('125',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_D_1 )
        | ( v2_struct_0 @ sk_C )
        | ~ ( m1_pre_topc @ sk_C @ X0 )
        | ( v5_pre_topc @ ( k10_tmap_1 @ X0 @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( k1_tsep_1 @ X0 @ sk_B @ sk_C ) @ sk_D_1 )
        | ~ ( r4_tsep_1 @ X0 @ sk_B @ sk_C )
        | ~ ( v1_funct_1 @ sk_E_1 )
        | ~ ( m1_pre_topc @ sk_B @ X0 )
        | ( v2_struct_0 @ sk_B )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 ) )
   <= ( ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v5_pre_topc @ sk_E_1 @ sk_B @ sk_D_1 )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v5_pre_topc @ sk_F @ sk_C @ sk_D_1 )
      & ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v1_funct_1 @ sk_F )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['103','124'])).

thf('126',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( m1_pre_topc @ sk_B @ X0 )
        | ~ ( v1_funct_1 @ sk_E_1 )
        | ~ ( r4_tsep_1 @ X0 @ sk_B @ sk_C )
        | ( v5_pre_topc @ ( k10_tmap_1 @ X0 @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( k1_tsep_1 @ X0 @ sk_B @ sk_C ) @ sk_D_1 )
        | ~ ( m1_pre_topc @ sk_C @ X0 )
        | ( v2_struct_0 @ sk_D_1 )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_B ) )
   <= ( ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v5_pre_topc @ sk_E_1 @ sk_B @ sk_D_1 )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v5_pre_topc @ sk_F @ sk_C @ sk_D_1 )
      & ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v1_funct_1 @ sk_F )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference(simplify,[status(thm)],['125'])).

thf('127',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_D_1 )
        | ~ ( m1_pre_topc @ sk_C @ X0 )
        | ( v5_pre_topc @ ( k10_tmap_1 @ X0 @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( k1_tsep_1 @ X0 @ sk_B @ sk_C ) @ sk_D_1 )
        | ~ ( r4_tsep_1 @ X0 @ sk_B @ sk_C )
        | ~ ( m1_pre_topc @ sk_B @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 ) )
   <= ( ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      & ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v5_pre_topc @ sk_E_1 @ sk_B @ sk_D_1 )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v5_pre_topc @ sk_F @ sk_C @ sk_D_1 )
      & ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v1_funct_1 @ sk_F )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['102','126'])).

thf('128',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ sk_B @ sk_A )
      | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D_1 )
      | ~ ( m1_pre_topc @ sk_C @ sk_A )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      & ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v5_pre_topc @ sk_E_1 @ sk_B @ sk_D_1 )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v5_pre_topc @ sk_F @ sk_C @ sk_D_1 )
      & ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v1_funct_1 @ sk_F )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['101','127'])).

thf('129',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D_1 )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      & ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v5_pre_topc @ sk_E_1 @ sk_B @ sk_D_1 )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v5_pre_topc @ sk_F @ sk_C @ sk_D_1 )
      & ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v1_funct_1 @ sk_F )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['128','129','130','131','132'])).

thf('134',plain,
    ( ( ( v2_struct_0 @ sk_D_1 )
      | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      & ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v5_pre_topc @ sk_E_1 @ sk_B @ sk_D_1 )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v5_pre_topc @ sk_F @ sk_C @ sk_D_1 )
      & ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v1_funct_1 @ sk_F )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference(simplify,[status(thm)],['133'])).

thf('135',plain,
    ( ~ ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D_1 )
   <= ~ ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D_1 ) ),
    inference(split,[status(esa)],['49'])).

thf('136',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D_1 ) )
   <= ( ~ ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D_1 )
      & ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      & ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v5_pre_topc @ sk_E_1 @ sk_B @ sk_D_1 )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v5_pre_topc @ sk_F @ sk_C @ sk_D_1 )
      & ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v1_funct_1 @ sk_F )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,
    ( ~ ( v2_struct_0 @ sk_D_1 )
   <= ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(split,[status(esa)],['52'])).

thf('138',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( v2_struct_0 @ sk_D_1 )
      & ~ ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D_1 )
      & ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      & ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v5_pre_topc @ sk_E_1 @ sk_B @ sk_D_1 )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v5_pre_topc @ sk_F @ sk_C @ sk_D_1 )
      & ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v1_funct_1 @ sk_F )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ~ ( v2_struct_0 @ sk_D_1 )
      & ~ ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D_1 )
      & ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      & ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v5_pre_topc @ sk_E_1 @ sk_B @ sk_D_1 )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v5_pre_topc @ sk_F @ sk_C @ sk_D_1 )
      & ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v1_funct_1 @ sk_F )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference(clc,[status(thm)],['138','139'])).

thf('141',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,
    ( ( v2_struct_0 @ sk_C )
   <= ( ~ ( v2_struct_0 @ sk_D_1 )
      & ~ ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D_1 )
      & ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      & ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v5_pre_topc @ sk_E_1 @ sk_B @ sk_D_1 )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v5_pre_topc @ sk_F @ sk_C @ sk_D_1 )
      & ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v1_funct_1 @ sk_F )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference(clc,[status(thm)],['140','141'])).

thf('143',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,
    ( ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D_1 )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ~ ( v2_pre_topc @ sk_D_1 )
    | ~ ( l1_pre_topc @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_F )
    | ~ ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ~ ( v5_pre_topc @ sk_F @ sk_C @ sk_D_1 )
    | ~ ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
    | ~ ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
    | ~ ( v5_pre_topc @ sk_E_1 @ sk_B @ sk_D_1 )
    | ~ ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ~ ( v1_funct_1 @ sk_E_1 )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,
    ( ( v2_pre_topc @ sk_D_1 )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['28'])).

thf('146',plain,
    ( ( l1_pre_topc @ sk_D_1 )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['26'])).

thf('147',plain,
    ( ( v1_funct_1 @ sk_F )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['20'])).

thf('148',plain,
    ( ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['22'])).

thf('149',plain,
    ( ( v5_pre_topc @ sk_F @ sk_C @ sk_D_1 )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['111'])).

thf('150',plain,
    ( ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['24'])).

thf('151',plain,
    ( ( v5_pre_topc @ sk_E_1 @ sk_B @ sk_D_1 )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['104'])).

thf('152',plain,
    ( ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['31'])).

thf('153',plain,
    ( ( v1_funct_1 @ sk_E_1 )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['10'])).

thf('154',plain,
    ( ~ ( v2_struct_0 @ sk_D_1 )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['52'])).

thf('155',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_C )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('156',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v2_struct_0 @ X10 )
      | ~ ( m1_pre_topc @ X10 @ X11 )
      | ~ ( r1_tsep_1 @ X10 @ X12 )
      | ( v1_funct_1 @ ( sk_E @ X12 @ X10 @ X11 ) )
      | ( r3_tsep_1 @ X11 @ X10 @ X12 )
      | ~ ( m1_pre_topc @ X12 @ X11 )
      | ( v2_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t135_tmap_1])).

thf('159',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_B @ X0 )
      | ( v1_funct_1 @ ( sk_E @ X0 @ sk_B @ sk_A ) )
      | ~ ( r1_tsep_1 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_B @ X0 )
      | ( v1_funct_1 @ ( sk_E @ X0 @ sk_B @ sk_A ) )
      | ~ ( r1_tsep_1 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['159','160','161'])).

thf('163',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v1_funct_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
    | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['156','162'])).

thf('164',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v1_funct_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['155','163'])).

thf('165',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_C )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('167',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v2_struct_0 @ X10 )
      | ~ ( m1_pre_topc @ X10 @ X11 )
      | ~ ( r1_tsep_1 @ X10 @ X12 )
      | ( v1_funct_1 @ ( k3_tmap_1 @ X11 @ ( sk_D @ X12 @ X10 @ X11 ) @ ( k1_tsep_1 @ X11 @ X10 @ X12 ) @ X12 @ ( sk_E @ X12 @ X10 @ X11 ) ) )
      | ( r3_tsep_1 @ X11 @ X10 @ X12 )
      | ~ ( m1_pre_topc @ X12 @ X11 )
      | ( v2_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t135_tmap_1])).

thf('170',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_B @ X0 )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) @ X0 @ ( sk_E @ X0 @ sk_B @ sk_A ) ) )
      | ~ ( r1_tsep_1 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['168','169'])).

thf('171',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_B @ X0 )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) @ X0 @ ( sk_E @ X0 @ sk_B @ sk_A ) ) )
      | ~ ( r1_tsep_1 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['170','171','172'])).

thf('174',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
    | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['167','173'])).

thf('175',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['166','174'])).

thf('176',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_C )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('177',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v2_struct_0 @ X10 )
      | ~ ( m1_pre_topc @ X10 @ X11 )
      | ~ ( r1_tsep_1 @ X10 @ X12 )
      | ( v1_funct_2 @ ( k3_tmap_1 @ X11 @ ( sk_D @ X12 @ X10 @ X11 ) @ ( k1_tsep_1 @ X11 @ X10 @ X12 ) @ X12 @ ( sk_E @ X12 @ X10 @ X11 ) ) @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ ( sk_D @ X12 @ X10 @ X11 ) ) )
      | ( r3_tsep_1 @ X11 @ X10 @ X12 )
      | ~ ( m1_pre_topc @ X12 @ X11 )
      | ( v2_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t135_tmap_1])).

thf('180',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_B @ X0 )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) @ X0 @ ( sk_E @ X0 @ sk_B @ sk_A ) ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ X0 @ sk_B @ sk_A ) ) )
      | ~ ( r1_tsep_1 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['178','179'])).

thf('181',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_B @ X0 )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) @ X0 @ ( sk_E @ X0 @ sk_B @ sk_A ) ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ X0 @ sk_B @ sk_A ) ) )
      | ~ ( r1_tsep_1 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['180','181','182'])).

thf('184',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
    | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['177','183'])).

thf('185',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['176','184'])).

thf('186',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_C )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('187',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v2_struct_0 @ X10 )
      | ~ ( m1_pre_topc @ X10 @ X11 )
      | ~ ( r1_tsep_1 @ X10 @ X12 )
      | ( m1_subset_1 @ ( k3_tmap_1 @ X11 @ ( sk_D @ X12 @ X10 @ X11 ) @ ( k1_tsep_1 @ X11 @ X10 @ X12 ) @ X12 @ ( sk_E @ X12 @ X10 @ X11 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ ( sk_D @ X12 @ X10 @ X11 ) ) ) ) )
      | ( r3_tsep_1 @ X11 @ X10 @ X12 )
      | ~ ( m1_pre_topc @ X12 @ X11 )
      | ( v2_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t135_tmap_1])).

thf('190',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_B @ X0 )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) @ X0 @ ( sk_E @ X0 @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ X0 @ sk_B @ sk_A ) ) ) ) )
      | ~ ( r1_tsep_1 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['188','189'])).

thf('191',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_B @ X0 )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) @ X0 @ ( sk_E @ X0 @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ X0 @ sk_B @ sk_A ) ) ) ) )
      | ~ ( r1_tsep_1 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['190','191','192'])).

thf('194',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
    | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['187','193'])).

thf('195',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['186','194'])).

thf('196',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_C )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('197',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v2_struct_0 @ X10 )
      | ~ ( m1_pre_topc @ X10 @ X11 )
      | ~ ( r1_tsep_1 @ X10 @ X12 )
      | ( v2_pre_topc @ ( sk_D @ X12 @ X10 @ X11 ) )
      | ( r3_tsep_1 @ X11 @ X10 @ X12 )
      | ~ ( m1_pre_topc @ X12 @ X11 )
      | ( v2_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t135_tmap_1])).

thf('200',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_B @ X0 )
      | ( v2_pre_topc @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r1_tsep_1 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['198','199'])).

thf('201',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('202',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('203',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_B @ X0 )
      | ( v2_pre_topc @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r1_tsep_1 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['200','201','202'])).

thf('204',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['197','203'])).

thf('205',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['196','204'])).

thf('206',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_C )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('207',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('209',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v2_struct_0 @ X10 )
      | ~ ( m1_pre_topc @ X10 @ X11 )
      | ~ ( r1_tsep_1 @ X10 @ X12 )
      | ( l1_pre_topc @ ( sk_D @ X12 @ X10 @ X11 ) )
      | ( r3_tsep_1 @ X11 @ X10 @ X12 )
      | ~ ( m1_pre_topc @ X12 @ X11 )
      | ( v2_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t135_tmap_1])).

thf('210',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_B @ X0 )
      | ( l1_pre_topc @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r1_tsep_1 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['208','209'])).

thf('211',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('212',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('213',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_B @ X0 )
      | ( l1_pre_topc @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r1_tsep_1 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['210','211','212'])).

thf('214',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ( l1_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['207','213'])).

thf('215',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( l1_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['206','214'])).

thf('216',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_C )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('217',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('218',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('219',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v2_struct_0 @ X10 )
      | ~ ( m1_pre_topc @ X10 @ X11 )
      | ~ ( r1_tsep_1 @ X10 @ X12 )
      | ( v1_funct_1 @ ( k3_tmap_1 @ X11 @ ( sk_D @ X12 @ X10 @ X11 ) @ ( k1_tsep_1 @ X11 @ X10 @ X12 ) @ X10 @ ( sk_E @ X12 @ X10 @ X11 ) ) )
      | ( r3_tsep_1 @ X11 @ X10 @ X12 )
      | ~ ( m1_pre_topc @ X12 @ X11 )
      | ( v2_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t135_tmap_1])).

thf('220',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_B @ X0 )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) @ sk_B @ ( sk_E @ X0 @ sk_B @ sk_A ) ) )
      | ~ ( r1_tsep_1 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['218','219'])).

thf('221',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('222',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('223',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_B @ X0 )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) @ sk_B @ ( sk_E @ X0 @ sk_B @ sk_A ) ) )
      | ~ ( r1_tsep_1 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['220','221','222'])).

thf('224',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
    | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['217','223'])).

thf('225',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['216','224'])).

thf('226',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_C )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('227',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('228',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('229',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v2_struct_0 @ X10 )
      | ~ ( m1_pre_topc @ X10 @ X11 )
      | ~ ( r1_tsep_1 @ X10 @ X12 )
      | ( v1_funct_2 @ ( k3_tmap_1 @ X11 @ ( sk_D @ X12 @ X10 @ X11 ) @ ( k1_tsep_1 @ X11 @ X10 @ X12 ) @ X10 @ ( sk_E @ X12 @ X10 @ X11 ) ) @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ ( sk_D @ X12 @ X10 @ X11 ) ) )
      | ( r3_tsep_1 @ X11 @ X10 @ X12 )
      | ~ ( m1_pre_topc @ X12 @ X11 )
      | ( v2_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t135_tmap_1])).

thf('230',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_B @ X0 )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) @ sk_B @ ( sk_E @ X0 @ sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ X0 @ sk_B @ sk_A ) ) )
      | ~ ( r1_tsep_1 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['228','229'])).

thf('231',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('232',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('233',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_B @ X0 )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) @ sk_B @ ( sk_E @ X0 @ sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ X0 @ sk_B @ sk_A ) ) )
      | ~ ( r1_tsep_1 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['230','231','232'])).

thf('234',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
    | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['227','233'])).

thf('235',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['226','234'])).

thf('236',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_C )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('237',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('238',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('239',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v2_struct_0 @ X10 )
      | ~ ( m1_pre_topc @ X10 @ X11 )
      | ~ ( r1_tsep_1 @ X10 @ X12 )
      | ( m1_subset_1 @ ( k3_tmap_1 @ X11 @ ( sk_D @ X12 @ X10 @ X11 ) @ ( k1_tsep_1 @ X11 @ X10 @ X12 ) @ X10 @ ( sk_E @ X12 @ X10 @ X11 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ ( sk_D @ X12 @ X10 @ X11 ) ) ) ) )
      | ( r3_tsep_1 @ X11 @ X10 @ X12 )
      | ~ ( m1_pre_topc @ X12 @ X11 )
      | ( v2_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t135_tmap_1])).

thf('240',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_B @ X0 )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) @ sk_B @ ( sk_E @ X0 @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ X0 @ sk_B @ sk_A ) ) ) ) )
      | ~ ( r1_tsep_1 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['238','239'])).

thf('241',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('242',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('243',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_B @ X0 )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) @ sk_B @ ( sk_E @ X0 @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ X0 @ sk_B @ sk_A ) ) ) ) )
      | ~ ( r1_tsep_1 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['240','241','242'])).

thf('244',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
    | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['237','243'])).

thf('245',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['236','244'])).

thf('246',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X5 ) @ ( u1_struct_0 @ X6 ) ) ) )
      | ~ ( v1_funct_2 @ X4 @ ( u1_struct_0 @ X5 ) @ ( u1_struct_0 @ X6 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( m1_pre_topc @ X7 @ X8 )
      | ( v2_struct_0 @ X7 )
      | ~ ( m1_pre_topc @ X5 @ X8 )
      | ( v2_struct_0 @ X5 )
      | ~ ( l1_pre_topc @ X6 )
      | ~ ( v2_pre_topc @ X6 )
      | ( v2_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 )
      | ( v2_struct_0 @ X8 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_funct_2 @ X9 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X6 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X6 ) ) ) )
      | ( v1_funct_1 @ ( k10_tmap_1 @ X8 @ X6 @ X5 @ X7 @ X4 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k10_tmap_1])).

thf('247',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( v1_funct_1 @ ( k10_tmap_1 @ X2 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ X1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( v1_funct_1 @ X0 )
        | ( v2_struct_0 @ X2 )
        | ~ ( v2_pre_topc @ X2 )
        | ~ ( l1_pre_topc @ X2 )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( l1_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ sk_B )
        | ~ ( m1_pre_topc @ sk_B @ X2 )
        | ( v2_struct_0 @ X1 )
        | ~ ( m1_pre_topc @ X1 @ X2 )
        | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['245','246'])).

thf('248',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( m1_pre_topc @ X1 @ X2 )
        | ( v2_struct_0 @ X1 )
        | ~ ( m1_pre_topc @ sk_B @ X2 )
        | ~ ( l1_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( l1_pre_topc @ X2 )
        | ~ ( v2_pre_topc @ X2 )
        | ( v2_struct_0 @ X2 )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ( v1_funct_1 @ ( k10_tmap_1 @ X2 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ X1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ X0 ) )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['247'])).

thf('249',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( v1_funct_1 @ ( k10_tmap_1 @ X2 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ X1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( v1_funct_1 @ X0 )
        | ( v2_struct_0 @ X2 )
        | ~ ( v2_pre_topc @ X2 )
        | ~ ( l1_pre_topc @ X2 )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( l1_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( m1_pre_topc @ sk_B @ X2 )
        | ( v2_struct_0 @ X1 )
        | ~ ( m1_pre_topc @ X1 @ X2 )
        | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['235','248'])).

thf('250',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( m1_pre_topc @ X1 @ X2 )
        | ( v2_struct_0 @ X1 )
        | ~ ( m1_pre_topc @ sk_B @ X2 )
        | ~ ( l1_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( l1_pre_topc @ X2 )
        | ~ ( v2_pre_topc @ X2 )
        | ( v2_struct_0 @ X2 )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ( v1_funct_1 @ ( k10_tmap_1 @ X2 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ X1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ X0 ) )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['249'])).

thf('251',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( v1_funct_1 @ ( k10_tmap_1 @ X2 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ X1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( v1_funct_1 @ X0 )
        | ( v2_struct_0 @ X2 )
        | ~ ( v2_pre_topc @ X2 )
        | ~ ( l1_pre_topc @ X2 )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( l1_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( m1_pre_topc @ sk_B @ X2 )
        | ( v2_struct_0 @ X1 )
        | ~ ( m1_pre_topc @ X1 @ X2 ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['225','250'])).

thf('252',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ~ ( m1_pre_topc @ X1 @ X2 )
        | ( v2_struct_0 @ X1 )
        | ~ ( m1_pre_topc @ sk_B @ X2 )
        | ~ ( l1_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( l1_pre_topc @ X2 )
        | ~ ( v2_pre_topc @ X2 )
        | ( v2_struct_0 @ X2 )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ( v1_funct_1 @ ( k10_tmap_1 @ X2 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ X1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ X0 ) )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['251'])).

thf('253',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( v1_funct_1 @ ( k10_tmap_1 @ X2 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ X1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( v1_funct_1 @ X0 )
        | ( v2_struct_0 @ X2 )
        | ~ ( v2_pre_topc @ X2 )
        | ~ ( l1_pre_topc @ X2 )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( m1_pre_topc @ sk_B @ X2 )
        | ( v2_struct_0 @ X1 )
        | ~ ( m1_pre_topc @ X1 @ X2 ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['215','252'])).

thf('254',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ~ ( m1_pre_topc @ X1 @ X2 )
        | ( v2_struct_0 @ X1 )
        | ~ ( m1_pre_topc @ sk_B @ X2 )
        | ~ ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( l1_pre_topc @ X2 )
        | ~ ( v2_pre_topc @ X2 )
        | ( v2_struct_0 @ X2 )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ( v1_funct_1 @ ( k10_tmap_1 @ X2 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ X1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ X0 ) )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['253'])).

thf('255',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( v1_funct_1 @ ( k10_tmap_1 @ X2 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ X1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( v1_funct_1 @ X0 )
        | ( v2_struct_0 @ X2 )
        | ~ ( v2_pre_topc @ X2 )
        | ~ ( l1_pre_topc @ X2 )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( m1_pre_topc @ sk_B @ X2 )
        | ( v2_struct_0 @ X1 )
        | ~ ( m1_pre_topc @ X1 @ X2 ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['205','254'])).

thf('256',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ~ ( m1_pre_topc @ X1 @ X2 )
        | ( v2_struct_0 @ X1 )
        | ~ ( m1_pre_topc @ sk_B @ X2 )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( l1_pre_topc @ X2 )
        | ~ ( v2_pre_topc @ X2 )
        | ( v2_struct_0 @ X2 )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ( v1_funct_1 @ ( k10_tmap_1 @ X2 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ X1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ X0 ) )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['255'])).

thf('257',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( v1_funct_1 @ ( k10_tmap_1 @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) )
        | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( m1_pre_topc @ sk_B @ X0 )
        | ( v2_struct_0 @ sk_C )
        | ~ ( m1_pre_topc @ sk_C @ X0 ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['195','256'])).

thf('258',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_pre_topc @ sk_C @ X0 )
        | ~ ( m1_pre_topc @ sk_B @ X0 )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 )
        | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ( v1_funct_1 @ ( k10_tmap_1 @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['257'])).

thf('259',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( v1_funct_1 @ ( k10_tmap_1 @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) )
        | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( m1_pre_topc @ sk_B @ X0 )
        | ~ ( m1_pre_topc @ sk_C @ X0 ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['185','258'])).

thf('260',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_pre_topc @ sk_C @ X0 )
        | ~ ( m1_pre_topc @ sk_B @ X0 )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 )
        | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
        | ( v1_funct_1 @ ( k10_tmap_1 @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['259'])).

thf('261',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( v1_funct_1 @ ( k10_tmap_1 @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) )
        | ( v2_struct_0 @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( m1_pre_topc @ sk_B @ X0 )
        | ~ ( m1_pre_topc @ sk_C @ X0 ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['175','260'])).

thf('262',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_pre_topc @ sk_C @ X0 )
        | ~ ( m1_pre_topc @ sk_B @ X0 )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 )
        | ( v1_funct_1 @ ( k10_tmap_1 @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['261'])).

thf('263',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( m1_pre_topc @ sk_B @ sk_A ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['165','262'])).

thf('264',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('265',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('266',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('267',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['263','264','265','266'])).

thf('268',plain,
    ( ( ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['267'])).

thf('269',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('270',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['166','174'])).

thf('271',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['176','184'])).

thf('272',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['186','194'])).

thf('273',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['196','204'])).

thf('274',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( l1_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['206','214'])).

thf('275',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['216','224'])).

thf('276',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['226','234'])).

thf('277',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['236','244'])).

thf('278',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X5 ) @ ( u1_struct_0 @ X6 ) ) ) )
      | ~ ( v1_funct_2 @ X4 @ ( u1_struct_0 @ X5 ) @ ( u1_struct_0 @ X6 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( m1_pre_topc @ X7 @ X8 )
      | ( v2_struct_0 @ X7 )
      | ~ ( m1_pre_topc @ X5 @ X8 )
      | ( v2_struct_0 @ X5 )
      | ~ ( l1_pre_topc @ X6 )
      | ~ ( v2_pre_topc @ X6 )
      | ( v2_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 )
      | ( v2_struct_0 @ X8 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_funct_2 @ X9 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X6 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X6 ) ) ) )
      | ( v1_funct_2 @ ( k10_tmap_1 @ X8 @ X6 @ X5 @ X7 @ X4 @ X9 ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X8 @ X5 @ X7 ) ) @ ( u1_struct_0 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k10_tmap_1])).

thf('279',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( v1_funct_2 @ ( k10_tmap_1 @ X1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ X0 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ X2 ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X1 @ sk_B @ X0 ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( v1_funct_1 @ X2 )
        | ( v2_struct_0 @ X1 )
        | ~ ( v2_pre_topc @ X1 )
        | ~ ( l1_pre_topc @ X1 )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( l1_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ sk_B )
        | ~ ( m1_pre_topc @ sk_B @ X1 )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ X0 @ X1 )
        | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['277','278'])).

thf('280',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( m1_pre_topc @ X0 @ X1 )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ sk_B @ X1 )
        | ~ ( l1_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( l1_pre_topc @ X1 )
        | ~ ( v2_pre_topc @ X1 )
        | ( v2_struct_0 @ X1 )
        | ~ ( v1_funct_1 @ X2 )
        | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ( v1_funct_2 @ ( k10_tmap_1 @ X1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ X0 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ X2 ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X1 @ sk_B @ X0 ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['279'])).

thf('281',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( v1_funct_2 @ ( k10_tmap_1 @ X1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ X0 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ X2 ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X1 @ sk_B @ X0 ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( v1_funct_1 @ X2 )
        | ( v2_struct_0 @ X1 )
        | ~ ( v2_pre_topc @ X1 )
        | ~ ( l1_pre_topc @ X1 )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( l1_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( m1_pre_topc @ sk_B @ X1 )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ X0 @ X1 )
        | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['276','280'])).

thf('282',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( m1_pre_topc @ X0 @ X1 )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ sk_B @ X1 )
        | ~ ( l1_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( l1_pre_topc @ X1 )
        | ~ ( v2_pre_topc @ X1 )
        | ( v2_struct_0 @ X1 )
        | ~ ( v1_funct_1 @ X2 )
        | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ( v1_funct_2 @ ( k10_tmap_1 @ X1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ X0 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ X2 ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X1 @ sk_B @ X0 ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['281'])).

thf('283',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( v1_funct_2 @ ( k10_tmap_1 @ X1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ X0 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ X2 ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X1 @ sk_B @ X0 ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( v1_funct_1 @ X2 )
        | ( v2_struct_0 @ X1 )
        | ~ ( v2_pre_topc @ X1 )
        | ~ ( l1_pre_topc @ X1 )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( l1_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( m1_pre_topc @ sk_B @ X1 )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ X0 @ X1 ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['275','282'])).

thf('284',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ~ ( m1_pre_topc @ X0 @ X1 )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ sk_B @ X1 )
        | ~ ( l1_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( l1_pre_topc @ X1 )
        | ~ ( v2_pre_topc @ X1 )
        | ( v2_struct_0 @ X1 )
        | ~ ( v1_funct_1 @ X2 )
        | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ( v1_funct_2 @ ( k10_tmap_1 @ X1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ X0 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ X2 ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X1 @ sk_B @ X0 ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['283'])).

thf('285',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( v1_funct_2 @ ( k10_tmap_1 @ X1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ X0 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ X2 ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X1 @ sk_B @ X0 ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( v1_funct_1 @ X2 )
        | ( v2_struct_0 @ X1 )
        | ~ ( v2_pre_topc @ X1 )
        | ~ ( l1_pre_topc @ X1 )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( m1_pre_topc @ sk_B @ X1 )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ X0 @ X1 ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['274','284'])).

thf('286',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ~ ( m1_pre_topc @ X0 @ X1 )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ sk_B @ X1 )
        | ~ ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( l1_pre_topc @ X1 )
        | ~ ( v2_pre_topc @ X1 )
        | ( v2_struct_0 @ X1 )
        | ~ ( v1_funct_1 @ X2 )
        | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ( v1_funct_2 @ ( k10_tmap_1 @ X1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ X0 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ X2 ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X1 @ sk_B @ X0 ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['285'])).

thf('287',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( v1_funct_2 @ ( k10_tmap_1 @ X1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ X0 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ X2 ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X1 @ sk_B @ X0 ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( v1_funct_1 @ X2 )
        | ( v2_struct_0 @ X1 )
        | ~ ( v2_pre_topc @ X1 )
        | ~ ( l1_pre_topc @ X1 )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( m1_pre_topc @ sk_B @ X1 )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ X0 @ X1 ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['273','286'])).

thf('288',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ~ ( m1_pre_topc @ X0 @ X1 )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ sk_B @ X1 )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( l1_pre_topc @ X1 )
        | ~ ( v2_pre_topc @ X1 )
        | ( v2_struct_0 @ X1 )
        | ~ ( v1_funct_1 @ X2 )
        | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ( v1_funct_2 @ ( k10_tmap_1 @ X1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ X0 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ X2 ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X1 @ sk_B @ X0 ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['287'])).

thf('289',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( v1_funct_2 @ ( k10_tmap_1 @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X0 @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( m1_pre_topc @ sk_B @ X0 )
        | ( v2_struct_0 @ sk_C )
        | ~ ( m1_pre_topc @ sk_C @ X0 ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['272','288'])).

thf('290',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_pre_topc @ sk_C @ X0 )
        | ~ ( m1_pre_topc @ sk_B @ X0 )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 )
        | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ( v1_funct_2 @ ( k10_tmap_1 @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X0 @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['289'])).

thf('291',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( v1_funct_2 @ ( k10_tmap_1 @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X0 @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( m1_pre_topc @ sk_B @ X0 )
        | ~ ( m1_pre_topc @ sk_C @ X0 ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['271','290'])).

thf('292',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_pre_topc @ sk_C @ X0 )
        | ~ ( m1_pre_topc @ sk_B @ X0 )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 )
        | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
        | ( v1_funct_2 @ ( k10_tmap_1 @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X0 @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['291'])).

thf('293',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( v1_funct_2 @ ( k10_tmap_1 @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X0 @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( m1_pre_topc @ sk_B @ X0 )
        | ~ ( m1_pre_topc @ sk_C @ X0 ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['270','292'])).

thf('294',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_pre_topc @ sk_C @ X0 )
        | ~ ( m1_pre_topc @ sk_B @ X0 )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 )
        | ( v1_funct_2 @ ( k10_tmap_1 @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X0 @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['293'])).

thf('295',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( m1_pre_topc @ sk_B @ sk_A ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['269','294'])).

thf('296',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('297',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('298',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('299',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['295','296','297','298'])).

thf('300',plain,
    ( ( ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['299'])).

thf('301',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('302',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['166','174'])).

thf('303',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['176','184'])).

thf('304',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['186','194'])).

thf('305',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['196','204'])).

thf('306',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( l1_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['206','214'])).

thf('307',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['216','224'])).

thf('308',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['226','234'])).

thf('309',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['236','244'])).

thf('310',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X5 ) @ ( u1_struct_0 @ X6 ) ) ) )
      | ~ ( v1_funct_2 @ X4 @ ( u1_struct_0 @ X5 ) @ ( u1_struct_0 @ X6 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( m1_pre_topc @ X7 @ X8 )
      | ( v2_struct_0 @ X7 )
      | ~ ( m1_pre_topc @ X5 @ X8 )
      | ( v2_struct_0 @ X5 )
      | ~ ( l1_pre_topc @ X6 )
      | ~ ( v2_pre_topc @ X6 )
      | ( v2_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 )
      | ( v2_struct_0 @ X8 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_funct_2 @ X9 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X6 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X6 ) ) ) )
      | ( m1_subset_1 @ ( k10_tmap_1 @ X8 @ X6 @ X5 @ X7 @ X4 @ X9 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X8 @ X5 @ X7 ) ) @ ( u1_struct_0 @ X6 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k10_tmap_1])).

thf('311',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( m1_subset_1 @ ( k10_tmap_1 @ X1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ X0 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ X2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X1 @ sk_B @ X0 ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( v1_funct_1 @ X2 )
        | ( v2_struct_0 @ X1 )
        | ~ ( v2_pre_topc @ X1 )
        | ~ ( l1_pre_topc @ X1 )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( l1_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ sk_B )
        | ~ ( m1_pre_topc @ sk_B @ X1 )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ X0 @ X1 )
        | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['309','310'])).

thf('312',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( m1_pre_topc @ X0 @ X1 )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ sk_B @ X1 )
        | ~ ( l1_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( l1_pre_topc @ X1 )
        | ~ ( v2_pre_topc @ X1 )
        | ( v2_struct_0 @ X1 )
        | ~ ( v1_funct_1 @ X2 )
        | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ( m1_subset_1 @ ( k10_tmap_1 @ X1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ X0 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ X2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X1 @ sk_B @ X0 ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['311'])).

thf('313',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( m1_subset_1 @ ( k10_tmap_1 @ X1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ X0 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ X2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X1 @ sk_B @ X0 ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( v1_funct_1 @ X2 )
        | ( v2_struct_0 @ X1 )
        | ~ ( v2_pre_topc @ X1 )
        | ~ ( l1_pre_topc @ X1 )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( l1_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( m1_pre_topc @ sk_B @ X1 )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ X0 @ X1 )
        | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['308','312'])).

thf('314',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( m1_pre_topc @ X0 @ X1 )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ sk_B @ X1 )
        | ~ ( l1_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( l1_pre_topc @ X1 )
        | ~ ( v2_pre_topc @ X1 )
        | ( v2_struct_0 @ X1 )
        | ~ ( v1_funct_1 @ X2 )
        | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ( m1_subset_1 @ ( k10_tmap_1 @ X1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ X0 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ X2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X1 @ sk_B @ X0 ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['313'])).

thf('315',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( m1_subset_1 @ ( k10_tmap_1 @ X1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ X0 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ X2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X1 @ sk_B @ X0 ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( v1_funct_1 @ X2 )
        | ( v2_struct_0 @ X1 )
        | ~ ( v2_pre_topc @ X1 )
        | ~ ( l1_pre_topc @ X1 )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( l1_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( m1_pre_topc @ sk_B @ X1 )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ X0 @ X1 ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['307','314'])).

thf('316',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ~ ( m1_pre_topc @ X0 @ X1 )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ sk_B @ X1 )
        | ~ ( l1_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( l1_pre_topc @ X1 )
        | ~ ( v2_pre_topc @ X1 )
        | ( v2_struct_0 @ X1 )
        | ~ ( v1_funct_1 @ X2 )
        | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ( m1_subset_1 @ ( k10_tmap_1 @ X1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ X0 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ X2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X1 @ sk_B @ X0 ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['315'])).

thf('317',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( m1_subset_1 @ ( k10_tmap_1 @ X1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ X0 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ X2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X1 @ sk_B @ X0 ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( v1_funct_1 @ X2 )
        | ( v2_struct_0 @ X1 )
        | ~ ( v2_pre_topc @ X1 )
        | ~ ( l1_pre_topc @ X1 )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( m1_pre_topc @ sk_B @ X1 )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ X0 @ X1 ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['306','316'])).

thf('318',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ~ ( m1_pre_topc @ X0 @ X1 )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ sk_B @ X1 )
        | ~ ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( l1_pre_topc @ X1 )
        | ~ ( v2_pre_topc @ X1 )
        | ( v2_struct_0 @ X1 )
        | ~ ( v1_funct_1 @ X2 )
        | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ( m1_subset_1 @ ( k10_tmap_1 @ X1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ X0 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ X2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X1 @ sk_B @ X0 ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['317'])).

thf('319',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( m1_subset_1 @ ( k10_tmap_1 @ X1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ X0 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ X2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X1 @ sk_B @ X0 ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( v1_funct_1 @ X2 )
        | ( v2_struct_0 @ X1 )
        | ~ ( v2_pre_topc @ X1 )
        | ~ ( l1_pre_topc @ X1 )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( m1_pre_topc @ sk_B @ X1 )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ X0 @ X1 ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['305','318'])).

thf('320',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ~ ( m1_pre_topc @ X0 @ X1 )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ sk_B @ X1 )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( l1_pre_topc @ X1 )
        | ~ ( v2_pre_topc @ X1 )
        | ( v2_struct_0 @ X1 )
        | ~ ( v1_funct_1 @ X2 )
        | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ( m1_subset_1 @ ( k10_tmap_1 @ X1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ X0 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ X2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X1 @ sk_B @ X0 ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['319'])).

thf('321',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( m1_subset_1 @ ( k10_tmap_1 @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X0 @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( m1_pre_topc @ sk_B @ X0 )
        | ( v2_struct_0 @ sk_C )
        | ~ ( m1_pre_topc @ sk_C @ X0 ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['304','320'])).

thf('322',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_pre_topc @ sk_C @ X0 )
        | ~ ( m1_pre_topc @ sk_B @ X0 )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 )
        | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ( m1_subset_1 @ ( k10_tmap_1 @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X0 @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['321'])).

thf('323',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( m1_subset_1 @ ( k10_tmap_1 @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X0 @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( m1_pre_topc @ sk_B @ X0 )
        | ~ ( m1_pre_topc @ sk_C @ X0 ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['303','322'])).

thf('324',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_pre_topc @ sk_C @ X0 )
        | ~ ( m1_pre_topc @ sk_B @ X0 )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 )
        | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
        | ( m1_subset_1 @ ( k10_tmap_1 @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X0 @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['323'])).

thf('325',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( m1_subset_1 @ ( k10_tmap_1 @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X0 @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ( v2_struct_0 @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( m1_pre_topc @ sk_B @ X0 )
        | ~ ( m1_pre_topc @ sk_C @ X0 ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['302','324'])).

thf('326',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_pre_topc @ sk_C @ X0 )
        | ~ ( m1_pre_topc @ sk_B @ X0 )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 )
        | ( m1_subset_1 @ ( k10_tmap_1 @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X0 @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['325'])).

thf('327',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( m1_pre_topc @ sk_B @ sk_A ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['301','326'])).

thf('328',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('329',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('330',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('331',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['327','328','329','330'])).

thf('332',plain,
    ( ( ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['331'])).

thf('333',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v1_funct_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['155','163'])).

thf('334',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( l1_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['206','214'])).

thf('335',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['196','204'])).

thf('336',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_C )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('337',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('338',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('339',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v2_struct_0 @ X10 )
      | ~ ( m1_pre_topc @ X10 @ X11 )
      | ~ ( r1_tsep_1 @ X10 @ X12 )
      | ( v1_funct_2 @ ( sk_E @ X12 @ X10 @ X11 ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X10 @ X12 ) ) @ ( u1_struct_0 @ ( sk_D @ X12 @ X10 @ X11 ) ) )
      | ( r3_tsep_1 @ X11 @ X10 @ X12 )
      | ~ ( m1_pre_topc @ X12 @ X11 )
      | ( v2_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t135_tmap_1])).

thf('340',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_B @ X0 )
      | ( v1_funct_2 @ ( sk_E @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) ) @ ( u1_struct_0 @ ( sk_D @ X0 @ sk_B @ sk_A ) ) )
      | ~ ( r1_tsep_1 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['338','339'])).

thf('341',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('342',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('343',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_B @ X0 )
      | ( v1_funct_2 @ ( sk_E @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) ) @ ( u1_struct_0 @ ( sk_D @ X0 @ sk_B @ sk_A ) ) )
      | ~ ( r1_tsep_1 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['340','341','342'])).

thf('344',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v1_funct_2 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
    | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['337','343'])).

thf('345',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v1_funct_2 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['336','344'])).

thf('346',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_C )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('347',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('348',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('349',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v2_struct_0 @ X10 )
      | ~ ( m1_pre_topc @ X10 @ X11 )
      | ~ ( r1_tsep_1 @ X10 @ X12 )
      | ( m1_subset_1 @ ( sk_E @ X12 @ X10 @ X11 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X10 @ X12 ) ) @ ( u1_struct_0 @ ( sk_D @ X12 @ X10 @ X11 ) ) ) ) )
      | ( r3_tsep_1 @ X11 @ X10 @ X12 )
      | ~ ( m1_pre_topc @ X12 @ X11 )
      | ( v2_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t135_tmap_1])).

thf('350',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_E @ X0 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) ) @ ( u1_struct_0 @ ( sk_D @ X0 @ sk_B @ sk_A ) ) ) ) )
      | ~ ( r1_tsep_1 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['348','349'])).

thf('351',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('352',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('353',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_E @ X0 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) ) @ ( u1_struct_0 @ ( sk_D @ X0 @ sk_B @ sk_A ) ) ) ) )
      | ~ ( r1_tsep_1 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['350','351','352'])).

thf('354',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ( m1_subset_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
    | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['347','353'])).

thf('355',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( m1_subset_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['346','354'])).

thf(t138_tmap_1,axiom,(
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
                & ( m1_pre_topc @ C @ A ) )
             => ! [D: $i] :
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( m1_pre_topc @ D @ A ) )
                 => ! [E: $i] :
                      ( ( ( v1_funct_1 @ E )
                        & ( v1_funct_2 @ E @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) ) ) ) )
                     => ( r2_funct_2 @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) @ E @ ( k10_tmap_1 @ A @ B @ C @ D @ ( k3_tmap_1 @ A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ C @ E ) @ ( k3_tmap_1 @ A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ D @ E ) ) ) ) ) ) ) ) )).

thf('356',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( v2_struct_0 @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ~ ( l1_pre_topc @ X15 )
      | ( v2_struct_0 @ X16 )
      | ~ ( m1_pre_topc @ X16 @ X17 )
      | ( r2_funct_2 @ ( u1_struct_0 @ ( k1_tsep_1 @ X17 @ X18 @ X16 ) ) @ ( u1_struct_0 @ X15 ) @ X19 @ ( k10_tmap_1 @ X17 @ X15 @ X18 @ X16 @ ( k3_tmap_1 @ X17 @ X15 @ ( k1_tsep_1 @ X17 @ X18 @ X16 ) @ X18 @ X19 ) @ ( k3_tmap_1 @ X17 @ X15 @ ( k1_tsep_1 @ X17 @ X18 @ X16 ) @ X16 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X17 @ X18 @ X16 ) ) @ ( u1_struct_0 @ X15 ) ) ) )
      | ~ ( v1_funct_2 @ X19 @ ( u1_struct_0 @ ( k1_tsep_1 @ X17 @ X18 @ X16 ) ) @ ( u1_struct_0 @ X15 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( m1_pre_topc @ X18 @ X17 )
      | ( v2_struct_0 @ X18 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t138_tmap_1])).

thf('357',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_funct_2 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) )
      | ~ ( m1_pre_topc @ sk_C @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( l1_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['355','356'])).

thf('358',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('359',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('360',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('361',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('362',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v1_funct_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_funct_2 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) )
      | ( v2_struct_0 @ sk_C )
      | ~ ( l1_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['357','358','359','360','361'])).

thf('363',plain,
    ( ( ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( l1_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) )
      | ~ ( v1_funct_2 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ~ ( v1_funct_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['362'])).

thf('364',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v1_funct_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) )
      | ~ ( l1_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['345','363'])).

thf('365',plain,
    ( ( ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( l1_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) )
      | ~ ( v1_funct_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['364'])).

thf('366',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v1_funct_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) )
      | ~ ( l1_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['335','365'])).

thf('367',plain,
    ( ( ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( l1_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) )
      | ~ ( v1_funct_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['366'])).

thf('368',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v1_funct_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['334','367'])).

thf('369',plain,
    ( ( ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) )
      | ~ ( v1_funct_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['368'])).

thf('370',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( r2_funct_2 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['333','369'])).

thf('371',plain,
    ( ( ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['370'])).

thf('372',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v1_funct_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['155','163'])).

thf('373',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v1_funct_2 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['336','344'])).

thf('374',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( m1_subset_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['346','354'])).

thf(redefinition_r2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_funct_2 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('375',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) )
      | ~ ( v1_funct_2 @ X0 @ X1 @ X2 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_funct_2 @ X3 @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) )
      | ( X0 = X3 )
      | ~ ( r2_funct_2 @ X1 @ X2 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('376',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ~ ( r2_funct_2 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ X0 )
        | ( ( sk_E @ sk_C @ sk_B @ sk_A )
          = X0 )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v1_funct_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v1_funct_2 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['374','375'])).

thf('377',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ~ ( v1_funct_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ( ( sk_E @ sk_C @ sk_B @ sk_A )
          = X0 )
        | ~ ( r2_funct_2 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ X0 )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['373','376'])).

thf('378',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_funct_2 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ X0 )
        | ( ( sk_E @ sk_C @ sk_B @ sk_A )
          = X0 )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v1_funct_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['377'])).

thf('379',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ( ( sk_E @ sk_C @ sk_B @ sk_A )
          = X0 )
        | ~ ( r2_funct_2 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ X0 ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['372','378'])).

thf('380',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_funct_2 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ X0 )
        | ( ( sk_E @ sk_C @ sk_B @ sk_A )
          = X0 )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( v1_funct_1 @ X0 )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['379'])).

thf('381',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) )
      | ~ ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ~ ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
      | ( ( sk_E @ sk_C @ sk_B @ sk_A )
        = ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['371','380'])).

thf('382',plain,
    ( ( ( ( sk_E @ sk_C @ sk_B @ sk_A )
        = ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) )
      | ~ ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
      | ~ ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ~ ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['381'])).

thf('383',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) )
      | ~ ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ( ( sk_E @ sk_C @ sk_B @ sk_A )
        = ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['332','382'])).

thf('384',plain,
    ( ( ( ( sk_E @ sk_C @ sk_B @ sk_A )
        = ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) )
      | ~ ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ~ ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['383'])).

thf('385',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) )
      | ( ( sk_E @ sk_C @ sk_B @ sk_A )
        = ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['300','384'])).

thf('386',plain,
    ( ( ( ( sk_E @ sk_C @ sk_B @ sk_A )
        = ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) )
      | ~ ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['385'])).

thf('387',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( ( sk_E @ sk_C @ sk_B @ sk_A )
        = ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['268','386'])).

thf('388',plain,
    ( ( ( ( sk_E @ sk_C @ sk_B @ sk_A )
        = ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['387'])).

thf('389',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['216','224'])).

thf('390',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_C )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('391',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('392',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('393',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v2_struct_0 @ X10 )
      | ~ ( m1_pre_topc @ X10 @ X11 )
      | ~ ( r1_tsep_1 @ X10 @ X12 )
      | ( v5_pre_topc @ ( k3_tmap_1 @ X11 @ ( sk_D @ X12 @ X10 @ X11 ) @ ( k1_tsep_1 @ X11 @ X10 @ X12 ) @ X10 @ ( sk_E @ X12 @ X10 @ X11 ) ) @ X10 @ ( sk_D @ X12 @ X10 @ X11 ) )
      | ( r3_tsep_1 @ X11 @ X10 @ X12 )
      | ~ ( m1_pre_topc @ X12 @ X11 )
      | ( v2_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t135_tmap_1])).

thf('394',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_B @ X0 )
      | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) @ sk_B @ ( sk_E @ X0 @ sk_B @ sk_A ) ) @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r1_tsep_1 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['392','393'])).

thf('395',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('396',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('397',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_B @ X0 )
      | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) @ sk_B @ ( sk_E @ X0 @ sk_B @ sk_A ) ) @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r1_tsep_1 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['394','395','396'])).

thf('398',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['391','397'])).

thf('399',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['390','398'])).

thf('400',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['226','234'])).

thf('401',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['236','244'])).

thf('402',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['196','204'])).

thf('403',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( l1_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['206','214'])).

thf('404',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['166','174'])).

thf('405',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_C )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('406',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('407',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('408',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v2_struct_0 @ X10 )
      | ~ ( m1_pre_topc @ X10 @ X11 )
      | ~ ( r1_tsep_1 @ X10 @ X12 )
      | ( v5_pre_topc @ ( k3_tmap_1 @ X11 @ ( sk_D @ X12 @ X10 @ X11 ) @ ( k1_tsep_1 @ X11 @ X10 @ X12 ) @ X12 @ ( sk_E @ X12 @ X10 @ X11 ) ) @ X12 @ ( sk_D @ X12 @ X10 @ X11 ) )
      | ( r3_tsep_1 @ X11 @ X10 @ X12 )
      | ~ ( m1_pre_topc @ X12 @ X11 )
      | ( v2_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t135_tmap_1])).

thf('409',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_B @ X0 )
      | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) @ X0 @ ( sk_E @ X0 @ sk_B @ sk_A ) ) @ X0 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r1_tsep_1 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['407','408'])).

thf('410',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('411',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('412',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_B @ X0 )
      | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) @ X0 @ ( sk_E @ X0 @ sk_B @ sk_A ) ) @ X0 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r1_tsep_1 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['409','410','411'])).

thf('413',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['406','412'])).

thf('414',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['405','413'])).

thf('415',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['176','184'])).

thf('416',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['186','194'])).

thf('417',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( v2_struct_0 @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_funct_2 @ X30 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X29 ) )
      | ~ ( v5_pre_topc @ X30 @ sk_C @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X29 ) ) ) )
      | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X29 @ sk_B @ sk_C @ X31 @ X30 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X29 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X29 ) ) ) )
      | ~ ( v5_pre_topc @ X31 @ sk_B @ X29 )
      | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X29 ) )
      | ~ ( v1_funct_1 @ X31 )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('418',plain,
    ( ! [X29: $i,X30: $i,X31: $i] :
        ( ( v2_struct_0 @ X29 )
        | ~ ( v2_pre_topc @ X29 )
        | ~ ( l1_pre_topc @ X29 )
        | ~ ( v1_funct_1 @ X30 )
        | ~ ( v1_funct_2 @ X30 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X29 ) )
        | ~ ( v5_pre_topc @ X30 @ sk_C @ X29 )
        | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X29 ) ) ) )
        | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X29 ) ) ) )
        | ~ ( v5_pre_topc @ X31 @ sk_B @ X29 )
        | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X29 ) )
        | ~ ( v1_funct_1 @ X31 )
        | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X29 @ sk_B @ sk_C @ X31 @ X30 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X29 ) )
   <= ! [X29: $i,X30: $i,X31: $i] :
        ( ( v2_struct_0 @ X29 )
        | ~ ( v2_pre_topc @ X29 )
        | ~ ( l1_pre_topc @ X29 )
        | ~ ( v1_funct_1 @ X30 )
        | ~ ( v1_funct_2 @ X30 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X29 ) )
        | ~ ( v5_pre_topc @ X30 @ sk_C @ X29 )
        | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X29 ) ) ) )
        | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X29 ) ) ) )
        | ~ ( v5_pre_topc @ X31 @ sk_B @ X29 )
        | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X29 ) )
        | ~ ( v1_funct_1 @ X31 )
        | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X29 @ sk_B @ sk_C @ X31 @ X30 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X29 ) ) ),
    inference(split,[status(esa)],['417'])).

thf('419',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ X0 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( v5_pre_topc @ X0 @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( l1_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X29: $i,X30: $i,X31: $i] :
          ( ( v2_struct_0 @ X29 )
          | ~ ( v2_pre_topc @ X29 )
          | ~ ( l1_pre_topc @ X29 )
          | ~ ( v1_funct_1 @ X30 )
          | ~ ( v1_funct_2 @ X30 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X29 ) )
          | ~ ( v5_pre_topc @ X30 @ sk_C @ X29 )
          | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X29 ) ) ) )
          | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X29 ) ) ) )
          | ~ ( v5_pre_topc @ X31 @ sk_B @ X29 )
          | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X29 ) )
          | ~ ( v1_funct_1 @ X31 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X29 @ sk_B @ sk_C @ X31 @ X30 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X29 ) ) ) ),
    inference('sup-',[status(thm)],['416','418'])).

thf('420',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( l1_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ~ ( v5_pre_topc @ X0 @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( v1_funct_1 @ X0 )
        | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ X0 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_B ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X29: $i,X30: $i,X31: $i] :
          ( ( v2_struct_0 @ X29 )
          | ~ ( v2_pre_topc @ X29 )
          | ~ ( l1_pre_topc @ X29 )
          | ~ ( v1_funct_1 @ X30 )
          | ~ ( v1_funct_2 @ X30 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X29 ) )
          | ~ ( v5_pre_topc @ X30 @ sk_C @ X29 )
          | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X29 ) ) ) )
          | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X29 ) ) ) )
          | ~ ( v5_pre_topc @ X31 @ sk_B @ X29 )
          | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X29 ) )
          | ~ ( v1_funct_1 @ X31 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X29 @ sk_B @ sk_C @ X31 @ X30 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X29 ) ) ) ),
    inference('sup-',[status(thm)],['415','419'])).

thf('421',plain,
    ( ! [X0: $i] :
        ( ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ X0 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( v5_pre_topc @ X0 @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( l1_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_B ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X29: $i,X30: $i,X31: $i] :
          ( ( v2_struct_0 @ X29 )
          | ~ ( v2_pre_topc @ X29 )
          | ~ ( l1_pre_topc @ X29 )
          | ~ ( v1_funct_1 @ X30 )
          | ~ ( v1_funct_2 @ X30 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X29 ) )
          | ~ ( v5_pre_topc @ X30 @ sk_C @ X29 )
          | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X29 ) ) ) )
          | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X29 ) ) ) )
          | ~ ( v5_pre_topc @ X31 @ sk_B @ X29 )
          | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X29 ) )
          | ~ ( v1_funct_1 @ X31 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X29 @ sk_B @ sk_C @ X31 @ X30 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X29 ) ) ) ),
    inference(simplify,[status(thm)],['420'])).

thf('422',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( l1_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ~ ( v5_pre_topc @ X0 @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( v1_funct_1 @ X0 )
        | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ X0 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X29: $i,X30: $i,X31: $i] :
          ( ( v2_struct_0 @ X29 )
          | ~ ( v2_pre_topc @ X29 )
          | ~ ( l1_pre_topc @ X29 )
          | ~ ( v1_funct_1 @ X30 )
          | ~ ( v1_funct_2 @ X30 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X29 ) )
          | ~ ( v5_pre_topc @ X30 @ sk_C @ X29 )
          | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X29 ) ) ) )
          | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X29 ) ) ) )
          | ~ ( v5_pre_topc @ X31 @ sk_B @ X29 )
          | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X29 ) )
          | ~ ( v1_funct_1 @ X31 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X29 @ sk_B @ sk_C @ X31 @ X30 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X29 ) ) ) ),
    inference('sup-',[status(thm)],['414','421'])).

thf('423',plain,
    ( ! [X0: $i] :
        ( ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ X0 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( v5_pre_topc @ X0 @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( l1_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_B ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X29: $i,X30: $i,X31: $i] :
          ( ( v2_struct_0 @ X29 )
          | ~ ( v2_pre_topc @ X29 )
          | ~ ( l1_pre_topc @ X29 )
          | ~ ( v1_funct_1 @ X30 )
          | ~ ( v1_funct_2 @ X30 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X29 ) )
          | ~ ( v5_pre_topc @ X30 @ sk_C @ X29 )
          | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X29 ) ) ) )
          | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X29 ) ) ) )
          | ~ ( v5_pre_topc @ X31 @ sk_B @ X29 )
          | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X29 ) )
          | ~ ( v1_funct_1 @ X31 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X29 @ sk_B @ sk_C @ X31 @ X30 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X29 ) ) ) ),
    inference(simplify,[status(thm)],['422'])).

thf('424',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( l1_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ~ ( v5_pre_topc @ X0 @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( v1_funct_1 @ X0 )
        | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ X0 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X29: $i,X30: $i,X31: $i] :
          ( ( v2_struct_0 @ X29 )
          | ~ ( v2_pre_topc @ X29 )
          | ~ ( l1_pre_topc @ X29 )
          | ~ ( v1_funct_1 @ X30 )
          | ~ ( v1_funct_2 @ X30 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X29 ) )
          | ~ ( v5_pre_topc @ X30 @ sk_C @ X29 )
          | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X29 ) ) ) )
          | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X29 ) ) ) )
          | ~ ( v5_pre_topc @ X31 @ sk_B @ X29 )
          | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X29 ) )
          | ~ ( v1_funct_1 @ X31 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X29 @ sk_B @ sk_C @ X31 @ X30 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X29 ) ) ) ),
    inference('sup-',[status(thm)],['404','423'])).

thf('425',plain,
    ( ! [X0: $i] :
        ( ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ X0 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( v5_pre_topc @ X0 @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ~ ( l1_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_B ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X29: $i,X30: $i,X31: $i] :
          ( ( v2_struct_0 @ X29 )
          | ~ ( v2_pre_topc @ X29 )
          | ~ ( l1_pre_topc @ X29 )
          | ~ ( v1_funct_1 @ X30 )
          | ~ ( v1_funct_2 @ X30 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X29 ) )
          | ~ ( v5_pre_topc @ X30 @ sk_C @ X29 )
          | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X29 ) ) ) )
          | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X29 ) ) ) )
          | ~ ( v5_pre_topc @ X31 @ sk_B @ X29 )
          | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X29 ) )
          | ~ ( v1_funct_1 @ X31 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X29 @ sk_B @ sk_C @ X31 @ X30 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X29 ) ) ) ),
    inference(simplify,[status(thm)],['424'])).

thf('426',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ~ ( v5_pre_topc @ X0 @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( v1_funct_1 @ X0 )
        | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ X0 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X29: $i,X30: $i,X31: $i] :
          ( ( v2_struct_0 @ X29 )
          | ~ ( v2_pre_topc @ X29 )
          | ~ ( l1_pre_topc @ X29 )
          | ~ ( v1_funct_1 @ X30 )
          | ~ ( v1_funct_2 @ X30 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X29 ) )
          | ~ ( v5_pre_topc @ X30 @ sk_C @ X29 )
          | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X29 ) ) ) )
          | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X29 ) ) ) )
          | ~ ( v5_pre_topc @ X31 @ sk_B @ X29 )
          | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X29 ) )
          | ~ ( v1_funct_1 @ X31 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X29 @ sk_B @ sk_C @ X31 @ X30 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X29 ) ) ) ),
    inference('sup-',[status(thm)],['403','425'])).

thf('427',plain,
    ( ! [X0: $i] :
        ( ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ X0 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( v5_pre_topc @ X0 @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ~ ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_B ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X29: $i,X30: $i,X31: $i] :
          ( ( v2_struct_0 @ X29 )
          | ~ ( v2_pre_topc @ X29 )
          | ~ ( l1_pre_topc @ X29 )
          | ~ ( v1_funct_1 @ X30 )
          | ~ ( v1_funct_2 @ X30 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X29 ) )
          | ~ ( v5_pre_topc @ X30 @ sk_C @ X29 )
          | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X29 ) ) ) )
          | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X29 ) ) ) )
          | ~ ( v5_pre_topc @ X31 @ sk_B @ X29 )
          | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X29 ) )
          | ~ ( v1_funct_1 @ X31 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X29 @ sk_B @ sk_C @ X31 @ X30 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X29 ) ) ) ),
    inference(simplify,[status(thm)],['426'])).

thf('428',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ~ ( v5_pre_topc @ X0 @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( v1_funct_1 @ X0 )
        | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ X0 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X29: $i,X30: $i,X31: $i] :
          ( ( v2_struct_0 @ X29 )
          | ~ ( v2_pre_topc @ X29 )
          | ~ ( l1_pre_topc @ X29 )
          | ~ ( v1_funct_1 @ X30 )
          | ~ ( v1_funct_2 @ X30 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X29 ) )
          | ~ ( v5_pre_topc @ X30 @ sk_C @ X29 )
          | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X29 ) ) ) )
          | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X29 ) ) ) )
          | ~ ( v5_pre_topc @ X31 @ sk_B @ X29 )
          | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X29 ) )
          | ~ ( v1_funct_1 @ X31 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X29 @ sk_B @ sk_C @ X31 @ X30 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X29 ) ) ) ),
    inference('sup-',[status(thm)],['402','427'])).

thf('429',plain,
    ( ! [X0: $i] :
        ( ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ X0 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( v5_pre_topc @ X0 @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_B ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X29: $i,X30: $i,X31: $i] :
          ( ( v2_struct_0 @ X29 )
          | ~ ( v2_pre_topc @ X29 )
          | ~ ( l1_pre_topc @ X29 )
          | ~ ( v1_funct_1 @ X30 )
          | ~ ( v1_funct_2 @ X30 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X29 ) )
          | ~ ( v5_pre_topc @ X30 @ sk_C @ X29 )
          | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X29 ) ) ) )
          | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X29 ) ) ) )
          | ~ ( v5_pre_topc @ X31 @ sk_B @ X29 )
          | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X29 ) )
          | ~ ( v1_funct_1 @ X31 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X29 @ sk_B @ sk_C @ X31 @ X30 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X29 ) ) ) ),
    inference(simplify,[status(thm)],['428'])).

thf('430',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
      | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X29: $i,X30: $i,X31: $i] :
          ( ( v2_struct_0 @ X29 )
          | ~ ( v2_pre_topc @ X29 )
          | ~ ( l1_pre_topc @ X29 )
          | ~ ( v1_funct_1 @ X30 )
          | ~ ( v1_funct_2 @ X30 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X29 ) )
          | ~ ( v5_pre_topc @ X30 @ sk_C @ X29 )
          | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X29 ) ) ) )
          | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X29 ) ) ) )
          | ~ ( v5_pre_topc @ X31 @ sk_B @ X29 )
          | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X29 ) )
          | ~ ( v1_funct_1 @ X31 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X29 @ sk_B @ sk_C @ X31 @ X30 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X29 ) ) ) ),
    inference('sup-',[status(thm)],['401','429'])).

thf('431',plain,
    ( ( ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X29: $i,X30: $i,X31: $i] :
          ( ( v2_struct_0 @ X29 )
          | ~ ( v2_pre_topc @ X29 )
          | ~ ( l1_pre_topc @ X29 )
          | ~ ( v1_funct_1 @ X30 )
          | ~ ( v1_funct_2 @ X30 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X29 ) )
          | ~ ( v5_pre_topc @ X30 @ sk_C @ X29 )
          | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X29 ) ) ) )
          | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X29 ) ) ) )
          | ~ ( v5_pre_topc @ X31 @ sk_B @ X29 )
          | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X29 ) )
          | ~ ( v1_funct_1 @ X31 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X29 @ sk_B @ sk_C @ X31 @ X30 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X29 ) ) ) ),
    inference(simplify,[status(thm)],['430'])).

thf('432',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
      | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X29: $i,X30: $i,X31: $i] :
          ( ( v2_struct_0 @ X29 )
          | ~ ( v2_pre_topc @ X29 )
          | ~ ( l1_pre_topc @ X29 )
          | ~ ( v1_funct_1 @ X30 )
          | ~ ( v1_funct_2 @ X30 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X29 ) )
          | ~ ( v5_pre_topc @ X30 @ sk_C @ X29 )
          | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X29 ) ) ) )
          | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X29 ) ) ) )
          | ~ ( v5_pre_topc @ X31 @ sk_B @ X29 )
          | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X29 ) )
          | ~ ( v1_funct_1 @ X31 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X29 @ sk_B @ sk_C @ X31 @ X30 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X29 ) ) ) ),
    inference('sup-',[status(thm)],['400','431'])).

thf('433',plain,
    ( ( ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
      | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X29: $i,X30: $i,X31: $i] :
          ( ( v2_struct_0 @ X29 )
          | ~ ( v2_pre_topc @ X29 )
          | ~ ( l1_pre_topc @ X29 )
          | ~ ( v1_funct_1 @ X30 )
          | ~ ( v1_funct_2 @ X30 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X29 ) )
          | ~ ( v5_pre_topc @ X30 @ sk_C @ X29 )
          | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X29 ) ) ) )
          | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X29 ) ) ) )
          | ~ ( v5_pre_topc @ X31 @ sk_B @ X29 )
          | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X29 ) )
          | ~ ( v1_funct_1 @ X31 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X29 @ sk_B @ sk_C @ X31 @ X30 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X29 ) ) ) ),
    inference(simplify,[status(thm)],['432'])).

thf('434',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
      | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X29: $i,X30: $i,X31: $i] :
          ( ( v2_struct_0 @ X29 )
          | ~ ( v2_pre_topc @ X29 )
          | ~ ( l1_pre_topc @ X29 )
          | ~ ( v1_funct_1 @ X30 )
          | ~ ( v1_funct_2 @ X30 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X29 ) )
          | ~ ( v5_pre_topc @ X30 @ sk_C @ X29 )
          | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X29 ) ) ) )
          | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X29 ) ) ) )
          | ~ ( v5_pre_topc @ X31 @ sk_B @ X29 )
          | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X29 ) )
          | ~ ( v1_funct_1 @ X31 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X29 @ sk_B @ sk_C @ X31 @ X30 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X29 ) ) ) ),
    inference('sup-',[status(thm)],['399','433'])).

thf('435',plain,
    ( ( ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X29: $i,X30: $i,X31: $i] :
          ( ( v2_struct_0 @ X29 )
          | ~ ( v2_pre_topc @ X29 )
          | ~ ( l1_pre_topc @ X29 )
          | ~ ( v1_funct_1 @ X30 )
          | ~ ( v1_funct_2 @ X30 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X29 ) )
          | ~ ( v5_pre_topc @ X30 @ sk_C @ X29 )
          | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X29 ) ) ) )
          | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X29 ) ) ) )
          | ~ ( v5_pre_topc @ X31 @ sk_B @ X29 )
          | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X29 ) )
          | ~ ( v1_funct_1 @ X31 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X29 @ sk_B @ sk_C @ X31 @ X30 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X29 ) ) ) ),
    inference(simplify,[status(thm)],['434'])).

thf('436',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X29: $i,X30: $i,X31: $i] :
          ( ( v2_struct_0 @ X29 )
          | ~ ( v2_pre_topc @ X29 )
          | ~ ( l1_pre_topc @ X29 )
          | ~ ( v1_funct_1 @ X30 )
          | ~ ( v1_funct_2 @ X30 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X29 ) )
          | ~ ( v5_pre_topc @ X30 @ sk_C @ X29 )
          | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X29 ) ) ) )
          | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X29 ) ) ) )
          | ~ ( v5_pre_topc @ X31 @ sk_B @ X29 )
          | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X29 ) )
          | ~ ( v1_funct_1 @ X31 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X29 @ sk_B @ sk_C @ X31 @ X30 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X29 ) ) ) ),
    inference('sup-',[status(thm)],['389','435'])).

thf('437',plain,
    ( ( ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X29: $i,X30: $i,X31: $i] :
          ( ( v2_struct_0 @ X29 )
          | ~ ( v2_pre_topc @ X29 )
          | ~ ( l1_pre_topc @ X29 )
          | ~ ( v1_funct_1 @ X30 )
          | ~ ( v1_funct_2 @ X30 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X29 ) )
          | ~ ( v5_pre_topc @ X30 @ sk_C @ X29 )
          | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X29 ) ) ) )
          | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X29 ) ) ) )
          | ~ ( v5_pre_topc @ X31 @ sk_B @ X29 )
          | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X29 ) )
          | ~ ( v1_funct_1 @ X31 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X29 @ sk_B @ sk_C @ X31 @ X30 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X29 ) ) ) ),
    inference(simplify,[status(thm)],['436'])).

thf('438',plain,
    ( ( ( v5_pre_topc @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X29: $i,X30: $i,X31: $i] :
          ( ( v2_struct_0 @ X29 )
          | ~ ( v2_pre_topc @ X29 )
          | ~ ( l1_pre_topc @ X29 )
          | ~ ( v1_funct_1 @ X30 )
          | ~ ( v1_funct_2 @ X30 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X29 ) )
          | ~ ( v5_pre_topc @ X30 @ sk_C @ X29 )
          | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X29 ) ) ) )
          | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X29 ) ) ) )
          | ~ ( v5_pre_topc @ X31 @ sk_B @ X29 )
          | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X29 ) )
          | ~ ( v1_funct_1 @ X31 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X29 @ sk_B @ sk_C @ X31 @ X30 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X29 ) ) ) ),
    inference('sup+',[status(thm)],['388','437'])).

thf('439',plain,
    ( ( ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v5_pre_topc @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X29: $i,X30: $i,X31: $i] :
          ( ( v2_struct_0 @ X29 )
          | ~ ( v2_pre_topc @ X29 )
          | ~ ( l1_pre_topc @ X29 )
          | ~ ( v1_funct_1 @ X30 )
          | ~ ( v1_funct_2 @ X30 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X29 ) )
          | ~ ( v5_pre_topc @ X30 @ sk_C @ X29 )
          | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X29 ) ) ) )
          | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X29 ) ) ) )
          | ~ ( v5_pre_topc @ X31 @ sk_B @ X29 )
          | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X29 ) )
          | ~ ( v1_funct_1 @ X31 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X29 @ sk_B @ sk_C @ X31 @ X30 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X29 ) ) ) ),
    inference(simplify,[status(thm)],['438'])).

thf('440',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v1_funct_2 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['336','344'])).

thf('441',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( m1_subset_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['346','354'])).

thf('442',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v2_struct_0 @ X10 )
      | ~ ( m1_pre_topc @ X10 @ X11 )
      | ~ ( r1_tsep_1 @ X10 @ X12 )
      | ~ ( v1_funct_1 @ ( sk_E @ X12 @ X10 @ X11 ) )
      | ~ ( v1_funct_2 @ ( sk_E @ X12 @ X10 @ X11 ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X10 @ X12 ) ) @ ( u1_struct_0 @ ( sk_D @ X12 @ X10 @ X11 ) ) )
      | ~ ( v5_pre_topc @ ( sk_E @ X12 @ X10 @ X11 ) @ ( k1_tsep_1 @ X11 @ X10 @ X12 ) @ ( sk_D @ X12 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ ( sk_E @ X12 @ X10 @ X11 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X10 @ X12 ) ) @ ( u1_struct_0 @ ( sk_D @ X12 @ X10 @ X11 ) ) ) ) )
      | ( r3_tsep_1 @ X11 @ X10 @ X12 )
      | ~ ( m1_pre_topc @ X12 @ X11 )
      | ( v2_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t135_tmap_1])).

thf('443',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ~ ( v5_pre_topc @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_funct_2 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ~ ( v1_funct_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
      | ~ ( r1_tsep_1 @ sk_B @ sk_C )
      | ~ ( m1_pre_topc @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['441','442'])).

thf('444',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('445',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('446',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('447',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_C )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('448',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('449',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ~ ( v5_pre_topc @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_funct_2 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ~ ( v1_funct_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['443','444','445','446','447','448'])).

thf('450',plain,
    ( ( ~ ( v1_funct_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_funct_2 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ~ ( v5_pre_topc @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['449'])).

thf('451',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v5_pre_topc @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_funct_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['440','450'])).

thf('452',plain,
    ( ( ~ ( v1_funct_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v5_pre_topc @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['451'])).

thf('453',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v1_funct_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X29: $i,X30: $i,X31: $i] :
          ( ( v2_struct_0 @ X29 )
          | ~ ( v2_pre_topc @ X29 )
          | ~ ( l1_pre_topc @ X29 )
          | ~ ( v1_funct_1 @ X30 )
          | ~ ( v1_funct_2 @ X30 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X29 ) )
          | ~ ( v5_pre_topc @ X30 @ sk_C @ X29 )
          | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X29 ) ) ) )
          | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X29 ) ) ) )
          | ~ ( v5_pre_topc @ X31 @ sk_B @ X29 )
          | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X29 ) )
          | ~ ( v1_funct_1 @ X31 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X29 @ sk_B @ sk_C @ X31 @ X30 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X29 ) ) ) ),
    inference('sup-',[status(thm)],['439','452'])).

thf('454',plain,
    ( ( ~ ( v1_funct_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X29: $i,X30: $i,X31: $i] :
          ( ( v2_struct_0 @ X29 )
          | ~ ( v2_pre_topc @ X29 )
          | ~ ( l1_pre_topc @ X29 )
          | ~ ( v1_funct_1 @ X30 )
          | ~ ( v1_funct_2 @ X30 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X29 ) )
          | ~ ( v5_pre_topc @ X30 @ sk_C @ X29 )
          | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X29 ) ) ) )
          | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X29 ) ) ) )
          | ~ ( v5_pre_topc @ X31 @ sk_B @ X29 )
          | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X29 ) )
          | ~ ( v1_funct_1 @ X31 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X29 @ sk_B @ sk_C @ X31 @ X30 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X29 ) ) ) ),
    inference(simplify,[status(thm)],['453'])).

thf('455',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X29: $i,X30: $i,X31: $i] :
          ( ( v2_struct_0 @ X29 )
          | ~ ( v2_pre_topc @ X29 )
          | ~ ( l1_pre_topc @ X29 )
          | ~ ( v1_funct_1 @ X30 )
          | ~ ( v1_funct_2 @ X30 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X29 ) )
          | ~ ( v5_pre_topc @ X30 @ sk_C @ X29 )
          | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X29 ) ) ) )
          | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X29 ) ) ) )
          | ~ ( v5_pre_topc @ X31 @ sk_B @ X29 )
          | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X29 ) )
          | ~ ( v1_funct_1 @ X31 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X29 @ sk_B @ sk_C @ X31 @ X30 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X29 ) ) ) ),
    inference('sup-',[status(thm)],['164','454'])).

thf('456',plain,
    ( ( ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X29: $i,X30: $i,X31: $i] :
          ( ( v2_struct_0 @ X29 )
          | ~ ( v2_pre_topc @ X29 )
          | ~ ( l1_pre_topc @ X29 )
          | ~ ( v1_funct_1 @ X30 )
          | ~ ( v1_funct_2 @ X30 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X29 ) )
          | ~ ( v5_pre_topc @ X30 @ sk_C @ X29 )
          | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X29 ) ) ) )
          | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X29 ) ) ) )
          | ~ ( v5_pre_topc @ X31 @ sk_B @ X29 )
          | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X29 ) )
          | ~ ( v1_funct_1 @ X31 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X29 @ sk_B @ sk_C @ X31 @ X30 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X29 ) ) ) ),
    inference(simplify,[status(thm)],['455'])).

thf('457',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v2_struct_0 @ X10 )
      | ~ ( m1_pre_topc @ X10 @ X11 )
      | ~ ( r1_tsep_1 @ X10 @ X12 )
      | ~ ( v2_struct_0 @ ( sk_D @ X12 @ X10 @ X11 ) )
      | ( r3_tsep_1 @ X11 @ X10 @ X12 )
      | ~ ( m1_pre_topc @ X12 @ X11 )
      | ( v2_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t135_tmap_1])).

thf('458',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ~ ( r1_tsep_1 @ sk_B @ sk_C )
      | ~ ( m1_pre_topc @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X29: $i,X30: $i,X31: $i] :
          ( ( v2_struct_0 @ X29 )
          | ~ ( v2_pre_topc @ X29 )
          | ~ ( l1_pre_topc @ X29 )
          | ~ ( v1_funct_1 @ X30 )
          | ~ ( v1_funct_2 @ X30 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X29 ) )
          | ~ ( v5_pre_topc @ X30 @ sk_C @ X29 )
          | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X29 ) ) ) )
          | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X29 ) ) ) )
          | ~ ( v5_pre_topc @ X31 @ sk_B @ X29 )
          | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X29 ) )
          | ~ ( v1_funct_1 @ X31 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X29 @ sk_B @ sk_C @ X31 @ X30 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X29 ) ) ) ),
    inference('sup-',[status(thm)],['456','457'])).

thf('459',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('460',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('461',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('462',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_C )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('463',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('464',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X29: $i,X30: $i,X31: $i] :
          ( ( v2_struct_0 @ X29 )
          | ~ ( v2_pre_topc @ X29 )
          | ~ ( l1_pre_topc @ X29 )
          | ~ ( v1_funct_1 @ X30 )
          | ~ ( v1_funct_2 @ X30 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X29 ) )
          | ~ ( v5_pre_topc @ X30 @ sk_C @ X29 )
          | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X29 ) ) ) )
          | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X29 ) ) ) )
          | ~ ( v5_pre_topc @ X31 @ sk_B @ X29 )
          | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X29 ) )
          | ~ ( v1_funct_1 @ X31 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X29 @ sk_B @ sk_C @ X31 @ X30 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X29 ) ) ) ),
    inference(demod,[status(thm)],['458','459','460','461','462','463'])).

thf('465',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X29: $i,X30: $i,X31: $i] :
          ( ( v2_struct_0 @ X29 )
          | ~ ( v2_pre_topc @ X29 )
          | ~ ( l1_pre_topc @ X29 )
          | ~ ( v1_funct_1 @ X30 )
          | ~ ( v1_funct_2 @ X30 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X29 ) )
          | ~ ( v5_pre_topc @ X30 @ sk_C @ X29 )
          | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X29 ) ) ) )
          | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X29 ) ) ) )
          | ~ ( v5_pre_topc @ X31 @ sk_B @ X29 )
          | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X29 ) )
          | ~ ( v1_funct_1 @ X31 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X29 @ sk_B @ sk_C @ X31 @ X30 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X29 ) ) ) ),
    inference(simplify,[status(thm)],['464'])).

thf('466',plain,
    ( ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
   <= ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['10'])).

thf('467',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      & ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X29: $i,X30: $i,X31: $i] :
          ( ( v2_struct_0 @ X29 )
          | ~ ( v2_pre_topc @ X29 )
          | ~ ( l1_pre_topc @ X29 )
          | ~ ( v1_funct_1 @ X30 )
          | ~ ( v1_funct_2 @ X30 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X29 ) )
          | ~ ( v5_pre_topc @ X30 @ sk_C @ X29 )
          | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X29 ) ) ) )
          | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X29 ) ) ) )
          | ~ ( v5_pre_topc @ X31 @ sk_B @ X29 )
          | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X29 ) )
          | ~ ( v1_funct_1 @ X31 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X29 @ sk_B @ sk_C @ X31 @ X30 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X29 ) ) ) ),
    inference('sup-',[status(thm)],['465','466'])).

thf('468',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('469',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      & ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X29: $i,X30: $i,X31: $i] :
          ( ( v2_struct_0 @ X29 )
          | ~ ( v2_pre_topc @ X29 )
          | ~ ( l1_pre_topc @ X29 )
          | ~ ( v1_funct_1 @ X30 )
          | ~ ( v1_funct_2 @ X30 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X29 ) )
          | ~ ( v5_pre_topc @ X30 @ sk_C @ X29 )
          | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X29 ) ) ) )
          | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X29 ) ) ) )
          | ~ ( v5_pre_topc @ X31 @ sk_B @ X29 )
          | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X29 ) )
          | ~ ( v1_funct_1 @ X31 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X29 @ sk_B @ sk_C @ X31 @ X30 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X29 ) ) ) ),
    inference(clc,[status(thm)],['467','468'])).

thf('470',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('471',plain,
    ( ( v2_struct_0 @ sk_C )
   <= ( ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      & ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X29: $i,X30: $i,X31: $i] :
          ( ( v2_struct_0 @ X29 )
          | ~ ( v2_pre_topc @ X29 )
          | ~ ( l1_pre_topc @ X29 )
          | ~ ( v1_funct_1 @ X30 )
          | ~ ( v1_funct_2 @ X30 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X29 ) )
          | ~ ( v5_pre_topc @ X30 @ sk_C @ X29 )
          | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X29 ) ) ) )
          | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X29 ) ) ) )
          | ~ ( v5_pre_topc @ X31 @ sk_B @ X29 )
          | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X29 ) )
          | ~ ( v1_funct_1 @ X31 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X29 @ sk_B @ sk_C @ X31 @ X30 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X29 ) ) ) ),
    inference(clc,[status(thm)],['469','470'])).

thf('472',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('473',plain,
    ( ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ~ ! [X29: $i,X30: $i,X31: $i] :
          ( ( v2_struct_0 @ X29 )
          | ~ ( v2_pre_topc @ X29 )
          | ~ ( l1_pre_topc @ X29 )
          | ~ ( v1_funct_1 @ X30 )
          | ~ ( v1_funct_2 @ X30 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X29 ) )
          | ~ ( v5_pre_topc @ X30 @ sk_C @ X29 )
          | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X29 ) ) ) )
          | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X29 ) ) ) )
          | ~ ( v5_pre_topc @ X31 @ sk_B @ X29 )
          | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X29 ) )
          | ~ ( v1_funct_1 @ X31 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X29 @ sk_B @ sk_C @ X31 @ X30 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X29 ) )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['471','472'])).

thf('474',plain,
    ( ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ! [X29: $i,X30: $i,X31: $i] :
        ( ( v2_struct_0 @ X29 )
        | ~ ( v2_pre_topc @ X29 )
        | ~ ( l1_pre_topc @ X29 )
        | ~ ( v1_funct_1 @ X30 )
        | ~ ( v1_funct_2 @ X30 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X29 ) )
        | ~ ( v5_pre_topc @ X30 @ sk_C @ X29 )
        | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X29 ) ) ) )
        | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X29 ) ) ) )
        | ~ ( v5_pre_topc @ X31 @ sk_B @ X29 )
        | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X29 ) )
        | ~ ( v1_funct_1 @ X31 )
        | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X29 @ sk_B @ sk_C @ X31 @ X30 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X29 ) ) ),
    inference(split,[status(esa)],['417'])).

thf('475',plain,
    ( ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['33'])).

thf('476',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('477',plain,
    ( ( v1_funct_1 @ sk_F )
   <= ( v1_funct_1 @ sk_F ) ),
    inference(split,[status(esa)],['20'])).

thf('478',plain,
    ( ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
   <= ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(split,[status(esa)],['22'])).

thf('479',plain,
    ( ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
   <= ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ) ),
    inference(split,[status(esa)],['24'])).

thf('480',plain,
    ( ( v1_funct_1 @ sk_E_1 )
   <= ( v1_funct_1 @ sk_E_1 ) ),
    inference(split,[status(esa)],['10'])).

thf('481',plain,
    ( ( v2_pre_topc @ sk_D_1 )
   <= ( v2_pre_topc @ sk_D_1 ) ),
    inference(split,[status(esa)],['28'])).

thf('482',plain,
    ( ( l1_pre_topc @ sk_D_1 )
   <= ( l1_pre_topc @ sk_D_1 ) ),
    inference(split,[status(esa)],['26'])).

thf('483',plain,
    ( ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
   <= ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(split,[status(esa)],['31'])).

thf('484',plain,
    ( ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
   <= ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ) ),
    inference(split,[status(esa)],['33'])).

thf('485',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X5 ) @ ( u1_struct_0 @ X6 ) ) ) )
      | ~ ( v1_funct_2 @ X4 @ ( u1_struct_0 @ X5 ) @ ( u1_struct_0 @ X6 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( m1_pre_topc @ X7 @ X8 )
      | ( v2_struct_0 @ X7 )
      | ~ ( m1_pre_topc @ X5 @ X8 )
      | ( v2_struct_0 @ X5 )
      | ~ ( l1_pre_topc @ X6 )
      | ~ ( v2_pre_topc @ X6 )
      | ( v2_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 )
      | ( v2_struct_0 @ X8 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_funct_2 @ X9 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X6 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X6 ) ) ) )
      | ( v1_funct_1 @ ( k10_tmap_1 @ X8 @ X6 @ X5 @ X7 @ X4 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k10_tmap_1])).

thf('486',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( v1_funct_1 @ ( k10_tmap_1 @ X2 @ sk_D_1 @ sk_B @ X1 @ sk_E_1 @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_D_1 ) )
        | ~ ( v1_funct_1 @ X0 )
        | ( v2_struct_0 @ X2 )
        | ~ ( v2_pre_topc @ X2 )
        | ~ ( l1_pre_topc @ X2 )
        | ( v2_struct_0 @ sk_D_1 )
        | ~ ( v2_pre_topc @ sk_D_1 )
        | ~ ( l1_pre_topc @ sk_D_1 )
        | ( v2_struct_0 @ sk_B )
        | ~ ( m1_pre_topc @ sk_B @ X2 )
        | ( v2_struct_0 @ X1 )
        | ~ ( m1_pre_topc @ X1 @ X2 )
        | ~ ( v1_funct_1 @ sk_E_1 )
        | ~ ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) )
   <= ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['484','485'])).

thf('487',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ~ ( v1_funct_1 @ sk_E_1 )
        | ~ ( m1_pre_topc @ X1 @ X0 )
        | ( v2_struct_0 @ X1 )
        | ~ ( m1_pre_topc @ sk_B @ X0 )
        | ( v2_struct_0 @ sk_B )
        | ~ ( l1_pre_topc @ sk_D_1 )
        | ~ ( v2_pre_topc @ sk_D_1 )
        | ( v2_struct_0 @ sk_D_1 )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 )
        | ~ ( v1_funct_1 @ X2 )
        | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_D_1 ) )
        | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
        | ( v1_funct_1 @ ( k10_tmap_1 @ X0 @ sk_D_1 @ sk_B @ X1 @ sk_E_1 @ X2 ) ) )
   <= ( ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['483','486'])).

thf('488',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( v1_funct_1 @ ( k10_tmap_1 @ X2 @ sk_D_1 @ sk_B @ X1 @ sk_E_1 @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_D_1 ) )
        | ~ ( v1_funct_1 @ X0 )
        | ( v2_struct_0 @ X2 )
        | ~ ( v2_pre_topc @ X2 )
        | ~ ( l1_pre_topc @ X2 )
        | ( v2_struct_0 @ sk_D_1 )
        | ~ ( v2_pre_topc @ sk_D_1 )
        | ( v2_struct_0 @ sk_B )
        | ~ ( m1_pre_topc @ sk_B @ X2 )
        | ( v2_struct_0 @ X1 )
        | ~ ( m1_pre_topc @ X1 @ X2 )
        | ~ ( v1_funct_1 @ sk_E_1 ) )
   <= ( ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( l1_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['482','487'])).

thf('489',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ~ ( v1_funct_1 @ sk_E_1 )
        | ~ ( m1_pre_topc @ X1 @ X0 )
        | ( v2_struct_0 @ X1 )
        | ~ ( m1_pre_topc @ sk_B @ X0 )
        | ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_D_1 )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 )
        | ~ ( v1_funct_1 @ X2 )
        | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_D_1 ) )
        | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
        | ( v1_funct_1 @ ( k10_tmap_1 @ X0 @ sk_D_1 @ sk_B @ X1 @ sk_E_1 @ X2 ) ) )
   <= ( ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['481','488'])).

thf('490',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( v1_funct_1 @ ( k10_tmap_1 @ X2 @ sk_D_1 @ sk_B @ X1 @ sk_E_1 @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_D_1 ) )
        | ~ ( v1_funct_1 @ X0 )
        | ( v2_struct_0 @ X2 )
        | ~ ( v2_pre_topc @ X2 )
        | ~ ( l1_pre_topc @ X2 )
        | ( v2_struct_0 @ sk_D_1 )
        | ( v2_struct_0 @ sk_B )
        | ~ ( m1_pre_topc @ sk_B @ X2 )
        | ( v2_struct_0 @ X1 )
        | ~ ( m1_pre_topc @ X1 @ X2 ) )
   <= ( ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['480','489'])).

thf('491',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_pre_topc @ sk_C @ X0 )
        | ( v2_struct_0 @ sk_C )
        | ~ ( m1_pre_topc @ sk_B @ X0 )
        | ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_D_1 )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 )
        | ~ ( v1_funct_1 @ sk_F )
        | ~ ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
        | ( v1_funct_1 @ ( k10_tmap_1 @ X0 @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) ) )
   <= ( ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['479','490'])).

thf('492',plain,
    ( ! [X0: $i] :
        ( ( v1_funct_1 @ ( k10_tmap_1 @ X0 @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) )
        | ~ ( v1_funct_1 @ sk_F )
        | ( v2_struct_0 @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ( v2_struct_0 @ sk_D_1 )
        | ( v2_struct_0 @ sk_B )
        | ~ ( m1_pre_topc @ sk_B @ X0 )
        | ( v2_struct_0 @ sk_C )
        | ~ ( m1_pre_topc @ sk_C @ X0 ) )
   <= ( ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['478','491'])).

thf('493',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_pre_topc @ sk_C @ X0 )
        | ( v2_struct_0 @ sk_C )
        | ~ ( m1_pre_topc @ sk_B @ X0 )
        | ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_D_1 )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 )
        | ( v1_funct_1 @ ( k10_tmap_1 @ X0 @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) ) )
   <= ( ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v1_funct_1 @ sk_F )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['477','492'])).

thf('494',plain,
    ( ( ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v1_funct_1 @ sk_F )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['476','493'])).

thf('495',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('496',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('497',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('498',plain,
    ( ( ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v1_funct_1 @ sk_F )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['494','495','496','497'])).

thf('499',plain,
    ( ~ ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) )
   <= ~ ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) ) ),
    inference(split,[status(esa)],['49'])).

thf('500',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) )
      & ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v1_funct_1 @ sk_F )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['498','499'])).

thf('501',plain,
    ( ~ ( v2_struct_0 @ sk_D_1 )
   <= ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(split,[status(esa)],['52'])).

thf('502',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ~ ( v2_struct_0 @ sk_D_1 )
      & ~ ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) )
      & ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v1_funct_1 @ sk_F )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['500','501'])).

thf('503',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('504',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( v2_struct_0 @ sk_D_1 )
      & ~ ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) )
      & ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v1_funct_1 @ sk_F )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference(clc,[status(thm)],['502','503'])).

thf('505',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('506',plain,
    ( ( v2_struct_0 @ sk_B )
   <= ( ~ ( v2_struct_0 @ sk_D_1 )
      & ~ ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) )
      & ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v1_funct_1 @ sk_F )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference(clc,[status(thm)],['504','505'])).

thf('507',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('508',plain,
    ( ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) )
    | ~ ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
    | ~ ( v2_pre_topc @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_F )
    | ~ ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ~ ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
    | ~ ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ~ ( v1_funct_1 @ sk_E_1 )
    | ~ ( l1_pre_topc @ sk_D_1 )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['506','507'])).

thf('509',plain,
    ( ~ ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) )
    | ~ ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ~ ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ~ ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D_1 ) ),
    inference(split,[status(esa)],['49'])).

thf('510',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','18','60','93','144','145','146','147','148','149','150','151','152','153','154','473','474','475','508','509'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YUa72bH9HZ
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:49:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.19/0.34  % Python version: Python 3.6.8
% 0.19/0.34  % Running in FO mode
% 2.52/2.70  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.52/2.70  % Solved by: fo/fo7.sh
% 2.52/2.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.52/2.70  % done 1827 iterations in 2.216s
% 2.52/2.70  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.52/2.70  % SZS output start Refutation
% 2.52/2.70  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.52/2.70  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 2.52/2.70  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 2.52/2.70  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 2.52/2.70  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 2.52/2.70  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 2.52/2.70  thf(sk_D_1_type, type, sk_D_1: $i).
% 2.52/2.70  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 2.52/2.70  thf(r4_tsep_1_type, type, r4_tsep_1: $i > $i > $i > $o).
% 2.52/2.70  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.52/2.70  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.52/2.70  thf(r1_tsep_1_type, type, r1_tsep_1: $i > $i > $o).
% 2.52/2.70  thf(sk_C_type, type, sk_C: $i).
% 2.52/2.70  thf(sk_F_type, type, sk_F: $i).
% 2.52/2.70  thf(sk_A_type, type, sk_A: $i).
% 2.52/2.70  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 2.52/2.70  thf(sk_B_type, type, sk_B: $i).
% 2.52/2.70  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 2.52/2.70  thf(k10_tmap_1_type, type, k10_tmap_1: $i > $i > $i > $i > $i > $i > $i).
% 2.52/2.70  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 2.52/2.70  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 2.52/2.70  thf(sk_E_1_type, type, sk_E_1: $i).
% 2.52/2.70  thf(k1_tsep_1_type, type, k1_tsep_1: $i > $i > $i > $i).
% 2.52/2.70  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.52/2.70  thf(r3_tsep_1_type, type, r3_tsep_1: $i > $i > $i > $o).
% 2.52/2.70  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.52/2.70  thf(t150_tmap_1, conjecture,
% 2.52/2.70    (![A:$i]:
% 2.52/2.70     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.52/2.70       ( ![B:$i]:
% 2.52/2.70         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 2.52/2.70           ( ![C:$i]:
% 2.52/2.70             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 2.52/2.70               ( ( r3_tsep_1 @ A @ B @ C ) <=>
% 2.52/2.70                 ( ( r1_tsep_1 @ B @ C ) & 
% 2.52/2.70                   ( ![D:$i]:
% 2.52/2.70                     ( ( ( ~( v2_struct_0 @ D ) ) & ( v2_pre_topc @ D ) & 
% 2.52/2.70                         ( l1_pre_topc @ D ) ) =>
% 2.52/2.70                       ( ![E:$i]:
% 2.52/2.70                         ( ( ( v1_funct_1 @ E ) & 
% 2.52/2.70                             ( v1_funct_2 @
% 2.52/2.70                               E @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ D ) ) & 
% 2.52/2.70                             ( v5_pre_topc @ E @ B @ D ) & 
% 2.52/2.70                             ( m1_subset_1 @
% 2.52/2.70                               E @ 
% 2.52/2.70                               ( k1_zfmisc_1 @
% 2.52/2.70                                 ( k2_zfmisc_1 @
% 2.52/2.70                                   ( u1_struct_0 @ B ) @ ( u1_struct_0 @ D ) ) ) ) ) =>
% 2.52/2.70                           ( ![F:$i]:
% 2.52/2.70                             ( ( ( v1_funct_1 @ F ) & 
% 2.52/2.70                                 ( v1_funct_2 @
% 2.52/2.70                                   F @ ( u1_struct_0 @ C ) @ 
% 2.52/2.70                                   ( u1_struct_0 @ D ) ) & 
% 2.52/2.70                                 ( v5_pre_topc @ F @ C @ D ) & 
% 2.52/2.70                                 ( m1_subset_1 @
% 2.52/2.70                                   F @ 
% 2.52/2.70                                   ( k1_zfmisc_1 @
% 2.52/2.70                                     ( k2_zfmisc_1 @
% 2.52/2.70                                       ( u1_struct_0 @ C ) @ 
% 2.52/2.70                                       ( u1_struct_0 @ D ) ) ) ) ) =>
% 2.52/2.70                               ( ( v1_funct_1 @
% 2.52/2.70                                   ( k10_tmap_1 @ A @ D @ B @ C @ E @ F ) ) & 
% 2.52/2.70                                 ( v1_funct_2 @
% 2.52/2.70                                   ( k10_tmap_1 @ A @ D @ B @ C @ E @ F ) @ 
% 2.52/2.70                                   ( u1_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) @ 
% 2.52/2.70                                   ( u1_struct_0 @ D ) ) & 
% 2.52/2.70                                 ( v5_pre_topc @
% 2.52/2.70                                   ( k10_tmap_1 @ A @ D @ B @ C @ E @ F ) @ 
% 2.52/2.70                                   ( k1_tsep_1 @ A @ B @ C ) @ D ) & 
% 2.52/2.70                                 ( m1_subset_1 @
% 2.52/2.70                                   ( k10_tmap_1 @ A @ D @ B @ C @ E @ F ) @ 
% 2.52/2.70                                   ( k1_zfmisc_1 @
% 2.52/2.70                                     ( k2_zfmisc_1 @
% 2.52/2.70                                       ( u1_struct_0 @
% 2.52/2.70                                         ( k1_tsep_1 @ A @ B @ C ) ) @ 
% 2.52/2.70                                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 2.52/2.70  thf(zf_stmt_0, negated_conjecture,
% 2.52/2.70    (~( ![A:$i]:
% 2.52/2.70        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 2.52/2.70            ( l1_pre_topc @ A ) ) =>
% 2.52/2.70          ( ![B:$i]:
% 2.52/2.70            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 2.52/2.70              ( ![C:$i]:
% 2.52/2.70                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 2.52/2.70                  ( ( r3_tsep_1 @ A @ B @ C ) <=>
% 2.52/2.70                    ( ( r1_tsep_1 @ B @ C ) & 
% 2.52/2.70                      ( ![D:$i]:
% 2.52/2.70                        ( ( ( ~( v2_struct_0 @ D ) ) & ( v2_pre_topc @ D ) & 
% 2.52/2.70                            ( l1_pre_topc @ D ) ) =>
% 2.52/2.70                          ( ![E:$i]:
% 2.52/2.70                            ( ( ( v1_funct_1 @ E ) & 
% 2.52/2.70                                ( v1_funct_2 @
% 2.52/2.70                                  E @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ D ) ) & 
% 2.52/2.70                                ( v5_pre_topc @ E @ B @ D ) & 
% 2.52/2.70                                ( m1_subset_1 @
% 2.52/2.70                                  E @ 
% 2.52/2.70                                  ( k1_zfmisc_1 @
% 2.52/2.70                                    ( k2_zfmisc_1 @
% 2.52/2.70                                      ( u1_struct_0 @ B ) @ ( u1_struct_0 @ D ) ) ) ) ) =>
% 2.52/2.70                              ( ![F:$i]:
% 2.52/2.70                                ( ( ( v1_funct_1 @ F ) & 
% 2.52/2.70                                    ( v1_funct_2 @
% 2.52/2.70                                      F @ ( u1_struct_0 @ C ) @ 
% 2.52/2.70                                      ( u1_struct_0 @ D ) ) & 
% 2.52/2.70                                    ( v5_pre_topc @ F @ C @ D ) & 
% 2.52/2.70                                    ( m1_subset_1 @
% 2.52/2.70                                      F @ 
% 2.52/2.70                                      ( k1_zfmisc_1 @
% 2.52/2.70                                        ( k2_zfmisc_1 @
% 2.52/2.70                                          ( u1_struct_0 @ C ) @ 
% 2.52/2.70                                          ( u1_struct_0 @ D ) ) ) ) ) =>
% 2.52/2.70                                  ( ( v1_funct_1 @
% 2.52/2.70                                      ( k10_tmap_1 @ A @ D @ B @ C @ E @ F ) ) & 
% 2.52/2.70                                    ( v1_funct_2 @
% 2.52/2.70                                      ( k10_tmap_1 @ A @ D @ B @ C @ E @ F ) @ 
% 2.52/2.70                                      ( u1_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) @ 
% 2.52/2.70                                      ( u1_struct_0 @ D ) ) & 
% 2.52/2.70                                    ( v5_pre_topc @
% 2.52/2.70                                      ( k10_tmap_1 @ A @ D @ B @ C @ E @ F ) @ 
% 2.52/2.70                                      ( k1_tsep_1 @ A @ B @ C ) @ D ) & 
% 2.52/2.70                                    ( m1_subset_1 @
% 2.52/2.70                                      ( k10_tmap_1 @ A @ D @ B @ C @ E @ F ) @ 
% 2.52/2.70                                      ( k1_zfmisc_1 @
% 2.52/2.70                                        ( k2_zfmisc_1 @
% 2.52/2.70                                          ( u1_struct_0 @
% 2.52/2.70                                            ( k1_tsep_1 @ A @ B @ C ) ) @ 
% 2.52/2.70                                          ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 2.52/2.70    inference('cnf.neg', [status(esa)], [t150_tmap_1])).
% 2.52/2.70  thf('0', plain,
% 2.52/2.70      (((r1_tsep_1 @ sk_B @ sk_C) | (r3_tsep_1 @ sk_A @ sk_B @ sk_C))),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('1', plain,
% 2.52/2.70      (((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) | ((r1_tsep_1 @ sk_B @ sk_C))),
% 2.52/2.70      inference('split', [status(esa)], ['0'])).
% 2.52/2.70  thf('2', plain,
% 2.52/2.70      (((r3_tsep_1 @ sk_A @ sk_B @ sk_C))
% 2.52/2.70         <= (((r3_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 2.52/2.70      inference('split', [status(esa)], ['0'])).
% 2.52/2.70  thf(t135_tmap_1, axiom,
% 2.52/2.70    (![A:$i]:
% 2.52/2.70     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.52/2.70       ( ![B:$i]:
% 2.52/2.70         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 2.52/2.70           ( ![C:$i]:
% 2.52/2.70             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 2.52/2.70               ( ( r3_tsep_1 @ A @ B @ C ) <=>
% 2.52/2.70                 ( ( r1_tsep_1 @ B @ C ) & 
% 2.52/2.70                   ( ![D:$i]:
% 2.52/2.70                     ( ( ( ~( v2_struct_0 @ D ) ) & ( v2_pre_topc @ D ) & 
% 2.52/2.70                         ( l1_pre_topc @ D ) ) =>
% 2.52/2.70                       ( ![E:$i]:
% 2.52/2.70                         ( ( ( v1_funct_1 @ E ) & 
% 2.52/2.70                             ( v1_funct_2 @
% 2.52/2.70                               E @ 
% 2.52/2.70                               ( u1_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) @ 
% 2.52/2.70                               ( u1_struct_0 @ D ) ) & 
% 2.52/2.70                             ( m1_subset_1 @
% 2.52/2.70                               E @ 
% 2.52/2.70                               ( k1_zfmisc_1 @
% 2.52/2.70                                 ( k2_zfmisc_1 @
% 2.52/2.70                                   ( u1_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) @ 
% 2.52/2.70                                   ( u1_struct_0 @ D ) ) ) ) ) =>
% 2.52/2.70                           ( ( ( v1_funct_1 @
% 2.52/2.70                                 ( k3_tmap_1 @
% 2.52/2.70                                   A @ D @ ( k1_tsep_1 @ A @ B @ C ) @ B @ E ) ) & 
% 2.52/2.70                               ( v1_funct_2 @
% 2.52/2.70                                 ( k3_tmap_1 @
% 2.52/2.70                                   A @ D @ ( k1_tsep_1 @ A @ B @ C ) @ B @ E ) @ 
% 2.52/2.70                                 ( u1_struct_0 @ B ) @ ( u1_struct_0 @ D ) ) & 
% 2.52/2.70                               ( v5_pre_topc @
% 2.52/2.70                                 ( k3_tmap_1 @
% 2.52/2.70                                   A @ D @ ( k1_tsep_1 @ A @ B @ C ) @ B @ E ) @ 
% 2.52/2.70                                 B @ D ) & 
% 2.52/2.70                               ( m1_subset_1 @
% 2.52/2.70                                 ( k3_tmap_1 @
% 2.52/2.70                                   A @ D @ ( k1_tsep_1 @ A @ B @ C ) @ B @ E ) @ 
% 2.52/2.70                                 ( k1_zfmisc_1 @
% 2.52/2.70                                   ( k2_zfmisc_1 @
% 2.52/2.70                                     ( u1_struct_0 @ B ) @ ( u1_struct_0 @ D ) ) ) ) & 
% 2.52/2.70                               ( v1_funct_1 @
% 2.52/2.70                                 ( k3_tmap_1 @
% 2.52/2.70                                   A @ D @ ( k1_tsep_1 @ A @ B @ C ) @ C @ E ) ) & 
% 2.52/2.70                               ( v1_funct_2 @
% 2.52/2.70                                 ( k3_tmap_1 @
% 2.52/2.70                                   A @ D @ ( k1_tsep_1 @ A @ B @ C ) @ C @ E ) @ 
% 2.52/2.70                                 ( u1_struct_0 @ C ) @ ( u1_struct_0 @ D ) ) & 
% 2.52/2.70                               ( v5_pre_topc @
% 2.52/2.70                                 ( k3_tmap_1 @
% 2.52/2.70                                   A @ D @ ( k1_tsep_1 @ A @ B @ C ) @ C @ E ) @ 
% 2.52/2.70                                 C @ D ) & 
% 2.52/2.70                               ( m1_subset_1 @
% 2.52/2.70                                 ( k3_tmap_1 @
% 2.52/2.70                                   A @ D @ ( k1_tsep_1 @ A @ B @ C ) @ C @ E ) @ 
% 2.52/2.70                                 ( k1_zfmisc_1 @
% 2.52/2.70                                   ( k2_zfmisc_1 @
% 2.52/2.70                                     ( u1_struct_0 @ C ) @ ( u1_struct_0 @ D ) ) ) ) ) =>
% 2.52/2.70                             ( ( v1_funct_1 @ E ) & 
% 2.52/2.70                               ( v1_funct_2 @
% 2.52/2.70                                 E @ 
% 2.52/2.70                                 ( u1_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) @ 
% 2.52/2.70                                 ( u1_struct_0 @ D ) ) & 
% 2.52/2.70                               ( v5_pre_topc @
% 2.52/2.70                                 E @ ( k1_tsep_1 @ A @ B @ C ) @ D ) & 
% 2.52/2.70                               ( m1_subset_1 @
% 2.52/2.70                                 E @ 
% 2.52/2.70                                 ( k1_zfmisc_1 @
% 2.52/2.70                                   ( k2_zfmisc_1 @
% 2.52/2.70                                     ( u1_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) @ 
% 2.52/2.70                                     ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 2.52/2.70  thf('3', plain,
% 2.52/2.70      (![X10 : $i, X11 : $i, X12 : $i]:
% 2.52/2.70         ((v2_struct_0 @ X10)
% 2.52/2.70          | ~ (m1_pre_topc @ X10 @ X11)
% 2.52/2.70          | ~ (r3_tsep_1 @ X11 @ X10 @ X12)
% 2.52/2.70          | (r1_tsep_1 @ X10 @ X12)
% 2.52/2.70          | ~ (m1_pre_topc @ X12 @ X11)
% 2.52/2.70          | (v2_struct_0 @ X12)
% 2.52/2.70          | ~ (l1_pre_topc @ X11)
% 2.52/2.70          | ~ (v2_pre_topc @ X11)
% 2.52/2.70          | (v2_struct_0 @ X11))),
% 2.52/2.70      inference('cnf', [status(esa)], [t135_tmap_1])).
% 2.52/2.70  thf('4', plain,
% 2.52/2.70      ((((v2_struct_0 @ sk_A)
% 2.52/2.70         | ~ (v2_pre_topc @ sk_A)
% 2.52/2.70         | ~ (l1_pre_topc @ sk_A)
% 2.52/2.70         | (v2_struct_0 @ sk_C)
% 2.52/2.70         | ~ (m1_pre_topc @ sk_C @ sk_A)
% 2.52/2.70         | (r1_tsep_1 @ sk_B @ sk_C)
% 2.52/2.70         | ~ (m1_pre_topc @ sk_B @ sk_A)
% 2.52/2.70         | (v2_struct_0 @ sk_B))) <= (((r3_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['2', '3'])).
% 2.52/2.70  thf('5', plain, ((v2_pre_topc @ sk_A)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('7', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('8', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('9', plain,
% 2.52/2.70      ((((v2_struct_0 @ sk_A)
% 2.52/2.70         | (v2_struct_0 @ sk_C)
% 2.52/2.70         | (r1_tsep_1 @ sk_B @ sk_C)
% 2.52/2.70         | (v2_struct_0 @ sk_B))) <= (((r3_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 2.52/2.70      inference('demod', [status(thm)], ['4', '5', '6', '7', '8'])).
% 2.52/2.70  thf('10', plain,
% 2.52/2.70      (((v1_funct_1 @ sk_E_1)
% 2.52/2.70        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 2.52/2.70        | ~ (r3_tsep_1 @ sk_A @ sk_B @ sk_C))),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('11', plain,
% 2.52/2.70      ((~ (r1_tsep_1 @ sk_B @ sk_C)) <= (~ ((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('split', [status(esa)], ['10'])).
% 2.52/2.70  thf('12', plain,
% 2.52/2.70      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A)))
% 2.52/2.70         <= (~ ((r1_tsep_1 @ sk_B @ sk_C)) & ((r3_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['9', '11'])).
% 2.52/2.70  thf('13', plain, (~ (v2_struct_0 @ sk_B)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('14', plain,
% 2.52/2.70      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C)))
% 2.52/2.70         <= (~ ((r1_tsep_1 @ sk_B @ sk_C)) & ((r3_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 2.52/2.70      inference('clc', [status(thm)], ['12', '13'])).
% 2.52/2.70  thf('15', plain, (~ (v2_struct_0 @ sk_A)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('16', plain,
% 2.52/2.70      (((v2_struct_0 @ sk_C))
% 2.52/2.70         <= (~ ((r1_tsep_1 @ sk_B @ sk_C)) & ((r3_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 2.52/2.70      inference('clc', [status(thm)], ['14', '15'])).
% 2.52/2.70  thf('17', plain, (~ (v2_struct_0 @ sk_C)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('18', plain,
% 2.52/2.70      (((r1_tsep_1 @ sk_B @ sk_C)) | ~ ((r3_tsep_1 @ sk_A @ sk_B @ sk_C))),
% 2.52/2.70      inference('sup-', [status(thm)], ['16', '17'])).
% 2.52/2.70  thf('19', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('20', plain,
% 2.52/2.70      (((v1_funct_1 @ sk_F)
% 2.52/2.70        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 2.52/2.70        | ~ (r3_tsep_1 @ sk_A @ sk_B @ sk_C))),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('21', plain, (((v1_funct_1 @ sk_F)) <= (((v1_funct_1 @ sk_F)))),
% 2.52/2.70      inference('split', [status(esa)], ['20'])).
% 2.52/2.70  thf('22', plain,
% 2.52/2.70      (((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))
% 2.52/2.70        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 2.52/2.70        | ~ (r3_tsep_1 @ sk_A @ sk_B @ sk_C))),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('23', plain,
% 2.52/2.70      (((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1)))
% 2.52/2.70         <= (((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.70               (u1_struct_0 @ sk_D_1))))),
% 2.52/2.70      inference('split', [status(esa)], ['22'])).
% 2.52/2.70  thf('24', plain,
% 2.52/2.70      (((m1_subset_1 @ sk_F @ 
% 2.52/2.70         (k1_zfmisc_1 @ 
% 2.52/2.70          (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))
% 2.52/2.70        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 2.52/2.70        | ~ (r3_tsep_1 @ sk_A @ sk_B @ sk_C))),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('25', plain,
% 2.52/2.70      (((m1_subset_1 @ sk_F @ 
% 2.52/2.70         (k1_zfmisc_1 @ 
% 2.52/2.70          (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1)))))
% 2.52/2.70         <= (((m1_subset_1 @ sk_F @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))))),
% 2.52/2.70      inference('split', [status(esa)], ['24'])).
% 2.52/2.70  thf('26', plain,
% 2.52/2.70      (((l1_pre_topc @ sk_D_1)
% 2.52/2.70        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 2.52/2.70        | ~ (r3_tsep_1 @ sk_A @ sk_B @ sk_C))),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('27', plain, (((l1_pre_topc @ sk_D_1)) <= (((l1_pre_topc @ sk_D_1)))),
% 2.52/2.70      inference('split', [status(esa)], ['26'])).
% 2.52/2.70  thf('28', plain,
% 2.52/2.70      (((v2_pre_topc @ sk_D_1)
% 2.52/2.70        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 2.52/2.70        | ~ (r3_tsep_1 @ sk_A @ sk_B @ sk_C))),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('29', plain, (((v2_pre_topc @ sk_D_1)) <= (((v2_pre_topc @ sk_D_1)))),
% 2.52/2.70      inference('split', [status(esa)], ['28'])).
% 2.52/2.70  thf('30', plain, (((v1_funct_1 @ sk_E_1)) <= (((v1_funct_1 @ sk_E_1)))),
% 2.52/2.70      inference('split', [status(esa)], ['10'])).
% 2.52/2.70  thf('31', plain,
% 2.52/2.70      (((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))
% 2.52/2.70        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 2.52/2.70        | ~ (r3_tsep_1 @ sk_A @ sk_B @ sk_C))),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('32', plain,
% 2.52/2.70      (((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1)))
% 2.52/2.70         <= (((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.70               (u1_struct_0 @ sk_D_1))))),
% 2.52/2.70      inference('split', [status(esa)], ['31'])).
% 2.52/2.70  thf('33', plain,
% 2.52/2.70      (((m1_subset_1 @ sk_E_1 @ 
% 2.52/2.70         (k1_zfmisc_1 @ 
% 2.52/2.70          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))
% 2.52/2.70        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 2.52/2.70        | ~ (r3_tsep_1 @ sk_A @ sk_B @ sk_C))),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('34', plain,
% 2.52/2.70      (((m1_subset_1 @ sk_E_1 @ 
% 2.52/2.70         (k1_zfmisc_1 @ 
% 2.52/2.70          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1)))))
% 2.52/2.70         <= (((m1_subset_1 @ sk_E_1 @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))))),
% 2.52/2.70      inference('split', [status(esa)], ['33'])).
% 2.52/2.70  thf(dt_k10_tmap_1, axiom,
% 2.52/2.70    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.52/2.70     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 2.52/2.70         ( l1_pre_topc @ A ) & ( ~( v2_struct_0 @ B ) ) & 
% 2.52/2.70         ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) & 
% 2.52/2.70         ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) & 
% 2.52/2.70         ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) & 
% 2.52/2.70         ( v1_funct_1 @ E ) & 
% 2.52/2.70         ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 2.52/2.70         ( m1_subset_1 @
% 2.52/2.70           E @ 
% 2.52/2.70           ( k1_zfmisc_1 @
% 2.52/2.70             ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 2.52/2.70         ( v1_funct_1 @ F ) & 
% 2.52/2.70         ( v1_funct_2 @ F @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 2.52/2.70         ( m1_subset_1 @
% 2.52/2.70           F @ 
% 2.52/2.70           ( k1_zfmisc_1 @
% 2.52/2.70             ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 2.52/2.70       ( ( v1_funct_1 @ ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) ) & 
% 2.52/2.70         ( v1_funct_2 @
% 2.52/2.70           ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 2.52/2.70           ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) ) & 
% 2.52/2.70         ( m1_subset_1 @
% 2.52/2.70           ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 2.52/2.70           ( k1_zfmisc_1 @
% 2.52/2.70             ( k2_zfmisc_1 @
% 2.52/2.70               ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 2.52/2.70               ( u1_struct_0 @ B ) ) ) ) ) ))).
% 2.52/2.70  thf('35', plain,
% 2.52/2.70      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 2.52/2.70         (~ (m1_subset_1 @ X4 @ 
% 2.52/2.70             (k1_zfmisc_1 @ 
% 2.52/2.70              (k2_zfmisc_1 @ (u1_struct_0 @ X5) @ (u1_struct_0 @ X6))))
% 2.52/2.70          | ~ (v1_funct_2 @ X4 @ (u1_struct_0 @ X5) @ (u1_struct_0 @ X6))
% 2.52/2.70          | ~ (v1_funct_1 @ X4)
% 2.52/2.70          | ~ (m1_pre_topc @ X7 @ X8)
% 2.52/2.70          | (v2_struct_0 @ X7)
% 2.52/2.70          | ~ (m1_pre_topc @ X5 @ X8)
% 2.52/2.70          | (v2_struct_0 @ X5)
% 2.52/2.70          | ~ (l1_pre_topc @ X6)
% 2.52/2.70          | ~ (v2_pre_topc @ X6)
% 2.52/2.70          | (v2_struct_0 @ X6)
% 2.52/2.70          | ~ (l1_pre_topc @ X8)
% 2.52/2.70          | ~ (v2_pre_topc @ X8)
% 2.52/2.70          | (v2_struct_0 @ X8)
% 2.52/2.70          | ~ (v1_funct_1 @ X9)
% 2.52/2.70          | ~ (v1_funct_2 @ X9 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X6))
% 2.52/2.70          | ~ (m1_subset_1 @ X9 @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X6))))
% 2.52/2.70          | (v1_funct_2 @ (k10_tmap_1 @ X8 @ X6 @ X5 @ X7 @ X4 @ X9) @ 
% 2.52/2.70             (u1_struct_0 @ (k1_tsep_1 @ X8 @ X5 @ X7)) @ (u1_struct_0 @ X6)))),
% 2.52/2.70      inference('cnf', [status(esa)], [dt_k10_tmap_1])).
% 2.52/2.70  thf('36', plain,
% 2.52/2.70      ((![X0 : $i, X1 : $i, X2 : $i]:
% 2.52/2.70          ((v1_funct_2 @ 
% 2.52/2.70            (k10_tmap_1 @ X1 @ sk_D_1 @ sk_B @ X0 @ sk_E_1 @ X2) @ 
% 2.52/2.70            (u1_struct_0 @ (k1_tsep_1 @ X1 @ sk_B @ X0)) @ 
% 2.52/2.70            (u1_struct_0 @ sk_D_1))
% 2.52/2.70           | ~ (m1_subset_1 @ X2 @ 
% 2.52/2.70                (k1_zfmisc_1 @ 
% 2.52/2.70                 (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_D_1))))
% 2.52/2.70           | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_D_1))
% 2.52/2.70           | ~ (v1_funct_1 @ X2)
% 2.52/2.70           | (v2_struct_0 @ X1)
% 2.52/2.70           | ~ (v2_pre_topc @ X1)
% 2.52/2.70           | ~ (l1_pre_topc @ X1)
% 2.52/2.70           | (v2_struct_0 @ sk_D_1)
% 2.52/2.70           | ~ (v2_pre_topc @ sk_D_1)
% 2.52/2.70           | ~ (l1_pre_topc @ sk_D_1)
% 2.52/2.70           | (v2_struct_0 @ sk_B)
% 2.52/2.70           | ~ (m1_pre_topc @ sk_B @ X1)
% 2.52/2.70           | (v2_struct_0 @ X0)
% 2.52/2.70           | ~ (m1_pre_topc @ X0 @ X1)
% 2.52/2.70           | ~ (v1_funct_1 @ sk_E_1)
% 2.52/2.70           | ~ (v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.70                (u1_struct_0 @ sk_D_1))))
% 2.52/2.70         <= (((m1_subset_1 @ sk_E_1 @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))))),
% 2.52/2.70      inference('sup-', [status(thm)], ['34', '35'])).
% 2.52/2.70  thf('37', plain,
% 2.52/2.70      ((![X0 : $i, X1 : $i, X2 : $i]:
% 2.52/2.70          (~ (v1_funct_1 @ sk_E_1)
% 2.52/2.70           | ~ (m1_pre_topc @ X1 @ X0)
% 2.52/2.70           | (v2_struct_0 @ X1)
% 2.52/2.70           | ~ (m1_pre_topc @ sk_B @ X0)
% 2.52/2.70           | (v2_struct_0 @ sk_B)
% 2.52/2.70           | ~ (l1_pre_topc @ sk_D_1)
% 2.52/2.70           | ~ (v2_pre_topc @ sk_D_1)
% 2.52/2.70           | (v2_struct_0 @ sk_D_1)
% 2.52/2.70           | ~ (l1_pre_topc @ X0)
% 2.52/2.70           | ~ (v2_pre_topc @ X0)
% 2.52/2.70           | (v2_struct_0 @ X0)
% 2.52/2.70           | ~ (v1_funct_1 @ X2)
% 2.52/2.70           | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_D_1))
% 2.52/2.70           | ~ (m1_subset_1 @ X2 @ 
% 2.52/2.70                (k1_zfmisc_1 @ 
% 2.52/2.70                 (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_D_1))))
% 2.52/2.70           | (v1_funct_2 @ 
% 2.52/2.70              (k10_tmap_1 @ X0 @ sk_D_1 @ sk_B @ X1 @ sk_E_1 @ X2) @ 
% 2.52/2.70              (u1_struct_0 @ (k1_tsep_1 @ X0 @ sk_B @ X1)) @ 
% 2.52/2.70              (u1_struct_0 @ sk_D_1))))
% 2.52/2.70         <= (((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.70               (u1_struct_0 @ sk_D_1))) & 
% 2.52/2.70             ((m1_subset_1 @ sk_E_1 @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))))),
% 2.52/2.70      inference('sup-', [status(thm)], ['32', '36'])).
% 2.52/2.70  thf('38', plain,
% 2.52/2.70      ((![X0 : $i, X1 : $i, X2 : $i]:
% 2.52/2.70          ((v1_funct_2 @ 
% 2.52/2.70            (k10_tmap_1 @ X1 @ sk_D_1 @ sk_B @ X0 @ sk_E_1 @ X2) @ 
% 2.52/2.70            (u1_struct_0 @ (k1_tsep_1 @ X1 @ sk_B @ X0)) @ 
% 2.52/2.70            (u1_struct_0 @ sk_D_1))
% 2.52/2.70           | ~ (m1_subset_1 @ X2 @ 
% 2.52/2.70                (k1_zfmisc_1 @ 
% 2.52/2.70                 (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_D_1))))
% 2.52/2.70           | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_D_1))
% 2.52/2.70           | ~ (v1_funct_1 @ X2)
% 2.52/2.70           | (v2_struct_0 @ X1)
% 2.52/2.70           | ~ (v2_pre_topc @ X1)
% 2.52/2.70           | ~ (l1_pre_topc @ X1)
% 2.52/2.70           | (v2_struct_0 @ sk_D_1)
% 2.52/2.70           | ~ (v2_pre_topc @ sk_D_1)
% 2.52/2.70           | ~ (l1_pre_topc @ sk_D_1)
% 2.52/2.70           | (v2_struct_0 @ sk_B)
% 2.52/2.70           | ~ (m1_pre_topc @ sk_B @ X1)
% 2.52/2.70           | (v2_struct_0 @ X0)
% 2.52/2.70           | ~ (m1_pre_topc @ X0 @ X1)))
% 2.52/2.70         <= (((v1_funct_1 @ sk_E_1)) & 
% 2.52/2.70             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.70               (u1_struct_0 @ sk_D_1))) & 
% 2.52/2.70             ((m1_subset_1 @ sk_E_1 @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))))),
% 2.52/2.70      inference('sup-', [status(thm)], ['30', '37'])).
% 2.52/2.70  thf('39', plain,
% 2.52/2.70      ((![X0 : $i, X1 : $i, X2 : $i]:
% 2.52/2.70          (~ (m1_pre_topc @ X1 @ X0)
% 2.52/2.70           | (v2_struct_0 @ X1)
% 2.52/2.70           | ~ (m1_pre_topc @ sk_B @ X0)
% 2.52/2.70           | (v2_struct_0 @ sk_B)
% 2.52/2.70           | ~ (l1_pre_topc @ sk_D_1)
% 2.52/2.70           | (v2_struct_0 @ sk_D_1)
% 2.52/2.70           | ~ (l1_pre_topc @ X0)
% 2.52/2.70           | ~ (v2_pre_topc @ X0)
% 2.52/2.70           | (v2_struct_0 @ X0)
% 2.52/2.70           | ~ (v1_funct_1 @ X2)
% 2.52/2.70           | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_D_1))
% 2.52/2.70           | ~ (m1_subset_1 @ X2 @ 
% 2.52/2.70                (k1_zfmisc_1 @ 
% 2.52/2.70                 (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_D_1))))
% 2.52/2.70           | (v1_funct_2 @ 
% 2.52/2.70              (k10_tmap_1 @ X0 @ sk_D_1 @ sk_B @ X1 @ sk_E_1 @ X2) @ 
% 2.52/2.70              (u1_struct_0 @ (k1_tsep_1 @ X0 @ sk_B @ X1)) @ 
% 2.52/2.70              (u1_struct_0 @ sk_D_1))))
% 2.52/2.70         <= (((v1_funct_1 @ sk_E_1)) & 
% 2.52/2.70             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.70               (u1_struct_0 @ sk_D_1))) & 
% 2.52/2.70             ((m1_subset_1 @ sk_E_1 @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.70             ((v2_pre_topc @ sk_D_1)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['29', '38'])).
% 2.52/2.70  thf('40', plain,
% 2.52/2.70      ((![X0 : $i, X1 : $i, X2 : $i]:
% 2.52/2.70          ((v1_funct_2 @ 
% 2.52/2.70            (k10_tmap_1 @ X1 @ sk_D_1 @ sk_B @ X0 @ sk_E_1 @ X2) @ 
% 2.52/2.70            (u1_struct_0 @ (k1_tsep_1 @ X1 @ sk_B @ X0)) @ 
% 2.52/2.70            (u1_struct_0 @ sk_D_1))
% 2.52/2.70           | ~ (m1_subset_1 @ X2 @ 
% 2.52/2.70                (k1_zfmisc_1 @ 
% 2.52/2.70                 (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_D_1))))
% 2.52/2.70           | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_D_1))
% 2.52/2.70           | ~ (v1_funct_1 @ X2)
% 2.52/2.70           | (v2_struct_0 @ X1)
% 2.52/2.70           | ~ (v2_pre_topc @ X1)
% 2.52/2.70           | ~ (l1_pre_topc @ X1)
% 2.52/2.70           | (v2_struct_0 @ sk_D_1)
% 2.52/2.70           | (v2_struct_0 @ sk_B)
% 2.52/2.70           | ~ (m1_pre_topc @ sk_B @ X1)
% 2.52/2.70           | (v2_struct_0 @ X0)
% 2.52/2.70           | ~ (m1_pre_topc @ X0 @ X1)))
% 2.52/2.70         <= (((v1_funct_1 @ sk_E_1)) & 
% 2.52/2.70             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.70               (u1_struct_0 @ sk_D_1))) & 
% 2.52/2.70             ((m1_subset_1 @ sk_E_1 @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.70             ((l1_pre_topc @ sk_D_1)) & 
% 2.52/2.70             ((v2_pre_topc @ sk_D_1)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['27', '39'])).
% 2.52/2.70  thf('41', plain,
% 2.52/2.70      ((![X0 : $i]:
% 2.52/2.70          (~ (m1_pre_topc @ sk_C @ X0)
% 2.52/2.70           | (v2_struct_0 @ sk_C)
% 2.52/2.70           | ~ (m1_pre_topc @ sk_B @ X0)
% 2.52/2.70           | (v2_struct_0 @ sk_B)
% 2.52/2.70           | (v2_struct_0 @ sk_D_1)
% 2.52/2.70           | ~ (l1_pre_topc @ X0)
% 2.52/2.70           | ~ (v2_pre_topc @ X0)
% 2.52/2.70           | (v2_struct_0 @ X0)
% 2.52/2.70           | ~ (v1_funct_1 @ sk_F)
% 2.52/2.70           | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.70                (u1_struct_0 @ sk_D_1))
% 2.52/2.70           | (v1_funct_2 @ 
% 2.52/2.70              (k10_tmap_1 @ X0 @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F) @ 
% 2.52/2.70              (u1_struct_0 @ (k1_tsep_1 @ X0 @ sk_B @ sk_C)) @ 
% 2.52/2.70              (u1_struct_0 @ sk_D_1))))
% 2.52/2.70         <= (((v1_funct_1 @ sk_E_1)) & 
% 2.52/2.70             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.70               (u1_struct_0 @ sk_D_1))) & 
% 2.52/2.70             ((m1_subset_1 @ sk_E_1 @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.70             ((m1_subset_1 @ sk_F @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.70             ((l1_pre_topc @ sk_D_1)) & 
% 2.52/2.70             ((v2_pre_topc @ sk_D_1)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['25', '40'])).
% 2.52/2.70  thf('42', plain,
% 2.52/2.70      ((![X0 : $i]:
% 2.52/2.70          ((v1_funct_2 @ 
% 2.52/2.70            (k10_tmap_1 @ X0 @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F) @ 
% 2.52/2.70            (u1_struct_0 @ (k1_tsep_1 @ X0 @ sk_B @ sk_C)) @ 
% 2.52/2.70            (u1_struct_0 @ sk_D_1))
% 2.52/2.70           | ~ (v1_funct_1 @ sk_F)
% 2.52/2.70           | (v2_struct_0 @ X0)
% 2.52/2.70           | ~ (v2_pre_topc @ X0)
% 2.52/2.70           | ~ (l1_pre_topc @ X0)
% 2.52/2.70           | (v2_struct_0 @ sk_D_1)
% 2.52/2.70           | (v2_struct_0 @ sk_B)
% 2.52/2.70           | ~ (m1_pre_topc @ sk_B @ X0)
% 2.52/2.70           | (v2_struct_0 @ sk_C)
% 2.52/2.70           | ~ (m1_pre_topc @ sk_C @ X0)))
% 2.52/2.70         <= (((v1_funct_1 @ sk_E_1)) & 
% 2.52/2.70             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.70               (u1_struct_0 @ sk_D_1))) & 
% 2.52/2.70             ((m1_subset_1 @ sk_E_1 @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.70             ((m1_subset_1 @ sk_F @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.70             ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.70               (u1_struct_0 @ sk_D_1))) & 
% 2.52/2.70             ((l1_pre_topc @ sk_D_1)) & 
% 2.52/2.70             ((v2_pre_topc @ sk_D_1)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['23', '41'])).
% 2.52/2.70  thf('43', plain,
% 2.52/2.70      ((![X0 : $i]:
% 2.52/2.70          (~ (m1_pre_topc @ sk_C @ X0)
% 2.52/2.70           | (v2_struct_0 @ sk_C)
% 2.52/2.70           | ~ (m1_pre_topc @ sk_B @ X0)
% 2.52/2.70           | (v2_struct_0 @ sk_B)
% 2.52/2.70           | (v2_struct_0 @ sk_D_1)
% 2.52/2.70           | ~ (l1_pre_topc @ X0)
% 2.52/2.70           | ~ (v2_pre_topc @ X0)
% 2.52/2.70           | (v2_struct_0 @ X0)
% 2.52/2.70           | (v1_funct_2 @ 
% 2.52/2.70              (k10_tmap_1 @ X0 @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F) @ 
% 2.52/2.70              (u1_struct_0 @ (k1_tsep_1 @ X0 @ sk_B @ sk_C)) @ 
% 2.52/2.70              (u1_struct_0 @ sk_D_1))))
% 2.52/2.70         <= (((v1_funct_1 @ sk_E_1)) & 
% 2.52/2.70             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.70               (u1_struct_0 @ sk_D_1))) & 
% 2.52/2.70             ((m1_subset_1 @ sk_E_1 @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.70             ((m1_subset_1 @ sk_F @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.70             ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.70               (u1_struct_0 @ sk_D_1))) & 
% 2.52/2.70             ((v1_funct_1 @ sk_F)) & 
% 2.52/2.70             ((l1_pre_topc @ sk_D_1)) & 
% 2.52/2.70             ((v2_pre_topc @ sk_D_1)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['21', '42'])).
% 2.52/2.70  thf('44', plain,
% 2.52/2.70      ((((v1_funct_2 @ 
% 2.52/2.70          (k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F) @ 
% 2.52/2.70          (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.52/2.70          (u1_struct_0 @ sk_D_1))
% 2.52/2.70         | (v2_struct_0 @ sk_A)
% 2.52/2.70         | ~ (v2_pre_topc @ sk_A)
% 2.52/2.70         | ~ (l1_pre_topc @ sk_A)
% 2.52/2.70         | (v2_struct_0 @ sk_D_1)
% 2.52/2.70         | (v2_struct_0 @ sk_B)
% 2.52/2.70         | ~ (m1_pre_topc @ sk_B @ sk_A)
% 2.52/2.70         | (v2_struct_0 @ sk_C)))
% 2.52/2.70         <= (((v1_funct_1 @ sk_E_1)) & 
% 2.52/2.70             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.70               (u1_struct_0 @ sk_D_1))) & 
% 2.52/2.70             ((m1_subset_1 @ sk_E_1 @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.70             ((m1_subset_1 @ sk_F @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.70             ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.70               (u1_struct_0 @ sk_D_1))) & 
% 2.52/2.70             ((v1_funct_1 @ sk_F)) & 
% 2.52/2.70             ((l1_pre_topc @ sk_D_1)) & 
% 2.52/2.70             ((v2_pre_topc @ sk_D_1)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['19', '43'])).
% 2.52/2.70  thf('45', plain, ((v2_pre_topc @ sk_A)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('47', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('48', plain,
% 2.52/2.70      ((((v1_funct_2 @ 
% 2.52/2.70          (k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F) @ 
% 2.52/2.70          (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.52/2.70          (u1_struct_0 @ sk_D_1))
% 2.52/2.70         | (v2_struct_0 @ sk_A)
% 2.52/2.70         | (v2_struct_0 @ sk_D_1)
% 2.52/2.70         | (v2_struct_0 @ sk_B)
% 2.52/2.70         | (v2_struct_0 @ sk_C)))
% 2.52/2.70         <= (((v1_funct_1 @ sk_E_1)) & 
% 2.52/2.70             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.70               (u1_struct_0 @ sk_D_1))) & 
% 2.52/2.70             ((m1_subset_1 @ sk_E_1 @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.70             ((m1_subset_1 @ sk_F @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.70             ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.70               (u1_struct_0 @ sk_D_1))) & 
% 2.52/2.70             ((v1_funct_1 @ sk_F)) & 
% 2.52/2.70             ((l1_pre_topc @ sk_D_1)) & 
% 2.52/2.70             ((v2_pre_topc @ sk_D_1)))),
% 2.52/2.70      inference('demod', [status(thm)], ['44', '45', '46', '47'])).
% 2.52/2.70  thf('49', plain,
% 2.52/2.70      ((~ (m1_subset_1 @ 
% 2.52/2.70           (k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F) @ 
% 2.52/2.70           (k1_zfmisc_1 @ 
% 2.52/2.70            (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.52/2.70             (u1_struct_0 @ sk_D_1))))
% 2.52/2.70        | ~ (v5_pre_topc @ 
% 2.52/2.70             (k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F) @ 
% 2.52/2.70             (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D_1)
% 2.52/2.70        | ~ (v1_funct_2 @ 
% 2.52/2.70             (k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F) @ 
% 2.52/2.70             (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.52/2.70             (u1_struct_0 @ sk_D_1))
% 2.52/2.70        | ~ (v1_funct_1 @ 
% 2.52/2.70             (k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F))
% 2.52/2.70        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 2.52/2.70        | ~ (r3_tsep_1 @ sk_A @ sk_B @ sk_C))),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('50', plain,
% 2.52/2.70      ((~ (v1_funct_2 @ 
% 2.52/2.70           (k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F) @ 
% 2.52/2.70           (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.52/2.70           (u1_struct_0 @ sk_D_1)))
% 2.52/2.70         <= (~
% 2.52/2.70             ((v1_funct_2 @ 
% 2.52/2.70               (k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F) @ 
% 2.52/2.70               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.52/2.70               (u1_struct_0 @ sk_D_1))))),
% 2.52/2.70      inference('split', [status(esa)], ['49'])).
% 2.52/2.70  thf('51', plain,
% 2.52/2.70      ((((v2_struct_0 @ sk_C)
% 2.52/2.70         | (v2_struct_0 @ sk_B)
% 2.52/2.70         | (v2_struct_0 @ sk_D_1)
% 2.52/2.70         | (v2_struct_0 @ sk_A)))
% 2.52/2.70         <= (~
% 2.52/2.70             ((v1_funct_2 @ 
% 2.52/2.70               (k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F) @ 
% 2.52/2.70               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.52/2.70               (u1_struct_0 @ sk_D_1))) & 
% 2.52/2.70             ((v1_funct_1 @ sk_E_1)) & 
% 2.52/2.70             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.70               (u1_struct_0 @ sk_D_1))) & 
% 2.52/2.70             ((m1_subset_1 @ sk_E_1 @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.70             ((m1_subset_1 @ sk_F @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.70             ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.70               (u1_struct_0 @ sk_D_1))) & 
% 2.52/2.70             ((v1_funct_1 @ sk_F)) & 
% 2.52/2.70             ((l1_pre_topc @ sk_D_1)) & 
% 2.52/2.70             ((v2_pre_topc @ sk_D_1)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['48', '50'])).
% 2.52/2.70  thf('52', plain,
% 2.52/2.70      ((~ (v2_struct_0 @ sk_D_1)
% 2.52/2.70        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 2.52/2.70        | ~ (r3_tsep_1 @ sk_A @ sk_B @ sk_C))),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('53', plain,
% 2.52/2.70      ((~ (v2_struct_0 @ sk_D_1)) <= (~ ((v2_struct_0 @ sk_D_1)))),
% 2.52/2.70      inference('split', [status(esa)], ['52'])).
% 2.52/2.70  thf('54', plain,
% 2.52/2.70      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C)))
% 2.52/2.70         <= (~ ((v2_struct_0 @ sk_D_1)) & 
% 2.52/2.70             ~
% 2.52/2.70             ((v1_funct_2 @ 
% 2.52/2.70               (k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F) @ 
% 2.52/2.70               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.52/2.70               (u1_struct_0 @ sk_D_1))) & 
% 2.52/2.70             ((v1_funct_1 @ sk_E_1)) & 
% 2.52/2.70             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.70               (u1_struct_0 @ sk_D_1))) & 
% 2.52/2.70             ((m1_subset_1 @ sk_E_1 @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.70             ((m1_subset_1 @ sk_F @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.70             ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.70               (u1_struct_0 @ sk_D_1))) & 
% 2.52/2.70             ((v1_funct_1 @ sk_F)) & 
% 2.52/2.70             ((l1_pre_topc @ sk_D_1)) & 
% 2.52/2.70             ((v2_pre_topc @ sk_D_1)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['51', '53'])).
% 2.52/2.70  thf('55', plain, (~ (v2_struct_0 @ sk_A)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('56', plain,
% 2.52/2.70      ((((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B)))
% 2.52/2.70         <= (~ ((v2_struct_0 @ sk_D_1)) & 
% 2.52/2.70             ~
% 2.52/2.70             ((v1_funct_2 @ 
% 2.52/2.70               (k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F) @ 
% 2.52/2.70               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.52/2.70               (u1_struct_0 @ sk_D_1))) & 
% 2.52/2.70             ((v1_funct_1 @ sk_E_1)) & 
% 2.52/2.70             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.70               (u1_struct_0 @ sk_D_1))) & 
% 2.52/2.70             ((m1_subset_1 @ sk_E_1 @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.70             ((m1_subset_1 @ sk_F @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.70             ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.70               (u1_struct_0 @ sk_D_1))) & 
% 2.52/2.70             ((v1_funct_1 @ sk_F)) & 
% 2.52/2.70             ((l1_pre_topc @ sk_D_1)) & 
% 2.52/2.70             ((v2_pre_topc @ sk_D_1)))),
% 2.52/2.70      inference('clc', [status(thm)], ['54', '55'])).
% 2.52/2.70  thf('57', plain, (~ (v2_struct_0 @ sk_C)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('58', plain,
% 2.52/2.70      (((v2_struct_0 @ sk_B))
% 2.52/2.70         <= (~ ((v2_struct_0 @ sk_D_1)) & 
% 2.52/2.70             ~
% 2.52/2.70             ((v1_funct_2 @ 
% 2.52/2.70               (k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F) @ 
% 2.52/2.70               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.52/2.70               (u1_struct_0 @ sk_D_1))) & 
% 2.52/2.70             ((v1_funct_1 @ sk_E_1)) & 
% 2.52/2.70             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.70               (u1_struct_0 @ sk_D_1))) & 
% 2.52/2.70             ((m1_subset_1 @ sk_E_1 @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.70             ((m1_subset_1 @ sk_F @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.70             ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.70               (u1_struct_0 @ sk_D_1))) & 
% 2.52/2.70             ((v1_funct_1 @ sk_F)) & 
% 2.52/2.70             ((l1_pre_topc @ sk_D_1)) & 
% 2.52/2.70             ((v2_pre_topc @ sk_D_1)))),
% 2.52/2.70      inference('clc', [status(thm)], ['56', '57'])).
% 2.52/2.70  thf('59', plain, (~ (v2_struct_0 @ sk_B)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('60', plain,
% 2.52/2.70      (((v1_funct_2 @ 
% 2.52/2.70         (k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F) @ 
% 2.52/2.70         (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.52/2.70         (u1_struct_0 @ sk_D_1))) | 
% 2.52/2.70       ~ ((v1_funct_1 @ sk_E_1)) | ~ ((v2_pre_topc @ sk_D_1)) | 
% 2.52/2.70       ~ ((l1_pre_topc @ sk_D_1)) | ~ ((v1_funct_1 @ sk_F)) | 
% 2.52/2.70       ~ ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))) | 
% 2.52/2.70       ~
% 2.52/2.70       ((m1_subset_1 @ sk_F @ 
% 2.52/2.70         (k1_zfmisc_1 @ 
% 2.52/2.70          (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) | 
% 2.52/2.70       ~
% 2.52/2.70       ((m1_subset_1 @ sk_E_1 @ 
% 2.52/2.70         (k1_zfmisc_1 @ 
% 2.52/2.70          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) | 
% 2.52/2.70       ~
% 2.52/2.70       ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))) | 
% 2.52/2.70       ((v2_struct_0 @ sk_D_1))),
% 2.52/2.70      inference('sup-', [status(thm)], ['58', '59'])).
% 2.52/2.70  thf('61', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('62', plain, (((v1_funct_1 @ sk_F)) <= (((v1_funct_1 @ sk_F)))),
% 2.52/2.70      inference('split', [status(esa)], ['20'])).
% 2.52/2.70  thf('63', plain,
% 2.52/2.70      (((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1)))
% 2.52/2.70         <= (((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.70               (u1_struct_0 @ sk_D_1))))),
% 2.52/2.70      inference('split', [status(esa)], ['22'])).
% 2.52/2.70  thf('64', plain,
% 2.52/2.70      (((m1_subset_1 @ sk_F @ 
% 2.52/2.70         (k1_zfmisc_1 @ 
% 2.52/2.70          (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1)))))
% 2.52/2.70         <= (((m1_subset_1 @ sk_F @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))))),
% 2.52/2.70      inference('split', [status(esa)], ['24'])).
% 2.52/2.70  thf('65', plain, (((l1_pre_topc @ sk_D_1)) <= (((l1_pre_topc @ sk_D_1)))),
% 2.52/2.70      inference('split', [status(esa)], ['26'])).
% 2.52/2.70  thf('66', plain, (((v2_pre_topc @ sk_D_1)) <= (((v2_pre_topc @ sk_D_1)))),
% 2.52/2.70      inference('split', [status(esa)], ['28'])).
% 2.52/2.70  thf('67', plain, (((v1_funct_1 @ sk_E_1)) <= (((v1_funct_1 @ sk_E_1)))),
% 2.52/2.70      inference('split', [status(esa)], ['10'])).
% 2.52/2.70  thf('68', plain,
% 2.52/2.70      (((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1)))
% 2.52/2.70         <= (((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.70               (u1_struct_0 @ sk_D_1))))),
% 2.52/2.70      inference('split', [status(esa)], ['31'])).
% 2.52/2.70  thf('69', plain,
% 2.52/2.70      (((m1_subset_1 @ sk_E_1 @ 
% 2.52/2.70         (k1_zfmisc_1 @ 
% 2.52/2.70          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1)))))
% 2.52/2.70         <= (((m1_subset_1 @ sk_E_1 @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))))),
% 2.52/2.70      inference('split', [status(esa)], ['33'])).
% 2.52/2.70  thf('70', plain,
% 2.52/2.70      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 2.52/2.70         (~ (m1_subset_1 @ X4 @ 
% 2.52/2.70             (k1_zfmisc_1 @ 
% 2.52/2.70              (k2_zfmisc_1 @ (u1_struct_0 @ X5) @ (u1_struct_0 @ X6))))
% 2.52/2.70          | ~ (v1_funct_2 @ X4 @ (u1_struct_0 @ X5) @ (u1_struct_0 @ X6))
% 2.52/2.70          | ~ (v1_funct_1 @ X4)
% 2.52/2.70          | ~ (m1_pre_topc @ X7 @ X8)
% 2.52/2.70          | (v2_struct_0 @ X7)
% 2.52/2.70          | ~ (m1_pre_topc @ X5 @ X8)
% 2.52/2.70          | (v2_struct_0 @ X5)
% 2.52/2.70          | ~ (l1_pre_topc @ X6)
% 2.52/2.70          | ~ (v2_pre_topc @ X6)
% 2.52/2.70          | (v2_struct_0 @ X6)
% 2.52/2.70          | ~ (l1_pre_topc @ X8)
% 2.52/2.70          | ~ (v2_pre_topc @ X8)
% 2.52/2.70          | (v2_struct_0 @ X8)
% 2.52/2.70          | ~ (v1_funct_1 @ X9)
% 2.52/2.70          | ~ (v1_funct_2 @ X9 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X6))
% 2.52/2.70          | ~ (m1_subset_1 @ X9 @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X6))))
% 2.52/2.70          | (m1_subset_1 @ (k10_tmap_1 @ X8 @ X6 @ X5 @ X7 @ X4 @ X9) @ 
% 2.52/2.70             (k1_zfmisc_1 @ 
% 2.52/2.70              (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X8 @ X5 @ X7)) @ 
% 2.52/2.70               (u1_struct_0 @ X6)))))),
% 2.52/2.70      inference('cnf', [status(esa)], [dt_k10_tmap_1])).
% 2.52/2.70  thf('71', plain,
% 2.52/2.70      ((![X0 : $i, X1 : $i, X2 : $i]:
% 2.52/2.70          ((m1_subset_1 @ 
% 2.52/2.70            (k10_tmap_1 @ X1 @ sk_D_1 @ sk_B @ X0 @ sk_E_1 @ X2) @ 
% 2.52/2.70            (k1_zfmisc_1 @ 
% 2.52/2.70             (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X1 @ sk_B @ X0)) @ 
% 2.52/2.70              (u1_struct_0 @ sk_D_1))))
% 2.52/2.70           | ~ (m1_subset_1 @ X2 @ 
% 2.52/2.70                (k1_zfmisc_1 @ 
% 2.52/2.70                 (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_D_1))))
% 2.52/2.70           | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_D_1))
% 2.52/2.70           | ~ (v1_funct_1 @ X2)
% 2.52/2.70           | (v2_struct_0 @ X1)
% 2.52/2.70           | ~ (v2_pre_topc @ X1)
% 2.52/2.70           | ~ (l1_pre_topc @ X1)
% 2.52/2.70           | (v2_struct_0 @ sk_D_1)
% 2.52/2.70           | ~ (v2_pre_topc @ sk_D_1)
% 2.52/2.70           | ~ (l1_pre_topc @ sk_D_1)
% 2.52/2.70           | (v2_struct_0 @ sk_B)
% 2.52/2.70           | ~ (m1_pre_topc @ sk_B @ X1)
% 2.52/2.70           | (v2_struct_0 @ X0)
% 2.52/2.70           | ~ (m1_pre_topc @ X0 @ X1)
% 2.52/2.70           | ~ (v1_funct_1 @ sk_E_1)
% 2.52/2.70           | ~ (v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.70                (u1_struct_0 @ sk_D_1))))
% 2.52/2.70         <= (((m1_subset_1 @ sk_E_1 @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))))),
% 2.52/2.70      inference('sup-', [status(thm)], ['69', '70'])).
% 2.52/2.70  thf('72', plain,
% 2.52/2.70      ((![X0 : $i, X1 : $i, X2 : $i]:
% 2.52/2.70          (~ (v1_funct_1 @ sk_E_1)
% 2.52/2.70           | ~ (m1_pre_topc @ X1 @ X0)
% 2.52/2.70           | (v2_struct_0 @ X1)
% 2.52/2.70           | ~ (m1_pre_topc @ sk_B @ X0)
% 2.52/2.70           | (v2_struct_0 @ sk_B)
% 2.52/2.70           | ~ (l1_pre_topc @ sk_D_1)
% 2.52/2.70           | ~ (v2_pre_topc @ sk_D_1)
% 2.52/2.70           | (v2_struct_0 @ sk_D_1)
% 2.52/2.70           | ~ (l1_pre_topc @ X0)
% 2.52/2.70           | ~ (v2_pre_topc @ X0)
% 2.52/2.70           | (v2_struct_0 @ X0)
% 2.52/2.70           | ~ (v1_funct_1 @ X2)
% 2.52/2.70           | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_D_1))
% 2.52/2.70           | ~ (m1_subset_1 @ X2 @ 
% 2.52/2.70                (k1_zfmisc_1 @ 
% 2.52/2.70                 (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_D_1))))
% 2.52/2.70           | (m1_subset_1 @ 
% 2.52/2.70              (k10_tmap_1 @ X0 @ sk_D_1 @ sk_B @ X1 @ sk_E_1 @ X2) @ 
% 2.52/2.70              (k1_zfmisc_1 @ 
% 2.52/2.70               (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X0 @ sk_B @ X1)) @ 
% 2.52/2.70                (u1_struct_0 @ sk_D_1))))))
% 2.52/2.70         <= (((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.70               (u1_struct_0 @ sk_D_1))) & 
% 2.52/2.70             ((m1_subset_1 @ sk_E_1 @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))))),
% 2.52/2.70      inference('sup-', [status(thm)], ['68', '71'])).
% 2.52/2.70  thf('73', plain,
% 2.52/2.70      ((![X0 : $i, X1 : $i, X2 : $i]:
% 2.52/2.70          ((m1_subset_1 @ 
% 2.52/2.70            (k10_tmap_1 @ X1 @ sk_D_1 @ sk_B @ X0 @ sk_E_1 @ X2) @ 
% 2.52/2.70            (k1_zfmisc_1 @ 
% 2.52/2.70             (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X1 @ sk_B @ X0)) @ 
% 2.52/2.70              (u1_struct_0 @ sk_D_1))))
% 2.52/2.70           | ~ (m1_subset_1 @ X2 @ 
% 2.52/2.70                (k1_zfmisc_1 @ 
% 2.52/2.70                 (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_D_1))))
% 2.52/2.70           | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_D_1))
% 2.52/2.70           | ~ (v1_funct_1 @ X2)
% 2.52/2.70           | (v2_struct_0 @ X1)
% 2.52/2.70           | ~ (v2_pre_topc @ X1)
% 2.52/2.70           | ~ (l1_pre_topc @ X1)
% 2.52/2.70           | (v2_struct_0 @ sk_D_1)
% 2.52/2.70           | ~ (v2_pre_topc @ sk_D_1)
% 2.52/2.70           | ~ (l1_pre_topc @ sk_D_1)
% 2.52/2.70           | (v2_struct_0 @ sk_B)
% 2.52/2.70           | ~ (m1_pre_topc @ sk_B @ X1)
% 2.52/2.70           | (v2_struct_0 @ X0)
% 2.52/2.70           | ~ (m1_pre_topc @ X0 @ X1)))
% 2.52/2.70         <= (((v1_funct_1 @ sk_E_1)) & 
% 2.52/2.70             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.70               (u1_struct_0 @ sk_D_1))) & 
% 2.52/2.70             ((m1_subset_1 @ sk_E_1 @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))))),
% 2.52/2.70      inference('sup-', [status(thm)], ['67', '72'])).
% 2.52/2.70  thf('74', plain,
% 2.52/2.70      ((![X0 : $i, X1 : $i, X2 : $i]:
% 2.52/2.70          (~ (m1_pre_topc @ X1 @ X0)
% 2.52/2.70           | (v2_struct_0 @ X1)
% 2.52/2.70           | ~ (m1_pre_topc @ sk_B @ X0)
% 2.52/2.70           | (v2_struct_0 @ sk_B)
% 2.52/2.70           | ~ (l1_pre_topc @ sk_D_1)
% 2.52/2.70           | (v2_struct_0 @ sk_D_1)
% 2.52/2.70           | ~ (l1_pre_topc @ X0)
% 2.52/2.70           | ~ (v2_pre_topc @ X0)
% 2.52/2.70           | (v2_struct_0 @ X0)
% 2.52/2.70           | ~ (v1_funct_1 @ X2)
% 2.52/2.70           | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_D_1))
% 2.52/2.70           | ~ (m1_subset_1 @ X2 @ 
% 2.52/2.70                (k1_zfmisc_1 @ 
% 2.52/2.70                 (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_D_1))))
% 2.52/2.70           | (m1_subset_1 @ 
% 2.52/2.70              (k10_tmap_1 @ X0 @ sk_D_1 @ sk_B @ X1 @ sk_E_1 @ X2) @ 
% 2.52/2.70              (k1_zfmisc_1 @ 
% 2.52/2.70               (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X0 @ sk_B @ X1)) @ 
% 2.52/2.70                (u1_struct_0 @ sk_D_1))))))
% 2.52/2.70         <= (((v1_funct_1 @ sk_E_1)) & 
% 2.52/2.70             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.70               (u1_struct_0 @ sk_D_1))) & 
% 2.52/2.70             ((m1_subset_1 @ sk_E_1 @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.70             ((v2_pre_topc @ sk_D_1)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['66', '73'])).
% 2.52/2.70  thf('75', plain,
% 2.52/2.70      ((![X0 : $i, X1 : $i, X2 : $i]:
% 2.52/2.70          ((m1_subset_1 @ 
% 2.52/2.70            (k10_tmap_1 @ X1 @ sk_D_1 @ sk_B @ X0 @ sk_E_1 @ X2) @ 
% 2.52/2.70            (k1_zfmisc_1 @ 
% 2.52/2.70             (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X1 @ sk_B @ X0)) @ 
% 2.52/2.70              (u1_struct_0 @ sk_D_1))))
% 2.52/2.70           | ~ (m1_subset_1 @ X2 @ 
% 2.52/2.70                (k1_zfmisc_1 @ 
% 2.52/2.70                 (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_D_1))))
% 2.52/2.70           | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_D_1))
% 2.52/2.70           | ~ (v1_funct_1 @ X2)
% 2.52/2.70           | (v2_struct_0 @ X1)
% 2.52/2.70           | ~ (v2_pre_topc @ X1)
% 2.52/2.70           | ~ (l1_pre_topc @ X1)
% 2.52/2.70           | (v2_struct_0 @ sk_D_1)
% 2.52/2.70           | (v2_struct_0 @ sk_B)
% 2.52/2.70           | ~ (m1_pre_topc @ sk_B @ X1)
% 2.52/2.70           | (v2_struct_0 @ X0)
% 2.52/2.70           | ~ (m1_pre_topc @ X0 @ X1)))
% 2.52/2.70         <= (((v1_funct_1 @ sk_E_1)) & 
% 2.52/2.70             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.70               (u1_struct_0 @ sk_D_1))) & 
% 2.52/2.70             ((m1_subset_1 @ sk_E_1 @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.70             ((l1_pre_topc @ sk_D_1)) & 
% 2.52/2.70             ((v2_pre_topc @ sk_D_1)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['65', '74'])).
% 2.52/2.70  thf('76', plain,
% 2.52/2.70      ((![X0 : $i]:
% 2.52/2.70          (~ (m1_pre_topc @ sk_C @ X0)
% 2.52/2.70           | (v2_struct_0 @ sk_C)
% 2.52/2.70           | ~ (m1_pre_topc @ sk_B @ X0)
% 2.52/2.70           | (v2_struct_0 @ sk_B)
% 2.52/2.70           | (v2_struct_0 @ sk_D_1)
% 2.52/2.70           | ~ (l1_pre_topc @ X0)
% 2.52/2.70           | ~ (v2_pre_topc @ X0)
% 2.52/2.70           | (v2_struct_0 @ X0)
% 2.52/2.70           | ~ (v1_funct_1 @ sk_F)
% 2.52/2.70           | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.70                (u1_struct_0 @ sk_D_1))
% 2.52/2.70           | (m1_subset_1 @ 
% 2.52/2.70              (k10_tmap_1 @ X0 @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F) @ 
% 2.52/2.70              (k1_zfmisc_1 @ 
% 2.52/2.70               (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X0 @ sk_B @ sk_C)) @ 
% 2.52/2.70                (u1_struct_0 @ sk_D_1))))))
% 2.52/2.70         <= (((v1_funct_1 @ sk_E_1)) & 
% 2.52/2.70             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.70               (u1_struct_0 @ sk_D_1))) & 
% 2.52/2.70             ((m1_subset_1 @ sk_E_1 @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.70             ((m1_subset_1 @ sk_F @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.70             ((l1_pre_topc @ sk_D_1)) & 
% 2.52/2.70             ((v2_pre_topc @ sk_D_1)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['64', '75'])).
% 2.52/2.70  thf('77', plain,
% 2.52/2.70      ((![X0 : $i]:
% 2.52/2.70          ((m1_subset_1 @ 
% 2.52/2.70            (k10_tmap_1 @ X0 @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F) @ 
% 2.52/2.70            (k1_zfmisc_1 @ 
% 2.52/2.70             (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X0 @ sk_B @ sk_C)) @ 
% 2.52/2.70              (u1_struct_0 @ sk_D_1))))
% 2.52/2.70           | ~ (v1_funct_1 @ sk_F)
% 2.52/2.70           | (v2_struct_0 @ X0)
% 2.52/2.70           | ~ (v2_pre_topc @ X0)
% 2.52/2.70           | ~ (l1_pre_topc @ X0)
% 2.52/2.70           | (v2_struct_0 @ sk_D_1)
% 2.52/2.70           | (v2_struct_0 @ sk_B)
% 2.52/2.70           | ~ (m1_pre_topc @ sk_B @ X0)
% 2.52/2.70           | (v2_struct_0 @ sk_C)
% 2.52/2.70           | ~ (m1_pre_topc @ sk_C @ X0)))
% 2.52/2.70         <= (((v1_funct_1 @ sk_E_1)) & 
% 2.52/2.70             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.70               (u1_struct_0 @ sk_D_1))) & 
% 2.52/2.70             ((m1_subset_1 @ sk_E_1 @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.70             ((m1_subset_1 @ sk_F @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.70             ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.70               (u1_struct_0 @ sk_D_1))) & 
% 2.52/2.70             ((l1_pre_topc @ sk_D_1)) & 
% 2.52/2.70             ((v2_pre_topc @ sk_D_1)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['63', '76'])).
% 2.52/2.70  thf('78', plain,
% 2.52/2.70      ((![X0 : $i]:
% 2.52/2.70          (~ (m1_pre_topc @ sk_C @ X0)
% 2.52/2.70           | (v2_struct_0 @ sk_C)
% 2.52/2.70           | ~ (m1_pre_topc @ sk_B @ X0)
% 2.52/2.70           | (v2_struct_0 @ sk_B)
% 2.52/2.70           | (v2_struct_0 @ sk_D_1)
% 2.52/2.70           | ~ (l1_pre_topc @ X0)
% 2.52/2.70           | ~ (v2_pre_topc @ X0)
% 2.52/2.70           | (v2_struct_0 @ X0)
% 2.52/2.70           | (m1_subset_1 @ 
% 2.52/2.70              (k10_tmap_1 @ X0 @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F) @ 
% 2.52/2.70              (k1_zfmisc_1 @ 
% 2.52/2.70               (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X0 @ sk_B @ sk_C)) @ 
% 2.52/2.70                (u1_struct_0 @ sk_D_1))))))
% 2.52/2.70         <= (((v1_funct_1 @ sk_E_1)) & 
% 2.52/2.70             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.70               (u1_struct_0 @ sk_D_1))) & 
% 2.52/2.70             ((m1_subset_1 @ sk_E_1 @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.70             ((m1_subset_1 @ sk_F @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.70             ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.70               (u1_struct_0 @ sk_D_1))) & 
% 2.52/2.70             ((v1_funct_1 @ sk_F)) & 
% 2.52/2.70             ((l1_pre_topc @ sk_D_1)) & 
% 2.52/2.70             ((v2_pre_topc @ sk_D_1)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['62', '77'])).
% 2.52/2.70  thf('79', plain,
% 2.52/2.70      ((((m1_subset_1 @ 
% 2.52/2.70          (k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F) @ 
% 2.52/2.70          (k1_zfmisc_1 @ 
% 2.52/2.70           (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.52/2.70            (u1_struct_0 @ sk_D_1))))
% 2.52/2.70         | (v2_struct_0 @ sk_A)
% 2.52/2.70         | ~ (v2_pre_topc @ sk_A)
% 2.52/2.70         | ~ (l1_pre_topc @ sk_A)
% 2.52/2.70         | (v2_struct_0 @ sk_D_1)
% 2.52/2.70         | (v2_struct_0 @ sk_B)
% 2.52/2.70         | ~ (m1_pre_topc @ sk_B @ sk_A)
% 2.52/2.70         | (v2_struct_0 @ sk_C)))
% 2.52/2.70         <= (((v1_funct_1 @ sk_E_1)) & 
% 2.52/2.70             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.70               (u1_struct_0 @ sk_D_1))) & 
% 2.52/2.70             ((m1_subset_1 @ sk_E_1 @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.70             ((m1_subset_1 @ sk_F @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.70             ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.70               (u1_struct_0 @ sk_D_1))) & 
% 2.52/2.70             ((v1_funct_1 @ sk_F)) & 
% 2.52/2.70             ((l1_pre_topc @ sk_D_1)) & 
% 2.52/2.70             ((v2_pre_topc @ sk_D_1)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['61', '78'])).
% 2.52/2.70  thf('80', plain, ((v2_pre_topc @ sk_A)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('81', plain, ((l1_pre_topc @ sk_A)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('82', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('83', plain,
% 2.52/2.70      ((((m1_subset_1 @ 
% 2.52/2.70          (k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F) @ 
% 2.52/2.70          (k1_zfmisc_1 @ 
% 2.52/2.70           (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.52/2.70            (u1_struct_0 @ sk_D_1))))
% 2.52/2.70         | (v2_struct_0 @ sk_A)
% 2.52/2.70         | (v2_struct_0 @ sk_D_1)
% 2.52/2.70         | (v2_struct_0 @ sk_B)
% 2.52/2.70         | (v2_struct_0 @ sk_C)))
% 2.52/2.70         <= (((v1_funct_1 @ sk_E_1)) & 
% 2.52/2.70             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.70               (u1_struct_0 @ sk_D_1))) & 
% 2.52/2.70             ((m1_subset_1 @ sk_E_1 @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.70             ((m1_subset_1 @ sk_F @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.70             ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.70               (u1_struct_0 @ sk_D_1))) & 
% 2.52/2.70             ((v1_funct_1 @ sk_F)) & 
% 2.52/2.70             ((l1_pre_topc @ sk_D_1)) & 
% 2.52/2.70             ((v2_pre_topc @ sk_D_1)))),
% 2.52/2.70      inference('demod', [status(thm)], ['79', '80', '81', '82'])).
% 2.52/2.70  thf('84', plain,
% 2.52/2.70      ((~ (m1_subset_1 @ 
% 2.52/2.70           (k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F) @ 
% 2.52/2.70           (k1_zfmisc_1 @ 
% 2.52/2.70            (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.52/2.70             (u1_struct_0 @ sk_D_1)))))
% 2.52/2.70         <= (~
% 2.52/2.70             ((m1_subset_1 @ 
% 2.52/2.70               (k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F) @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ 
% 2.52/2.70                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.52/2.70                 (u1_struct_0 @ sk_D_1))))))),
% 2.52/2.70      inference('split', [status(esa)], ['49'])).
% 2.52/2.70  thf('85', plain,
% 2.52/2.70      ((((v2_struct_0 @ sk_C)
% 2.52/2.70         | (v2_struct_0 @ sk_B)
% 2.52/2.70         | (v2_struct_0 @ sk_D_1)
% 2.52/2.70         | (v2_struct_0 @ sk_A)))
% 2.52/2.70         <= (~
% 2.52/2.70             ((m1_subset_1 @ 
% 2.52/2.70               (k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F) @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ 
% 2.52/2.70                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.52/2.70                 (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.70             ((v1_funct_1 @ sk_E_1)) & 
% 2.52/2.70             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.70               (u1_struct_0 @ sk_D_1))) & 
% 2.52/2.70             ((m1_subset_1 @ sk_E_1 @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.70             ((m1_subset_1 @ sk_F @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.70             ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.70               (u1_struct_0 @ sk_D_1))) & 
% 2.52/2.70             ((v1_funct_1 @ sk_F)) & 
% 2.52/2.70             ((l1_pre_topc @ sk_D_1)) & 
% 2.52/2.70             ((v2_pre_topc @ sk_D_1)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['83', '84'])).
% 2.52/2.70  thf('86', plain,
% 2.52/2.70      ((~ (v2_struct_0 @ sk_D_1)) <= (~ ((v2_struct_0 @ sk_D_1)))),
% 2.52/2.70      inference('split', [status(esa)], ['52'])).
% 2.52/2.70  thf('87', plain,
% 2.52/2.70      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C)))
% 2.52/2.70         <= (~ ((v2_struct_0 @ sk_D_1)) & 
% 2.52/2.70             ~
% 2.52/2.70             ((m1_subset_1 @ 
% 2.52/2.70               (k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F) @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ 
% 2.52/2.70                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.52/2.70                 (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.70             ((v1_funct_1 @ sk_E_1)) & 
% 2.52/2.70             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.70               (u1_struct_0 @ sk_D_1))) & 
% 2.52/2.70             ((m1_subset_1 @ sk_E_1 @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.70             ((m1_subset_1 @ sk_F @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.70             ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.70               (u1_struct_0 @ sk_D_1))) & 
% 2.52/2.70             ((v1_funct_1 @ sk_F)) & 
% 2.52/2.70             ((l1_pre_topc @ sk_D_1)) & 
% 2.52/2.70             ((v2_pre_topc @ sk_D_1)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['85', '86'])).
% 2.52/2.70  thf('88', plain, (~ (v2_struct_0 @ sk_A)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('89', plain,
% 2.52/2.70      ((((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B)))
% 2.52/2.70         <= (~ ((v2_struct_0 @ sk_D_1)) & 
% 2.52/2.70             ~
% 2.52/2.70             ((m1_subset_1 @ 
% 2.52/2.70               (k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F) @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ 
% 2.52/2.70                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.52/2.70                 (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.70             ((v1_funct_1 @ sk_E_1)) & 
% 2.52/2.70             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.70               (u1_struct_0 @ sk_D_1))) & 
% 2.52/2.70             ((m1_subset_1 @ sk_E_1 @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.70             ((m1_subset_1 @ sk_F @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.70             ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.70               (u1_struct_0 @ sk_D_1))) & 
% 2.52/2.70             ((v1_funct_1 @ sk_F)) & 
% 2.52/2.70             ((l1_pre_topc @ sk_D_1)) & 
% 2.52/2.70             ((v2_pre_topc @ sk_D_1)))),
% 2.52/2.70      inference('clc', [status(thm)], ['87', '88'])).
% 2.52/2.70  thf('90', plain, (~ (v2_struct_0 @ sk_C)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('91', plain,
% 2.52/2.70      (((v2_struct_0 @ sk_B))
% 2.52/2.70         <= (~ ((v2_struct_0 @ sk_D_1)) & 
% 2.52/2.70             ~
% 2.52/2.70             ((m1_subset_1 @ 
% 2.52/2.70               (k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F) @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ 
% 2.52/2.70                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.52/2.70                 (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.70             ((v1_funct_1 @ sk_E_1)) & 
% 2.52/2.70             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.70               (u1_struct_0 @ sk_D_1))) & 
% 2.52/2.70             ((m1_subset_1 @ sk_E_1 @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.70             ((m1_subset_1 @ sk_F @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.70             ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.70               (u1_struct_0 @ sk_D_1))) & 
% 2.52/2.70             ((v1_funct_1 @ sk_F)) & 
% 2.52/2.70             ((l1_pre_topc @ sk_D_1)) & 
% 2.52/2.70             ((v2_pre_topc @ sk_D_1)))),
% 2.52/2.70      inference('clc', [status(thm)], ['89', '90'])).
% 2.52/2.70  thf('92', plain, (~ (v2_struct_0 @ sk_B)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('93', plain,
% 2.52/2.70      (((m1_subset_1 @ 
% 2.52/2.70         (k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F) @ 
% 2.52/2.70         (k1_zfmisc_1 @ 
% 2.52/2.70          (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.52/2.70           (u1_struct_0 @ sk_D_1))))) | 
% 2.52/2.70       ~ ((v1_funct_1 @ sk_E_1)) | ~ ((v2_pre_topc @ sk_D_1)) | 
% 2.52/2.70       ~ ((l1_pre_topc @ sk_D_1)) | ~ ((v1_funct_1 @ sk_F)) | 
% 2.52/2.70       ~ ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))) | 
% 2.52/2.70       ~
% 2.52/2.70       ((m1_subset_1 @ sk_F @ 
% 2.52/2.70         (k1_zfmisc_1 @ 
% 2.52/2.70          (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) | 
% 2.52/2.70       ~
% 2.52/2.70       ((m1_subset_1 @ sk_E_1 @ 
% 2.52/2.70         (k1_zfmisc_1 @ 
% 2.52/2.70          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) | 
% 2.52/2.70       ~
% 2.52/2.70       ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))) | 
% 2.52/2.70       ((v2_struct_0 @ sk_D_1))),
% 2.52/2.70      inference('sup-', [status(thm)], ['91', '92'])).
% 2.52/2.70  thf('94', plain,
% 2.52/2.70      (((r3_tsep_1 @ sk_A @ sk_B @ sk_C))
% 2.52/2.70         <= (((r3_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 2.52/2.70      inference('split', [status(esa)], ['0'])).
% 2.52/2.70  thf(t85_tsep_1, axiom,
% 2.52/2.70    (![A:$i]:
% 2.52/2.70     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.52/2.70       ( ![B:$i]:
% 2.52/2.70         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 2.52/2.70           ( ![C:$i]:
% 2.52/2.70             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 2.52/2.70               ( ( ( r1_tsep_1 @ B @ C ) & ( r4_tsep_1 @ A @ B @ C ) ) <=>
% 2.52/2.70                 ( r3_tsep_1 @ A @ B @ C ) ) ) ) ) ) ))).
% 2.52/2.70  thf('95', plain,
% 2.52/2.70      (![X26 : $i, X27 : $i, X28 : $i]:
% 2.52/2.70         ((v2_struct_0 @ X26)
% 2.52/2.70          | ~ (m1_pre_topc @ X26 @ X27)
% 2.52/2.70          | ~ (r3_tsep_1 @ X27 @ X26 @ X28)
% 2.52/2.70          | (r4_tsep_1 @ X27 @ X26 @ X28)
% 2.52/2.70          | ~ (m1_pre_topc @ X28 @ X27)
% 2.52/2.70          | (v2_struct_0 @ X28)
% 2.52/2.70          | ~ (l1_pre_topc @ X27)
% 2.52/2.70          | ~ (v2_pre_topc @ X27)
% 2.52/2.70          | (v2_struct_0 @ X27))),
% 2.52/2.70      inference('cnf', [status(esa)], [t85_tsep_1])).
% 2.52/2.70  thf('96', plain,
% 2.52/2.70      ((((v2_struct_0 @ sk_A)
% 2.52/2.70         | ~ (v2_pre_topc @ sk_A)
% 2.52/2.70         | ~ (l1_pre_topc @ sk_A)
% 2.52/2.70         | (v2_struct_0 @ sk_C)
% 2.52/2.70         | ~ (m1_pre_topc @ sk_C @ sk_A)
% 2.52/2.70         | (r4_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70         | ~ (m1_pre_topc @ sk_B @ sk_A)
% 2.52/2.70         | (v2_struct_0 @ sk_B))) <= (((r3_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['94', '95'])).
% 2.52/2.70  thf('97', plain, ((v2_pre_topc @ sk_A)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('98', plain, ((l1_pre_topc @ sk_A)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('99', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('100', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('101', plain,
% 2.52/2.70      ((((v2_struct_0 @ sk_A)
% 2.52/2.70         | (v2_struct_0 @ sk_C)
% 2.52/2.70         | (r4_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70         | (v2_struct_0 @ sk_B))) <= (((r3_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 2.52/2.70      inference('demod', [status(thm)], ['96', '97', '98', '99', '100'])).
% 2.52/2.70  thf('102', plain, (((v1_funct_1 @ sk_E_1)) <= (((v1_funct_1 @ sk_E_1)))),
% 2.52/2.70      inference('split', [status(esa)], ['10'])).
% 2.52/2.70  thf('103', plain,
% 2.52/2.70      ((((v2_struct_0 @ sk_A)
% 2.52/2.70         | (v2_struct_0 @ sk_C)
% 2.52/2.70         | (r1_tsep_1 @ sk_B @ sk_C)
% 2.52/2.70         | (v2_struct_0 @ sk_B))) <= (((r3_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 2.52/2.70      inference('demod', [status(thm)], ['4', '5', '6', '7', '8'])).
% 2.52/2.70  thf('104', plain,
% 2.52/2.70      (((v5_pre_topc @ sk_E_1 @ sk_B @ sk_D_1)
% 2.52/2.70        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 2.52/2.70        | ~ (r3_tsep_1 @ sk_A @ sk_B @ sk_C))),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('105', plain,
% 2.52/2.70      (((v5_pre_topc @ sk_E_1 @ sk_B @ sk_D_1))
% 2.52/2.70         <= (((v5_pre_topc @ sk_E_1 @ sk_B @ sk_D_1)))),
% 2.52/2.70      inference('split', [status(esa)], ['104'])).
% 2.52/2.70  thf('106', plain,
% 2.52/2.70      (((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1)))
% 2.52/2.70         <= (((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.70               (u1_struct_0 @ sk_D_1))))),
% 2.52/2.70      inference('split', [status(esa)], ['31'])).
% 2.52/2.70  thf('107', plain,
% 2.52/2.70      (((m1_subset_1 @ sk_E_1 @ 
% 2.52/2.70         (k1_zfmisc_1 @ 
% 2.52/2.70          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1)))))
% 2.52/2.70         <= (((m1_subset_1 @ sk_E_1 @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))))),
% 2.52/2.70      inference('split', [status(esa)], ['33'])).
% 2.52/2.70  thf('108', plain, (((l1_pre_topc @ sk_D_1)) <= (((l1_pre_topc @ sk_D_1)))),
% 2.52/2.70      inference('split', [status(esa)], ['26'])).
% 2.52/2.70  thf('109', plain, (((v2_pre_topc @ sk_D_1)) <= (((v2_pre_topc @ sk_D_1)))),
% 2.52/2.70      inference('split', [status(esa)], ['28'])).
% 2.52/2.70  thf('110', plain, (((v1_funct_1 @ sk_F)) <= (((v1_funct_1 @ sk_F)))),
% 2.52/2.70      inference('split', [status(esa)], ['20'])).
% 2.52/2.70  thf('111', plain,
% 2.52/2.70      (((v5_pre_topc @ sk_F @ sk_C @ sk_D_1)
% 2.52/2.70        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 2.52/2.70        | ~ (r3_tsep_1 @ sk_A @ sk_B @ sk_C))),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('112', plain,
% 2.52/2.70      (((v5_pre_topc @ sk_F @ sk_C @ sk_D_1))
% 2.52/2.70         <= (((v5_pre_topc @ sk_F @ sk_C @ sk_D_1)))),
% 2.52/2.70      inference('split', [status(esa)], ['111'])).
% 2.52/2.70  thf('113', plain,
% 2.52/2.70      (((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1)))
% 2.52/2.70         <= (((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.70               (u1_struct_0 @ sk_D_1))))),
% 2.52/2.70      inference('split', [status(esa)], ['22'])).
% 2.52/2.70  thf('114', plain,
% 2.52/2.70      (((m1_subset_1 @ sk_F @ 
% 2.52/2.70         (k1_zfmisc_1 @ 
% 2.52/2.70          (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1)))))
% 2.52/2.70         <= (((m1_subset_1 @ sk_F @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))))),
% 2.52/2.70      inference('split', [status(esa)], ['24'])).
% 2.52/2.70  thf(t145_tmap_1, axiom,
% 2.52/2.70    (![A:$i]:
% 2.52/2.70     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.52/2.70       ( ![B:$i]:
% 2.52/2.70         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 2.52/2.70             ( l1_pre_topc @ B ) ) =>
% 2.52/2.70           ( ![C:$i]:
% 2.52/2.70             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 2.52/2.70               ( ![D:$i]:
% 2.52/2.70                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 2.52/2.70                   ( ( r1_tsep_1 @ C @ D ) =>
% 2.52/2.70                     ( ![E:$i]:
% 2.52/2.70                       ( ( ( v1_funct_1 @ E ) & 
% 2.52/2.70                           ( v1_funct_2 @
% 2.52/2.70                             E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 2.52/2.70                           ( v5_pre_topc @ E @ C @ B ) & 
% 2.52/2.70                           ( m1_subset_1 @
% 2.52/2.70                             E @ 
% 2.52/2.70                             ( k1_zfmisc_1 @
% 2.52/2.70                               ( k2_zfmisc_1 @
% 2.52/2.70                                 ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 2.52/2.70                         ( ![F:$i]:
% 2.52/2.70                           ( ( ( v1_funct_1 @ F ) & 
% 2.52/2.70                               ( v1_funct_2 @
% 2.52/2.70                                 F @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 2.52/2.70                               ( v5_pre_topc @ F @ D @ B ) & 
% 2.52/2.70                               ( m1_subset_1 @
% 2.52/2.70                                 F @ 
% 2.52/2.70                                 ( k1_zfmisc_1 @
% 2.52/2.70                                   ( k2_zfmisc_1 @
% 2.52/2.70                                     ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 2.52/2.70                             ( ( r4_tsep_1 @ A @ C @ D ) =>
% 2.52/2.70                               ( ( v1_funct_1 @
% 2.52/2.70                                   ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) ) & 
% 2.52/2.70                                 ( v1_funct_2 @
% 2.52/2.70                                   ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 2.52/2.70                                   ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 2.52/2.70                                   ( u1_struct_0 @ B ) ) & 
% 2.52/2.70                                 ( v5_pre_topc @
% 2.52/2.70                                   ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 2.52/2.70                                   ( k1_tsep_1 @ A @ C @ D ) @ B ) & 
% 2.52/2.70                                 ( m1_subset_1 @
% 2.52/2.70                                   ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 2.52/2.70                                   ( k1_zfmisc_1 @
% 2.52/2.70                                     ( k2_zfmisc_1 @
% 2.52/2.70                                       ( u1_struct_0 @
% 2.52/2.70                                         ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 2.52/2.70                                       ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 2.52/2.70  thf('115', plain,
% 2.52/2.70      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 2.52/2.70         ((v2_struct_0 @ X20)
% 2.52/2.70          | ~ (v2_pre_topc @ X20)
% 2.52/2.70          | ~ (l1_pre_topc @ X20)
% 2.52/2.70          | (v2_struct_0 @ X21)
% 2.52/2.70          | ~ (m1_pre_topc @ X21 @ X22)
% 2.52/2.70          | ~ (v1_funct_1 @ X23)
% 2.52/2.70          | ~ (v1_funct_2 @ X23 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X20))
% 2.52/2.70          | ~ (v5_pre_topc @ X23 @ X21 @ X20)
% 2.52/2.70          | ~ (m1_subset_1 @ X23 @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X20))))
% 2.52/2.70          | (v5_pre_topc @ (k10_tmap_1 @ X22 @ X20 @ X24 @ X21 @ X25 @ X23) @ 
% 2.52/2.70             (k1_tsep_1 @ X22 @ X24 @ X21) @ X20)
% 2.52/2.70          | ~ (r4_tsep_1 @ X22 @ X24 @ X21)
% 2.52/2.70          | ~ (m1_subset_1 @ X25 @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X20))))
% 2.52/2.70          | ~ (v5_pre_topc @ X25 @ X24 @ X20)
% 2.52/2.70          | ~ (v1_funct_2 @ X25 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X20))
% 2.52/2.70          | ~ (v1_funct_1 @ X25)
% 2.52/2.70          | ~ (r1_tsep_1 @ X24 @ X21)
% 2.52/2.70          | ~ (m1_pre_topc @ X24 @ X22)
% 2.52/2.70          | (v2_struct_0 @ X24)
% 2.52/2.70          | ~ (l1_pre_topc @ X22)
% 2.52/2.70          | ~ (v2_pre_topc @ X22)
% 2.52/2.70          | (v2_struct_0 @ X22))),
% 2.52/2.70      inference('cnf', [status(esa)], [t145_tmap_1])).
% 2.52/2.70  thf('116', plain,
% 2.52/2.70      ((![X0 : $i, X1 : $i, X2 : $i]:
% 2.52/2.70          ((v2_struct_0 @ X0)
% 2.52/2.70           | ~ (v2_pre_topc @ X0)
% 2.52/2.70           | ~ (l1_pre_topc @ X0)
% 2.52/2.70           | (v2_struct_0 @ X1)
% 2.52/2.70           | ~ (m1_pre_topc @ X1 @ X0)
% 2.52/2.70           | ~ (r1_tsep_1 @ X1 @ sk_C)
% 2.52/2.70           | ~ (v1_funct_1 @ X2)
% 2.52/2.70           | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_D_1))
% 2.52/2.70           | ~ (v5_pre_topc @ X2 @ X1 @ sk_D_1)
% 2.52/2.70           | ~ (m1_subset_1 @ X2 @ 
% 2.52/2.70                (k1_zfmisc_1 @ 
% 2.52/2.70                 (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_D_1))))
% 2.52/2.70           | ~ (r4_tsep_1 @ X0 @ X1 @ sk_C)
% 2.52/2.70           | (v5_pre_topc @ 
% 2.52/2.70              (k10_tmap_1 @ X0 @ sk_D_1 @ X1 @ sk_C @ X2 @ sk_F) @ 
% 2.52/2.70              (k1_tsep_1 @ X0 @ X1 @ sk_C) @ sk_D_1)
% 2.52/2.70           | ~ (v5_pre_topc @ sk_F @ sk_C @ sk_D_1)
% 2.52/2.70           | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.70                (u1_struct_0 @ sk_D_1))
% 2.52/2.70           | ~ (v1_funct_1 @ sk_F)
% 2.52/2.70           | ~ (m1_pre_topc @ sk_C @ X0)
% 2.52/2.70           | (v2_struct_0 @ sk_C)
% 2.52/2.70           | ~ (l1_pre_topc @ sk_D_1)
% 2.52/2.70           | ~ (v2_pre_topc @ sk_D_1)
% 2.52/2.70           | (v2_struct_0 @ sk_D_1)))
% 2.52/2.70         <= (((m1_subset_1 @ sk_F @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))))),
% 2.52/2.70      inference('sup-', [status(thm)], ['114', '115'])).
% 2.52/2.70  thf('117', plain,
% 2.52/2.70      ((![X0 : $i, X1 : $i, X2 : $i]:
% 2.52/2.70          ((v2_struct_0 @ sk_D_1)
% 2.52/2.70           | ~ (v2_pre_topc @ sk_D_1)
% 2.52/2.70           | ~ (l1_pre_topc @ sk_D_1)
% 2.52/2.70           | (v2_struct_0 @ sk_C)
% 2.52/2.70           | ~ (m1_pre_topc @ sk_C @ X0)
% 2.52/2.70           | ~ (v1_funct_1 @ sk_F)
% 2.52/2.70           | ~ (v5_pre_topc @ sk_F @ sk_C @ sk_D_1)
% 2.52/2.70           | (v5_pre_topc @ 
% 2.52/2.70              (k10_tmap_1 @ X0 @ sk_D_1 @ X1 @ sk_C @ X2 @ sk_F) @ 
% 2.52/2.70              (k1_tsep_1 @ X0 @ X1 @ sk_C) @ sk_D_1)
% 2.52/2.70           | ~ (r4_tsep_1 @ X0 @ X1 @ sk_C)
% 2.52/2.70           | ~ (m1_subset_1 @ X2 @ 
% 2.52/2.70                (k1_zfmisc_1 @ 
% 2.52/2.70                 (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_D_1))))
% 2.52/2.70           | ~ (v5_pre_topc @ X2 @ X1 @ sk_D_1)
% 2.52/2.70           | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_D_1))
% 2.52/2.70           | ~ (v1_funct_1 @ X2)
% 2.52/2.70           | ~ (r1_tsep_1 @ X1 @ sk_C)
% 2.52/2.70           | ~ (m1_pre_topc @ X1 @ X0)
% 2.52/2.70           | (v2_struct_0 @ X1)
% 2.52/2.70           | ~ (l1_pre_topc @ X0)
% 2.52/2.70           | ~ (v2_pre_topc @ X0)
% 2.52/2.70           | (v2_struct_0 @ X0)))
% 2.52/2.70         <= (((m1_subset_1 @ sk_F @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.70             ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.70               (u1_struct_0 @ sk_D_1))))),
% 2.52/2.70      inference('sup-', [status(thm)], ['113', '116'])).
% 2.52/2.70  thf('118', plain,
% 2.52/2.70      ((![X0 : $i, X1 : $i, X2 : $i]:
% 2.52/2.70          ((v2_struct_0 @ X0)
% 2.52/2.70           | ~ (v2_pre_topc @ X0)
% 2.52/2.70           | ~ (l1_pre_topc @ X0)
% 2.52/2.70           | (v2_struct_0 @ X1)
% 2.52/2.70           | ~ (m1_pre_topc @ X1 @ X0)
% 2.52/2.70           | ~ (r1_tsep_1 @ X1 @ sk_C)
% 2.52/2.70           | ~ (v1_funct_1 @ X2)
% 2.52/2.70           | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_D_1))
% 2.52/2.70           | ~ (v5_pre_topc @ X2 @ X1 @ sk_D_1)
% 2.52/2.70           | ~ (m1_subset_1 @ X2 @ 
% 2.52/2.70                (k1_zfmisc_1 @ 
% 2.52/2.70                 (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_D_1))))
% 2.52/2.70           | ~ (r4_tsep_1 @ X0 @ X1 @ sk_C)
% 2.52/2.70           | (v5_pre_topc @ 
% 2.52/2.70              (k10_tmap_1 @ X0 @ sk_D_1 @ X1 @ sk_C @ X2 @ sk_F) @ 
% 2.52/2.70              (k1_tsep_1 @ X0 @ X1 @ sk_C) @ sk_D_1)
% 2.52/2.70           | ~ (v1_funct_1 @ sk_F)
% 2.52/2.70           | ~ (m1_pre_topc @ sk_C @ X0)
% 2.52/2.70           | (v2_struct_0 @ sk_C)
% 2.52/2.70           | ~ (l1_pre_topc @ sk_D_1)
% 2.52/2.70           | ~ (v2_pre_topc @ sk_D_1)
% 2.52/2.70           | (v2_struct_0 @ sk_D_1)))
% 2.52/2.70         <= (((m1_subset_1 @ sk_F @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.70             ((v5_pre_topc @ sk_F @ sk_C @ sk_D_1)) & 
% 2.52/2.70             ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.70               (u1_struct_0 @ sk_D_1))))),
% 2.52/2.70      inference('sup-', [status(thm)], ['112', '117'])).
% 2.52/2.70  thf('119', plain,
% 2.52/2.70      ((![X0 : $i, X1 : $i, X2 : $i]:
% 2.52/2.70          ((v2_struct_0 @ sk_D_1)
% 2.52/2.70           | ~ (v2_pre_topc @ sk_D_1)
% 2.52/2.70           | ~ (l1_pre_topc @ sk_D_1)
% 2.52/2.70           | (v2_struct_0 @ sk_C)
% 2.52/2.70           | ~ (m1_pre_topc @ sk_C @ X0)
% 2.52/2.70           | (v5_pre_topc @ 
% 2.52/2.70              (k10_tmap_1 @ X0 @ sk_D_1 @ X1 @ sk_C @ X2 @ sk_F) @ 
% 2.52/2.70              (k1_tsep_1 @ X0 @ X1 @ sk_C) @ sk_D_1)
% 2.52/2.70           | ~ (r4_tsep_1 @ X0 @ X1 @ sk_C)
% 2.52/2.70           | ~ (m1_subset_1 @ X2 @ 
% 2.52/2.70                (k1_zfmisc_1 @ 
% 2.52/2.70                 (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_D_1))))
% 2.52/2.70           | ~ (v5_pre_topc @ X2 @ X1 @ sk_D_1)
% 2.52/2.70           | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_D_1))
% 2.52/2.70           | ~ (v1_funct_1 @ X2)
% 2.52/2.70           | ~ (r1_tsep_1 @ X1 @ sk_C)
% 2.52/2.70           | ~ (m1_pre_topc @ X1 @ X0)
% 2.52/2.70           | (v2_struct_0 @ X1)
% 2.52/2.70           | ~ (l1_pre_topc @ X0)
% 2.52/2.70           | ~ (v2_pre_topc @ X0)
% 2.52/2.70           | (v2_struct_0 @ X0)))
% 2.52/2.70         <= (((m1_subset_1 @ sk_F @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.70             ((v5_pre_topc @ sk_F @ sk_C @ sk_D_1)) & 
% 2.52/2.70             ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.70               (u1_struct_0 @ sk_D_1))) & 
% 2.52/2.70             ((v1_funct_1 @ sk_F)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['110', '118'])).
% 2.52/2.70  thf('120', plain,
% 2.52/2.70      ((![X0 : $i, X1 : $i, X2 : $i]:
% 2.52/2.70          ((v2_struct_0 @ X0)
% 2.52/2.70           | ~ (v2_pre_topc @ X0)
% 2.52/2.70           | ~ (l1_pre_topc @ X0)
% 2.52/2.70           | (v2_struct_0 @ X1)
% 2.52/2.70           | ~ (m1_pre_topc @ X1 @ X0)
% 2.52/2.70           | ~ (r1_tsep_1 @ X1 @ sk_C)
% 2.52/2.70           | ~ (v1_funct_1 @ X2)
% 2.52/2.70           | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_D_1))
% 2.52/2.70           | ~ (v5_pre_topc @ X2 @ X1 @ sk_D_1)
% 2.52/2.70           | ~ (m1_subset_1 @ X2 @ 
% 2.52/2.70                (k1_zfmisc_1 @ 
% 2.52/2.70                 (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_D_1))))
% 2.52/2.70           | ~ (r4_tsep_1 @ X0 @ X1 @ sk_C)
% 2.52/2.70           | (v5_pre_topc @ 
% 2.52/2.70              (k10_tmap_1 @ X0 @ sk_D_1 @ X1 @ sk_C @ X2 @ sk_F) @ 
% 2.52/2.70              (k1_tsep_1 @ X0 @ X1 @ sk_C) @ sk_D_1)
% 2.52/2.70           | ~ (m1_pre_topc @ sk_C @ X0)
% 2.52/2.70           | (v2_struct_0 @ sk_C)
% 2.52/2.70           | ~ (l1_pre_topc @ sk_D_1)
% 2.52/2.70           | (v2_struct_0 @ sk_D_1)))
% 2.52/2.70         <= (((m1_subset_1 @ sk_F @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.70             ((v5_pre_topc @ sk_F @ sk_C @ sk_D_1)) & 
% 2.52/2.70             ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.70               (u1_struct_0 @ sk_D_1))) & 
% 2.52/2.70             ((v1_funct_1 @ sk_F)) & 
% 2.52/2.70             ((v2_pre_topc @ sk_D_1)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['109', '119'])).
% 2.52/2.70  thf('121', plain,
% 2.52/2.70      ((![X0 : $i, X1 : $i, X2 : $i]:
% 2.52/2.70          ((v2_struct_0 @ sk_D_1)
% 2.52/2.70           | (v2_struct_0 @ sk_C)
% 2.52/2.70           | ~ (m1_pre_topc @ sk_C @ X0)
% 2.52/2.70           | (v5_pre_topc @ 
% 2.52/2.70              (k10_tmap_1 @ X0 @ sk_D_1 @ X1 @ sk_C @ X2 @ sk_F) @ 
% 2.52/2.70              (k1_tsep_1 @ X0 @ X1 @ sk_C) @ sk_D_1)
% 2.52/2.70           | ~ (r4_tsep_1 @ X0 @ X1 @ sk_C)
% 2.52/2.70           | ~ (m1_subset_1 @ X2 @ 
% 2.52/2.70                (k1_zfmisc_1 @ 
% 2.52/2.70                 (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_D_1))))
% 2.52/2.70           | ~ (v5_pre_topc @ X2 @ X1 @ sk_D_1)
% 2.52/2.70           | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_D_1))
% 2.52/2.70           | ~ (v1_funct_1 @ X2)
% 2.52/2.70           | ~ (r1_tsep_1 @ X1 @ sk_C)
% 2.52/2.70           | ~ (m1_pre_topc @ X1 @ X0)
% 2.52/2.70           | (v2_struct_0 @ X1)
% 2.52/2.70           | ~ (l1_pre_topc @ X0)
% 2.52/2.70           | ~ (v2_pre_topc @ X0)
% 2.52/2.70           | (v2_struct_0 @ X0)))
% 2.52/2.70         <= (((m1_subset_1 @ sk_F @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.70             ((v5_pre_topc @ sk_F @ sk_C @ sk_D_1)) & 
% 2.52/2.70             ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.70               (u1_struct_0 @ sk_D_1))) & 
% 2.52/2.70             ((v1_funct_1 @ sk_F)) & 
% 2.52/2.70             ((l1_pre_topc @ sk_D_1)) & 
% 2.52/2.70             ((v2_pre_topc @ sk_D_1)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['108', '120'])).
% 2.52/2.70  thf('122', plain,
% 2.52/2.70      ((![X0 : $i]:
% 2.52/2.70          ((v2_struct_0 @ X0)
% 2.52/2.70           | ~ (v2_pre_topc @ X0)
% 2.52/2.70           | ~ (l1_pre_topc @ X0)
% 2.52/2.70           | (v2_struct_0 @ sk_B)
% 2.52/2.70           | ~ (m1_pre_topc @ sk_B @ X0)
% 2.52/2.70           | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 2.52/2.70           | ~ (v1_funct_1 @ sk_E_1)
% 2.52/2.70           | ~ (v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.70                (u1_struct_0 @ sk_D_1))
% 2.52/2.70           | ~ (v5_pre_topc @ sk_E_1 @ sk_B @ sk_D_1)
% 2.52/2.70           | ~ (r4_tsep_1 @ X0 @ sk_B @ sk_C)
% 2.52/2.70           | (v5_pre_topc @ 
% 2.52/2.70              (k10_tmap_1 @ X0 @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F) @ 
% 2.52/2.70              (k1_tsep_1 @ X0 @ sk_B @ sk_C) @ sk_D_1)
% 2.52/2.70           | ~ (m1_pre_topc @ sk_C @ X0)
% 2.52/2.70           | (v2_struct_0 @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_D_1)))
% 2.52/2.70         <= (((m1_subset_1 @ sk_E_1 @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.70             ((m1_subset_1 @ sk_F @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.70             ((v5_pre_topc @ sk_F @ sk_C @ sk_D_1)) & 
% 2.52/2.70             ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.70               (u1_struct_0 @ sk_D_1))) & 
% 2.52/2.70             ((v1_funct_1 @ sk_F)) & 
% 2.52/2.70             ((l1_pre_topc @ sk_D_1)) & 
% 2.52/2.70             ((v2_pre_topc @ sk_D_1)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['107', '121'])).
% 2.52/2.70  thf('123', plain,
% 2.52/2.70      ((![X0 : $i]:
% 2.52/2.70          ((v2_struct_0 @ sk_D_1)
% 2.52/2.70           | (v2_struct_0 @ sk_C)
% 2.52/2.70           | ~ (m1_pre_topc @ sk_C @ X0)
% 2.52/2.70           | (v5_pre_topc @ 
% 2.52/2.70              (k10_tmap_1 @ X0 @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F) @ 
% 2.52/2.70              (k1_tsep_1 @ X0 @ sk_B @ sk_C) @ sk_D_1)
% 2.52/2.70           | ~ (r4_tsep_1 @ X0 @ sk_B @ sk_C)
% 2.52/2.70           | ~ (v5_pre_topc @ sk_E_1 @ sk_B @ sk_D_1)
% 2.52/2.70           | ~ (v1_funct_1 @ sk_E_1)
% 2.52/2.70           | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 2.52/2.70           | ~ (m1_pre_topc @ sk_B @ X0)
% 2.52/2.70           | (v2_struct_0 @ sk_B)
% 2.52/2.70           | ~ (l1_pre_topc @ X0)
% 2.52/2.70           | ~ (v2_pre_topc @ X0)
% 2.52/2.70           | (v2_struct_0 @ X0)))
% 2.52/2.70         <= (((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.70               (u1_struct_0 @ sk_D_1))) & 
% 2.52/2.70             ((m1_subset_1 @ sk_E_1 @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.70             ((m1_subset_1 @ sk_F @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.70             ((v5_pre_topc @ sk_F @ sk_C @ sk_D_1)) & 
% 2.52/2.70             ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.70               (u1_struct_0 @ sk_D_1))) & 
% 2.52/2.70             ((v1_funct_1 @ sk_F)) & 
% 2.52/2.70             ((l1_pre_topc @ sk_D_1)) & 
% 2.52/2.70             ((v2_pre_topc @ sk_D_1)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['106', '122'])).
% 2.52/2.70  thf('124', plain,
% 2.52/2.70      ((![X0 : $i]:
% 2.52/2.70          ((v2_struct_0 @ X0)
% 2.52/2.70           | ~ (v2_pre_topc @ X0)
% 2.52/2.70           | ~ (l1_pre_topc @ X0)
% 2.52/2.70           | (v2_struct_0 @ sk_B)
% 2.52/2.70           | ~ (m1_pre_topc @ sk_B @ X0)
% 2.52/2.70           | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 2.52/2.70           | ~ (v1_funct_1 @ sk_E_1)
% 2.52/2.70           | ~ (r4_tsep_1 @ X0 @ sk_B @ sk_C)
% 2.52/2.70           | (v5_pre_topc @ 
% 2.52/2.70              (k10_tmap_1 @ X0 @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F) @ 
% 2.52/2.70              (k1_tsep_1 @ X0 @ sk_B @ sk_C) @ sk_D_1)
% 2.52/2.70           | ~ (m1_pre_topc @ sk_C @ X0)
% 2.52/2.70           | (v2_struct_0 @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_D_1)))
% 2.52/2.70         <= (((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.70               (u1_struct_0 @ sk_D_1))) & 
% 2.52/2.70             ((v5_pre_topc @ sk_E_1 @ sk_B @ sk_D_1)) & 
% 2.52/2.70             ((m1_subset_1 @ sk_E_1 @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.70             ((m1_subset_1 @ sk_F @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.70             ((v5_pre_topc @ sk_F @ sk_C @ sk_D_1)) & 
% 2.52/2.70             ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.70               (u1_struct_0 @ sk_D_1))) & 
% 2.52/2.70             ((v1_funct_1 @ sk_F)) & 
% 2.52/2.70             ((l1_pre_topc @ sk_D_1)) & 
% 2.52/2.70             ((v2_pre_topc @ sk_D_1)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['105', '123'])).
% 2.52/2.70  thf('125', plain,
% 2.52/2.70      ((![X0 : $i]:
% 2.52/2.70          ((v2_struct_0 @ sk_B)
% 2.52/2.70           | (v2_struct_0 @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_A)
% 2.52/2.70           | (v2_struct_0 @ sk_D_1)
% 2.52/2.70           | (v2_struct_0 @ sk_C)
% 2.52/2.70           | ~ (m1_pre_topc @ sk_C @ X0)
% 2.52/2.70           | (v5_pre_topc @ 
% 2.52/2.70              (k10_tmap_1 @ X0 @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F) @ 
% 2.52/2.70              (k1_tsep_1 @ X0 @ sk_B @ sk_C) @ sk_D_1)
% 2.52/2.70           | ~ (r4_tsep_1 @ X0 @ sk_B @ sk_C)
% 2.52/2.70           | ~ (v1_funct_1 @ sk_E_1)
% 2.52/2.70           | ~ (m1_pre_topc @ sk_B @ X0)
% 2.52/2.70           | (v2_struct_0 @ sk_B)
% 2.52/2.70           | ~ (l1_pre_topc @ X0)
% 2.52/2.70           | ~ (v2_pre_topc @ X0)
% 2.52/2.70           | (v2_struct_0 @ X0)))
% 2.52/2.70         <= (((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) & 
% 2.52/2.70             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.70               (u1_struct_0 @ sk_D_1))) & 
% 2.52/2.70             ((v5_pre_topc @ sk_E_1 @ sk_B @ sk_D_1)) & 
% 2.52/2.70             ((m1_subset_1 @ sk_E_1 @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.70             ((m1_subset_1 @ sk_F @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.70             ((v5_pre_topc @ sk_F @ sk_C @ sk_D_1)) & 
% 2.52/2.70             ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.70               (u1_struct_0 @ sk_D_1))) & 
% 2.52/2.70             ((v1_funct_1 @ sk_F)) & 
% 2.52/2.70             ((l1_pre_topc @ sk_D_1)) & 
% 2.52/2.70             ((v2_pre_topc @ sk_D_1)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['103', '124'])).
% 2.52/2.70  thf('126', plain,
% 2.52/2.70      ((![X0 : $i]:
% 2.52/2.70          ((v2_struct_0 @ X0)
% 2.52/2.70           | ~ (v2_pre_topc @ X0)
% 2.52/2.70           | ~ (l1_pre_topc @ X0)
% 2.52/2.70           | ~ (m1_pre_topc @ sk_B @ X0)
% 2.52/2.70           | ~ (v1_funct_1 @ sk_E_1)
% 2.52/2.70           | ~ (r4_tsep_1 @ X0 @ sk_B @ sk_C)
% 2.52/2.70           | (v5_pre_topc @ 
% 2.52/2.70              (k10_tmap_1 @ X0 @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F) @ 
% 2.52/2.70              (k1_tsep_1 @ X0 @ sk_B @ sk_C) @ sk_D_1)
% 2.52/2.70           | ~ (m1_pre_topc @ sk_C @ X0)
% 2.52/2.70           | (v2_struct_0 @ sk_D_1)
% 2.52/2.70           | (v2_struct_0 @ sk_A)
% 2.52/2.70           | (v2_struct_0 @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_B)))
% 2.52/2.70         <= (((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) & 
% 2.52/2.70             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.70               (u1_struct_0 @ sk_D_1))) & 
% 2.52/2.70             ((v5_pre_topc @ sk_E_1 @ sk_B @ sk_D_1)) & 
% 2.52/2.70             ((m1_subset_1 @ sk_E_1 @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.70             ((m1_subset_1 @ sk_F @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.70             ((v5_pre_topc @ sk_F @ sk_C @ sk_D_1)) & 
% 2.52/2.70             ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.70               (u1_struct_0 @ sk_D_1))) & 
% 2.52/2.70             ((v1_funct_1 @ sk_F)) & 
% 2.52/2.70             ((l1_pre_topc @ sk_D_1)) & 
% 2.52/2.70             ((v2_pre_topc @ sk_D_1)))),
% 2.52/2.70      inference('simplify', [status(thm)], ['125'])).
% 2.52/2.70  thf('127', plain,
% 2.52/2.70      ((![X0 : $i]:
% 2.52/2.70          ((v2_struct_0 @ sk_B)
% 2.52/2.70           | (v2_struct_0 @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_A)
% 2.52/2.70           | (v2_struct_0 @ sk_D_1)
% 2.52/2.70           | ~ (m1_pre_topc @ sk_C @ X0)
% 2.52/2.70           | (v5_pre_topc @ 
% 2.52/2.70              (k10_tmap_1 @ X0 @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F) @ 
% 2.52/2.70              (k1_tsep_1 @ X0 @ sk_B @ sk_C) @ sk_D_1)
% 2.52/2.70           | ~ (r4_tsep_1 @ X0 @ sk_B @ sk_C)
% 2.52/2.70           | ~ (m1_pre_topc @ sk_B @ X0)
% 2.52/2.70           | ~ (l1_pre_topc @ X0)
% 2.52/2.70           | ~ (v2_pre_topc @ X0)
% 2.52/2.70           | (v2_struct_0 @ X0)))
% 2.52/2.70         <= (((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) & 
% 2.52/2.70             ((v1_funct_1 @ sk_E_1)) & 
% 2.52/2.70             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.70               (u1_struct_0 @ sk_D_1))) & 
% 2.52/2.70             ((v5_pre_topc @ sk_E_1 @ sk_B @ sk_D_1)) & 
% 2.52/2.70             ((m1_subset_1 @ sk_E_1 @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.70             ((m1_subset_1 @ sk_F @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.70             ((v5_pre_topc @ sk_F @ sk_C @ sk_D_1)) & 
% 2.52/2.70             ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.70               (u1_struct_0 @ sk_D_1))) & 
% 2.52/2.70             ((v1_funct_1 @ sk_F)) & 
% 2.52/2.70             ((l1_pre_topc @ sk_D_1)) & 
% 2.52/2.70             ((v2_pre_topc @ sk_D_1)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['102', '126'])).
% 2.52/2.70  thf('128', plain,
% 2.52/2.70      ((((v2_struct_0 @ sk_B)
% 2.52/2.70         | (v2_struct_0 @ sk_C)
% 2.52/2.70         | (v2_struct_0 @ sk_A)
% 2.52/2.70         | (v2_struct_0 @ sk_A)
% 2.52/2.70         | ~ (v2_pre_topc @ sk_A)
% 2.52/2.70         | ~ (l1_pre_topc @ sk_A)
% 2.52/2.70         | ~ (m1_pre_topc @ sk_B @ sk_A)
% 2.52/2.70         | (v5_pre_topc @ 
% 2.52/2.70            (k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F) @ 
% 2.52/2.70            (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D_1)
% 2.52/2.70         | ~ (m1_pre_topc @ sk_C @ sk_A)
% 2.52/2.70         | (v2_struct_0 @ sk_D_1)
% 2.52/2.70         | (v2_struct_0 @ sk_A)
% 2.52/2.70         | (v2_struct_0 @ sk_C)
% 2.52/2.70         | (v2_struct_0 @ sk_B)))
% 2.52/2.70         <= (((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) & 
% 2.52/2.70             ((v1_funct_1 @ sk_E_1)) & 
% 2.52/2.70             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.70               (u1_struct_0 @ sk_D_1))) & 
% 2.52/2.70             ((v5_pre_topc @ sk_E_1 @ sk_B @ sk_D_1)) & 
% 2.52/2.70             ((m1_subset_1 @ sk_E_1 @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.70             ((m1_subset_1 @ sk_F @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.70             ((v5_pre_topc @ sk_F @ sk_C @ sk_D_1)) & 
% 2.52/2.70             ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.70               (u1_struct_0 @ sk_D_1))) & 
% 2.52/2.70             ((v1_funct_1 @ sk_F)) & 
% 2.52/2.70             ((l1_pre_topc @ sk_D_1)) & 
% 2.52/2.70             ((v2_pre_topc @ sk_D_1)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['101', '127'])).
% 2.52/2.70  thf('129', plain, ((v2_pre_topc @ sk_A)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('130', plain, ((l1_pre_topc @ sk_A)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('131', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('132', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('133', plain,
% 2.52/2.70      ((((v2_struct_0 @ sk_B)
% 2.52/2.70         | (v2_struct_0 @ sk_C)
% 2.52/2.70         | (v2_struct_0 @ sk_A)
% 2.52/2.70         | (v2_struct_0 @ sk_A)
% 2.52/2.70         | (v5_pre_topc @ 
% 2.52/2.70            (k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F) @ 
% 2.52/2.70            (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D_1)
% 2.52/2.70         | (v2_struct_0 @ sk_D_1)
% 2.52/2.70         | (v2_struct_0 @ sk_A)
% 2.52/2.70         | (v2_struct_0 @ sk_C)
% 2.52/2.70         | (v2_struct_0 @ sk_B)))
% 2.52/2.70         <= (((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) & 
% 2.52/2.70             ((v1_funct_1 @ sk_E_1)) & 
% 2.52/2.70             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.70               (u1_struct_0 @ sk_D_1))) & 
% 2.52/2.70             ((v5_pre_topc @ sk_E_1 @ sk_B @ sk_D_1)) & 
% 2.52/2.70             ((m1_subset_1 @ sk_E_1 @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.70             ((m1_subset_1 @ sk_F @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.70             ((v5_pre_topc @ sk_F @ sk_C @ sk_D_1)) & 
% 2.52/2.70             ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.70               (u1_struct_0 @ sk_D_1))) & 
% 2.52/2.70             ((v1_funct_1 @ sk_F)) & 
% 2.52/2.70             ((l1_pre_topc @ sk_D_1)) & 
% 2.52/2.70             ((v2_pre_topc @ sk_D_1)))),
% 2.52/2.70      inference('demod', [status(thm)], ['128', '129', '130', '131', '132'])).
% 2.52/2.70  thf('134', plain,
% 2.52/2.70      ((((v2_struct_0 @ sk_D_1)
% 2.52/2.70         | (v5_pre_topc @ 
% 2.52/2.70            (k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F) @ 
% 2.52/2.70            (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D_1)
% 2.52/2.70         | (v2_struct_0 @ sk_A)
% 2.52/2.70         | (v2_struct_0 @ sk_C)
% 2.52/2.70         | (v2_struct_0 @ sk_B)))
% 2.52/2.70         <= (((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) & 
% 2.52/2.70             ((v1_funct_1 @ sk_E_1)) & 
% 2.52/2.70             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.70               (u1_struct_0 @ sk_D_1))) & 
% 2.52/2.70             ((v5_pre_topc @ sk_E_1 @ sk_B @ sk_D_1)) & 
% 2.52/2.70             ((m1_subset_1 @ sk_E_1 @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.70             ((m1_subset_1 @ sk_F @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.70             ((v5_pre_topc @ sk_F @ sk_C @ sk_D_1)) & 
% 2.52/2.70             ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.70               (u1_struct_0 @ sk_D_1))) & 
% 2.52/2.70             ((v1_funct_1 @ sk_F)) & 
% 2.52/2.70             ((l1_pre_topc @ sk_D_1)) & 
% 2.52/2.70             ((v2_pre_topc @ sk_D_1)))),
% 2.52/2.70      inference('simplify', [status(thm)], ['133'])).
% 2.52/2.70  thf('135', plain,
% 2.52/2.70      ((~ (v5_pre_topc @ 
% 2.52/2.70           (k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F) @ 
% 2.52/2.70           (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D_1))
% 2.52/2.70         <= (~
% 2.52/2.70             ((v5_pre_topc @ 
% 2.52/2.70               (k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F) @ 
% 2.52/2.70               (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D_1)))),
% 2.52/2.70      inference('split', [status(esa)], ['49'])).
% 2.52/2.70  thf('136', plain,
% 2.52/2.70      ((((v2_struct_0 @ sk_B)
% 2.52/2.70         | (v2_struct_0 @ sk_C)
% 2.52/2.70         | (v2_struct_0 @ sk_A)
% 2.52/2.70         | (v2_struct_0 @ sk_D_1)))
% 2.52/2.70         <= (~
% 2.52/2.70             ((v5_pre_topc @ 
% 2.52/2.70               (k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F) @ 
% 2.52/2.70               (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D_1)) & 
% 2.52/2.70             ((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) & 
% 2.52/2.70             ((v1_funct_1 @ sk_E_1)) & 
% 2.52/2.70             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.70               (u1_struct_0 @ sk_D_1))) & 
% 2.52/2.70             ((v5_pre_topc @ sk_E_1 @ sk_B @ sk_D_1)) & 
% 2.52/2.70             ((m1_subset_1 @ sk_E_1 @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.70             ((m1_subset_1 @ sk_F @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.70             ((v5_pre_topc @ sk_F @ sk_C @ sk_D_1)) & 
% 2.52/2.70             ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.70               (u1_struct_0 @ sk_D_1))) & 
% 2.52/2.70             ((v1_funct_1 @ sk_F)) & 
% 2.52/2.70             ((l1_pre_topc @ sk_D_1)) & 
% 2.52/2.70             ((v2_pre_topc @ sk_D_1)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['134', '135'])).
% 2.52/2.70  thf('137', plain,
% 2.52/2.70      ((~ (v2_struct_0 @ sk_D_1)) <= (~ ((v2_struct_0 @ sk_D_1)))),
% 2.52/2.70      inference('split', [status(esa)], ['52'])).
% 2.52/2.70  thf('138', plain,
% 2.52/2.70      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B)))
% 2.52/2.70         <= (~ ((v2_struct_0 @ sk_D_1)) & 
% 2.52/2.70             ~
% 2.52/2.70             ((v5_pre_topc @ 
% 2.52/2.70               (k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F) @ 
% 2.52/2.70               (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D_1)) & 
% 2.52/2.70             ((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) & 
% 2.52/2.70             ((v1_funct_1 @ sk_E_1)) & 
% 2.52/2.70             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.70               (u1_struct_0 @ sk_D_1))) & 
% 2.52/2.70             ((v5_pre_topc @ sk_E_1 @ sk_B @ sk_D_1)) & 
% 2.52/2.70             ((m1_subset_1 @ sk_E_1 @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.70             ((m1_subset_1 @ sk_F @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.70             ((v5_pre_topc @ sk_F @ sk_C @ sk_D_1)) & 
% 2.52/2.70             ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.70               (u1_struct_0 @ sk_D_1))) & 
% 2.52/2.70             ((v1_funct_1 @ sk_F)) & 
% 2.52/2.70             ((l1_pre_topc @ sk_D_1)) & 
% 2.52/2.70             ((v2_pre_topc @ sk_D_1)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['136', '137'])).
% 2.52/2.70  thf('139', plain, (~ (v2_struct_0 @ sk_A)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('140', plain,
% 2.52/2.70      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C)))
% 2.52/2.70         <= (~ ((v2_struct_0 @ sk_D_1)) & 
% 2.52/2.70             ~
% 2.52/2.70             ((v5_pre_topc @ 
% 2.52/2.70               (k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F) @ 
% 2.52/2.70               (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D_1)) & 
% 2.52/2.70             ((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) & 
% 2.52/2.70             ((v1_funct_1 @ sk_E_1)) & 
% 2.52/2.70             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.70               (u1_struct_0 @ sk_D_1))) & 
% 2.52/2.70             ((v5_pre_topc @ sk_E_1 @ sk_B @ sk_D_1)) & 
% 2.52/2.70             ((m1_subset_1 @ sk_E_1 @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.70             ((m1_subset_1 @ sk_F @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.70             ((v5_pre_topc @ sk_F @ sk_C @ sk_D_1)) & 
% 2.52/2.70             ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.70               (u1_struct_0 @ sk_D_1))) & 
% 2.52/2.70             ((v1_funct_1 @ sk_F)) & 
% 2.52/2.70             ((l1_pre_topc @ sk_D_1)) & 
% 2.52/2.70             ((v2_pre_topc @ sk_D_1)))),
% 2.52/2.70      inference('clc', [status(thm)], ['138', '139'])).
% 2.52/2.70  thf('141', plain, (~ (v2_struct_0 @ sk_B)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('142', plain,
% 2.52/2.70      (((v2_struct_0 @ sk_C))
% 2.52/2.70         <= (~ ((v2_struct_0 @ sk_D_1)) & 
% 2.52/2.70             ~
% 2.52/2.70             ((v5_pre_topc @ 
% 2.52/2.70               (k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F) @ 
% 2.52/2.70               (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D_1)) & 
% 2.52/2.70             ((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) & 
% 2.52/2.70             ((v1_funct_1 @ sk_E_1)) & 
% 2.52/2.70             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.70               (u1_struct_0 @ sk_D_1))) & 
% 2.52/2.70             ((v5_pre_topc @ sk_E_1 @ sk_B @ sk_D_1)) & 
% 2.52/2.70             ((m1_subset_1 @ sk_E_1 @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.70             ((m1_subset_1 @ sk_F @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.70             ((v5_pre_topc @ sk_F @ sk_C @ sk_D_1)) & 
% 2.52/2.70             ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.70               (u1_struct_0 @ sk_D_1))) & 
% 2.52/2.70             ((v1_funct_1 @ sk_F)) & 
% 2.52/2.70             ((l1_pre_topc @ sk_D_1)) & 
% 2.52/2.70             ((v2_pre_topc @ sk_D_1)))),
% 2.52/2.70      inference('clc', [status(thm)], ['140', '141'])).
% 2.52/2.70  thf('143', plain, (~ (v2_struct_0 @ sk_C)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('144', plain,
% 2.52/2.70      (((v5_pre_topc @ 
% 2.52/2.70         (k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F) @ 
% 2.52/2.70         (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D_1)) | 
% 2.52/2.70       ~ ((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) | ~ ((v2_pre_topc @ sk_D_1)) | 
% 2.52/2.70       ~ ((l1_pre_topc @ sk_D_1)) | ~ ((v1_funct_1 @ sk_F)) | 
% 2.52/2.70       ~ ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))) | 
% 2.52/2.70       ~ ((v5_pre_topc @ sk_F @ sk_C @ sk_D_1)) | 
% 2.52/2.70       ~
% 2.52/2.70       ((m1_subset_1 @ sk_F @ 
% 2.52/2.70         (k1_zfmisc_1 @ 
% 2.52/2.70          (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) | 
% 2.52/2.70       ~
% 2.52/2.70       ((m1_subset_1 @ sk_E_1 @ 
% 2.52/2.70         (k1_zfmisc_1 @ 
% 2.52/2.70          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) | 
% 2.52/2.70       ~ ((v5_pre_topc @ sk_E_1 @ sk_B @ sk_D_1)) | 
% 2.52/2.70       ~
% 2.52/2.70       ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))) | 
% 2.52/2.70       ~ ((v1_funct_1 @ sk_E_1)) | ((v2_struct_0 @ sk_D_1))),
% 2.52/2.70      inference('sup-', [status(thm)], ['142', '143'])).
% 2.52/2.70  thf('145', plain,
% 2.52/2.70      (((v2_pre_topc @ sk_D_1)) | ~ ((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) | 
% 2.52/2.70       ~ ((r1_tsep_1 @ sk_B @ sk_C))),
% 2.52/2.70      inference('split', [status(esa)], ['28'])).
% 2.52/2.70  thf('146', plain,
% 2.52/2.70      (((l1_pre_topc @ sk_D_1)) | ~ ((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) | 
% 2.52/2.70       ~ ((r1_tsep_1 @ sk_B @ sk_C))),
% 2.52/2.70      inference('split', [status(esa)], ['26'])).
% 2.52/2.70  thf('147', plain,
% 2.52/2.70      (((v1_funct_1 @ sk_F)) | ~ ((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) | 
% 2.52/2.70       ~ ((r1_tsep_1 @ sk_B @ sk_C))),
% 2.52/2.70      inference('split', [status(esa)], ['20'])).
% 2.52/2.70  thf('148', plain,
% 2.52/2.70      (((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))) | 
% 2.52/2.70       ~ ((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) | ~ ((r1_tsep_1 @ sk_B @ sk_C))),
% 2.52/2.70      inference('split', [status(esa)], ['22'])).
% 2.52/2.70  thf('149', plain,
% 2.52/2.70      (((v5_pre_topc @ sk_F @ sk_C @ sk_D_1)) | 
% 2.52/2.70       ~ ((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) | ~ ((r1_tsep_1 @ sk_B @ sk_C))),
% 2.52/2.70      inference('split', [status(esa)], ['111'])).
% 2.52/2.70  thf('150', plain,
% 2.52/2.70      (((m1_subset_1 @ sk_F @ 
% 2.52/2.70         (k1_zfmisc_1 @ 
% 2.52/2.70          (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) | 
% 2.52/2.70       ~ ((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) | ~ ((r1_tsep_1 @ sk_B @ sk_C))),
% 2.52/2.70      inference('split', [status(esa)], ['24'])).
% 2.52/2.70  thf('151', plain,
% 2.52/2.70      (((v5_pre_topc @ sk_E_1 @ sk_B @ sk_D_1)) | 
% 2.52/2.70       ~ ((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) | ~ ((r1_tsep_1 @ sk_B @ sk_C))),
% 2.52/2.70      inference('split', [status(esa)], ['104'])).
% 2.52/2.70  thf('152', plain,
% 2.52/2.70      (((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))) | 
% 2.52/2.70       ~ ((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) | ~ ((r1_tsep_1 @ sk_B @ sk_C))),
% 2.52/2.70      inference('split', [status(esa)], ['31'])).
% 2.52/2.70  thf('153', plain,
% 2.52/2.70      (((v1_funct_1 @ sk_E_1)) | ~ ((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) | 
% 2.52/2.70       ~ ((r1_tsep_1 @ sk_B @ sk_C))),
% 2.52/2.70      inference('split', [status(esa)], ['10'])).
% 2.52/2.70  thf('154', plain,
% 2.52/2.70      (~ ((v2_struct_0 @ sk_D_1)) | ~ ((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) | 
% 2.52/2.70       ~ ((r1_tsep_1 @ sk_B @ sk_C))),
% 2.52/2.70      inference('split', [status(esa)], ['52'])).
% 2.52/2.70  thf('155', plain,
% 2.52/2.70      (((r1_tsep_1 @ sk_B @ sk_C)) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('split', [status(esa)], ['0'])).
% 2.52/2.70  thf('156', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('157', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('158', plain,
% 2.52/2.70      (![X10 : $i, X11 : $i, X12 : $i]:
% 2.52/2.70         ((v2_struct_0 @ X10)
% 2.52/2.70          | ~ (m1_pre_topc @ X10 @ X11)
% 2.52/2.70          | ~ (r1_tsep_1 @ X10 @ X12)
% 2.52/2.70          | (v1_funct_1 @ (sk_E @ X12 @ X10 @ X11))
% 2.52/2.70          | (r3_tsep_1 @ X11 @ X10 @ X12)
% 2.52/2.70          | ~ (m1_pre_topc @ X12 @ X11)
% 2.52/2.70          | (v2_struct_0 @ X12)
% 2.52/2.70          | ~ (l1_pre_topc @ X11)
% 2.52/2.70          | ~ (v2_pre_topc @ X11)
% 2.52/2.70          | (v2_struct_0 @ X11))),
% 2.52/2.70      inference('cnf', [status(esa)], [t135_tmap_1])).
% 2.52/2.70  thf('159', plain,
% 2.52/2.70      (![X0 : $i]:
% 2.52/2.70         ((v2_struct_0 @ sk_A)
% 2.52/2.70          | ~ (v2_pre_topc @ sk_A)
% 2.52/2.70          | ~ (l1_pre_topc @ sk_A)
% 2.52/2.70          | (v2_struct_0 @ X0)
% 2.52/2.70          | ~ (m1_pre_topc @ X0 @ sk_A)
% 2.52/2.70          | (r3_tsep_1 @ sk_A @ sk_B @ X0)
% 2.52/2.70          | (v1_funct_1 @ (sk_E @ X0 @ sk_B @ sk_A))
% 2.52/2.70          | ~ (r1_tsep_1 @ sk_B @ X0)
% 2.52/2.70          | (v2_struct_0 @ sk_B))),
% 2.52/2.70      inference('sup-', [status(thm)], ['157', '158'])).
% 2.52/2.70  thf('160', plain, ((v2_pre_topc @ sk_A)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('161', plain, ((l1_pre_topc @ sk_A)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('162', plain,
% 2.52/2.70      (![X0 : $i]:
% 2.52/2.70         ((v2_struct_0 @ sk_A)
% 2.52/2.70          | (v2_struct_0 @ X0)
% 2.52/2.70          | ~ (m1_pre_topc @ X0 @ sk_A)
% 2.52/2.70          | (r3_tsep_1 @ sk_A @ sk_B @ X0)
% 2.52/2.70          | (v1_funct_1 @ (sk_E @ X0 @ sk_B @ sk_A))
% 2.52/2.70          | ~ (r1_tsep_1 @ sk_B @ X0)
% 2.52/2.70          | (v2_struct_0 @ sk_B))),
% 2.52/2.70      inference('demod', [status(thm)], ['159', '160', '161'])).
% 2.52/2.70  thf('163', plain,
% 2.52/2.70      (((v2_struct_0 @ sk_B)
% 2.52/2.70        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 2.52/2.70        | (v1_funct_1 @ (sk_E @ sk_C @ sk_B @ sk_A))
% 2.52/2.70        | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70        | (v2_struct_0 @ sk_C)
% 2.52/2.70        | (v2_struct_0 @ sk_A))),
% 2.52/2.70      inference('sup-', [status(thm)], ['156', '162'])).
% 2.52/2.70  thf('164', plain,
% 2.52/2.70      ((((v2_struct_0 @ sk_A)
% 2.52/2.70         | (v2_struct_0 @ sk_C)
% 2.52/2.70         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70         | (v1_funct_1 @ (sk_E @ sk_C @ sk_B @ sk_A))
% 2.52/2.70         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['155', '163'])).
% 2.52/2.70  thf('165', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('166', plain,
% 2.52/2.70      (((r1_tsep_1 @ sk_B @ sk_C)) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('split', [status(esa)], ['0'])).
% 2.52/2.70  thf('167', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('168', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('169', plain,
% 2.52/2.70      (![X10 : $i, X11 : $i, X12 : $i]:
% 2.52/2.70         ((v2_struct_0 @ X10)
% 2.52/2.70          | ~ (m1_pre_topc @ X10 @ X11)
% 2.52/2.70          | ~ (r1_tsep_1 @ X10 @ X12)
% 2.52/2.70          | (v1_funct_1 @ 
% 2.52/2.70             (k3_tmap_1 @ X11 @ (sk_D @ X12 @ X10 @ X11) @ 
% 2.52/2.70              (k1_tsep_1 @ X11 @ X10 @ X12) @ X12 @ (sk_E @ X12 @ X10 @ X11)))
% 2.52/2.70          | (r3_tsep_1 @ X11 @ X10 @ X12)
% 2.52/2.70          | ~ (m1_pre_topc @ X12 @ X11)
% 2.52/2.70          | (v2_struct_0 @ X12)
% 2.52/2.70          | ~ (l1_pre_topc @ X11)
% 2.52/2.70          | ~ (v2_pre_topc @ X11)
% 2.52/2.70          | (v2_struct_0 @ X11))),
% 2.52/2.70      inference('cnf', [status(esa)], [t135_tmap_1])).
% 2.52/2.70  thf('170', plain,
% 2.52/2.70      (![X0 : $i]:
% 2.52/2.70         ((v2_struct_0 @ sk_A)
% 2.52/2.70          | ~ (v2_pre_topc @ sk_A)
% 2.52/2.70          | ~ (l1_pre_topc @ sk_A)
% 2.52/2.70          | (v2_struct_0 @ X0)
% 2.52/2.70          | ~ (m1_pre_topc @ X0 @ sk_A)
% 2.52/2.70          | (r3_tsep_1 @ sk_A @ sk_B @ X0)
% 2.52/2.70          | (v1_funct_1 @ 
% 2.52/2.70             (k3_tmap_1 @ sk_A @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 2.52/2.70              (k1_tsep_1 @ sk_A @ sk_B @ X0) @ X0 @ (sk_E @ X0 @ sk_B @ sk_A)))
% 2.52/2.70          | ~ (r1_tsep_1 @ sk_B @ X0)
% 2.52/2.70          | (v2_struct_0 @ sk_B))),
% 2.52/2.70      inference('sup-', [status(thm)], ['168', '169'])).
% 2.52/2.70  thf('171', plain, ((v2_pre_topc @ sk_A)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('172', plain, ((l1_pre_topc @ sk_A)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('173', plain,
% 2.52/2.70      (![X0 : $i]:
% 2.52/2.70         ((v2_struct_0 @ sk_A)
% 2.52/2.70          | (v2_struct_0 @ X0)
% 2.52/2.70          | ~ (m1_pre_topc @ X0 @ sk_A)
% 2.52/2.70          | (r3_tsep_1 @ sk_A @ sk_B @ X0)
% 2.52/2.70          | (v1_funct_1 @ 
% 2.52/2.70             (k3_tmap_1 @ sk_A @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 2.52/2.70              (k1_tsep_1 @ sk_A @ sk_B @ X0) @ X0 @ (sk_E @ X0 @ sk_B @ sk_A)))
% 2.52/2.70          | ~ (r1_tsep_1 @ sk_B @ X0)
% 2.52/2.70          | (v2_struct_0 @ sk_B))),
% 2.52/2.70      inference('demod', [status(thm)], ['170', '171', '172'])).
% 2.52/2.70  thf('174', plain,
% 2.52/2.70      (((v2_struct_0 @ sk_B)
% 2.52/2.70        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 2.52/2.70        | (v1_funct_1 @ 
% 2.52/2.70           (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70            (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.70            (sk_E @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70        | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70        | (v2_struct_0 @ sk_C)
% 2.52/2.70        | (v2_struct_0 @ sk_A))),
% 2.52/2.70      inference('sup-', [status(thm)], ['167', '173'])).
% 2.52/2.70  thf('175', plain,
% 2.52/2.70      ((((v2_struct_0 @ sk_A)
% 2.52/2.70         | (v2_struct_0 @ sk_C)
% 2.52/2.70         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70         | (v1_funct_1 @ 
% 2.52/2.70            (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70             (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.70             (sk_E @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['166', '174'])).
% 2.52/2.70  thf('176', plain,
% 2.52/2.70      (((r1_tsep_1 @ sk_B @ sk_C)) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('split', [status(esa)], ['0'])).
% 2.52/2.70  thf('177', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('178', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('179', plain,
% 2.52/2.70      (![X10 : $i, X11 : $i, X12 : $i]:
% 2.52/2.70         ((v2_struct_0 @ X10)
% 2.52/2.70          | ~ (m1_pre_topc @ X10 @ X11)
% 2.52/2.70          | ~ (r1_tsep_1 @ X10 @ X12)
% 2.52/2.70          | (v1_funct_2 @ 
% 2.52/2.70             (k3_tmap_1 @ X11 @ (sk_D @ X12 @ X10 @ X11) @ 
% 2.52/2.70              (k1_tsep_1 @ X11 @ X10 @ X12) @ X12 @ (sk_E @ X12 @ X10 @ X11)) @ 
% 2.52/2.70             (u1_struct_0 @ X12) @ (u1_struct_0 @ (sk_D @ X12 @ X10 @ X11)))
% 2.52/2.70          | (r3_tsep_1 @ X11 @ X10 @ X12)
% 2.52/2.70          | ~ (m1_pre_topc @ X12 @ X11)
% 2.52/2.70          | (v2_struct_0 @ X12)
% 2.52/2.70          | ~ (l1_pre_topc @ X11)
% 2.52/2.70          | ~ (v2_pre_topc @ X11)
% 2.52/2.70          | (v2_struct_0 @ X11))),
% 2.52/2.70      inference('cnf', [status(esa)], [t135_tmap_1])).
% 2.52/2.70  thf('180', plain,
% 2.52/2.70      (![X0 : $i]:
% 2.52/2.70         ((v2_struct_0 @ sk_A)
% 2.52/2.70          | ~ (v2_pre_topc @ sk_A)
% 2.52/2.70          | ~ (l1_pre_topc @ sk_A)
% 2.52/2.70          | (v2_struct_0 @ X0)
% 2.52/2.70          | ~ (m1_pre_topc @ X0 @ sk_A)
% 2.52/2.70          | (r3_tsep_1 @ sk_A @ sk_B @ X0)
% 2.52/2.70          | (v1_funct_2 @ 
% 2.52/2.70             (k3_tmap_1 @ sk_A @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 2.52/2.70              (k1_tsep_1 @ sk_A @ sk_B @ X0) @ X0 @ (sk_E @ X0 @ sk_B @ sk_A)) @ 
% 2.52/2.70             (u1_struct_0 @ X0) @ (u1_struct_0 @ (sk_D @ X0 @ sk_B @ sk_A)))
% 2.52/2.70          | ~ (r1_tsep_1 @ sk_B @ X0)
% 2.52/2.70          | (v2_struct_0 @ sk_B))),
% 2.52/2.70      inference('sup-', [status(thm)], ['178', '179'])).
% 2.52/2.70  thf('181', plain, ((v2_pre_topc @ sk_A)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('182', plain, ((l1_pre_topc @ sk_A)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('183', plain,
% 2.52/2.70      (![X0 : $i]:
% 2.52/2.70         ((v2_struct_0 @ sk_A)
% 2.52/2.70          | (v2_struct_0 @ X0)
% 2.52/2.70          | ~ (m1_pre_topc @ X0 @ sk_A)
% 2.52/2.70          | (r3_tsep_1 @ sk_A @ sk_B @ X0)
% 2.52/2.70          | (v1_funct_2 @ 
% 2.52/2.70             (k3_tmap_1 @ sk_A @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 2.52/2.70              (k1_tsep_1 @ sk_A @ sk_B @ X0) @ X0 @ (sk_E @ X0 @ sk_B @ sk_A)) @ 
% 2.52/2.70             (u1_struct_0 @ X0) @ (u1_struct_0 @ (sk_D @ X0 @ sk_B @ sk_A)))
% 2.52/2.70          | ~ (r1_tsep_1 @ sk_B @ X0)
% 2.52/2.70          | (v2_struct_0 @ sk_B))),
% 2.52/2.70      inference('demod', [status(thm)], ['180', '181', '182'])).
% 2.52/2.70  thf('184', plain,
% 2.52/2.70      (((v2_struct_0 @ sk_B)
% 2.52/2.70        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 2.52/2.70        | (v1_funct_2 @ 
% 2.52/2.70           (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70            (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.70            (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70           (u1_struct_0 @ sk_C) @ (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70        | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70        | (v2_struct_0 @ sk_C)
% 2.52/2.70        | (v2_struct_0 @ sk_A))),
% 2.52/2.70      inference('sup-', [status(thm)], ['177', '183'])).
% 2.52/2.70  thf('185', plain,
% 2.52/2.70      ((((v2_struct_0 @ sk_A)
% 2.52/2.70         | (v2_struct_0 @ sk_C)
% 2.52/2.70         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70         | (v1_funct_2 @ 
% 2.52/2.70            (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70             (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.70             (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70            (u1_struct_0 @ sk_C) @ (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['176', '184'])).
% 2.52/2.70  thf('186', plain,
% 2.52/2.70      (((r1_tsep_1 @ sk_B @ sk_C)) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('split', [status(esa)], ['0'])).
% 2.52/2.70  thf('187', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('188', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('189', plain,
% 2.52/2.70      (![X10 : $i, X11 : $i, X12 : $i]:
% 2.52/2.70         ((v2_struct_0 @ X10)
% 2.52/2.70          | ~ (m1_pre_topc @ X10 @ X11)
% 2.52/2.70          | ~ (r1_tsep_1 @ X10 @ X12)
% 2.52/2.70          | (m1_subset_1 @ 
% 2.52/2.70             (k3_tmap_1 @ X11 @ (sk_D @ X12 @ X10 @ X11) @ 
% 2.52/2.70              (k1_tsep_1 @ X11 @ X10 @ X12) @ X12 @ (sk_E @ X12 @ X10 @ X11)) @ 
% 2.52/2.70             (k1_zfmisc_1 @ 
% 2.52/2.70              (k2_zfmisc_1 @ (u1_struct_0 @ X12) @ 
% 2.52/2.70               (u1_struct_0 @ (sk_D @ X12 @ X10 @ X11)))))
% 2.52/2.70          | (r3_tsep_1 @ X11 @ X10 @ X12)
% 2.52/2.70          | ~ (m1_pre_topc @ X12 @ X11)
% 2.52/2.70          | (v2_struct_0 @ X12)
% 2.52/2.70          | ~ (l1_pre_topc @ X11)
% 2.52/2.70          | ~ (v2_pre_topc @ X11)
% 2.52/2.70          | (v2_struct_0 @ X11))),
% 2.52/2.70      inference('cnf', [status(esa)], [t135_tmap_1])).
% 2.52/2.70  thf('190', plain,
% 2.52/2.70      (![X0 : $i]:
% 2.52/2.70         ((v2_struct_0 @ sk_A)
% 2.52/2.70          | ~ (v2_pre_topc @ sk_A)
% 2.52/2.70          | ~ (l1_pre_topc @ sk_A)
% 2.52/2.70          | (v2_struct_0 @ X0)
% 2.52/2.70          | ~ (m1_pre_topc @ X0 @ sk_A)
% 2.52/2.70          | (r3_tsep_1 @ sk_A @ sk_B @ X0)
% 2.52/2.70          | (m1_subset_1 @ 
% 2.52/2.70             (k3_tmap_1 @ sk_A @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 2.52/2.70              (k1_tsep_1 @ sk_A @ sk_B @ X0) @ X0 @ (sk_E @ X0 @ sk_B @ sk_A)) @ 
% 2.52/2.70             (k1_zfmisc_1 @ 
% 2.52/2.70              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ 
% 2.52/2.70               (u1_struct_0 @ (sk_D @ X0 @ sk_B @ sk_A)))))
% 2.52/2.70          | ~ (r1_tsep_1 @ sk_B @ X0)
% 2.52/2.70          | (v2_struct_0 @ sk_B))),
% 2.52/2.70      inference('sup-', [status(thm)], ['188', '189'])).
% 2.52/2.70  thf('191', plain, ((v2_pre_topc @ sk_A)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('192', plain, ((l1_pre_topc @ sk_A)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('193', plain,
% 2.52/2.70      (![X0 : $i]:
% 2.52/2.70         ((v2_struct_0 @ sk_A)
% 2.52/2.70          | (v2_struct_0 @ X0)
% 2.52/2.70          | ~ (m1_pre_topc @ X0 @ sk_A)
% 2.52/2.70          | (r3_tsep_1 @ sk_A @ sk_B @ X0)
% 2.52/2.70          | (m1_subset_1 @ 
% 2.52/2.70             (k3_tmap_1 @ sk_A @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 2.52/2.70              (k1_tsep_1 @ sk_A @ sk_B @ X0) @ X0 @ (sk_E @ X0 @ sk_B @ sk_A)) @ 
% 2.52/2.70             (k1_zfmisc_1 @ 
% 2.52/2.70              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ 
% 2.52/2.70               (u1_struct_0 @ (sk_D @ X0 @ sk_B @ sk_A)))))
% 2.52/2.70          | ~ (r1_tsep_1 @ sk_B @ X0)
% 2.52/2.70          | (v2_struct_0 @ sk_B))),
% 2.52/2.70      inference('demod', [status(thm)], ['190', '191', '192'])).
% 2.52/2.70  thf('194', plain,
% 2.52/2.70      (((v2_struct_0 @ sk_B)
% 2.52/2.70        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 2.52/2.70        | (m1_subset_1 @ 
% 2.52/2.70           (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70            (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.70            (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70           (k1_zfmisc_1 @ 
% 2.52/2.70            (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.70             (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.52/2.70        | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70        | (v2_struct_0 @ sk_C)
% 2.52/2.70        | (v2_struct_0 @ sk_A))),
% 2.52/2.70      inference('sup-', [status(thm)], ['187', '193'])).
% 2.52/2.70  thf('195', plain,
% 2.52/2.70      ((((v2_struct_0 @ sk_A)
% 2.52/2.70         | (v2_struct_0 @ sk_C)
% 2.52/2.70         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70         | (m1_subset_1 @ 
% 2.52/2.70            (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70             (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.70             (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70            (k1_zfmisc_1 @ 
% 2.52/2.70             (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.70              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.52/2.70         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['186', '194'])).
% 2.52/2.70  thf('196', plain,
% 2.52/2.70      (((r1_tsep_1 @ sk_B @ sk_C)) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('split', [status(esa)], ['0'])).
% 2.52/2.70  thf('197', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('198', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('199', plain,
% 2.52/2.70      (![X10 : $i, X11 : $i, X12 : $i]:
% 2.52/2.70         ((v2_struct_0 @ X10)
% 2.52/2.70          | ~ (m1_pre_topc @ X10 @ X11)
% 2.52/2.70          | ~ (r1_tsep_1 @ X10 @ X12)
% 2.52/2.70          | (v2_pre_topc @ (sk_D @ X12 @ X10 @ X11))
% 2.52/2.70          | (r3_tsep_1 @ X11 @ X10 @ X12)
% 2.52/2.70          | ~ (m1_pre_topc @ X12 @ X11)
% 2.52/2.70          | (v2_struct_0 @ X12)
% 2.52/2.70          | ~ (l1_pre_topc @ X11)
% 2.52/2.70          | ~ (v2_pre_topc @ X11)
% 2.52/2.70          | (v2_struct_0 @ X11))),
% 2.52/2.70      inference('cnf', [status(esa)], [t135_tmap_1])).
% 2.52/2.70  thf('200', plain,
% 2.52/2.70      (![X0 : $i]:
% 2.52/2.70         ((v2_struct_0 @ sk_A)
% 2.52/2.70          | ~ (v2_pre_topc @ sk_A)
% 2.52/2.70          | ~ (l1_pre_topc @ sk_A)
% 2.52/2.70          | (v2_struct_0 @ X0)
% 2.52/2.70          | ~ (m1_pre_topc @ X0 @ sk_A)
% 2.52/2.70          | (r3_tsep_1 @ sk_A @ sk_B @ X0)
% 2.52/2.70          | (v2_pre_topc @ (sk_D @ X0 @ sk_B @ sk_A))
% 2.52/2.70          | ~ (r1_tsep_1 @ sk_B @ X0)
% 2.52/2.70          | (v2_struct_0 @ sk_B))),
% 2.52/2.70      inference('sup-', [status(thm)], ['198', '199'])).
% 2.52/2.70  thf('201', plain, ((v2_pre_topc @ sk_A)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('202', plain, ((l1_pre_topc @ sk_A)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('203', plain,
% 2.52/2.70      (![X0 : $i]:
% 2.52/2.70         ((v2_struct_0 @ sk_A)
% 2.52/2.70          | (v2_struct_0 @ X0)
% 2.52/2.70          | ~ (m1_pre_topc @ X0 @ sk_A)
% 2.52/2.70          | (r3_tsep_1 @ sk_A @ sk_B @ X0)
% 2.52/2.70          | (v2_pre_topc @ (sk_D @ X0 @ sk_B @ sk_A))
% 2.52/2.70          | ~ (r1_tsep_1 @ sk_B @ X0)
% 2.52/2.70          | (v2_struct_0 @ sk_B))),
% 2.52/2.70      inference('demod', [status(thm)], ['200', '201', '202'])).
% 2.52/2.70  thf('204', plain,
% 2.52/2.70      (((v2_struct_0 @ sk_B)
% 2.52/2.70        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 2.52/2.70        | (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70        | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70        | (v2_struct_0 @ sk_C)
% 2.52/2.70        | (v2_struct_0 @ sk_A))),
% 2.52/2.70      inference('sup-', [status(thm)], ['197', '203'])).
% 2.52/2.70  thf('205', plain,
% 2.52/2.70      ((((v2_struct_0 @ sk_A)
% 2.52/2.70         | (v2_struct_0 @ sk_C)
% 2.52/2.70         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70         | (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['196', '204'])).
% 2.52/2.70  thf('206', plain,
% 2.52/2.70      (((r1_tsep_1 @ sk_B @ sk_C)) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('split', [status(esa)], ['0'])).
% 2.52/2.70  thf('207', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('208', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('209', plain,
% 2.52/2.70      (![X10 : $i, X11 : $i, X12 : $i]:
% 2.52/2.70         ((v2_struct_0 @ X10)
% 2.52/2.70          | ~ (m1_pre_topc @ X10 @ X11)
% 2.52/2.70          | ~ (r1_tsep_1 @ X10 @ X12)
% 2.52/2.70          | (l1_pre_topc @ (sk_D @ X12 @ X10 @ X11))
% 2.52/2.70          | (r3_tsep_1 @ X11 @ X10 @ X12)
% 2.52/2.70          | ~ (m1_pre_topc @ X12 @ X11)
% 2.52/2.70          | (v2_struct_0 @ X12)
% 2.52/2.70          | ~ (l1_pre_topc @ X11)
% 2.52/2.70          | ~ (v2_pre_topc @ X11)
% 2.52/2.70          | (v2_struct_0 @ X11))),
% 2.52/2.70      inference('cnf', [status(esa)], [t135_tmap_1])).
% 2.52/2.70  thf('210', plain,
% 2.52/2.70      (![X0 : $i]:
% 2.52/2.70         ((v2_struct_0 @ sk_A)
% 2.52/2.70          | ~ (v2_pre_topc @ sk_A)
% 2.52/2.70          | ~ (l1_pre_topc @ sk_A)
% 2.52/2.70          | (v2_struct_0 @ X0)
% 2.52/2.70          | ~ (m1_pre_topc @ X0 @ sk_A)
% 2.52/2.70          | (r3_tsep_1 @ sk_A @ sk_B @ X0)
% 2.52/2.70          | (l1_pre_topc @ (sk_D @ X0 @ sk_B @ sk_A))
% 2.52/2.70          | ~ (r1_tsep_1 @ sk_B @ X0)
% 2.52/2.70          | (v2_struct_0 @ sk_B))),
% 2.52/2.70      inference('sup-', [status(thm)], ['208', '209'])).
% 2.52/2.70  thf('211', plain, ((v2_pre_topc @ sk_A)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('212', plain, ((l1_pre_topc @ sk_A)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('213', plain,
% 2.52/2.70      (![X0 : $i]:
% 2.52/2.70         ((v2_struct_0 @ sk_A)
% 2.52/2.70          | (v2_struct_0 @ X0)
% 2.52/2.70          | ~ (m1_pre_topc @ X0 @ sk_A)
% 2.52/2.70          | (r3_tsep_1 @ sk_A @ sk_B @ X0)
% 2.52/2.70          | (l1_pre_topc @ (sk_D @ X0 @ sk_B @ sk_A))
% 2.52/2.70          | ~ (r1_tsep_1 @ sk_B @ X0)
% 2.52/2.70          | (v2_struct_0 @ sk_B))),
% 2.52/2.70      inference('demod', [status(thm)], ['210', '211', '212'])).
% 2.52/2.70  thf('214', plain,
% 2.52/2.70      (((v2_struct_0 @ sk_B)
% 2.52/2.70        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 2.52/2.70        | (l1_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70        | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70        | (v2_struct_0 @ sk_C)
% 2.52/2.70        | (v2_struct_0 @ sk_A))),
% 2.52/2.70      inference('sup-', [status(thm)], ['207', '213'])).
% 2.52/2.70  thf('215', plain,
% 2.52/2.70      ((((v2_struct_0 @ sk_A)
% 2.52/2.70         | (v2_struct_0 @ sk_C)
% 2.52/2.70         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70         | (l1_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['206', '214'])).
% 2.52/2.70  thf('216', plain,
% 2.52/2.70      (((r1_tsep_1 @ sk_B @ sk_C)) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('split', [status(esa)], ['0'])).
% 2.52/2.70  thf('217', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('218', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('219', plain,
% 2.52/2.70      (![X10 : $i, X11 : $i, X12 : $i]:
% 2.52/2.70         ((v2_struct_0 @ X10)
% 2.52/2.70          | ~ (m1_pre_topc @ X10 @ X11)
% 2.52/2.70          | ~ (r1_tsep_1 @ X10 @ X12)
% 2.52/2.70          | (v1_funct_1 @ 
% 2.52/2.70             (k3_tmap_1 @ X11 @ (sk_D @ X12 @ X10 @ X11) @ 
% 2.52/2.70              (k1_tsep_1 @ X11 @ X10 @ X12) @ X10 @ (sk_E @ X12 @ X10 @ X11)))
% 2.52/2.70          | (r3_tsep_1 @ X11 @ X10 @ X12)
% 2.52/2.70          | ~ (m1_pre_topc @ X12 @ X11)
% 2.52/2.70          | (v2_struct_0 @ X12)
% 2.52/2.70          | ~ (l1_pre_topc @ X11)
% 2.52/2.70          | ~ (v2_pre_topc @ X11)
% 2.52/2.70          | (v2_struct_0 @ X11))),
% 2.52/2.70      inference('cnf', [status(esa)], [t135_tmap_1])).
% 2.52/2.70  thf('220', plain,
% 2.52/2.70      (![X0 : $i]:
% 2.52/2.70         ((v2_struct_0 @ sk_A)
% 2.52/2.70          | ~ (v2_pre_topc @ sk_A)
% 2.52/2.70          | ~ (l1_pre_topc @ sk_A)
% 2.52/2.70          | (v2_struct_0 @ X0)
% 2.52/2.70          | ~ (m1_pre_topc @ X0 @ sk_A)
% 2.52/2.70          | (r3_tsep_1 @ sk_A @ sk_B @ X0)
% 2.52/2.70          | (v1_funct_1 @ 
% 2.52/2.70             (k3_tmap_1 @ sk_A @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 2.52/2.70              (k1_tsep_1 @ sk_A @ sk_B @ X0) @ sk_B @ (sk_E @ X0 @ sk_B @ sk_A)))
% 2.52/2.70          | ~ (r1_tsep_1 @ sk_B @ X0)
% 2.52/2.70          | (v2_struct_0 @ sk_B))),
% 2.52/2.70      inference('sup-', [status(thm)], ['218', '219'])).
% 2.52/2.70  thf('221', plain, ((v2_pre_topc @ sk_A)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('222', plain, ((l1_pre_topc @ sk_A)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('223', plain,
% 2.52/2.70      (![X0 : $i]:
% 2.52/2.70         ((v2_struct_0 @ sk_A)
% 2.52/2.70          | (v2_struct_0 @ X0)
% 2.52/2.70          | ~ (m1_pre_topc @ X0 @ sk_A)
% 2.52/2.70          | (r3_tsep_1 @ sk_A @ sk_B @ X0)
% 2.52/2.70          | (v1_funct_1 @ 
% 2.52/2.70             (k3_tmap_1 @ sk_A @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 2.52/2.70              (k1_tsep_1 @ sk_A @ sk_B @ X0) @ sk_B @ (sk_E @ X0 @ sk_B @ sk_A)))
% 2.52/2.70          | ~ (r1_tsep_1 @ sk_B @ X0)
% 2.52/2.70          | (v2_struct_0 @ sk_B))),
% 2.52/2.70      inference('demod', [status(thm)], ['220', '221', '222'])).
% 2.52/2.70  thf('224', plain,
% 2.52/2.70      (((v2_struct_0 @ sk_B)
% 2.52/2.70        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 2.52/2.70        | (v1_funct_1 @ 
% 2.52/2.70           (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70            (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70            (sk_E @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70        | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70        | (v2_struct_0 @ sk_C)
% 2.52/2.70        | (v2_struct_0 @ sk_A))),
% 2.52/2.70      inference('sup-', [status(thm)], ['217', '223'])).
% 2.52/2.70  thf('225', plain,
% 2.52/2.70      ((((v2_struct_0 @ sk_A)
% 2.52/2.70         | (v2_struct_0 @ sk_C)
% 2.52/2.70         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70         | (v1_funct_1 @ 
% 2.52/2.70            (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70             (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70             (sk_E @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['216', '224'])).
% 2.52/2.70  thf('226', plain,
% 2.52/2.70      (((r1_tsep_1 @ sk_B @ sk_C)) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('split', [status(esa)], ['0'])).
% 2.52/2.70  thf('227', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('228', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('229', plain,
% 2.52/2.70      (![X10 : $i, X11 : $i, X12 : $i]:
% 2.52/2.70         ((v2_struct_0 @ X10)
% 2.52/2.70          | ~ (m1_pre_topc @ X10 @ X11)
% 2.52/2.70          | ~ (r1_tsep_1 @ X10 @ X12)
% 2.52/2.70          | (v1_funct_2 @ 
% 2.52/2.70             (k3_tmap_1 @ X11 @ (sk_D @ X12 @ X10 @ X11) @ 
% 2.52/2.70              (k1_tsep_1 @ X11 @ X10 @ X12) @ X10 @ (sk_E @ X12 @ X10 @ X11)) @ 
% 2.52/2.70             (u1_struct_0 @ X10) @ (u1_struct_0 @ (sk_D @ X12 @ X10 @ X11)))
% 2.52/2.70          | (r3_tsep_1 @ X11 @ X10 @ X12)
% 2.52/2.70          | ~ (m1_pre_topc @ X12 @ X11)
% 2.52/2.70          | (v2_struct_0 @ X12)
% 2.52/2.70          | ~ (l1_pre_topc @ X11)
% 2.52/2.70          | ~ (v2_pre_topc @ X11)
% 2.52/2.70          | (v2_struct_0 @ X11))),
% 2.52/2.70      inference('cnf', [status(esa)], [t135_tmap_1])).
% 2.52/2.70  thf('230', plain,
% 2.52/2.70      (![X0 : $i]:
% 2.52/2.70         ((v2_struct_0 @ sk_A)
% 2.52/2.70          | ~ (v2_pre_topc @ sk_A)
% 2.52/2.70          | ~ (l1_pre_topc @ sk_A)
% 2.52/2.70          | (v2_struct_0 @ X0)
% 2.52/2.70          | ~ (m1_pre_topc @ X0 @ sk_A)
% 2.52/2.70          | (r3_tsep_1 @ sk_A @ sk_B @ X0)
% 2.52/2.70          | (v1_funct_2 @ 
% 2.52/2.70             (k3_tmap_1 @ sk_A @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 2.52/2.70              (k1_tsep_1 @ sk_A @ sk_B @ X0) @ sk_B @ (sk_E @ X0 @ sk_B @ sk_A)) @ 
% 2.52/2.70             (u1_struct_0 @ sk_B) @ (u1_struct_0 @ (sk_D @ X0 @ sk_B @ sk_A)))
% 2.52/2.70          | ~ (r1_tsep_1 @ sk_B @ X0)
% 2.52/2.70          | (v2_struct_0 @ sk_B))),
% 2.52/2.70      inference('sup-', [status(thm)], ['228', '229'])).
% 2.52/2.70  thf('231', plain, ((v2_pre_topc @ sk_A)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('232', plain, ((l1_pre_topc @ sk_A)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('233', plain,
% 2.52/2.70      (![X0 : $i]:
% 2.52/2.70         ((v2_struct_0 @ sk_A)
% 2.52/2.70          | (v2_struct_0 @ X0)
% 2.52/2.70          | ~ (m1_pre_topc @ X0 @ sk_A)
% 2.52/2.70          | (r3_tsep_1 @ sk_A @ sk_B @ X0)
% 2.52/2.70          | (v1_funct_2 @ 
% 2.52/2.70             (k3_tmap_1 @ sk_A @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 2.52/2.70              (k1_tsep_1 @ sk_A @ sk_B @ X0) @ sk_B @ (sk_E @ X0 @ sk_B @ sk_A)) @ 
% 2.52/2.70             (u1_struct_0 @ sk_B) @ (u1_struct_0 @ (sk_D @ X0 @ sk_B @ sk_A)))
% 2.52/2.70          | ~ (r1_tsep_1 @ sk_B @ X0)
% 2.52/2.70          | (v2_struct_0 @ sk_B))),
% 2.52/2.70      inference('demod', [status(thm)], ['230', '231', '232'])).
% 2.52/2.70  thf('234', plain,
% 2.52/2.70      (((v2_struct_0 @ sk_B)
% 2.52/2.70        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 2.52/2.70        | (v1_funct_2 @ 
% 2.52/2.70           (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70            (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70            (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70           (u1_struct_0 @ sk_B) @ (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70        | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70        | (v2_struct_0 @ sk_C)
% 2.52/2.70        | (v2_struct_0 @ sk_A))),
% 2.52/2.70      inference('sup-', [status(thm)], ['227', '233'])).
% 2.52/2.70  thf('235', plain,
% 2.52/2.70      ((((v2_struct_0 @ sk_A)
% 2.52/2.70         | (v2_struct_0 @ sk_C)
% 2.52/2.70         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70         | (v1_funct_2 @ 
% 2.52/2.70            (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70             (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70             (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70            (u1_struct_0 @ sk_B) @ (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['226', '234'])).
% 2.52/2.70  thf('236', plain,
% 2.52/2.70      (((r1_tsep_1 @ sk_B @ sk_C)) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('split', [status(esa)], ['0'])).
% 2.52/2.70  thf('237', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('238', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('239', plain,
% 2.52/2.70      (![X10 : $i, X11 : $i, X12 : $i]:
% 2.52/2.70         ((v2_struct_0 @ X10)
% 2.52/2.70          | ~ (m1_pre_topc @ X10 @ X11)
% 2.52/2.70          | ~ (r1_tsep_1 @ X10 @ X12)
% 2.52/2.70          | (m1_subset_1 @ 
% 2.52/2.70             (k3_tmap_1 @ X11 @ (sk_D @ X12 @ X10 @ X11) @ 
% 2.52/2.70              (k1_tsep_1 @ X11 @ X10 @ X12) @ X10 @ (sk_E @ X12 @ X10 @ X11)) @ 
% 2.52/2.70             (k1_zfmisc_1 @ 
% 2.52/2.70              (k2_zfmisc_1 @ (u1_struct_0 @ X10) @ 
% 2.52/2.70               (u1_struct_0 @ (sk_D @ X12 @ X10 @ X11)))))
% 2.52/2.70          | (r3_tsep_1 @ X11 @ X10 @ X12)
% 2.52/2.70          | ~ (m1_pre_topc @ X12 @ X11)
% 2.52/2.70          | (v2_struct_0 @ X12)
% 2.52/2.70          | ~ (l1_pre_topc @ X11)
% 2.52/2.70          | ~ (v2_pre_topc @ X11)
% 2.52/2.70          | (v2_struct_0 @ X11))),
% 2.52/2.70      inference('cnf', [status(esa)], [t135_tmap_1])).
% 2.52/2.70  thf('240', plain,
% 2.52/2.70      (![X0 : $i]:
% 2.52/2.70         ((v2_struct_0 @ sk_A)
% 2.52/2.70          | ~ (v2_pre_topc @ sk_A)
% 2.52/2.70          | ~ (l1_pre_topc @ sk_A)
% 2.52/2.70          | (v2_struct_0 @ X0)
% 2.52/2.70          | ~ (m1_pre_topc @ X0 @ sk_A)
% 2.52/2.70          | (r3_tsep_1 @ sk_A @ sk_B @ X0)
% 2.52/2.70          | (m1_subset_1 @ 
% 2.52/2.70             (k3_tmap_1 @ sk_A @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 2.52/2.70              (k1_tsep_1 @ sk_A @ sk_B @ X0) @ sk_B @ (sk_E @ X0 @ sk_B @ sk_A)) @ 
% 2.52/2.70             (k1_zfmisc_1 @ 
% 2.52/2.70              (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.70               (u1_struct_0 @ (sk_D @ X0 @ sk_B @ sk_A)))))
% 2.52/2.70          | ~ (r1_tsep_1 @ sk_B @ X0)
% 2.52/2.70          | (v2_struct_0 @ sk_B))),
% 2.52/2.70      inference('sup-', [status(thm)], ['238', '239'])).
% 2.52/2.70  thf('241', plain, ((v2_pre_topc @ sk_A)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('242', plain, ((l1_pre_topc @ sk_A)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('243', plain,
% 2.52/2.70      (![X0 : $i]:
% 2.52/2.70         ((v2_struct_0 @ sk_A)
% 2.52/2.70          | (v2_struct_0 @ X0)
% 2.52/2.70          | ~ (m1_pre_topc @ X0 @ sk_A)
% 2.52/2.70          | (r3_tsep_1 @ sk_A @ sk_B @ X0)
% 2.52/2.70          | (m1_subset_1 @ 
% 2.52/2.70             (k3_tmap_1 @ sk_A @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 2.52/2.70              (k1_tsep_1 @ sk_A @ sk_B @ X0) @ sk_B @ (sk_E @ X0 @ sk_B @ sk_A)) @ 
% 2.52/2.70             (k1_zfmisc_1 @ 
% 2.52/2.70              (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.70               (u1_struct_0 @ (sk_D @ X0 @ sk_B @ sk_A)))))
% 2.52/2.70          | ~ (r1_tsep_1 @ sk_B @ X0)
% 2.52/2.70          | (v2_struct_0 @ sk_B))),
% 2.52/2.70      inference('demod', [status(thm)], ['240', '241', '242'])).
% 2.52/2.70  thf('244', plain,
% 2.52/2.70      (((v2_struct_0 @ sk_B)
% 2.52/2.70        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 2.52/2.70        | (m1_subset_1 @ 
% 2.52/2.70           (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70            (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70            (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70           (k1_zfmisc_1 @ 
% 2.52/2.70            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.70             (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.52/2.70        | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70        | (v2_struct_0 @ sk_C)
% 2.52/2.70        | (v2_struct_0 @ sk_A))),
% 2.52/2.70      inference('sup-', [status(thm)], ['237', '243'])).
% 2.52/2.70  thf('245', plain,
% 2.52/2.70      ((((v2_struct_0 @ sk_A)
% 2.52/2.70         | (v2_struct_0 @ sk_C)
% 2.52/2.70         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70         | (m1_subset_1 @ 
% 2.52/2.70            (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70             (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70             (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70            (k1_zfmisc_1 @ 
% 2.52/2.70             (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.70              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.52/2.70         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['236', '244'])).
% 2.52/2.70  thf('246', plain,
% 2.52/2.70      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 2.52/2.70         (~ (m1_subset_1 @ X4 @ 
% 2.52/2.70             (k1_zfmisc_1 @ 
% 2.52/2.70              (k2_zfmisc_1 @ (u1_struct_0 @ X5) @ (u1_struct_0 @ X6))))
% 2.52/2.70          | ~ (v1_funct_2 @ X4 @ (u1_struct_0 @ X5) @ (u1_struct_0 @ X6))
% 2.52/2.70          | ~ (v1_funct_1 @ X4)
% 2.52/2.70          | ~ (m1_pre_topc @ X7 @ X8)
% 2.52/2.70          | (v2_struct_0 @ X7)
% 2.52/2.70          | ~ (m1_pre_topc @ X5 @ X8)
% 2.52/2.70          | (v2_struct_0 @ X5)
% 2.52/2.70          | ~ (l1_pre_topc @ X6)
% 2.52/2.70          | ~ (v2_pre_topc @ X6)
% 2.52/2.70          | (v2_struct_0 @ X6)
% 2.52/2.70          | ~ (l1_pre_topc @ X8)
% 2.52/2.70          | ~ (v2_pre_topc @ X8)
% 2.52/2.70          | (v2_struct_0 @ X8)
% 2.52/2.70          | ~ (v1_funct_1 @ X9)
% 2.52/2.70          | ~ (v1_funct_2 @ X9 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X6))
% 2.52/2.70          | ~ (m1_subset_1 @ X9 @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X6))))
% 2.52/2.70          | (v1_funct_1 @ (k10_tmap_1 @ X8 @ X6 @ X5 @ X7 @ X4 @ X9)))),
% 2.52/2.70      inference('cnf', [status(esa)], [dt_k10_tmap_1])).
% 2.52/2.70  thf('247', plain,
% 2.52/2.70      ((![X0 : $i, X1 : $i, X2 : $i]:
% 2.52/2.70          ((v2_struct_0 @ sk_B)
% 2.52/2.70           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_A)
% 2.52/2.70           | (v1_funct_1 @ 
% 2.52/2.70              (k10_tmap_1 @ X2 @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ X1 @ 
% 2.52/2.70               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70                (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70               X0))
% 2.52/2.70           | ~ (m1_subset_1 @ X0 @ 
% 2.52/2.70                (k1_zfmisc_1 @ 
% 2.52/2.70                 (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ 
% 2.52/2.70                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.52/2.70           | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ X1) @ 
% 2.52/2.70                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70           | ~ (v1_funct_1 @ X0)
% 2.52/2.70           | (v2_struct_0 @ X2)
% 2.52/2.70           | ~ (v2_pre_topc @ X2)
% 2.52/2.70           | ~ (l1_pre_topc @ X2)
% 2.52/2.70           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70           | ~ (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70           | ~ (l1_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70           | (v2_struct_0 @ sk_B)
% 2.52/2.70           | ~ (m1_pre_topc @ sk_B @ X2)
% 2.52/2.70           | (v2_struct_0 @ X1)
% 2.52/2.70           | ~ (m1_pre_topc @ X1 @ X2)
% 2.52/2.70           | ~ (v1_funct_1 @ 
% 2.52/2.70                (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                 (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70                 (sk_E @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70           | ~ (v1_funct_2 @ 
% 2.52/2.70                (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                 (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70                 (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70                (u1_struct_0 @ sk_B) @ 
% 2.52/2.70                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.52/2.70         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['245', '246'])).
% 2.52/2.70  thf('248', plain,
% 2.52/2.70      ((![X0 : $i, X1 : $i, X2 : $i]:
% 2.52/2.70          (~ (v1_funct_2 @ 
% 2.52/2.70              (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70               (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70               (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70              (u1_struct_0 @ sk_B) @ 
% 2.52/2.70              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70           | ~ (v1_funct_1 @ 
% 2.52/2.70                (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                 (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70                 (sk_E @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70           | ~ (m1_pre_topc @ X1 @ X2)
% 2.52/2.70           | (v2_struct_0 @ X1)
% 2.52/2.70           | ~ (m1_pre_topc @ sk_B @ X2)
% 2.52/2.70           | ~ (l1_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70           | ~ (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70           | ~ (l1_pre_topc @ X2)
% 2.52/2.70           | ~ (v2_pre_topc @ X2)
% 2.52/2.70           | (v2_struct_0 @ X2)
% 2.52/2.70           | ~ (v1_funct_1 @ X0)
% 2.52/2.70           | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ X1) @ 
% 2.52/2.70                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70           | ~ (m1_subset_1 @ X0 @ 
% 2.52/2.70                (k1_zfmisc_1 @ 
% 2.52/2.70                 (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ 
% 2.52/2.70                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.52/2.70           | (v1_funct_1 @ 
% 2.52/2.70              (k10_tmap_1 @ X2 @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ X1 @ 
% 2.52/2.70               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70                (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70               X0))
% 2.52/2.70           | (v2_struct_0 @ sk_A)
% 2.52/2.70           | (v2_struct_0 @ sk_C)
% 2.52/2.70           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_B)))
% 2.52/2.70         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('simplify', [status(thm)], ['247'])).
% 2.52/2.70  thf('249', plain,
% 2.52/2.70      ((![X0 : $i, X1 : $i, X2 : $i]:
% 2.52/2.70          ((v2_struct_0 @ sk_B)
% 2.52/2.70           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_A)
% 2.52/2.70           | (v2_struct_0 @ sk_B)
% 2.52/2.70           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_A)
% 2.52/2.70           | (v1_funct_1 @ 
% 2.52/2.70              (k10_tmap_1 @ X2 @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ X1 @ 
% 2.52/2.70               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70                (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70               X0))
% 2.52/2.70           | ~ (m1_subset_1 @ X0 @ 
% 2.52/2.70                (k1_zfmisc_1 @ 
% 2.52/2.70                 (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ 
% 2.52/2.70                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.52/2.70           | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ X1) @ 
% 2.52/2.70                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70           | ~ (v1_funct_1 @ X0)
% 2.52/2.70           | (v2_struct_0 @ X2)
% 2.52/2.70           | ~ (v2_pre_topc @ X2)
% 2.52/2.70           | ~ (l1_pre_topc @ X2)
% 2.52/2.70           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70           | ~ (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70           | ~ (l1_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70           | ~ (m1_pre_topc @ sk_B @ X2)
% 2.52/2.70           | (v2_struct_0 @ X1)
% 2.52/2.70           | ~ (m1_pre_topc @ X1 @ X2)
% 2.52/2.70           | ~ (v1_funct_1 @ 
% 2.52/2.70                (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                 (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70                 (sk_E @ sk_C @ sk_B @ sk_A)))))
% 2.52/2.70         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['235', '248'])).
% 2.52/2.70  thf('250', plain,
% 2.52/2.70      ((![X0 : $i, X1 : $i, X2 : $i]:
% 2.52/2.70          (~ (v1_funct_1 @ 
% 2.52/2.70              (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70               (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70               (sk_E @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70           | ~ (m1_pre_topc @ X1 @ X2)
% 2.52/2.70           | (v2_struct_0 @ X1)
% 2.52/2.70           | ~ (m1_pre_topc @ sk_B @ X2)
% 2.52/2.70           | ~ (l1_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70           | ~ (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70           | ~ (l1_pre_topc @ X2)
% 2.52/2.70           | ~ (v2_pre_topc @ X2)
% 2.52/2.70           | (v2_struct_0 @ X2)
% 2.52/2.70           | ~ (v1_funct_1 @ X0)
% 2.52/2.70           | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ X1) @ 
% 2.52/2.70                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70           | ~ (m1_subset_1 @ X0 @ 
% 2.52/2.70                (k1_zfmisc_1 @ 
% 2.52/2.70                 (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ 
% 2.52/2.70                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.52/2.70           | (v1_funct_1 @ 
% 2.52/2.70              (k10_tmap_1 @ X2 @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ X1 @ 
% 2.52/2.70               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70                (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70               X0))
% 2.52/2.70           | (v2_struct_0 @ sk_A)
% 2.52/2.70           | (v2_struct_0 @ sk_C)
% 2.52/2.70           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_B)))
% 2.52/2.70         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('simplify', [status(thm)], ['249'])).
% 2.52/2.70  thf('251', plain,
% 2.52/2.70      ((![X0 : $i, X1 : $i, X2 : $i]:
% 2.52/2.70          ((v2_struct_0 @ sk_B)
% 2.52/2.70           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_A)
% 2.52/2.70           | (v2_struct_0 @ sk_B)
% 2.52/2.70           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_A)
% 2.52/2.70           | (v1_funct_1 @ 
% 2.52/2.70              (k10_tmap_1 @ X2 @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ X1 @ 
% 2.52/2.70               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70                (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70               X0))
% 2.52/2.70           | ~ (m1_subset_1 @ X0 @ 
% 2.52/2.70                (k1_zfmisc_1 @ 
% 2.52/2.70                 (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ 
% 2.52/2.70                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.52/2.70           | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ X1) @ 
% 2.52/2.70                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70           | ~ (v1_funct_1 @ X0)
% 2.52/2.70           | (v2_struct_0 @ X2)
% 2.52/2.70           | ~ (v2_pre_topc @ X2)
% 2.52/2.70           | ~ (l1_pre_topc @ X2)
% 2.52/2.70           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70           | ~ (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70           | ~ (l1_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70           | ~ (m1_pre_topc @ sk_B @ X2)
% 2.52/2.70           | (v2_struct_0 @ X1)
% 2.52/2.70           | ~ (m1_pre_topc @ X1 @ X2)))
% 2.52/2.70         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['225', '250'])).
% 2.52/2.70  thf('252', plain,
% 2.52/2.70      ((![X0 : $i, X1 : $i, X2 : $i]:
% 2.52/2.70          (~ (m1_pre_topc @ X1 @ X2)
% 2.52/2.70           | (v2_struct_0 @ X1)
% 2.52/2.70           | ~ (m1_pre_topc @ sk_B @ X2)
% 2.52/2.70           | ~ (l1_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70           | ~ (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70           | ~ (l1_pre_topc @ X2)
% 2.52/2.70           | ~ (v2_pre_topc @ X2)
% 2.52/2.70           | (v2_struct_0 @ X2)
% 2.52/2.70           | ~ (v1_funct_1 @ X0)
% 2.52/2.70           | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ X1) @ 
% 2.52/2.70                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70           | ~ (m1_subset_1 @ X0 @ 
% 2.52/2.70                (k1_zfmisc_1 @ 
% 2.52/2.70                 (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ 
% 2.52/2.70                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.52/2.70           | (v1_funct_1 @ 
% 2.52/2.70              (k10_tmap_1 @ X2 @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ X1 @ 
% 2.52/2.70               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70                (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70               X0))
% 2.52/2.70           | (v2_struct_0 @ sk_A)
% 2.52/2.70           | (v2_struct_0 @ sk_C)
% 2.52/2.70           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_B)))
% 2.52/2.70         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('simplify', [status(thm)], ['251'])).
% 2.52/2.70  thf('253', plain,
% 2.52/2.70      ((![X0 : $i, X1 : $i, X2 : $i]:
% 2.52/2.70          ((v2_struct_0 @ sk_B)
% 2.52/2.70           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_A)
% 2.52/2.70           | (v2_struct_0 @ sk_B)
% 2.52/2.70           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_A)
% 2.52/2.70           | (v1_funct_1 @ 
% 2.52/2.70              (k10_tmap_1 @ X2 @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ X1 @ 
% 2.52/2.70               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70                (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70               X0))
% 2.52/2.70           | ~ (m1_subset_1 @ X0 @ 
% 2.52/2.70                (k1_zfmisc_1 @ 
% 2.52/2.70                 (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ 
% 2.52/2.70                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.52/2.70           | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ X1) @ 
% 2.52/2.70                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70           | ~ (v1_funct_1 @ X0)
% 2.52/2.70           | (v2_struct_0 @ X2)
% 2.52/2.70           | ~ (v2_pre_topc @ X2)
% 2.52/2.70           | ~ (l1_pre_topc @ X2)
% 2.52/2.70           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70           | ~ (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70           | ~ (m1_pre_topc @ sk_B @ X2)
% 2.52/2.70           | (v2_struct_0 @ X1)
% 2.52/2.70           | ~ (m1_pre_topc @ X1 @ X2)))
% 2.52/2.70         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['215', '252'])).
% 2.52/2.70  thf('254', plain,
% 2.52/2.70      ((![X0 : $i, X1 : $i, X2 : $i]:
% 2.52/2.70          (~ (m1_pre_topc @ X1 @ X2)
% 2.52/2.70           | (v2_struct_0 @ X1)
% 2.52/2.70           | ~ (m1_pre_topc @ sk_B @ X2)
% 2.52/2.70           | ~ (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70           | ~ (l1_pre_topc @ X2)
% 2.52/2.70           | ~ (v2_pre_topc @ X2)
% 2.52/2.70           | (v2_struct_0 @ X2)
% 2.52/2.70           | ~ (v1_funct_1 @ X0)
% 2.52/2.70           | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ X1) @ 
% 2.52/2.70                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70           | ~ (m1_subset_1 @ X0 @ 
% 2.52/2.70                (k1_zfmisc_1 @ 
% 2.52/2.70                 (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ 
% 2.52/2.70                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.52/2.70           | (v1_funct_1 @ 
% 2.52/2.70              (k10_tmap_1 @ X2 @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ X1 @ 
% 2.52/2.70               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70                (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70               X0))
% 2.52/2.70           | (v2_struct_0 @ sk_A)
% 2.52/2.70           | (v2_struct_0 @ sk_C)
% 2.52/2.70           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_B)))
% 2.52/2.70         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('simplify', [status(thm)], ['253'])).
% 2.52/2.70  thf('255', plain,
% 2.52/2.70      ((![X0 : $i, X1 : $i, X2 : $i]:
% 2.52/2.70          ((v2_struct_0 @ sk_B)
% 2.52/2.70           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_A)
% 2.52/2.70           | (v2_struct_0 @ sk_B)
% 2.52/2.70           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_A)
% 2.52/2.70           | (v1_funct_1 @ 
% 2.52/2.70              (k10_tmap_1 @ X2 @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ X1 @ 
% 2.52/2.70               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70                (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70               X0))
% 2.52/2.70           | ~ (m1_subset_1 @ X0 @ 
% 2.52/2.70                (k1_zfmisc_1 @ 
% 2.52/2.70                 (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ 
% 2.52/2.70                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.52/2.70           | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ X1) @ 
% 2.52/2.70                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70           | ~ (v1_funct_1 @ X0)
% 2.52/2.70           | (v2_struct_0 @ X2)
% 2.52/2.70           | ~ (v2_pre_topc @ X2)
% 2.52/2.70           | ~ (l1_pre_topc @ X2)
% 2.52/2.70           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70           | ~ (m1_pre_topc @ sk_B @ X2)
% 2.52/2.70           | (v2_struct_0 @ X1)
% 2.52/2.70           | ~ (m1_pre_topc @ X1 @ X2)))
% 2.52/2.70         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['205', '254'])).
% 2.52/2.70  thf('256', plain,
% 2.52/2.70      ((![X0 : $i, X1 : $i, X2 : $i]:
% 2.52/2.70          (~ (m1_pre_topc @ X1 @ X2)
% 2.52/2.70           | (v2_struct_0 @ X1)
% 2.52/2.70           | ~ (m1_pre_topc @ sk_B @ X2)
% 2.52/2.70           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70           | ~ (l1_pre_topc @ X2)
% 2.52/2.70           | ~ (v2_pre_topc @ X2)
% 2.52/2.70           | (v2_struct_0 @ X2)
% 2.52/2.70           | ~ (v1_funct_1 @ X0)
% 2.52/2.70           | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ X1) @ 
% 2.52/2.70                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70           | ~ (m1_subset_1 @ X0 @ 
% 2.52/2.70                (k1_zfmisc_1 @ 
% 2.52/2.70                 (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ 
% 2.52/2.70                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.52/2.70           | (v1_funct_1 @ 
% 2.52/2.70              (k10_tmap_1 @ X2 @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ X1 @ 
% 2.52/2.70               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70                (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70               X0))
% 2.52/2.70           | (v2_struct_0 @ sk_A)
% 2.52/2.70           | (v2_struct_0 @ sk_C)
% 2.52/2.70           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_B)))
% 2.52/2.70         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('simplify', [status(thm)], ['255'])).
% 2.52/2.70  thf('257', plain,
% 2.52/2.70      ((![X0 : $i]:
% 2.52/2.70          ((v2_struct_0 @ sk_B)
% 2.52/2.70           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_A)
% 2.52/2.70           | (v2_struct_0 @ sk_B)
% 2.52/2.70           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_A)
% 2.52/2.70           | (v1_funct_1 @ 
% 2.52/2.70              (k10_tmap_1 @ X0 @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ sk_C @ 
% 2.52/2.70               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70                (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.70                (sk_E @ sk_C @ sk_B @ sk_A))))
% 2.52/2.70           | ~ (v1_funct_2 @ 
% 2.52/2.70                (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                 (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.70                 (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70                (u1_struct_0 @ sk_C) @ 
% 2.52/2.70                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70           | ~ (v1_funct_1 @ 
% 2.52/2.70                (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                 (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.70                 (sk_E @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70           | (v2_struct_0 @ X0)
% 2.52/2.70           | ~ (v2_pre_topc @ X0)
% 2.52/2.70           | ~ (l1_pre_topc @ X0)
% 2.52/2.70           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70           | ~ (m1_pre_topc @ sk_B @ X0)
% 2.52/2.70           | (v2_struct_0 @ sk_C)
% 2.52/2.70           | ~ (m1_pre_topc @ sk_C @ X0)))
% 2.52/2.70         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['195', '256'])).
% 2.52/2.70  thf('258', plain,
% 2.52/2.70      ((![X0 : $i]:
% 2.52/2.70          (~ (m1_pre_topc @ sk_C @ X0)
% 2.52/2.70           | ~ (m1_pre_topc @ sk_B @ X0)
% 2.52/2.70           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70           | ~ (l1_pre_topc @ X0)
% 2.52/2.70           | ~ (v2_pre_topc @ X0)
% 2.52/2.70           | (v2_struct_0 @ X0)
% 2.52/2.70           | ~ (v1_funct_1 @ 
% 2.52/2.70                (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                 (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.70                 (sk_E @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70           | ~ (v1_funct_2 @ 
% 2.52/2.70                (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                 (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.70                 (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70                (u1_struct_0 @ sk_C) @ 
% 2.52/2.70                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70           | (v1_funct_1 @ 
% 2.52/2.70              (k10_tmap_1 @ X0 @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ sk_C @ 
% 2.52/2.70               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70                (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.70                (sk_E @ sk_C @ sk_B @ sk_A))))
% 2.52/2.70           | (v2_struct_0 @ sk_A)
% 2.52/2.70           | (v2_struct_0 @ sk_C)
% 2.52/2.70           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_B)))
% 2.52/2.70         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('simplify', [status(thm)], ['257'])).
% 2.52/2.70  thf('259', plain,
% 2.52/2.70      ((![X0 : $i]:
% 2.52/2.70          ((v2_struct_0 @ sk_B)
% 2.52/2.70           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_A)
% 2.52/2.70           | (v2_struct_0 @ sk_B)
% 2.52/2.70           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_A)
% 2.52/2.70           | (v1_funct_1 @ 
% 2.52/2.70              (k10_tmap_1 @ X0 @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ sk_C @ 
% 2.52/2.70               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70                (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.70                (sk_E @ sk_C @ sk_B @ sk_A))))
% 2.52/2.70           | ~ (v1_funct_1 @ 
% 2.52/2.70                (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                 (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.70                 (sk_E @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70           | (v2_struct_0 @ X0)
% 2.52/2.70           | ~ (v2_pre_topc @ X0)
% 2.52/2.70           | ~ (l1_pre_topc @ X0)
% 2.52/2.70           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70           | ~ (m1_pre_topc @ sk_B @ X0)
% 2.52/2.70           | ~ (m1_pre_topc @ sk_C @ X0)))
% 2.52/2.70         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['185', '258'])).
% 2.52/2.70  thf('260', plain,
% 2.52/2.70      ((![X0 : $i]:
% 2.52/2.70          (~ (m1_pre_topc @ sk_C @ X0)
% 2.52/2.70           | ~ (m1_pre_topc @ sk_B @ X0)
% 2.52/2.70           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70           | ~ (l1_pre_topc @ X0)
% 2.52/2.70           | ~ (v2_pre_topc @ X0)
% 2.52/2.70           | (v2_struct_0 @ X0)
% 2.52/2.70           | ~ (v1_funct_1 @ 
% 2.52/2.70                (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                 (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.70                 (sk_E @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70           | (v1_funct_1 @ 
% 2.52/2.70              (k10_tmap_1 @ X0 @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ sk_C @ 
% 2.52/2.70               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70                (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.70                (sk_E @ sk_C @ sk_B @ sk_A))))
% 2.52/2.70           | (v2_struct_0 @ sk_A)
% 2.52/2.70           | (v2_struct_0 @ sk_C)
% 2.52/2.70           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_B)))
% 2.52/2.70         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('simplify', [status(thm)], ['259'])).
% 2.52/2.70  thf('261', plain,
% 2.52/2.70      ((![X0 : $i]:
% 2.52/2.70          ((v2_struct_0 @ sk_B)
% 2.52/2.70           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_A)
% 2.52/2.70           | (v2_struct_0 @ sk_B)
% 2.52/2.70           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_A)
% 2.52/2.70           | (v1_funct_1 @ 
% 2.52/2.70              (k10_tmap_1 @ X0 @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ sk_C @ 
% 2.52/2.70               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70                (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.70                (sk_E @ sk_C @ sk_B @ sk_A))))
% 2.52/2.70           | (v2_struct_0 @ X0)
% 2.52/2.70           | ~ (v2_pre_topc @ X0)
% 2.52/2.70           | ~ (l1_pre_topc @ X0)
% 2.52/2.70           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70           | ~ (m1_pre_topc @ sk_B @ X0)
% 2.52/2.70           | ~ (m1_pre_topc @ sk_C @ X0)))
% 2.52/2.70         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['175', '260'])).
% 2.52/2.70  thf('262', plain,
% 2.52/2.70      ((![X0 : $i]:
% 2.52/2.70          (~ (m1_pre_topc @ sk_C @ X0)
% 2.52/2.70           | ~ (m1_pre_topc @ sk_B @ X0)
% 2.52/2.70           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70           | ~ (l1_pre_topc @ X0)
% 2.52/2.70           | ~ (v2_pre_topc @ X0)
% 2.52/2.70           | (v2_struct_0 @ X0)
% 2.52/2.70           | (v1_funct_1 @ 
% 2.52/2.70              (k10_tmap_1 @ X0 @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ sk_C @ 
% 2.52/2.70               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70                (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.70                (sk_E @ sk_C @ sk_B @ sk_A))))
% 2.52/2.70           | (v2_struct_0 @ sk_A)
% 2.52/2.70           | (v2_struct_0 @ sk_C)
% 2.52/2.70           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_B)))
% 2.52/2.70         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('simplify', [status(thm)], ['261'])).
% 2.52/2.70  thf('263', plain,
% 2.52/2.70      ((((v2_struct_0 @ sk_B)
% 2.52/2.70         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70         | (v2_struct_0 @ sk_C)
% 2.52/2.70         | (v2_struct_0 @ sk_A)
% 2.52/2.70         | (v1_funct_1 @ 
% 2.52/2.70            (k10_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ sk_C @ 
% 2.52/2.70             (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70              (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70              (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70             (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70              (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.70              (sk_E @ sk_C @ sk_B @ sk_A))))
% 2.52/2.70         | (v2_struct_0 @ sk_A)
% 2.52/2.70         | ~ (v2_pre_topc @ sk_A)
% 2.52/2.70         | ~ (l1_pre_topc @ sk_A)
% 2.52/2.70         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70         | ~ (m1_pre_topc @ sk_B @ sk_A))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['165', '262'])).
% 2.52/2.70  thf('264', plain, ((v2_pre_topc @ sk_A)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('265', plain, ((l1_pre_topc @ sk_A)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('266', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('267', plain,
% 2.52/2.70      ((((v2_struct_0 @ sk_B)
% 2.52/2.70         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70         | (v2_struct_0 @ sk_C)
% 2.52/2.70         | (v2_struct_0 @ sk_A)
% 2.52/2.70         | (v1_funct_1 @ 
% 2.52/2.70            (k10_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ sk_C @ 
% 2.52/2.70             (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70              (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70              (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70             (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70              (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.70              (sk_E @ sk_C @ sk_B @ sk_A))))
% 2.52/2.70         | (v2_struct_0 @ sk_A)
% 2.52/2.70         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))))
% 2.52/2.70         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('demod', [status(thm)], ['263', '264', '265', '266'])).
% 2.52/2.70  thf('268', plain,
% 2.52/2.70      ((((v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70         | (v1_funct_1 @ 
% 2.52/2.70            (k10_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ sk_C @ 
% 2.52/2.70             (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70              (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70              (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70             (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70              (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.70              (sk_E @ sk_C @ sk_B @ sk_A))))
% 2.52/2.70         | (v2_struct_0 @ sk_A)
% 2.52/2.70         | (v2_struct_0 @ sk_C)
% 2.52/2.70         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('simplify', [status(thm)], ['267'])).
% 2.52/2.70  thf('269', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('270', plain,
% 2.52/2.70      ((((v2_struct_0 @ sk_A)
% 2.52/2.70         | (v2_struct_0 @ sk_C)
% 2.52/2.70         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70         | (v1_funct_1 @ 
% 2.52/2.70            (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70             (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.70             (sk_E @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['166', '174'])).
% 2.52/2.70  thf('271', plain,
% 2.52/2.70      ((((v2_struct_0 @ sk_A)
% 2.52/2.70         | (v2_struct_0 @ sk_C)
% 2.52/2.70         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70         | (v1_funct_2 @ 
% 2.52/2.70            (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70             (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.70             (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70            (u1_struct_0 @ sk_C) @ (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['176', '184'])).
% 2.52/2.70  thf('272', plain,
% 2.52/2.70      ((((v2_struct_0 @ sk_A)
% 2.52/2.70         | (v2_struct_0 @ sk_C)
% 2.52/2.70         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70         | (m1_subset_1 @ 
% 2.52/2.70            (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70             (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.70             (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70            (k1_zfmisc_1 @ 
% 2.52/2.70             (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.70              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.52/2.70         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['186', '194'])).
% 2.52/2.70  thf('273', plain,
% 2.52/2.70      ((((v2_struct_0 @ sk_A)
% 2.52/2.70         | (v2_struct_0 @ sk_C)
% 2.52/2.70         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70         | (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['196', '204'])).
% 2.52/2.70  thf('274', plain,
% 2.52/2.70      ((((v2_struct_0 @ sk_A)
% 2.52/2.70         | (v2_struct_0 @ sk_C)
% 2.52/2.70         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70         | (l1_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['206', '214'])).
% 2.52/2.70  thf('275', plain,
% 2.52/2.70      ((((v2_struct_0 @ sk_A)
% 2.52/2.70         | (v2_struct_0 @ sk_C)
% 2.52/2.70         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70         | (v1_funct_1 @ 
% 2.52/2.70            (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70             (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70             (sk_E @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['216', '224'])).
% 2.52/2.70  thf('276', plain,
% 2.52/2.70      ((((v2_struct_0 @ sk_A)
% 2.52/2.70         | (v2_struct_0 @ sk_C)
% 2.52/2.70         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70         | (v1_funct_2 @ 
% 2.52/2.70            (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70             (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70             (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70            (u1_struct_0 @ sk_B) @ (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['226', '234'])).
% 2.52/2.70  thf('277', plain,
% 2.52/2.70      ((((v2_struct_0 @ sk_A)
% 2.52/2.70         | (v2_struct_0 @ sk_C)
% 2.52/2.70         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70         | (m1_subset_1 @ 
% 2.52/2.70            (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70             (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70             (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70            (k1_zfmisc_1 @ 
% 2.52/2.70             (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.70              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.52/2.70         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['236', '244'])).
% 2.52/2.70  thf('278', plain,
% 2.52/2.70      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 2.52/2.70         (~ (m1_subset_1 @ X4 @ 
% 2.52/2.70             (k1_zfmisc_1 @ 
% 2.52/2.70              (k2_zfmisc_1 @ (u1_struct_0 @ X5) @ (u1_struct_0 @ X6))))
% 2.52/2.70          | ~ (v1_funct_2 @ X4 @ (u1_struct_0 @ X5) @ (u1_struct_0 @ X6))
% 2.52/2.70          | ~ (v1_funct_1 @ X4)
% 2.52/2.70          | ~ (m1_pre_topc @ X7 @ X8)
% 2.52/2.70          | (v2_struct_0 @ X7)
% 2.52/2.70          | ~ (m1_pre_topc @ X5 @ X8)
% 2.52/2.70          | (v2_struct_0 @ X5)
% 2.52/2.70          | ~ (l1_pre_topc @ X6)
% 2.52/2.70          | ~ (v2_pre_topc @ X6)
% 2.52/2.70          | (v2_struct_0 @ X6)
% 2.52/2.70          | ~ (l1_pre_topc @ X8)
% 2.52/2.70          | ~ (v2_pre_topc @ X8)
% 2.52/2.70          | (v2_struct_0 @ X8)
% 2.52/2.70          | ~ (v1_funct_1 @ X9)
% 2.52/2.70          | ~ (v1_funct_2 @ X9 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X6))
% 2.52/2.70          | ~ (m1_subset_1 @ X9 @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X6))))
% 2.52/2.70          | (v1_funct_2 @ (k10_tmap_1 @ X8 @ X6 @ X5 @ X7 @ X4 @ X9) @ 
% 2.52/2.70             (u1_struct_0 @ (k1_tsep_1 @ X8 @ X5 @ X7)) @ (u1_struct_0 @ X6)))),
% 2.52/2.70      inference('cnf', [status(esa)], [dt_k10_tmap_1])).
% 2.52/2.70  thf('279', plain,
% 2.52/2.70      ((![X0 : $i, X1 : $i, X2 : $i]:
% 2.52/2.70          ((v2_struct_0 @ sk_B)
% 2.52/2.70           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_A)
% 2.52/2.70           | (v1_funct_2 @ 
% 2.52/2.70              (k10_tmap_1 @ X1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ X0 @ 
% 2.52/2.70               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70                (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70               X2) @ 
% 2.52/2.70              (u1_struct_0 @ (k1_tsep_1 @ X1 @ sk_B @ X0)) @ 
% 2.52/2.70              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70           | ~ (m1_subset_1 @ X2 @ 
% 2.52/2.70                (k1_zfmisc_1 @ 
% 2.52/2.70                 (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ 
% 2.52/2.70                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.52/2.70           | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X0) @ 
% 2.52/2.70                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70           | ~ (v1_funct_1 @ X2)
% 2.52/2.70           | (v2_struct_0 @ X1)
% 2.52/2.70           | ~ (v2_pre_topc @ X1)
% 2.52/2.70           | ~ (l1_pre_topc @ X1)
% 2.52/2.70           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70           | ~ (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70           | ~ (l1_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70           | (v2_struct_0 @ sk_B)
% 2.52/2.70           | ~ (m1_pre_topc @ sk_B @ X1)
% 2.52/2.70           | (v2_struct_0 @ X0)
% 2.52/2.70           | ~ (m1_pre_topc @ X0 @ X1)
% 2.52/2.70           | ~ (v1_funct_1 @ 
% 2.52/2.70                (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                 (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70                 (sk_E @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70           | ~ (v1_funct_2 @ 
% 2.52/2.70                (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                 (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70                 (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70                (u1_struct_0 @ sk_B) @ 
% 2.52/2.70                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.52/2.70         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['277', '278'])).
% 2.52/2.70  thf('280', plain,
% 2.52/2.70      ((![X0 : $i, X1 : $i, X2 : $i]:
% 2.52/2.70          (~ (v1_funct_2 @ 
% 2.52/2.70              (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70               (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70               (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70              (u1_struct_0 @ sk_B) @ 
% 2.52/2.70              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70           | ~ (v1_funct_1 @ 
% 2.52/2.70                (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                 (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70                 (sk_E @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70           | ~ (m1_pre_topc @ X0 @ X1)
% 2.52/2.70           | (v2_struct_0 @ X0)
% 2.52/2.70           | ~ (m1_pre_topc @ sk_B @ X1)
% 2.52/2.70           | ~ (l1_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70           | ~ (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70           | ~ (l1_pre_topc @ X1)
% 2.52/2.70           | ~ (v2_pre_topc @ X1)
% 2.52/2.70           | (v2_struct_0 @ X1)
% 2.52/2.70           | ~ (v1_funct_1 @ X2)
% 2.52/2.70           | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X0) @ 
% 2.52/2.70                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70           | ~ (m1_subset_1 @ X2 @ 
% 2.52/2.70                (k1_zfmisc_1 @ 
% 2.52/2.70                 (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ 
% 2.52/2.70                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.52/2.70           | (v1_funct_2 @ 
% 2.52/2.70              (k10_tmap_1 @ X1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ X0 @ 
% 2.52/2.70               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70                (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70               X2) @ 
% 2.52/2.70              (u1_struct_0 @ (k1_tsep_1 @ X1 @ sk_B @ X0)) @ 
% 2.52/2.70              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70           | (v2_struct_0 @ sk_A)
% 2.52/2.70           | (v2_struct_0 @ sk_C)
% 2.52/2.70           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_B)))
% 2.52/2.70         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('simplify', [status(thm)], ['279'])).
% 2.52/2.70  thf('281', plain,
% 2.52/2.70      ((![X0 : $i, X1 : $i, X2 : $i]:
% 2.52/2.70          ((v2_struct_0 @ sk_B)
% 2.52/2.70           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_A)
% 2.52/2.70           | (v2_struct_0 @ sk_B)
% 2.52/2.70           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_A)
% 2.52/2.70           | (v1_funct_2 @ 
% 2.52/2.70              (k10_tmap_1 @ X1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ X0 @ 
% 2.52/2.70               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70                (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70               X2) @ 
% 2.52/2.70              (u1_struct_0 @ (k1_tsep_1 @ X1 @ sk_B @ X0)) @ 
% 2.52/2.70              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70           | ~ (m1_subset_1 @ X2 @ 
% 2.52/2.70                (k1_zfmisc_1 @ 
% 2.52/2.70                 (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ 
% 2.52/2.70                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.52/2.70           | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X0) @ 
% 2.52/2.70                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70           | ~ (v1_funct_1 @ X2)
% 2.52/2.70           | (v2_struct_0 @ X1)
% 2.52/2.70           | ~ (v2_pre_topc @ X1)
% 2.52/2.70           | ~ (l1_pre_topc @ X1)
% 2.52/2.70           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70           | ~ (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70           | ~ (l1_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70           | ~ (m1_pre_topc @ sk_B @ X1)
% 2.52/2.70           | (v2_struct_0 @ X0)
% 2.52/2.70           | ~ (m1_pre_topc @ X0 @ X1)
% 2.52/2.70           | ~ (v1_funct_1 @ 
% 2.52/2.70                (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                 (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70                 (sk_E @ sk_C @ sk_B @ sk_A)))))
% 2.52/2.70         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['276', '280'])).
% 2.52/2.70  thf('282', plain,
% 2.52/2.70      ((![X0 : $i, X1 : $i, X2 : $i]:
% 2.52/2.70          (~ (v1_funct_1 @ 
% 2.52/2.70              (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70               (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70               (sk_E @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70           | ~ (m1_pre_topc @ X0 @ X1)
% 2.52/2.70           | (v2_struct_0 @ X0)
% 2.52/2.70           | ~ (m1_pre_topc @ sk_B @ X1)
% 2.52/2.70           | ~ (l1_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70           | ~ (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70           | ~ (l1_pre_topc @ X1)
% 2.52/2.70           | ~ (v2_pre_topc @ X1)
% 2.52/2.70           | (v2_struct_0 @ X1)
% 2.52/2.70           | ~ (v1_funct_1 @ X2)
% 2.52/2.70           | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X0) @ 
% 2.52/2.70                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70           | ~ (m1_subset_1 @ X2 @ 
% 2.52/2.70                (k1_zfmisc_1 @ 
% 2.52/2.70                 (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ 
% 2.52/2.70                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.52/2.70           | (v1_funct_2 @ 
% 2.52/2.70              (k10_tmap_1 @ X1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ X0 @ 
% 2.52/2.70               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70                (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70               X2) @ 
% 2.52/2.70              (u1_struct_0 @ (k1_tsep_1 @ X1 @ sk_B @ X0)) @ 
% 2.52/2.70              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70           | (v2_struct_0 @ sk_A)
% 2.52/2.70           | (v2_struct_0 @ sk_C)
% 2.52/2.70           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_B)))
% 2.52/2.70         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('simplify', [status(thm)], ['281'])).
% 2.52/2.70  thf('283', plain,
% 2.52/2.70      ((![X0 : $i, X1 : $i, X2 : $i]:
% 2.52/2.70          ((v2_struct_0 @ sk_B)
% 2.52/2.70           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_A)
% 2.52/2.70           | (v2_struct_0 @ sk_B)
% 2.52/2.70           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_A)
% 2.52/2.70           | (v1_funct_2 @ 
% 2.52/2.70              (k10_tmap_1 @ X1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ X0 @ 
% 2.52/2.70               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70                (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70               X2) @ 
% 2.52/2.70              (u1_struct_0 @ (k1_tsep_1 @ X1 @ sk_B @ X0)) @ 
% 2.52/2.70              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70           | ~ (m1_subset_1 @ X2 @ 
% 2.52/2.70                (k1_zfmisc_1 @ 
% 2.52/2.70                 (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ 
% 2.52/2.70                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.52/2.70           | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X0) @ 
% 2.52/2.70                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70           | ~ (v1_funct_1 @ X2)
% 2.52/2.70           | (v2_struct_0 @ X1)
% 2.52/2.70           | ~ (v2_pre_topc @ X1)
% 2.52/2.70           | ~ (l1_pre_topc @ X1)
% 2.52/2.70           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70           | ~ (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70           | ~ (l1_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70           | ~ (m1_pre_topc @ sk_B @ X1)
% 2.52/2.70           | (v2_struct_0 @ X0)
% 2.52/2.70           | ~ (m1_pre_topc @ X0 @ X1)))
% 2.52/2.70         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['275', '282'])).
% 2.52/2.70  thf('284', plain,
% 2.52/2.70      ((![X0 : $i, X1 : $i, X2 : $i]:
% 2.52/2.70          (~ (m1_pre_topc @ X0 @ X1)
% 2.52/2.70           | (v2_struct_0 @ X0)
% 2.52/2.70           | ~ (m1_pre_topc @ sk_B @ X1)
% 2.52/2.70           | ~ (l1_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70           | ~ (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70           | ~ (l1_pre_topc @ X1)
% 2.52/2.70           | ~ (v2_pre_topc @ X1)
% 2.52/2.70           | (v2_struct_0 @ X1)
% 2.52/2.70           | ~ (v1_funct_1 @ X2)
% 2.52/2.70           | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X0) @ 
% 2.52/2.70                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70           | ~ (m1_subset_1 @ X2 @ 
% 2.52/2.70                (k1_zfmisc_1 @ 
% 2.52/2.70                 (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ 
% 2.52/2.70                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.52/2.70           | (v1_funct_2 @ 
% 2.52/2.70              (k10_tmap_1 @ X1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ X0 @ 
% 2.52/2.70               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70                (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70               X2) @ 
% 2.52/2.70              (u1_struct_0 @ (k1_tsep_1 @ X1 @ sk_B @ X0)) @ 
% 2.52/2.70              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70           | (v2_struct_0 @ sk_A)
% 2.52/2.70           | (v2_struct_0 @ sk_C)
% 2.52/2.70           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_B)))
% 2.52/2.70         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('simplify', [status(thm)], ['283'])).
% 2.52/2.70  thf('285', plain,
% 2.52/2.70      ((![X0 : $i, X1 : $i, X2 : $i]:
% 2.52/2.70          ((v2_struct_0 @ sk_B)
% 2.52/2.70           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_A)
% 2.52/2.70           | (v2_struct_0 @ sk_B)
% 2.52/2.70           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_A)
% 2.52/2.70           | (v1_funct_2 @ 
% 2.52/2.70              (k10_tmap_1 @ X1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ X0 @ 
% 2.52/2.70               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70                (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70               X2) @ 
% 2.52/2.70              (u1_struct_0 @ (k1_tsep_1 @ X1 @ sk_B @ X0)) @ 
% 2.52/2.70              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70           | ~ (m1_subset_1 @ X2 @ 
% 2.52/2.70                (k1_zfmisc_1 @ 
% 2.52/2.70                 (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ 
% 2.52/2.70                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.52/2.70           | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X0) @ 
% 2.52/2.70                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70           | ~ (v1_funct_1 @ X2)
% 2.52/2.70           | (v2_struct_0 @ X1)
% 2.52/2.70           | ~ (v2_pre_topc @ X1)
% 2.52/2.70           | ~ (l1_pre_topc @ X1)
% 2.52/2.70           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70           | ~ (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70           | ~ (m1_pre_topc @ sk_B @ X1)
% 2.52/2.70           | (v2_struct_0 @ X0)
% 2.52/2.70           | ~ (m1_pre_topc @ X0 @ X1)))
% 2.52/2.70         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['274', '284'])).
% 2.52/2.70  thf('286', plain,
% 2.52/2.70      ((![X0 : $i, X1 : $i, X2 : $i]:
% 2.52/2.70          (~ (m1_pre_topc @ X0 @ X1)
% 2.52/2.70           | (v2_struct_0 @ X0)
% 2.52/2.70           | ~ (m1_pre_topc @ sk_B @ X1)
% 2.52/2.70           | ~ (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70           | ~ (l1_pre_topc @ X1)
% 2.52/2.70           | ~ (v2_pre_topc @ X1)
% 2.52/2.70           | (v2_struct_0 @ X1)
% 2.52/2.70           | ~ (v1_funct_1 @ X2)
% 2.52/2.70           | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X0) @ 
% 2.52/2.70                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70           | ~ (m1_subset_1 @ X2 @ 
% 2.52/2.70                (k1_zfmisc_1 @ 
% 2.52/2.70                 (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ 
% 2.52/2.70                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.52/2.70           | (v1_funct_2 @ 
% 2.52/2.70              (k10_tmap_1 @ X1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ X0 @ 
% 2.52/2.70               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70                (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70               X2) @ 
% 2.52/2.70              (u1_struct_0 @ (k1_tsep_1 @ X1 @ sk_B @ X0)) @ 
% 2.52/2.70              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70           | (v2_struct_0 @ sk_A)
% 2.52/2.70           | (v2_struct_0 @ sk_C)
% 2.52/2.70           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_B)))
% 2.52/2.70         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('simplify', [status(thm)], ['285'])).
% 2.52/2.70  thf('287', plain,
% 2.52/2.70      ((![X0 : $i, X1 : $i, X2 : $i]:
% 2.52/2.70          ((v2_struct_0 @ sk_B)
% 2.52/2.70           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_A)
% 2.52/2.70           | (v2_struct_0 @ sk_B)
% 2.52/2.70           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_A)
% 2.52/2.70           | (v1_funct_2 @ 
% 2.52/2.70              (k10_tmap_1 @ X1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ X0 @ 
% 2.52/2.70               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70                (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70               X2) @ 
% 2.52/2.70              (u1_struct_0 @ (k1_tsep_1 @ X1 @ sk_B @ X0)) @ 
% 2.52/2.70              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70           | ~ (m1_subset_1 @ X2 @ 
% 2.52/2.70                (k1_zfmisc_1 @ 
% 2.52/2.70                 (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ 
% 2.52/2.70                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.52/2.70           | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X0) @ 
% 2.52/2.70                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70           | ~ (v1_funct_1 @ X2)
% 2.52/2.70           | (v2_struct_0 @ X1)
% 2.52/2.70           | ~ (v2_pre_topc @ X1)
% 2.52/2.70           | ~ (l1_pre_topc @ X1)
% 2.52/2.70           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70           | ~ (m1_pre_topc @ sk_B @ X1)
% 2.52/2.70           | (v2_struct_0 @ X0)
% 2.52/2.70           | ~ (m1_pre_topc @ X0 @ X1)))
% 2.52/2.70         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['273', '286'])).
% 2.52/2.70  thf('288', plain,
% 2.52/2.70      ((![X0 : $i, X1 : $i, X2 : $i]:
% 2.52/2.70          (~ (m1_pre_topc @ X0 @ X1)
% 2.52/2.70           | (v2_struct_0 @ X0)
% 2.52/2.70           | ~ (m1_pre_topc @ sk_B @ X1)
% 2.52/2.70           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70           | ~ (l1_pre_topc @ X1)
% 2.52/2.70           | ~ (v2_pre_topc @ X1)
% 2.52/2.70           | (v2_struct_0 @ X1)
% 2.52/2.70           | ~ (v1_funct_1 @ X2)
% 2.52/2.70           | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X0) @ 
% 2.52/2.70                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70           | ~ (m1_subset_1 @ X2 @ 
% 2.52/2.70                (k1_zfmisc_1 @ 
% 2.52/2.70                 (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ 
% 2.52/2.70                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.52/2.70           | (v1_funct_2 @ 
% 2.52/2.70              (k10_tmap_1 @ X1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ X0 @ 
% 2.52/2.70               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70                (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70               X2) @ 
% 2.52/2.70              (u1_struct_0 @ (k1_tsep_1 @ X1 @ sk_B @ X0)) @ 
% 2.52/2.70              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70           | (v2_struct_0 @ sk_A)
% 2.52/2.70           | (v2_struct_0 @ sk_C)
% 2.52/2.70           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_B)))
% 2.52/2.70         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('simplify', [status(thm)], ['287'])).
% 2.52/2.70  thf('289', plain,
% 2.52/2.70      ((![X0 : $i]:
% 2.52/2.70          ((v2_struct_0 @ sk_B)
% 2.52/2.70           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_A)
% 2.52/2.70           | (v2_struct_0 @ sk_B)
% 2.52/2.70           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_A)
% 2.52/2.70           | (v1_funct_2 @ 
% 2.52/2.70              (k10_tmap_1 @ X0 @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ sk_C @ 
% 2.52/2.70               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70                (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.70                (sk_E @ sk_C @ sk_B @ sk_A))) @ 
% 2.52/2.70              (u1_struct_0 @ (k1_tsep_1 @ X0 @ sk_B @ sk_C)) @ 
% 2.52/2.70              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70           | ~ (v1_funct_2 @ 
% 2.52/2.70                (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                 (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.70                 (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70                (u1_struct_0 @ sk_C) @ 
% 2.52/2.70                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70           | ~ (v1_funct_1 @ 
% 2.52/2.70                (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                 (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.70                 (sk_E @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70           | (v2_struct_0 @ X0)
% 2.52/2.70           | ~ (v2_pre_topc @ X0)
% 2.52/2.70           | ~ (l1_pre_topc @ X0)
% 2.52/2.70           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70           | ~ (m1_pre_topc @ sk_B @ X0)
% 2.52/2.70           | (v2_struct_0 @ sk_C)
% 2.52/2.70           | ~ (m1_pre_topc @ sk_C @ X0)))
% 2.52/2.70         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['272', '288'])).
% 2.52/2.70  thf('290', plain,
% 2.52/2.70      ((![X0 : $i]:
% 2.52/2.70          (~ (m1_pre_topc @ sk_C @ X0)
% 2.52/2.70           | ~ (m1_pre_topc @ sk_B @ X0)
% 2.52/2.70           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70           | ~ (l1_pre_topc @ X0)
% 2.52/2.70           | ~ (v2_pre_topc @ X0)
% 2.52/2.70           | (v2_struct_0 @ X0)
% 2.52/2.70           | ~ (v1_funct_1 @ 
% 2.52/2.70                (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                 (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.70                 (sk_E @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70           | ~ (v1_funct_2 @ 
% 2.52/2.70                (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                 (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.70                 (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70                (u1_struct_0 @ sk_C) @ 
% 2.52/2.70                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70           | (v1_funct_2 @ 
% 2.52/2.70              (k10_tmap_1 @ X0 @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ sk_C @ 
% 2.52/2.70               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70                (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.70                (sk_E @ sk_C @ sk_B @ sk_A))) @ 
% 2.52/2.70              (u1_struct_0 @ (k1_tsep_1 @ X0 @ sk_B @ sk_C)) @ 
% 2.52/2.70              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70           | (v2_struct_0 @ sk_A)
% 2.52/2.70           | (v2_struct_0 @ sk_C)
% 2.52/2.70           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_B)))
% 2.52/2.70         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('simplify', [status(thm)], ['289'])).
% 2.52/2.70  thf('291', plain,
% 2.52/2.70      ((![X0 : $i]:
% 2.52/2.70          ((v2_struct_0 @ sk_B)
% 2.52/2.70           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_A)
% 2.52/2.70           | (v2_struct_0 @ sk_B)
% 2.52/2.70           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_A)
% 2.52/2.70           | (v1_funct_2 @ 
% 2.52/2.70              (k10_tmap_1 @ X0 @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ sk_C @ 
% 2.52/2.70               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70                (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.70                (sk_E @ sk_C @ sk_B @ sk_A))) @ 
% 2.52/2.70              (u1_struct_0 @ (k1_tsep_1 @ X0 @ sk_B @ sk_C)) @ 
% 2.52/2.70              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70           | ~ (v1_funct_1 @ 
% 2.52/2.70                (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                 (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.70                 (sk_E @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70           | (v2_struct_0 @ X0)
% 2.52/2.70           | ~ (v2_pre_topc @ X0)
% 2.52/2.70           | ~ (l1_pre_topc @ X0)
% 2.52/2.70           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70           | ~ (m1_pre_topc @ sk_B @ X0)
% 2.52/2.70           | ~ (m1_pre_topc @ sk_C @ X0)))
% 2.52/2.70         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['271', '290'])).
% 2.52/2.70  thf('292', plain,
% 2.52/2.70      ((![X0 : $i]:
% 2.52/2.70          (~ (m1_pre_topc @ sk_C @ X0)
% 2.52/2.70           | ~ (m1_pre_topc @ sk_B @ X0)
% 2.52/2.70           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70           | ~ (l1_pre_topc @ X0)
% 2.52/2.70           | ~ (v2_pre_topc @ X0)
% 2.52/2.70           | (v2_struct_0 @ X0)
% 2.52/2.70           | ~ (v1_funct_1 @ 
% 2.52/2.70                (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                 (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.70                 (sk_E @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70           | (v1_funct_2 @ 
% 2.52/2.70              (k10_tmap_1 @ X0 @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ sk_C @ 
% 2.52/2.70               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70                (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.70                (sk_E @ sk_C @ sk_B @ sk_A))) @ 
% 2.52/2.70              (u1_struct_0 @ (k1_tsep_1 @ X0 @ sk_B @ sk_C)) @ 
% 2.52/2.70              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70           | (v2_struct_0 @ sk_A)
% 2.52/2.70           | (v2_struct_0 @ sk_C)
% 2.52/2.70           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_B)))
% 2.52/2.70         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('simplify', [status(thm)], ['291'])).
% 2.52/2.70  thf('293', plain,
% 2.52/2.70      ((![X0 : $i]:
% 2.52/2.70          ((v2_struct_0 @ sk_B)
% 2.52/2.70           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_A)
% 2.52/2.70           | (v2_struct_0 @ sk_B)
% 2.52/2.70           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_A)
% 2.52/2.70           | (v1_funct_2 @ 
% 2.52/2.70              (k10_tmap_1 @ X0 @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ sk_C @ 
% 2.52/2.70               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70                (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.70                (sk_E @ sk_C @ sk_B @ sk_A))) @ 
% 2.52/2.70              (u1_struct_0 @ (k1_tsep_1 @ X0 @ sk_B @ sk_C)) @ 
% 2.52/2.70              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70           | (v2_struct_0 @ X0)
% 2.52/2.70           | ~ (v2_pre_topc @ X0)
% 2.52/2.70           | ~ (l1_pre_topc @ X0)
% 2.52/2.70           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70           | ~ (m1_pre_topc @ sk_B @ X0)
% 2.52/2.70           | ~ (m1_pre_topc @ sk_C @ X0)))
% 2.52/2.70         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['270', '292'])).
% 2.52/2.70  thf('294', plain,
% 2.52/2.70      ((![X0 : $i]:
% 2.52/2.70          (~ (m1_pre_topc @ sk_C @ X0)
% 2.52/2.70           | ~ (m1_pre_topc @ sk_B @ X0)
% 2.52/2.70           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70           | ~ (l1_pre_topc @ X0)
% 2.52/2.70           | ~ (v2_pre_topc @ X0)
% 2.52/2.70           | (v2_struct_0 @ X0)
% 2.52/2.70           | (v1_funct_2 @ 
% 2.52/2.70              (k10_tmap_1 @ X0 @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ sk_C @ 
% 2.52/2.70               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70                (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.70                (sk_E @ sk_C @ sk_B @ sk_A))) @ 
% 2.52/2.70              (u1_struct_0 @ (k1_tsep_1 @ X0 @ sk_B @ sk_C)) @ 
% 2.52/2.70              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70           | (v2_struct_0 @ sk_A)
% 2.52/2.70           | (v2_struct_0 @ sk_C)
% 2.52/2.70           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_B)))
% 2.52/2.70         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('simplify', [status(thm)], ['293'])).
% 2.52/2.70  thf('295', plain,
% 2.52/2.70      ((((v2_struct_0 @ sk_B)
% 2.52/2.70         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70         | (v2_struct_0 @ sk_C)
% 2.52/2.70         | (v2_struct_0 @ sk_A)
% 2.52/2.70         | (v1_funct_2 @ 
% 2.52/2.70            (k10_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ sk_C @ 
% 2.52/2.70             (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70              (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70              (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70             (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70              (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.70              (sk_E @ sk_C @ sk_B @ sk_A))) @ 
% 2.52/2.70            (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.52/2.70            (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70         | (v2_struct_0 @ sk_A)
% 2.52/2.70         | ~ (v2_pre_topc @ sk_A)
% 2.52/2.70         | ~ (l1_pre_topc @ sk_A)
% 2.52/2.70         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70         | ~ (m1_pre_topc @ sk_B @ sk_A))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['269', '294'])).
% 2.52/2.70  thf('296', plain, ((v2_pre_topc @ sk_A)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('297', plain, ((l1_pre_topc @ sk_A)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('298', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('299', plain,
% 2.52/2.70      ((((v2_struct_0 @ sk_B)
% 2.52/2.70         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70         | (v2_struct_0 @ sk_C)
% 2.52/2.70         | (v2_struct_0 @ sk_A)
% 2.52/2.70         | (v1_funct_2 @ 
% 2.52/2.70            (k10_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ sk_C @ 
% 2.52/2.70             (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70              (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70              (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70             (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70              (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.70              (sk_E @ sk_C @ sk_B @ sk_A))) @ 
% 2.52/2.70            (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.52/2.70            (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70         | (v2_struct_0 @ sk_A)
% 2.52/2.70         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))))
% 2.52/2.70         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('demod', [status(thm)], ['295', '296', '297', '298'])).
% 2.52/2.70  thf('300', plain,
% 2.52/2.70      ((((v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70         | (v1_funct_2 @ 
% 2.52/2.70            (k10_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ sk_C @ 
% 2.52/2.70             (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70              (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70              (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70             (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70              (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.70              (sk_E @ sk_C @ sk_B @ sk_A))) @ 
% 2.52/2.70            (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.52/2.70            (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70         | (v2_struct_0 @ sk_A)
% 2.52/2.70         | (v2_struct_0 @ sk_C)
% 2.52/2.70         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('simplify', [status(thm)], ['299'])).
% 2.52/2.70  thf('301', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('302', plain,
% 2.52/2.70      ((((v2_struct_0 @ sk_A)
% 2.52/2.70         | (v2_struct_0 @ sk_C)
% 2.52/2.70         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70         | (v1_funct_1 @ 
% 2.52/2.70            (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70             (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.70             (sk_E @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['166', '174'])).
% 2.52/2.70  thf('303', plain,
% 2.52/2.70      ((((v2_struct_0 @ sk_A)
% 2.52/2.70         | (v2_struct_0 @ sk_C)
% 2.52/2.70         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70         | (v1_funct_2 @ 
% 2.52/2.70            (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70             (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.70             (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70            (u1_struct_0 @ sk_C) @ (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['176', '184'])).
% 2.52/2.70  thf('304', plain,
% 2.52/2.70      ((((v2_struct_0 @ sk_A)
% 2.52/2.70         | (v2_struct_0 @ sk_C)
% 2.52/2.70         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70         | (m1_subset_1 @ 
% 2.52/2.70            (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70             (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.70             (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70            (k1_zfmisc_1 @ 
% 2.52/2.70             (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.70              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.52/2.70         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['186', '194'])).
% 2.52/2.70  thf('305', plain,
% 2.52/2.70      ((((v2_struct_0 @ sk_A)
% 2.52/2.70         | (v2_struct_0 @ sk_C)
% 2.52/2.70         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70         | (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['196', '204'])).
% 2.52/2.70  thf('306', plain,
% 2.52/2.70      ((((v2_struct_0 @ sk_A)
% 2.52/2.70         | (v2_struct_0 @ sk_C)
% 2.52/2.70         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70         | (l1_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['206', '214'])).
% 2.52/2.70  thf('307', plain,
% 2.52/2.70      ((((v2_struct_0 @ sk_A)
% 2.52/2.70         | (v2_struct_0 @ sk_C)
% 2.52/2.70         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70         | (v1_funct_1 @ 
% 2.52/2.70            (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70             (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70             (sk_E @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['216', '224'])).
% 2.52/2.70  thf('308', plain,
% 2.52/2.70      ((((v2_struct_0 @ sk_A)
% 2.52/2.70         | (v2_struct_0 @ sk_C)
% 2.52/2.70         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70         | (v1_funct_2 @ 
% 2.52/2.70            (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70             (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70             (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70            (u1_struct_0 @ sk_B) @ (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['226', '234'])).
% 2.52/2.70  thf('309', plain,
% 2.52/2.70      ((((v2_struct_0 @ sk_A)
% 2.52/2.70         | (v2_struct_0 @ sk_C)
% 2.52/2.70         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70         | (m1_subset_1 @ 
% 2.52/2.70            (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70             (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70             (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70            (k1_zfmisc_1 @ 
% 2.52/2.70             (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.70              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.52/2.70         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['236', '244'])).
% 2.52/2.70  thf('310', plain,
% 2.52/2.70      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 2.52/2.70         (~ (m1_subset_1 @ X4 @ 
% 2.52/2.70             (k1_zfmisc_1 @ 
% 2.52/2.70              (k2_zfmisc_1 @ (u1_struct_0 @ X5) @ (u1_struct_0 @ X6))))
% 2.52/2.70          | ~ (v1_funct_2 @ X4 @ (u1_struct_0 @ X5) @ (u1_struct_0 @ X6))
% 2.52/2.70          | ~ (v1_funct_1 @ X4)
% 2.52/2.70          | ~ (m1_pre_topc @ X7 @ X8)
% 2.52/2.70          | (v2_struct_0 @ X7)
% 2.52/2.70          | ~ (m1_pre_topc @ X5 @ X8)
% 2.52/2.70          | (v2_struct_0 @ X5)
% 2.52/2.70          | ~ (l1_pre_topc @ X6)
% 2.52/2.70          | ~ (v2_pre_topc @ X6)
% 2.52/2.70          | (v2_struct_0 @ X6)
% 2.52/2.70          | ~ (l1_pre_topc @ X8)
% 2.52/2.70          | ~ (v2_pre_topc @ X8)
% 2.52/2.70          | (v2_struct_0 @ X8)
% 2.52/2.70          | ~ (v1_funct_1 @ X9)
% 2.52/2.70          | ~ (v1_funct_2 @ X9 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X6))
% 2.52/2.70          | ~ (m1_subset_1 @ X9 @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X6))))
% 2.52/2.70          | (m1_subset_1 @ (k10_tmap_1 @ X8 @ X6 @ X5 @ X7 @ X4 @ X9) @ 
% 2.52/2.70             (k1_zfmisc_1 @ 
% 2.52/2.70              (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X8 @ X5 @ X7)) @ 
% 2.52/2.70               (u1_struct_0 @ X6)))))),
% 2.52/2.70      inference('cnf', [status(esa)], [dt_k10_tmap_1])).
% 2.52/2.70  thf('311', plain,
% 2.52/2.70      ((![X0 : $i, X1 : $i, X2 : $i]:
% 2.52/2.70          ((v2_struct_0 @ sk_B)
% 2.52/2.70           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_A)
% 2.52/2.70           | (m1_subset_1 @ 
% 2.52/2.70              (k10_tmap_1 @ X1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ X0 @ 
% 2.52/2.70               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70                (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70               X2) @ 
% 2.52/2.70              (k1_zfmisc_1 @ 
% 2.52/2.70               (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X1 @ sk_B @ X0)) @ 
% 2.52/2.70                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.52/2.70           | ~ (m1_subset_1 @ X2 @ 
% 2.52/2.70                (k1_zfmisc_1 @ 
% 2.52/2.70                 (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ 
% 2.52/2.70                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.52/2.70           | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X0) @ 
% 2.52/2.70                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70           | ~ (v1_funct_1 @ X2)
% 2.52/2.70           | (v2_struct_0 @ X1)
% 2.52/2.70           | ~ (v2_pre_topc @ X1)
% 2.52/2.70           | ~ (l1_pre_topc @ X1)
% 2.52/2.70           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70           | ~ (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70           | ~ (l1_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70           | (v2_struct_0 @ sk_B)
% 2.52/2.70           | ~ (m1_pre_topc @ sk_B @ X1)
% 2.52/2.70           | (v2_struct_0 @ X0)
% 2.52/2.70           | ~ (m1_pre_topc @ X0 @ X1)
% 2.52/2.70           | ~ (v1_funct_1 @ 
% 2.52/2.70                (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                 (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70                 (sk_E @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70           | ~ (v1_funct_2 @ 
% 2.52/2.70                (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                 (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70                 (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70                (u1_struct_0 @ sk_B) @ 
% 2.52/2.70                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.52/2.70         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['309', '310'])).
% 2.52/2.70  thf('312', plain,
% 2.52/2.70      ((![X0 : $i, X1 : $i, X2 : $i]:
% 2.52/2.70          (~ (v1_funct_2 @ 
% 2.52/2.70              (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70               (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70               (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70              (u1_struct_0 @ sk_B) @ 
% 2.52/2.70              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70           | ~ (v1_funct_1 @ 
% 2.52/2.70                (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                 (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70                 (sk_E @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70           | ~ (m1_pre_topc @ X0 @ X1)
% 2.52/2.70           | (v2_struct_0 @ X0)
% 2.52/2.70           | ~ (m1_pre_topc @ sk_B @ X1)
% 2.52/2.70           | ~ (l1_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70           | ~ (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70           | ~ (l1_pre_topc @ X1)
% 2.52/2.70           | ~ (v2_pre_topc @ X1)
% 2.52/2.70           | (v2_struct_0 @ X1)
% 2.52/2.70           | ~ (v1_funct_1 @ X2)
% 2.52/2.70           | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X0) @ 
% 2.52/2.70                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70           | ~ (m1_subset_1 @ X2 @ 
% 2.52/2.70                (k1_zfmisc_1 @ 
% 2.52/2.70                 (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ 
% 2.52/2.70                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.52/2.70           | (m1_subset_1 @ 
% 2.52/2.70              (k10_tmap_1 @ X1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ X0 @ 
% 2.52/2.70               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70                (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70               X2) @ 
% 2.52/2.70              (k1_zfmisc_1 @ 
% 2.52/2.70               (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X1 @ sk_B @ X0)) @ 
% 2.52/2.70                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.52/2.70           | (v2_struct_0 @ sk_A)
% 2.52/2.70           | (v2_struct_0 @ sk_C)
% 2.52/2.70           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_B)))
% 2.52/2.70         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('simplify', [status(thm)], ['311'])).
% 2.52/2.70  thf('313', plain,
% 2.52/2.70      ((![X0 : $i, X1 : $i, X2 : $i]:
% 2.52/2.70          ((v2_struct_0 @ sk_B)
% 2.52/2.70           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_A)
% 2.52/2.70           | (v2_struct_0 @ sk_B)
% 2.52/2.70           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_A)
% 2.52/2.70           | (m1_subset_1 @ 
% 2.52/2.70              (k10_tmap_1 @ X1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ X0 @ 
% 2.52/2.70               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70                (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70               X2) @ 
% 2.52/2.70              (k1_zfmisc_1 @ 
% 2.52/2.70               (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X1 @ sk_B @ X0)) @ 
% 2.52/2.70                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.52/2.70           | ~ (m1_subset_1 @ X2 @ 
% 2.52/2.70                (k1_zfmisc_1 @ 
% 2.52/2.70                 (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ 
% 2.52/2.70                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.52/2.70           | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X0) @ 
% 2.52/2.70                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70           | ~ (v1_funct_1 @ X2)
% 2.52/2.70           | (v2_struct_0 @ X1)
% 2.52/2.70           | ~ (v2_pre_topc @ X1)
% 2.52/2.70           | ~ (l1_pre_topc @ X1)
% 2.52/2.70           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70           | ~ (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70           | ~ (l1_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70           | ~ (m1_pre_topc @ sk_B @ X1)
% 2.52/2.70           | (v2_struct_0 @ X0)
% 2.52/2.70           | ~ (m1_pre_topc @ X0 @ X1)
% 2.52/2.70           | ~ (v1_funct_1 @ 
% 2.52/2.70                (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                 (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70                 (sk_E @ sk_C @ sk_B @ sk_A)))))
% 2.52/2.70         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['308', '312'])).
% 2.52/2.70  thf('314', plain,
% 2.52/2.70      ((![X0 : $i, X1 : $i, X2 : $i]:
% 2.52/2.70          (~ (v1_funct_1 @ 
% 2.52/2.70              (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70               (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70               (sk_E @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70           | ~ (m1_pre_topc @ X0 @ X1)
% 2.52/2.70           | (v2_struct_0 @ X0)
% 2.52/2.70           | ~ (m1_pre_topc @ sk_B @ X1)
% 2.52/2.70           | ~ (l1_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70           | ~ (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70           | ~ (l1_pre_topc @ X1)
% 2.52/2.70           | ~ (v2_pre_topc @ X1)
% 2.52/2.70           | (v2_struct_0 @ X1)
% 2.52/2.70           | ~ (v1_funct_1 @ X2)
% 2.52/2.70           | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X0) @ 
% 2.52/2.70                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70           | ~ (m1_subset_1 @ X2 @ 
% 2.52/2.70                (k1_zfmisc_1 @ 
% 2.52/2.70                 (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ 
% 2.52/2.70                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.52/2.70           | (m1_subset_1 @ 
% 2.52/2.70              (k10_tmap_1 @ X1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ X0 @ 
% 2.52/2.70               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70                (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70               X2) @ 
% 2.52/2.70              (k1_zfmisc_1 @ 
% 2.52/2.70               (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X1 @ sk_B @ X0)) @ 
% 2.52/2.70                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.52/2.70           | (v2_struct_0 @ sk_A)
% 2.52/2.70           | (v2_struct_0 @ sk_C)
% 2.52/2.70           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_B)))
% 2.52/2.70         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('simplify', [status(thm)], ['313'])).
% 2.52/2.70  thf('315', plain,
% 2.52/2.70      ((![X0 : $i, X1 : $i, X2 : $i]:
% 2.52/2.70          ((v2_struct_0 @ sk_B)
% 2.52/2.70           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_A)
% 2.52/2.70           | (v2_struct_0 @ sk_B)
% 2.52/2.70           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_A)
% 2.52/2.70           | (m1_subset_1 @ 
% 2.52/2.70              (k10_tmap_1 @ X1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ X0 @ 
% 2.52/2.70               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70                (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70               X2) @ 
% 2.52/2.70              (k1_zfmisc_1 @ 
% 2.52/2.70               (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X1 @ sk_B @ X0)) @ 
% 2.52/2.70                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.52/2.70           | ~ (m1_subset_1 @ X2 @ 
% 2.52/2.70                (k1_zfmisc_1 @ 
% 2.52/2.70                 (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ 
% 2.52/2.70                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.52/2.70           | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X0) @ 
% 2.52/2.70                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70           | ~ (v1_funct_1 @ X2)
% 2.52/2.70           | (v2_struct_0 @ X1)
% 2.52/2.70           | ~ (v2_pre_topc @ X1)
% 2.52/2.70           | ~ (l1_pre_topc @ X1)
% 2.52/2.70           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70           | ~ (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70           | ~ (l1_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70           | ~ (m1_pre_topc @ sk_B @ X1)
% 2.52/2.70           | (v2_struct_0 @ X0)
% 2.52/2.70           | ~ (m1_pre_topc @ X0 @ X1)))
% 2.52/2.70         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['307', '314'])).
% 2.52/2.70  thf('316', plain,
% 2.52/2.70      ((![X0 : $i, X1 : $i, X2 : $i]:
% 2.52/2.70          (~ (m1_pre_topc @ X0 @ X1)
% 2.52/2.70           | (v2_struct_0 @ X0)
% 2.52/2.70           | ~ (m1_pre_topc @ sk_B @ X1)
% 2.52/2.70           | ~ (l1_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70           | ~ (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70           | ~ (l1_pre_topc @ X1)
% 2.52/2.70           | ~ (v2_pre_topc @ X1)
% 2.52/2.70           | (v2_struct_0 @ X1)
% 2.52/2.70           | ~ (v1_funct_1 @ X2)
% 2.52/2.70           | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X0) @ 
% 2.52/2.70                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70           | ~ (m1_subset_1 @ X2 @ 
% 2.52/2.70                (k1_zfmisc_1 @ 
% 2.52/2.70                 (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ 
% 2.52/2.70                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.52/2.70           | (m1_subset_1 @ 
% 2.52/2.70              (k10_tmap_1 @ X1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ X0 @ 
% 2.52/2.70               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70                (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70               X2) @ 
% 2.52/2.70              (k1_zfmisc_1 @ 
% 2.52/2.70               (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X1 @ sk_B @ X0)) @ 
% 2.52/2.70                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.52/2.70           | (v2_struct_0 @ sk_A)
% 2.52/2.70           | (v2_struct_0 @ sk_C)
% 2.52/2.70           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_B)))
% 2.52/2.70         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('simplify', [status(thm)], ['315'])).
% 2.52/2.70  thf('317', plain,
% 2.52/2.70      ((![X0 : $i, X1 : $i, X2 : $i]:
% 2.52/2.70          ((v2_struct_0 @ sk_B)
% 2.52/2.70           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_A)
% 2.52/2.70           | (v2_struct_0 @ sk_B)
% 2.52/2.70           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_A)
% 2.52/2.70           | (m1_subset_1 @ 
% 2.52/2.70              (k10_tmap_1 @ X1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ X0 @ 
% 2.52/2.70               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70                (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70               X2) @ 
% 2.52/2.70              (k1_zfmisc_1 @ 
% 2.52/2.70               (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X1 @ sk_B @ X0)) @ 
% 2.52/2.70                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.52/2.70           | ~ (m1_subset_1 @ X2 @ 
% 2.52/2.70                (k1_zfmisc_1 @ 
% 2.52/2.70                 (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ 
% 2.52/2.70                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.52/2.70           | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X0) @ 
% 2.52/2.70                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70           | ~ (v1_funct_1 @ X2)
% 2.52/2.70           | (v2_struct_0 @ X1)
% 2.52/2.70           | ~ (v2_pre_topc @ X1)
% 2.52/2.70           | ~ (l1_pre_topc @ X1)
% 2.52/2.70           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70           | ~ (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70           | ~ (m1_pre_topc @ sk_B @ X1)
% 2.52/2.70           | (v2_struct_0 @ X0)
% 2.52/2.70           | ~ (m1_pre_topc @ X0 @ X1)))
% 2.52/2.70         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['306', '316'])).
% 2.52/2.70  thf('318', plain,
% 2.52/2.70      ((![X0 : $i, X1 : $i, X2 : $i]:
% 2.52/2.70          (~ (m1_pre_topc @ X0 @ X1)
% 2.52/2.70           | (v2_struct_0 @ X0)
% 2.52/2.70           | ~ (m1_pre_topc @ sk_B @ X1)
% 2.52/2.70           | ~ (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70           | ~ (l1_pre_topc @ X1)
% 2.52/2.70           | ~ (v2_pre_topc @ X1)
% 2.52/2.70           | (v2_struct_0 @ X1)
% 2.52/2.70           | ~ (v1_funct_1 @ X2)
% 2.52/2.70           | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X0) @ 
% 2.52/2.70                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70           | ~ (m1_subset_1 @ X2 @ 
% 2.52/2.70                (k1_zfmisc_1 @ 
% 2.52/2.70                 (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ 
% 2.52/2.70                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.52/2.70           | (m1_subset_1 @ 
% 2.52/2.70              (k10_tmap_1 @ X1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ X0 @ 
% 2.52/2.70               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70                (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70               X2) @ 
% 2.52/2.70              (k1_zfmisc_1 @ 
% 2.52/2.70               (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X1 @ sk_B @ X0)) @ 
% 2.52/2.70                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.52/2.70           | (v2_struct_0 @ sk_A)
% 2.52/2.70           | (v2_struct_0 @ sk_C)
% 2.52/2.70           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_B)))
% 2.52/2.70         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('simplify', [status(thm)], ['317'])).
% 2.52/2.70  thf('319', plain,
% 2.52/2.70      ((![X0 : $i, X1 : $i, X2 : $i]:
% 2.52/2.70          ((v2_struct_0 @ sk_B)
% 2.52/2.70           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_A)
% 2.52/2.70           | (v2_struct_0 @ sk_B)
% 2.52/2.70           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_A)
% 2.52/2.70           | (m1_subset_1 @ 
% 2.52/2.70              (k10_tmap_1 @ X1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ X0 @ 
% 2.52/2.70               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70                (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70               X2) @ 
% 2.52/2.70              (k1_zfmisc_1 @ 
% 2.52/2.70               (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X1 @ sk_B @ X0)) @ 
% 2.52/2.70                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.52/2.70           | ~ (m1_subset_1 @ X2 @ 
% 2.52/2.70                (k1_zfmisc_1 @ 
% 2.52/2.70                 (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ 
% 2.52/2.70                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.52/2.70           | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X0) @ 
% 2.52/2.70                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70           | ~ (v1_funct_1 @ X2)
% 2.52/2.70           | (v2_struct_0 @ X1)
% 2.52/2.70           | ~ (v2_pre_topc @ X1)
% 2.52/2.70           | ~ (l1_pre_topc @ X1)
% 2.52/2.70           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70           | ~ (m1_pre_topc @ sk_B @ X1)
% 2.52/2.70           | (v2_struct_0 @ X0)
% 2.52/2.70           | ~ (m1_pre_topc @ X0 @ X1)))
% 2.52/2.70         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['305', '318'])).
% 2.52/2.70  thf('320', plain,
% 2.52/2.70      ((![X0 : $i, X1 : $i, X2 : $i]:
% 2.52/2.70          (~ (m1_pre_topc @ X0 @ X1)
% 2.52/2.70           | (v2_struct_0 @ X0)
% 2.52/2.70           | ~ (m1_pre_topc @ sk_B @ X1)
% 2.52/2.70           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70           | ~ (l1_pre_topc @ X1)
% 2.52/2.70           | ~ (v2_pre_topc @ X1)
% 2.52/2.70           | (v2_struct_0 @ X1)
% 2.52/2.70           | ~ (v1_funct_1 @ X2)
% 2.52/2.70           | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X0) @ 
% 2.52/2.70                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70           | ~ (m1_subset_1 @ X2 @ 
% 2.52/2.70                (k1_zfmisc_1 @ 
% 2.52/2.70                 (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ 
% 2.52/2.70                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.52/2.70           | (m1_subset_1 @ 
% 2.52/2.70              (k10_tmap_1 @ X1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ X0 @ 
% 2.52/2.70               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70                (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70               X2) @ 
% 2.52/2.70              (k1_zfmisc_1 @ 
% 2.52/2.70               (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X1 @ sk_B @ X0)) @ 
% 2.52/2.70                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.52/2.70           | (v2_struct_0 @ sk_A)
% 2.52/2.70           | (v2_struct_0 @ sk_C)
% 2.52/2.70           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_B)))
% 2.52/2.70         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('simplify', [status(thm)], ['319'])).
% 2.52/2.70  thf('321', plain,
% 2.52/2.70      ((![X0 : $i]:
% 2.52/2.70          ((v2_struct_0 @ sk_B)
% 2.52/2.70           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_A)
% 2.52/2.70           | (v2_struct_0 @ sk_B)
% 2.52/2.70           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_A)
% 2.52/2.70           | (m1_subset_1 @ 
% 2.52/2.70              (k10_tmap_1 @ X0 @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ sk_C @ 
% 2.52/2.70               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70                (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.70                (sk_E @ sk_C @ sk_B @ sk_A))) @ 
% 2.52/2.70              (k1_zfmisc_1 @ 
% 2.52/2.70               (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X0 @ sk_B @ sk_C)) @ 
% 2.52/2.70                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.52/2.70           | ~ (v1_funct_2 @ 
% 2.52/2.70                (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                 (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.70                 (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70                (u1_struct_0 @ sk_C) @ 
% 2.52/2.70                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70           | ~ (v1_funct_1 @ 
% 2.52/2.70                (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                 (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.70                 (sk_E @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70           | (v2_struct_0 @ X0)
% 2.52/2.70           | ~ (v2_pre_topc @ X0)
% 2.52/2.70           | ~ (l1_pre_topc @ X0)
% 2.52/2.70           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70           | ~ (m1_pre_topc @ sk_B @ X0)
% 2.52/2.70           | (v2_struct_0 @ sk_C)
% 2.52/2.70           | ~ (m1_pre_topc @ sk_C @ X0)))
% 2.52/2.70         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['304', '320'])).
% 2.52/2.70  thf('322', plain,
% 2.52/2.70      ((![X0 : $i]:
% 2.52/2.70          (~ (m1_pre_topc @ sk_C @ X0)
% 2.52/2.70           | ~ (m1_pre_topc @ sk_B @ X0)
% 2.52/2.70           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70           | ~ (l1_pre_topc @ X0)
% 2.52/2.70           | ~ (v2_pre_topc @ X0)
% 2.52/2.70           | (v2_struct_0 @ X0)
% 2.52/2.70           | ~ (v1_funct_1 @ 
% 2.52/2.70                (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                 (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.70                 (sk_E @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70           | ~ (v1_funct_2 @ 
% 2.52/2.70                (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                 (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.70                 (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70                (u1_struct_0 @ sk_C) @ 
% 2.52/2.70                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70           | (m1_subset_1 @ 
% 2.52/2.70              (k10_tmap_1 @ X0 @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ sk_C @ 
% 2.52/2.70               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70                (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.70                (sk_E @ sk_C @ sk_B @ sk_A))) @ 
% 2.52/2.70              (k1_zfmisc_1 @ 
% 2.52/2.70               (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X0 @ sk_B @ sk_C)) @ 
% 2.52/2.70                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.52/2.70           | (v2_struct_0 @ sk_A)
% 2.52/2.70           | (v2_struct_0 @ sk_C)
% 2.52/2.70           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_B)))
% 2.52/2.70         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('simplify', [status(thm)], ['321'])).
% 2.52/2.70  thf('323', plain,
% 2.52/2.70      ((![X0 : $i]:
% 2.52/2.70          ((v2_struct_0 @ sk_B)
% 2.52/2.70           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_A)
% 2.52/2.70           | (v2_struct_0 @ sk_B)
% 2.52/2.70           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_A)
% 2.52/2.70           | (m1_subset_1 @ 
% 2.52/2.70              (k10_tmap_1 @ X0 @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ sk_C @ 
% 2.52/2.70               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70                (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.70                (sk_E @ sk_C @ sk_B @ sk_A))) @ 
% 2.52/2.70              (k1_zfmisc_1 @ 
% 2.52/2.70               (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X0 @ sk_B @ sk_C)) @ 
% 2.52/2.70                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.52/2.70           | ~ (v1_funct_1 @ 
% 2.52/2.70                (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                 (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.70                 (sk_E @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70           | (v2_struct_0 @ X0)
% 2.52/2.70           | ~ (v2_pre_topc @ X0)
% 2.52/2.70           | ~ (l1_pre_topc @ X0)
% 2.52/2.70           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70           | ~ (m1_pre_topc @ sk_B @ X0)
% 2.52/2.70           | ~ (m1_pre_topc @ sk_C @ X0)))
% 2.52/2.70         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['303', '322'])).
% 2.52/2.70  thf('324', plain,
% 2.52/2.70      ((![X0 : $i]:
% 2.52/2.70          (~ (m1_pre_topc @ sk_C @ X0)
% 2.52/2.70           | ~ (m1_pre_topc @ sk_B @ X0)
% 2.52/2.70           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70           | ~ (l1_pre_topc @ X0)
% 2.52/2.70           | ~ (v2_pre_topc @ X0)
% 2.52/2.70           | (v2_struct_0 @ X0)
% 2.52/2.70           | ~ (v1_funct_1 @ 
% 2.52/2.70                (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                 (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.70                 (sk_E @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70           | (m1_subset_1 @ 
% 2.52/2.70              (k10_tmap_1 @ X0 @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ sk_C @ 
% 2.52/2.70               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70                (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.70                (sk_E @ sk_C @ sk_B @ sk_A))) @ 
% 2.52/2.70              (k1_zfmisc_1 @ 
% 2.52/2.70               (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X0 @ sk_B @ sk_C)) @ 
% 2.52/2.70                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.52/2.70           | (v2_struct_0 @ sk_A)
% 2.52/2.70           | (v2_struct_0 @ sk_C)
% 2.52/2.70           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_B)))
% 2.52/2.70         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('simplify', [status(thm)], ['323'])).
% 2.52/2.70  thf('325', plain,
% 2.52/2.70      ((![X0 : $i]:
% 2.52/2.70          ((v2_struct_0 @ sk_B)
% 2.52/2.70           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_A)
% 2.52/2.70           | (v2_struct_0 @ sk_B)
% 2.52/2.70           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_A)
% 2.52/2.70           | (m1_subset_1 @ 
% 2.52/2.70              (k10_tmap_1 @ X0 @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ sk_C @ 
% 2.52/2.70               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70                (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.70                (sk_E @ sk_C @ sk_B @ sk_A))) @ 
% 2.52/2.70              (k1_zfmisc_1 @ 
% 2.52/2.70               (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X0 @ sk_B @ sk_C)) @ 
% 2.52/2.70                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.52/2.70           | (v2_struct_0 @ X0)
% 2.52/2.70           | ~ (v2_pre_topc @ X0)
% 2.52/2.70           | ~ (l1_pre_topc @ X0)
% 2.52/2.70           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70           | ~ (m1_pre_topc @ sk_B @ X0)
% 2.52/2.70           | ~ (m1_pre_topc @ sk_C @ X0)))
% 2.52/2.70         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['302', '324'])).
% 2.52/2.70  thf('326', plain,
% 2.52/2.70      ((![X0 : $i]:
% 2.52/2.70          (~ (m1_pre_topc @ sk_C @ X0)
% 2.52/2.70           | ~ (m1_pre_topc @ sk_B @ X0)
% 2.52/2.70           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70           | ~ (l1_pre_topc @ X0)
% 2.52/2.70           | ~ (v2_pre_topc @ X0)
% 2.52/2.70           | (v2_struct_0 @ X0)
% 2.52/2.70           | (m1_subset_1 @ 
% 2.52/2.70              (k10_tmap_1 @ X0 @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ sk_C @ 
% 2.52/2.70               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70                (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.70                (sk_E @ sk_C @ sk_B @ sk_A))) @ 
% 2.52/2.70              (k1_zfmisc_1 @ 
% 2.52/2.70               (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X0 @ sk_B @ sk_C)) @ 
% 2.52/2.70                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.52/2.70           | (v2_struct_0 @ sk_A)
% 2.52/2.70           | (v2_struct_0 @ sk_C)
% 2.52/2.70           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70           | (v2_struct_0 @ sk_B)))
% 2.52/2.70         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('simplify', [status(thm)], ['325'])).
% 2.52/2.70  thf('327', plain,
% 2.52/2.70      ((((v2_struct_0 @ sk_B)
% 2.52/2.70         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70         | (v2_struct_0 @ sk_C)
% 2.52/2.70         | (v2_struct_0 @ sk_A)
% 2.52/2.70         | (m1_subset_1 @ 
% 2.52/2.70            (k10_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ sk_C @ 
% 2.52/2.70             (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70              (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70              (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70             (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70              (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.70              (sk_E @ sk_C @ sk_B @ sk_A))) @ 
% 2.52/2.70            (k1_zfmisc_1 @ 
% 2.52/2.70             (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.52/2.70              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.52/2.70         | (v2_struct_0 @ sk_A)
% 2.52/2.70         | ~ (v2_pre_topc @ sk_A)
% 2.52/2.70         | ~ (l1_pre_topc @ sk_A)
% 2.52/2.70         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70         | ~ (m1_pre_topc @ sk_B @ sk_A))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['301', '326'])).
% 2.52/2.70  thf('328', plain, ((v2_pre_topc @ sk_A)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('329', plain, ((l1_pre_topc @ sk_A)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('330', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('331', plain,
% 2.52/2.70      ((((v2_struct_0 @ sk_B)
% 2.52/2.70         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70         | (v2_struct_0 @ sk_C)
% 2.52/2.70         | (v2_struct_0 @ sk_A)
% 2.52/2.70         | (m1_subset_1 @ 
% 2.52/2.70            (k10_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ sk_C @ 
% 2.52/2.70             (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70              (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70              (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70             (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70              (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.70              (sk_E @ sk_C @ sk_B @ sk_A))) @ 
% 2.52/2.70            (k1_zfmisc_1 @ 
% 2.52/2.70             (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.52/2.70              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.52/2.70         | (v2_struct_0 @ sk_A)
% 2.52/2.70         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))))
% 2.52/2.70         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('demod', [status(thm)], ['327', '328', '329', '330'])).
% 2.52/2.70  thf('332', plain,
% 2.52/2.70      ((((v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70         | (m1_subset_1 @ 
% 2.52/2.70            (k10_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ sk_C @ 
% 2.52/2.70             (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70              (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70              (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70             (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70              (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.70              (sk_E @ sk_C @ sk_B @ sk_A))) @ 
% 2.52/2.70            (k1_zfmisc_1 @ 
% 2.52/2.70             (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.52/2.70              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.52/2.70         | (v2_struct_0 @ sk_A)
% 2.52/2.70         | (v2_struct_0 @ sk_C)
% 2.52/2.70         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('simplify', [status(thm)], ['331'])).
% 2.52/2.70  thf('333', plain,
% 2.52/2.70      ((((v2_struct_0 @ sk_A)
% 2.52/2.70         | (v2_struct_0 @ sk_C)
% 2.52/2.70         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70         | (v1_funct_1 @ (sk_E @ sk_C @ sk_B @ sk_A))
% 2.52/2.70         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['155', '163'])).
% 2.52/2.70  thf('334', plain,
% 2.52/2.70      ((((v2_struct_0 @ sk_A)
% 2.52/2.70         | (v2_struct_0 @ sk_C)
% 2.52/2.70         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70         | (l1_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['206', '214'])).
% 2.52/2.70  thf('335', plain,
% 2.52/2.70      ((((v2_struct_0 @ sk_A)
% 2.52/2.70         | (v2_struct_0 @ sk_C)
% 2.52/2.70         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70         | (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['196', '204'])).
% 2.52/2.70  thf('336', plain,
% 2.52/2.70      (((r1_tsep_1 @ sk_B @ sk_C)) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('split', [status(esa)], ['0'])).
% 2.52/2.70  thf('337', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('338', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('339', plain,
% 2.52/2.70      (![X10 : $i, X11 : $i, X12 : $i]:
% 2.52/2.70         ((v2_struct_0 @ X10)
% 2.52/2.70          | ~ (m1_pre_topc @ X10 @ X11)
% 2.52/2.70          | ~ (r1_tsep_1 @ X10 @ X12)
% 2.52/2.70          | (v1_funct_2 @ (sk_E @ X12 @ X10 @ X11) @ 
% 2.52/2.70             (u1_struct_0 @ (k1_tsep_1 @ X11 @ X10 @ X12)) @ 
% 2.52/2.70             (u1_struct_0 @ (sk_D @ X12 @ X10 @ X11)))
% 2.52/2.70          | (r3_tsep_1 @ X11 @ X10 @ X12)
% 2.52/2.70          | ~ (m1_pre_topc @ X12 @ X11)
% 2.52/2.70          | (v2_struct_0 @ X12)
% 2.52/2.70          | ~ (l1_pre_topc @ X11)
% 2.52/2.70          | ~ (v2_pre_topc @ X11)
% 2.52/2.70          | (v2_struct_0 @ X11))),
% 2.52/2.70      inference('cnf', [status(esa)], [t135_tmap_1])).
% 2.52/2.70  thf('340', plain,
% 2.52/2.70      (![X0 : $i]:
% 2.52/2.70         ((v2_struct_0 @ sk_A)
% 2.52/2.70          | ~ (v2_pre_topc @ sk_A)
% 2.52/2.70          | ~ (l1_pre_topc @ sk_A)
% 2.52/2.70          | (v2_struct_0 @ X0)
% 2.52/2.70          | ~ (m1_pre_topc @ X0 @ sk_A)
% 2.52/2.70          | (r3_tsep_1 @ sk_A @ sk_B @ X0)
% 2.52/2.70          | (v1_funct_2 @ (sk_E @ X0 @ sk_B @ sk_A) @ 
% 2.52/2.70             (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ X0)) @ 
% 2.52/2.70             (u1_struct_0 @ (sk_D @ X0 @ sk_B @ sk_A)))
% 2.52/2.70          | ~ (r1_tsep_1 @ sk_B @ X0)
% 2.52/2.70          | (v2_struct_0 @ sk_B))),
% 2.52/2.70      inference('sup-', [status(thm)], ['338', '339'])).
% 2.52/2.70  thf('341', plain, ((v2_pre_topc @ sk_A)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('342', plain, ((l1_pre_topc @ sk_A)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('343', plain,
% 2.52/2.70      (![X0 : $i]:
% 2.52/2.70         ((v2_struct_0 @ sk_A)
% 2.52/2.70          | (v2_struct_0 @ X0)
% 2.52/2.70          | ~ (m1_pre_topc @ X0 @ sk_A)
% 2.52/2.70          | (r3_tsep_1 @ sk_A @ sk_B @ X0)
% 2.52/2.70          | (v1_funct_2 @ (sk_E @ X0 @ sk_B @ sk_A) @ 
% 2.52/2.70             (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ X0)) @ 
% 2.52/2.70             (u1_struct_0 @ (sk_D @ X0 @ sk_B @ sk_A)))
% 2.52/2.70          | ~ (r1_tsep_1 @ sk_B @ X0)
% 2.52/2.70          | (v2_struct_0 @ sk_B))),
% 2.52/2.70      inference('demod', [status(thm)], ['340', '341', '342'])).
% 2.52/2.70  thf('344', plain,
% 2.52/2.70      (((v2_struct_0 @ sk_B)
% 2.52/2.70        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 2.52/2.70        | (v1_funct_2 @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70           (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.52/2.70           (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70        | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70        | (v2_struct_0 @ sk_C)
% 2.52/2.70        | (v2_struct_0 @ sk_A))),
% 2.52/2.70      inference('sup-', [status(thm)], ['337', '343'])).
% 2.52/2.70  thf('345', plain,
% 2.52/2.70      ((((v2_struct_0 @ sk_A)
% 2.52/2.70         | (v2_struct_0 @ sk_C)
% 2.52/2.70         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70         | (v1_funct_2 @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70            (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.52/2.70            (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['336', '344'])).
% 2.52/2.70  thf('346', plain,
% 2.52/2.70      (((r1_tsep_1 @ sk_B @ sk_C)) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('split', [status(esa)], ['0'])).
% 2.52/2.70  thf('347', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('348', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('349', plain,
% 2.52/2.70      (![X10 : $i, X11 : $i, X12 : $i]:
% 2.52/2.70         ((v2_struct_0 @ X10)
% 2.52/2.70          | ~ (m1_pre_topc @ X10 @ X11)
% 2.52/2.70          | ~ (r1_tsep_1 @ X10 @ X12)
% 2.52/2.70          | (m1_subset_1 @ (sk_E @ X12 @ X10 @ X11) @ 
% 2.52/2.70             (k1_zfmisc_1 @ 
% 2.52/2.70              (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X11 @ X10 @ X12)) @ 
% 2.52/2.70               (u1_struct_0 @ (sk_D @ X12 @ X10 @ X11)))))
% 2.52/2.70          | (r3_tsep_1 @ X11 @ X10 @ X12)
% 2.52/2.70          | ~ (m1_pre_topc @ X12 @ X11)
% 2.52/2.70          | (v2_struct_0 @ X12)
% 2.52/2.70          | ~ (l1_pre_topc @ X11)
% 2.52/2.70          | ~ (v2_pre_topc @ X11)
% 2.52/2.70          | (v2_struct_0 @ X11))),
% 2.52/2.70      inference('cnf', [status(esa)], [t135_tmap_1])).
% 2.52/2.70  thf('350', plain,
% 2.52/2.70      (![X0 : $i]:
% 2.52/2.70         ((v2_struct_0 @ sk_A)
% 2.52/2.70          | ~ (v2_pre_topc @ sk_A)
% 2.52/2.70          | ~ (l1_pre_topc @ sk_A)
% 2.52/2.70          | (v2_struct_0 @ X0)
% 2.52/2.70          | ~ (m1_pre_topc @ X0 @ sk_A)
% 2.52/2.70          | (r3_tsep_1 @ sk_A @ sk_B @ X0)
% 2.52/2.70          | (m1_subset_1 @ (sk_E @ X0 @ sk_B @ sk_A) @ 
% 2.52/2.70             (k1_zfmisc_1 @ 
% 2.52/2.70              (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ X0)) @ 
% 2.52/2.70               (u1_struct_0 @ (sk_D @ X0 @ sk_B @ sk_A)))))
% 2.52/2.70          | ~ (r1_tsep_1 @ sk_B @ X0)
% 2.52/2.70          | (v2_struct_0 @ sk_B))),
% 2.52/2.70      inference('sup-', [status(thm)], ['348', '349'])).
% 2.52/2.70  thf('351', plain, ((v2_pre_topc @ sk_A)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('352', plain, ((l1_pre_topc @ sk_A)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('353', plain,
% 2.52/2.70      (![X0 : $i]:
% 2.52/2.70         ((v2_struct_0 @ sk_A)
% 2.52/2.70          | (v2_struct_0 @ X0)
% 2.52/2.70          | ~ (m1_pre_topc @ X0 @ sk_A)
% 2.52/2.70          | (r3_tsep_1 @ sk_A @ sk_B @ X0)
% 2.52/2.70          | (m1_subset_1 @ (sk_E @ X0 @ sk_B @ sk_A) @ 
% 2.52/2.70             (k1_zfmisc_1 @ 
% 2.52/2.70              (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ X0)) @ 
% 2.52/2.70               (u1_struct_0 @ (sk_D @ X0 @ sk_B @ sk_A)))))
% 2.52/2.70          | ~ (r1_tsep_1 @ sk_B @ X0)
% 2.52/2.70          | (v2_struct_0 @ sk_B))),
% 2.52/2.70      inference('demod', [status(thm)], ['350', '351', '352'])).
% 2.52/2.70  thf('354', plain,
% 2.52/2.70      (((v2_struct_0 @ sk_B)
% 2.52/2.70        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 2.52/2.70        | (m1_subset_1 @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70           (k1_zfmisc_1 @ 
% 2.52/2.70            (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.52/2.70             (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.52/2.70        | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70        | (v2_struct_0 @ sk_C)
% 2.52/2.70        | (v2_struct_0 @ sk_A))),
% 2.52/2.70      inference('sup-', [status(thm)], ['347', '353'])).
% 2.52/2.70  thf('355', plain,
% 2.52/2.70      ((((v2_struct_0 @ sk_A)
% 2.52/2.70         | (v2_struct_0 @ sk_C)
% 2.52/2.70         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70         | (m1_subset_1 @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70            (k1_zfmisc_1 @ 
% 2.52/2.70             (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.52/2.70              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.52/2.70         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['346', '354'])).
% 2.52/2.70  thf(t138_tmap_1, axiom,
% 2.52/2.70    (![A:$i]:
% 2.52/2.70     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.52/2.70       ( ![B:$i]:
% 2.52/2.70         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 2.52/2.70             ( l1_pre_topc @ B ) ) =>
% 2.52/2.70           ( ![C:$i]:
% 2.52/2.70             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 2.52/2.70               ( ![D:$i]:
% 2.52/2.70                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 2.52/2.70                   ( ![E:$i]:
% 2.52/2.70                     ( ( ( v1_funct_1 @ E ) & 
% 2.52/2.70                         ( v1_funct_2 @
% 2.52/2.70                           E @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 2.52/2.70                           ( u1_struct_0 @ B ) ) & 
% 2.52/2.70                         ( m1_subset_1 @
% 2.52/2.70                           E @ 
% 2.52/2.70                           ( k1_zfmisc_1 @
% 2.52/2.70                             ( k2_zfmisc_1 @
% 2.52/2.70                               ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 2.52/2.70                               ( u1_struct_0 @ B ) ) ) ) ) =>
% 2.52/2.70                       ( r2_funct_2 @
% 2.52/2.70                         ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 2.52/2.70                         ( u1_struct_0 @ B ) @ E @ 
% 2.52/2.70                         ( k10_tmap_1 @
% 2.52/2.70                           A @ B @ C @ D @ 
% 2.52/2.70                           ( k3_tmap_1 @
% 2.52/2.70                             A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ C @ E ) @ 
% 2.52/2.70                           ( k3_tmap_1 @
% 2.52/2.70                             A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ D @ E ) ) ) ) ) ) ) ) ) ) ) ))).
% 2.52/2.70  thf('356', plain,
% 2.52/2.70      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 2.52/2.70         ((v2_struct_0 @ X15)
% 2.52/2.70          | ~ (v2_pre_topc @ X15)
% 2.52/2.70          | ~ (l1_pre_topc @ X15)
% 2.52/2.70          | (v2_struct_0 @ X16)
% 2.52/2.70          | ~ (m1_pre_topc @ X16 @ X17)
% 2.52/2.70          | (r2_funct_2 @ (u1_struct_0 @ (k1_tsep_1 @ X17 @ X18 @ X16)) @ 
% 2.52/2.70             (u1_struct_0 @ X15) @ X19 @ 
% 2.52/2.70             (k10_tmap_1 @ X17 @ X15 @ X18 @ X16 @ 
% 2.52/2.70              (k3_tmap_1 @ X17 @ X15 @ (k1_tsep_1 @ X17 @ X18 @ X16) @ X18 @ 
% 2.52/2.70               X19) @ 
% 2.52/2.70              (k3_tmap_1 @ X17 @ X15 @ (k1_tsep_1 @ X17 @ X18 @ X16) @ X16 @ 
% 2.52/2.70               X19)))
% 2.52/2.70          | ~ (m1_subset_1 @ X19 @ 
% 2.52/2.70               (k1_zfmisc_1 @ 
% 2.52/2.70                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X17 @ X18 @ X16)) @ 
% 2.52/2.70                 (u1_struct_0 @ X15))))
% 2.52/2.70          | ~ (v1_funct_2 @ X19 @ 
% 2.52/2.70               (u1_struct_0 @ (k1_tsep_1 @ X17 @ X18 @ X16)) @ 
% 2.52/2.70               (u1_struct_0 @ X15))
% 2.52/2.70          | ~ (v1_funct_1 @ X19)
% 2.52/2.70          | ~ (m1_pre_topc @ X18 @ X17)
% 2.52/2.70          | (v2_struct_0 @ X18)
% 2.52/2.70          | ~ (l1_pre_topc @ X17)
% 2.52/2.70          | ~ (v2_pre_topc @ X17)
% 2.52/2.70          | (v2_struct_0 @ X17))),
% 2.52/2.70      inference('cnf', [status(esa)], [t138_tmap_1])).
% 2.52/2.70  thf('357', plain,
% 2.52/2.70      ((((v2_struct_0 @ sk_B)
% 2.52/2.70         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70         | (v2_struct_0 @ sk_C)
% 2.52/2.70         | (v2_struct_0 @ sk_A)
% 2.52/2.70         | (v2_struct_0 @ sk_A)
% 2.52/2.70         | ~ (v2_pre_topc @ sk_A)
% 2.52/2.70         | ~ (l1_pre_topc @ sk_A)
% 2.52/2.70         | (v2_struct_0 @ sk_B)
% 2.52/2.70         | ~ (m1_pre_topc @ sk_B @ sk_A)
% 2.52/2.70         | ~ (v1_funct_1 @ (sk_E @ sk_C @ sk_B @ sk_A))
% 2.52/2.70         | ~ (v1_funct_2 @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70              (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.52/2.70              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70         | (r2_funct_2 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.52/2.70            (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70            (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70            (k10_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ sk_C @ 
% 2.52/2.70             (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70              (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70              (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70             (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70              (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.70              (sk_E @ sk_C @ sk_B @ sk_A))))
% 2.52/2.70         | ~ (m1_pre_topc @ sk_C @ sk_A)
% 2.52/2.70         | (v2_struct_0 @ sk_C)
% 2.52/2.70         | ~ (l1_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70         | ~ (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))))
% 2.52/2.70         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['355', '356'])).
% 2.52/2.70  thf('358', plain, ((v2_pre_topc @ sk_A)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('359', plain, ((l1_pre_topc @ sk_A)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('360', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('361', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 2.52/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.70  thf('362', plain,
% 2.52/2.70      ((((v2_struct_0 @ sk_B)
% 2.52/2.70         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70         | (v2_struct_0 @ sk_C)
% 2.52/2.70         | (v2_struct_0 @ sk_A)
% 2.52/2.70         | (v2_struct_0 @ sk_A)
% 2.52/2.70         | (v2_struct_0 @ sk_B)
% 2.52/2.70         | ~ (v1_funct_1 @ (sk_E @ sk_C @ sk_B @ sk_A))
% 2.52/2.70         | ~ (v1_funct_2 @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70              (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.52/2.70              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70         | (r2_funct_2 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.52/2.70            (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70            (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70            (k10_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ sk_C @ 
% 2.52/2.70             (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70              (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70              (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70             (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70              (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.70              (sk_E @ sk_C @ sk_B @ sk_A))))
% 2.52/2.70         | (v2_struct_0 @ sk_C)
% 2.52/2.70         | ~ (l1_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70         | ~ (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))))
% 2.52/2.70         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('demod', [status(thm)], ['357', '358', '359', '360', '361'])).
% 2.52/2.70  thf('363', plain,
% 2.52/2.70      ((((v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70         | ~ (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70         | ~ (l1_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70         | (r2_funct_2 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.52/2.70            (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70            (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70            (k10_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ sk_C @ 
% 2.52/2.70             (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70              (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70              (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70             (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70              (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.70              (sk_E @ sk_C @ sk_B @ sk_A))))
% 2.52/2.70         | ~ (v1_funct_2 @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70              (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.52/2.70              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.70         | ~ (v1_funct_1 @ (sk_E @ sk_C @ sk_B @ sk_A))
% 2.52/2.70         | (v2_struct_0 @ sk_A)
% 2.52/2.70         | (v2_struct_0 @ sk_C)
% 2.52/2.70         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('simplify', [status(thm)], ['362'])).
% 2.52/2.70  thf('364', plain,
% 2.52/2.70      ((((v2_struct_0 @ sk_B)
% 2.52/2.70         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70         | (v2_struct_0 @ sk_C)
% 2.52/2.70         | (v2_struct_0 @ sk_A)
% 2.52/2.70         | (v2_struct_0 @ sk_B)
% 2.52/2.70         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70         | (v2_struct_0 @ sk_C)
% 2.52/2.70         | (v2_struct_0 @ sk_A)
% 2.52/2.70         | ~ (v1_funct_1 @ (sk_E @ sk_C @ sk_B @ sk_A))
% 2.52/2.70         | (r2_funct_2 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.52/2.70            (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70            (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70            (k10_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ sk_C @ 
% 2.52/2.70             (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70              (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70              (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70             (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70              (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.70              (sk_E @ sk_C @ sk_B @ sk_A))))
% 2.52/2.70         | ~ (l1_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70         | ~ (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))))
% 2.52/2.70         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['345', '363'])).
% 2.52/2.70  thf('365', plain,
% 2.52/2.70      ((((v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70         | ~ (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70         | ~ (l1_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70         | (r2_funct_2 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.52/2.70            (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70            (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70            (k10_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ sk_C @ 
% 2.52/2.70             (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70              (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70              (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70             (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70              (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.70              (sk_E @ sk_C @ sk_B @ sk_A))))
% 2.52/2.70         | ~ (v1_funct_1 @ (sk_E @ sk_C @ sk_B @ sk_A))
% 2.52/2.70         | (v2_struct_0 @ sk_A)
% 2.52/2.70         | (v2_struct_0 @ sk_C)
% 2.52/2.70         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('simplify', [status(thm)], ['364'])).
% 2.52/2.70  thf('366', plain,
% 2.52/2.70      ((((v2_struct_0 @ sk_B)
% 2.52/2.70         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70         | (v2_struct_0 @ sk_C)
% 2.52/2.70         | (v2_struct_0 @ sk_A)
% 2.52/2.70         | (v2_struct_0 @ sk_B)
% 2.52/2.70         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70         | (v2_struct_0 @ sk_C)
% 2.52/2.70         | (v2_struct_0 @ sk_A)
% 2.52/2.70         | ~ (v1_funct_1 @ (sk_E @ sk_C @ sk_B @ sk_A))
% 2.52/2.70         | (r2_funct_2 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.52/2.70            (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70            (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70            (k10_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ sk_C @ 
% 2.52/2.70             (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70              (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70              (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70             (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70              (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.70              (sk_E @ sk_C @ sk_B @ sk_A))))
% 2.52/2.70         | ~ (l1_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))))
% 2.52/2.70         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['335', '365'])).
% 2.52/2.70  thf('367', plain,
% 2.52/2.70      ((((v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70         | ~ (l1_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70         | (r2_funct_2 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.52/2.70            (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70            (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70            (k10_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ sk_C @ 
% 2.52/2.70             (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70              (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70              (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70             (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70              (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.70              (sk_E @ sk_C @ sk_B @ sk_A))))
% 2.52/2.70         | ~ (v1_funct_1 @ (sk_E @ sk_C @ sk_B @ sk_A))
% 2.52/2.70         | (v2_struct_0 @ sk_A)
% 2.52/2.70         | (v2_struct_0 @ sk_C)
% 2.52/2.70         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('simplify', [status(thm)], ['366'])).
% 2.52/2.70  thf('368', plain,
% 2.52/2.70      ((((v2_struct_0 @ sk_B)
% 2.52/2.70         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70         | (v2_struct_0 @ sk_C)
% 2.52/2.70         | (v2_struct_0 @ sk_A)
% 2.52/2.70         | (v2_struct_0 @ sk_B)
% 2.52/2.70         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70         | (v2_struct_0 @ sk_C)
% 2.52/2.70         | (v2_struct_0 @ sk_A)
% 2.52/2.70         | ~ (v1_funct_1 @ (sk_E @ sk_C @ sk_B @ sk_A))
% 2.52/2.70         | (r2_funct_2 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.52/2.70            (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70            (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70            (k10_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ sk_C @ 
% 2.52/2.70             (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70              (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70              (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70             (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70              (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.70              (sk_E @ sk_C @ sk_B @ sk_A))))
% 2.52/2.70         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))))
% 2.52/2.70         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('sup-', [status(thm)], ['334', '367'])).
% 2.52/2.70  thf('369', plain,
% 2.52/2.70      ((((v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.70         | (r2_funct_2 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.52/2.70            (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70            (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70            (k10_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ sk_C @ 
% 2.52/2.70             (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70              (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.70              (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70             (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70              (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.70              (sk_E @ sk_C @ sk_B @ sk_A))))
% 2.52/2.70         | ~ (v1_funct_1 @ (sk_E @ sk_C @ sk_B @ sk_A))
% 2.52/2.70         | (v2_struct_0 @ sk_A)
% 2.52/2.70         | (v2_struct_0 @ sk_C)
% 2.52/2.70         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.70      inference('simplify', [status(thm)], ['368'])).
% 2.52/2.70  thf('370', plain,
% 2.52/2.70      ((((v2_struct_0 @ sk_B)
% 2.52/2.70         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70         | (v2_struct_0 @ sk_C)
% 2.52/2.70         | (v2_struct_0 @ sk_A)
% 2.52/2.70         | (v2_struct_0 @ sk_B)
% 2.52/2.70         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.70         | (v2_struct_0 @ sk_C)
% 2.52/2.70         | (v2_struct_0 @ sk_A)
% 2.52/2.70         | (r2_funct_2 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.52/2.70            (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.70            (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.70            (k10_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ sk_C @ 
% 2.52/2.70             (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71              (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.71              (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.71             (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71              (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.71              (sk_E @ sk_C @ sk_B @ sk_A))))
% 2.52/2.71         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))))
% 2.52/2.71         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.71      inference('sup-', [status(thm)], ['333', '369'])).
% 2.52/2.71  thf('371', plain,
% 2.52/2.71      ((((v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.71         | (r2_funct_2 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.52/2.71            (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.71            (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71            (k10_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ sk_C @ 
% 2.52/2.71             (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71              (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.71              (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.71             (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71              (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.71              (sk_E @ sk_C @ sk_B @ sk_A))))
% 2.52/2.71         | (v2_struct_0 @ sk_A)
% 2.52/2.71         | (v2_struct_0 @ sk_C)
% 2.52/2.71         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.71         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.71      inference('simplify', [status(thm)], ['370'])).
% 2.52/2.71  thf('372', plain,
% 2.52/2.71      ((((v2_struct_0 @ sk_A)
% 2.52/2.71         | (v2_struct_0 @ sk_C)
% 2.52/2.71         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.71         | (v1_funct_1 @ (sk_E @ sk_C @ sk_B @ sk_A))
% 2.52/2.71         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.71      inference('sup-', [status(thm)], ['155', '163'])).
% 2.52/2.71  thf('373', plain,
% 2.52/2.71      ((((v2_struct_0 @ sk_A)
% 2.52/2.71         | (v2_struct_0 @ sk_C)
% 2.52/2.71         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.71         | (v1_funct_2 @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71            (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.52/2.71            (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.71         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.71      inference('sup-', [status(thm)], ['336', '344'])).
% 2.52/2.71  thf('374', plain,
% 2.52/2.71      ((((v2_struct_0 @ sk_A)
% 2.52/2.71         | (v2_struct_0 @ sk_C)
% 2.52/2.71         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.71         | (m1_subset_1 @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71            (k1_zfmisc_1 @ 
% 2.52/2.71             (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.52/2.71              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.52/2.71         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.71      inference('sup-', [status(thm)], ['346', '354'])).
% 2.52/2.71  thf(redefinition_r2_funct_2, axiom,
% 2.52/2.71    (![A:$i,B:$i,C:$i,D:$i]:
% 2.52/2.71     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.52/2.71         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.52/2.71         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 2.52/2.71         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.52/2.71       ( ( r2_funct_2 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 2.52/2.71  thf('375', plain,
% 2.52/2.71      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.52/2.71         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 2.52/2.71          | ~ (v1_funct_2 @ X0 @ X1 @ X2)
% 2.52/2.71          | ~ (v1_funct_1 @ X0)
% 2.52/2.71          | ~ (v1_funct_1 @ X3)
% 2.52/2.71          | ~ (v1_funct_2 @ X3 @ X1 @ X2)
% 2.52/2.71          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 2.52/2.71          | ((X0) = (X3))
% 2.52/2.71          | ~ (r2_funct_2 @ X1 @ X2 @ X0 @ X3))),
% 2.52/2.71      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 2.52/2.71  thf('376', plain,
% 2.52/2.71      ((![X0 : $i]:
% 2.52/2.71          ((v2_struct_0 @ sk_B)
% 2.52/2.71           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.71           | (v2_struct_0 @ sk_C)
% 2.52/2.71           | (v2_struct_0 @ sk_A)
% 2.52/2.71           | ~ (r2_funct_2 @ 
% 2.52/2.71                (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.52/2.71                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.71                (sk_E @ sk_C @ sk_B @ sk_A) @ X0)
% 2.52/2.71           | ((sk_E @ sk_C @ sk_B @ sk_A) = (X0))
% 2.52/2.71           | ~ (m1_subset_1 @ X0 @ 
% 2.52/2.71                (k1_zfmisc_1 @ 
% 2.52/2.71                 (k2_zfmisc_1 @ 
% 2.52/2.71                  (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.52/2.71                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.52/2.71           | ~ (v1_funct_2 @ X0 @ 
% 2.52/2.71                (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.52/2.71                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.71           | ~ (v1_funct_1 @ X0)
% 2.52/2.71           | ~ (v1_funct_1 @ (sk_E @ sk_C @ sk_B @ sk_A))
% 2.52/2.71           | ~ (v1_funct_2 @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71                (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.52/2.71                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.52/2.71         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.71      inference('sup-', [status(thm)], ['374', '375'])).
% 2.52/2.71  thf('377', plain,
% 2.52/2.71      ((![X0 : $i]:
% 2.52/2.71          ((v2_struct_0 @ sk_B)
% 2.52/2.71           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.71           | (v2_struct_0 @ sk_C)
% 2.52/2.71           | (v2_struct_0 @ sk_A)
% 2.52/2.71           | ~ (v1_funct_1 @ (sk_E @ sk_C @ sk_B @ sk_A))
% 2.52/2.71           | ~ (v1_funct_1 @ X0)
% 2.52/2.71           | ~ (v1_funct_2 @ X0 @ 
% 2.52/2.71                (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.52/2.71                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.71           | ~ (m1_subset_1 @ X0 @ 
% 2.52/2.71                (k1_zfmisc_1 @ 
% 2.52/2.71                 (k2_zfmisc_1 @ 
% 2.52/2.71                  (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.52/2.71                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.52/2.71           | ((sk_E @ sk_C @ sk_B @ sk_A) = (X0))
% 2.52/2.71           | ~ (r2_funct_2 @ 
% 2.52/2.71                (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.52/2.71                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.71                (sk_E @ sk_C @ sk_B @ sk_A) @ X0)
% 2.52/2.71           | (v2_struct_0 @ sk_A)
% 2.52/2.71           | (v2_struct_0 @ sk_C)
% 2.52/2.71           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.71           | (v2_struct_0 @ sk_B)))
% 2.52/2.71         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.71      inference('sup-', [status(thm)], ['373', '376'])).
% 2.52/2.71  thf('378', plain,
% 2.52/2.71      ((![X0 : $i]:
% 2.52/2.71          (~ (r2_funct_2 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.52/2.71              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.71              (sk_E @ sk_C @ sk_B @ sk_A) @ X0)
% 2.52/2.71           | ((sk_E @ sk_C @ sk_B @ sk_A) = (X0))
% 2.52/2.71           | ~ (m1_subset_1 @ X0 @ 
% 2.52/2.71                (k1_zfmisc_1 @ 
% 2.52/2.71                 (k2_zfmisc_1 @ 
% 2.52/2.71                  (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.52/2.71                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.52/2.71           | ~ (v1_funct_2 @ X0 @ 
% 2.52/2.71                (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.52/2.71                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.71           | ~ (v1_funct_1 @ X0)
% 2.52/2.71           | ~ (v1_funct_1 @ (sk_E @ sk_C @ sk_B @ sk_A))
% 2.52/2.71           | (v2_struct_0 @ sk_A)
% 2.52/2.71           | (v2_struct_0 @ sk_C)
% 2.52/2.71           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.71           | (v2_struct_0 @ sk_B)))
% 2.52/2.71         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.71      inference('simplify', [status(thm)], ['377'])).
% 2.52/2.71  thf('379', plain,
% 2.52/2.71      ((![X0 : $i]:
% 2.52/2.71          ((v2_struct_0 @ sk_B)
% 2.52/2.71           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.71           | (v2_struct_0 @ sk_C)
% 2.52/2.71           | (v2_struct_0 @ sk_A)
% 2.52/2.71           | (v2_struct_0 @ sk_B)
% 2.52/2.71           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.71           | (v2_struct_0 @ sk_C)
% 2.52/2.71           | (v2_struct_0 @ sk_A)
% 2.52/2.71           | ~ (v1_funct_1 @ X0)
% 2.52/2.71           | ~ (v1_funct_2 @ X0 @ 
% 2.52/2.71                (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.52/2.71                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.71           | ~ (m1_subset_1 @ X0 @ 
% 2.52/2.71                (k1_zfmisc_1 @ 
% 2.52/2.71                 (k2_zfmisc_1 @ 
% 2.52/2.71                  (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.52/2.71                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.52/2.71           | ((sk_E @ sk_C @ sk_B @ sk_A) = (X0))
% 2.52/2.71           | ~ (r2_funct_2 @ 
% 2.52/2.71                (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.52/2.71                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.71                (sk_E @ sk_C @ sk_B @ sk_A) @ X0)))
% 2.52/2.71         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.71      inference('sup-', [status(thm)], ['372', '378'])).
% 2.52/2.71  thf('380', plain,
% 2.52/2.71      ((![X0 : $i]:
% 2.52/2.71          (~ (r2_funct_2 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.52/2.71              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.71              (sk_E @ sk_C @ sk_B @ sk_A) @ X0)
% 2.52/2.71           | ((sk_E @ sk_C @ sk_B @ sk_A) = (X0))
% 2.52/2.71           | ~ (m1_subset_1 @ X0 @ 
% 2.52/2.71                (k1_zfmisc_1 @ 
% 2.52/2.71                 (k2_zfmisc_1 @ 
% 2.52/2.71                  (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.52/2.71                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.52/2.71           | ~ (v1_funct_2 @ X0 @ 
% 2.52/2.71                (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.52/2.71                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.71           | ~ (v1_funct_1 @ X0)
% 2.52/2.71           | (v2_struct_0 @ sk_A)
% 2.52/2.71           | (v2_struct_0 @ sk_C)
% 2.52/2.71           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.71           | (v2_struct_0 @ sk_B)))
% 2.52/2.71         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.71      inference('simplify', [status(thm)], ['379'])).
% 2.52/2.71  thf('381', plain,
% 2.52/2.71      ((((v2_struct_0 @ sk_B)
% 2.52/2.71         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.71         | (v2_struct_0 @ sk_C)
% 2.52/2.71         | (v2_struct_0 @ sk_A)
% 2.52/2.71         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.71         | (v2_struct_0 @ sk_B)
% 2.52/2.71         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.71         | (v2_struct_0 @ sk_C)
% 2.52/2.71         | (v2_struct_0 @ sk_A)
% 2.52/2.71         | ~ (v1_funct_1 @ 
% 2.52/2.71              (k10_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ sk_C @ 
% 2.52/2.71               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.71                (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.71               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.71                (sk_E @ sk_C @ sk_B @ sk_A))))
% 2.52/2.71         | ~ (v1_funct_2 @ 
% 2.52/2.71              (k10_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ sk_C @ 
% 2.52/2.71               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.71                (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.71               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.71                (sk_E @ sk_C @ sk_B @ sk_A))) @ 
% 2.52/2.71              (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.52/2.71              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.71         | ~ (m1_subset_1 @ 
% 2.52/2.71              (k10_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ sk_C @ 
% 2.52/2.71               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.71                (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.71               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.71                (sk_E @ sk_C @ sk_B @ sk_A))) @ 
% 2.52/2.71              (k1_zfmisc_1 @ 
% 2.52/2.71               (k2_zfmisc_1 @ 
% 2.52/2.71                (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.52/2.71                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.52/2.71         | ((sk_E @ sk_C @ sk_B @ sk_A)
% 2.52/2.71             = (k10_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ 
% 2.52/2.71                sk_C @ 
% 2.52/2.71                (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71                 (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.71                 (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.71                (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71                 (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.71                 (sk_E @ sk_C @ sk_B @ sk_A))))))
% 2.52/2.71         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.71      inference('sup-', [status(thm)], ['371', '380'])).
% 2.52/2.71  thf('382', plain,
% 2.52/2.71      (((((sk_E @ sk_C @ sk_B @ sk_A)
% 2.52/2.71           = (k10_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ sk_C @ 
% 2.52/2.71              (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71               (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.71               (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.71              (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71               (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.71               (sk_E @ sk_C @ sk_B @ sk_A))))
% 2.52/2.71         | ~ (m1_subset_1 @ 
% 2.52/2.71              (k10_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ sk_C @ 
% 2.52/2.71               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.71                (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.71               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.71                (sk_E @ sk_C @ sk_B @ sk_A))) @ 
% 2.52/2.71              (k1_zfmisc_1 @ 
% 2.52/2.71               (k2_zfmisc_1 @ 
% 2.52/2.71                (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.52/2.71                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.52/2.71         | ~ (v1_funct_2 @ 
% 2.52/2.71              (k10_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ sk_C @ 
% 2.52/2.71               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.71                (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.71               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.71                (sk_E @ sk_C @ sk_B @ sk_A))) @ 
% 2.52/2.71              (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.52/2.71              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.71         | ~ (v1_funct_1 @ 
% 2.52/2.71              (k10_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ sk_C @ 
% 2.52/2.71               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.71                (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.71               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.71                (sk_E @ sk_C @ sk_B @ sk_A))))
% 2.52/2.71         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.71         | (v2_struct_0 @ sk_A)
% 2.52/2.71         | (v2_struct_0 @ sk_C)
% 2.52/2.71         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.71         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.71      inference('simplify', [status(thm)], ['381'])).
% 2.52/2.71  thf('383', plain,
% 2.52/2.71      ((((v2_struct_0 @ sk_B)
% 2.52/2.71         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.71         | (v2_struct_0 @ sk_C)
% 2.52/2.71         | (v2_struct_0 @ sk_A)
% 2.52/2.71         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.71         | (v2_struct_0 @ sk_B)
% 2.52/2.71         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.71         | (v2_struct_0 @ sk_C)
% 2.52/2.71         | (v2_struct_0 @ sk_A)
% 2.52/2.71         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.71         | ~ (v1_funct_1 @ 
% 2.52/2.71              (k10_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ sk_C @ 
% 2.52/2.71               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.71                (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.71               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.71                (sk_E @ sk_C @ sk_B @ sk_A))))
% 2.52/2.71         | ~ (v1_funct_2 @ 
% 2.52/2.71              (k10_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ sk_C @ 
% 2.52/2.71               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.71                (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.71               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.71                (sk_E @ sk_C @ sk_B @ sk_A))) @ 
% 2.52/2.71              (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.52/2.71              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.71         | ((sk_E @ sk_C @ sk_B @ sk_A)
% 2.52/2.71             = (k10_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ 
% 2.52/2.71                sk_C @ 
% 2.52/2.71                (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71                 (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.71                 (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.71                (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71                 (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.71                 (sk_E @ sk_C @ sk_B @ sk_A))))))
% 2.52/2.71         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.71      inference('sup-', [status(thm)], ['332', '382'])).
% 2.52/2.71  thf('384', plain,
% 2.52/2.71      (((((sk_E @ sk_C @ sk_B @ sk_A)
% 2.52/2.71           = (k10_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ sk_C @ 
% 2.52/2.71              (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71               (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.71               (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.71              (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71               (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.71               (sk_E @ sk_C @ sk_B @ sk_A))))
% 2.52/2.71         | ~ (v1_funct_2 @ 
% 2.52/2.71              (k10_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ sk_C @ 
% 2.52/2.71               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.71                (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.71               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.71                (sk_E @ sk_C @ sk_B @ sk_A))) @ 
% 2.52/2.71              (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.52/2.71              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.71         | ~ (v1_funct_1 @ 
% 2.52/2.71              (k10_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ sk_C @ 
% 2.52/2.71               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.71                (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.71               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.71                (sk_E @ sk_C @ sk_B @ sk_A))))
% 2.52/2.71         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.71         | (v2_struct_0 @ sk_A)
% 2.52/2.71         | (v2_struct_0 @ sk_C)
% 2.52/2.71         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.71         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.71      inference('simplify', [status(thm)], ['383'])).
% 2.52/2.71  thf('385', plain,
% 2.52/2.71      ((((v2_struct_0 @ sk_B)
% 2.52/2.71         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.71         | (v2_struct_0 @ sk_C)
% 2.52/2.71         | (v2_struct_0 @ sk_A)
% 2.52/2.71         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.71         | (v2_struct_0 @ sk_B)
% 2.52/2.71         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.71         | (v2_struct_0 @ sk_C)
% 2.52/2.71         | (v2_struct_0 @ sk_A)
% 2.52/2.71         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.71         | ~ (v1_funct_1 @ 
% 2.52/2.71              (k10_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ sk_C @ 
% 2.52/2.71               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.71                (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.71               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.71                (sk_E @ sk_C @ sk_B @ sk_A))))
% 2.52/2.71         | ((sk_E @ sk_C @ sk_B @ sk_A)
% 2.52/2.71             = (k10_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ 
% 2.52/2.71                sk_C @ 
% 2.52/2.71                (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71                 (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.71                 (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.71                (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71                 (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.71                 (sk_E @ sk_C @ sk_B @ sk_A))))))
% 2.52/2.71         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.71      inference('sup-', [status(thm)], ['300', '384'])).
% 2.52/2.71  thf('386', plain,
% 2.52/2.71      (((((sk_E @ sk_C @ sk_B @ sk_A)
% 2.52/2.71           = (k10_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ sk_C @ 
% 2.52/2.71              (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71               (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.71               (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.71              (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71               (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.71               (sk_E @ sk_C @ sk_B @ sk_A))))
% 2.52/2.71         | ~ (v1_funct_1 @ 
% 2.52/2.71              (k10_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ sk_C @ 
% 2.52/2.71               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.71                (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.71               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.71                (sk_E @ sk_C @ sk_B @ sk_A))))
% 2.52/2.71         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.71         | (v2_struct_0 @ sk_A)
% 2.52/2.71         | (v2_struct_0 @ sk_C)
% 2.52/2.71         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.71         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.71      inference('simplify', [status(thm)], ['385'])).
% 2.52/2.71  thf('387', plain,
% 2.52/2.71      ((((v2_struct_0 @ sk_B)
% 2.52/2.71         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.71         | (v2_struct_0 @ sk_C)
% 2.52/2.71         | (v2_struct_0 @ sk_A)
% 2.52/2.71         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.71         | (v2_struct_0 @ sk_B)
% 2.52/2.71         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.71         | (v2_struct_0 @ sk_C)
% 2.52/2.71         | (v2_struct_0 @ sk_A)
% 2.52/2.71         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.71         | ((sk_E @ sk_C @ sk_B @ sk_A)
% 2.52/2.71             = (k10_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ 
% 2.52/2.71                sk_C @ 
% 2.52/2.71                (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71                 (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.71                 (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.71                (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71                 (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.71                 (sk_E @ sk_C @ sk_B @ sk_A))))))
% 2.52/2.71         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.71      inference('sup-', [status(thm)], ['268', '386'])).
% 2.52/2.71  thf('388', plain,
% 2.52/2.71      (((((sk_E @ sk_C @ sk_B @ sk_A)
% 2.52/2.71           = (k10_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ sk_C @ 
% 2.52/2.71              (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71               (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.71               (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.71              (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71               (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.71               (sk_E @ sk_C @ sk_B @ sk_A))))
% 2.52/2.71         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.71         | (v2_struct_0 @ sk_A)
% 2.52/2.71         | (v2_struct_0 @ sk_C)
% 2.52/2.71         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.71         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.71      inference('simplify', [status(thm)], ['387'])).
% 2.52/2.71  thf('389', plain,
% 2.52/2.71      ((((v2_struct_0 @ sk_A)
% 2.52/2.71         | (v2_struct_0 @ sk_C)
% 2.52/2.71         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.71         | (v1_funct_1 @ 
% 2.52/2.71            (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71             (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.71             (sk_E @ sk_C @ sk_B @ sk_A)))
% 2.52/2.71         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.71      inference('sup-', [status(thm)], ['216', '224'])).
% 2.52/2.71  thf('390', plain,
% 2.52/2.71      (((r1_tsep_1 @ sk_B @ sk_C)) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.71      inference('split', [status(esa)], ['0'])).
% 2.52/2.71  thf('391', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 2.52/2.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.71  thf('392', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 2.52/2.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.71  thf('393', plain,
% 2.52/2.71      (![X10 : $i, X11 : $i, X12 : $i]:
% 2.52/2.71         ((v2_struct_0 @ X10)
% 2.52/2.71          | ~ (m1_pre_topc @ X10 @ X11)
% 2.52/2.71          | ~ (r1_tsep_1 @ X10 @ X12)
% 2.52/2.71          | (v5_pre_topc @ 
% 2.52/2.71             (k3_tmap_1 @ X11 @ (sk_D @ X12 @ X10 @ X11) @ 
% 2.52/2.71              (k1_tsep_1 @ X11 @ X10 @ X12) @ X10 @ (sk_E @ X12 @ X10 @ X11)) @ 
% 2.52/2.71             X10 @ (sk_D @ X12 @ X10 @ X11))
% 2.52/2.71          | (r3_tsep_1 @ X11 @ X10 @ X12)
% 2.52/2.71          | ~ (m1_pre_topc @ X12 @ X11)
% 2.52/2.71          | (v2_struct_0 @ X12)
% 2.52/2.71          | ~ (l1_pre_topc @ X11)
% 2.52/2.71          | ~ (v2_pre_topc @ X11)
% 2.52/2.71          | (v2_struct_0 @ X11))),
% 2.52/2.71      inference('cnf', [status(esa)], [t135_tmap_1])).
% 2.52/2.71  thf('394', plain,
% 2.52/2.71      (![X0 : $i]:
% 2.52/2.71         ((v2_struct_0 @ sk_A)
% 2.52/2.71          | ~ (v2_pre_topc @ sk_A)
% 2.52/2.71          | ~ (l1_pre_topc @ sk_A)
% 2.52/2.71          | (v2_struct_0 @ X0)
% 2.52/2.71          | ~ (m1_pre_topc @ X0 @ sk_A)
% 2.52/2.71          | (r3_tsep_1 @ sk_A @ sk_B @ X0)
% 2.52/2.71          | (v5_pre_topc @ 
% 2.52/2.71             (k3_tmap_1 @ sk_A @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 2.52/2.71              (k1_tsep_1 @ sk_A @ sk_B @ X0) @ sk_B @ (sk_E @ X0 @ sk_B @ sk_A)) @ 
% 2.52/2.71             sk_B @ (sk_D @ X0 @ sk_B @ sk_A))
% 2.52/2.71          | ~ (r1_tsep_1 @ sk_B @ X0)
% 2.52/2.71          | (v2_struct_0 @ sk_B))),
% 2.52/2.71      inference('sup-', [status(thm)], ['392', '393'])).
% 2.52/2.71  thf('395', plain, ((v2_pre_topc @ sk_A)),
% 2.52/2.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.71  thf('396', plain, ((l1_pre_topc @ sk_A)),
% 2.52/2.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.71  thf('397', plain,
% 2.52/2.71      (![X0 : $i]:
% 2.52/2.71         ((v2_struct_0 @ sk_A)
% 2.52/2.71          | (v2_struct_0 @ X0)
% 2.52/2.71          | ~ (m1_pre_topc @ X0 @ sk_A)
% 2.52/2.71          | (r3_tsep_1 @ sk_A @ sk_B @ X0)
% 2.52/2.71          | (v5_pre_topc @ 
% 2.52/2.71             (k3_tmap_1 @ sk_A @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 2.52/2.71              (k1_tsep_1 @ sk_A @ sk_B @ X0) @ sk_B @ (sk_E @ X0 @ sk_B @ sk_A)) @ 
% 2.52/2.71             sk_B @ (sk_D @ X0 @ sk_B @ sk_A))
% 2.52/2.71          | ~ (r1_tsep_1 @ sk_B @ X0)
% 2.52/2.71          | (v2_struct_0 @ sk_B))),
% 2.52/2.71      inference('demod', [status(thm)], ['394', '395', '396'])).
% 2.52/2.71  thf('398', plain,
% 2.52/2.71      (((v2_struct_0 @ sk_B)
% 2.52/2.71        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 2.52/2.71        | (v5_pre_topc @ 
% 2.52/2.71           (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71            (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.71            (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.71           sk_B @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.71        | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.71        | (v2_struct_0 @ sk_C)
% 2.52/2.71        | (v2_struct_0 @ sk_A))),
% 2.52/2.71      inference('sup-', [status(thm)], ['391', '397'])).
% 2.52/2.71  thf('399', plain,
% 2.52/2.71      ((((v2_struct_0 @ sk_A)
% 2.52/2.71         | (v2_struct_0 @ sk_C)
% 2.52/2.71         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.71         | (v5_pre_topc @ 
% 2.52/2.71            (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71             (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.71             (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.71            sk_B @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.71         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.71      inference('sup-', [status(thm)], ['390', '398'])).
% 2.52/2.71  thf('400', plain,
% 2.52/2.71      ((((v2_struct_0 @ sk_A)
% 2.52/2.71         | (v2_struct_0 @ sk_C)
% 2.52/2.71         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.71         | (v1_funct_2 @ 
% 2.52/2.71            (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71             (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.71             (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.71            (u1_struct_0 @ sk_B) @ (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.71         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.71      inference('sup-', [status(thm)], ['226', '234'])).
% 2.52/2.71  thf('401', plain,
% 2.52/2.71      ((((v2_struct_0 @ sk_A)
% 2.52/2.71         | (v2_struct_0 @ sk_C)
% 2.52/2.71         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.71         | (m1_subset_1 @ 
% 2.52/2.71            (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71             (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.71             (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.71            (k1_zfmisc_1 @ 
% 2.52/2.71             (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.52/2.71         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.71      inference('sup-', [status(thm)], ['236', '244'])).
% 2.52/2.71  thf('402', plain,
% 2.52/2.71      ((((v2_struct_0 @ sk_A)
% 2.52/2.71         | (v2_struct_0 @ sk_C)
% 2.52/2.71         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.71         | (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.71         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.71      inference('sup-', [status(thm)], ['196', '204'])).
% 2.52/2.71  thf('403', plain,
% 2.52/2.71      ((((v2_struct_0 @ sk_A)
% 2.52/2.71         | (v2_struct_0 @ sk_C)
% 2.52/2.71         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.71         | (l1_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.71         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.71      inference('sup-', [status(thm)], ['206', '214'])).
% 2.52/2.71  thf('404', plain,
% 2.52/2.71      ((((v2_struct_0 @ sk_A)
% 2.52/2.71         | (v2_struct_0 @ sk_C)
% 2.52/2.71         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.71         | (v1_funct_1 @ 
% 2.52/2.71            (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71             (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.71             (sk_E @ sk_C @ sk_B @ sk_A)))
% 2.52/2.71         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.71      inference('sup-', [status(thm)], ['166', '174'])).
% 2.52/2.71  thf('405', plain,
% 2.52/2.71      (((r1_tsep_1 @ sk_B @ sk_C)) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.71      inference('split', [status(esa)], ['0'])).
% 2.52/2.71  thf('406', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 2.52/2.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.71  thf('407', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 2.52/2.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.71  thf('408', plain,
% 2.52/2.71      (![X10 : $i, X11 : $i, X12 : $i]:
% 2.52/2.71         ((v2_struct_0 @ X10)
% 2.52/2.71          | ~ (m1_pre_topc @ X10 @ X11)
% 2.52/2.71          | ~ (r1_tsep_1 @ X10 @ X12)
% 2.52/2.71          | (v5_pre_topc @ 
% 2.52/2.71             (k3_tmap_1 @ X11 @ (sk_D @ X12 @ X10 @ X11) @ 
% 2.52/2.71              (k1_tsep_1 @ X11 @ X10 @ X12) @ X12 @ (sk_E @ X12 @ X10 @ X11)) @ 
% 2.52/2.71             X12 @ (sk_D @ X12 @ X10 @ X11))
% 2.52/2.71          | (r3_tsep_1 @ X11 @ X10 @ X12)
% 2.52/2.71          | ~ (m1_pre_topc @ X12 @ X11)
% 2.52/2.71          | (v2_struct_0 @ X12)
% 2.52/2.71          | ~ (l1_pre_topc @ X11)
% 2.52/2.71          | ~ (v2_pre_topc @ X11)
% 2.52/2.71          | (v2_struct_0 @ X11))),
% 2.52/2.71      inference('cnf', [status(esa)], [t135_tmap_1])).
% 2.52/2.71  thf('409', plain,
% 2.52/2.71      (![X0 : $i]:
% 2.52/2.71         ((v2_struct_0 @ sk_A)
% 2.52/2.71          | ~ (v2_pre_topc @ sk_A)
% 2.52/2.71          | ~ (l1_pre_topc @ sk_A)
% 2.52/2.71          | (v2_struct_0 @ X0)
% 2.52/2.71          | ~ (m1_pre_topc @ X0 @ sk_A)
% 2.52/2.71          | (r3_tsep_1 @ sk_A @ sk_B @ X0)
% 2.52/2.71          | (v5_pre_topc @ 
% 2.52/2.71             (k3_tmap_1 @ sk_A @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 2.52/2.71              (k1_tsep_1 @ sk_A @ sk_B @ X0) @ X0 @ (sk_E @ X0 @ sk_B @ sk_A)) @ 
% 2.52/2.71             X0 @ (sk_D @ X0 @ sk_B @ sk_A))
% 2.52/2.71          | ~ (r1_tsep_1 @ sk_B @ X0)
% 2.52/2.71          | (v2_struct_0 @ sk_B))),
% 2.52/2.71      inference('sup-', [status(thm)], ['407', '408'])).
% 2.52/2.71  thf('410', plain, ((v2_pre_topc @ sk_A)),
% 2.52/2.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.71  thf('411', plain, ((l1_pre_topc @ sk_A)),
% 2.52/2.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.71  thf('412', plain,
% 2.52/2.71      (![X0 : $i]:
% 2.52/2.71         ((v2_struct_0 @ sk_A)
% 2.52/2.71          | (v2_struct_0 @ X0)
% 2.52/2.71          | ~ (m1_pre_topc @ X0 @ sk_A)
% 2.52/2.71          | (r3_tsep_1 @ sk_A @ sk_B @ X0)
% 2.52/2.71          | (v5_pre_topc @ 
% 2.52/2.71             (k3_tmap_1 @ sk_A @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 2.52/2.71              (k1_tsep_1 @ sk_A @ sk_B @ X0) @ X0 @ (sk_E @ X0 @ sk_B @ sk_A)) @ 
% 2.52/2.71             X0 @ (sk_D @ X0 @ sk_B @ sk_A))
% 2.52/2.71          | ~ (r1_tsep_1 @ sk_B @ X0)
% 2.52/2.71          | (v2_struct_0 @ sk_B))),
% 2.52/2.71      inference('demod', [status(thm)], ['409', '410', '411'])).
% 2.52/2.71  thf('413', plain,
% 2.52/2.71      (((v2_struct_0 @ sk_B)
% 2.52/2.71        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 2.52/2.71        | (v5_pre_topc @ 
% 2.52/2.71           (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71            (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.71            (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.71           sk_C @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.71        | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.71        | (v2_struct_0 @ sk_C)
% 2.52/2.71        | (v2_struct_0 @ sk_A))),
% 2.52/2.71      inference('sup-', [status(thm)], ['406', '412'])).
% 2.52/2.71  thf('414', plain,
% 2.52/2.71      ((((v2_struct_0 @ sk_A)
% 2.52/2.71         | (v2_struct_0 @ sk_C)
% 2.52/2.71         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.71         | (v5_pre_topc @ 
% 2.52/2.71            (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71             (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.71             (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.71            sk_C @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.71         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.71      inference('sup-', [status(thm)], ['405', '413'])).
% 2.52/2.71  thf('415', plain,
% 2.52/2.71      ((((v2_struct_0 @ sk_A)
% 2.52/2.71         | (v2_struct_0 @ sk_C)
% 2.52/2.71         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.71         | (v1_funct_2 @ 
% 2.52/2.71            (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71             (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.71             (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.71            (u1_struct_0 @ sk_C) @ (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.71         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.71      inference('sup-', [status(thm)], ['176', '184'])).
% 2.52/2.71  thf('416', plain,
% 2.52/2.71      ((((v2_struct_0 @ sk_A)
% 2.52/2.71         | (v2_struct_0 @ sk_C)
% 2.52/2.71         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.71         | (m1_subset_1 @ 
% 2.52/2.71            (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71             (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.71             (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.71            (k1_zfmisc_1 @ 
% 2.52/2.71             (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.71              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.52/2.71         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.71      inference('sup-', [status(thm)], ['186', '194'])).
% 2.52/2.71  thf('417', plain,
% 2.52/2.71      (![X29 : $i, X30 : $i, X31 : $i]:
% 2.52/2.71         ((v2_struct_0 @ X29)
% 2.52/2.71          | ~ (v2_pre_topc @ X29)
% 2.52/2.71          | ~ (l1_pre_topc @ X29)
% 2.52/2.71          | ~ (v1_funct_1 @ X30)
% 2.52/2.71          | ~ (v1_funct_2 @ X30 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X29))
% 2.52/2.71          | ~ (v5_pre_topc @ X30 @ sk_C @ X29)
% 2.52/2.71          | ~ (m1_subset_1 @ X30 @ 
% 2.52/2.71               (k1_zfmisc_1 @ 
% 2.52/2.71                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X29))))
% 2.52/2.71          | (v5_pre_topc @ 
% 2.52/2.71             (k10_tmap_1 @ sk_A @ X29 @ sk_B @ sk_C @ X31 @ X30) @ 
% 2.52/2.71             (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ X29)
% 2.52/2.71          | ~ (m1_subset_1 @ X31 @ 
% 2.52/2.71               (k1_zfmisc_1 @ 
% 2.52/2.71                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X29))))
% 2.52/2.71          | ~ (v5_pre_topc @ X31 @ sk_B @ X29)
% 2.52/2.71          | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X29))
% 2.52/2.71          | ~ (v1_funct_1 @ X31)
% 2.52/2.71          | (r3_tsep_1 @ sk_A @ sk_B @ sk_C))),
% 2.52/2.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.71  thf('418', plain,
% 2.52/2.71      ((![X29 : $i, X30 : $i, X31 : $i]:
% 2.52/2.71          ((v2_struct_0 @ X29)
% 2.52/2.71           | ~ (v2_pre_topc @ X29)
% 2.52/2.71           | ~ (l1_pre_topc @ X29)
% 2.52/2.71           | ~ (v1_funct_1 @ X30)
% 2.52/2.71           | ~ (v1_funct_2 @ X30 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X29))
% 2.52/2.71           | ~ (v5_pre_topc @ X30 @ sk_C @ X29)
% 2.52/2.71           | ~ (m1_subset_1 @ X30 @ 
% 2.52/2.71                (k1_zfmisc_1 @ 
% 2.52/2.71                 (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X29))))
% 2.52/2.71           | ~ (m1_subset_1 @ X31 @ 
% 2.52/2.71                (k1_zfmisc_1 @ 
% 2.52/2.71                 (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X29))))
% 2.52/2.71           | ~ (v5_pre_topc @ X31 @ sk_B @ X29)
% 2.52/2.71           | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X29))
% 2.52/2.71           | ~ (v1_funct_1 @ X31)
% 2.52/2.71           | (v5_pre_topc @ 
% 2.52/2.71              (k10_tmap_1 @ sk_A @ X29 @ sk_B @ sk_C @ X31 @ X30) @ 
% 2.52/2.71              (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ X29)))
% 2.52/2.71         <= ((![X29 : $i, X30 : $i, X31 : $i]:
% 2.52/2.71                ((v2_struct_0 @ X29)
% 2.52/2.71                 | ~ (v2_pre_topc @ X29)
% 2.52/2.71                 | ~ (l1_pre_topc @ X29)
% 2.52/2.71                 | ~ (v1_funct_1 @ X30)
% 2.52/2.71                 | ~ (v1_funct_2 @ X30 @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.71                      (u1_struct_0 @ X29))
% 2.52/2.71                 | ~ (v5_pre_topc @ X30 @ sk_C @ X29)
% 2.52/2.71                 | ~ (m1_subset_1 @ X30 @ 
% 2.52/2.71                      (k1_zfmisc_1 @ 
% 2.52/2.71                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.71                        (u1_struct_0 @ X29))))
% 2.52/2.71                 | ~ (m1_subset_1 @ X31 @ 
% 2.52/2.71                      (k1_zfmisc_1 @ 
% 2.52/2.71                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71                        (u1_struct_0 @ X29))))
% 2.52/2.71                 | ~ (v5_pre_topc @ X31 @ sk_B @ X29)
% 2.52/2.71                 | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71                      (u1_struct_0 @ X29))
% 2.52/2.71                 | ~ (v1_funct_1 @ X31)
% 2.52/2.71                 | (v5_pre_topc @ 
% 2.52/2.71                    (k10_tmap_1 @ sk_A @ X29 @ sk_B @ sk_C @ X31 @ X30) @ 
% 2.52/2.71                    (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ X29))))),
% 2.52/2.71      inference('split', [status(esa)], ['417'])).
% 2.52/2.71  thf('419', plain,
% 2.52/2.71      ((![X0 : $i]:
% 2.52/2.71          ((v2_struct_0 @ sk_B)
% 2.52/2.71           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.71           | (v2_struct_0 @ sk_C)
% 2.52/2.71           | (v2_struct_0 @ sk_A)
% 2.52/2.71           | (v5_pre_topc @ 
% 2.52/2.71              (k10_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ sk_C @ 
% 2.52/2.71               X0 @ 
% 2.52/2.71               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.71                (sk_E @ sk_C @ sk_B @ sk_A))) @ 
% 2.52/2.71              (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.71           | ~ (v1_funct_1 @ X0)
% 2.52/2.71           | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.71           | ~ (v5_pre_topc @ X0 @ sk_B @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.71           | ~ (m1_subset_1 @ X0 @ 
% 2.52/2.71                (k1_zfmisc_1 @ 
% 2.52/2.71                 (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.52/2.71           | ~ (v5_pre_topc @ 
% 2.52/2.71                (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71                 (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.71                 (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.71                sk_C @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.71           | ~ (v1_funct_2 @ 
% 2.52/2.71                (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71                 (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.71                 (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.71                (u1_struct_0 @ sk_C) @ 
% 2.52/2.71                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.71           | ~ (v1_funct_1 @ 
% 2.52/2.71                (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71                 (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.71                 (sk_E @ sk_C @ sk_B @ sk_A)))
% 2.52/2.71           | ~ (l1_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.71           | ~ (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.71           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))))
% 2.52/2.71         <= (((r1_tsep_1 @ sk_B @ sk_C)) & 
% 2.52/2.71             (![X29 : $i, X30 : $i, X31 : $i]:
% 2.52/2.71                ((v2_struct_0 @ X29)
% 2.52/2.71                 | ~ (v2_pre_topc @ X29)
% 2.52/2.71                 | ~ (l1_pre_topc @ X29)
% 2.52/2.71                 | ~ (v1_funct_1 @ X30)
% 2.52/2.71                 | ~ (v1_funct_2 @ X30 @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.71                      (u1_struct_0 @ X29))
% 2.52/2.71                 | ~ (v5_pre_topc @ X30 @ sk_C @ X29)
% 2.52/2.71                 | ~ (m1_subset_1 @ X30 @ 
% 2.52/2.71                      (k1_zfmisc_1 @ 
% 2.52/2.71                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.71                        (u1_struct_0 @ X29))))
% 2.52/2.71                 | ~ (m1_subset_1 @ X31 @ 
% 2.52/2.71                      (k1_zfmisc_1 @ 
% 2.52/2.71                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71                        (u1_struct_0 @ X29))))
% 2.52/2.71                 | ~ (v5_pre_topc @ X31 @ sk_B @ X29)
% 2.52/2.71                 | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71                      (u1_struct_0 @ X29))
% 2.52/2.71                 | ~ (v1_funct_1 @ X31)
% 2.52/2.71                 | (v5_pre_topc @ 
% 2.52/2.71                    (k10_tmap_1 @ sk_A @ X29 @ sk_B @ sk_C @ X31 @ X30) @ 
% 2.52/2.71                    (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ X29))))),
% 2.52/2.71      inference('sup-', [status(thm)], ['416', '418'])).
% 2.52/2.71  thf('420', plain,
% 2.52/2.71      ((![X0 : $i]:
% 2.52/2.71          ((v2_struct_0 @ sk_B)
% 2.52/2.71           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.71           | (v2_struct_0 @ sk_C)
% 2.52/2.71           | (v2_struct_0 @ sk_A)
% 2.52/2.71           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.71           | ~ (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.71           | ~ (l1_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.71           | ~ (v1_funct_1 @ 
% 2.52/2.71                (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71                 (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.71                 (sk_E @ sk_C @ sk_B @ sk_A)))
% 2.52/2.71           | ~ (v5_pre_topc @ 
% 2.52/2.71                (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71                 (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.71                 (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.71                sk_C @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.71           | ~ (m1_subset_1 @ X0 @ 
% 2.52/2.71                (k1_zfmisc_1 @ 
% 2.52/2.71                 (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.52/2.71           | ~ (v5_pre_topc @ X0 @ sk_B @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.71           | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.71           | ~ (v1_funct_1 @ X0)
% 2.52/2.71           | (v5_pre_topc @ 
% 2.52/2.71              (k10_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ sk_C @ 
% 2.52/2.71               X0 @ 
% 2.52/2.71               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.71                (sk_E @ sk_C @ sk_B @ sk_A))) @ 
% 2.52/2.71              (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.71           | (v2_struct_0 @ sk_A)
% 2.52/2.71           | (v2_struct_0 @ sk_C)
% 2.52/2.71           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.71           | (v2_struct_0 @ sk_B)))
% 2.52/2.71         <= (((r1_tsep_1 @ sk_B @ sk_C)) & 
% 2.52/2.71             (![X29 : $i, X30 : $i, X31 : $i]:
% 2.52/2.71                ((v2_struct_0 @ X29)
% 2.52/2.71                 | ~ (v2_pre_topc @ X29)
% 2.52/2.71                 | ~ (l1_pre_topc @ X29)
% 2.52/2.71                 | ~ (v1_funct_1 @ X30)
% 2.52/2.71                 | ~ (v1_funct_2 @ X30 @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.71                      (u1_struct_0 @ X29))
% 2.52/2.71                 | ~ (v5_pre_topc @ X30 @ sk_C @ X29)
% 2.52/2.71                 | ~ (m1_subset_1 @ X30 @ 
% 2.52/2.71                      (k1_zfmisc_1 @ 
% 2.52/2.71                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.71                        (u1_struct_0 @ X29))))
% 2.52/2.71                 | ~ (m1_subset_1 @ X31 @ 
% 2.52/2.71                      (k1_zfmisc_1 @ 
% 2.52/2.71                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71                        (u1_struct_0 @ X29))))
% 2.52/2.71                 | ~ (v5_pre_topc @ X31 @ sk_B @ X29)
% 2.52/2.71                 | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71                      (u1_struct_0 @ X29))
% 2.52/2.71                 | ~ (v1_funct_1 @ X31)
% 2.52/2.71                 | (v5_pre_topc @ 
% 2.52/2.71                    (k10_tmap_1 @ sk_A @ X29 @ sk_B @ sk_C @ X31 @ X30) @ 
% 2.52/2.71                    (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ X29))))),
% 2.52/2.71      inference('sup-', [status(thm)], ['415', '419'])).
% 2.52/2.71  thf('421', plain,
% 2.52/2.71      ((![X0 : $i]:
% 2.52/2.71          ((v5_pre_topc @ 
% 2.52/2.71            (k10_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ sk_C @ 
% 2.52/2.71             X0 @ 
% 2.52/2.71             (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71              (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.71              (sk_E @ sk_C @ sk_B @ sk_A))) @ 
% 2.52/2.71            (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.71           | ~ (v1_funct_1 @ X0)
% 2.52/2.71           | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.71           | ~ (v5_pre_topc @ X0 @ sk_B @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.71           | ~ (m1_subset_1 @ X0 @ 
% 2.52/2.71                (k1_zfmisc_1 @ 
% 2.52/2.71                 (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.52/2.71           | ~ (v5_pre_topc @ 
% 2.52/2.71                (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71                 (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.71                 (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.71                sk_C @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.71           | ~ (v1_funct_1 @ 
% 2.52/2.71                (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71                 (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.71                 (sk_E @ sk_C @ sk_B @ sk_A)))
% 2.52/2.71           | ~ (l1_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.71           | ~ (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.71           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.71           | (v2_struct_0 @ sk_A)
% 2.52/2.71           | (v2_struct_0 @ sk_C)
% 2.52/2.71           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.71           | (v2_struct_0 @ sk_B)))
% 2.52/2.71         <= (((r1_tsep_1 @ sk_B @ sk_C)) & 
% 2.52/2.71             (![X29 : $i, X30 : $i, X31 : $i]:
% 2.52/2.71                ((v2_struct_0 @ X29)
% 2.52/2.71                 | ~ (v2_pre_topc @ X29)
% 2.52/2.71                 | ~ (l1_pre_topc @ X29)
% 2.52/2.71                 | ~ (v1_funct_1 @ X30)
% 2.52/2.71                 | ~ (v1_funct_2 @ X30 @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.71                      (u1_struct_0 @ X29))
% 2.52/2.71                 | ~ (v5_pre_topc @ X30 @ sk_C @ X29)
% 2.52/2.71                 | ~ (m1_subset_1 @ X30 @ 
% 2.52/2.71                      (k1_zfmisc_1 @ 
% 2.52/2.71                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.71                        (u1_struct_0 @ X29))))
% 2.52/2.71                 | ~ (m1_subset_1 @ X31 @ 
% 2.52/2.71                      (k1_zfmisc_1 @ 
% 2.52/2.71                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71                        (u1_struct_0 @ X29))))
% 2.52/2.71                 | ~ (v5_pre_topc @ X31 @ sk_B @ X29)
% 2.52/2.71                 | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71                      (u1_struct_0 @ X29))
% 2.52/2.71                 | ~ (v1_funct_1 @ X31)
% 2.52/2.71                 | (v5_pre_topc @ 
% 2.52/2.71                    (k10_tmap_1 @ sk_A @ X29 @ sk_B @ sk_C @ X31 @ X30) @ 
% 2.52/2.71                    (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ X29))))),
% 2.52/2.71      inference('simplify', [status(thm)], ['420'])).
% 2.52/2.71  thf('422', plain,
% 2.52/2.71      ((![X0 : $i]:
% 2.52/2.71          ((v2_struct_0 @ sk_B)
% 2.52/2.71           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.71           | (v2_struct_0 @ sk_C)
% 2.52/2.71           | (v2_struct_0 @ sk_A)
% 2.52/2.71           | (v2_struct_0 @ sk_B)
% 2.52/2.71           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.71           | (v2_struct_0 @ sk_C)
% 2.52/2.71           | (v2_struct_0 @ sk_A)
% 2.52/2.71           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.71           | ~ (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.71           | ~ (l1_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.71           | ~ (v1_funct_1 @ 
% 2.52/2.71                (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71                 (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.71                 (sk_E @ sk_C @ sk_B @ sk_A)))
% 2.52/2.71           | ~ (m1_subset_1 @ X0 @ 
% 2.52/2.71                (k1_zfmisc_1 @ 
% 2.52/2.71                 (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.52/2.71           | ~ (v5_pre_topc @ X0 @ sk_B @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.71           | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.71           | ~ (v1_funct_1 @ X0)
% 2.52/2.71           | (v5_pre_topc @ 
% 2.52/2.71              (k10_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ sk_C @ 
% 2.52/2.71               X0 @ 
% 2.52/2.71               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.71                (sk_E @ sk_C @ sk_B @ sk_A))) @ 
% 2.52/2.71              (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ (sk_D @ sk_C @ sk_B @ sk_A))))
% 2.52/2.71         <= (((r1_tsep_1 @ sk_B @ sk_C)) & 
% 2.52/2.71             (![X29 : $i, X30 : $i, X31 : $i]:
% 2.52/2.71                ((v2_struct_0 @ X29)
% 2.52/2.71                 | ~ (v2_pre_topc @ X29)
% 2.52/2.71                 | ~ (l1_pre_topc @ X29)
% 2.52/2.71                 | ~ (v1_funct_1 @ X30)
% 2.52/2.71                 | ~ (v1_funct_2 @ X30 @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.71                      (u1_struct_0 @ X29))
% 2.52/2.71                 | ~ (v5_pre_topc @ X30 @ sk_C @ X29)
% 2.52/2.71                 | ~ (m1_subset_1 @ X30 @ 
% 2.52/2.71                      (k1_zfmisc_1 @ 
% 2.52/2.71                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.71                        (u1_struct_0 @ X29))))
% 2.52/2.71                 | ~ (m1_subset_1 @ X31 @ 
% 2.52/2.71                      (k1_zfmisc_1 @ 
% 2.52/2.71                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71                        (u1_struct_0 @ X29))))
% 2.52/2.71                 | ~ (v5_pre_topc @ X31 @ sk_B @ X29)
% 2.52/2.71                 | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71                      (u1_struct_0 @ X29))
% 2.52/2.71                 | ~ (v1_funct_1 @ X31)
% 2.52/2.71                 | (v5_pre_topc @ 
% 2.52/2.71                    (k10_tmap_1 @ sk_A @ X29 @ sk_B @ sk_C @ X31 @ X30) @ 
% 2.52/2.71                    (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ X29))))),
% 2.52/2.71      inference('sup-', [status(thm)], ['414', '421'])).
% 2.52/2.71  thf('423', plain,
% 2.52/2.71      ((![X0 : $i]:
% 2.52/2.71          ((v5_pre_topc @ 
% 2.52/2.71            (k10_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ sk_C @ 
% 2.52/2.71             X0 @ 
% 2.52/2.71             (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71              (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.71              (sk_E @ sk_C @ sk_B @ sk_A))) @ 
% 2.52/2.71            (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.71           | ~ (v1_funct_1 @ X0)
% 2.52/2.71           | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.71           | ~ (v5_pre_topc @ X0 @ sk_B @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.71           | ~ (m1_subset_1 @ X0 @ 
% 2.52/2.71                (k1_zfmisc_1 @ 
% 2.52/2.71                 (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.52/2.71           | ~ (v1_funct_1 @ 
% 2.52/2.71                (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71                 (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.71                 (sk_E @ sk_C @ sk_B @ sk_A)))
% 2.52/2.71           | ~ (l1_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.71           | ~ (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.71           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.71           | (v2_struct_0 @ sk_A)
% 2.52/2.71           | (v2_struct_0 @ sk_C)
% 2.52/2.71           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.71           | (v2_struct_0 @ sk_B)))
% 2.52/2.71         <= (((r1_tsep_1 @ sk_B @ sk_C)) & 
% 2.52/2.71             (![X29 : $i, X30 : $i, X31 : $i]:
% 2.52/2.71                ((v2_struct_0 @ X29)
% 2.52/2.71                 | ~ (v2_pre_topc @ X29)
% 2.52/2.71                 | ~ (l1_pre_topc @ X29)
% 2.52/2.71                 | ~ (v1_funct_1 @ X30)
% 2.52/2.71                 | ~ (v1_funct_2 @ X30 @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.71                      (u1_struct_0 @ X29))
% 2.52/2.71                 | ~ (v5_pre_topc @ X30 @ sk_C @ X29)
% 2.52/2.71                 | ~ (m1_subset_1 @ X30 @ 
% 2.52/2.71                      (k1_zfmisc_1 @ 
% 2.52/2.71                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.71                        (u1_struct_0 @ X29))))
% 2.52/2.71                 | ~ (m1_subset_1 @ X31 @ 
% 2.52/2.71                      (k1_zfmisc_1 @ 
% 2.52/2.71                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71                        (u1_struct_0 @ X29))))
% 2.52/2.71                 | ~ (v5_pre_topc @ X31 @ sk_B @ X29)
% 2.52/2.71                 | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71                      (u1_struct_0 @ X29))
% 2.52/2.71                 | ~ (v1_funct_1 @ X31)
% 2.52/2.71                 | (v5_pre_topc @ 
% 2.52/2.71                    (k10_tmap_1 @ sk_A @ X29 @ sk_B @ sk_C @ X31 @ X30) @ 
% 2.52/2.71                    (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ X29))))),
% 2.52/2.71      inference('simplify', [status(thm)], ['422'])).
% 2.52/2.71  thf('424', plain,
% 2.52/2.71      ((![X0 : $i]:
% 2.52/2.71          ((v2_struct_0 @ sk_B)
% 2.52/2.71           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.71           | (v2_struct_0 @ sk_C)
% 2.52/2.71           | (v2_struct_0 @ sk_A)
% 2.52/2.71           | (v2_struct_0 @ sk_B)
% 2.52/2.71           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.71           | (v2_struct_0 @ sk_C)
% 2.52/2.71           | (v2_struct_0 @ sk_A)
% 2.52/2.71           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.71           | ~ (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.71           | ~ (l1_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.71           | ~ (m1_subset_1 @ X0 @ 
% 2.52/2.71                (k1_zfmisc_1 @ 
% 2.52/2.71                 (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.52/2.71           | ~ (v5_pre_topc @ X0 @ sk_B @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.71           | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.71           | ~ (v1_funct_1 @ X0)
% 2.52/2.71           | (v5_pre_topc @ 
% 2.52/2.71              (k10_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ sk_C @ 
% 2.52/2.71               X0 @ 
% 2.52/2.71               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.71                (sk_E @ sk_C @ sk_B @ sk_A))) @ 
% 2.52/2.71              (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ (sk_D @ sk_C @ sk_B @ sk_A))))
% 2.52/2.71         <= (((r1_tsep_1 @ sk_B @ sk_C)) & 
% 2.52/2.71             (![X29 : $i, X30 : $i, X31 : $i]:
% 2.52/2.71                ((v2_struct_0 @ X29)
% 2.52/2.71                 | ~ (v2_pre_topc @ X29)
% 2.52/2.71                 | ~ (l1_pre_topc @ X29)
% 2.52/2.71                 | ~ (v1_funct_1 @ X30)
% 2.52/2.71                 | ~ (v1_funct_2 @ X30 @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.71                      (u1_struct_0 @ X29))
% 2.52/2.71                 | ~ (v5_pre_topc @ X30 @ sk_C @ X29)
% 2.52/2.71                 | ~ (m1_subset_1 @ X30 @ 
% 2.52/2.71                      (k1_zfmisc_1 @ 
% 2.52/2.71                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.71                        (u1_struct_0 @ X29))))
% 2.52/2.71                 | ~ (m1_subset_1 @ X31 @ 
% 2.52/2.71                      (k1_zfmisc_1 @ 
% 2.52/2.71                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71                        (u1_struct_0 @ X29))))
% 2.52/2.71                 | ~ (v5_pre_topc @ X31 @ sk_B @ X29)
% 2.52/2.71                 | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71                      (u1_struct_0 @ X29))
% 2.52/2.71                 | ~ (v1_funct_1 @ X31)
% 2.52/2.71                 | (v5_pre_topc @ 
% 2.52/2.71                    (k10_tmap_1 @ sk_A @ X29 @ sk_B @ sk_C @ X31 @ X30) @ 
% 2.52/2.71                    (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ X29))))),
% 2.52/2.71      inference('sup-', [status(thm)], ['404', '423'])).
% 2.52/2.71  thf('425', plain,
% 2.52/2.71      ((![X0 : $i]:
% 2.52/2.71          ((v5_pre_topc @ 
% 2.52/2.71            (k10_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ sk_C @ 
% 2.52/2.71             X0 @ 
% 2.52/2.71             (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71              (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.71              (sk_E @ sk_C @ sk_B @ sk_A))) @ 
% 2.52/2.71            (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.71           | ~ (v1_funct_1 @ X0)
% 2.52/2.71           | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.71           | ~ (v5_pre_topc @ X0 @ sk_B @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.71           | ~ (m1_subset_1 @ X0 @ 
% 2.52/2.71                (k1_zfmisc_1 @ 
% 2.52/2.71                 (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.52/2.71           | ~ (l1_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.71           | ~ (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.71           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.71           | (v2_struct_0 @ sk_A)
% 2.52/2.71           | (v2_struct_0 @ sk_C)
% 2.52/2.71           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.71           | (v2_struct_0 @ sk_B)))
% 2.52/2.71         <= (((r1_tsep_1 @ sk_B @ sk_C)) & 
% 2.52/2.71             (![X29 : $i, X30 : $i, X31 : $i]:
% 2.52/2.71                ((v2_struct_0 @ X29)
% 2.52/2.71                 | ~ (v2_pre_topc @ X29)
% 2.52/2.71                 | ~ (l1_pre_topc @ X29)
% 2.52/2.71                 | ~ (v1_funct_1 @ X30)
% 2.52/2.71                 | ~ (v1_funct_2 @ X30 @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.71                      (u1_struct_0 @ X29))
% 2.52/2.71                 | ~ (v5_pre_topc @ X30 @ sk_C @ X29)
% 2.52/2.71                 | ~ (m1_subset_1 @ X30 @ 
% 2.52/2.71                      (k1_zfmisc_1 @ 
% 2.52/2.71                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.71                        (u1_struct_0 @ X29))))
% 2.52/2.71                 | ~ (m1_subset_1 @ X31 @ 
% 2.52/2.71                      (k1_zfmisc_1 @ 
% 2.52/2.71                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71                        (u1_struct_0 @ X29))))
% 2.52/2.71                 | ~ (v5_pre_topc @ X31 @ sk_B @ X29)
% 2.52/2.71                 | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71                      (u1_struct_0 @ X29))
% 2.52/2.71                 | ~ (v1_funct_1 @ X31)
% 2.52/2.71                 | (v5_pre_topc @ 
% 2.52/2.71                    (k10_tmap_1 @ sk_A @ X29 @ sk_B @ sk_C @ X31 @ X30) @ 
% 2.52/2.71                    (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ X29))))),
% 2.52/2.71      inference('simplify', [status(thm)], ['424'])).
% 2.52/2.71  thf('426', plain,
% 2.52/2.71      ((![X0 : $i]:
% 2.52/2.71          ((v2_struct_0 @ sk_B)
% 2.52/2.71           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.71           | (v2_struct_0 @ sk_C)
% 2.52/2.71           | (v2_struct_0 @ sk_A)
% 2.52/2.71           | (v2_struct_0 @ sk_B)
% 2.52/2.71           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.71           | (v2_struct_0 @ sk_C)
% 2.52/2.71           | (v2_struct_0 @ sk_A)
% 2.52/2.71           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.71           | ~ (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.71           | ~ (m1_subset_1 @ X0 @ 
% 2.52/2.71                (k1_zfmisc_1 @ 
% 2.52/2.71                 (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.52/2.71           | ~ (v5_pre_topc @ X0 @ sk_B @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.71           | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.71           | ~ (v1_funct_1 @ X0)
% 2.52/2.71           | (v5_pre_topc @ 
% 2.52/2.71              (k10_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ sk_C @ 
% 2.52/2.71               X0 @ 
% 2.52/2.71               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.71                (sk_E @ sk_C @ sk_B @ sk_A))) @ 
% 2.52/2.71              (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ (sk_D @ sk_C @ sk_B @ sk_A))))
% 2.52/2.71         <= (((r1_tsep_1 @ sk_B @ sk_C)) & 
% 2.52/2.71             (![X29 : $i, X30 : $i, X31 : $i]:
% 2.52/2.71                ((v2_struct_0 @ X29)
% 2.52/2.71                 | ~ (v2_pre_topc @ X29)
% 2.52/2.71                 | ~ (l1_pre_topc @ X29)
% 2.52/2.71                 | ~ (v1_funct_1 @ X30)
% 2.52/2.71                 | ~ (v1_funct_2 @ X30 @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.71                      (u1_struct_0 @ X29))
% 2.52/2.71                 | ~ (v5_pre_topc @ X30 @ sk_C @ X29)
% 2.52/2.71                 | ~ (m1_subset_1 @ X30 @ 
% 2.52/2.71                      (k1_zfmisc_1 @ 
% 2.52/2.71                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.71                        (u1_struct_0 @ X29))))
% 2.52/2.71                 | ~ (m1_subset_1 @ X31 @ 
% 2.52/2.71                      (k1_zfmisc_1 @ 
% 2.52/2.71                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71                        (u1_struct_0 @ X29))))
% 2.52/2.71                 | ~ (v5_pre_topc @ X31 @ sk_B @ X29)
% 2.52/2.71                 | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71                      (u1_struct_0 @ X29))
% 2.52/2.71                 | ~ (v1_funct_1 @ X31)
% 2.52/2.71                 | (v5_pre_topc @ 
% 2.52/2.71                    (k10_tmap_1 @ sk_A @ X29 @ sk_B @ sk_C @ X31 @ X30) @ 
% 2.52/2.71                    (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ X29))))),
% 2.52/2.71      inference('sup-', [status(thm)], ['403', '425'])).
% 2.52/2.71  thf('427', plain,
% 2.52/2.71      ((![X0 : $i]:
% 2.52/2.71          ((v5_pre_topc @ 
% 2.52/2.71            (k10_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ sk_C @ 
% 2.52/2.71             X0 @ 
% 2.52/2.71             (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71              (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.71              (sk_E @ sk_C @ sk_B @ sk_A))) @ 
% 2.52/2.71            (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.71           | ~ (v1_funct_1 @ X0)
% 2.52/2.71           | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.71           | ~ (v5_pre_topc @ X0 @ sk_B @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.71           | ~ (m1_subset_1 @ X0 @ 
% 2.52/2.71                (k1_zfmisc_1 @ 
% 2.52/2.71                 (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.52/2.71           | ~ (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.71           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.71           | (v2_struct_0 @ sk_A)
% 2.52/2.71           | (v2_struct_0 @ sk_C)
% 2.52/2.71           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.71           | (v2_struct_0 @ sk_B)))
% 2.52/2.71         <= (((r1_tsep_1 @ sk_B @ sk_C)) & 
% 2.52/2.71             (![X29 : $i, X30 : $i, X31 : $i]:
% 2.52/2.71                ((v2_struct_0 @ X29)
% 2.52/2.71                 | ~ (v2_pre_topc @ X29)
% 2.52/2.71                 | ~ (l1_pre_topc @ X29)
% 2.52/2.71                 | ~ (v1_funct_1 @ X30)
% 2.52/2.71                 | ~ (v1_funct_2 @ X30 @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.71                      (u1_struct_0 @ X29))
% 2.52/2.71                 | ~ (v5_pre_topc @ X30 @ sk_C @ X29)
% 2.52/2.71                 | ~ (m1_subset_1 @ X30 @ 
% 2.52/2.71                      (k1_zfmisc_1 @ 
% 2.52/2.71                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.71                        (u1_struct_0 @ X29))))
% 2.52/2.71                 | ~ (m1_subset_1 @ X31 @ 
% 2.52/2.71                      (k1_zfmisc_1 @ 
% 2.52/2.71                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71                        (u1_struct_0 @ X29))))
% 2.52/2.71                 | ~ (v5_pre_topc @ X31 @ sk_B @ X29)
% 2.52/2.71                 | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71                      (u1_struct_0 @ X29))
% 2.52/2.71                 | ~ (v1_funct_1 @ X31)
% 2.52/2.71                 | (v5_pre_topc @ 
% 2.52/2.71                    (k10_tmap_1 @ sk_A @ X29 @ sk_B @ sk_C @ X31 @ X30) @ 
% 2.52/2.71                    (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ X29))))),
% 2.52/2.71      inference('simplify', [status(thm)], ['426'])).
% 2.52/2.71  thf('428', plain,
% 2.52/2.71      ((![X0 : $i]:
% 2.52/2.71          ((v2_struct_0 @ sk_B)
% 2.52/2.71           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.71           | (v2_struct_0 @ sk_C)
% 2.52/2.71           | (v2_struct_0 @ sk_A)
% 2.52/2.71           | (v2_struct_0 @ sk_B)
% 2.52/2.71           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.71           | (v2_struct_0 @ sk_C)
% 2.52/2.71           | (v2_struct_0 @ sk_A)
% 2.52/2.71           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.71           | ~ (m1_subset_1 @ X0 @ 
% 2.52/2.71                (k1_zfmisc_1 @ 
% 2.52/2.71                 (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.52/2.71           | ~ (v5_pre_topc @ X0 @ sk_B @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.71           | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.71           | ~ (v1_funct_1 @ X0)
% 2.52/2.71           | (v5_pre_topc @ 
% 2.52/2.71              (k10_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ sk_C @ 
% 2.52/2.71               X0 @ 
% 2.52/2.71               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.71                (sk_E @ sk_C @ sk_B @ sk_A))) @ 
% 2.52/2.71              (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ (sk_D @ sk_C @ sk_B @ sk_A))))
% 2.52/2.71         <= (((r1_tsep_1 @ sk_B @ sk_C)) & 
% 2.52/2.71             (![X29 : $i, X30 : $i, X31 : $i]:
% 2.52/2.71                ((v2_struct_0 @ X29)
% 2.52/2.71                 | ~ (v2_pre_topc @ X29)
% 2.52/2.71                 | ~ (l1_pre_topc @ X29)
% 2.52/2.71                 | ~ (v1_funct_1 @ X30)
% 2.52/2.71                 | ~ (v1_funct_2 @ X30 @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.71                      (u1_struct_0 @ X29))
% 2.52/2.71                 | ~ (v5_pre_topc @ X30 @ sk_C @ X29)
% 2.52/2.71                 | ~ (m1_subset_1 @ X30 @ 
% 2.52/2.71                      (k1_zfmisc_1 @ 
% 2.52/2.71                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.71                        (u1_struct_0 @ X29))))
% 2.52/2.71                 | ~ (m1_subset_1 @ X31 @ 
% 2.52/2.71                      (k1_zfmisc_1 @ 
% 2.52/2.71                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71                        (u1_struct_0 @ X29))))
% 2.52/2.71                 | ~ (v5_pre_topc @ X31 @ sk_B @ X29)
% 2.52/2.71                 | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71                      (u1_struct_0 @ X29))
% 2.52/2.71                 | ~ (v1_funct_1 @ X31)
% 2.52/2.71                 | (v5_pre_topc @ 
% 2.52/2.71                    (k10_tmap_1 @ sk_A @ X29 @ sk_B @ sk_C @ X31 @ X30) @ 
% 2.52/2.71                    (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ X29))))),
% 2.52/2.71      inference('sup-', [status(thm)], ['402', '427'])).
% 2.52/2.71  thf('429', plain,
% 2.52/2.71      ((![X0 : $i]:
% 2.52/2.71          ((v5_pre_topc @ 
% 2.52/2.71            (k10_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ sk_C @ 
% 2.52/2.71             X0 @ 
% 2.52/2.71             (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71              (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.71              (sk_E @ sk_C @ sk_B @ sk_A))) @ 
% 2.52/2.71            (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.71           | ~ (v1_funct_1 @ X0)
% 2.52/2.71           | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.71           | ~ (v5_pre_topc @ X0 @ sk_B @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.71           | ~ (m1_subset_1 @ X0 @ 
% 2.52/2.71                (k1_zfmisc_1 @ 
% 2.52/2.71                 (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.52/2.71           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.71           | (v2_struct_0 @ sk_A)
% 2.52/2.71           | (v2_struct_0 @ sk_C)
% 2.52/2.71           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.71           | (v2_struct_0 @ sk_B)))
% 2.52/2.71         <= (((r1_tsep_1 @ sk_B @ sk_C)) & 
% 2.52/2.71             (![X29 : $i, X30 : $i, X31 : $i]:
% 2.52/2.71                ((v2_struct_0 @ X29)
% 2.52/2.71                 | ~ (v2_pre_topc @ X29)
% 2.52/2.71                 | ~ (l1_pre_topc @ X29)
% 2.52/2.71                 | ~ (v1_funct_1 @ X30)
% 2.52/2.71                 | ~ (v1_funct_2 @ X30 @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.71                      (u1_struct_0 @ X29))
% 2.52/2.71                 | ~ (v5_pre_topc @ X30 @ sk_C @ X29)
% 2.52/2.71                 | ~ (m1_subset_1 @ X30 @ 
% 2.52/2.71                      (k1_zfmisc_1 @ 
% 2.52/2.71                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.71                        (u1_struct_0 @ X29))))
% 2.52/2.71                 | ~ (m1_subset_1 @ X31 @ 
% 2.52/2.71                      (k1_zfmisc_1 @ 
% 2.52/2.71                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71                        (u1_struct_0 @ X29))))
% 2.52/2.71                 | ~ (v5_pre_topc @ X31 @ sk_B @ X29)
% 2.52/2.71                 | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71                      (u1_struct_0 @ X29))
% 2.52/2.71                 | ~ (v1_funct_1 @ X31)
% 2.52/2.71                 | (v5_pre_topc @ 
% 2.52/2.71                    (k10_tmap_1 @ sk_A @ X29 @ sk_B @ sk_C @ X31 @ X30) @ 
% 2.52/2.71                    (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ X29))))),
% 2.52/2.71      inference('simplify', [status(thm)], ['428'])).
% 2.52/2.71  thf('430', plain,
% 2.52/2.71      ((((v2_struct_0 @ sk_B)
% 2.52/2.71         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.71         | (v2_struct_0 @ sk_C)
% 2.52/2.71         | (v2_struct_0 @ sk_A)
% 2.52/2.71         | (v2_struct_0 @ sk_B)
% 2.52/2.71         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.71         | (v2_struct_0 @ sk_C)
% 2.52/2.71         | (v2_struct_0 @ sk_A)
% 2.52/2.71         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.71         | ~ (v5_pre_topc @ 
% 2.52/2.71              (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71               (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.71               (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.71              sk_B @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.71         | ~ (v1_funct_2 @ 
% 2.52/2.71              (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71               (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.71               (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.71              (u1_struct_0 @ sk_B) @ 
% 2.52/2.71              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.71         | ~ (v1_funct_1 @ 
% 2.52/2.71              (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71               (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.71               (sk_E @ sk_C @ sk_B @ sk_A)))
% 2.52/2.71         | (v5_pre_topc @ 
% 2.52/2.71            (k10_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ sk_C @ 
% 2.52/2.71             (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71              (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.71              (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.71             (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71              (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.71              (sk_E @ sk_C @ sk_B @ sk_A))) @ 
% 2.52/2.71            (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ (sk_D @ sk_C @ sk_B @ sk_A))))
% 2.52/2.71         <= (((r1_tsep_1 @ sk_B @ sk_C)) & 
% 2.52/2.71             (![X29 : $i, X30 : $i, X31 : $i]:
% 2.52/2.71                ((v2_struct_0 @ X29)
% 2.52/2.71                 | ~ (v2_pre_topc @ X29)
% 2.52/2.71                 | ~ (l1_pre_topc @ X29)
% 2.52/2.71                 | ~ (v1_funct_1 @ X30)
% 2.52/2.71                 | ~ (v1_funct_2 @ X30 @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.71                      (u1_struct_0 @ X29))
% 2.52/2.71                 | ~ (v5_pre_topc @ X30 @ sk_C @ X29)
% 2.52/2.71                 | ~ (m1_subset_1 @ X30 @ 
% 2.52/2.71                      (k1_zfmisc_1 @ 
% 2.52/2.71                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.71                        (u1_struct_0 @ X29))))
% 2.52/2.71                 | ~ (m1_subset_1 @ X31 @ 
% 2.52/2.71                      (k1_zfmisc_1 @ 
% 2.52/2.71                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71                        (u1_struct_0 @ X29))))
% 2.52/2.71                 | ~ (v5_pre_topc @ X31 @ sk_B @ X29)
% 2.52/2.71                 | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71                      (u1_struct_0 @ X29))
% 2.52/2.71                 | ~ (v1_funct_1 @ X31)
% 2.52/2.71                 | (v5_pre_topc @ 
% 2.52/2.71                    (k10_tmap_1 @ sk_A @ X29 @ sk_B @ sk_C @ X31 @ X30) @ 
% 2.52/2.71                    (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ X29))))),
% 2.52/2.71      inference('sup-', [status(thm)], ['401', '429'])).
% 2.52/2.71  thf('431', plain,
% 2.52/2.71      ((((v5_pre_topc @ 
% 2.52/2.71          (k10_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ sk_C @ 
% 2.52/2.71           (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71            (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.71            (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.71           (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71            (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.71            (sk_E @ sk_C @ sk_B @ sk_A))) @ 
% 2.52/2.71          (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.71         | ~ (v1_funct_1 @ 
% 2.52/2.71              (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71               (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.71               (sk_E @ sk_C @ sk_B @ sk_A)))
% 2.52/2.71         | ~ (v1_funct_2 @ 
% 2.52/2.71              (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71               (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.71               (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.71              (u1_struct_0 @ sk_B) @ 
% 2.52/2.71              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.71         | ~ (v5_pre_topc @ 
% 2.52/2.71              (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71               (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.71               (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.71              sk_B @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.71         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.71         | (v2_struct_0 @ sk_A)
% 2.52/2.71         | (v2_struct_0 @ sk_C)
% 2.52/2.71         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.71         | (v2_struct_0 @ sk_B)))
% 2.52/2.71         <= (((r1_tsep_1 @ sk_B @ sk_C)) & 
% 2.52/2.71             (![X29 : $i, X30 : $i, X31 : $i]:
% 2.52/2.71                ((v2_struct_0 @ X29)
% 2.52/2.71                 | ~ (v2_pre_topc @ X29)
% 2.52/2.71                 | ~ (l1_pre_topc @ X29)
% 2.52/2.71                 | ~ (v1_funct_1 @ X30)
% 2.52/2.71                 | ~ (v1_funct_2 @ X30 @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.71                      (u1_struct_0 @ X29))
% 2.52/2.71                 | ~ (v5_pre_topc @ X30 @ sk_C @ X29)
% 2.52/2.71                 | ~ (m1_subset_1 @ X30 @ 
% 2.52/2.71                      (k1_zfmisc_1 @ 
% 2.52/2.71                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.71                        (u1_struct_0 @ X29))))
% 2.52/2.71                 | ~ (m1_subset_1 @ X31 @ 
% 2.52/2.71                      (k1_zfmisc_1 @ 
% 2.52/2.71                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71                        (u1_struct_0 @ X29))))
% 2.52/2.71                 | ~ (v5_pre_topc @ X31 @ sk_B @ X29)
% 2.52/2.71                 | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71                      (u1_struct_0 @ X29))
% 2.52/2.71                 | ~ (v1_funct_1 @ X31)
% 2.52/2.71                 | (v5_pre_topc @ 
% 2.52/2.71                    (k10_tmap_1 @ sk_A @ X29 @ sk_B @ sk_C @ X31 @ X30) @ 
% 2.52/2.71                    (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ X29))))),
% 2.52/2.71      inference('simplify', [status(thm)], ['430'])).
% 2.52/2.71  thf('432', plain,
% 2.52/2.71      ((((v2_struct_0 @ sk_B)
% 2.52/2.71         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.71         | (v2_struct_0 @ sk_C)
% 2.52/2.71         | (v2_struct_0 @ sk_A)
% 2.52/2.71         | (v2_struct_0 @ sk_B)
% 2.52/2.71         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.71         | (v2_struct_0 @ sk_C)
% 2.52/2.71         | (v2_struct_0 @ sk_A)
% 2.52/2.71         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.71         | ~ (v5_pre_topc @ 
% 2.52/2.71              (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71               (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.71               (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.71              sk_B @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.71         | ~ (v1_funct_1 @ 
% 2.52/2.71              (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71               (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.71               (sk_E @ sk_C @ sk_B @ sk_A)))
% 2.52/2.71         | (v5_pre_topc @ 
% 2.52/2.71            (k10_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ sk_C @ 
% 2.52/2.71             (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71              (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.71              (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.71             (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71              (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.71              (sk_E @ sk_C @ sk_B @ sk_A))) @ 
% 2.52/2.71            (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ (sk_D @ sk_C @ sk_B @ sk_A))))
% 2.52/2.71         <= (((r1_tsep_1 @ sk_B @ sk_C)) & 
% 2.52/2.71             (![X29 : $i, X30 : $i, X31 : $i]:
% 2.52/2.71                ((v2_struct_0 @ X29)
% 2.52/2.71                 | ~ (v2_pre_topc @ X29)
% 2.52/2.71                 | ~ (l1_pre_topc @ X29)
% 2.52/2.71                 | ~ (v1_funct_1 @ X30)
% 2.52/2.71                 | ~ (v1_funct_2 @ X30 @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.71                      (u1_struct_0 @ X29))
% 2.52/2.71                 | ~ (v5_pre_topc @ X30 @ sk_C @ X29)
% 2.52/2.71                 | ~ (m1_subset_1 @ X30 @ 
% 2.52/2.71                      (k1_zfmisc_1 @ 
% 2.52/2.71                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.71                        (u1_struct_0 @ X29))))
% 2.52/2.71                 | ~ (m1_subset_1 @ X31 @ 
% 2.52/2.71                      (k1_zfmisc_1 @ 
% 2.52/2.71                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71                        (u1_struct_0 @ X29))))
% 2.52/2.71                 | ~ (v5_pre_topc @ X31 @ sk_B @ X29)
% 2.52/2.71                 | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71                      (u1_struct_0 @ X29))
% 2.52/2.71                 | ~ (v1_funct_1 @ X31)
% 2.52/2.71                 | (v5_pre_topc @ 
% 2.52/2.71                    (k10_tmap_1 @ sk_A @ X29 @ sk_B @ sk_C @ X31 @ X30) @ 
% 2.52/2.71                    (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ X29))))),
% 2.52/2.71      inference('sup-', [status(thm)], ['400', '431'])).
% 2.52/2.71  thf('433', plain,
% 2.52/2.71      ((((v5_pre_topc @ 
% 2.52/2.71          (k10_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ sk_C @ 
% 2.52/2.71           (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71            (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.71            (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.71           (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71            (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.71            (sk_E @ sk_C @ sk_B @ sk_A))) @ 
% 2.52/2.71          (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.71         | ~ (v1_funct_1 @ 
% 2.52/2.71              (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71               (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.71               (sk_E @ sk_C @ sk_B @ sk_A)))
% 2.52/2.71         | ~ (v5_pre_topc @ 
% 2.52/2.71              (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71               (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.71               (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.71              sk_B @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.71         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.71         | (v2_struct_0 @ sk_A)
% 2.52/2.71         | (v2_struct_0 @ sk_C)
% 2.52/2.71         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.71         | (v2_struct_0 @ sk_B)))
% 2.52/2.71         <= (((r1_tsep_1 @ sk_B @ sk_C)) & 
% 2.52/2.71             (![X29 : $i, X30 : $i, X31 : $i]:
% 2.52/2.71                ((v2_struct_0 @ X29)
% 2.52/2.71                 | ~ (v2_pre_topc @ X29)
% 2.52/2.71                 | ~ (l1_pre_topc @ X29)
% 2.52/2.71                 | ~ (v1_funct_1 @ X30)
% 2.52/2.71                 | ~ (v1_funct_2 @ X30 @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.71                      (u1_struct_0 @ X29))
% 2.52/2.71                 | ~ (v5_pre_topc @ X30 @ sk_C @ X29)
% 2.52/2.71                 | ~ (m1_subset_1 @ X30 @ 
% 2.52/2.71                      (k1_zfmisc_1 @ 
% 2.52/2.71                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.71                        (u1_struct_0 @ X29))))
% 2.52/2.71                 | ~ (m1_subset_1 @ X31 @ 
% 2.52/2.71                      (k1_zfmisc_1 @ 
% 2.52/2.71                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71                        (u1_struct_0 @ X29))))
% 2.52/2.71                 | ~ (v5_pre_topc @ X31 @ sk_B @ X29)
% 2.52/2.71                 | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71                      (u1_struct_0 @ X29))
% 2.52/2.71                 | ~ (v1_funct_1 @ X31)
% 2.52/2.71                 | (v5_pre_topc @ 
% 2.52/2.71                    (k10_tmap_1 @ sk_A @ X29 @ sk_B @ sk_C @ X31 @ X30) @ 
% 2.52/2.71                    (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ X29))))),
% 2.52/2.71      inference('simplify', [status(thm)], ['432'])).
% 2.52/2.71  thf('434', plain,
% 2.52/2.71      ((((v2_struct_0 @ sk_B)
% 2.52/2.71         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.71         | (v2_struct_0 @ sk_C)
% 2.52/2.71         | (v2_struct_0 @ sk_A)
% 2.52/2.71         | (v2_struct_0 @ sk_B)
% 2.52/2.71         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.71         | (v2_struct_0 @ sk_C)
% 2.52/2.71         | (v2_struct_0 @ sk_A)
% 2.52/2.71         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.71         | ~ (v1_funct_1 @ 
% 2.52/2.71              (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71               (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.71               (sk_E @ sk_C @ sk_B @ sk_A)))
% 2.52/2.71         | (v5_pre_topc @ 
% 2.52/2.71            (k10_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ sk_C @ 
% 2.52/2.71             (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71              (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.71              (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.71             (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71              (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.71              (sk_E @ sk_C @ sk_B @ sk_A))) @ 
% 2.52/2.71            (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ (sk_D @ sk_C @ sk_B @ sk_A))))
% 2.52/2.71         <= (((r1_tsep_1 @ sk_B @ sk_C)) & 
% 2.52/2.71             (![X29 : $i, X30 : $i, X31 : $i]:
% 2.52/2.71                ((v2_struct_0 @ X29)
% 2.52/2.71                 | ~ (v2_pre_topc @ X29)
% 2.52/2.71                 | ~ (l1_pre_topc @ X29)
% 2.52/2.71                 | ~ (v1_funct_1 @ X30)
% 2.52/2.71                 | ~ (v1_funct_2 @ X30 @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.71                      (u1_struct_0 @ X29))
% 2.52/2.71                 | ~ (v5_pre_topc @ X30 @ sk_C @ X29)
% 2.52/2.71                 | ~ (m1_subset_1 @ X30 @ 
% 2.52/2.71                      (k1_zfmisc_1 @ 
% 2.52/2.71                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.71                        (u1_struct_0 @ X29))))
% 2.52/2.71                 | ~ (m1_subset_1 @ X31 @ 
% 2.52/2.71                      (k1_zfmisc_1 @ 
% 2.52/2.71                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71                        (u1_struct_0 @ X29))))
% 2.52/2.71                 | ~ (v5_pre_topc @ X31 @ sk_B @ X29)
% 2.52/2.71                 | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71                      (u1_struct_0 @ X29))
% 2.52/2.71                 | ~ (v1_funct_1 @ X31)
% 2.52/2.71                 | (v5_pre_topc @ 
% 2.52/2.71                    (k10_tmap_1 @ sk_A @ X29 @ sk_B @ sk_C @ X31 @ X30) @ 
% 2.52/2.71                    (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ X29))))),
% 2.52/2.71      inference('sup-', [status(thm)], ['399', '433'])).
% 2.52/2.71  thf('435', plain,
% 2.52/2.71      ((((v5_pre_topc @ 
% 2.52/2.71          (k10_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ sk_C @ 
% 2.52/2.71           (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71            (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.71            (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.71           (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71            (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.71            (sk_E @ sk_C @ sk_B @ sk_A))) @ 
% 2.52/2.71          (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.71         | ~ (v1_funct_1 @ 
% 2.52/2.71              (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71               (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.71               (sk_E @ sk_C @ sk_B @ sk_A)))
% 2.52/2.71         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.71         | (v2_struct_0 @ sk_A)
% 2.52/2.71         | (v2_struct_0 @ sk_C)
% 2.52/2.71         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.71         | (v2_struct_0 @ sk_B)))
% 2.52/2.71         <= (((r1_tsep_1 @ sk_B @ sk_C)) & 
% 2.52/2.71             (![X29 : $i, X30 : $i, X31 : $i]:
% 2.52/2.71                ((v2_struct_0 @ X29)
% 2.52/2.71                 | ~ (v2_pre_topc @ X29)
% 2.52/2.71                 | ~ (l1_pre_topc @ X29)
% 2.52/2.71                 | ~ (v1_funct_1 @ X30)
% 2.52/2.71                 | ~ (v1_funct_2 @ X30 @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.71                      (u1_struct_0 @ X29))
% 2.52/2.71                 | ~ (v5_pre_topc @ X30 @ sk_C @ X29)
% 2.52/2.71                 | ~ (m1_subset_1 @ X30 @ 
% 2.52/2.71                      (k1_zfmisc_1 @ 
% 2.52/2.71                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.71                        (u1_struct_0 @ X29))))
% 2.52/2.71                 | ~ (m1_subset_1 @ X31 @ 
% 2.52/2.71                      (k1_zfmisc_1 @ 
% 2.52/2.71                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71                        (u1_struct_0 @ X29))))
% 2.52/2.71                 | ~ (v5_pre_topc @ X31 @ sk_B @ X29)
% 2.52/2.71                 | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71                      (u1_struct_0 @ X29))
% 2.52/2.71                 | ~ (v1_funct_1 @ X31)
% 2.52/2.71                 | (v5_pre_topc @ 
% 2.52/2.71                    (k10_tmap_1 @ sk_A @ X29 @ sk_B @ sk_C @ X31 @ X30) @ 
% 2.52/2.71                    (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ X29))))),
% 2.52/2.71      inference('simplify', [status(thm)], ['434'])).
% 2.52/2.71  thf('436', plain,
% 2.52/2.71      ((((v2_struct_0 @ sk_B)
% 2.52/2.71         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.71         | (v2_struct_0 @ sk_C)
% 2.52/2.71         | (v2_struct_0 @ sk_A)
% 2.52/2.71         | (v2_struct_0 @ sk_B)
% 2.52/2.71         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.71         | (v2_struct_0 @ sk_C)
% 2.52/2.71         | (v2_struct_0 @ sk_A)
% 2.52/2.71         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.71         | (v5_pre_topc @ 
% 2.52/2.71            (k10_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ sk_C @ 
% 2.52/2.71             (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71              (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.71              (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.71             (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71              (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.71              (sk_E @ sk_C @ sk_B @ sk_A))) @ 
% 2.52/2.71            (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ (sk_D @ sk_C @ sk_B @ sk_A))))
% 2.52/2.71         <= (((r1_tsep_1 @ sk_B @ sk_C)) & 
% 2.52/2.71             (![X29 : $i, X30 : $i, X31 : $i]:
% 2.52/2.71                ((v2_struct_0 @ X29)
% 2.52/2.71                 | ~ (v2_pre_topc @ X29)
% 2.52/2.71                 | ~ (l1_pre_topc @ X29)
% 2.52/2.71                 | ~ (v1_funct_1 @ X30)
% 2.52/2.71                 | ~ (v1_funct_2 @ X30 @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.71                      (u1_struct_0 @ X29))
% 2.52/2.71                 | ~ (v5_pre_topc @ X30 @ sk_C @ X29)
% 2.52/2.71                 | ~ (m1_subset_1 @ X30 @ 
% 2.52/2.71                      (k1_zfmisc_1 @ 
% 2.52/2.71                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.71                        (u1_struct_0 @ X29))))
% 2.52/2.71                 | ~ (m1_subset_1 @ X31 @ 
% 2.52/2.71                      (k1_zfmisc_1 @ 
% 2.52/2.71                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71                        (u1_struct_0 @ X29))))
% 2.52/2.71                 | ~ (v5_pre_topc @ X31 @ sk_B @ X29)
% 2.52/2.71                 | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71                      (u1_struct_0 @ X29))
% 2.52/2.71                 | ~ (v1_funct_1 @ X31)
% 2.52/2.71                 | (v5_pre_topc @ 
% 2.52/2.71                    (k10_tmap_1 @ sk_A @ X29 @ sk_B @ sk_C @ X31 @ X30) @ 
% 2.52/2.71                    (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ X29))))),
% 2.52/2.71      inference('sup-', [status(thm)], ['389', '435'])).
% 2.52/2.71  thf('437', plain,
% 2.52/2.71      ((((v5_pre_topc @ 
% 2.52/2.71          (k10_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ sk_C @ 
% 2.52/2.71           (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71            (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.52/2.71            (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.52/2.71           (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71            (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.52/2.71            (sk_E @ sk_C @ sk_B @ sk_A))) @ 
% 2.52/2.71          (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.71         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.71         | (v2_struct_0 @ sk_A)
% 2.52/2.71         | (v2_struct_0 @ sk_C)
% 2.52/2.71         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.71         | (v2_struct_0 @ sk_B)))
% 2.52/2.71         <= (((r1_tsep_1 @ sk_B @ sk_C)) & 
% 2.52/2.71             (![X29 : $i, X30 : $i, X31 : $i]:
% 2.52/2.71                ((v2_struct_0 @ X29)
% 2.52/2.71                 | ~ (v2_pre_topc @ X29)
% 2.52/2.71                 | ~ (l1_pre_topc @ X29)
% 2.52/2.71                 | ~ (v1_funct_1 @ X30)
% 2.52/2.71                 | ~ (v1_funct_2 @ X30 @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.71                      (u1_struct_0 @ X29))
% 2.52/2.71                 | ~ (v5_pre_topc @ X30 @ sk_C @ X29)
% 2.52/2.71                 | ~ (m1_subset_1 @ X30 @ 
% 2.52/2.71                      (k1_zfmisc_1 @ 
% 2.52/2.71                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.71                        (u1_struct_0 @ X29))))
% 2.52/2.71                 | ~ (m1_subset_1 @ X31 @ 
% 2.52/2.71                      (k1_zfmisc_1 @ 
% 2.52/2.71                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71                        (u1_struct_0 @ X29))))
% 2.52/2.71                 | ~ (v5_pre_topc @ X31 @ sk_B @ X29)
% 2.52/2.71                 | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71                      (u1_struct_0 @ X29))
% 2.52/2.71                 | ~ (v1_funct_1 @ X31)
% 2.52/2.71                 | (v5_pre_topc @ 
% 2.52/2.71                    (k10_tmap_1 @ sk_A @ X29 @ sk_B @ sk_C @ X31 @ X30) @ 
% 2.52/2.71                    (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ X29))))),
% 2.52/2.71      inference('simplify', [status(thm)], ['436'])).
% 2.52/2.71  thf('438', plain,
% 2.52/2.71      ((((v5_pre_topc @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71          (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.71         | (v2_struct_0 @ sk_B)
% 2.52/2.71         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.71         | (v2_struct_0 @ sk_C)
% 2.52/2.71         | (v2_struct_0 @ sk_A)
% 2.52/2.71         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.71         | (v2_struct_0 @ sk_B)
% 2.52/2.71         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.71         | (v2_struct_0 @ sk_C)
% 2.52/2.71         | (v2_struct_0 @ sk_A)
% 2.52/2.71         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))))
% 2.52/2.71         <= (((r1_tsep_1 @ sk_B @ sk_C)) & 
% 2.52/2.71             (![X29 : $i, X30 : $i, X31 : $i]:
% 2.52/2.71                ((v2_struct_0 @ X29)
% 2.52/2.71                 | ~ (v2_pre_topc @ X29)
% 2.52/2.71                 | ~ (l1_pre_topc @ X29)
% 2.52/2.71                 | ~ (v1_funct_1 @ X30)
% 2.52/2.71                 | ~ (v1_funct_2 @ X30 @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.71                      (u1_struct_0 @ X29))
% 2.52/2.71                 | ~ (v5_pre_topc @ X30 @ sk_C @ X29)
% 2.52/2.71                 | ~ (m1_subset_1 @ X30 @ 
% 2.52/2.71                      (k1_zfmisc_1 @ 
% 2.52/2.71                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.71                        (u1_struct_0 @ X29))))
% 2.52/2.71                 | ~ (m1_subset_1 @ X31 @ 
% 2.52/2.71                      (k1_zfmisc_1 @ 
% 2.52/2.71                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71                        (u1_struct_0 @ X29))))
% 2.52/2.71                 | ~ (v5_pre_topc @ X31 @ sk_B @ X29)
% 2.52/2.71                 | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71                      (u1_struct_0 @ X29))
% 2.52/2.71                 | ~ (v1_funct_1 @ X31)
% 2.52/2.71                 | (v5_pre_topc @ 
% 2.52/2.71                    (k10_tmap_1 @ sk_A @ X29 @ sk_B @ sk_C @ X31 @ X30) @ 
% 2.52/2.71                    (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ X29))))),
% 2.52/2.71      inference('sup+', [status(thm)], ['388', '437'])).
% 2.52/2.71  thf('439', plain,
% 2.52/2.71      ((((v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.71         | (v2_struct_0 @ sk_A)
% 2.52/2.71         | (v2_struct_0 @ sk_C)
% 2.52/2.71         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.71         | (v2_struct_0 @ sk_B)
% 2.52/2.71         | (v5_pre_topc @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71            (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ (sk_D @ sk_C @ sk_B @ sk_A))))
% 2.52/2.71         <= (((r1_tsep_1 @ sk_B @ sk_C)) & 
% 2.52/2.71             (![X29 : $i, X30 : $i, X31 : $i]:
% 2.52/2.71                ((v2_struct_0 @ X29)
% 2.52/2.71                 | ~ (v2_pre_topc @ X29)
% 2.52/2.71                 | ~ (l1_pre_topc @ X29)
% 2.52/2.71                 | ~ (v1_funct_1 @ X30)
% 2.52/2.71                 | ~ (v1_funct_2 @ X30 @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.71                      (u1_struct_0 @ X29))
% 2.52/2.71                 | ~ (v5_pre_topc @ X30 @ sk_C @ X29)
% 2.52/2.71                 | ~ (m1_subset_1 @ X30 @ 
% 2.52/2.71                      (k1_zfmisc_1 @ 
% 2.52/2.71                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.71                        (u1_struct_0 @ X29))))
% 2.52/2.71                 | ~ (m1_subset_1 @ X31 @ 
% 2.52/2.71                      (k1_zfmisc_1 @ 
% 2.52/2.71                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71                        (u1_struct_0 @ X29))))
% 2.52/2.71                 | ~ (v5_pre_topc @ X31 @ sk_B @ X29)
% 2.52/2.71                 | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71                      (u1_struct_0 @ X29))
% 2.52/2.71                 | ~ (v1_funct_1 @ X31)
% 2.52/2.71                 | (v5_pre_topc @ 
% 2.52/2.71                    (k10_tmap_1 @ sk_A @ X29 @ sk_B @ sk_C @ X31 @ X30) @ 
% 2.52/2.71                    (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ X29))))),
% 2.52/2.71      inference('simplify', [status(thm)], ['438'])).
% 2.52/2.71  thf('440', plain,
% 2.52/2.71      ((((v2_struct_0 @ sk_A)
% 2.52/2.71         | (v2_struct_0 @ sk_C)
% 2.52/2.71         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.71         | (v1_funct_2 @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71            (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.52/2.71            (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.71         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.71      inference('sup-', [status(thm)], ['336', '344'])).
% 2.52/2.71  thf('441', plain,
% 2.52/2.71      ((((v2_struct_0 @ sk_A)
% 2.52/2.71         | (v2_struct_0 @ sk_C)
% 2.52/2.71         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.71         | (m1_subset_1 @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71            (k1_zfmisc_1 @ 
% 2.52/2.71             (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.52/2.71              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.52/2.71         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.71      inference('sup-', [status(thm)], ['346', '354'])).
% 2.52/2.71  thf('442', plain,
% 2.52/2.71      (![X10 : $i, X11 : $i, X12 : $i]:
% 2.52/2.71         ((v2_struct_0 @ X10)
% 2.52/2.71          | ~ (m1_pre_topc @ X10 @ X11)
% 2.52/2.71          | ~ (r1_tsep_1 @ X10 @ X12)
% 2.52/2.71          | ~ (v1_funct_1 @ (sk_E @ X12 @ X10 @ X11))
% 2.52/2.71          | ~ (v1_funct_2 @ (sk_E @ X12 @ X10 @ X11) @ 
% 2.52/2.71               (u1_struct_0 @ (k1_tsep_1 @ X11 @ X10 @ X12)) @ 
% 2.52/2.71               (u1_struct_0 @ (sk_D @ X12 @ X10 @ X11)))
% 2.52/2.71          | ~ (v5_pre_topc @ (sk_E @ X12 @ X10 @ X11) @ 
% 2.52/2.71               (k1_tsep_1 @ X11 @ X10 @ X12) @ (sk_D @ X12 @ X10 @ X11))
% 2.52/2.71          | ~ (m1_subset_1 @ (sk_E @ X12 @ X10 @ X11) @ 
% 2.52/2.71               (k1_zfmisc_1 @ 
% 2.52/2.71                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X11 @ X10 @ X12)) @ 
% 2.52/2.71                 (u1_struct_0 @ (sk_D @ X12 @ X10 @ X11)))))
% 2.52/2.71          | (r3_tsep_1 @ X11 @ X10 @ X12)
% 2.52/2.71          | ~ (m1_pre_topc @ X12 @ X11)
% 2.52/2.71          | (v2_struct_0 @ X12)
% 2.52/2.71          | ~ (l1_pre_topc @ X11)
% 2.52/2.71          | ~ (v2_pre_topc @ X11)
% 2.52/2.71          | (v2_struct_0 @ X11))),
% 2.52/2.71      inference('cnf', [status(esa)], [t135_tmap_1])).
% 2.52/2.71  thf('443', plain,
% 2.52/2.71      ((((v2_struct_0 @ sk_B)
% 2.52/2.71         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.71         | (v2_struct_0 @ sk_C)
% 2.52/2.71         | (v2_struct_0 @ sk_A)
% 2.52/2.71         | (v2_struct_0 @ sk_A)
% 2.52/2.71         | ~ (v2_pre_topc @ sk_A)
% 2.52/2.71         | ~ (l1_pre_topc @ sk_A)
% 2.52/2.71         | (v2_struct_0 @ sk_C)
% 2.52/2.71         | ~ (m1_pre_topc @ sk_C @ sk_A)
% 2.52/2.71         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.71         | ~ (v5_pre_topc @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71              (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.71         | ~ (v1_funct_2 @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71              (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.52/2.71              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.71         | ~ (v1_funct_1 @ (sk_E @ sk_C @ sk_B @ sk_A))
% 2.52/2.71         | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 2.52/2.71         | ~ (m1_pre_topc @ sk_B @ sk_A)
% 2.52/2.71         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.71      inference('sup-', [status(thm)], ['441', '442'])).
% 2.52/2.71  thf('444', plain, ((v2_pre_topc @ sk_A)),
% 2.52/2.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.71  thf('445', plain, ((l1_pre_topc @ sk_A)),
% 2.52/2.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.71  thf('446', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 2.52/2.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.71  thf('447', plain,
% 2.52/2.71      (((r1_tsep_1 @ sk_B @ sk_C)) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.71      inference('split', [status(esa)], ['0'])).
% 2.52/2.71  thf('448', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 2.52/2.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.71  thf('449', plain,
% 2.52/2.71      ((((v2_struct_0 @ sk_B)
% 2.52/2.71         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.71         | (v2_struct_0 @ sk_C)
% 2.52/2.71         | (v2_struct_0 @ sk_A)
% 2.52/2.71         | (v2_struct_0 @ sk_A)
% 2.52/2.71         | (v2_struct_0 @ sk_C)
% 2.52/2.71         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.71         | ~ (v5_pre_topc @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71              (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.71         | ~ (v1_funct_2 @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71              (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.52/2.71              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.71         | ~ (v1_funct_1 @ (sk_E @ sk_C @ sk_B @ sk_A))
% 2.52/2.71         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.71      inference('demod', [status(thm)],
% 2.52/2.71                ['443', '444', '445', '446', '447', '448'])).
% 2.52/2.71  thf('450', plain,
% 2.52/2.71      (((~ (v1_funct_1 @ (sk_E @ sk_C @ sk_B @ sk_A))
% 2.52/2.71         | ~ (v1_funct_2 @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71              (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.52/2.71              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.52/2.71         | ~ (v5_pre_topc @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71              (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.71         | (v2_struct_0 @ sk_A)
% 2.52/2.71         | (v2_struct_0 @ sk_C)
% 2.52/2.71         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.71         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.71      inference('simplify', [status(thm)], ['449'])).
% 2.52/2.71  thf('451', plain,
% 2.52/2.71      ((((v2_struct_0 @ sk_B)
% 2.52/2.71         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.71         | (v2_struct_0 @ sk_C)
% 2.52/2.71         | (v2_struct_0 @ sk_A)
% 2.52/2.71         | (v2_struct_0 @ sk_B)
% 2.52/2.71         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.71         | (v2_struct_0 @ sk_C)
% 2.52/2.71         | (v2_struct_0 @ sk_A)
% 2.52/2.71         | ~ (v5_pre_topc @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71              (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.71         | ~ (v1_funct_1 @ (sk_E @ sk_C @ sk_B @ sk_A))))
% 2.52/2.71         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.71      inference('sup-', [status(thm)], ['440', '450'])).
% 2.52/2.71  thf('452', plain,
% 2.52/2.71      (((~ (v1_funct_1 @ (sk_E @ sk_C @ sk_B @ sk_A))
% 2.52/2.71         | ~ (v5_pre_topc @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 2.52/2.71              (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.71         | (v2_struct_0 @ sk_A)
% 2.52/2.71         | (v2_struct_0 @ sk_C)
% 2.52/2.71         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.71         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.71      inference('simplify', [status(thm)], ['451'])).
% 2.52/2.71  thf('453', plain,
% 2.52/2.71      ((((v2_struct_0 @ sk_B)
% 2.52/2.71         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.71         | (v2_struct_0 @ sk_C)
% 2.52/2.71         | (v2_struct_0 @ sk_A)
% 2.52/2.71         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.71         | (v2_struct_0 @ sk_B)
% 2.52/2.71         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.71         | (v2_struct_0 @ sk_C)
% 2.52/2.71         | (v2_struct_0 @ sk_A)
% 2.52/2.71         | ~ (v1_funct_1 @ (sk_E @ sk_C @ sk_B @ sk_A))))
% 2.52/2.71         <= (((r1_tsep_1 @ sk_B @ sk_C)) & 
% 2.52/2.71             (![X29 : $i, X30 : $i, X31 : $i]:
% 2.52/2.71                ((v2_struct_0 @ X29)
% 2.52/2.71                 | ~ (v2_pre_topc @ X29)
% 2.52/2.71                 | ~ (l1_pre_topc @ X29)
% 2.52/2.71                 | ~ (v1_funct_1 @ X30)
% 2.52/2.71                 | ~ (v1_funct_2 @ X30 @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.71                      (u1_struct_0 @ X29))
% 2.52/2.71                 | ~ (v5_pre_topc @ X30 @ sk_C @ X29)
% 2.52/2.71                 | ~ (m1_subset_1 @ X30 @ 
% 2.52/2.71                      (k1_zfmisc_1 @ 
% 2.52/2.71                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.71                        (u1_struct_0 @ X29))))
% 2.52/2.71                 | ~ (m1_subset_1 @ X31 @ 
% 2.52/2.71                      (k1_zfmisc_1 @ 
% 2.52/2.71                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71                        (u1_struct_0 @ X29))))
% 2.52/2.71                 | ~ (v5_pre_topc @ X31 @ sk_B @ X29)
% 2.52/2.71                 | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71                      (u1_struct_0 @ X29))
% 2.52/2.71                 | ~ (v1_funct_1 @ X31)
% 2.52/2.71                 | (v5_pre_topc @ 
% 2.52/2.71                    (k10_tmap_1 @ sk_A @ X29 @ sk_B @ sk_C @ X31 @ X30) @ 
% 2.52/2.71                    (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ X29))))),
% 2.52/2.71      inference('sup-', [status(thm)], ['439', '452'])).
% 2.52/2.71  thf('454', plain,
% 2.52/2.71      (((~ (v1_funct_1 @ (sk_E @ sk_C @ sk_B @ sk_A))
% 2.52/2.71         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.71         | (v2_struct_0 @ sk_A)
% 2.52/2.71         | (v2_struct_0 @ sk_C)
% 2.52/2.71         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.71         | (v2_struct_0 @ sk_B)))
% 2.52/2.71         <= (((r1_tsep_1 @ sk_B @ sk_C)) & 
% 2.52/2.71             (![X29 : $i, X30 : $i, X31 : $i]:
% 2.52/2.71                ((v2_struct_0 @ X29)
% 2.52/2.71                 | ~ (v2_pre_topc @ X29)
% 2.52/2.71                 | ~ (l1_pre_topc @ X29)
% 2.52/2.71                 | ~ (v1_funct_1 @ X30)
% 2.52/2.71                 | ~ (v1_funct_2 @ X30 @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.71                      (u1_struct_0 @ X29))
% 2.52/2.71                 | ~ (v5_pre_topc @ X30 @ sk_C @ X29)
% 2.52/2.71                 | ~ (m1_subset_1 @ X30 @ 
% 2.52/2.71                      (k1_zfmisc_1 @ 
% 2.52/2.71                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.71                        (u1_struct_0 @ X29))))
% 2.52/2.71                 | ~ (m1_subset_1 @ X31 @ 
% 2.52/2.71                      (k1_zfmisc_1 @ 
% 2.52/2.71                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71                        (u1_struct_0 @ X29))))
% 2.52/2.71                 | ~ (v5_pre_topc @ X31 @ sk_B @ X29)
% 2.52/2.71                 | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71                      (u1_struct_0 @ X29))
% 2.52/2.71                 | ~ (v1_funct_1 @ X31)
% 2.52/2.71                 | (v5_pre_topc @ 
% 2.52/2.71                    (k10_tmap_1 @ sk_A @ X29 @ sk_B @ sk_C @ X31 @ X30) @ 
% 2.52/2.71                    (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ X29))))),
% 2.52/2.71      inference('simplify', [status(thm)], ['453'])).
% 2.52/2.71  thf('455', plain,
% 2.52/2.71      ((((v2_struct_0 @ sk_B)
% 2.52/2.71         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.71         | (v2_struct_0 @ sk_C)
% 2.52/2.71         | (v2_struct_0 @ sk_A)
% 2.52/2.71         | (v2_struct_0 @ sk_B)
% 2.52/2.71         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.71         | (v2_struct_0 @ sk_C)
% 2.52/2.71         | (v2_struct_0 @ sk_A)
% 2.52/2.71         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))))
% 2.52/2.71         <= (((r1_tsep_1 @ sk_B @ sk_C)) & 
% 2.52/2.71             (![X29 : $i, X30 : $i, X31 : $i]:
% 2.52/2.71                ((v2_struct_0 @ X29)
% 2.52/2.71                 | ~ (v2_pre_topc @ X29)
% 2.52/2.71                 | ~ (l1_pre_topc @ X29)
% 2.52/2.71                 | ~ (v1_funct_1 @ X30)
% 2.52/2.71                 | ~ (v1_funct_2 @ X30 @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.71                      (u1_struct_0 @ X29))
% 2.52/2.71                 | ~ (v5_pre_topc @ X30 @ sk_C @ X29)
% 2.52/2.71                 | ~ (m1_subset_1 @ X30 @ 
% 2.52/2.71                      (k1_zfmisc_1 @ 
% 2.52/2.71                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.71                        (u1_struct_0 @ X29))))
% 2.52/2.71                 | ~ (m1_subset_1 @ X31 @ 
% 2.52/2.71                      (k1_zfmisc_1 @ 
% 2.52/2.71                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71                        (u1_struct_0 @ X29))))
% 2.52/2.71                 | ~ (v5_pre_topc @ X31 @ sk_B @ X29)
% 2.52/2.71                 | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71                      (u1_struct_0 @ X29))
% 2.52/2.71                 | ~ (v1_funct_1 @ X31)
% 2.52/2.71                 | (v5_pre_topc @ 
% 2.52/2.71                    (k10_tmap_1 @ sk_A @ X29 @ sk_B @ sk_C @ X31 @ X30) @ 
% 2.52/2.71                    (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ X29))))),
% 2.52/2.71      inference('sup-', [status(thm)], ['164', '454'])).
% 2.52/2.71  thf('456', plain,
% 2.52/2.71      ((((v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.52/2.71         | (v2_struct_0 @ sk_A)
% 2.52/2.71         | (v2_struct_0 @ sk_C)
% 2.52/2.71         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.71         | (v2_struct_0 @ sk_B)))
% 2.52/2.71         <= (((r1_tsep_1 @ sk_B @ sk_C)) & 
% 2.52/2.71             (![X29 : $i, X30 : $i, X31 : $i]:
% 2.52/2.71                ((v2_struct_0 @ X29)
% 2.52/2.71                 | ~ (v2_pre_topc @ X29)
% 2.52/2.71                 | ~ (l1_pre_topc @ X29)
% 2.52/2.71                 | ~ (v1_funct_1 @ X30)
% 2.52/2.71                 | ~ (v1_funct_2 @ X30 @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.71                      (u1_struct_0 @ X29))
% 2.52/2.71                 | ~ (v5_pre_topc @ X30 @ sk_C @ X29)
% 2.52/2.71                 | ~ (m1_subset_1 @ X30 @ 
% 2.52/2.71                      (k1_zfmisc_1 @ 
% 2.52/2.71                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.71                        (u1_struct_0 @ X29))))
% 2.52/2.71                 | ~ (m1_subset_1 @ X31 @ 
% 2.52/2.71                      (k1_zfmisc_1 @ 
% 2.52/2.71                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71                        (u1_struct_0 @ X29))))
% 2.52/2.71                 | ~ (v5_pre_topc @ X31 @ sk_B @ X29)
% 2.52/2.71                 | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71                      (u1_struct_0 @ X29))
% 2.52/2.71                 | ~ (v1_funct_1 @ X31)
% 2.52/2.71                 | (v5_pre_topc @ 
% 2.52/2.71                    (k10_tmap_1 @ sk_A @ X29 @ sk_B @ sk_C @ X31 @ X30) @ 
% 2.52/2.71                    (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ X29))))),
% 2.52/2.71      inference('simplify', [status(thm)], ['455'])).
% 2.52/2.71  thf('457', plain,
% 2.52/2.71      (![X10 : $i, X11 : $i, X12 : $i]:
% 2.52/2.71         ((v2_struct_0 @ X10)
% 2.52/2.71          | ~ (m1_pre_topc @ X10 @ X11)
% 2.52/2.71          | ~ (r1_tsep_1 @ X10 @ X12)
% 2.52/2.71          | ~ (v2_struct_0 @ (sk_D @ X12 @ X10 @ X11))
% 2.52/2.71          | (r3_tsep_1 @ X11 @ X10 @ X12)
% 2.52/2.71          | ~ (m1_pre_topc @ X12 @ X11)
% 2.52/2.71          | (v2_struct_0 @ X12)
% 2.52/2.71          | ~ (l1_pre_topc @ X11)
% 2.52/2.71          | ~ (v2_pre_topc @ X11)
% 2.52/2.71          | (v2_struct_0 @ X11))),
% 2.52/2.71      inference('cnf', [status(esa)], [t135_tmap_1])).
% 2.52/2.71  thf('458', plain,
% 2.52/2.71      ((((v2_struct_0 @ sk_B)
% 2.52/2.71         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.71         | (v2_struct_0 @ sk_C)
% 2.52/2.71         | (v2_struct_0 @ sk_A)
% 2.52/2.71         | (v2_struct_0 @ sk_A)
% 2.52/2.71         | ~ (v2_pre_topc @ sk_A)
% 2.52/2.71         | ~ (l1_pre_topc @ sk_A)
% 2.52/2.71         | (v2_struct_0 @ sk_C)
% 2.52/2.71         | ~ (m1_pre_topc @ sk_C @ sk_A)
% 2.52/2.71         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.71         | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 2.52/2.71         | ~ (m1_pre_topc @ sk_B @ sk_A)
% 2.52/2.71         | (v2_struct_0 @ sk_B)))
% 2.52/2.71         <= (((r1_tsep_1 @ sk_B @ sk_C)) & 
% 2.52/2.71             (![X29 : $i, X30 : $i, X31 : $i]:
% 2.52/2.71                ((v2_struct_0 @ X29)
% 2.52/2.71                 | ~ (v2_pre_topc @ X29)
% 2.52/2.71                 | ~ (l1_pre_topc @ X29)
% 2.52/2.71                 | ~ (v1_funct_1 @ X30)
% 2.52/2.71                 | ~ (v1_funct_2 @ X30 @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.71                      (u1_struct_0 @ X29))
% 2.52/2.71                 | ~ (v5_pre_topc @ X30 @ sk_C @ X29)
% 2.52/2.71                 | ~ (m1_subset_1 @ X30 @ 
% 2.52/2.71                      (k1_zfmisc_1 @ 
% 2.52/2.71                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.71                        (u1_struct_0 @ X29))))
% 2.52/2.71                 | ~ (m1_subset_1 @ X31 @ 
% 2.52/2.71                      (k1_zfmisc_1 @ 
% 2.52/2.71                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71                        (u1_struct_0 @ X29))))
% 2.52/2.71                 | ~ (v5_pre_topc @ X31 @ sk_B @ X29)
% 2.52/2.71                 | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71                      (u1_struct_0 @ X29))
% 2.52/2.71                 | ~ (v1_funct_1 @ X31)
% 2.52/2.71                 | (v5_pre_topc @ 
% 2.52/2.71                    (k10_tmap_1 @ sk_A @ X29 @ sk_B @ sk_C @ X31 @ X30) @ 
% 2.52/2.71                    (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ X29))))),
% 2.52/2.71      inference('sup-', [status(thm)], ['456', '457'])).
% 2.52/2.71  thf('459', plain, ((v2_pre_topc @ sk_A)),
% 2.52/2.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.71  thf('460', plain, ((l1_pre_topc @ sk_A)),
% 2.52/2.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.71  thf('461', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 2.52/2.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.71  thf('462', plain,
% 2.52/2.71      (((r1_tsep_1 @ sk_B @ sk_C)) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.52/2.71      inference('split', [status(esa)], ['0'])).
% 2.52/2.71  thf('463', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 2.52/2.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.71  thf('464', plain,
% 2.52/2.71      ((((v2_struct_0 @ sk_B)
% 2.52/2.71         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.71         | (v2_struct_0 @ sk_C)
% 2.52/2.71         | (v2_struct_0 @ sk_A)
% 2.52/2.71         | (v2_struct_0 @ sk_A)
% 2.52/2.71         | (v2_struct_0 @ sk_C)
% 2.52/2.71         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.71         | (v2_struct_0 @ sk_B)))
% 2.52/2.71         <= (((r1_tsep_1 @ sk_B @ sk_C)) & 
% 2.52/2.71             (![X29 : $i, X30 : $i, X31 : $i]:
% 2.52/2.71                ((v2_struct_0 @ X29)
% 2.52/2.71                 | ~ (v2_pre_topc @ X29)
% 2.52/2.71                 | ~ (l1_pre_topc @ X29)
% 2.52/2.71                 | ~ (v1_funct_1 @ X30)
% 2.52/2.71                 | ~ (v1_funct_2 @ X30 @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.71                      (u1_struct_0 @ X29))
% 2.52/2.71                 | ~ (v5_pre_topc @ X30 @ sk_C @ X29)
% 2.52/2.71                 | ~ (m1_subset_1 @ X30 @ 
% 2.52/2.71                      (k1_zfmisc_1 @ 
% 2.52/2.71                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.71                        (u1_struct_0 @ X29))))
% 2.52/2.71                 | ~ (m1_subset_1 @ X31 @ 
% 2.52/2.71                      (k1_zfmisc_1 @ 
% 2.52/2.71                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71                        (u1_struct_0 @ X29))))
% 2.52/2.71                 | ~ (v5_pre_topc @ X31 @ sk_B @ X29)
% 2.52/2.71                 | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71                      (u1_struct_0 @ X29))
% 2.52/2.71                 | ~ (v1_funct_1 @ X31)
% 2.52/2.71                 | (v5_pre_topc @ 
% 2.52/2.71                    (k10_tmap_1 @ sk_A @ X29 @ sk_B @ sk_C @ X31 @ X30) @ 
% 2.52/2.71                    (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ X29))))),
% 2.52/2.71      inference('demod', [status(thm)],
% 2.52/2.71                ['458', '459', '460', '461', '462', '463'])).
% 2.52/2.71  thf('465', plain,
% 2.52/2.71      ((((v2_struct_0 @ sk_A)
% 2.52/2.71         | (v2_struct_0 @ sk_C)
% 2.52/2.71         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.52/2.71         | (v2_struct_0 @ sk_B)))
% 2.52/2.71         <= (((r1_tsep_1 @ sk_B @ sk_C)) & 
% 2.52/2.71             (![X29 : $i, X30 : $i, X31 : $i]:
% 2.52/2.71                ((v2_struct_0 @ X29)
% 2.52/2.71                 | ~ (v2_pre_topc @ X29)
% 2.52/2.71                 | ~ (l1_pre_topc @ X29)
% 2.52/2.71                 | ~ (v1_funct_1 @ X30)
% 2.52/2.71                 | ~ (v1_funct_2 @ X30 @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.71                      (u1_struct_0 @ X29))
% 2.52/2.71                 | ~ (v5_pre_topc @ X30 @ sk_C @ X29)
% 2.52/2.71                 | ~ (m1_subset_1 @ X30 @ 
% 2.52/2.71                      (k1_zfmisc_1 @ 
% 2.52/2.71                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.71                        (u1_struct_0 @ X29))))
% 2.52/2.71                 | ~ (m1_subset_1 @ X31 @ 
% 2.52/2.71                      (k1_zfmisc_1 @ 
% 2.52/2.71                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71                        (u1_struct_0 @ X29))))
% 2.52/2.71                 | ~ (v5_pre_topc @ X31 @ sk_B @ X29)
% 2.52/2.71                 | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71                      (u1_struct_0 @ X29))
% 2.52/2.71                 | ~ (v1_funct_1 @ X31)
% 2.52/2.71                 | (v5_pre_topc @ 
% 2.52/2.71                    (k10_tmap_1 @ sk_A @ X29 @ sk_B @ sk_C @ X31 @ X30) @ 
% 2.52/2.71                    (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ X29))))),
% 2.52/2.71      inference('simplify', [status(thm)], ['464'])).
% 2.52/2.71  thf('466', plain,
% 2.52/2.71      ((~ (r3_tsep_1 @ sk_A @ sk_B @ sk_C))
% 2.52/2.71         <= (~ ((r3_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 2.52/2.71      inference('split', [status(esa)], ['10'])).
% 2.52/2.71  thf('467', plain,
% 2.52/2.71      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A)))
% 2.52/2.71         <= (~ ((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) & 
% 2.52/2.71             ((r1_tsep_1 @ sk_B @ sk_C)) & 
% 2.52/2.71             (![X29 : $i, X30 : $i, X31 : $i]:
% 2.52/2.71                ((v2_struct_0 @ X29)
% 2.52/2.71                 | ~ (v2_pre_topc @ X29)
% 2.52/2.71                 | ~ (l1_pre_topc @ X29)
% 2.52/2.71                 | ~ (v1_funct_1 @ X30)
% 2.52/2.71                 | ~ (v1_funct_2 @ X30 @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.71                      (u1_struct_0 @ X29))
% 2.52/2.71                 | ~ (v5_pre_topc @ X30 @ sk_C @ X29)
% 2.52/2.71                 | ~ (m1_subset_1 @ X30 @ 
% 2.52/2.71                      (k1_zfmisc_1 @ 
% 2.52/2.71                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.71                        (u1_struct_0 @ X29))))
% 2.52/2.71                 | ~ (m1_subset_1 @ X31 @ 
% 2.52/2.71                      (k1_zfmisc_1 @ 
% 2.52/2.71                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71                        (u1_struct_0 @ X29))))
% 2.52/2.71                 | ~ (v5_pre_topc @ X31 @ sk_B @ X29)
% 2.52/2.71                 | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71                      (u1_struct_0 @ X29))
% 2.52/2.71                 | ~ (v1_funct_1 @ X31)
% 2.52/2.71                 | (v5_pre_topc @ 
% 2.52/2.71                    (k10_tmap_1 @ sk_A @ X29 @ sk_B @ sk_C @ X31 @ X30) @ 
% 2.52/2.71                    (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ X29))))),
% 2.52/2.71      inference('sup-', [status(thm)], ['465', '466'])).
% 2.52/2.71  thf('468', plain, (~ (v2_struct_0 @ sk_B)),
% 2.52/2.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.71  thf('469', plain,
% 2.52/2.71      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C)))
% 2.52/2.71         <= (~ ((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) & 
% 2.52/2.71             ((r1_tsep_1 @ sk_B @ sk_C)) & 
% 2.52/2.71             (![X29 : $i, X30 : $i, X31 : $i]:
% 2.52/2.71                ((v2_struct_0 @ X29)
% 2.52/2.71                 | ~ (v2_pre_topc @ X29)
% 2.52/2.71                 | ~ (l1_pre_topc @ X29)
% 2.52/2.71                 | ~ (v1_funct_1 @ X30)
% 2.52/2.71                 | ~ (v1_funct_2 @ X30 @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.71                      (u1_struct_0 @ X29))
% 2.52/2.71                 | ~ (v5_pre_topc @ X30 @ sk_C @ X29)
% 2.52/2.71                 | ~ (m1_subset_1 @ X30 @ 
% 2.52/2.71                      (k1_zfmisc_1 @ 
% 2.52/2.71                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.71                        (u1_struct_0 @ X29))))
% 2.52/2.71                 | ~ (m1_subset_1 @ X31 @ 
% 2.52/2.71                      (k1_zfmisc_1 @ 
% 2.52/2.71                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71                        (u1_struct_0 @ X29))))
% 2.52/2.71                 | ~ (v5_pre_topc @ X31 @ sk_B @ X29)
% 2.52/2.71                 | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71                      (u1_struct_0 @ X29))
% 2.52/2.71                 | ~ (v1_funct_1 @ X31)
% 2.52/2.71                 | (v5_pre_topc @ 
% 2.52/2.71                    (k10_tmap_1 @ sk_A @ X29 @ sk_B @ sk_C @ X31 @ X30) @ 
% 2.52/2.71                    (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ X29))))),
% 2.52/2.71      inference('clc', [status(thm)], ['467', '468'])).
% 2.52/2.71  thf('470', plain, (~ (v2_struct_0 @ sk_A)),
% 2.52/2.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.71  thf('471', plain,
% 2.52/2.71      (((v2_struct_0 @ sk_C))
% 2.52/2.71         <= (~ ((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) & 
% 2.52/2.71             ((r1_tsep_1 @ sk_B @ sk_C)) & 
% 2.52/2.71             (![X29 : $i, X30 : $i, X31 : $i]:
% 2.52/2.71                ((v2_struct_0 @ X29)
% 2.52/2.71                 | ~ (v2_pre_topc @ X29)
% 2.52/2.71                 | ~ (l1_pre_topc @ X29)
% 2.52/2.71                 | ~ (v1_funct_1 @ X30)
% 2.52/2.71                 | ~ (v1_funct_2 @ X30 @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.71                      (u1_struct_0 @ X29))
% 2.52/2.71                 | ~ (v5_pre_topc @ X30 @ sk_C @ X29)
% 2.52/2.71                 | ~ (m1_subset_1 @ X30 @ 
% 2.52/2.71                      (k1_zfmisc_1 @ 
% 2.52/2.71                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.71                        (u1_struct_0 @ X29))))
% 2.52/2.71                 | ~ (m1_subset_1 @ X31 @ 
% 2.52/2.71                      (k1_zfmisc_1 @ 
% 2.52/2.71                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71                        (u1_struct_0 @ X29))))
% 2.52/2.71                 | ~ (v5_pre_topc @ X31 @ sk_B @ X29)
% 2.52/2.71                 | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71                      (u1_struct_0 @ X29))
% 2.52/2.71                 | ~ (v1_funct_1 @ X31)
% 2.52/2.71                 | (v5_pre_topc @ 
% 2.52/2.71                    (k10_tmap_1 @ sk_A @ X29 @ sk_B @ sk_C @ X31 @ X30) @ 
% 2.52/2.71                    (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ X29))))),
% 2.52/2.71      inference('clc', [status(thm)], ['469', '470'])).
% 2.52/2.71  thf('472', plain, (~ (v2_struct_0 @ sk_C)),
% 2.52/2.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.71  thf('473', plain,
% 2.52/2.71      (((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) | 
% 2.52/2.71       ~
% 2.52/2.71       (![X29 : $i, X30 : $i, X31 : $i]:
% 2.52/2.71          ((v2_struct_0 @ X29)
% 2.52/2.71           | ~ (v2_pre_topc @ X29)
% 2.52/2.71           | ~ (l1_pre_topc @ X29)
% 2.52/2.71           | ~ (v1_funct_1 @ X30)
% 2.52/2.71           | ~ (v1_funct_2 @ X30 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X29))
% 2.52/2.71           | ~ (v5_pre_topc @ X30 @ sk_C @ X29)
% 2.52/2.71           | ~ (m1_subset_1 @ X30 @ 
% 2.52/2.71                (k1_zfmisc_1 @ 
% 2.52/2.71                 (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X29))))
% 2.52/2.71           | ~ (m1_subset_1 @ X31 @ 
% 2.52/2.71                (k1_zfmisc_1 @ 
% 2.52/2.71                 (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X29))))
% 2.52/2.71           | ~ (v5_pre_topc @ X31 @ sk_B @ X29)
% 2.52/2.71           | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X29))
% 2.52/2.71           | ~ (v1_funct_1 @ X31)
% 2.52/2.71           | (v5_pre_topc @ 
% 2.52/2.71              (k10_tmap_1 @ sk_A @ X29 @ sk_B @ sk_C @ X31 @ X30) @ 
% 2.52/2.71              (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ X29))) | 
% 2.52/2.71       ~ ((r1_tsep_1 @ sk_B @ sk_C))),
% 2.52/2.71      inference('sup-', [status(thm)], ['471', '472'])).
% 2.52/2.71  thf('474', plain,
% 2.52/2.71      (((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) | 
% 2.52/2.71       (![X29 : $i, X30 : $i, X31 : $i]:
% 2.52/2.71          ((v2_struct_0 @ X29)
% 2.52/2.71           | ~ (v2_pre_topc @ X29)
% 2.52/2.71           | ~ (l1_pre_topc @ X29)
% 2.52/2.71           | ~ (v1_funct_1 @ X30)
% 2.52/2.71           | ~ (v1_funct_2 @ X30 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X29))
% 2.52/2.71           | ~ (v5_pre_topc @ X30 @ sk_C @ X29)
% 2.52/2.71           | ~ (m1_subset_1 @ X30 @ 
% 2.52/2.71                (k1_zfmisc_1 @ 
% 2.52/2.71                 (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X29))))
% 2.52/2.71           | ~ (m1_subset_1 @ X31 @ 
% 2.52/2.71                (k1_zfmisc_1 @ 
% 2.52/2.71                 (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X29))))
% 2.52/2.71           | ~ (v5_pre_topc @ X31 @ sk_B @ X29)
% 2.52/2.71           | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X29))
% 2.52/2.71           | ~ (v1_funct_1 @ X31)
% 2.52/2.71           | (v5_pre_topc @ 
% 2.52/2.71              (k10_tmap_1 @ sk_A @ X29 @ sk_B @ sk_C @ X31 @ X30) @ 
% 2.52/2.71              (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ X29)))),
% 2.52/2.71      inference('split', [status(esa)], ['417'])).
% 2.52/2.71  thf('475', plain,
% 2.52/2.71      (((m1_subset_1 @ sk_E_1 @ 
% 2.52/2.71         (k1_zfmisc_1 @ 
% 2.52/2.71          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) | 
% 2.52/2.71       ~ ((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) | ~ ((r1_tsep_1 @ sk_B @ sk_C))),
% 2.52/2.71      inference('split', [status(esa)], ['33'])).
% 2.52/2.71  thf('476', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 2.52/2.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.71  thf('477', plain, (((v1_funct_1 @ sk_F)) <= (((v1_funct_1 @ sk_F)))),
% 2.52/2.71      inference('split', [status(esa)], ['20'])).
% 2.52/2.71  thf('478', plain,
% 2.52/2.71      (((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1)))
% 2.52/2.71         <= (((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.71               (u1_struct_0 @ sk_D_1))))),
% 2.52/2.71      inference('split', [status(esa)], ['22'])).
% 2.52/2.71  thf('479', plain,
% 2.52/2.71      (((m1_subset_1 @ sk_F @ 
% 2.52/2.71         (k1_zfmisc_1 @ 
% 2.52/2.71          (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1)))))
% 2.52/2.71         <= (((m1_subset_1 @ sk_F @ 
% 2.52/2.71               (k1_zfmisc_1 @ 
% 2.52/2.71                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))))),
% 2.52/2.71      inference('split', [status(esa)], ['24'])).
% 2.52/2.71  thf('480', plain, (((v1_funct_1 @ sk_E_1)) <= (((v1_funct_1 @ sk_E_1)))),
% 2.52/2.71      inference('split', [status(esa)], ['10'])).
% 2.52/2.71  thf('481', plain, (((v2_pre_topc @ sk_D_1)) <= (((v2_pre_topc @ sk_D_1)))),
% 2.52/2.71      inference('split', [status(esa)], ['28'])).
% 2.52/2.71  thf('482', plain, (((l1_pre_topc @ sk_D_1)) <= (((l1_pre_topc @ sk_D_1)))),
% 2.52/2.71      inference('split', [status(esa)], ['26'])).
% 2.52/2.71  thf('483', plain,
% 2.52/2.71      (((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1)))
% 2.52/2.71         <= (((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71               (u1_struct_0 @ sk_D_1))))),
% 2.52/2.71      inference('split', [status(esa)], ['31'])).
% 2.52/2.71  thf('484', plain,
% 2.52/2.71      (((m1_subset_1 @ sk_E_1 @ 
% 2.52/2.71         (k1_zfmisc_1 @ 
% 2.52/2.71          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1)))))
% 2.52/2.71         <= (((m1_subset_1 @ sk_E_1 @ 
% 2.52/2.71               (k1_zfmisc_1 @ 
% 2.52/2.71                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))))),
% 2.52/2.71      inference('split', [status(esa)], ['33'])).
% 2.52/2.71  thf('485', plain,
% 2.52/2.71      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 2.52/2.71         (~ (m1_subset_1 @ X4 @ 
% 2.52/2.71             (k1_zfmisc_1 @ 
% 2.52/2.71              (k2_zfmisc_1 @ (u1_struct_0 @ X5) @ (u1_struct_0 @ X6))))
% 2.52/2.71          | ~ (v1_funct_2 @ X4 @ (u1_struct_0 @ X5) @ (u1_struct_0 @ X6))
% 2.52/2.71          | ~ (v1_funct_1 @ X4)
% 2.52/2.71          | ~ (m1_pre_topc @ X7 @ X8)
% 2.52/2.71          | (v2_struct_0 @ X7)
% 2.52/2.71          | ~ (m1_pre_topc @ X5 @ X8)
% 2.52/2.71          | (v2_struct_0 @ X5)
% 2.52/2.71          | ~ (l1_pre_topc @ X6)
% 2.52/2.71          | ~ (v2_pre_topc @ X6)
% 2.52/2.71          | (v2_struct_0 @ X6)
% 2.52/2.71          | ~ (l1_pre_topc @ X8)
% 2.52/2.71          | ~ (v2_pre_topc @ X8)
% 2.52/2.71          | (v2_struct_0 @ X8)
% 2.52/2.71          | ~ (v1_funct_1 @ X9)
% 2.52/2.71          | ~ (v1_funct_2 @ X9 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X6))
% 2.52/2.71          | ~ (m1_subset_1 @ X9 @ 
% 2.52/2.71               (k1_zfmisc_1 @ 
% 2.52/2.71                (k2_zfmisc_1 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X6))))
% 2.52/2.71          | (v1_funct_1 @ (k10_tmap_1 @ X8 @ X6 @ X5 @ X7 @ X4 @ X9)))),
% 2.52/2.71      inference('cnf', [status(esa)], [dt_k10_tmap_1])).
% 2.52/2.71  thf('486', plain,
% 2.52/2.71      ((![X0 : $i, X1 : $i, X2 : $i]:
% 2.52/2.71          ((v1_funct_1 @ (k10_tmap_1 @ X2 @ sk_D_1 @ sk_B @ X1 @ sk_E_1 @ X0))
% 2.52/2.71           | ~ (m1_subset_1 @ X0 @ 
% 2.52/2.71                (k1_zfmisc_1 @ 
% 2.52/2.71                 (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_D_1))))
% 2.52/2.71           | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_D_1))
% 2.52/2.71           | ~ (v1_funct_1 @ X0)
% 2.52/2.71           | (v2_struct_0 @ X2)
% 2.52/2.71           | ~ (v2_pre_topc @ X2)
% 2.52/2.71           | ~ (l1_pre_topc @ X2)
% 2.52/2.71           | (v2_struct_0 @ sk_D_1)
% 2.52/2.71           | ~ (v2_pre_topc @ sk_D_1)
% 2.52/2.71           | ~ (l1_pre_topc @ sk_D_1)
% 2.52/2.71           | (v2_struct_0 @ sk_B)
% 2.52/2.71           | ~ (m1_pre_topc @ sk_B @ X2)
% 2.52/2.71           | (v2_struct_0 @ X1)
% 2.52/2.71           | ~ (m1_pre_topc @ X1 @ X2)
% 2.52/2.71           | ~ (v1_funct_1 @ sk_E_1)
% 2.52/2.71           | ~ (v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71                (u1_struct_0 @ sk_D_1))))
% 2.52/2.71         <= (((m1_subset_1 @ sk_E_1 @ 
% 2.52/2.71               (k1_zfmisc_1 @ 
% 2.52/2.71                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))))),
% 2.52/2.71      inference('sup-', [status(thm)], ['484', '485'])).
% 2.52/2.71  thf('487', plain,
% 2.52/2.71      ((![X0 : $i, X1 : $i, X2 : $i]:
% 2.52/2.71          (~ (v1_funct_1 @ sk_E_1)
% 2.52/2.71           | ~ (m1_pre_topc @ X1 @ X0)
% 2.52/2.71           | (v2_struct_0 @ X1)
% 2.52/2.71           | ~ (m1_pre_topc @ sk_B @ X0)
% 2.52/2.71           | (v2_struct_0 @ sk_B)
% 2.52/2.71           | ~ (l1_pre_topc @ sk_D_1)
% 2.52/2.71           | ~ (v2_pre_topc @ sk_D_1)
% 2.52/2.71           | (v2_struct_0 @ sk_D_1)
% 2.52/2.71           | ~ (l1_pre_topc @ X0)
% 2.52/2.71           | ~ (v2_pre_topc @ X0)
% 2.52/2.71           | (v2_struct_0 @ X0)
% 2.52/2.71           | ~ (v1_funct_1 @ X2)
% 2.52/2.71           | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_D_1))
% 2.52/2.71           | ~ (m1_subset_1 @ X2 @ 
% 2.52/2.71                (k1_zfmisc_1 @ 
% 2.52/2.71                 (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_D_1))))
% 2.52/2.71           | (v1_funct_1 @ (k10_tmap_1 @ X0 @ sk_D_1 @ sk_B @ X1 @ sk_E_1 @ X2))))
% 2.52/2.71         <= (((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71               (u1_struct_0 @ sk_D_1))) & 
% 2.52/2.71             ((m1_subset_1 @ sk_E_1 @ 
% 2.52/2.71               (k1_zfmisc_1 @ 
% 2.52/2.71                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))))),
% 2.52/2.71      inference('sup-', [status(thm)], ['483', '486'])).
% 2.52/2.71  thf('488', plain,
% 2.52/2.71      ((![X0 : $i, X1 : $i, X2 : $i]:
% 2.52/2.71          ((v1_funct_1 @ (k10_tmap_1 @ X2 @ sk_D_1 @ sk_B @ X1 @ sk_E_1 @ X0))
% 2.52/2.71           | ~ (m1_subset_1 @ X0 @ 
% 2.52/2.71                (k1_zfmisc_1 @ 
% 2.52/2.71                 (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_D_1))))
% 2.52/2.71           | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_D_1))
% 2.52/2.71           | ~ (v1_funct_1 @ X0)
% 2.52/2.71           | (v2_struct_0 @ X2)
% 2.52/2.71           | ~ (v2_pre_topc @ X2)
% 2.52/2.71           | ~ (l1_pre_topc @ X2)
% 2.52/2.71           | (v2_struct_0 @ sk_D_1)
% 2.52/2.71           | ~ (v2_pre_topc @ sk_D_1)
% 2.52/2.71           | (v2_struct_0 @ sk_B)
% 2.52/2.71           | ~ (m1_pre_topc @ sk_B @ X2)
% 2.52/2.71           | (v2_struct_0 @ X1)
% 2.52/2.71           | ~ (m1_pre_topc @ X1 @ X2)
% 2.52/2.71           | ~ (v1_funct_1 @ sk_E_1)))
% 2.52/2.71         <= (((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71               (u1_struct_0 @ sk_D_1))) & 
% 2.52/2.71             ((m1_subset_1 @ sk_E_1 @ 
% 2.52/2.71               (k1_zfmisc_1 @ 
% 2.52/2.71                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.71             ((l1_pre_topc @ sk_D_1)))),
% 2.52/2.71      inference('sup-', [status(thm)], ['482', '487'])).
% 2.52/2.71  thf('489', plain,
% 2.52/2.71      ((![X0 : $i, X1 : $i, X2 : $i]:
% 2.52/2.71          (~ (v1_funct_1 @ sk_E_1)
% 2.52/2.71           | ~ (m1_pre_topc @ X1 @ X0)
% 2.52/2.71           | (v2_struct_0 @ X1)
% 2.52/2.71           | ~ (m1_pre_topc @ sk_B @ X0)
% 2.52/2.71           | (v2_struct_0 @ sk_B)
% 2.52/2.71           | (v2_struct_0 @ sk_D_1)
% 2.52/2.71           | ~ (l1_pre_topc @ X0)
% 2.52/2.71           | ~ (v2_pre_topc @ X0)
% 2.52/2.71           | (v2_struct_0 @ X0)
% 2.52/2.71           | ~ (v1_funct_1 @ X2)
% 2.52/2.71           | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_D_1))
% 2.52/2.71           | ~ (m1_subset_1 @ X2 @ 
% 2.52/2.71                (k1_zfmisc_1 @ 
% 2.52/2.71                 (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_D_1))))
% 2.52/2.71           | (v1_funct_1 @ (k10_tmap_1 @ X0 @ sk_D_1 @ sk_B @ X1 @ sk_E_1 @ X2))))
% 2.52/2.71         <= (((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71               (u1_struct_0 @ sk_D_1))) & 
% 2.52/2.71             ((m1_subset_1 @ sk_E_1 @ 
% 2.52/2.71               (k1_zfmisc_1 @ 
% 2.52/2.71                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.71             ((l1_pre_topc @ sk_D_1)) & 
% 2.52/2.71             ((v2_pre_topc @ sk_D_1)))),
% 2.52/2.71      inference('sup-', [status(thm)], ['481', '488'])).
% 2.52/2.71  thf('490', plain,
% 2.52/2.71      ((![X0 : $i, X1 : $i, X2 : $i]:
% 2.52/2.71          ((v1_funct_1 @ (k10_tmap_1 @ X2 @ sk_D_1 @ sk_B @ X1 @ sk_E_1 @ X0))
% 2.52/2.71           | ~ (m1_subset_1 @ X0 @ 
% 2.52/2.71                (k1_zfmisc_1 @ 
% 2.52/2.71                 (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_D_1))))
% 2.52/2.71           | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_D_1))
% 2.52/2.71           | ~ (v1_funct_1 @ X0)
% 2.52/2.71           | (v2_struct_0 @ X2)
% 2.52/2.71           | ~ (v2_pre_topc @ X2)
% 2.52/2.71           | ~ (l1_pre_topc @ X2)
% 2.52/2.71           | (v2_struct_0 @ sk_D_1)
% 2.52/2.71           | (v2_struct_0 @ sk_B)
% 2.52/2.71           | ~ (m1_pre_topc @ sk_B @ X2)
% 2.52/2.71           | (v2_struct_0 @ X1)
% 2.52/2.71           | ~ (m1_pre_topc @ X1 @ X2)))
% 2.52/2.71         <= (((v1_funct_1 @ sk_E_1)) & 
% 2.52/2.71             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71               (u1_struct_0 @ sk_D_1))) & 
% 2.52/2.71             ((m1_subset_1 @ sk_E_1 @ 
% 2.52/2.71               (k1_zfmisc_1 @ 
% 2.52/2.71                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.71             ((l1_pre_topc @ sk_D_1)) & 
% 2.52/2.71             ((v2_pre_topc @ sk_D_1)))),
% 2.52/2.71      inference('sup-', [status(thm)], ['480', '489'])).
% 2.52/2.71  thf('491', plain,
% 2.52/2.71      ((![X0 : $i]:
% 2.52/2.71          (~ (m1_pre_topc @ sk_C @ X0)
% 2.52/2.71           | (v2_struct_0 @ sk_C)
% 2.52/2.71           | ~ (m1_pre_topc @ sk_B @ X0)
% 2.52/2.71           | (v2_struct_0 @ sk_B)
% 2.52/2.71           | (v2_struct_0 @ sk_D_1)
% 2.52/2.71           | ~ (l1_pre_topc @ X0)
% 2.52/2.71           | ~ (v2_pre_topc @ X0)
% 2.52/2.71           | (v2_struct_0 @ X0)
% 2.52/2.71           | ~ (v1_funct_1 @ sk_F)
% 2.52/2.71           | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.71                (u1_struct_0 @ sk_D_1))
% 2.52/2.71           | (v1_funct_1 @ 
% 2.52/2.71              (k10_tmap_1 @ X0 @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F))))
% 2.52/2.71         <= (((v1_funct_1 @ sk_E_1)) & 
% 2.52/2.71             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71               (u1_struct_0 @ sk_D_1))) & 
% 2.52/2.71             ((m1_subset_1 @ sk_E_1 @ 
% 2.52/2.71               (k1_zfmisc_1 @ 
% 2.52/2.71                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.71             ((m1_subset_1 @ sk_F @ 
% 2.52/2.71               (k1_zfmisc_1 @ 
% 2.52/2.71                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.71             ((l1_pre_topc @ sk_D_1)) & 
% 2.52/2.71             ((v2_pre_topc @ sk_D_1)))),
% 2.52/2.71      inference('sup-', [status(thm)], ['479', '490'])).
% 2.52/2.71  thf('492', plain,
% 2.52/2.71      ((![X0 : $i]:
% 2.52/2.71          ((v1_funct_1 @ 
% 2.52/2.71            (k10_tmap_1 @ X0 @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F))
% 2.52/2.71           | ~ (v1_funct_1 @ sk_F)
% 2.52/2.71           | (v2_struct_0 @ X0)
% 2.52/2.71           | ~ (v2_pre_topc @ X0)
% 2.52/2.71           | ~ (l1_pre_topc @ X0)
% 2.52/2.71           | (v2_struct_0 @ sk_D_1)
% 2.52/2.71           | (v2_struct_0 @ sk_B)
% 2.52/2.71           | ~ (m1_pre_topc @ sk_B @ X0)
% 2.52/2.71           | (v2_struct_0 @ sk_C)
% 2.52/2.71           | ~ (m1_pre_topc @ sk_C @ X0)))
% 2.52/2.71         <= (((v1_funct_1 @ sk_E_1)) & 
% 2.52/2.71             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71               (u1_struct_0 @ sk_D_1))) & 
% 2.52/2.71             ((m1_subset_1 @ sk_E_1 @ 
% 2.52/2.71               (k1_zfmisc_1 @ 
% 2.52/2.71                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.71             ((m1_subset_1 @ sk_F @ 
% 2.52/2.71               (k1_zfmisc_1 @ 
% 2.52/2.71                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.71             ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.71               (u1_struct_0 @ sk_D_1))) & 
% 2.52/2.71             ((l1_pre_topc @ sk_D_1)) & 
% 2.52/2.71             ((v2_pre_topc @ sk_D_1)))),
% 2.52/2.71      inference('sup-', [status(thm)], ['478', '491'])).
% 2.52/2.71  thf('493', plain,
% 2.52/2.71      ((![X0 : $i]:
% 2.52/2.71          (~ (m1_pre_topc @ sk_C @ X0)
% 2.52/2.71           | (v2_struct_0 @ sk_C)
% 2.52/2.71           | ~ (m1_pre_topc @ sk_B @ X0)
% 2.52/2.71           | (v2_struct_0 @ sk_B)
% 2.52/2.71           | (v2_struct_0 @ sk_D_1)
% 2.52/2.71           | ~ (l1_pre_topc @ X0)
% 2.52/2.71           | ~ (v2_pre_topc @ X0)
% 2.52/2.71           | (v2_struct_0 @ X0)
% 2.52/2.71           | (v1_funct_1 @ 
% 2.52/2.71              (k10_tmap_1 @ X0 @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F))))
% 2.52/2.71         <= (((v1_funct_1 @ sk_E_1)) & 
% 2.52/2.71             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71               (u1_struct_0 @ sk_D_1))) & 
% 2.52/2.71             ((m1_subset_1 @ sk_E_1 @ 
% 2.52/2.71               (k1_zfmisc_1 @ 
% 2.52/2.71                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.71             ((m1_subset_1 @ sk_F @ 
% 2.52/2.71               (k1_zfmisc_1 @ 
% 2.52/2.71                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.71             ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.71               (u1_struct_0 @ sk_D_1))) & 
% 2.52/2.71             ((v1_funct_1 @ sk_F)) & 
% 2.52/2.71             ((l1_pre_topc @ sk_D_1)) & 
% 2.52/2.71             ((v2_pre_topc @ sk_D_1)))),
% 2.52/2.71      inference('sup-', [status(thm)], ['477', '492'])).
% 2.52/2.71  thf('494', plain,
% 2.52/2.71      ((((v1_funct_1 @ 
% 2.52/2.71          (k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F))
% 2.52/2.71         | (v2_struct_0 @ sk_A)
% 2.52/2.71         | ~ (v2_pre_topc @ sk_A)
% 2.52/2.71         | ~ (l1_pre_topc @ sk_A)
% 2.52/2.71         | (v2_struct_0 @ sk_D_1)
% 2.52/2.71         | (v2_struct_0 @ sk_B)
% 2.52/2.71         | ~ (m1_pre_topc @ sk_B @ sk_A)
% 2.52/2.71         | (v2_struct_0 @ sk_C)))
% 2.52/2.71         <= (((v1_funct_1 @ sk_E_1)) & 
% 2.52/2.71             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71               (u1_struct_0 @ sk_D_1))) & 
% 2.52/2.71             ((m1_subset_1 @ sk_E_1 @ 
% 2.52/2.71               (k1_zfmisc_1 @ 
% 2.52/2.71                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.71             ((m1_subset_1 @ sk_F @ 
% 2.52/2.71               (k1_zfmisc_1 @ 
% 2.52/2.71                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.71             ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.71               (u1_struct_0 @ sk_D_1))) & 
% 2.52/2.71             ((v1_funct_1 @ sk_F)) & 
% 2.52/2.71             ((l1_pre_topc @ sk_D_1)) & 
% 2.52/2.71             ((v2_pre_topc @ sk_D_1)))),
% 2.52/2.71      inference('sup-', [status(thm)], ['476', '493'])).
% 2.52/2.71  thf('495', plain, ((v2_pre_topc @ sk_A)),
% 2.52/2.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.71  thf('496', plain, ((l1_pre_topc @ sk_A)),
% 2.52/2.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.71  thf('497', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 2.52/2.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.71  thf('498', plain,
% 2.52/2.71      ((((v1_funct_1 @ 
% 2.52/2.71          (k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F))
% 2.52/2.71         | (v2_struct_0 @ sk_A)
% 2.52/2.71         | (v2_struct_0 @ sk_D_1)
% 2.52/2.71         | (v2_struct_0 @ sk_B)
% 2.52/2.71         | (v2_struct_0 @ sk_C)))
% 2.52/2.71         <= (((v1_funct_1 @ sk_E_1)) & 
% 2.52/2.71             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71               (u1_struct_0 @ sk_D_1))) & 
% 2.52/2.71             ((m1_subset_1 @ sk_E_1 @ 
% 2.52/2.71               (k1_zfmisc_1 @ 
% 2.52/2.71                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.71             ((m1_subset_1 @ sk_F @ 
% 2.52/2.71               (k1_zfmisc_1 @ 
% 2.52/2.71                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.71             ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.71               (u1_struct_0 @ sk_D_1))) & 
% 2.52/2.71             ((v1_funct_1 @ sk_F)) & 
% 2.52/2.71             ((l1_pre_topc @ sk_D_1)) & 
% 2.52/2.71             ((v2_pre_topc @ sk_D_1)))),
% 2.52/2.71      inference('demod', [status(thm)], ['494', '495', '496', '497'])).
% 2.52/2.71  thf('499', plain,
% 2.52/2.71      ((~ (v1_funct_1 @ 
% 2.52/2.71           (k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F)))
% 2.52/2.71         <= (~
% 2.52/2.71             ((v1_funct_1 @ 
% 2.52/2.71               (k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F))))),
% 2.52/2.71      inference('split', [status(esa)], ['49'])).
% 2.52/2.71  thf('500', plain,
% 2.52/2.71      ((((v2_struct_0 @ sk_C)
% 2.52/2.71         | (v2_struct_0 @ sk_B)
% 2.52/2.71         | (v2_struct_0 @ sk_D_1)
% 2.52/2.71         | (v2_struct_0 @ sk_A)))
% 2.52/2.71         <= (~
% 2.52/2.71             ((v1_funct_1 @ 
% 2.52/2.71               (k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F))) & 
% 2.52/2.71             ((v1_funct_1 @ sk_E_1)) & 
% 2.52/2.71             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71               (u1_struct_0 @ sk_D_1))) & 
% 2.52/2.71             ((m1_subset_1 @ sk_E_1 @ 
% 2.52/2.71               (k1_zfmisc_1 @ 
% 2.52/2.71                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.71             ((m1_subset_1 @ sk_F @ 
% 2.52/2.71               (k1_zfmisc_1 @ 
% 2.52/2.71                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.71             ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.71               (u1_struct_0 @ sk_D_1))) & 
% 2.52/2.71             ((v1_funct_1 @ sk_F)) & 
% 2.52/2.71             ((l1_pre_topc @ sk_D_1)) & 
% 2.52/2.71             ((v2_pre_topc @ sk_D_1)))),
% 2.52/2.71      inference('sup-', [status(thm)], ['498', '499'])).
% 2.52/2.71  thf('501', plain,
% 2.52/2.71      ((~ (v2_struct_0 @ sk_D_1)) <= (~ ((v2_struct_0 @ sk_D_1)))),
% 2.52/2.71      inference('split', [status(esa)], ['52'])).
% 2.52/2.71  thf('502', plain,
% 2.52/2.71      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C)))
% 2.52/2.71         <= (~ ((v2_struct_0 @ sk_D_1)) & 
% 2.52/2.71             ~
% 2.52/2.71             ((v1_funct_1 @ 
% 2.52/2.71               (k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F))) & 
% 2.52/2.71             ((v1_funct_1 @ sk_E_1)) & 
% 2.52/2.71             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71               (u1_struct_0 @ sk_D_1))) & 
% 2.52/2.71             ((m1_subset_1 @ sk_E_1 @ 
% 2.52/2.71               (k1_zfmisc_1 @ 
% 2.52/2.71                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.71             ((m1_subset_1 @ sk_F @ 
% 2.52/2.71               (k1_zfmisc_1 @ 
% 2.52/2.71                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.71             ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.71               (u1_struct_0 @ sk_D_1))) & 
% 2.52/2.71             ((v1_funct_1 @ sk_F)) & 
% 2.52/2.71             ((l1_pre_topc @ sk_D_1)) & 
% 2.52/2.71             ((v2_pre_topc @ sk_D_1)))),
% 2.52/2.71      inference('sup-', [status(thm)], ['500', '501'])).
% 2.52/2.71  thf('503', plain, (~ (v2_struct_0 @ sk_A)),
% 2.52/2.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.71  thf('504', plain,
% 2.52/2.71      ((((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B)))
% 2.52/2.71         <= (~ ((v2_struct_0 @ sk_D_1)) & 
% 2.52/2.71             ~
% 2.52/2.71             ((v1_funct_1 @ 
% 2.52/2.71               (k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F))) & 
% 2.52/2.71             ((v1_funct_1 @ sk_E_1)) & 
% 2.52/2.71             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71               (u1_struct_0 @ sk_D_1))) & 
% 2.52/2.71             ((m1_subset_1 @ sk_E_1 @ 
% 2.52/2.71               (k1_zfmisc_1 @ 
% 2.52/2.71                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.71             ((m1_subset_1 @ sk_F @ 
% 2.52/2.71               (k1_zfmisc_1 @ 
% 2.52/2.71                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.71             ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.71               (u1_struct_0 @ sk_D_1))) & 
% 2.52/2.71             ((v1_funct_1 @ sk_F)) & 
% 2.52/2.71             ((l1_pre_topc @ sk_D_1)) & 
% 2.52/2.71             ((v2_pre_topc @ sk_D_1)))),
% 2.52/2.71      inference('clc', [status(thm)], ['502', '503'])).
% 2.52/2.71  thf('505', plain, (~ (v2_struct_0 @ sk_C)),
% 2.52/2.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.71  thf('506', plain,
% 2.52/2.71      (((v2_struct_0 @ sk_B))
% 2.52/2.71         <= (~ ((v2_struct_0 @ sk_D_1)) & 
% 2.52/2.71             ~
% 2.52/2.71             ((v1_funct_1 @ 
% 2.52/2.71               (k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F))) & 
% 2.52/2.71             ((v1_funct_1 @ sk_E_1)) & 
% 2.52/2.71             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.52/2.71               (u1_struct_0 @ sk_D_1))) & 
% 2.52/2.71             ((m1_subset_1 @ sk_E_1 @ 
% 2.52/2.71               (k1_zfmisc_1 @ 
% 2.52/2.71                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.71             ((m1_subset_1 @ sk_F @ 
% 2.52/2.71               (k1_zfmisc_1 @ 
% 2.52/2.71                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.52/2.71             ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.52/2.71               (u1_struct_0 @ sk_D_1))) & 
% 2.52/2.71             ((v1_funct_1 @ sk_F)) & 
% 2.52/2.71             ((l1_pre_topc @ sk_D_1)) & 
% 2.52/2.71             ((v2_pre_topc @ sk_D_1)))),
% 2.52/2.71      inference('clc', [status(thm)], ['504', '505'])).
% 2.52/2.71  thf('507', plain, (~ (v2_struct_0 @ sk_B)),
% 2.52/2.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.71  thf('508', plain,
% 2.52/2.71      (((v1_funct_1 @ 
% 2.52/2.71         (k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F))) | 
% 2.52/2.71       ~
% 2.52/2.71       ((m1_subset_1 @ sk_E_1 @ 
% 2.52/2.71         (k1_zfmisc_1 @ 
% 2.52/2.71          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) | 
% 2.52/2.71       ~ ((v2_pre_topc @ sk_D_1)) | ~ ((v1_funct_1 @ sk_F)) | 
% 2.52/2.71       ~ ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))) | 
% 2.52/2.71       ~
% 2.52/2.71       ((m1_subset_1 @ sk_F @ 
% 2.52/2.71         (k1_zfmisc_1 @ 
% 2.52/2.71          (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) | 
% 2.52/2.71       ~
% 2.52/2.71       ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))) | 
% 2.52/2.71       ~ ((v1_funct_1 @ sk_E_1)) | ~ ((l1_pre_topc @ sk_D_1)) | 
% 2.52/2.71       ((v2_struct_0 @ sk_D_1))),
% 2.52/2.71      inference('sup-', [status(thm)], ['506', '507'])).
% 2.52/2.71  thf('509', plain,
% 2.52/2.71      (~
% 2.52/2.71       ((v1_funct_1 @ 
% 2.52/2.71         (k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F))) | 
% 2.52/2.71       ~
% 2.52/2.71       ((m1_subset_1 @ 
% 2.52/2.71         (k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F) @ 
% 2.52/2.71         (k1_zfmisc_1 @ 
% 2.52/2.71          (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.52/2.71           (u1_struct_0 @ sk_D_1))))) | 
% 2.52/2.71       ~ ((r1_tsep_1 @ sk_B @ sk_C)) | ~ ((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) | 
% 2.52/2.71       ~
% 2.52/2.71       ((v1_funct_2 @ 
% 2.52/2.71         (k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F) @ 
% 2.52/2.71         (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.52/2.71         (u1_struct_0 @ sk_D_1))) | 
% 2.52/2.71       ~
% 2.52/2.71       ((v5_pre_topc @ 
% 2.52/2.71         (k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F) @ 
% 2.52/2.71         (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D_1))),
% 2.52/2.71      inference('split', [status(esa)], ['49'])).
% 2.52/2.71  thf('510', plain, ($false),
% 2.52/2.71      inference('sat_resolution*', [status(thm)],
% 2.52/2.71                ['1', '18', '60', '93', '144', '145', '146', '147', '148', 
% 2.52/2.71                 '149', '150', '151', '152', '153', '154', '473', '474', 
% 2.52/2.71                 '475', '508', '509'])).
% 2.52/2.71  
% 2.52/2.71  % SZS output end Refutation
% 2.52/2.71  
% 2.52/2.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
