%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7IaM9m5gdj

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:05 EST 2020

% Result     : Theorem 0.17s
% Output     : Refutation 0.17s
% Verified   : 
% Statistics : Number of formulae       :  181 ( 811 expanded)
%              Number of leaves         :   32 ( 232 expanded)
%              Depth                    :   32
%              Number of atoms          : 2569 (38421 expanded)
%              Number of equality atoms :   26 (1230 expanded)
%              Maximal formula depth    :   31 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(k1_tsep_1_type,type,(
    k1_tsep_1: $i > $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t125_tmap_1,conjecture,(
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
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( m1_pre_topc @ D @ A ) )
                 => ! [E: $i] :
                      ( ( ~ ( v2_struct_0 @ E )
                        & ( m1_pre_topc @ E @ A ) )
                     => ( ( A
                          = ( k1_tsep_1 @ A @ D @ E ) )
                       => ! [F: $i] :
                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ A ) )
                           => ! [G: $i] :
                                ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) )
                               => ! [H: $i] :
                                    ( ( m1_subset_1 @ H @ ( u1_struct_0 @ E ) )
                                   => ( ( ( F = G )
                                        & ( F = H ) )
                                     => ( ( r1_tmap_1 @ A @ B @ C @ F )
                                      <=> ( ( r1_tmap_1 @ D @ B @ ( k2_tmap_1 @ A @ B @ C @ D ) @ G )
                                          & ( r1_tmap_1 @ E @ B @ ( k2_tmap_1 @ A @ B @ C @ E ) @ H ) ) ) ) ) ) ) ) ) ) ) ) ) )).

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
                ( ( ( v1_funct_1 @ C )
                  & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
               => ! [D: $i] :
                    ( ( ~ ( v2_struct_0 @ D )
                      & ( m1_pre_topc @ D @ A ) )
                   => ! [E: $i] :
                        ( ( ~ ( v2_struct_0 @ E )
                          & ( m1_pre_topc @ E @ A ) )
                       => ( ( A
                            = ( k1_tsep_1 @ A @ D @ E ) )
                         => ! [F: $i] :
                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ A ) )
                             => ! [G: $i] :
                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) )
                                 => ! [H: $i] :
                                      ( ( m1_subset_1 @ H @ ( u1_struct_0 @ E ) )
                                     => ( ( ( F = G )
                                          & ( F = H ) )
                                       => ( ( r1_tmap_1 @ A @ B @ C @ F )
                                        <=> ( ( r1_tmap_1 @ D @ B @ ( k2_tmap_1 @ A @ B @ C @ D ) @ G )
                                            & ( r1_tmap_1 @ E @ B @ ( k2_tmap_1 @ A @ B @ C @ E ) @ H ) ) ) ) ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t125_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(existence_m1_connsp_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ? [C: $i] :
          ( m1_connsp_2 @ C @ A @ B ) ) )).

thf('4',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X9 ) )
      | ( m1_connsp_2 @ ( sk_C @ X10 @ X9 ) @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[existence_m1_connsp_2])).

thf('5',plain,
    ( ( m1_connsp_2 @ ( sk_C @ sk_G @ sk_A ) @ sk_A @ sk_G )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( m1_connsp_2 @ ( sk_C @ sk_G @ sk_A ) @ sk_A @ sk_G )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('9',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_connsp_2 @ ( sk_C @ sk_G @ sk_A ) @ sk_A @ sk_G ),
    inference(clc,[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(dt_m1_connsp_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_connsp_2 @ C @ A @ B )
         => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('12',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( l1_pre_topc @ X6 )
      | ~ ( v2_pre_topc @ X6 )
      | ( v2_struct_0 @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X6 ) )
      | ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( m1_connsp_2 @ X8 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_connsp_2])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( m1_connsp_2 @ X0 @ sk_A @ sk_G )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( m1_connsp_2 @ X0 @ sk_A @ sk_G )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_connsp_2 @ X0 @ sk_A @ sk_G ) ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ ( sk_C @ sk_G @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','18'])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('20',plain,(
    ! [X19: $i] :
      ( ( m1_pre_topc @ X19 @ X19 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('21',plain,
    ( ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_E ) @ sk_H )
    | ( r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_E ) @ sk_H )
   <= ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_E ) @ sk_H ) ),
    inference(split,[status(esa)],['21'])).

thf('23',plain,(
    sk_F = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    sk_H = sk_G ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_E ) @ sk_G )
   <= ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_E ) @ sk_H ) ),
    inference(demod,[status(thm)],['22','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) @ sk_G )
    | ( r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_F )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_F ) ),
    inference(split,[status(esa)],['28'])).

thf('30',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_F ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t64_tmap_1,axiom,(
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
             => ! [D: $i] :
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( m1_pre_topc @ D @ B ) )
                 => ! [E: $i] :
                      ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) )
                     => ! [F: $i] :
                          ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) )
                         => ( ( ( E = F )
                              & ( r1_tmap_1 @ B @ A @ C @ E ) )
                           => ( r1_tmap_1 @ D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) )).

thf('33',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( v2_struct_0 @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ~ ( l1_pre_topc @ X20 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_pre_topc @ X21 @ X20 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X21 ) )
      | ( r1_tmap_1 @ X21 @ X23 @ ( k2_tmap_1 @ X20 @ X23 @ X24 @ X21 ) @ X22 )
      | ( X25 != X22 )
      | ~ ( r1_tmap_1 @ X20 @ X23 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X20 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X23 ) ) ) )
      | ~ ( v1_funct_2 @ X24 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X23 ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t64_tmap_1])).

thf('34',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( v2_struct_0 @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_2 @ X24 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X23 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X23 ) ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X20 ) )
      | ~ ( r1_tmap_1 @ X20 @ X23 @ X24 @ X22 )
      | ( r1_tmap_1 @ X21 @ X23 @ ( k2_tmap_1 @ X20 @ X23 @ X24 @ X21 ) @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X21 ) )
      | ~ ( m1_pre_topc @ X21 @ X20 )
      | ( v2_struct_0 @ X21 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ X0 ) @ X1 )
      | ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['32','34'])).

thf('36',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ X0 ) @ X1 )
      | ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['35','36','37','38','39','40','41'])).

thf('43',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_A ) )
        | ( r1_tmap_1 @ X0 @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ X0 ) @ sk_G )
        | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ X0 ) )
        | ~ ( m1_pre_topc @ X0 @ sk_A )
        | ( v2_struct_0 @ X0 )
        | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_F ) ),
    inference('sup-',[status(thm)],['31','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('45',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( r1_tmap_1 @ X0 @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ X0 ) @ sk_G )
        | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ X0 ) )
        | ~ ( m1_pre_topc @ X0 @ sk_A )
        | ( v2_struct_0 @ X0 )
        | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_F ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) @ sk_G )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_F ) ),
    inference('sup-',[status(thm)],['27','45'])).

thf('47',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) @ sk_G )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_F ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ~ ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_E ) @ sk_H )
    | ~ ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) @ sk_G )
   <= ~ ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) @ sk_G ) ),
    inference(split,[status(esa)],['49'])).

thf('51',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) @ sk_G )
      & ( r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['48','50'])).

thf('52',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) @ sk_G )
      & ( r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_F ) ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( v2_struct_0 @ sk_D )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) @ sk_G )
      & ( r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_F ) ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('56',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_F ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) @ sk_G )
   <= ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) @ sk_G ) ),
    inference(split,[status(esa)],['28'])).

thf('59',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    sk_H = sk_G ),
    inference('sup+',[status(thm)],['23','24'])).

thf('61',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_E ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( r1_tmap_1 @ X0 @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ X0 ) @ sk_G )
        | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ X0 ) )
        | ~ ( m1_pre_topc @ X0 @ sk_A )
        | ( v2_struct_0 @ X0 )
        | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_F ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('63',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E )
      | ~ ( m1_pre_topc @ sk_E @ sk_A )
      | ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_E ) @ sk_G )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_F ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E )
      | ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_E ) @ sk_G )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_F ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ~ ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_E ) @ sk_H )
    | ~ ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    sk_H = sk_G ),
    inference('sup+',[status(thm)],['23','24'])).

thf('68',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ~ ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_E ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G )
      | ~ ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) @ sk_G ) )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_F ) ),
    inference('sup-',[status(thm)],['65','69'])).

thf('71',plain,
    ( ( r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_F ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('72',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) @ sk_G ) )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_F ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_F )
      & ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) @ sk_G ) ) ),
    inference('sup-',[status(thm)],['58','72'])).

thf('74',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_E ) )
   <= ( ( r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_F )
      & ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) @ sk_G ) ) ),
    inference(clc,[status(thm)],['73','74'])).

thf('76',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( v2_struct_0 @ sk_E )
   <= ( ( r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_F )
      & ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) @ sk_G ) ) ),
    inference(clc,[status(thm)],['75','76'])).

thf('78',plain,(
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_F )
    | ~ ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) @ sk_G ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_E ) @ sk_H )
    | ( r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_F ) ),
    inference(split,[status(esa)],['21'])).

thf('81',plain,(
    r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_E ) @ sk_H ),
    inference('sat_resolution*',[status(thm)],['57','79','80'])).

thf('82',plain,(
    r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_E ) @ sk_G ),
    inference(simpl_trail,[status(thm)],['26','81'])).

thf('83',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) @ sk_G )
   <= ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) @ sk_G ) ),
    inference(split,[status(esa)],['28'])).

thf('84',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) @ sk_G )
    | ( r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_F ) ),
    inference(split,[status(esa)],['28'])).

thf('85',plain,(
    r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) @ sk_G ),
    inference('sat_resolution*',[status(thm)],['57','79','84'])).

thf('86',plain,(
    r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) @ sk_G ),
    inference(simpl_trail,[status(thm)],['83','85'])).

thf('87',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t124_tmap_1,axiom,(
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
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( m1_pre_topc @ D @ A ) )
                 => ! [E: $i] :
                      ( ( ~ ( v2_struct_0 @ E )
                        & ( m1_pre_topc @ E @ A ) )
                     => ! [F: $i] :
                          ( ( m1_subset_1 @ F @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ D @ E ) ) )
                         => ! [G: $i] :
                              ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) )
                             => ! [H: $i] :
                                  ( ( m1_subset_1 @ H @ ( u1_struct_0 @ E ) )
                                 => ( ( ( F = G )
                                      & ( F = H ) )
                                   => ( ( r1_tmap_1 @ ( k1_tsep_1 @ A @ D @ E ) @ B @ ( k2_tmap_1 @ A @ B @ C @ ( k1_tsep_1 @ A @ D @ E ) ) @ F )
                                    <=> ( ( r1_tmap_1 @ D @ B @ ( k2_tmap_1 @ A @ B @ C @ D ) @ G )
                                        & ( r1_tmap_1 @ E @ B @ ( k2_tmap_1 @ A @ B @ C @ E ) @ H ) ) ) ) ) ) ) ) ) ) ) ) )).

thf('88',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( v2_struct_0 @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ( v2_struct_0 @ X12 )
      | ~ ( m1_pre_topc @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ ( k1_tsep_1 @ X13 @ X12 @ X15 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X15 ) )
      | ~ ( r1_tmap_1 @ X12 @ X11 @ ( k2_tmap_1 @ X13 @ X11 @ X17 @ X12 ) @ X18 )
      | ~ ( r1_tmap_1 @ X15 @ X11 @ ( k2_tmap_1 @ X13 @ X11 @ X17 @ X15 ) @ X16 )
      | ( r1_tmap_1 @ ( k1_tsep_1 @ X13 @ X12 @ X15 ) @ X11 @ ( k2_tmap_1 @ X13 @ X11 @ X17 @ ( k1_tsep_1 @ X13 @ X12 @ X15 ) ) @ X14 )
      | ( X14 != X16 )
      | ( X14 != X18 )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X12 ) )
      | ~ ( m1_pre_topc @ X15 @ X13 )
      | ( v2_struct_0 @ X15 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X11 ) ) ) )
      | ~ ( v1_funct_2 @ X17 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X11 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t124_tmap_1])).

thf('89',plain,(
    ! [X11: $i,X12: $i,X13: $i,X15: $i,X16: $i,X17: $i] :
      ( ( v2_struct_0 @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_funct_2 @ X17 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X11 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X11 ) ) ) )
      | ( v2_struct_0 @ X15 )
      | ~ ( m1_pre_topc @ X15 @ X13 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X12 ) )
      | ( r1_tmap_1 @ ( k1_tsep_1 @ X13 @ X12 @ X15 ) @ X11 @ ( k2_tmap_1 @ X13 @ X11 @ X17 @ ( k1_tsep_1 @ X13 @ X12 @ X15 ) ) @ X16 )
      | ~ ( r1_tmap_1 @ X15 @ X11 @ ( k2_tmap_1 @ X13 @ X11 @ X17 @ X15 ) @ X16 )
      | ~ ( r1_tmap_1 @ X12 @ X11 @ ( k2_tmap_1 @ X13 @ X11 @ X17 @ X12 ) @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X15 ) )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ ( k1_tsep_1 @ X13 @ X12 @ X15 ) ) )
      | ~ ( m1_pre_topc @ X12 @ X13 )
      | ( v2_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ X0 @ X1 ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_tmap_1 @ X0 @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ X0 ) @ X2 )
      | ~ ( r1_tmap_1 @ X1 @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ X1 ) @ X2 )
      | ( r1_tmap_1 @ ( k1_tsep_1 @ sk_A @ X0 @ X1 ) @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ ( k1_tsep_1 @ sk_A @ X0 @ X1 ) ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['87','89'])).

thf('91',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ X0 @ X1 ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_tmap_1 @ X0 @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ X0 ) @ X2 )
      | ~ ( r1_tmap_1 @ X1 @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ X1 ) @ X2 )
      | ( r1_tmap_1 @ ( k1_tsep_1 @ sk_A @ X0 @ X1 ) @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ ( k1_tsep_1 @ sk_A @ X0 @ X1 ) ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['90','91','92','93','94','95','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_D ) )
      | ( r1_tmap_1 @ ( k1_tsep_1 @ sk_A @ sk_D @ X0 ) @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ ( k1_tsep_1 @ sk_A @ sk_D @ X0 ) ) @ sk_G )
      | ~ ( r1_tmap_1 @ X0 @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ X0 ) @ sk_G )
      | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ X0 ) ) )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['86','97'])).

thf('99',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tmap_1 @ ( k1_tsep_1 @ sk_A @ sk_D @ X0 ) @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ ( k1_tsep_1 @ sk_A @ sk_D @ X0 ) ) @ sk_G )
      | ~ ( r1_tmap_1 @ X0 @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ X0 ) @ sk_G )
      | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ X0 ) ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['98','99','100'])).

thf('102',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
    | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_E ) )
    | ( r1_tmap_1 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ sk_G )
    | ~ ( m1_pre_topc @ sk_E @ sk_A )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['82','101'])).

thf('103',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('105',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_E ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('106',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tmap_1 @ sk_A @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_A ) @ sk_G )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['102','103','104','105','106','107','108'])).

thf('110',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tmap_1,axiom,(
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
             => ! [D: $i] :
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( m1_pre_topc @ D @ B ) )
                 => ! [E: $i] :
                      ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                     => ! [F: $i] :
                          ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) )
                         => ! [G: $i] :
                              ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) )
                             => ( ( ( r1_tarski @ E @ ( u1_struct_0 @ D ) )
                                  & ( m1_connsp_2 @ E @ B @ F )
                                  & ( F = G ) )
                               => ( ( r1_tmap_1 @ B @ A @ C @ F )
                                <=> ( r1_tmap_1 @ D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ G ) ) ) ) ) ) ) ) ) ) )).

thf('111',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( v2_struct_0 @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ~ ( l1_pre_topc @ X26 )
      | ( v2_struct_0 @ X27 )
      | ~ ( m1_pre_topc @ X27 @ X26 )
      | ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X26 ) )
      | ~ ( r1_tarski @ X29 @ ( u1_struct_0 @ X27 ) )
      | ~ ( m1_connsp_2 @ X29 @ X26 @ X28 )
      | ( X28 != X30 )
      | ~ ( r1_tmap_1 @ X27 @ X31 @ ( k2_tmap_1 @ X26 @ X31 @ X32 @ X27 ) @ X30 )
      | ( r1_tmap_1 @ X26 @ X31 @ X32 @ X28 )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X27 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X31 ) ) ) )
      | ~ ( v1_funct_2 @ X32 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X31 ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t65_tmap_1])).

thf('112',plain,(
    ! [X26: $i,X27: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( v2_struct_0 @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_funct_2 @ X32 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X31 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X31 ) ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X27 ) )
      | ( r1_tmap_1 @ X26 @ X31 @ X32 @ X30 )
      | ~ ( r1_tmap_1 @ X27 @ X31 @ ( k2_tmap_1 @ X26 @ X31 @ X32 @ X27 ) @ X30 )
      | ~ ( m1_connsp_2 @ X29 @ X26 @ X30 )
      | ~ ( r1_tarski @ X29 @ ( u1_struct_0 @ X27 ) )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X26 ) )
      | ~ ( m1_pre_topc @ X27 @ X26 )
      | ( v2_struct_0 @ X27 )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_connsp_2 @ X2 @ sk_A @ X1 )
      | ~ ( r1_tmap_1 @ X0 @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ X0 ) @ X1 )
      | ( r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['110','112'])).

thf('114',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_connsp_2 @ X2 @ sk_A @ X1 )
      | ~ ( r1_tmap_1 @ X0 @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ X0 ) @ X1 )
      | ( r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['113','114','115','116','117','118','119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G )
      | ~ ( m1_connsp_2 @ X0 @ sk_A @ sk_G )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_pre_topc @ sk_A @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['109','120'])).

thf('122',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('123',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G )
      | ~ ( m1_connsp_2 @ X0 @ sk_A @ sk_G )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_pre_topc @ sk_A @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['121','122','123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ sk_A @ sk_A )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_connsp_2 @ X0 @ sk_A @ sk_G )
      | ( r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['124'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G )
      | ~ ( m1_connsp_2 @ X0 @ sk_A @ sk_G )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['20','125'])).

thf('127',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G )
      | ~ ( m1_connsp_2 @ X0 @ sk_A @ sk_G )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,
    ( ~ ( r1_tarski @ ( sk_C @ sk_G @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_connsp_2 @ ( sk_C @ sk_G @ sk_A ) @ sk_A @ sk_G )
    | ( r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['19','128'])).

thf('130',plain,(
    m1_subset_1 @ ( sk_C @ sk_G @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','18'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('132',plain,(
    r1_tarski @ ( sk_C @ sk_G @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    m1_connsp_2 @ ( sk_C @ sk_G @ sk_A ) @ sk_A @ sk_G ),
    inference(clc,[status(thm)],['8','9'])).

thf('134',plain,
    ( ( r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['129','132','133'])).

thf('135',plain,
    ( ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_F ) ),
    inference(split,[status(esa)],['49'])).

thf('136',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G )
   <= ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_F ) ),
    inference(demod,[status(thm)],['135','136'])).

thf('138',plain,(
    ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_F ) ),
    inference('sat_resolution*',[status(thm)],['57','79'])).

thf('139',plain,(
    ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) ),
    inference(simpl_trail,[status(thm)],['137','138'])).

thf('140',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['134','139'])).

thf('141',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_E ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,
    ( ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_D ) ),
    inference(clc,[status(thm)],['142','143'])).

thf('145',plain,(
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    v2_struct_0 @ sk_D ),
    inference(clc,[status(thm)],['144','145'])).

thf('147',plain,(
    $false ),
    inference(demod,[status(thm)],['0','146'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.11  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7IaM9m5gdj
% 0.11/0.32  % Computer   : n001.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 13:11:30 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  % Running portfolio for 600 s
% 0.11/0.32  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.11/0.32  % Number of cores: 8
% 0.11/0.33  % Python version: Python 3.6.8
% 0.11/0.33  % Running in FO mode
% 0.17/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.17/0.52  % Solved by: fo/fo7.sh
% 0.17/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.17/0.52  % done 104 iterations in 0.077s
% 0.17/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.17/0.52  % SZS output start Refutation
% 0.17/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.17/0.52  thf(sk_G_type, type, sk_G: $i).
% 0.17/0.52  thf(sk_H_type, type, sk_H: $i).
% 0.17/0.52  thf(sk_E_type, type, sk_E: $i).
% 0.17/0.52  thf(sk_F_type, type, sk_F: $i).
% 0.17/0.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.17/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.17/0.52  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.17/0.52  thf(sk_D_type, type, sk_D: $i).
% 0.17/0.52  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.17/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.17/0.52  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.17/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.17/0.52  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.17/0.52  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.17/0.52  thf(k1_tsep_1_type, type, k1_tsep_1: $i > $i > $i > $i).
% 0.17/0.52  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.17/0.52  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.17/0.52  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.17/0.52  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.17/0.52  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.17/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.17/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.17/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.17/0.52  thf(t125_tmap_1, conjecture,
% 0.17/0.52    (![A:$i]:
% 0.17/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.17/0.52       ( ![B:$i]:
% 0.17/0.52         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.17/0.52             ( l1_pre_topc @ B ) ) =>
% 0.17/0.52           ( ![C:$i]:
% 0.17/0.52             ( ( ( v1_funct_1 @ C ) & 
% 0.17/0.52                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.17/0.52                 ( m1_subset_1 @
% 0.17/0.52                   C @ 
% 0.17/0.52                   ( k1_zfmisc_1 @
% 0.17/0.52                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.17/0.52               ( ![D:$i]:
% 0.17/0.52                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.17/0.52                   ( ![E:$i]:
% 0.17/0.52                     ( ( ( ~( v2_struct_0 @ E ) ) & ( m1_pre_topc @ E @ A ) ) =>
% 0.17/0.52                       ( ( ( A ) = ( k1_tsep_1 @ A @ D @ E ) ) =>
% 0.17/0.52                         ( ![F:$i]:
% 0.17/0.52                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ A ) ) =>
% 0.17/0.52                             ( ![G:$i]:
% 0.17/0.52                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.17/0.52                                 ( ![H:$i]:
% 0.17/0.52                                   ( ( m1_subset_1 @ H @ ( u1_struct_0 @ E ) ) =>
% 0.17/0.52                                     ( ( ( ( F ) = ( G ) ) & ( ( F ) = ( H ) ) ) =>
% 0.17/0.52                                       ( ( r1_tmap_1 @ A @ B @ C @ F ) <=>
% 0.17/0.52                                         ( ( r1_tmap_1 @
% 0.17/0.52                                             D @ B @ 
% 0.17/0.52                                             ( k2_tmap_1 @ A @ B @ C @ D ) @ G ) & 
% 0.17/0.52                                           ( r1_tmap_1 @
% 0.17/0.52                                             E @ B @ 
% 0.17/0.52                                             ( k2_tmap_1 @ A @ B @ C @ E ) @ H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.17/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.17/0.52    (~( ![A:$i]:
% 0.17/0.52        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.17/0.52            ( l1_pre_topc @ A ) ) =>
% 0.17/0.52          ( ![B:$i]:
% 0.17/0.52            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.17/0.52                ( l1_pre_topc @ B ) ) =>
% 0.17/0.52              ( ![C:$i]:
% 0.17/0.52                ( ( ( v1_funct_1 @ C ) & 
% 0.17/0.52                    ( v1_funct_2 @
% 0.17/0.52                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.17/0.52                    ( m1_subset_1 @
% 0.17/0.52                      C @ 
% 0.17/0.52                      ( k1_zfmisc_1 @
% 0.17/0.52                        ( k2_zfmisc_1 @
% 0.17/0.52                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.17/0.52                  ( ![D:$i]:
% 0.17/0.52                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.17/0.52                      ( ![E:$i]:
% 0.17/0.52                        ( ( ( ~( v2_struct_0 @ E ) ) & ( m1_pre_topc @ E @ A ) ) =>
% 0.17/0.52                          ( ( ( A ) = ( k1_tsep_1 @ A @ D @ E ) ) =>
% 0.17/0.52                            ( ![F:$i]:
% 0.17/0.52                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ A ) ) =>
% 0.17/0.52                                ( ![G:$i]:
% 0.17/0.52                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.17/0.52                                    ( ![H:$i]:
% 0.17/0.52                                      ( ( m1_subset_1 @ H @ ( u1_struct_0 @ E ) ) =>
% 0.17/0.52                                        ( ( ( ( F ) = ( G ) ) & 
% 0.17/0.52                                            ( ( F ) = ( H ) ) ) =>
% 0.17/0.52                                          ( ( r1_tmap_1 @ A @ B @ C @ F ) <=>
% 0.17/0.52                                            ( ( r1_tmap_1 @
% 0.17/0.52                                                D @ B @ 
% 0.17/0.52                                                ( k2_tmap_1 @ A @ B @ C @ D ) @ 
% 0.17/0.52                                                G ) & 
% 0.17/0.52                                              ( r1_tmap_1 @
% 0.17/0.52                                                E @ B @ 
% 0.17/0.52                                                ( k2_tmap_1 @ A @ B @ C @ E ) @ 
% 0.17/0.52                                                H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.17/0.52    inference('cnf.neg', [status(esa)], [t125_tmap_1])).
% 0.17/0.52  thf('0', plain, (~ (v2_struct_0 @ sk_D)),
% 0.17/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.52  thf('1', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_A))),
% 0.17/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.52  thf('2', plain, (((sk_F) = (sk_G))),
% 0.17/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.52  thf('3', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_A))),
% 0.17/0.52      inference('demod', [status(thm)], ['1', '2'])).
% 0.17/0.52  thf(existence_m1_connsp_2, axiom,
% 0.17/0.52    (![A:$i,B:$i]:
% 0.17/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.17/0.52         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.17/0.52       ( ?[C:$i]: ( m1_connsp_2 @ C @ A @ B ) ) ))).
% 0.17/0.52  thf('4', plain,
% 0.17/0.52      (![X9 : $i, X10 : $i]:
% 0.17/0.52         (~ (l1_pre_topc @ X9)
% 0.17/0.52          | ~ (v2_pre_topc @ X9)
% 0.17/0.52          | (v2_struct_0 @ X9)
% 0.17/0.52          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X9))
% 0.17/0.52          | (m1_connsp_2 @ (sk_C @ X10 @ X9) @ X9 @ X10))),
% 0.17/0.52      inference('cnf', [status(esa)], [existence_m1_connsp_2])).
% 0.17/0.52  thf('5', plain,
% 0.17/0.52      (((m1_connsp_2 @ (sk_C @ sk_G @ sk_A) @ sk_A @ sk_G)
% 0.17/0.52        | (v2_struct_0 @ sk_A)
% 0.17/0.52        | ~ (v2_pre_topc @ sk_A)
% 0.17/0.52        | ~ (l1_pre_topc @ sk_A))),
% 0.17/0.52      inference('sup-', [status(thm)], ['3', '4'])).
% 0.17/0.52  thf('6', plain, ((v2_pre_topc @ sk_A)),
% 0.17/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.52  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.17/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.52  thf('8', plain,
% 0.17/0.52      (((m1_connsp_2 @ (sk_C @ sk_G @ sk_A) @ sk_A @ sk_G)
% 0.17/0.52        | (v2_struct_0 @ sk_A))),
% 0.17/0.52      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.17/0.52  thf('9', plain, (~ (v2_struct_0 @ sk_A)),
% 0.17/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.52  thf('10', plain, ((m1_connsp_2 @ (sk_C @ sk_G @ sk_A) @ sk_A @ sk_G)),
% 0.17/0.52      inference('clc', [status(thm)], ['8', '9'])).
% 0.17/0.52  thf('11', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_A))),
% 0.17/0.52      inference('demod', [status(thm)], ['1', '2'])).
% 0.17/0.52  thf(dt_m1_connsp_2, axiom,
% 0.17/0.52    (![A:$i,B:$i]:
% 0.17/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.17/0.52         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.17/0.52       ( ![C:$i]:
% 0.17/0.52         ( ( m1_connsp_2 @ C @ A @ B ) =>
% 0.17/0.52           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.17/0.52  thf('12', plain,
% 0.17/0.52      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.17/0.52         (~ (l1_pre_topc @ X6)
% 0.17/0.52          | ~ (v2_pre_topc @ X6)
% 0.17/0.52          | (v2_struct_0 @ X6)
% 0.17/0.52          | ~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X6))
% 0.17/0.52          | (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.17/0.52          | ~ (m1_connsp_2 @ X8 @ X6 @ X7))),
% 0.17/0.52      inference('cnf', [status(esa)], [dt_m1_connsp_2])).
% 0.17/0.52  thf('13', plain,
% 0.17/0.52      (![X0 : $i]:
% 0.17/0.52         (~ (m1_connsp_2 @ X0 @ sk_A @ sk_G)
% 0.17/0.52          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.17/0.52          | (v2_struct_0 @ sk_A)
% 0.17/0.52          | ~ (v2_pre_topc @ sk_A)
% 0.17/0.52          | ~ (l1_pre_topc @ sk_A))),
% 0.17/0.52      inference('sup-', [status(thm)], ['11', '12'])).
% 0.17/0.52  thf('14', plain, ((v2_pre_topc @ sk_A)),
% 0.17/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.52  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.17/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.52  thf('16', plain,
% 0.17/0.52      (![X0 : $i]:
% 0.17/0.52         (~ (m1_connsp_2 @ X0 @ sk_A @ sk_G)
% 0.17/0.52          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.17/0.52          | (v2_struct_0 @ sk_A))),
% 0.17/0.52      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.17/0.52  thf('17', plain, (~ (v2_struct_0 @ sk_A)),
% 0.17/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.52  thf('18', plain,
% 0.17/0.52      (![X0 : $i]:
% 0.17/0.52         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.17/0.52          | ~ (m1_connsp_2 @ X0 @ sk_A @ sk_G))),
% 0.17/0.52      inference('clc', [status(thm)], ['16', '17'])).
% 0.17/0.52  thf('19', plain,
% 0.17/0.52      ((m1_subset_1 @ (sk_C @ sk_G @ sk_A) @ 
% 0.17/0.52        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.17/0.52      inference('sup-', [status(thm)], ['10', '18'])).
% 0.17/0.52  thf(t2_tsep_1, axiom,
% 0.17/0.52    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.17/0.52  thf('20', plain,
% 0.17/0.52      (![X19 : $i]: ((m1_pre_topc @ X19 @ X19) | ~ (l1_pre_topc @ X19))),
% 0.17/0.52      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.17/0.52  thf('21', plain,
% 0.17/0.52      (((r1_tmap_1 @ sk_E @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_E) @ 
% 0.17/0.52         sk_H)
% 0.17/0.52        | (r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_F))),
% 0.17/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.52  thf('22', plain,
% 0.17/0.52      (((r1_tmap_1 @ sk_E @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_E) @ 
% 0.17/0.52         sk_H))
% 0.17/0.52         <= (((r1_tmap_1 @ sk_E @ sk_B @ 
% 0.17/0.52               (k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_E) @ sk_H)))),
% 0.17/0.52      inference('split', [status(esa)], ['21'])).
% 0.17/0.52  thf('23', plain, (((sk_F) = (sk_H))),
% 0.17/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.52  thf('24', plain, (((sk_F) = (sk_G))),
% 0.17/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.52  thf('25', plain, (((sk_H) = (sk_G))),
% 0.17/0.52      inference('sup+', [status(thm)], ['23', '24'])).
% 0.17/0.52  thf('26', plain,
% 0.17/0.52      (((r1_tmap_1 @ sk_E @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_E) @ 
% 0.17/0.52         sk_G))
% 0.17/0.52         <= (((r1_tmap_1 @ sk_E @ sk_B @ 
% 0.17/0.52               (k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_E) @ sk_H)))),
% 0.17/0.52      inference('demod', [status(thm)], ['22', '25'])).
% 0.17/0.52  thf('27', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_D))),
% 0.17/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.52  thf('28', plain,
% 0.17/0.52      (((r1_tmap_1 @ sk_D @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D) @ 
% 0.17/0.52         sk_G)
% 0.17/0.52        | (r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_F))),
% 0.17/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.52  thf('29', plain,
% 0.17/0.52      (((r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_F))
% 0.17/0.52         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_F)))),
% 0.17/0.52      inference('split', [status(esa)], ['28'])).
% 0.17/0.52  thf('30', plain, (((sk_F) = (sk_G))),
% 0.17/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.52  thf('31', plain,
% 0.17/0.52      (((r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G))
% 0.17/0.52         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_F)))),
% 0.17/0.52      inference('demod', [status(thm)], ['29', '30'])).
% 0.17/0.52  thf('32', plain,
% 0.17/0.52      ((m1_subset_1 @ sk_C_1 @ 
% 0.17/0.52        (k1_zfmisc_1 @ 
% 0.17/0.52         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.17/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.52  thf(t64_tmap_1, axiom,
% 0.17/0.52    (![A:$i]:
% 0.17/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.17/0.52       ( ![B:$i]:
% 0.17/0.52         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.17/0.52             ( l1_pre_topc @ B ) ) =>
% 0.17/0.52           ( ![C:$i]:
% 0.17/0.52             ( ( ( v1_funct_1 @ C ) & 
% 0.17/0.52                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.17/0.52                 ( m1_subset_1 @
% 0.17/0.52                   C @ 
% 0.17/0.52                   ( k1_zfmisc_1 @
% 0.17/0.52                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.17/0.52               ( ![D:$i]:
% 0.17/0.52                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.17/0.52                   ( ![E:$i]:
% 0.17/0.52                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.17/0.52                       ( ![F:$i]:
% 0.17/0.52                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.17/0.52                           ( ( ( ( E ) = ( F ) ) & 
% 0.17/0.52                               ( r1_tmap_1 @ B @ A @ C @ E ) ) =>
% 0.17/0.52                             ( r1_tmap_1 @
% 0.17/0.52                               D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.17/0.52  thf('33', plain,
% 0.17/0.52      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.17/0.52         ((v2_struct_0 @ X20)
% 0.17/0.52          | ~ (v2_pre_topc @ X20)
% 0.17/0.52          | ~ (l1_pre_topc @ X20)
% 0.17/0.52          | (v2_struct_0 @ X21)
% 0.17/0.52          | ~ (m1_pre_topc @ X21 @ X20)
% 0.17/0.52          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X21))
% 0.17/0.52          | (r1_tmap_1 @ X21 @ X23 @ (k2_tmap_1 @ X20 @ X23 @ X24 @ X21) @ X22)
% 0.17/0.52          | ((X25) != (X22))
% 0.17/0.52          | ~ (r1_tmap_1 @ X20 @ X23 @ X24 @ X25)
% 0.17/0.52          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X20))
% 0.17/0.52          | ~ (m1_subset_1 @ X24 @ 
% 0.17/0.52               (k1_zfmisc_1 @ 
% 0.17/0.52                (k2_zfmisc_1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X23))))
% 0.17/0.52          | ~ (v1_funct_2 @ X24 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X23))
% 0.17/0.52          | ~ (v1_funct_1 @ X24)
% 0.17/0.52          | ~ (l1_pre_topc @ X23)
% 0.17/0.52          | ~ (v2_pre_topc @ X23)
% 0.17/0.52          | (v2_struct_0 @ X23))),
% 0.17/0.52      inference('cnf', [status(esa)], [t64_tmap_1])).
% 0.17/0.52  thf('34', plain,
% 0.17/0.52      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.17/0.52         ((v2_struct_0 @ X23)
% 0.17/0.52          | ~ (v2_pre_topc @ X23)
% 0.17/0.52          | ~ (l1_pre_topc @ X23)
% 0.17/0.52          | ~ (v1_funct_1 @ X24)
% 0.17/0.52          | ~ (v1_funct_2 @ X24 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X23))
% 0.17/0.52          | ~ (m1_subset_1 @ X24 @ 
% 0.17/0.52               (k1_zfmisc_1 @ 
% 0.17/0.52                (k2_zfmisc_1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X23))))
% 0.17/0.52          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X20))
% 0.17/0.52          | ~ (r1_tmap_1 @ X20 @ X23 @ X24 @ X22)
% 0.17/0.52          | (r1_tmap_1 @ X21 @ X23 @ (k2_tmap_1 @ X20 @ X23 @ X24 @ X21) @ X22)
% 0.17/0.52          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X21))
% 0.17/0.52          | ~ (m1_pre_topc @ X21 @ X20)
% 0.17/0.52          | (v2_struct_0 @ X21)
% 0.17/0.52          | ~ (l1_pre_topc @ X20)
% 0.17/0.52          | ~ (v2_pre_topc @ X20)
% 0.17/0.52          | (v2_struct_0 @ X20))),
% 0.17/0.52      inference('simplify', [status(thm)], ['33'])).
% 0.17/0.52  thf('35', plain,
% 0.17/0.52      (![X0 : $i, X1 : $i]:
% 0.17/0.52         ((v2_struct_0 @ sk_A)
% 0.17/0.52          | ~ (v2_pre_topc @ sk_A)
% 0.17/0.52          | ~ (l1_pre_topc @ sk_A)
% 0.17/0.52          | (v2_struct_0 @ X0)
% 0.17/0.52          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.17/0.52          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.17/0.52          | (r1_tmap_1 @ X0 @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ X0) @ 
% 0.17/0.52             X1)
% 0.17/0.52          | ~ (r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ X1)
% 0.17/0.52          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.17/0.52          | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ 
% 0.17/0.52               (u1_struct_0 @ sk_B))
% 0.17/0.52          | ~ (v1_funct_1 @ sk_C_1)
% 0.17/0.52          | ~ (l1_pre_topc @ sk_B)
% 0.17/0.52          | ~ (v2_pre_topc @ sk_B)
% 0.17/0.52          | (v2_struct_0 @ sk_B))),
% 0.17/0.52      inference('sup-', [status(thm)], ['32', '34'])).
% 0.17/0.52  thf('36', plain, ((v2_pre_topc @ sk_A)),
% 0.17/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.52  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 0.17/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.52  thf('38', plain,
% 0.17/0.52      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.17/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.52  thf('39', plain, ((v1_funct_1 @ sk_C_1)),
% 0.17/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.52  thf('40', plain, ((l1_pre_topc @ sk_B)),
% 0.17/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.52  thf('41', plain, ((v2_pre_topc @ sk_B)),
% 0.17/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.52  thf('42', plain,
% 0.17/0.52      (![X0 : $i, X1 : $i]:
% 0.17/0.52         ((v2_struct_0 @ sk_A)
% 0.17/0.52          | (v2_struct_0 @ X0)
% 0.17/0.52          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.17/0.52          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.17/0.52          | (r1_tmap_1 @ X0 @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ X0) @ 
% 0.17/0.52             X1)
% 0.17/0.52          | ~ (r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ X1)
% 0.17/0.52          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.17/0.52          | (v2_struct_0 @ sk_B))),
% 0.17/0.52      inference('demod', [status(thm)],
% 0.17/0.52                ['35', '36', '37', '38', '39', '40', '41'])).
% 0.17/0.52  thf('43', plain,
% 0.17/0.52      ((![X0 : $i]:
% 0.17/0.52          ((v2_struct_0 @ sk_B)
% 0.17/0.52           | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_A))
% 0.17/0.52           | (r1_tmap_1 @ X0 @ sk_B @ 
% 0.17/0.52              (k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ X0) @ sk_G)
% 0.17/0.52           | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ X0))
% 0.17/0.52           | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.17/0.52           | (v2_struct_0 @ X0)
% 0.17/0.52           | (v2_struct_0 @ sk_A)))
% 0.17/0.52         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_F)))),
% 0.17/0.52      inference('sup-', [status(thm)], ['31', '42'])).
% 0.17/0.52  thf('44', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_A))),
% 0.17/0.52      inference('demod', [status(thm)], ['1', '2'])).
% 0.17/0.52  thf('45', plain,
% 0.17/0.52      ((![X0 : $i]:
% 0.17/0.52          ((v2_struct_0 @ sk_B)
% 0.17/0.52           | (r1_tmap_1 @ X0 @ sk_B @ 
% 0.17/0.52              (k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ X0) @ sk_G)
% 0.17/0.52           | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ X0))
% 0.17/0.52           | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.17/0.52           | (v2_struct_0 @ X0)
% 0.17/0.52           | (v2_struct_0 @ sk_A)))
% 0.17/0.52         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_F)))),
% 0.17/0.52      inference('demod', [status(thm)], ['43', '44'])).
% 0.17/0.52  thf('46', plain,
% 0.17/0.52      ((((v2_struct_0 @ sk_A)
% 0.17/0.52         | (v2_struct_0 @ sk_D)
% 0.17/0.52         | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.17/0.52         | (r1_tmap_1 @ sk_D @ sk_B @ 
% 0.17/0.52            (k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D) @ sk_G)
% 0.17/0.52         | (v2_struct_0 @ sk_B)))
% 0.17/0.52         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_F)))),
% 0.17/0.52      inference('sup-', [status(thm)], ['27', '45'])).
% 0.17/0.52  thf('47', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.17/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.52  thf('48', plain,
% 0.17/0.52      ((((v2_struct_0 @ sk_A)
% 0.17/0.52         | (v2_struct_0 @ sk_D)
% 0.17/0.52         | (r1_tmap_1 @ sk_D @ sk_B @ 
% 0.17/0.52            (k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D) @ sk_G)
% 0.17/0.52         | (v2_struct_0 @ sk_B)))
% 0.17/0.52         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_F)))),
% 0.17/0.52      inference('demod', [status(thm)], ['46', '47'])).
% 0.17/0.52  thf('49', plain,
% 0.17/0.52      ((~ (r1_tmap_1 @ sk_E @ sk_B @ 
% 0.17/0.52           (k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_E) @ sk_H)
% 0.17/0.52        | ~ (r1_tmap_1 @ sk_D @ sk_B @ 
% 0.17/0.52             (k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D) @ sk_G)
% 0.17/0.52        | ~ (r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_F))),
% 0.17/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.52  thf('50', plain,
% 0.17/0.52      ((~ (r1_tmap_1 @ sk_D @ sk_B @ 
% 0.17/0.52           (k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D) @ sk_G))
% 0.17/0.52         <= (~
% 0.17/0.52             ((r1_tmap_1 @ sk_D @ sk_B @ 
% 0.17/0.52               (k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D) @ sk_G)))),
% 0.17/0.52      inference('split', [status(esa)], ['49'])).
% 0.17/0.52  thf('51', plain,
% 0.17/0.52      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_A)))
% 0.17/0.52         <= (~
% 0.17/0.52             ((r1_tmap_1 @ sk_D @ sk_B @ 
% 0.17/0.52               (k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D) @ sk_G)) & 
% 0.17/0.52             ((r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_F)))),
% 0.17/0.52      inference('sup-', [status(thm)], ['48', '50'])).
% 0.17/0.52  thf('52', plain, (~ (v2_struct_0 @ sk_B)),
% 0.17/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.52  thf('53', plain,
% 0.17/0.52      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D)))
% 0.17/0.52         <= (~
% 0.17/0.52             ((r1_tmap_1 @ sk_D @ sk_B @ 
% 0.17/0.52               (k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D) @ sk_G)) & 
% 0.17/0.52             ((r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_F)))),
% 0.17/0.52      inference('clc', [status(thm)], ['51', '52'])).
% 0.17/0.52  thf('54', plain, (~ (v2_struct_0 @ sk_A)),
% 0.17/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.52  thf('55', plain,
% 0.17/0.52      (((v2_struct_0 @ sk_D))
% 0.17/0.52         <= (~
% 0.17/0.52             ((r1_tmap_1 @ sk_D @ sk_B @ 
% 0.17/0.52               (k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D) @ sk_G)) & 
% 0.17/0.52             ((r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_F)))),
% 0.17/0.52      inference('clc', [status(thm)], ['53', '54'])).
% 0.17/0.52  thf('56', plain, (~ (v2_struct_0 @ sk_D)),
% 0.17/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.52  thf('57', plain,
% 0.17/0.52      (((r1_tmap_1 @ sk_D @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D) @ 
% 0.17/0.52         sk_G)) | 
% 0.17/0.52       ~ ((r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_F))),
% 0.17/0.52      inference('sup-', [status(thm)], ['55', '56'])).
% 0.17/0.52  thf('58', plain,
% 0.17/0.52      (((r1_tmap_1 @ sk_D @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D) @ 
% 0.17/0.52         sk_G))
% 0.17/0.52         <= (((r1_tmap_1 @ sk_D @ sk_B @ 
% 0.17/0.52               (k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D) @ sk_G)))),
% 0.17/0.52      inference('split', [status(esa)], ['28'])).
% 0.17/0.52  thf('59', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_E))),
% 0.17/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.52  thf('60', plain, (((sk_H) = (sk_G))),
% 0.17/0.52      inference('sup+', [status(thm)], ['23', '24'])).
% 0.17/0.52  thf('61', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_E))),
% 0.17/0.52      inference('demod', [status(thm)], ['59', '60'])).
% 0.17/0.52  thf('62', plain,
% 0.17/0.52      ((![X0 : $i]:
% 0.17/0.52          ((v2_struct_0 @ sk_B)
% 0.17/0.52           | (r1_tmap_1 @ X0 @ sk_B @ 
% 0.17/0.52              (k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ X0) @ sk_G)
% 0.17/0.52           | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ X0))
% 0.17/0.52           | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.17/0.52           | (v2_struct_0 @ X0)
% 0.17/0.52           | (v2_struct_0 @ sk_A)))
% 0.17/0.52         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_F)))),
% 0.17/0.52      inference('demod', [status(thm)], ['43', '44'])).
% 0.17/0.52  thf('63', plain,
% 0.17/0.52      ((((v2_struct_0 @ sk_A)
% 0.17/0.52         | (v2_struct_0 @ sk_E)
% 0.17/0.52         | ~ (m1_pre_topc @ sk_E @ sk_A)
% 0.17/0.52         | (r1_tmap_1 @ sk_E @ sk_B @ 
% 0.17/0.52            (k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_E) @ sk_G)
% 0.17/0.52         | (v2_struct_0 @ sk_B)))
% 0.17/0.52         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_F)))),
% 0.17/0.52      inference('sup-', [status(thm)], ['61', '62'])).
% 0.17/0.52  thf('64', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 0.17/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.52  thf('65', plain,
% 0.17/0.52      ((((v2_struct_0 @ sk_A)
% 0.17/0.52         | (v2_struct_0 @ sk_E)
% 0.17/0.52         | (r1_tmap_1 @ sk_E @ sk_B @ 
% 0.17/0.52            (k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_E) @ sk_G)
% 0.17/0.52         | (v2_struct_0 @ sk_B)))
% 0.17/0.52         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_F)))),
% 0.17/0.52      inference('demod', [status(thm)], ['63', '64'])).
% 0.17/0.52  thf('66', plain,
% 0.17/0.52      ((~ (r1_tmap_1 @ sk_E @ sk_B @ 
% 0.17/0.52           (k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_E) @ sk_H)
% 0.17/0.52        | ~ (r1_tmap_1 @ sk_D @ sk_B @ 
% 0.17/0.52             (k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D) @ sk_G)
% 0.17/0.52        | ~ (r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_F))),
% 0.17/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.52  thf('67', plain, (((sk_H) = (sk_G))),
% 0.17/0.52      inference('sup+', [status(thm)], ['23', '24'])).
% 0.17/0.52  thf('68', plain, (((sk_F) = (sk_G))),
% 0.17/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.52  thf('69', plain,
% 0.17/0.52      ((~ (r1_tmap_1 @ sk_E @ sk_B @ 
% 0.17/0.52           (k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_E) @ sk_G)
% 0.17/0.52        | ~ (r1_tmap_1 @ sk_D @ sk_B @ 
% 0.17/0.52             (k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D) @ sk_G)
% 0.17/0.52        | ~ (r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G))),
% 0.17/0.52      inference('demod', [status(thm)], ['66', '67', '68'])).
% 0.17/0.52  thf('70', plain,
% 0.17/0.52      ((((v2_struct_0 @ sk_B)
% 0.17/0.52         | (v2_struct_0 @ sk_E)
% 0.17/0.52         | (v2_struct_0 @ sk_A)
% 0.17/0.52         | ~ (r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G)
% 0.17/0.52         | ~ (r1_tmap_1 @ sk_D @ sk_B @ 
% 0.17/0.52              (k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D) @ sk_G)))
% 0.17/0.52         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_F)))),
% 0.17/0.52      inference('sup-', [status(thm)], ['65', '69'])).
% 0.17/0.52  thf('71', plain,
% 0.17/0.52      (((r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G))
% 0.17/0.52         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_F)))),
% 0.17/0.52      inference('demod', [status(thm)], ['29', '30'])).
% 0.17/0.52  thf('72', plain,
% 0.17/0.52      ((((v2_struct_0 @ sk_B)
% 0.17/0.52         | (v2_struct_0 @ sk_E)
% 0.17/0.52         | (v2_struct_0 @ sk_A)
% 0.17/0.52         | ~ (r1_tmap_1 @ sk_D @ sk_B @ 
% 0.17/0.52              (k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D) @ sk_G)))
% 0.17/0.52         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_F)))),
% 0.17/0.52      inference('demod', [status(thm)], ['70', '71'])).
% 0.17/0.52  thf('73', plain,
% 0.17/0.52      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_E) | (v2_struct_0 @ sk_B)))
% 0.17/0.52         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_F)) & 
% 0.17/0.52             ((r1_tmap_1 @ sk_D @ sk_B @ 
% 0.17/0.52               (k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D) @ sk_G)))),
% 0.17/0.52      inference('sup-', [status(thm)], ['58', '72'])).
% 0.17/0.52  thf('74', plain, (~ (v2_struct_0 @ sk_A)),
% 0.17/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.52  thf('75', plain,
% 0.17/0.52      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_E)))
% 0.17/0.52         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_F)) & 
% 0.17/0.52             ((r1_tmap_1 @ sk_D @ sk_B @ 
% 0.17/0.52               (k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D) @ sk_G)))),
% 0.17/0.52      inference('clc', [status(thm)], ['73', '74'])).
% 0.17/0.52  thf('76', plain, (~ (v2_struct_0 @ sk_B)),
% 0.17/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.52  thf('77', plain,
% 0.17/0.52      (((v2_struct_0 @ sk_E))
% 0.17/0.52         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_F)) & 
% 0.17/0.52             ((r1_tmap_1 @ sk_D @ sk_B @ 
% 0.17/0.52               (k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D) @ sk_G)))),
% 0.17/0.52      inference('clc', [status(thm)], ['75', '76'])).
% 0.17/0.52  thf('78', plain, (~ (v2_struct_0 @ sk_E)),
% 0.17/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.52  thf('79', plain,
% 0.17/0.52      (~ ((r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_F)) | 
% 0.17/0.52       ~
% 0.17/0.52       ((r1_tmap_1 @ sk_D @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D) @ 
% 0.17/0.52         sk_G))),
% 0.17/0.52      inference('sup-', [status(thm)], ['77', '78'])).
% 0.17/0.52  thf('80', plain,
% 0.17/0.52      (((r1_tmap_1 @ sk_E @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_E) @ 
% 0.17/0.52         sk_H)) | 
% 0.17/0.52       ((r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_F))),
% 0.17/0.52      inference('split', [status(esa)], ['21'])).
% 0.17/0.52  thf('81', plain,
% 0.17/0.52      (((r1_tmap_1 @ sk_E @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_E) @ 
% 0.17/0.52         sk_H))),
% 0.17/0.52      inference('sat_resolution*', [status(thm)], ['57', '79', '80'])).
% 0.17/0.52  thf('82', plain,
% 0.17/0.52      ((r1_tmap_1 @ sk_E @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_E) @ 
% 0.17/0.52        sk_G)),
% 0.17/0.52      inference('simpl_trail', [status(thm)], ['26', '81'])).
% 0.17/0.52  thf('83', plain,
% 0.17/0.52      (((r1_tmap_1 @ sk_D @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D) @ 
% 0.17/0.52         sk_G))
% 0.17/0.52         <= (((r1_tmap_1 @ sk_D @ sk_B @ 
% 0.17/0.52               (k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D) @ sk_G)))),
% 0.17/0.52      inference('split', [status(esa)], ['28'])).
% 0.17/0.52  thf('84', plain,
% 0.17/0.52      (((r1_tmap_1 @ sk_D @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D) @ 
% 0.17/0.52         sk_G)) | 
% 0.17/0.52       ((r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_F))),
% 0.17/0.52      inference('split', [status(esa)], ['28'])).
% 0.17/0.52  thf('85', plain,
% 0.17/0.52      (((r1_tmap_1 @ sk_D @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D) @ 
% 0.17/0.52         sk_G))),
% 0.17/0.52      inference('sat_resolution*', [status(thm)], ['57', '79', '84'])).
% 0.17/0.52  thf('86', plain,
% 0.17/0.52      ((r1_tmap_1 @ sk_D @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D) @ 
% 0.17/0.52        sk_G)),
% 0.17/0.52      inference('simpl_trail', [status(thm)], ['83', '85'])).
% 0.17/0.52  thf('87', plain,
% 0.17/0.52      ((m1_subset_1 @ sk_C_1 @ 
% 0.17/0.52        (k1_zfmisc_1 @ 
% 0.17/0.52         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.17/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.52  thf(t124_tmap_1, axiom,
% 0.17/0.52    (![A:$i]:
% 0.17/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.17/0.52       ( ![B:$i]:
% 0.17/0.52         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.17/0.52             ( l1_pre_topc @ B ) ) =>
% 0.17/0.52           ( ![C:$i]:
% 0.17/0.52             ( ( ( v1_funct_1 @ C ) & 
% 0.17/0.52                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.17/0.52                 ( m1_subset_1 @
% 0.17/0.52                   C @ 
% 0.17/0.52                   ( k1_zfmisc_1 @
% 0.17/0.52                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.17/0.52               ( ![D:$i]:
% 0.17/0.52                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.17/0.52                   ( ![E:$i]:
% 0.17/0.52                     ( ( ( ~( v2_struct_0 @ E ) ) & ( m1_pre_topc @ E @ A ) ) =>
% 0.17/0.52                       ( ![F:$i]:
% 0.17/0.52                         ( ( m1_subset_1 @
% 0.17/0.52                             F @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ D @ E ) ) ) =>
% 0.17/0.52                           ( ![G:$i]:
% 0.17/0.52                             ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.17/0.52                               ( ![H:$i]:
% 0.17/0.52                                 ( ( m1_subset_1 @ H @ ( u1_struct_0 @ E ) ) =>
% 0.17/0.52                                   ( ( ( ( F ) = ( G ) ) & ( ( F ) = ( H ) ) ) =>
% 0.17/0.52                                     ( ( r1_tmap_1 @
% 0.17/0.52                                         ( k1_tsep_1 @ A @ D @ E ) @ B @ 
% 0.17/0.52                                         ( k2_tmap_1 @
% 0.17/0.52                                           A @ B @ C @ 
% 0.17/0.52                                           ( k1_tsep_1 @ A @ D @ E ) ) @ 
% 0.17/0.52                                         F ) <=>
% 0.17/0.52                                       ( ( r1_tmap_1 @
% 0.17/0.52                                           D @ B @ 
% 0.17/0.52                                           ( k2_tmap_1 @ A @ B @ C @ D ) @ G ) & 
% 0.17/0.52                                         ( r1_tmap_1 @
% 0.17/0.52                                           E @ B @ 
% 0.17/0.52                                           ( k2_tmap_1 @ A @ B @ C @ E ) @ H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.17/0.52  thf('88', plain,
% 0.17/0.52      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i, 
% 0.17/0.52         X18 : $i]:
% 0.17/0.52         ((v2_struct_0 @ X11)
% 0.17/0.52          | ~ (v2_pre_topc @ X11)
% 0.17/0.52          | ~ (l1_pre_topc @ X11)
% 0.17/0.52          | (v2_struct_0 @ X12)
% 0.17/0.52          | ~ (m1_pre_topc @ X12 @ X13)
% 0.17/0.52          | ~ (m1_subset_1 @ X14 @ 
% 0.17/0.52               (u1_struct_0 @ (k1_tsep_1 @ X13 @ X12 @ X15)))
% 0.17/0.52          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X15))
% 0.17/0.52          | ~ (r1_tmap_1 @ X12 @ X11 @ (k2_tmap_1 @ X13 @ X11 @ X17 @ X12) @ 
% 0.17/0.52               X18)
% 0.17/0.52          | ~ (r1_tmap_1 @ X15 @ X11 @ (k2_tmap_1 @ X13 @ X11 @ X17 @ X15) @ 
% 0.17/0.52               X16)
% 0.17/0.52          | (r1_tmap_1 @ (k1_tsep_1 @ X13 @ X12 @ X15) @ X11 @ 
% 0.17/0.52             (k2_tmap_1 @ X13 @ X11 @ X17 @ (k1_tsep_1 @ X13 @ X12 @ X15)) @ 
% 0.17/0.52             X14)
% 0.17/0.52          | ((X14) != (X16))
% 0.17/0.52          | ((X14) != (X18))
% 0.17/0.52          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X12))
% 0.17/0.52          | ~ (m1_pre_topc @ X15 @ X13)
% 0.17/0.52          | (v2_struct_0 @ X15)
% 0.17/0.52          | ~ (m1_subset_1 @ X17 @ 
% 0.17/0.52               (k1_zfmisc_1 @ 
% 0.17/0.52                (k2_zfmisc_1 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X11))))
% 0.17/0.52          | ~ (v1_funct_2 @ X17 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X11))
% 0.17/0.52          | ~ (v1_funct_1 @ X17)
% 0.17/0.52          | ~ (l1_pre_topc @ X13)
% 0.17/0.52          | ~ (v2_pre_topc @ X13)
% 0.17/0.52          | (v2_struct_0 @ X13))),
% 0.17/0.52      inference('cnf', [status(esa)], [t124_tmap_1])).
% 0.17/0.52  thf('89', plain,
% 0.17/0.52      (![X11 : $i, X12 : $i, X13 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.17/0.52         ((v2_struct_0 @ X13)
% 0.17/0.52          | ~ (v2_pre_topc @ X13)
% 0.17/0.52          | ~ (l1_pre_topc @ X13)
% 0.17/0.52          | ~ (v1_funct_1 @ X17)
% 0.17/0.52          | ~ (v1_funct_2 @ X17 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X11))
% 0.17/0.52          | ~ (m1_subset_1 @ X17 @ 
% 0.17/0.52               (k1_zfmisc_1 @ 
% 0.17/0.52                (k2_zfmisc_1 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X11))))
% 0.17/0.52          | (v2_struct_0 @ X15)
% 0.17/0.52          | ~ (m1_pre_topc @ X15 @ X13)
% 0.17/0.52          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X12))
% 0.17/0.52          | (r1_tmap_1 @ (k1_tsep_1 @ X13 @ X12 @ X15) @ X11 @ 
% 0.17/0.52             (k2_tmap_1 @ X13 @ X11 @ X17 @ (k1_tsep_1 @ X13 @ X12 @ X15)) @ 
% 0.17/0.52             X16)
% 0.17/0.52          | ~ (r1_tmap_1 @ X15 @ X11 @ (k2_tmap_1 @ X13 @ X11 @ X17 @ X15) @ 
% 0.17/0.52               X16)
% 0.17/0.52          | ~ (r1_tmap_1 @ X12 @ X11 @ (k2_tmap_1 @ X13 @ X11 @ X17 @ X12) @ 
% 0.17/0.52               X16)
% 0.17/0.52          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X15))
% 0.17/0.52          | ~ (m1_subset_1 @ X16 @ 
% 0.17/0.52               (u1_struct_0 @ (k1_tsep_1 @ X13 @ X12 @ X15)))
% 0.17/0.52          | ~ (m1_pre_topc @ X12 @ X13)
% 0.17/0.52          | (v2_struct_0 @ X12)
% 0.17/0.52          | ~ (l1_pre_topc @ X11)
% 0.17/0.52          | ~ (v2_pre_topc @ X11)
% 0.17/0.52          | (v2_struct_0 @ X11))),
% 0.17/0.52      inference('simplify', [status(thm)], ['88'])).
% 0.17/0.52  thf('90', plain,
% 0.17/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.17/0.52         ((v2_struct_0 @ sk_B)
% 0.17/0.52          | ~ (v2_pre_topc @ sk_B)
% 0.17/0.52          | ~ (l1_pre_topc @ sk_B)
% 0.17/0.52          | (v2_struct_0 @ X0)
% 0.17/0.52          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.17/0.52          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ X0 @ X1)))
% 0.17/0.52          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.17/0.52          | ~ (r1_tmap_1 @ X0 @ sk_B @ 
% 0.17/0.52               (k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ X0) @ X2)
% 0.17/0.52          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.17/0.52               (k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ X1) @ X2)
% 0.17/0.52          | (r1_tmap_1 @ (k1_tsep_1 @ sk_A @ X0 @ X1) @ sk_B @ 
% 0.17/0.52             (k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tsep_1 @ sk_A @ X0 @ X1)) @ 
% 0.17/0.52             X2)
% 0.17/0.52          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.17/0.52          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.17/0.52          | (v2_struct_0 @ X1)
% 0.17/0.52          | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ 
% 0.17/0.52               (u1_struct_0 @ sk_B))
% 0.17/0.52          | ~ (v1_funct_1 @ sk_C_1)
% 0.17/0.52          | ~ (l1_pre_topc @ sk_A)
% 0.17/0.52          | ~ (v2_pre_topc @ sk_A)
% 0.17/0.52          | (v2_struct_0 @ sk_A))),
% 0.17/0.52      inference('sup-', [status(thm)], ['87', '89'])).
% 0.17/0.52  thf('91', plain, ((v2_pre_topc @ sk_B)),
% 0.17/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.52  thf('92', plain, ((l1_pre_topc @ sk_B)),
% 0.17/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.52  thf('93', plain,
% 0.17/0.52      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.17/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.52  thf('94', plain, ((v1_funct_1 @ sk_C_1)),
% 0.17/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.52  thf('95', plain, ((l1_pre_topc @ sk_A)),
% 0.17/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.52  thf('96', plain, ((v2_pre_topc @ sk_A)),
% 0.17/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.52  thf('97', plain,
% 0.17/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.17/0.52         ((v2_struct_0 @ sk_B)
% 0.17/0.52          | (v2_struct_0 @ X0)
% 0.17/0.52          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.17/0.52          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ X0 @ X1)))
% 0.17/0.52          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.17/0.52          | ~ (r1_tmap_1 @ X0 @ sk_B @ 
% 0.17/0.52               (k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ X0) @ X2)
% 0.17/0.52          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.17/0.52               (k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ X1) @ X2)
% 0.17/0.52          | (r1_tmap_1 @ (k1_tsep_1 @ sk_A @ X0 @ X1) @ sk_B @ 
% 0.17/0.52             (k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tsep_1 @ sk_A @ X0 @ X1)) @ 
% 0.17/0.52             X2)
% 0.17/0.52          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.17/0.52          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.17/0.52          | (v2_struct_0 @ X1)
% 0.17/0.52          | (v2_struct_0 @ sk_A))),
% 0.17/0.52      inference('demod', [status(thm)],
% 0.17/0.52                ['90', '91', '92', '93', '94', '95', '96'])).
% 0.17/0.52  thf('98', plain,
% 0.17/0.52      (![X0 : $i]:
% 0.17/0.52         ((v2_struct_0 @ sk_A)
% 0.17/0.52          | (v2_struct_0 @ X0)
% 0.17/0.52          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.17/0.52          | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_D))
% 0.17/0.52          | (r1_tmap_1 @ (k1_tsep_1 @ sk_A @ sk_D @ X0) @ sk_B @ 
% 0.17/0.52             (k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tsep_1 @ sk_A @ sk_D @ X0)) @ 
% 0.17/0.52             sk_G)
% 0.17/0.52          | ~ (r1_tmap_1 @ X0 @ sk_B @ 
% 0.17/0.52               (k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ X0) @ sk_G)
% 0.17/0.52          | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ X0))
% 0.17/0.52          | ~ (m1_subset_1 @ sk_G @ 
% 0.17/0.52               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ X0)))
% 0.17/0.52          | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.17/0.52          | (v2_struct_0 @ sk_D)
% 0.17/0.52          | (v2_struct_0 @ sk_B))),
% 0.17/0.52      inference('sup-', [status(thm)], ['86', '97'])).
% 0.17/0.52  thf('99', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_D))),
% 0.17/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.52  thf('100', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.17/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.52  thf('101', plain,
% 0.17/0.52      (![X0 : $i]:
% 0.17/0.52         ((v2_struct_0 @ sk_A)
% 0.17/0.52          | (v2_struct_0 @ X0)
% 0.17/0.52          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.17/0.52          | (r1_tmap_1 @ (k1_tsep_1 @ sk_A @ sk_D @ X0) @ sk_B @ 
% 0.17/0.52             (k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tsep_1 @ sk_A @ sk_D @ X0)) @ 
% 0.17/0.52             sk_G)
% 0.17/0.52          | ~ (r1_tmap_1 @ X0 @ sk_B @ 
% 0.17/0.52               (k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ X0) @ sk_G)
% 0.17/0.52          | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ X0))
% 0.17/0.52          | ~ (m1_subset_1 @ sk_G @ 
% 0.17/0.52               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ X0)))
% 0.17/0.52          | (v2_struct_0 @ sk_D)
% 0.17/0.52          | (v2_struct_0 @ sk_B))),
% 0.17/0.52      inference('demod', [status(thm)], ['98', '99', '100'])).
% 0.17/0.52  thf('102', plain,
% 0.17/0.52      (((v2_struct_0 @ sk_B)
% 0.17/0.52        | (v2_struct_0 @ sk_D)
% 0.17/0.52        | ~ (m1_subset_1 @ sk_G @ 
% 0.17/0.52             (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))
% 0.17/0.52        | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_E))
% 0.17/0.52        | (r1_tmap_1 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B @ 
% 0.17/0.52           (k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 0.17/0.52           sk_G)
% 0.17/0.52        | ~ (m1_pre_topc @ sk_E @ sk_A)
% 0.17/0.52        | (v2_struct_0 @ sk_E)
% 0.17/0.52        | (v2_struct_0 @ sk_A))),
% 0.17/0.52      inference('sup-', [status(thm)], ['82', '101'])).
% 0.17/0.52  thf('103', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.17/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.52  thf('104', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_A))),
% 0.17/0.52      inference('demod', [status(thm)], ['1', '2'])).
% 0.17/0.52  thf('105', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_E))),
% 0.17/0.52      inference('demod', [status(thm)], ['59', '60'])).
% 0.17/0.52  thf('106', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.17/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.52  thf('107', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.17/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.52  thf('108', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 0.17/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.52  thf('109', plain,
% 0.17/0.52      (((v2_struct_0 @ sk_B)
% 0.17/0.52        | (v2_struct_0 @ sk_D)
% 0.17/0.52        | (r1_tmap_1 @ sk_A @ sk_B @ 
% 0.17/0.52           (k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_A) @ sk_G)
% 0.17/0.52        | (v2_struct_0 @ sk_E)
% 0.17/0.52        | (v2_struct_0 @ sk_A))),
% 0.17/0.52      inference('demod', [status(thm)],
% 0.17/0.52                ['102', '103', '104', '105', '106', '107', '108'])).
% 0.17/0.52  thf('110', plain,
% 0.17/0.52      ((m1_subset_1 @ sk_C_1 @ 
% 0.17/0.52        (k1_zfmisc_1 @ 
% 0.17/0.52         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.17/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.52  thf(t65_tmap_1, axiom,
% 0.17/0.52    (![A:$i]:
% 0.17/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.17/0.52       ( ![B:$i]:
% 0.17/0.52         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.17/0.52             ( l1_pre_topc @ B ) ) =>
% 0.17/0.52           ( ![C:$i]:
% 0.17/0.52             ( ( ( v1_funct_1 @ C ) & 
% 0.17/0.52                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.17/0.52                 ( m1_subset_1 @
% 0.17/0.52                   C @ 
% 0.17/0.52                   ( k1_zfmisc_1 @
% 0.17/0.52                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.17/0.52               ( ![D:$i]:
% 0.17/0.52                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.17/0.52                   ( ![E:$i]:
% 0.17/0.52                     ( ( m1_subset_1 @
% 0.17/0.52                         E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.17/0.52                       ( ![F:$i]:
% 0.17/0.52                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 0.17/0.52                           ( ![G:$i]:
% 0.17/0.52                             ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.17/0.52                               ( ( ( r1_tarski @ E @ ( u1_struct_0 @ D ) ) & 
% 0.17/0.52                                   ( m1_connsp_2 @ E @ B @ F ) & 
% 0.17/0.52                                   ( ( F ) = ( G ) ) ) =>
% 0.17/0.52                                 ( ( r1_tmap_1 @ B @ A @ C @ F ) <=>
% 0.17/0.52                                   ( r1_tmap_1 @
% 0.17/0.52                                     D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.17/0.52  thf('111', plain,
% 0.17/0.52      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.17/0.52         ((v2_struct_0 @ X26)
% 0.17/0.52          | ~ (v2_pre_topc @ X26)
% 0.17/0.52          | ~ (l1_pre_topc @ X26)
% 0.17/0.52          | (v2_struct_0 @ X27)
% 0.17/0.52          | ~ (m1_pre_topc @ X27 @ X26)
% 0.17/0.52          | ~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X26))
% 0.17/0.52          | ~ (r1_tarski @ X29 @ (u1_struct_0 @ X27))
% 0.17/0.52          | ~ (m1_connsp_2 @ X29 @ X26 @ X28)
% 0.17/0.52          | ((X28) != (X30))
% 0.17/0.52          | ~ (r1_tmap_1 @ X27 @ X31 @ (k2_tmap_1 @ X26 @ X31 @ X32 @ X27) @ 
% 0.17/0.52               X30)
% 0.17/0.52          | (r1_tmap_1 @ X26 @ X31 @ X32 @ X28)
% 0.17/0.52          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X27))
% 0.17/0.52          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.17/0.52          | ~ (m1_subset_1 @ X32 @ 
% 0.17/0.52               (k1_zfmisc_1 @ 
% 0.17/0.52                (k2_zfmisc_1 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X31))))
% 0.17/0.52          | ~ (v1_funct_2 @ X32 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X31))
% 0.17/0.52          | ~ (v1_funct_1 @ X32)
% 0.17/0.52          | ~ (l1_pre_topc @ X31)
% 0.17/0.52          | ~ (v2_pre_topc @ X31)
% 0.17/0.52          | (v2_struct_0 @ X31))),
% 0.17/0.52      inference('cnf', [status(esa)], [t65_tmap_1])).
% 0.17/0.52  thf('112', plain,
% 0.17/0.52      (![X26 : $i, X27 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.17/0.52         ((v2_struct_0 @ X31)
% 0.17/0.52          | ~ (v2_pre_topc @ X31)
% 0.17/0.52          | ~ (l1_pre_topc @ X31)
% 0.17/0.52          | ~ (v1_funct_1 @ X32)
% 0.17/0.52          | ~ (v1_funct_2 @ X32 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X31))
% 0.17/0.52          | ~ (m1_subset_1 @ X32 @ 
% 0.17/0.52               (k1_zfmisc_1 @ 
% 0.17/0.52                (k2_zfmisc_1 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X31))))
% 0.17/0.52          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.17/0.52          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X27))
% 0.17/0.52          | (r1_tmap_1 @ X26 @ X31 @ X32 @ X30)
% 0.17/0.52          | ~ (r1_tmap_1 @ X27 @ X31 @ (k2_tmap_1 @ X26 @ X31 @ X32 @ X27) @ 
% 0.17/0.52               X30)
% 0.17/0.52          | ~ (m1_connsp_2 @ X29 @ X26 @ X30)
% 0.17/0.52          | ~ (r1_tarski @ X29 @ (u1_struct_0 @ X27))
% 0.17/0.52          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X26))
% 0.17/0.52          | ~ (m1_pre_topc @ X27 @ X26)
% 0.17/0.52          | (v2_struct_0 @ X27)
% 0.17/0.52          | ~ (l1_pre_topc @ X26)
% 0.17/0.52          | ~ (v2_pre_topc @ X26)
% 0.17/0.52          | (v2_struct_0 @ X26))),
% 0.17/0.52      inference('simplify', [status(thm)], ['111'])).
% 0.17/0.52  thf('113', plain,
% 0.17/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.17/0.52         ((v2_struct_0 @ sk_A)
% 0.17/0.52          | ~ (v2_pre_topc @ sk_A)
% 0.17/0.52          | ~ (l1_pre_topc @ sk_A)
% 0.17/0.52          | (v2_struct_0 @ X0)
% 0.17/0.52          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.17/0.52          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.17/0.52          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.17/0.52          | ~ (m1_connsp_2 @ X2 @ sk_A @ X1)
% 0.17/0.52          | ~ (r1_tmap_1 @ X0 @ sk_B @ 
% 0.17/0.52               (k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ X0) @ X1)
% 0.17/0.52          | (r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ X1)
% 0.17/0.52          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.17/0.52          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.17/0.52          | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ 
% 0.17/0.52               (u1_struct_0 @ sk_B))
% 0.17/0.52          | ~ (v1_funct_1 @ sk_C_1)
% 0.17/0.52          | ~ (l1_pre_topc @ sk_B)
% 0.17/0.52          | ~ (v2_pre_topc @ sk_B)
% 0.17/0.52          | (v2_struct_0 @ sk_B))),
% 0.17/0.52      inference('sup-', [status(thm)], ['110', '112'])).
% 0.17/0.52  thf('114', plain, ((v2_pre_topc @ sk_A)),
% 0.17/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.52  thf('115', plain, ((l1_pre_topc @ sk_A)),
% 0.17/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.52  thf('116', plain,
% 0.17/0.52      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.17/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.52  thf('117', plain, ((v1_funct_1 @ sk_C_1)),
% 0.17/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.52  thf('118', plain, ((l1_pre_topc @ sk_B)),
% 0.17/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.52  thf('119', plain, ((v2_pre_topc @ sk_B)),
% 0.17/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.52  thf('120', plain,
% 0.17/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.17/0.52         ((v2_struct_0 @ sk_A)
% 0.17/0.52          | (v2_struct_0 @ X0)
% 0.17/0.52          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.17/0.52          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.17/0.52          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.17/0.52          | ~ (m1_connsp_2 @ X2 @ sk_A @ X1)
% 0.17/0.52          | ~ (r1_tmap_1 @ X0 @ sk_B @ 
% 0.17/0.52               (k2_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ X0) @ X1)
% 0.17/0.52          | (r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ X1)
% 0.17/0.52          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.17/0.52          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.17/0.52          | (v2_struct_0 @ sk_B))),
% 0.17/0.52      inference('demod', [status(thm)],
% 0.17/0.52                ['113', '114', '115', '116', '117', '118', '119'])).
% 0.17/0.52  thf('121', plain,
% 0.17/0.52      (![X0 : $i]:
% 0.17/0.52         ((v2_struct_0 @ sk_A)
% 0.17/0.52          | (v2_struct_0 @ sk_E)
% 0.17/0.52          | (v2_struct_0 @ sk_D)
% 0.17/0.52          | (v2_struct_0 @ sk_B)
% 0.17/0.52          | (v2_struct_0 @ sk_B)
% 0.17/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.17/0.52          | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_A))
% 0.17/0.52          | (r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G)
% 0.17/0.52          | ~ (m1_connsp_2 @ X0 @ sk_A @ sk_G)
% 0.17/0.52          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_A))
% 0.17/0.52          | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_A))
% 0.17/0.52          | ~ (m1_pre_topc @ sk_A @ sk_A)
% 0.17/0.52          | (v2_struct_0 @ sk_A)
% 0.17/0.52          | (v2_struct_0 @ sk_A))),
% 0.17/0.52      inference('sup-', [status(thm)], ['109', '120'])).
% 0.17/0.52  thf('122', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_A))),
% 0.17/0.52      inference('demod', [status(thm)], ['1', '2'])).
% 0.17/0.52  thf('123', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_A))),
% 0.17/0.52      inference('demod', [status(thm)], ['1', '2'])).
% 0.17/0.52  thf('124', plain,
% 0.17/0.52      (![X0 : $i]:
% 0.17/0.52         ((v2_struct_0 @ sk_A)
% 0.17/0.52          | (v2_struct_0 @ sk_E)
% 0.17/0.52          | (v2_struct_0 @ sk_D)
% 0.17/0.52          | (v2_struct_0 @ sk_B)
% 0.17/0.52          | (v2_struct_0 @ sk_B)
% 0.17/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.17/0.52          | (r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G)
% 0.17/0.52          | ~ (m1_connsp_2 @ X0 @ sk_A @ sk_G)
% 0.17/0.52          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_A))
% 0.17/0.52          | ~ (m1_pre_topc @ sk_A @ sk_A)
% 0.17/0.52          | (v2_struct_0 @ sk_A)
% 0.17/0.52          | (v2_struct_0 @ sk_A))),
% 0.17/0.52      inference('demod', [status(thm)], ['121', '122', '123'])).
% 0.17/0.52  thf('125', plain,
% 0.17/0.52      (![X0 : $i]:
% 0.17/0.52         (~ (m1_pre_topc @ sk_A @ sk_A)
% 0.17/0.52          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_A))
% 0.17/0.52          | ~ (m1_connsp_2 @ X0 @ sk_A @ sk_G)
% 0.17/0.52          | (r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G)
% 0.17/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.17/0.52          | (v2_struct_0 @ sk_B)
% 0.17/0.52          | (v2_struct_0 @ sk_D)
% 0.17/0.52          | (v2_struct_0 @ sk_E)
% 0.17/0.52          | (v2_struct_0 @ sk_A))),
% 0.17/0.52      inference('simplify', [status(thm)], ['124'])).
% 0.17/0.52  thf('126', plain,
% 0.17/0.52      (![X0 : $i]:
% 0.17/0.52         (~ (l1_pre_topc @ sk_A)
% 0.17/0.52          | (v2_struct_0 @ sk_A)
% 0.17/0.52          | (v2_struct_0 @ sk_E)
% 0.17/0.52          | (v2_struct_0 @ sk_D)
% 0.17/0.52          | (v2_struct_0 @ sk_B)
% 0.17/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.17/0.52          | (r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G)
% 0.17/0.52          | ~ (m1_connsp_2 @ X0 @ sk_A @ sk_G)
% 0.17/0.52          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.17/0.52      inference('sup-', [status(thm)], ['20', '125'])).
% 0.17/0.52  thf('127', plain, ((l1_pre_topc @ sk_A)),
% 0.17/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.52  thf('128', plain,
% 0.17/0.52      (![X0 : $i]:
% 0.17/0.52         ((v2_struct_0 @ sk_A)
% 0.17/0.52          | (v2_struct_0 @ sk_E)
% 0.17/0.52          | (v2_struct_0 @ sk_D)
% 0.17/0.52          | (v2_struct_0 @ sk_B)
% 0.17/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.17/0.52          | (r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G)
% 0.17/0.52          | ~ (m1_connsp_2 @ X0 @ sk_A @ sk_G)
% 0.17/0.52          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.17/0.52      inference('demod', [status(thm)], ['126', '127'])).
% 0.17/0.52  thf('129', plain,
% 0.17/0.52      ((~ (r1_tarski @ (sk_C @ sk_G @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.17/0.52        | ~ (m1_connsp_2 @ (sk_C @ sk_G @ sk_A) @ sk_A @ sk_G)
% 0.17/0.52        | (r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G)
% 0.17/0.52        | (v2_struct_0 @ sk_B)
% 0.17/0.52        | (v2_struct_0 @ sk_D)
% 0.17/0.52        | (v2_struct_0 @ sk_E)
% 0.17/0.52        | (v2_struct_0 @ sk_A))),
% 0.17/0.52      inference('sup-', [status(thm)], ['19', '128'])).
% 0.17/0.52  thf('130', plain,
% 0.17/0.52      ((m1_subset_1 @ (sk_C @ sk_G @ sk_A) @ 
% 0.17/0.52        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.17/0.52      inference('sup-', [status(thm)], ['10', '18'])).
% 0.17/0.52  thf(t3_subset, axiom,
% 0.17/0.52    (![A:$i,B:$i]:
% 0.17/0.52     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.17/0.52  thf('131', plain,
% 0.17/0.52      (![X0 : $i, X1 : $i]:
% 0.17/0.52         ((r1_tarski @ X0 @ X1) | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.17/0.52      inference('cnf', [status(esa)], [t3_subset])).
% 0.17/0.52  thf('132', plain,
% 0.17/0.52      ((r1_tarski @ (sk_C @ sk_G @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.17/0.52      inference('sup-', [status(thm)], ['130', '131'])).
% 0.17/0.52  thf('133', plain, ((m1_connsp_2 @ (sk_C @ sk_G @ sk_A) @ sk_A @ sk_G)),
% 0.17/0.52      inference('clc', [status(thm)], ['8', '9'])).
% 0.17/0.52  thf('134', plain,
% 0.17/0.52      (((r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G)
% 0.17/0.52        | (v2_struct_0 @ sk_B)
% 0.17/0.52        | (v2_struct_0 @ sk_D)
% 0.17/0.52        | (v2_struct_0 @ sk_E)
% 0.17/0.52        | (v2_struct_0 @ sk_A))),
% 0.17/0.52      inference('demod', [status(thm)], ['129', '132', '133'])).
% 0.17/0.52  thf('135', plain,
% 0.17/0.52      ((~ (r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_F))
% 0.17/0.52         <= (~ ((r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_F)))),
% 0.17/0.52      inference('split', [status(esa)], ['49'])).
% 0.17/0.52  thf('136', plain, (((sk_F) = (sk_G))),
% 0.17/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.52  thf('137', plain,
% 0.17/0.52      ((~ (r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G))
% 0.17/0.52         <= (~ ((r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_F)))),
% 0.17/0.52      inference('demod', [status(thm)], ['135', '136'])).
% 0.17/0.52  thf('138', plain, (~ ((r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_F))),
% 0.17/0.52      inference('sat_resolution*', [status(thm)], ['57', '79'])).
% 0.17/0.52  thf('139', plain, (~ (r1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G)),
% 0.17/0.52      inference('simpl_trail', [status(thm)], ['137', '138'])).
% 0.17/0.52  thf('140', plain,
% 0.17/0.52      (((v2_struct_0 @ sk_A)
% 0.17/0.52        | (v2_struct_0 @ sk_E)
% 0.17/0.52        | (v2_struct_0 @ sk_D)
% 0.17/0.52        | (v2_struct_0 @ sk_B))),
% 0.17/0.52      inference('sup-', [status(thm)], ['134', '139'])).
% 0.17/0.52  thf('141', plain, (~ (v2_struct_0 @ sk_A)),
% 0.17/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.52  thf('142', plain,
% 0.17/0.52      (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_E))),
% 0.17/0.52      inference('sup-', [status(thm)], ['140', '141'])).
% 0.17/0.52  thf('143', plain, (~ (v2_struct_0 @ sk_B)),
% 0.17/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.52  thf('144', plain, (((v2_struct_0 @ sk_E) | (v2_struct_0 @ sk_D))),
% 0.17/0.52      inference('clc', [status(thm)], ['142', '143'])).
% 0.17/0.52  thf('145', plain, (~ (v2_struct_0 @ sk_E)),
% 0.17/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.52  thf('146', plain, ((v2_struct_0 @ sk_D)),
% 0.17/0.52      inference('clc', [status(thm)], ['144', '145'])).
% 0.17/0.52  thf('147', plain, ($false), inference('demod', [status(thm)], ['0', '146'])).
% 0.17/0.52  
% 0.17/0.52  % SZS output end Refutation
% 0.17/0.52  
% 0.17/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
