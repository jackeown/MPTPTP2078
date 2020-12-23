%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.noIeez1Sl6

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:16 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  174 ( 474 expanded)
%              Number of leaves         :   32 ( 145 expanded)
%              Depth                    :   26
%              Number of atoms          : 2116 (20591 expanded)
%              Number of equality atoms :   12 ( 237 expanded)
%              Maximal formula depth    :   32 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_F_type,type,(
    sk_F: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(t84_tmap_1,conjecture,(
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
                        & ( v1_funct_2 @ E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) )
                     => ( ( m1_pre_topc @ C @ D )
                       => ! [F: $i] :
                            ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ D ) ) )
                           => ! [G: $i] :
                                ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) )
                               => ! [H: $i] :
                                    ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) )
                                   => ( ( ( v3_pre_topc @ F @ D )
                                        & ( r2_hidden @ G @ F )
                                        & ( r1_tarski @ F @ ( u1_struct_0 @ C ) )
                                        & ( G = H ) )
                                     => ( ( r1_tmap_1 @ D @ B @ E @ G )
                                      <=> ( r1_tmap_1 @ C @ B @ ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ H ) ) ) ) ) ) ) ) ) ) ) ) )).

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
                  & ( m1_pre_topc @ C @ A ) )
               => ! [D: $i] :
                    ( ( ~ ( v2_struct_0 @ D )
                      & ( m1_pre_topc @ D @ A ) )
                   => ! [E: $i] :
                        ( ( ( v1_funct_1 @ E )
                          & ( v1_funct_2 @ E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
                          & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) )
                       => ( ( m1_pre_topc @ C @ D )
                         => ! [F: $i] :
                              ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ D ) ) )
                             => ! [G: $i] :
                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) )
                                 => ! [H: $i] :
                                      ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) )
                                     => ( ( ( v3_pre_topc @ F @ D )
                                          & ( r2_hidden @ G @ F )
                                          & ( r1_tarski @ F @ ( u1_struct_0 @ C ) )
                                          & ( G = H ) )
                                       => ( ( r1_tmap_1 @ D @ B @ E @ G )
                                        <=> ( r1_tmap_1 @ C @ B @ ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ H ) ) ) ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t84_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t9_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ~ ( ( r2_hidden @ C @ B )
                    & ! [D: $i] :
                        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                       => ~ ( ( m1_connsp_2 @ D @ A @ C )
                            & ( r1_tarski @ D @ B ) ) ) ) ) ) ) ) )).

thf('5',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( v3_pre_topc @ X7 @ X8 )
      | ( m1_subset_1 @ ( sk_D @ X9 @ X7 @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( r2_hidden @ X9 @ X7 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t9_connsp_2])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D_1 )
      | ~ ( v2_pre_topc @ sk_D_1 )
      | ~ ( l1_pre_topc @ sk_D_1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_F )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_F @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
      | ~ ( v3_pre_topc @ sk_F @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_pre_topc @ sk_D_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('8',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_pre_topc @ X3 @ X4 )
      | ( v2_pre_topc @ X3 )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( v2_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('9',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v2_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,(
    m1_pre_topc @ sk_D_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('14',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_pre_topc @ X5 @ X6 )
      | ( l1_pre_topc @ X5 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('15',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    v3_pre_topc @ sk_F @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D_1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_F )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_F @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) ) ) ),
    inference(demod,[status(thm)],['6','12','17','18'])).

thf('20',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_H @ sk_F @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
    | ~ ( r2_hidden @ sk_H @ sk_F )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['3','19'])).

thf('21',plain,(
    r2_hidden @ sk_G @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    r2_hidden @ sk_H @ sk_F ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_H @ sk_F @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['20','23'])).

thf('25',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    m1_subset_1 @ ( sk_D @ sk_H @ sk_F @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_H )
    | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_H )
   <= ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_H ) ),
    inference(split,[status(esa)],['27'])).

thf('29',plain,
    ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_H )
    | ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_H )
    | ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H )
    | ~ ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_H ) ),
    inference(split,[status(esa)],['31'])).

thf('33',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_H )
    | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_H )
    | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H ) ),
    inference(split,[status(esa)],['37'])).

thf('39',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t81_tmap_1,axiom,(
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
                        & ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) )
                     => ! [F: $i] :
                          ( ( m1_subset_1 @ F @ ( u1_struct_0 @ C ) )
                         => ! [G: $i] :
                              ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) )
                             => ( ( ( F = G )
                                  & ( m1_pre_topc @ D @ C )
                                  & ( r1_tmap_1 @ C @ B @ E @ F ) )
                               => ( r1_tmap_1 @ D @ B @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ G ) ) ) ) ) ) ) ) ) )).

thf('40',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( v2_struct_0 @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ~ ( l1_pre_topc @ X14 )
      | ( v2_struct_0 @ X15 )
      | ~ ( m1_pre_topc @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X18 ) )
      | ~ ( m1_pre_topc @ X15 @ X18 )
      | ~ ( r1_tmap_1 @ X18 @ X14 @ X19 @ X17 )
      | ( X17 != X20 )
      | ( r1_tmap_1 @ X15 @ X14 @ ( k3_tmap_1 @ X16 @ X14 @ X18 @ X15 @ X19 ) @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X15 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X14 ) ) ) )
      | ~ ( v1_funct_2 @ X19 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X14 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( m1_pre_topc @ X18 @ X16 )
      | ( v2_struct_0 @ X18 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t81_tmap_1])).

thf('41',plain,(
    ! [X14: $i,X15: $i,X16: $i,X18: $i,X19: $i,X20: $i] :
      ( ( v2_struct_0 @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ~ ( l1_pre_topc @ X16 )
      | ( v2_struct_0 @ X18 )
      | ~ ( m1_pre_topc @ X18 @ X16 )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_funct_2 @ X19 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X14 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X14 ) ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X15 ) )
      | ( r1_tmap_1 @ X15 @ X14 @ ( k3_tmap_1 @ X16 @ X14 @ X18 @ X15 @ X19 ) @ X20 )
      | ~ ( r1_tmap_1 @ X18 @ X14 @ X19 @ X20 )
      | ~ ( m1_pre_topc @ X15 @ X18 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X18 ) )
      | ~ ( m1_pre_topc @ X15 @ X16 )
      | ( v2_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D_1 )
      | ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ X2 )
      | ( r1_tmap_1 @ X0 @ sk_B @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D_1 @ X0 @ sk_E ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( m1_pre_topc @ sk_D_1 @ X1 )
      | ( v2_struct_0 @ sk_D_1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['39','41'])).

thf('43',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D_1 )
      | ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ X2 )
      | ( r1_tmap_1 @ X0 @ sk_B @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D_1 @ X0 @ sk_E ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_D_1 @ X1 )
      | ( v2_struct_0 @ sk_D_1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['42','43','44','45','46'])).

thf('48',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ( v2_struct_0 @ sk_D_1 )
        | ~ ( m1_pre_topc @ sk_D_1 @ X0 )
        | ~ ( m1_subset_1 @ sk_H @ ( u1_struct_0 @ X1 ) )
        | ( r1_tmap_1 @ X1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D_1 @ X1 @ sk_E ) @ sk_H )
        | ~ ( m1_pre_topc @ X1 @ sk_D_1 )
        | ~ ( m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_D_1 ) )
        | ~ ( m1_pre_topc @ X1 @ X0 )
        | ( v2_struct_0 @ X1 )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H ) ),
    inference('sup-',[status(thm)],['38','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('50',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ( v2_struct_0 @ sk_D_1 )
        | ~ ( m1_pre_topc @ sk_D_1 @ X0 )
        | ~ ( m1_subset_1 @ sk_H @ ( u1_struct_0 @ X1 ) )
        | ( r1_tmap_1 @ X1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D_1 @ X1 @ sk_E ) @ sk_H )
        | ~ ( m1_pre_topc @ X1 @ sk_D_1 )
        | ~ ( m1_pre_topc @ X1 @ X0 )
        | ( v2_struct_0 @ X1 )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_C_1 )
        | ~ ( m1_pre_topc @ sk_C_1 @ X0 )
        | ~ ( m1_pre_topc @ sk_C_1 @ sk_D_1 )
        | ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_H )
        | ~ ( m1_pre_topc @ sk_D_1 @ X0 )
        | ( v2_struct_0 @ sk_D_1 )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 ) )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H ) ),
    inference('sup-',[status(thm)],['34','50'])).

thf('52',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_C_1 )
        | ~ ( m1_pre_topc @ sk_C_1 @ X0 )
        | ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_H )
        | ~ ( m1_pre_topc @ sk_D_1 @ X0 )
        | ( v2_struct_0 @ sk_D_1 )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 ) )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_D_1 )
      | ~ ( m1_pre_topc @ sk_D_1 @ sk_A )
      | ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_H )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H ) ),
    inference('sup-',[status(thm)],['33','53'])).

thf('55',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    m1_pre_topc @ sk_D_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D_1 )
      | ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_H )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H ) ),
    inference(demod,[status(thm)],['54','55','56','57'])).

thf('59',plain,
    ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_H )
    | ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_H )
   <= ~ ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_H ) ),
    inference(split,[status(esa)],['59'])).

thf('61',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_H )
      & ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H ) ) ),
    inference('sup-',[status(thm)],['58','60'])).

thf('62',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_H )
      & ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C_1 ) )
   <= ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_H )
      & ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H ) ) ),
    inference(clc,[status(thm)],['63','64'])).

thf('66',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( v2_struct_0 @ sk_C_1 )
   <= ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_H )
      & ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H ) ) ),
    inference(clc,[status(thm)],['65','66'])).

thf('68',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_H )
    | ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_H )
    | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H ) ),
    inference(split,[status(esa)],['37'])).

thf('71',plain,(
    r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_H ),
    inference('sat_resolution*',[status(thm)],['32','69','70'])).

thf('72',plain,(
    r1_tmap_1 @ sk_C_1 @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_H ),
    inference(simpl_trail,[status(thm)],['28','71'])).

thf('73',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t83_tmap_1,axiom,(
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
                        & ( v1_funct_2 @ E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) )
                     => ( ( m1_pre_topc @ C @ D )
                       => ! [F: $i] :
                            ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ D ) ) )
                           => ! [G: $i] :
                                ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) )
                               => ! [H: $i] :
                                    ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) )
                                   => ( ( ( r1_tarski @ F @ ( u1_struct_0 @ C ) )
                                        & ( m1_connsp_2 @ F @ D @ G )
                                        & ( G = H ) )
                                     => ( ( r1_tmap_1 @ D @ B @ E @ G )
                                      <=> ( r1_tmap_1 @ C @ B @ ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ H ) ) ) ) ) ) ) ) ) ) ) ) )).

thf('74',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( v2_struct_0 @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ( v2_struct_0 @ X22 )
      | ~ ( m1_pre_topc @ X22 @ X23 )
      | ~ ( m1_pre_topc @ X24 @ X22 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X24 ) )
      | ~ ( r1_tmap_1 @ X24 @ X21 @ ( k3_tmap_1 @ X23 @ X21 @ X22 @ X24 @ X27 ) @ X26 )
      | ( r1_tmap_1 @ X22 @ X21 @ X27 @ X28 )
      | ( X28 != X26 )
      | ~ ( m1_connsp_2 @ X25 @ X22 @ X28 )
      | ~ ( r1_tarski @ X25 @ ( u1_struct_0 @ X24 ) )
      | ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X22 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X21 ) ) ) )
      | ~ ( v1_funct_2 @ X27 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X21 ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( m1_pre_topc @ X24 @ X23 )
      | ( v2_struct_0 @ X24 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t83_tmap_1])).

thf('75',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( v2_struct_0 @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ~ ( l1_pre_topc @ X23 )
      | ( v2_struct_0 @ X24 )
      | ~ ( m1_pre_topc @ X24 @ X23 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_funct_2 @ X27 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X21 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X21 ) ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X22 ) )
      | ~ ( r1_tarski @ X25 @ ( u1_struct_0 @ X24 ) )
      | ~ ( m1_connsp_2 @ X25 @ X22 @ X26 )
      | ( r1_tmap_1 @ X22 @ X21 @ X27 @ X26 )
      | ~ ( r1_tmap_1 @ X24 @ X21 @ ( k3_tmap_1 @ X23 @ X21 @ X22 @ X24 @ X27 ) @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X24 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( m1_pre_topc @ X24 @ X22 )
      | ~ ( m1_pre_topc @ X22 @ X23 )
      | ( v2_struct_0 @ X22 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_D_1 )
      | ~ ( m1_pre_topc @ sk_D_1 @ X0 )
      | ~ ( m1_pre_topc @ X1 @ sk_D_1 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_tmap_1 @ X1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D_1 @ X1 @ sk_E ) @ X3 )
      | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ X3 )
      | ~ ( m1_connsp_2 @ X2 @ sk_D_1 @ X3 )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['73','75'])).

thf('77',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 )
      | ~ ( m1_pre_topc @ sk_D_1 @ X0 )
      | ~ ( m1_pre_topc @ X1 @ sk_D_1 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_tmap_1 @ X1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D_1 @ X1 @ sk_E ) @ X3 )
      | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ X3 )
      | ~ ( m1_connsp_2 @ X2 @ sk_D_1 @ X3 )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['76','77','78','79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_C_1 )
      | ~ ( m1_pre_topc @ sk_C_1 @ sk_A )
      | ~ ( m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( m1_connsp_2 @ X0 @ sk_D_1 @ sk_H )
      | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H )
      | ~ ( m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
      | ~ ( m1_pre_topc @ sk_C_1 @ sk_D_1 )
      | ~ ( m1_pre_topc @ sk_D_1 @ sk_A )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['72','81'])).

thf('83',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('87',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    m1_pre_topc @ sk_D_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C_1 )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( m1_connsp_2 @ X0 @ sk_D_1 @ sk_H )
      | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['82','83','84','85','86','87','88','89'])).

thf('91',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 )
    | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H )
    | ~ ( m1_connsp_2 @ ( sk_D @ sk_H @ sk_F @ sk_D_1 ) @ sk_D_1 @ sk_H )
    | ~ ( r1_tarski @ ( sk_D @ sk_H @ sk_F @ sk_D_1 ) @ ( u1_struct_0 @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['26','90'])).

thf('92',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('93',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( v3_pre_topc @ X7 @ X8 )
      | ( m1_connsp_2 @ ( sk_D @ X9 @ X7 @ X8 ) @ X8 @ X9 )
      | ~ ( r2_hidden @ X9 @ X7 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t9_connsp_2])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D_1 )
      | ~ ( v2_pre_topc @ sk_D_1 )
      | ~ ( l1_pre_topc @ sk_D_1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_F )
      | ( m1_connsp_2 @ ( sk_D @ X0 @ sk_F @ sk_D_1 ) @ sk_D_1 @ X0 )
      | ~ ( v3_pre_topc @ sk_F @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    v2_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('97',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('98',plain,(
    v3_pre_topc @ sk_F @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D_1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_F )
      | ( m1_connsp_2 @ ( sk_D @ X0 @ sk_F @ sk_D_1 ) @ sk_D_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['95','96','97','98'])).

thf('100',plain,
    ( ( m1_connsp_2 @ ( sk_D @ sk_H @ sk_F @ sk_D_1 ) @ sk_D_1 @ sk_H )
    | ~ ( r2_hidden @ sk_H @ sk_F )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['92','99'])).

thf('101',plain,(
    r2_hidden @ sk_H @ sk_F ),
    inference(demod,[status(thm)],['21','22'])).

thf('102',plain,
    ( ( m1_connsp_2 @ ( sk_D @ sk_H @ sk_F @ sk_D_1 ) @ sk_D_1 @ sk_H )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    m1_connsp_2 @ ( sk_D @ sk_H @ sk_F @ sk_D_1 ) @ sk_D_1 @ sk_H ),
    inference(clc,[status(thm)],['102','103'])).

thf('105',plain,(
    r1_tarski @ sk_F @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('107',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( v3_pre_topc @ X7 @ X8 )
      | ( r1_tarski @ ( sk_D @ X9 @ X7 @ X8 ) @ X7 )
      | ~ ( r2_hidden @ X9 @ X7 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t9_connsp_2])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D_1 )
      | ~ ( v2_pre_topc @ sk_D_1 )
      | ~ ( l1_pre_topc @ sk_D_1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_F )
      | ( r1_tarski @ ( sk_D @ X0 @ sk_F @ sk_D_1 ) @ sk_F )
      | ~ ( v3_pre_topc @ sk_F @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    v2_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('111',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('112',plain,(
    v3_pre_topc @ sk_F @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D_1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_F )
      | ( r1_tarski @ ( sk_D @ X0 @ sk_F @ sk_D_1 ) @ sk_F ) ) ),
    inference(demod,[status(thm)],['109','110','111','112'])).

thf('114',plain,
    ( ( r1_tarski @ ( sk_D @ sk_H @ sk_F @ sk_D_1 ) @ sk_F )
    | ~ ( r2_hidden @ sk_H @ sk_F )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['106','113'])).

thf('115',plain,(
    r2_hidden @ sk_H @ sk_F ),
    inference(demod,[status(thm)],['21','22'])).

thf('116',plain,
    ( ( r1_tarski @ ( sk_D @ sk_H @ sk_F @ sk_D_1 ) @ sk_F )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    r1_tarski @ ( sk_D @ sk_H @ sk_F @ sk_D_1 ) @ sk_F ),
    inference(clc,[status(thm)],['116','117'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('119',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( sk_D @ sk_H @ sk_F @ sk_D_1 ) @ X0 )
      | ~ ( r1_tarski @ sk_F @ X0 ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    r1_tarski @ ( sk_D @ sk_H @ sk_F @ sk_D_1 ) @ ( u1_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['105','120'])).

thf('122',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 )
    | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['91','104','121'])).

thf('123',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G )
   <= ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G ) ),
    inference(split,[status(esa)],['59'])).

thf('124',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H )
   <= ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G ) ),
    inference(split,[status(esa)],['27'])).

thf('127',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H )
   <= ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H ) ),
    inference(split,[status(esa)],['31'])).

thf('130',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G )
    | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G ) ),
    inference('sat_resolution*',[status(thm)],['32','69','130'])).

thf('132',plain,(
    ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H ) ),
    inference(simpl_trail,[status(thm)],['125','131'])).

thf('133',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['122','132'])).

thf('134',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['135','136'])).

thf('138',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    v2_struct_0 @ sk_C_1 ),
    inference(clc,[status(thm)],['137','138'])).

thf('140',plain,(
    $false ),
    inference(demod,[status(thm)],['0','139'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.noIeez1Sl6
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:29:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.53  % Solved by: fo/fo7.sh
% 0.21/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.53  % done 95 iterations in 0.061s
% 0.21/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.53  % SZS output start Refutation
% 0.21/0.53  thf(sk_F_type, type, sk_F: $i).
% 0.21/0.53  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.53  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.21/0.53  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.53  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.21/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.53  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.53  thf(sk_H_type, type, sk_H: $i).
% 0.21/0.53  thf(sk_G_type, type, sk_G: $i).
% 0.21/0.53  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.53  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.53  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.21/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.53  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.21/0.53  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.21/0.53  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.21/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.53  thf(sk_E_type, type, sk_E: $i).
% 0.21/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.53  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.53  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.21/0.53  thf(t84_tmap_1, conjecture,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.53             ( l1_pre_topc @ B ) ) =>
% 0.21/0.53           ( ![C:$i]:
% 0.21/0.53             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.21/0.53               ( ![D:$i]:
% 0.21/0.53                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.21/0.53                   ( ![E:$i]:
% 0.21/0.53                     ( ( ( v1_funct_1 @ E ) & 
% 0.21/0.53                         ( v1_funct_2 @
% 0.21/0.53                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.53                         ( m1_subset_1 @
% 0.21/0.53                           E @ 
% 0.21/0.53                           ( k1_zfmisc_1 @
% 0.21/0.53                             ( k2_zfmisc_1 @
% 0.21/0.53                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.53                       ( ( m1_pre_topc @ C @ D ) =>
% 0.21/0.53                         ( ![F:$i]:
% 0.21/0.53                           ( ( m1_subset_1 @
% 0.21/0.53                               F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ D ) ) ) =>
% 0.21/0.53                             ( ![G:$i]:
% 0.21/0.53                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.21/0.53                                 ( ![H:$i]:
% 0.21/0.53                                   ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) ) =>
% 0.21/0.53                                     ( ( ( v3_pre_topc @ F @ D ) & 
% 0.21/0.53                                         ( r2_hidden @ G @ F ) & 
% 0.21/0.53                                         ( r1_tarski @ F @ ( u1_struct_0 @ C ) ) & 
% 0.21/0.53                                         ( ( G ) = ( H ) ) ) =>
% 0.21/0.53                                       ( ( r1_tmap_1 @ D @ B @ E @ G ) <=>
% 0.21/0.53                                         ( r1_tmap_1 @
% 0.21/0.53                                           C @ B @ 
% 0.21/0.53                                           ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ 
% 0.21/0.53                                           H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.53    (~( ![A:$i]:
% 0.21/0.53        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.53            ( l1_pre_topc @ A ) ) =>
% 0.21/0.53          ( ![B:$i]:
% 0.21/0.53            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.53                ( l1_pre_topc @ B ) ) =>
% 0.21/0.53              ( ![C:$i]:
% 0.21/0.53                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.21/0.53                  ( ![D:$i]:
% 0.21/0.53                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.21/0.53                      ( ![E:$i]:
% 0.21/0.53                        ( ( ( v1_funct_1 @ E ) & 
% 0.21/0.53                            ( v1_funct_2 @
% 0.21/0.53                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.53                            ( m1_subset_1 @
% 0.21/0.53                              E @ 
% 0.21/0.53                              ( k1_zfmisc_1 @
% 0.21/0.53                                ( k2_zfmisc_1 @
% 0.21/0.53                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.53                          ( ( m1_pre_topc @ C @ D ) =>
% 0.21/0.53                            ( ![F:$i]:
% 0.21/0.53                              ( ( m1_subset_1 @
% 0.21/0.53                                  F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ D ) ) ) =>
% 0.21/0.53                                ( ![G:$i]:
% 0.21/0.53                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.21/0.53                                    ( ![H:$i]:
% 0.21/0.53                                      ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) ) =>
% 0.21/0.53                                        ( ( ( v3_pre_topc @ F @ D ) & 
% 0.21/0.53                                            ( r2_hidden @ G @ F ) & 
% 0.21/0.53                                            ( r1_tarski @
% 0.21/0.53                                              F @ ( u1_struct_0 @ C ) ) & 
% 0.21/0.53                                            ( ( G ) = ( H ) ) ) =>
% 0.21/0.53                                          ( ( r1_tmap_1 @ D @ B @ E @ G ) <=>
% 0.21/0.53                                            ( r1_tmap_1 @
% 0.21/0.53                                              C @ B @ 
% 0.21/0.53                                              ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ 
% 0.21/0.53                                              H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.53    inference('cnf.neg', [status(esa)], [t84_tmap_1])).
% 0.21/0.53  thf('0', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('1', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_D_1))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('2', plain, (((sk_G) = (sk_H))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('3', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D_1))),
% 0.21/0.53      inference('demod', [status(thm)], ['1', '2'])).
% 0.21/0.53  thf('4', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(t9_connsp_2, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.53           ( ( v3_pre_topc @ B @ A ) <=>
% 0.21/0.53             ( ![C:$i]:
% 0.21/0.53               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.53                 ( ~( ( r2_hidden @ C @ B ) & 
% 0.21/0.53                      ( ![D:$i]:
% 0.21/0.53                        ( ( m1_subset_1 @
% 0.21/0.53                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.53                          ( ~( ( m1_connsp_2 @ D @ A @ C ) & 
% 0.21/0.53                               ( r1_tarski @ D @ B ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.53  thf('5', plain,
% 0.21/0.53      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.21/0.53          | ~ (v3_pre_topc @ X7 @ X8)
% 0.21/0.53          | (m1_subset_1 @ (sk_D @ X9 @ X7 @ X8) @ 
% 0.21/0.53             (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.21/0.53          | ~ (r2_hidden @ X9 @ X7)
% 0.21/0.53          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X8))
% 0.21/0.53          | ~ (l1_pre_topc @ X8)
% 0.21/0.53          | ~ (v2_pre_topc @ X8)
% 0.21/0.53          | (v2_struct_0 @ X8))),
% 0.21/0.53      inference('cnf', [status(esa)], [t9_connsp_2])).
% 0.21/0.53  thf('6', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v2_struct_0 @ sk_D_1)
% 0.21/0.53          | ~ (v2_pre_topc @ sk_D_1)
% 0.21/0.53          | ~ (l1_pre_topc @ sk_D_1)
% 0.21/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.21/0.53          | ~ (r2_hidden @ X0 @ sk_F)
% 0.21/0.53          | (m1_subset_1 @ (sk_D @ X0 @ sk_F @ sk_D_1) @ 
% 0.21/0.53             (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.21/0.53          | ~ (v3_pre_topc @ sk_F @ sk_D_1))),
% 0.21/0.53      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.53  thf('7', plain, ((m1_pre_topc @ sk_D_1 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(cc1_pre_topc, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.53       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.21/0.53  thf('8', plain,
% 0.21/0.53      (![X3 : $i, X4 : $i]:
% 0.21/0.53         (~ (m1_pre_topc @ X3 @ X4)
% 0.21/0.53          | (v2_pre_topc @ X3)
% 0.21/0.53          | ~ (l1_pre_topc @ X4)
% 0.21/0.53          | ~ (v2_pre_topc @ X4))),
% 0.21/0.53      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.21/0.53  thf('9', plain,
% 0.21/0.53      ((~ (v2_pre_topc @ sk_A)
% 0.21/0.53        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.53        | (v2_pre_topc @ sk_D_1))),
% 0.21/0.53      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.53  thf('10', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('12', plain, ((v2_pre_topc @ sk_D_1)),
% 0.21/0.53      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.21/0.53  thf('13', plain, ((m1_pre_topc @ sk_D_1 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(dt_m1_pre_topc, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( l1_pre_topc @ A ) =>
% 0.21/0.53       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.21/0.53  thf('14', plain,
% 0.21/0.53      (![X5 : $i, X6 : $i]:
% 0.21/0.53         (~ (m1_pre_topc @ X5 @ X6) | (l1_pre_topc @ X5) | ~ (l1_pre_topc @ X6))),
% 0.21/0.53      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.21/0.53  thf('15', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D_1))),
% 0.21/0.53      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.53  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('17', plain, ((l1_pre_topc @ sk_D_1)),
% 0.21/0.53      inference('demod', [status(thm)], ['15', '16'])).
% 0.21/0.53  thf('18', plain, ((v3_pre_topc @ sk_F @ sk_D_1)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('19', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v2_struct_0 @ sk_D_1)
% 0.21/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.21/0.53          | ~ (r2_hidden @ X0 @ sk_F)
% 0.21/0.53          | (m1_subset_1 @ (sk_D @ X0 @ sk_F @ sk_D_1) @ 
% 0.21/0.53             (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1))))),
% 0.21/0.53      inference('demod', [status(thm)], ['6', '12', '17', '18'])).
% 0.21/0.53  thf('20', plain,
% 0.21/0.53      (((m1_subset_1 @ (sk_D @ sk_H @ sk_F @ sk_D_1) @ 
% 0.21/0.53         (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.21/0.53        | ~ (r2_hidden @ sk_H @ sk_F)
% 0.21/0.53        | (v2_struct_0 @ sk_D_1))),
% 0.21/0.53      inference('sup-', [status(thm)], ['3', '19'])).
% 0.21/0.53  thf('21', plain, ((r2_hidden @ sk_G @ sk_F)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('22', plain, (((sk_G) = (sk_H))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('23', plain, ((r2_hidden @ sk_H @ sk_F)),
% 0.21/0.53      inference('demod', [status(thm)], ['21', '22'])).
% 0.21/0.53  thf('24', plain,
% 0.21/0.53      (((m1_subset_1 @ (sk_D @ sk_H @ sk_F @ sk_D_1) @ 
% 0.21/0.53         (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.21/0.53        | (v2_struct_0 @ sk_D_1))),
% 0.21/0.53      inference('demod', [status(thm)], ['20', '23'])).
% 0.21/0.53  thf('25', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('26', plain,
% 0.21/0.53      ((m1_subset_1 @ (sk_D @ sk_H @ sk_F @ sk_D_1) @ 
% 0.21/0.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))),
% 0.21/0.53      inference('clc', [status(thm)], ['24', '25'])).
% 0.21/0.53  thf('27', plain,
% 0.21/0.53      (((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.21/0.53         (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_H)
% 0.21/0.53        | (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('28', plain,
% 0.21/0.53      (((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.21/0.53         (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_H))
% 0.21/0.53         <= (((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.21/0.53               (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_H)))),
% 0.21/0.53      inference('split', [status(esa)], ['27'])).
% 0.21/0.53  thf('29', plain,
% 0.21/0.53      ((~ (r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.21/0.53           (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_H)
% 0.21/0.53        | ~ (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('30', plain, (((sk_G) = (sk_H))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('31', plain,
% 0.21/0.53      ((~ (r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.21/0.53           (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_H)
% 0.21/0.53        | ~ (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H))),
% 0.21/0.53      inference('demod', [status(thm)], ['29', '30'])).
% 0.21/0.53  thf('32', plain,
% 0.21/0.53      (~ ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H)) | 
% 0.21/0.53       ~
% 0.21/0.53       ((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.21/0.53         (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_H))),
% 0.21/0.53      inference('split', [status(esa)], ['31'])).
% 0.21/0.53  thf('33', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('34', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_C_1))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('35', plain,
% 0.21/0.53      (((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.21/0.53         (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_H)
% 0.21/0.53        | (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('36', plain, (((sk_G) = (sk_H))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('37', plain,
% 0.21/0.53      (((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.21/0.53         (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_H)
% 0.21/0.53        | (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H))),
% 0.21/0.53      inference('demod', [status(thm)], ['35', '36'])).
% 0.21/0.53  thf('38', plain,
% 0.21/0.53      (((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H))
% 0.21/0.53         <= (((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H)))),
% 0.21/0.53      inference('split', [status(esa)], ['37'])).
% 0.21/0.53  thf('39', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_E @ 
% 0.21/0.53        (k1_zfmisc_1 @ 
% 0.21/0.53         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(t81_tmap_1, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.53             ( l1_pre_topc @ B ) ) =>
% 0.21/0.53           ( ![C:$i]:
% 0.21/0.53             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.21/0.53               ( ![D:$i]:
% 0.21/0.53                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.21/0.53                   ( ![E:$i]:
% 0.21/0.53                     ( ( ( v1_funct_1 @ E ) & 
% 0.21/0.53                         ( v1_funct_2 @
% 0.21/0.53                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.53                         ( m1_subset_1 @
% 0.21/0.53                           E @ 
% 0.21/0.53                           ( k1_zfmisc_1 @
% 0.21/0.53                             ( k2_zfmisc_1 @
% 0.21/0.53                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.53                       ( ![F:$i]:
% 0.21/0.53                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ C ) ) =>
% 0.21/0.53                           ( ![G:$i]:
% 0.21/0.53                             ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.21/0.53                               ( ( ( ( F ) = ( G ) ) & 
% 0.21/0.53                                   ( m1_pre_topc @ D @ C ) & 
% 0.21/0.53                                   ( r1_tmap_1 @ C @ B @ E @ F ) ) =>
% 0.21/0.53                                 ( r1_tmap_1 @
% 0.21/0.53                                   D @ B @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ 
% 0.21/0.53                                   G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.53  thf('40', plain,
% 0.21/0.53      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.21/0.53         ((v2_struct_0 @ X14)
% 0.21/0.53          | ~ (v2_pre_topc @ X14)
% 0.21/0.53          | ~ (l1_pre_topc @ X14)
% 0.21/0.53          | (v2_struct_0 @ X15)
% 0.21/0.53          | ~ (m1_pre_topc @ X15 @ X16)
% 0.21/0.53          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X18))
% 0.21/0.53          | ~ (m1_pre_topc @ X15 @ X18)
% 0.21/0.53          | ~ (r1_tmap_1 @ X18 @ X14 @ X19 @ X17)
% 0.21/0.53          | ((X17) != (X20))
% 0.21/0.53          | (r1_tmap_1 @ X15 @ X14 @ 
% 0.21/0.53             (k3_tmap_1 @ X16 @ X14 @ X18 @ X15 @ X19) @ X20)
% 0.21/0.53          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X15))
% 0.21/0.53          | ~ (m1_subset_1 @ X19 @ 
% 0.21/0.53               (k1_zfmisc_1 @ 
% 0.21/0.53                (k2_zfmisc_1 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X14))))
% 0.21/0.53          | ~ (v1_funct_2 @ X19 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X14))
% 0.21/0.53          | ~ (v1_funct_1 @ X19)
% 0.21/0.53          | ~ (m1_pre_topc @ X18 @ X16)
% 0.21/0.53          | (v2_struct_0 @ X18)
% 0.21/0.53          | ~ (l1_pre_topc @ X16)
% 0.21/0.53          | ~ (v2_pre_topc @ X16)
% 0.21/0.53          | (v2_struct_0 @ X16))),
% 0.21/0.53      inference('cnf', [status(esa)], [t81_tmap_1])).
% 0.21/0.53  thf('41', plain,
% 0.21/0.53      (![X14 : $i, X15 : $i, X16 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.21/0.53         ((v2_struct_0 @ X16)
% 0.21/0.53          | ~ (v2_pre_topc @ X16)
% 0.21/0.53          | ~ (l1_pre_topc @ X16)
% 0.21/0.53          | (v2_struct_0 @ X18)
% 0.21/0.53          | ~ (m1_pre_topc @ X18 @ X16)
% 0.21/0.53          | ~ (v1_funct_1 @ X19)
% 0.21/0.53          | ~ (v1_funct_2 @ X19 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X14))
% 0.21/0.53          | ~ (m1_subset_1 @ X19 @ 
% 0.21/0.53               (k1_zfmisc_1 @ 
% 0.21/0.53                (k2_zfmisc_1 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X14))))
% 0.21/0.53          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X15))
% 0.21/0.53          | (r1_tmap_1 @ X15 @ X14 @ 
% 0.21/0.53             (k3_tmap_1 @ X16 @ X14 @ X18 @ X15 @ X19) @ X20)
% 0.21/0.53          | ~ (r1_tmap_1 @ X18 @ X14 @ X19 @ X20)
% 0.21/0.53          | ~ (m1_pre_topc @ X15 @ X18)
% 0.21/0.53          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X18))
% 0.21/0.53          | ~ (m1_pre_topc @ X15 @ X16)
% 0.21/0.53          | (v2_struct_0 @ X15)
% 0.21/0.53          | ~ (l1_pre_topc @ X14)
% 0.21/0.53          | ~ (v2_pre_topc @ X14)
% 0.21/0.53          | (v2_struct_0 @ X14))),
% 0.21/0.53      inference('simplify', [status(thm)], ['40'])).
% 0.21/0.53  thf('42', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         ((v2_struct_0 @ sk_B)
% 0.21/0.53          | ~ (v2_pre_topc @ sk_B)
% 0.21/0.53          | ~ (l1_pre_topc @ sk_B)
% 0.21/0.53          | (v2_struct_0 @ X0)
% 0.21/0.53          | ~ (m1_pre_topc @ X0 @ X1)
% 0.21/0.53          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D_1))
% 0.21/0.53          | ~ (m1_pre_topc @ X0 @ sk_D_1)
% 0.21/0.53          | ~ (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ X2)
% 0.21/0.53          | (r1_tmap_1 @ X0 @ sk_B @ 
% 0.21/0.53             (k3_tmap_1 @ X1 @ sk_B @ sk_D_1 @ X0 @ sk_E) @ X2)
% 0.21/0.53          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.21/0.53          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D_1) @ 
% 0.21/0.53               (u1_struct_0 @ sk_B))
% 0.21/0.53          | ~ (v1_funct_1 @ sk_E)
% 0.21/0.53          | ~ (m1_pre_topc @ sk_D_1 @ X1)
% 0.21/0.53          | (v2_struct_0 @ sk_D_1)
% 0.21/0.53          | ~ (l1_pre_topc @ X1)
% 0.21/0.53          | ~ (v2_pre_topc @ X1)
% 0.21/0.53          | (v2_struct_0 @ X1))),
% 0.21/0.53      inference('sup-', [status(thm)], ['39', '41'])).
% 0.21/0.53  thf('43', plain, ((v2_pre_topc @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('44', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('45', plain,
% 0.21/0.53      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('46', plain, ((v1_funct_1 @ sk_E)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('47', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         ((v2_struct_0 @ sk_B)
% 0.21/0.53          | (v2_struct_0 @ X0)
% 0.21/0.53          | ~ (m1_pre_topc @ X0 @ X1)
% 0.21/0.53          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D_1))
% 0.21/0.53          | ~ (m1_pre_topc @ X0 @ sk_D_1)
% 0.21/0.53          | ~ (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ X2)
% 0.21/0.53          | (r1_tmap_1 @ X0 @ sk_B @ 
% 0.21/0.53             (k3_tmap_1 @ X1 @ sk_B @ sk_D_1 @ X0 @ sk_E) @ X2)
% 0.21/0.53          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.21/0.53          | ~ (m1_pre_topc @ sk_D_1 @ X1)
% 0.21/0.53          | (v2_struct_0 @ sk_D_1)
% 0.21/0.53          | ~ (l1_pre_topc @ X1)
% 0.21/0.53          | ~ (v2_pre_topc @ X1)
% 0.21/0.53          | (v2_struct_0 @ X1))),
% 0.21/0.53      inference('demod', [status(thm)], ['42', '43', '44', '45', '46'])).
% 0.21/0.53  thf('48', plain,
% 0.21/0.53      ((![X0 : $i, X1 : $i]:
% 0.21/0.53          ((v2_struct_0 @ X0)
% 0.21/0.53           | ~ (v2_pre_topc @ X0)
% 0.21/0.53           | ~ (l1_pre_topc @ X0)
% 0.21/0.53           | (v2_struct_0 @ sk_D_1)
% 0.21/0.53           | ~ (m1_pre_topc @ sk_D_1 @ X0)
% 0.21/0.53           | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ X1))
% 0.21/0.53           | (r1_tmap_1 @ X1 @ sk_B @ 
% 0.21/0.53              (k3_tmap_1 @ X0 @ sk_B @ sk_D_1 @ X1 @ sk_E) @ sk_H)
% 0.21/0.53           | ~ (m1_pre_topc @ X1 @ sk_D_1)
% 0.21/0.53           | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D_1))
% 0.21/0.53           | ~ (m1_pre_topc @ X1 @ X0)
% 0.21/0.53           | (v2_struct_0 @ X1)
% 0.21/0.53           | (v2_struct_0 @ sk_B)))
% 0.21/0.53         <= (((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['38', '47'])).
% 0.21/0.53  thf('49', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D_1))),
% 0.21/0.53      inference('demod', [status(thm)], ['1', '2'])).
% 0.21/0.53  thf('50', plain,
% 0.21/0.53      ((![X0 : $i, X1 : $i]:
% 0.21/0.53          ((v2_struct_0 @ X0)
% 0.21/0.53           | ~ (v2_pre_topc @ X0)
% 0.21/0.53           | ~ (l1_pre_topc @ X0)
% 0.21/0.53           | (v2_struct_0 @ sk_D_1)
% 0.21/0.53           | ~ (m1_pre_topc @ sk_D_1 @ X0)
% 0.21/0.53           | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ X1))
% 0.21/0.53           | (r1_tmap_1 @ X1 @ sk_B @ 
% 0.21/0.53              (k3_tmap_1 @ X0 @ sk_B @ sk_D_1 @ X1 @ sk_E) @ sk_H)
% 0.21/0.53           | ~ (m1_pre_topc @ X1 @ sk_D_1)
% 0.21/0.53           | ~ (m1_pre_topc @ X1 @ X0)
% 0.21/0.53           | (v2_struct_0 @ X1)
% 0.21/0.53           | (v2_struct_0 @ sk_B)))
% 0.21/0.53         <= (((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H)))),
% 0.21/0.53      inference('demod', [status(thm)], ['48', '49'])).
% 0.21/0.53  thf('51', plain,
% 0.21/0.53      ((![X0 : $i]:
% 0.21/0.53          ((v2_struct_0 @ sk_B)
% 0.21/0.53           | (v2_struct_0 @ sk_C_1)
% 0.21/0.53           | ~ (m1_pre_topc @ sk_C_1 @ X0)
% 0.21/0.53           | ~ (m1_pre_topc @ sk_C_1 @ sk_D_1)
% 0.21/0.53           | (r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.21/0.53              (k3_tmap_1 @ X0 @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_H)
% 0.21/0.53           | ~ (m1_pre_topc @ sk_D_1 @ X0)
% 0.21/0.53           | (v2_struct_0 @ sk_D_1)
% 0.21/0.53           | ~ (l1_pre_topc @ X0)
% 0.21/0.53           | ~ (v2_pre_topc @ X0)
% 0.21/0.53           | (v2_struct_0 @ X0)))
% 0.21/0.53         <= (((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['34', '50'])).
% 0.21/0.53  thf('52', plain, ((m1_pre_topc @ sk_C_1 @ sk_D_1)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('53', plain,
% 0.21/0.53      ((![X0 : $i]:
% 0.21/0.53          ((v2_struct_0 @ sk_B)
% 0.21/0.53           | (v2_struct_0 @ sk_C_1)
% 0.21/0.53           | ~ (m1_pre_topc @ sk_C_1 @ X0)
% 0.21/0.53           | (r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.21/0.53              (k3_tmap_1 @ X0 @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_H)
% 0.21/0.53           | ~ (m1_pre_topc @ sk_D_1 @ X0)
% 0.21/0.53           | (v2_struct_0 @ sk_D_1)
% 0.21/0.53           | ~ (l1_pre_topc @ X0)
% 0.21/0.53           | ~ (v2_pre_topc @ X0)
% 0.21/0.53           | (v2_struct_0 @ X0)))
% 0.21/0.53         <= (((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H)))),
% 0.21/0.53      inference('demod', [status(thm)], ['51', '52'])).
% 0.21/0.53  thf('54', plain,
% 0.21/0.53      ((((v2_struct_0 @ sk_A)
% 0.21/0.53         | ~ (v2_pre_topc @ sk_A)
% 0.21/0.53         | ~ (l1_pre_topc @ sk_A)
% 0.21/0.53         | (v2_struct_0 @ sk_D_1)
% 0.21/0.53         | ~ (m1_pre_topc @ sk_D_1 @ sk_A)
% 0.21/0.53         | (r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.21/0.53            (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_H)
% 0.21/0.53         | (v2_struct_0 @ sk_C_1)
% 0.21/0.53         | (v2_struct_0 @ sk_B)))
% 0.21/0.53         <= (((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['33', '53'])).
% 0.21/0.53  thf('55', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('56', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('57', plain, ((m1_pre_topc @ sk_D_1 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('58', plain,
% 0.21/0.53      ((((v2_struct_0 @ sk_A)
% 0.21/0.53         | (v2_struct_0 @ sk_D_1)
% 0.21/0.53         | (r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.21/0.53            (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_H)
% 0.21/0.53         | (v2_struct_0 @ sk_C_1)
% 0.21/0.53         | (v2_struct_0 @ sk_B)))
% 0.21/0.53         <= (((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H)))),
% 0.21/0.53      inference('demod', [status(thm)], ['54', '55', '56', '57'])).
% 0.21/0.53  thf('59', plain,
% 0.21/0.53      ((~ (r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.21/0.53           (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_H)
% 0.21/0.53        | ~ (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('60', plain,
% 0.21/0.53      ((~ (r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.21/0.53           (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_H))
% 0.21/0.53         <= (~
% 0.21/0.53             ((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.21/0.53               (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_H)))),
% 0.21/0.53      inference('split', [status(esa)], ['59'])).
% 0.21/0.53  thf('61', plain,
% 0.21/0.53      ((((v2_struct_0 @ sk_B)
% 0.21/0.53         | (v2_struct_0 @ sk_C_1)
% 0.21/0.53         | (v2_struct_0 @ sk_D_1)
% 0.21/0.53         | (v2_struct_0 @ sk_A)))
% 0.21/0.53         <= (~
% 0.21/0.53             ((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.21/0.53               (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_H)) & 
% 0.21/0.53             ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['58', '60'])).
% 0.21/0.53  thf('62', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('63', plain,
% 0.21/0.53      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C_1) | (v2_struct_0 @ sk_B)))
% 0.21/0.53         <= (~
% 0.21/0.53             ((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.21/0.53               (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_H)) & 
% 0.21/0.53             ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['61', '62'])).
% 0.21/0.53  thf('64', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('65', plain,
% 0.21/0.53      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C_1)))
% 0.21/0.53         <= (~
% 0.21/0.53             ((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.21/0.53               (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_H)) & 
% 0.21/0.53             ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H)))),
% 0.21/0.53      inference('clc', [status(thm)], ['63', '64'])).
% 0.21/0.53  thf('66', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('67', plain,
% 0.21/0.53      (((v2_struct_0 @ sk_C_1))
% 0.21/0.53         <= (~
% 0.21/0.53             ((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.21/0.53               (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_H)) & 
% 0.21/0.53             ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H)))),
% 0.21/0.53      inference('clc', [status(thm)], ['65', '66'])).
% 0.21/0.53  thf('68', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('69', plain,
% 0.21/0.53      (((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.21/0.53         (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_H)) | 
% 0.21/0.53       ~ ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H))),
% 0.21/0.53      inference('sup-', [status(thm)], ['67', '68'])).
% 0.21/0.53  thf('70', plain,
% 0.21/0.53      (((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.21/0.53         (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_H)) | 
% 0.21/0.53       ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H))),
% 0.21/0.53      inference('split', [status(esa)], ['37'])).
% 0.21/0.53  thf('71', plain,
% 0.21/0.53      (((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.21/0.53         (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_H))),
% 0.21/0.53      inference('sat_resolution*', [status(thm)], ['32', '69', '70'])).
% 0.21/0.53  thf('72', plain,
% 0.21/0.53      ((r1_tmap_1 @ sk_C_1 @ sk_B @ 
% 0.21/0.53        (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_H)),
% 0.21/0.53      inference('simpl_trail', [status(thm)], ['28', '71'])).
% 0.21/0.53  thf('73', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_E @ 
% 0.21/0.53        (k1_zfmisc_1 @ 
% 0.21/0.53         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(t83_tmap_1, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.53             ( l1_pre_topc @ B ) ) =>
% 0.21/0.53           ( ![C:$i]:
% 0.21/0.53             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.21/0.53               ( ![D:$i]:
% 0.21/0.53                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.21/0.53                   ( ![E:$i]:
% 0.21/0.53                     ( ( ( v1_funct_1 @ E ) & 
% 0.21/0.53                         ( v1_funct_2 @
% 0.21/0.53                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.53                         ( m1_subset_1 @
% 0.21/0.53                           E @ 
% 0.21/0.53                           ( k1_zfmisc_1 @
% 0.21/0.53                             ( k2_zfmisc_1 @
% 0.21/0.53                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.53                       ( ( m1_pre_topc @ C @ D ) =>
% 0.21/0.53                         ( ![F:$i]:
% 0.21/0.53                           ( ( m1_subset_1 @
% 0.21/0.53                               F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ D ) ) ) =>
% 0.21/0.53                             ( ![G:$i]:
% 0.21/0.53                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.21/0.53                                 ( ![H:$i]:
% 0.21/0.53                                   ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) ) =>
% 0.21/0.53                                     ( ( ( r1_tarski @ F @ ( u1_struct_0 @ C ) ) & 
% 0.21/0.53                                         ( m1_connsp_2 @ F @ D @ G ) & 
% 0.21/0.53                                         ( ( G ) = ( H ) ) ) =>
% 0.21/0.53                                       ( ( r1_tmap_1 @ D @ B @ E @ G ) <=>
% 0.21/0.53                                         ( r1_tmap_1 @
% 0.21/0.53                                           C @ B @ 
% 0.21/0.53                                           ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ 
% 0.21/0.53                                           H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.53  thf('74', plain,
% 0.21/0.53      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, 
% 0.21/0.53         X28 : $i]:
% 0.21/0.53         ((v2_struct_0 @ X21)
% 0.21/0.53          | ~ (v2_pre_topc @ X21)
% 0.21/0.53          | ~ (l1_pre_topc @ X21)
% 0.21/0.53          | (v2_struct_0 @ X22)
% 0.21/0.53          | ~ (m1_pre_topc @ X22 @ X23)
% 0.21/0.53          | ~ (m1_pre_topc @ X24 @ X22)
% 0.21/0.53          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.21/0.53          | ~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X24))
% 0.21/0.53          | ~ (r1_tmap_1 @ X24 @ X21 @ 
% 0.21/0.53               (k3_tmap_1 @ X23 @ X21 @ X22 @ X24 @ X27) @ X26)
% 0.21/0.53          | (r1_tmap_1 @ X22 @ X21 @ X27 @ X28)
% 0.21/0.53          | ((X28) != (X26))
% 0.21/0.53          | ~ (m1_connsp_2 @ X25 @ X22 @ X28)
% 0.21/0.53          | ~ (r1_tarski @ X25 @ (u1_struct_0 @ X24))
% 0.21/0.53          | ~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X22))
% 0.21/0.53          | ~ (m1_subset_1 @ X27 @ 
% 0.21/0.53               (k1_zfmisc_1 @ 
% 0.21/0.53                (k2_zfmisc_1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X21))))
% 0.21/0.53          | ~ (v1_funct_2 @ X27 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X21))
% 0.21/0.53          | ~ (v1_funct_1 @ X27)
% 0.21/0.53          | ~ (m1_pre_topc @ X24 @ X23)
% 0.21/0.53          | (v2_struct_0 @ X24)
% 0.21/0.53          | ~ (l1_pre_topc @ X23)
% 0.21/0.53          | ~ (v2_pre_topc @ X23)
% 0.21/0.53          | (v2_struct_0 @ X23))),
% 0.21/0.53      inference('cnf', [status(esa)], [t83_tmap_1])).
% 0.21/0.53  thf('75', plain,
% 0.21/0.53      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.21/0.53         ((v2_struct_0 @ X23)
% 0.21/0.53          | ~ (v2_pre_topc @ X23)
% 0.21/0.53          | ~ (l1_pre_topc @ X23)
% 0.21/0.53          | (v2_struct_0 @ X24)
% 0.21/0.53          | ~ (m1_pre_topc @ X24 @ X23)
% 0.21/0.53          | ~ (v1_funct_1 @ X27)
% 0.21/0.53          | ~ (v1_funct_2 @ X27 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X21))
% 0.21/0.53          | ~ (m1_subset_1 @ X27 @ 
% 0.21/0.53               (k1_zfmisc_1 @ 
% 0.21/0.53                (k2_zfmisc_1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X21))))
% 0.21/0.53          | ~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X22))
% 0.21/0.53          | ~ (r1_tarski @ X25 @ (u1_struct_0 @ X24))
% 0.21/0.53          | ~ (m1_connsp_2 @ X25 @ X22 @ X26)
% 0.21/0.53          | (r1_tmap_1 @ X22 @ X21 @ X27 @ X26)
% 0.21/0.53          | ~ (r1_tmap_1 @ X24 @ X21 @ 
% 0.21/0.53               (k3_tmap_1 @ X23 @ X21 @ X22 @ X24 @ X27) @ X26)
% 0.21/0.53          | ~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X24))
% 0.21/0.53          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.21/0.53          | ~ (m1_pre_topc @ X24 @ X22)
% 0.21/0.53          | ~ (m1_pre_topc @ X22 @ X23)
% 0.21/0.53          | (v2_struct_0 @ X22)
% 0.21/0.53          | ~ (l1_pre_topc @ X21)
% 0.21/0.53          | ~ (v2_pre_topc @ X21)
% 0.21/0.53          | (v2_struct_0 @ X21))),
% 0.21/0.53      inference('simplify', [status(thm)], ['74'])).
% 0.21/0.53  thf('76', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.53         ((v2_struct_0 @ sk_B)
% 0.21/0.53          | ~ (v2_pre_topc @ sk_B)
% 0.21/0.53          | ~ (l1_pre_topc @ sk_B)
% 0.21/0.53          | (v2_struct_0 @ sk_D_1)
% 0.21/0.53          | ~ (m1_pre_topc @ sk_D_1 @ X0)
% 0.21/0.53          | ~ (m1_pre_topc @ X1 @ sk_D_1)
% 0.21/0.53          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.21/0.53          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.21/0.53          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.21/0.53               (k3_tmap_1 @ X0 @ sk_B @ sk_D_1 @ X1 @ sk_E) @ X3)
% 0.21/0.53          | (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ X3)
% 0.21/0.53          | ~ (m1_connsp_2 @ X2 @ sk_D_1 @ X3)
% 0.21/0.53          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X1))
% 0.21/0.53          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_D_1))
% 0.21/0.53          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D_1) @ 
% 0.21/0.53               (u1_struct_0 @ sk_B))
% 0.21/0.53          | ~ (v1_funct_1 @ sk_E)
% 0.21/0.53          | ~ (m1_pre_topc @ X1 @ X0)
% 0.21/0.53          | (v2_struct_0 @ X1)
% 0.21/0.53          | ~ (l1_pre_topc @ X0)
% 0.21/0.53          | ~ (v2_pre_topc @ X0)
% 0.21/0.53          | (v2_struct_0 @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['73', '75'])).
% 0.21/0.53  thf('77', plain, ((v2_pre_topc @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('78', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('79', plain,
% 0.21/0.53      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('80', plain, ((v1_funct_1 @ sk_E)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('81', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.53         ((v2_struct_0 @ sk_B)
% 0.21/0.53          | (v2_struct_0 @ sk_D_1)
% 0.21/0.53          | ~ (m1_pre_topc @ sk_D_1 @ X0)
% 0.21/0.53          | ~ (m1_pre_topc @ X1 @ sk_D_1)
% 0.21/0.53          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.21/0.53          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.21/0.53          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.21/0.53               (k3_tmap_1 @ X0 @ sk_B @ sk_D_1 @ X1 @ sk_E) @ X3)
% 0.21/0.53          | (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ X3)
% 0.21/0.53          | ~ (m1_connsp_2 @ X2 @ sk_D_1 @ X3)
% 0.21/0.53          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X1))
% 0.21/0.53          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_D_1))
% 0.21/0.53          | ~ (m1_pre_topc @ X1 @ X0)
% 0.21/0.53          | (v2_struct_0 @ X1)
% 0.21/0.53          | ~ (l1_pre_topc @ X0)
% 0.21/0.53          | ~ (v2_pre_topc @ X0)
% 0.21/0.53          | (v2_struct_0 @ X0))),
% 0.21/0.53      inference('demod', [status(thm)], ['76', '77', '78', '79', '80'])).
% 0.21/0.53  thf('82', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v2_struct_0 @ sk_A)
% 0.21/0.53          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.53          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.53          | (v2_struct_0 @ sk_C_1)
% 0.21/0.53          | ~ (m1_pre_topc @ sk_C_1 @ sk_A)
% 0.21/0.53          | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D_1))
% 0.21/0.53          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.21/0.53          | ~ (m1_connsp_2 @ X0 @ sk_D_1 @ sk_H)
% 0.21/0.53          | (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H)
% 0.21/0.53          | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_C_1))
% 0.21/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.21/0.53          | ~ (m1_pre_topc @ sk_C_1 @ sk_D_1)
% 0.21/0.53          | ~ (m1_pre_topc @ sk_D_1 @ sk_A)
% 0.21/0.53          | (v2_struct_0 @ sk_D_1)
% 0.21/0.53          | (v2_struct_0 @ sk_B))),
% 0.21/0.53      inference('sup-', [status(thm)], ['72', '81'])).
% 0.21/0.53  thf('83', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('84', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('85', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('86', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D_1))),
% 0.21/0.53      inference('demod', [status(thm)], ['1', '2'])).
% 0.21/0.53  thf('87', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_C_1))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('88', plain, ((m1_pre_topc @ sk_C_1 @ sk_D_1)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('89', plain, ((m1_pre_topc @ sk_D_1 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('90', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v2_struct_0 @ sk_A)
% 0.21/0.53          | (v2_struct_0 @ sk_C_1)
% 0.21/0.53          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.21/0.53          | ~ (m1_connsp_2 @ X0 @ sk_D_1 @ sk_H)
% 0.21/0.53          | (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H)
% 0.21/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.21/0.53          | (v2_struct_0 @ sk_D_1)
% 0.21/0.53          | (v2_struct_0 @ sk_B))),
% 0.21/0.53      inference('demod', [status(thm)],
% 0.21/0.53                ['82', '83', '84', '85', '86', '87', '88', '89'])).
% 0.21/0.53  thf('91', plain,
% 0.21/0.53      (((v2_struct_0 @ sk_B)
% 0.21/0.53        | (v2_struct_0 @ sk_D_1)
% 0.21/0.53        | (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H)
% 0.21/0.53        | ~ (m1_connsp_2 @ (sk_D @ sk_H @ sk_F @ sk_D_1) @ sk_D_1 @ sk_H)
% 0.21/0.53        | ~ (r1_tarski @ (sk_D @ sk_H @ sk_F @ sk_D_1) @ (u1_struct_0 @ sk_C_1))
% 0.21/0.53        | (v2_struct_0 @ sk_C_1)
% 0.21/0.53        | (v2_struct_0 @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['26', '90'])).
% 0.21/0.53  thf('92', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D_1))),
% 0.21/0.53      inference('demod', [status(thm)], ['1', '2'])).
% 0.21/0.53  thf('93', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('94', plain,
% 0.21/0.53      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.21/0.53          | ~ (v3_pre_topc @ X7 @ X8)
% 0.21/0.53          | (m1_connsp_2 @ (sk_D @ X9 @ X7 @ X8) @ X8 @ X9)
% 0.21/0.53          | ~ (r2_hidden @ X9 @ X7)
% 0.21/0.53          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X8))
% 0.21/0.53          | ~ (l1_pre_topc @ X8)
% 0.21/0.53          | ~ (v2_pre_topc @ X8)
% 0.21/0.53          | (v2_struct_0 @ X8))),
% 0.21/0.53      inference('cnf', [status(esa)], [t9_connsp_2])).
% 0.21/0.53  thf('95', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v2_struct_0 @ sk_D_1)
% 0.21/0.53          | ~ (v2_pre_topc @ sk_D_1)
% 0.21/0.53          | ~ (l1_pre_topc @ sk_D_1)
% 0.21/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.21/0.53          | ~ (r2_hidden @ X0 @ sk_F)
% 0.21/0.53          | (m1_connsp_2 @ (sk_D @ X0 @ sk_F @ sk_D_1) @ sk_D_1 @ X0)
% 0.21/0.53          | ~ (v3_pre_topc @ sk_F @ sk_D_1))),
% 0.21/0.53      inference('sup-', [status(thm)], ['93', '94'])).
% 0.21/0.53  thf('96', plain, ((v2_pre_topc @ sk_D_1)),
% 0.21/0.53      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.21/0.53  thf('97', plain, ((l1_pre_topc @ sk_D_1)),
% 0.21/0.53      inference('demod', [status(thm)], ['15', '16'])).
% 0.21/0.53  thf('98', plain, ((v3_pre_topc @ sk_F @ sk_D_1)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('99', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v2_struct_0 @ sk_D_1)
% 0.21/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.21/0.53          | ~ (r2_hidden @ X0 @ sk_F)
% 0.21/0.53          | (m1_connsp_2 @ (sk_D @ X0 @ sk_F @ sk_D_1) @ sk_D_1 @ X0))),
% 0.21/0.53      inference('demod', [status(thm)], ['95', '96', '97', '98'])).
% 0.21/0.53  thf('100', plain,
% 0.21/0.53      (((m1_connsp_2 @ (sk_D @ sk_H @ sk_F @ sk_D_1) @ sk_D_1 @ sk_H)
% 0.21/0.53        | ~ (r2_hidden @ sk_H @ sk_F)
% 0.21/0.53        | (v2_struct_0 @ sk_D_1))),
% 0.21/0.53      inference('sup-', [status(thm)], ['92', '99'])).
% 0.21/0.53  thf('101', plain, ((r2_hidden @ sk_H @ sk_F)),
% 0.21/0.53      inference('demod', [status(thm)], ['21', '22'])).
% 0.21/0.53  thf('102', plain,
% 0.21/0.53      (((m1_connsp_2 @ (sk_D @ sk_H @ sk_F @ sk_D_1) @ sk_D_1 @ sk_H)
% 0.21/0.53        | (v2_struct_0 @ sk_D_1))),
% 0.21/0.53      inference('demod', [status(thm)], ['100', '101'])).
% 0.21/0.53  thf('103', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('104', plain,
% 0.21/0.53      ((m1_connsp_2 @ (sk_D @ sk_H @ sk_F @ sk_D_1) @ sk_D_1 @ sk_H)),
% 0.21/0.53      inference('clc', [status(thm)], ['102', '103'])).
% 0.21/0.53  thf('105', plain, ((r1_tarski @ sk_F @ (u1_struct_0 @ sk_C_1))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('106', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D_1))),
% 0.21/0.53      inference('demod', [status(thm)], ['1', '2'])).
% 0.21/0.53  thf('107', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('108', plain,
% 0.21/0.53      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.21/0.53          | ~ (v3_pre_topc @ X7 @ X8)
% 0.21/0.53          | (r1_tarski @ (sk_D @ X9 @ X7 @ X8) @ X7)
% 0.21/0.53          | ~ (r2_hidden @ X9 @ X7)
% 0.21/0.53          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X8))
% 0.21/0.53          | ~ (l1_pre_topc @ X8)
% 0.21/0.53          | ~ (v2_pre_topc @ X8)
% 0.21/0.53          | (v2_struct_0 @ X8))),
% 0.21/0.53      inference('cnf', [status(esa)], [t9_connsp_2])).
% 0.21/0.53  thf('109', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v2_struct_0 @ sk_D_1)
% 0.21/0.53          | ~ (v2_pre_topc @ sk_D_1)
% 0.21/0.53          | ~ (l1_pre_topc @ sk_D_1)
% 0.21/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.21/0.53          | ~ (r2_hidden @ X0 @ sk_F)
% 0.21/0.53          | (r1_tarski @ (sk_D @ X0 @ sk_F @ sk_D_1) @ sk_F)
% 0.21/0.53          | ~ (v3_pre_topc @ sk_F @ sk_D_1))),
% 0.21/0.53      inference('sup-', [status(thm)], ['107', '108'])).
% 0.21/0.53  thf('110', plain, ((v2_pre_topc @ sk_D_1)),
% 0.21/0.53      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.21/0.53  thf('111', plain, ((l1_pre_topc @ sk_D_1)),
% 0.21/0.53      inference('demod', [status(thm)], ['15', '16'])).
% 0.21/0.53  thf('112', plain, ((v3_pre_topc @ sk_F @ sk_D_1)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('113', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v2_struct_0 @ sk_D_1)
% 0.21/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.21/0.53          | ~ (r2_hidden @ X0 @ sk_F)
% 0.21/0.53          | (r1_tarski @ (sk_D @ X0 @ sk_F @ sk_D_1) @ sk_F))),
% 0.21/0.53      inference('demod', [status(thm)], ['109', '110', '111', '112'])).
% 0.21/0.53  thf('114', plain,
% 0.21/0.53      (((r1_tarski @ (sk_D @ sk_H @ sk_F @ sk_D_1) @ sk_F)
% 0.21/0.53        | ~ (r2_hidden @ sk_H @ sk_F)
% 0.21/0.53        | (v2_struct_0 @ sk_D_1))),
% 0.21/0.53      inference('sup-', [status(thm)], ['106', '113'])).
% 0.21/0.53  thf('115', plain, ((r2_hidden @ sk_H @ sk_F)),
% 0.21/0.53      inference('demod', [status(thm)], ['21', '22'])).
% 0.21/0.53  thf('116', plain,
% 0.21/0.53      (((r1_tarski @ (sk_D @ sk_H @ sk_F @ sk_D_1) @ sk_F)
% 0.21/0.53        | (v2_struct_0 @ sk_D_1))),
% 0.21/0.53      inference('demod', [status(thm)], ['114', '115'])).
% 0.21/0.53  thf('117', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('118', plain, ((r1_tarski @ (sk_D @ sk_H @ sk_F @ sk_D_1) @ sk_F)),
% 0.21/0.53      inference('clc', [status(thm)], ['116', '117'])).
% 0.21/0.53  thf(t1_xboole_1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.21/0.53       ( r1_tarski @ A @ C ) ))).
% 0.21/0.53  thf('119', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         (~ (r1_tarski @ X0 @ X1)
% 0.21/0.53          | ~ (r1_tarski @ X1 @ X2)
% 0.21/0.53          | (r1_tarski @ X0 @ X2))),
% 0.21/0.53      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.21/0.53  thf('120', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((r1_tarski @ (sk_D @ sk_H @ sk_F @ sk_D_1) @ X0)
% 0.21/0.53          | ~ (r1_tarski @ sk_F @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['118', '119'])).
% 0.21/0.53  thf('121', plain,
% 0.21/0.53      ((r1_tarski @ (sk_D @ sk_H @ sk_F @ sk_D_1) @ (u1_struct_0 @ sk_C_1))),
% 0.21/0.53      inference('sup-', [status(thm)], ['105', '120'])).
% 0.21/0.53  thf('122', plain,
% 0.21/0.53      (((v2_struct_0 @ sk_B)
% 0.21/0.53        | (v2_struct_0 @ sk_D_1)
% 0.21/0.53        | (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H)
% 0.21/0.53        | (v2_struct_0 @ sk_C_1)
% 0.21/0.53        | (v2_struct_0 @ sk_A))),
% 0.21/0.53      inference('demod', [status(thm)], ['91', '104', '121'])).
% 0.21/0.53  thf('123', plain,
% 0.21/0.53      ((~ (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G))
% 0.21/0.53         <= (~ ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G)))),
% 0.21/0.53      inference('split', [status(esa)], ['59'])).
% 0.21/0.53  thf('124', plain, (((sk_G) = (sk_H))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('125', plain,
% 0.21/0.53      ((~ (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H))
% 0.21/0.53         <= (~ ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G)))),
% 0.21/0.53      inference('demod', [status(thm)], ['123', '124'])).
% 0.21/0.53  thf('126', plain,
% 0.21/0.53      (((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G))
% 0.21/0.53         <= (((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G)))),
% 0.21/0.53      inference('split', [status(esa)], ['27'])).
% 0.21/0.53  thf('127', plain, (((sk_G) = (sk_H))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('128', plain,
% 0.21/0.53      (((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H))
% 0.21/0.53         <= (((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G)))),
% 0.21/0.53      inference('demod', [status(thm)], ['126', '127'])).
% 0.21/0.53  thf('129', plain,
% 0.21/0.53      ((~ (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H))
% 0.21/0.53         <= (~ ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H)))),
% 0.21/0.53      inference('split', [status(esa)], ['31'])).
% 0.21/0.53  thf('130', plain,
% 0.21/0.53      (~ ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G)) | 
% 0.21/0.53       ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H))),
% 0.21/0.53      inference('sup-', [status(thm)], ['128', '129'])).
% 0.21/0.53  thf('131', plain, (~ ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G))),
% 0.21/0.53      inference('sat_resolution*', [status(thm)], ['32', '69', '130'])).
% 0.21/0.53  thf('132', plain, (~ (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H)),
% 0.21/0.53      inference('simpl_trail', [status(thm)], ['125', '131'])).
% 0.21/0.53  thf('133', plain,
% 0.21/0.53      (((v2_struct_0 @ sk_A)
% 0.21/0.53        | (v2_struct_0 @ sk_C_1)
% 0.21/0.53        | (v2_struct_0 @ sk_D_1)
% 0.21/0.53        | (v2_struct_0 @ sk_B))),
% 0.21/0.53      inference('sup-', [status(thm)], ['122', '132'])).
% 0.21/0.53  thf('134', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('135', plain,
% 0.21/0.53      (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C_1) | (v2_struct_0 @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['133', '134'])).
% 0.21/0.53  thf('136', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('137', plain, (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C_1))),
% 0.21/0.53      inference('clc', [status(thm)], ['135', '136'])).
% 0.21/0.53  thf('138', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('139', plain, ((v2_struct_0 @ sk_C_1)),
% 0.21/0.53      inference('clc', [status(thm)], ['137', '138'])).
% 0.21/0.53  thf('140', plain, ($false), inference('demod', [status(thm)], ['0', '139'])).
% 0.21/0.53  
% 0.21/0.53  % SZS output end Refutation
% 0.21/0.53  
% 0.21/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
