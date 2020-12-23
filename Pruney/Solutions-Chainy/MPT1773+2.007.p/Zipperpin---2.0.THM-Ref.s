%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BfjRRsZOaA

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:15 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 617 expanded)
%              Number of leaves         :   31 ( 187 expanded)
%              Depth                    :   32
%              Number of atoms          : 2011 (25781 expanded)
%              Number of equality atoms :   19 ( 330 expanded)
%              Maximal formula depth    :   32 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

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
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_H )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G )
   <= ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H )
   <= ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_H )
    | ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_H )
    | ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G ) ),
    inference(split,[status(esa)],['7'])).

thf('9',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_H )
   <= ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_H ) ),
    inference(split,[status(esa)],['3'])).

thf('11',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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

thf('12',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( v2_struct_0 @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ~ ( l1_pre_topc @ X14 )
      | ( v2_struct_0 @ X15 )
      | ~ ( m1_pre_topc @ X15 @ X16 )
      | ~ ( m1_pre_topc @ X17 @ X15 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X17 ) )
      | ~ ( r1_tmap_1 @ X17 @ X14 @ ( k3_tmap_1 @ X16 @ X14 @ X15 @ X17 @ X20 ) @ X19 )
      | ( r1_tmap_1 @ X15 @ X14 @ X20 @ X21 )
      | ( X21 != X19 )
      | ~ ( m1_connsp_2 @ X18 @ X15 @ X21 )
      | ~ ( r1_tarski @ X18 @ ( u1_struct_0 @ X17 ) )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X15 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X14 ) ) ) )
      | ~ ( v1_funct_2 @ X20 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X14 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( m1_pre_topc @ X17 @ X16 )
      | ( v2_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t83_tmap_1])).

thf('13',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( v2_struct_0 @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ~ ( l1_pre_topc @ X16 )
      | ( v2_struct_0 @ X17 )
      | ~ ( m1_pre_topc @ X17 @ X16 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_funct_2 @ X20 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X14 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X14 ) ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X15 ) )
      | ~ ( r1_tarski @ X18 @ ( u1_struct_0 @ X17 ) )
      | ~ ( m1_connsp_2 @ X18 @ X15 @ X19 )
      | ( r1_tmap_1 @ X15 @ X14 @ X20 @ X19 )
      | ~ ( r1_tmap_1 @ X17 @ X14 @ ( k3_tmap_1 @ X16 @ X14 @ X15 @ X17 @ X20 ) @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X17 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( m1_pre_topc @ X17 @ X15 )
      | ~ ( m1_pre_topc @ X15 @ X16 )
      | ( v2_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_tmap_1 @ X1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E ) @ X3 )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X3 )
      | ~ ( m1_connsp_2 @ X2 @ sk_D @ X3 )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_tmap_1 @ X1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E ) @ X3 )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X3 )
      | ~ ( m1_connsp_2 @ X2 @ sk_D @ X3 )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['14','15','16','17','18'])).

thf('20',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( v2_pre_topc @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ~ ( m1_pre_topc @ sk_C @ sk_A )
        | ~ ( m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_D ) )
        | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_C ) )
        | ~ ( m1_connsp_2 @ X0 @ sk_D @ sk_H )
        | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H )
        | ~ ( m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_C ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
        | ~ ( m1_pre_topc @ sk_C @ sk_D )
        | ~ ( m1_pre_topc @ sk_D @ sk_A )
        | ( v2_struct_0 @ sk_D )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_H ) ),
    inference('sup-',[status(thm)],['10','19'])).

thf('21',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_C ) )
        | ~ ( m1_connsp_2 @ X0 @ sk_D @ sk_H )
        | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
        | ( v2_struct_0 @ sk_D )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_H ) ),
    inference(demod,[status(thm)],['20','21','22','23','26','27','28','29'])).

thf('31',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H )
      | ~ ( m1_connsp_2 @ sk_F @ sk_D @ sk_H )
      | ~ ( r1_tarski @ sk_F @ ( u1_struct_0 @ sk_C ) )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_H ) ),
    inference('sup-',[status(thm)],['9','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('33',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( m1_connsp_2 @ C @ A @ B )
              <=> ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('34',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X9 ) )
      | ~ ( r2_hidden @ X8 @ ( k1_tops_1 @ X9 @ X10 ) )
      | ( m1_connsp_2 @ X10 @ X9 @ X8 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ~ ( l1_pre_topc @ sk_D )
      | ( m1_connsp_2 @ sk_F @ sk_D @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_D @ sk_F ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('38',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('43',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_pre_topc @ X2 @ X3 )
      | ( l1_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('44',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t55_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                 => ( ( ( v3_pre_topc @ D @ B )
                     => ( ( k1_tops_1 @ B @ D )
                        = D ) )
                    & ( ( ( k1_tops_1 @ A @ C )
                        = C )
                     => ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) )).

thf('48',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( l1_pre_topc @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( v3_pre_topc @ X5 @ X4 )
      | ( ( k1_tops_1 @ X4 @ X5 )
        = X5 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('49',plain,
    ( ! [X4: $i,X5: $i] :
        ( ~ ( l1_pre_topc @ X4 )
        | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
        | ~ ( v3_pre_topc @ X5 @ X4 )
        | ( ( k1_tops_1 @ X4 @ X5 )
          = X5 ) )
   <= ! [X4: $i,X5: $i] :
        ( ~ ( l1_pre_topc @ X4 )
        | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
        | ~ ( v3_pre_topc @ X5 @ X4 )
        | ( ( k1_tops_1 @ X4 @ X5 )
          = X5 ) ) ),
    inference(split,[status(esa)],['48'])).

thf('50',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ! [X6: $i,X7: $i] :
        ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
        | ~ ( l1_pre_topc @ X7 )
        | ~ ( v2_pre_topc @ X7 ) )
   <= ! [X6: $i,X7: $i] :
        ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
        | ~ ( l1_pre_topc @ X7 )
        | ~ ( v2_pre_topc @ X7 ) ) ),
    inference(split,[status(esa)],['48'])).

thf('52',plain,
    ( ( ~ ( v2_pre_topc @ sk_D )
      | ~ ( l1_pre_topc @ sk_D ) )
   <= ! [X6: $i,X7: $i] :
        ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
        | ~ ( l1_pre_topc @ X7 )
        | ~ ( v2_pre_topc @ X7 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('54',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['44','45'])).

thf('55',plain,(
    ~ ! [X6: $i,X7: $i] :
        ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
        | ~ ( l1_pre_topc @ X7 )
        | ~ ( v2_pre_topc @ X7 ) ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,
    ( ! [X4: $i,X5: $i] :
        ( ~ ( l1_pre_topc @ X4 )
        | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
        | ~ ( v3_pre_topc @ X5 @ X4 )
        | ( ( k1_tops_1 @ X4 @ X5 )
          = X5 ) )
    | ! [X6: $i,X7: $i] :
        ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
        | ~ ( l1_pre_topc @ X7 )
        | ~ ( v2_pre_topc @ X7 ) ) ),
    inference(split,[status(esa)],['48'])).

thf('57',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( l1_pre_topc @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( v3_pre_topc @ X5 @ X4 )
      | ( ( k1_tops_1 @ X4 @ X5 )
        = X5 ) ) ),
    inference('sat_resolution*',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( l1_pre_topc @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( v3_pre_topc @ X5 @ X4 )
      | ( ( k1_tops_1 @ X4 @ X5 )
        = X5 ) ) ),
    inference(simpl_trail,[status(thm)],['49','57'])).

thf('59',plain,
    ( ( ( k1_tops_1 @ sk_D @ sk_F )
      = sk_F )
    | ~ ( v3_pre_topc @ sk_F @ sk_D )
    | ~ ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['47','58'])).

thf('60',plain,(
    v3_pre_topc @ sk_F @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['44','45'])).

thf('62',plain,
    ( ( k1_tops_1 @ sk_D @ sk_F )
    = sk_F ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( m1_connsp_2 @ sk_F @ sk_D @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_F )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['35','41','46','62'])).

thf('64',plain,
    ( ~ ( r2_hidden @ sk_H @ sk_F )
    | ( m1_connsp_2 @ sk_F @ sk_D @ sk_H )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['32','63'])).

thf('65',plain,(
    r2_hidden @ sk_G @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    r2_hidden @ sk_H @ sk_F ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,
    ( ( m1_connsp_2 @ sk_F @ sk_D @ sk_H )
    | ( v2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['64','67'])).

thf('69',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    m1_connsp_2 @ sk_F @ sk_D @ sk_H ),
    inference(clc,[status(thm)],['68','69'])).

thf('71',plain,(
    r1_tarski @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_H ) ),
    inference(demod,[status(thm)],['31','70','71'])).

thf('73',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G )
   <= ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G ) ),
    inference(split,[status(esa)],['7'])).

thf('74',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H )
   <= ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G )
      & ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_H ) ) ),
    inference('sup-',[status(thm)],['72','75'])).

thf('77',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G )
      & ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_H ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G )
      & ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_H ) ) ),
    inference(clc,[status(thm)],['78','79'])).

thf('81',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( v2_struct_0 @ sk_C )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G )
      & ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_H ) ) ),
    inference(clc,[status(thm)],['80','81'])).

thf('83',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G )
    | ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_H ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G )
    | ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_H ) ),
    inference(split,[status(esa)],['3'])).

thf('86',plain,(
    r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G ),
    inference('sat_resolution*',[status(thm)],['8','84','85'])).

thf('87',plain,(
    r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H ),
    inference(simpl_trail,[status(thm)],['6','86'])).

thf('88',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( v2_struct_0 @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ~ ( l1_pre_topc @ X14 )
      | ( v2_struct_0 @ X15 )
      | ~ ( m1_pre_topc @ X15 @ X16 )
      | ~ ( m1_pre_topc @ X17 @ X15 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X17 ) )
      | ~ ( r1_tmap_1 @ X15 @ X14 @ X20 @ X21 )
      | ( r1_tmap_1 @ X17 @ X14 @ ( k3_tmap_1 @ X16 @ X14 @ X15 @ X17 @ X20 ) @ X19 )
      | ( X21 != X19 )
      | ~ ( m1_connsp_2 @ X18 @ X15 @ X21 )
      | ~ ( r1_tarski @ X18 @ ( u1_struct_0 @ X17 ) )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X15 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X14 ) ) ) )
      | ~ ( v1_funct_2 @ X20 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X14 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( m1_pre_topc @ X17 @ X16 )
      | ( v2_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t83_tmap_1])).

thf('91',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( v2_struct_0 @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ~ ( l1_pre_topc @ X16 )
      | ( v2_struct_0 @ X17 )
      | ~ ( m1_pre_topc @ X17 @ X16 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_funct_2 @ X20 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X14 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X14 ) ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X15 ) )
      | ~ ( r1_tarski @ X18 @ ( u1_struct_0 @ X17 ) )
      | ~ ( m1_connsp_2 @ X18 @ X15 @ X19 )
      | ( r1_tmap_1 @ X17 @ X14 @ ( k3_tmap_1 @ X16 @ X14 @ X15 @ X17 @ X20 ) @ X19 )
      | ~ ( r1_tmap_1 @ X15 @ X14 @ X20 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X17 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( m1_pre_topc @ X17 @ X15 )
      | ~ ( m1_pre_topc @ X15 @ X16 )
      | ( v2_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X3 )
      | ( r1_tmap_1 @ X1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E ) @ X3 )
      | ~ ( m1_connsp_2 @ X2 @ sk_D @ X3 )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['89','91'])).

thf('93',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X3 )
      | ( r1_tmap_1 @ X1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E ) @ X3 )
      | ~ ( m1_connsp_2 @ X2 @ sk_D @ X3 )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['92','93','94','95','96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( r1_tarski @ sk_F @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_connsp_2 @ sk_F @ sk_D @ X2 )
      | ( r1_tmap_1 @ X1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E ) @ X2 )
      | ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['88','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_subset_1 @ sk_H @ ( u1_struct_0 @ X1 ) )
      | ( r1_tmap_1 @ X1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E ) @ sk_H )
      | ~ ( m1_connsp_2 @ sk_F @ sk_D @ sk_H )
      | ~ ( r1_tarski @ sk_F @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_D ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['87','98'])).

thf('100',plain,(
    m1_connsp_2 @ sk_F @ sk_D @ sk_H ),
    inference(clc,[status(thm)],['68','69'])).

thf('101',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_subset_1 @ sk_H @ ( u1_struct_0 @ X1 ) )
      | ( r1_tmap_1 @ X1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E ) @ sk_H )
      | ~ ( r1_tarski @ sk_F @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['99','100','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ~ ( r1_tarski @ sk_F @ ( u1_struct_0 @ sk_C ) )
      | ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_H )
      | ~ ( m1_pre_topc @ sk_C @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','102'])).

thf('104',plain,(
    r1_tarski @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_H )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['103','104','105'])).

thf('107',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ~ ( m1_pre_topc @ sk_D @ sk_A )
    | ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_H )
    | ( v2_struct_0 @ sk_C )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','106'])).

thf('108',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_H )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['107','108','109','110'])).

thf('112',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_H )
   <= ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_H ) ),
    inference(split,[status(esa)],['7'])).

thf('113',plain,(
    ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_H ) ),
    inference('sat_resolution*',[status(thm)],['8','84'])).

thf('114',plain,(
    ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_H ) ),
    inference(simpl_trail,[status(thm)],['112','113'])).

thf('115',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['111','114'])).

thf('116',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['117','118'])).

thf('120',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    v2_struct_0 @ sk_C ),
    inference(clc,[status(thm)],['119','120'])).

thf('122',plain,(
    $false ),
    inference(demod,[status(thm)],['0','121'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BfjRRsZOaA
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:00:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 76 iterations in 0.027s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.20/0.49  thf(sk_G_type, type, sk_G: $i).
% 0.20/0.49  thf(sk_H_type, type, sk_H: $i).
% 0.20/0.49  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.20/0.49  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.20/0.49  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.49  thf(sk_E_type, type, sk_E: $i).
% 0.20/0.49  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.49  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.20/0.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.49  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.20/0.49  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.49  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.49  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.20/0.49  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.49  thf(sk_F_type, type, sk_F: $i).
% 0.20/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.49  thf(t84_tmap_1, conjecture,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.49             ( l1_pre_topc @ B ) ) =>
% 0.20/0.49           ( ![C:$i]:
% 0.20/0.49             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.49               ( ![D:$i]:
% 0.20/0.49                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.20/0.49                   ( ![E:$i]:
% 0.20/0.49                     ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.49                         ( v1_funct_2 @
% 0.20/0.49                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.49                         ( m1_subset_1 @
% 0.20/0.49                           E @ 
% 0.20/0.49                           ( k1_zfmisc_1 @
% 0.20/0.49                             ( k2_zfmisc_1 @
% 0.20/0.49                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.49                       ( ( m1_pre_topc @ C @ D ) =>
% 0.20/0.49                         ( ![F:$i]:
% 0.20/0.49                           ( ( m1_subset_1 @
% 0.20/0.49                               F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ D ) ) ) =>
% 0.20/0.49                             ( ![G:$i]:
% 0.20/0.49                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.20/0.49                                 ( ![H:$i]:
% 0.20/0.49                                   ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) ) =>
% 0.20/0.49                                     ( ( ( v3_pre_topc @ F @ D ) & 
% 0.20/0.49                                         ( r2_hidden @ G @ F ) & 
% 0.20/0.49                                         ( r1_tarski @ F @ ( u1_struct_0 @ C ) ) & 
% 0.20/0.49                                         ( ( G ) = ( H ) ) ) =>
% 0.20/0.49                                       ( ( r1_tmap_1 @ D @ B @ E @ G ) <=>
% 0.20/0.50                                         ( r1_tmap_1 @
% 0.20/0.50                                           C @ B @ 
% 0.20/0.50                                           ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ 
% 0.20/0.50                                           H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i]:
% 0.20/0.50        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.50            ( l1_pre_topc @ A ) ) =>
% 0.20/0.50          ( ![B:$i]:
% 0.20/0.50            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.50                ( l1_pre_topc @ B ) ) =>
% 0.20/0.50              ( ![C:$i]:
% 0.20/0.50                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.50                  ( ![D:$i]:
% 0.20/0.50                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.20/0.50                      ( ![E:$i]:
% 0.20/0.50                        ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.50                            ( v1_funct_2 @
% 0.20/0.50                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.50                            ( m1_subset_1 @
% 0.20/0.50                              E @ 
% 0.20/0.50                              ( k1_zfmisc_1 @
% 0.20/0.50                                ( k2_zfmisc_1 @
% 0.20/0.50                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.50                          ( ( m1_pre_topc @ C @ D ) =>
% 0.20/0.50                            ( ![F:$i]:
% 0.20/0.50                              ( ( m1_subset_1 @
% 0.20/0.50                                  F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ D ) ) ) =>
% 0.20/0.50                                ( ![G:$i]:
% 0.20/0.50                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.20/0.50                                    ( ![H:$i]:
% 0.20/0.50                                      ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) ) =>
% 0.20/0.50                                        ( ( ( v3_pre_topc @ F @ D ) & 
% 0.20/0.50                                            ( r2_hidden @ G @ F ) & 
% 0.20/0.50                                            ( r1_tarski @
% 0.20/0.50                                              F @ ( u1_struct_0 @ C ) ) & 
% 0.20/0.50                                            ( ( G ) = ( H ) ) ) =>
% 0.20/0.50                                          ( ( r1_tmap_1 @ D @ B @ E @ G ) <=>
% 0.20/0.50                                            ( r1_tmap_1 @
% 0.20/0.50                                              C @ B @ 
% 0.20/0.50                                              ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ 
% 0.20/0.50                                              H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t84_tmap_1])).
% 0.20/0.50  thf('0', plain, (~ (v2_struct_0 @ sk_C)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('1', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('2', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_C))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('3', plain,
% 0.20/0.50      (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.50         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_H)
% 0.20/0.50        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('4', plain,
% 0.20/0.50      (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G))
% 0.20/0.50         <= (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G)))),
% 0.20/0.50      inference('split', [status(esa)], ['3'])).
% 0.20/0.50  thf('5', plain, (((sk_G) = (sk_H))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('6', plain,
% 0.20/0.50      (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H))
% 0.20/0.50         <= (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G)))),
% 0.20/0.50      inference('demod', [status(thm)], ['4', '5'])).
% 0.20/0.50  thf('7', plain,
% 0.20/0.50      ((~ (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.50           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_H)
% 0.20/0.50        | ~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('8', plain,
% 0.20/0.50      (~
% 0.20/0.50       ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.50         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_H)) | 
% 0.20/0.50       ~ ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G))),
% 0.20/0.50      inference('split', [status(esa)], ['7'])).
% 0.20/0.50  thf('9', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('10', plain,
% 0.20/0.50      (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.50         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_H))
% 0.20/0.50         <= (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.50               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_H)))),
% 0.20/0.50      inference('split', [status(esa)], ['3'])).
% 0.20/0.50  thf('11', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_E @ 
% 0.20/0.50        (k1_zfmisc_1 @ 
% 0.20/0.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t83_tmap_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.50             ( l1_pre_topc @ B ) ) =>
% 0.20/0.50           ( ![C:$i]:
% 0.20/0.50             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.50               ( ![D:$i]:
% 0.20/0.50                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.20/0.50                   ( ![E:$i]:
% 0.20/0.50                     ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.50                         ( v1_funct_2 @
% 0.20/0.50                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.50                         ( m1_subset_1 @
% 0.20/0.50                           E @ 
% 0.20/0.50                           ( k1_zfmisc_1 @
% 0.20/0.50                             ( k2_zfmisc_1 @
% 0.20/0.50                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.50                       ( ( m1_pre_topc @ C @ D ) =>
% 0.20/0.50                         ( ![F:$i]:
% 0.20/0.50                           ( ( m1_subset_1 @
% 0.20/0.50                               F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ D ) ) ) =>
% 0.20/0.50                             ( ![G:$i]:
% 0.20/0.50                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.20/0.50                                 ( ![H:$i]:
% 0.20/0.50                                   ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) ) =>
% 0.20/0.50                                     ( ( ( r1_tarski @ F @ ( u1_struct_0 @ C ) ) & 
% 0.20/0.50                                         ( m1_connsp_2 @ F @ D @ G ) & 
% 0.20/0.50                                         ( ( G ) = ( H ) ) ) =>
% 0.20/0.50                                       ( ( r1_tmap_1 @ D @ B @ E @ G ) <=>
% 0.20/0.50                                         ( r1_tmap_1 @
% 0.20/0.50                                           C @ B @ 
% 0.20/0.50                                           ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ 
% 0.20/0.50                                           H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.50  thf('12', plain,
% 0.20/0.50      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, 
% 0.20/0.50         X21 : $i]:
% 0.20/0.50         ((v2_struct_0 @ X14)
% 0.20/0.50          | ~ (v2_pre_topc @ X14)
% 0.20/0.50          | ~ (l1_pre_topc @ X14)
% 0.20/0.50          | (v2_struct_0 @ X15)
% 0.20/0.50          | ~ (m1_pre_topc @ X15 @ X16)
% 0.20/0.50          | ~ (m1_pre_topc @ X17 @ X15)
% 0.20/0.50          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.20/0.50          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X17))
% 0.20/0.50          | ~ (r1_tmap_1 @ X17 @ X14 @ 
% 0.20/0.50               (k3_tmap_1 @ X16 @ X14 @ X15 @ X17 @ X20) @ X19)
% 0.20/0.50          | (r1_tmap_1 @ X15 @ X14 @ X20 @ X21)
% 0.20/0.50          | ((X21) != (X19))
% 0.20/0.50          | ~ (m1_connsp_2 @ X18 @ X15 @ X21)
% 0.20/0.50          | ~ (r1_tarski @ X18 @ (u1_struct_0 @ X17))
% 0.20/0.50          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X15))
% 0.20/0.50          | ~ (m1_subset_1 @ X20 @ 
% 0.20/0.50               (k1_zfmisc_1 @ 
% 0.20/0.50                (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X14))))
% 0.20/0.50          | ~ (v1_funct_2 @ X20 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X14))
% 0.20/0.50          | ~ (v1_funct_1 @ X20)
% 0.20/0.50          | ~ (m1_pre_topc @ X17 @ X16)
% 0.20/0.50          | (v2_struct_0 @ X17)
% 0.20/0.50          | ~ (l1_pre_topc @ X16)
% 0.20/0.50          | ~ (v2_pre_topc @ X16)
% 0.20/0.50          | (v2_struct_0 @ X16))),
% 0.20/0.50      inference('cnf', [status(esa)], [t83_tmap_1])).
% 0.20/0.50  thf('13', plain,
% 0.20/0.50      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.20/0.50         ((v2_struct_0 @ X16)
% 0.20/0.50          | ~ (v2_pre_topc @ X16)
% 0.20/0.50          | ~ (l1_pre_topc @ X16)
% 0.20/0.50          | (v2_struct_0 @ X17)
% 0.20/0.50          | ~ (m1_pre_topc @ X17 @ X16)
% 0.20/0.50          | ~ (v1_funct_1 @ X20)
% 0.20/0.50          | ~ (v1_funct_2 @ X20 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X14))
% 0.20/0.50          | ~ (m1_subset_1 @ X20 @ 
% 0.20/0.50               (k1_zfmisc_1 @ 
% 0.20/0.50                (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X14))))
% 0.20/0.50          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X15))
% 0.20/0.50          | ~ (r1_tarski @ X18 @ (u1_struct_0 @ X17))
% 0.20/0.50          | ~ (m1_connsp_2 @ X18 @ X15 @ X19)
% 0.20/0.50          | (r1_tmap_1 @ X15 @ X14 @ X20 @ X19)
% 0.20/0.50          | ~ (r1_tmap_1 @ X17 @ X14 @ 
% 0.20/0.50               (k3_tmap_1 @ X16 @ X14 @ X15 @ X17 @ X20) @ X19)
% 0.20/0.50          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X17))
% 0.20/0.50          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.20/0.50          | ~ (m1_pre_topc @ X17 @ X15)
% 0.20/0.50          | ~ (m1_pre_topc @ X15 @ X16)
% 0.20/0.50          | (v2_struct_0 @ X15)
% 0.20/0.50          | ~ (l1_pre_topc @ X14)
% 0.20/0.50          | ~ (v2_pre_topc @ X14)
% 0.20/0.50          | (v2_struct_0 @ X14))),
% 0.20/0.50      inference('simplify', [status(thm)], ['12'])).
% 0.20/0.50  thf('14', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.50         ((v2_struct_0 @ sk_B)
% 0.20/0.50          | ~ (v2_pre_topc @ sk_B)
% 0.20/0.50          | ~ (l1_pre_topc @ sk_B)
% 0.20/0.50          | (v2_struct_0 @ sk_D)
% 0.20/0.50          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.20/0.50          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.20/0.50          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.20/0.50          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.20/0.50          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.20/0.50               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X3)
% 0.20/0.50          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X3)
% 0.20/0.50          | ~ (m1_connsp_2 @ X2 @ sk_D @ X3)
% 0.20/0.50          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X1))
% 0.20/0.50          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_D))
% 0.20/0.50          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.20/0.50          | ~ (v1_funct_1 @ sk_E)
% 0.20/0.50          | ~ (m1_pre_topc @ X1 @ X0)
% 0.20/0.50          | (v2_struct_0 @ X1)
% 0.20/0.50          | ~ (l1_pre_topc @ X0)
% 0.20/0.50          | ~ (v2_pre_topc @ X0)
% 0.20/0.50          | (v2_struct_0 @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['11', '13'])).
% 0.20/0.50  thf('15', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('16', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('17', plain,
% 0.20/0.50      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('18', plain, ((v1_funct_1 @ sk_E)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('19', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.50         ((v2_struct_0 @ sk_B)
% 0.20/0.50          | (v2_struct_0 @ sk_D)
% 0.20/0.50          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.20/0.50          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.20/0.50          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.20/0.50          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.20/0.50          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.20/0.50               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X3)
% 0.20/0.50          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X3)
% 0.20/0.50          | ~ (m1_connsp_2 @ X2 @ sk_D @ X3)
% 0.20/0.50          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X1))
% 0.20/0.50          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_D))
% 0.20/0.50          | ~ (m1_pre_topc @ X1 @ X0)
% 0.20/0.50          | (v2_struct_0 @ X1)
% 0.20/0.50          | ~ (l1_pre_topc @ X0)
% 0.20/0.50          | ~ (v2_pre_topc @ X0)
% 0.20/0.50          | (v2_struct_0 @ X0))),
% 0.20/0.50      inference('demod', [status(thm)], ['14', '15', '16', '17', '18'])).
% 0.20/0.50  thf('20', plain,
% 0.20/0.50      ((![X0 : $i]:
% 0.20/0.50          ((v2_struct_0 @ sk_A)
% 0.20/0.50           | ~ (v2_pre_topc @ sk_A)
% 0.20/0.50           | ~ (l1_pre_topc @ sk_A)
% 0.20/0.50           | (v2_struct_0 @ sk_C)
% 0.20/0.50           | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.20/0.50           | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D))
% 0.20/0.50           | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C))
% 0.20/0.50           | ~ (m1_connsp_2 @ X0 @ sk_D @ sk_H)
% 0.20/0.50           | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H)
% 0.20/0.50           | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_C))
% 0.20/0.50           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.20/0.50           | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.20/0.50           | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.20/0.50           | (v2_struct_0 @ sk_D)
% 0.20/0.50           | (v2_struct_0 @ sk_B)))
% 0.20/0.50         <= (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.50               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_H)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['10', '19'])).
% 0.20/0.50  thf('21', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('23', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('24', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_D))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('25', plain, (((sk_G) = (sk_H))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('26', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D))),
% 0.20/0.50      inference('demod', [status(thm)], ['24', '25'])).
% 0.20/0.50  thf('27', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_C))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('28', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('29', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('30', plain,
% 0.20/0.50      ((![X0 : $i]:
% 0.20/0.50          ((v2_struct_0 @ sk_A)
% 0.20/0.50           | (v2_struct_0 @ sk_C)
% 0.20/0.50           | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C))
% 0.20/0.50           | ~ (m1_connsp_2 @ X0 @ sk_D @ sk_H)
% 0.20/0.50           | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H)
% 0.20/0.50           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.20/0.50           | (v2_struct_0 @ sk_D)
% 0.20/0.50           | (v2_struct_0 @ sk_B)))
% 0.20/0.50         <= (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.50               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_H)))),
% 0.20/0.50      inference('demod', [status(thm)],
% 0.20/0.50                ['20', '21', '22', '23', '26', '27', '28', '29'])).
% 0.20/0.50  thf('31', plain,
% 0.20/0.50      ((((v2_struct_0 @ sk_B)
% 0.20/0.50         | (v2_struct_0 @ sk_D)
% 0.20/0.50         | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H)
% 0.20/0.50         | ~ (m1_connsp_2 @ sk_F @ sk_D @ sk_H)
% 0.20/0.50         | ~ (r1_tarski @ sk_F @ (u1_struct_0 @ sk_C))
% 0.20/0.50         | (v2_struct_0 @ sk_C)
% 0.20/0.50         | (v2_struct_0 @ sk_A)))
% 0.20/0.50         <= (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.50               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_H)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['9', '30'])).
% 0.20/0.50  thf('32', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D))),
% 0.20/0.50      inference('demod', [status(thm)], ['24', '25'])).
% 0.20/0.50  thf('33', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(d1_connsp_2, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.50           ( ![C:$i]:
% 0.20/0.50             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.50               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 0.20/0.50                 ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.20/0.50  thf('34', plain,
% 0.20/0.50      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X9))
% 0.20/0.50          | ~ (r2_hidden @ X8 @ (k1_tops_1 @ X9 @ X10))
% 0.20/0.50          | (m1_connsp_2 @ X10 @ X9 @ X8)
% 0.20/0.50          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.20/0.50          | ~ (l1_pre_topc @ X9)
% 0.20/0.50          | ~ (v2_pre_topc @ X9)
% 0.20/0.50          | (v2_struct_0 @ X9))),
% 0.20/0.50      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.20/0.50  thf('35', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v2_struct_0 @ sk_D)
% 0.20/0.50          | ~ (v2_pre_topc @ sk_D)
% 0.20/0.50          | ~ (l1_pre_topc @ sk_D)
% 0.20/0.50          | (m1_connsp_2 @ sk_F @ sk_D @ X0)
% 0.20/0.50          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_D @ sk_F))
% 0.20/0.50          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.50  thf('36', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(cc1_pre_topc, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.50       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.20/0.50  thf('37', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (~ (m1_pre_topc @ X0 @ X1)
% 0.20/0.50          | (v2_pre_topc @ X0)
% 0.20/0.50          | ~ (l1_pre_topc @ X1)
% 0.20/0.50          | ~ (v2_pre_topc @ X1))),
% 0.20/0.50      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.20/0.50  thf('38', plain,
% 0.20/0.50      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_D))),
% 0.20/0.50      inference('sup-', [status(thm)], ['36', '37'])).
% 0.20/0.50  thf('39', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('41', plain, ((v2_pre_topc @ sk_D)),
% 0.20/0.50      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.20/0.50  thf('42', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(dt_m1_pre_topc, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( l1_pre_topc @ A ) =>
% 0.20/0.50       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.20/0.50  thf('43', plain,
% 0.20/0.50      (![X2 : $i, X3 : $i]:
% 0.20/0.50         (~ (m1_pre_topc @ X2 @ X3) | (l1_pre_topc @ X2) | ~ (l1_pre_topc @ X3))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.20/0.50  thf('44', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 0.20/0.50      inference('sup-', [status(thm)], ['42', '43'])).
% 0.20/0.50  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('46', plain, ((l1_pre_topc @ sk_D)),
% 0.20/0.50      inference('demod', [status(thm)], ['44', '45'])).
% 0.20/0.50  thf('47', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t55_tops_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( l1_pre_topc @ B ) =>
% 0.20/0.50           ( ![C:$i]:
% 0.20/0.50             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.50               ( ![D:$i]:
% 0.20/0.50                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.20/0.50                   ( ( ( v3_pre_topc @ D @ B ) =>
% 0.20/0.50                       ( ( k1_tops_1 @ B @ D ) = ( D ) ) ) & 
% 0.20/0.50                     ( ( ( k1_tops_1 @ A @ C ) = ( C ) ) =>
% 0.20/0.50                       ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.50  thf('48', plain,
% 0.20/0.50      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.50         (~ (l1_pre_topc @ X4)
% 0.20/0.50          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.20/0.50          | ~ (v3_pre_topc @ X5 @ X4)
% 0.20/0.50          | ((k1_tops_1 @ X4 @ X5) = (X5))
% 0.20/0.50          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.20/0.50          | ~ (l1_pre_topc @ X7)
% 0.20/0.50          | ~ (v2_pre_topc @ X7))),
% 0.20/0.50      inference('cnf', [status(esa)], [t55_tops_1])).
% 0.20/0.50  thf('49', plain,
% 0.20/0.50      ((![X4 : $i, X5 : $i]:
% 0.20/0.50          (~ (l1_pre_topc @ X4)
% 0.20/0.50           | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.20/0.50           | ~ (v3_pre_topc @ X5 @ X4)
% 0.20/0.50           | ((k1_tops_1 @ X4 @ X5) = (X5))))
% 0.20/0.50         <= ((![X4 : $i, X5 : $i]:
% 0.20/0.50                (~ (l1_pre_topc @ X4)
% 0.20/0.50                 | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.20/0.50                 | ~ (v3_pre_topc @ X5 @ X4)
% 0.20/0.50                 | ((k1_tops_1 @ X4 @ X5) = (X5)))))),
% 0.20/0.50      inference('split', [status(esa)], ['48'])).
% 0.20/0.50  thf('50', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('51', plain,
% 0.20/0.50      ((![X6 : $i, X7 : $i]:
% 0.20/0.50          (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.20/0.50           | ~ (l1_pre_topc @ X7)
% 0.20/0.50           | ~ (v2_pre_topc @ X7)))
% 0.20/0.50         <= ((![X6 : $i, X7 : $i]:
% 0.20/0.50                (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.20/0.50                 | ~ (l1_pre_topc @ X7)
% 0.20/0.50                 | ~ (v2_pre_topc @ X7))))),
% 0.20/0.50      inference('split', [status(esa)], ['48'])).
% 0.20/0.50  thf('52', plain,
% 0.20/0.50      (((~ (v2_pre_topc @ sk_D) | ~ (l1_pre_topc @ sk_D)))
% 0.20/0.50         <= ((![X6 : $i, X7 : $i]:
% 0.20/0.50                (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.20/0.50                 | ~ (l1_pre_topc @ X7)
% 0.20/0.50                 | ~ (v2_pre_topc @ X7))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['50', '51'])).
% 0.20/0.50  thf('53', plain, ((v2_pre_topc @ sk_D)),
% 0.20/0.50      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.20/0.50  thf('54', plain, ((l1_pre_topc @ sk_D)),
% 0.20/0.50      inference('demod', [status(thm)], ['44', '45'])).
% 0.20/0.50  thf('55', plain,
% 0.20/0.50      (~
% 0.20/0.50       (![X6 : $i, X7 : $i]:
% 0.20/0.50          (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.20/0.50           | ~ (l1_pre_topc @ X7)
% 0.20/0.50           | ~ (v2_pre_topc @ X7)))),
% 0.20/0.50      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.20/0.50  thf('56', plain,
% 0.20/0.50      ((![X4 : $i, X5 : $i]:
% 0.20/0.50          (~ (l1_pre_topc @ X4)
% 0.20/0.50           | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.20/0.50           | ~ (v3_pre_topc @ X5 @ X4)
% 0.20/0.50           | ((k1_tops_1 @ X4 @ X5) = (X5)))) | 
% 0.20/0.50       (![X6 : $i, X7 : $i]:
% 0.20/0.50          (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.20/0.50           | ~ (l1_pre_topc @ X7)
% 0.20/0.50           | ~ (v2_pre_topc @ X7)))),
% 0.20/0.50      inference('split', [status(esa)], ['48'])).
% 0.20/0.50  thf('57', plain,
% 0.20/0.50      ((![X4 : $i, X5 : $i]:
% 0.20/0.50          (~ (l1_pre_topc @ X4)
% 0.20/0.50           | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.20/0.50           | ~ (v3_pre_topc @ X5 @ X4)
% 0.20/0.50           | ((k1_tops_1 @ X4 @ X5) = (X5))))),
% 0.20/0.50      inference('sat_resolution*', [status(thm)], ['55', '56'])).
% 0.20/0.50  thf('58', plain,
% 0.20/0.50      (![X4 : $i, X5 : $i]:
% 0.20/0.50         (~ (l1_pre_topc @ X4)
% 0.20/0.50          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.20/0.50          | ~ (v3_pre_topc @ X5 @ X4)
% 0.20/0.50          | ((k1_tops_1 @ X4 @ X5) = (X5)))),
% 0.20/0.50      inference('simpl_trail', [status(thm)], ['49', '57'])).
% 0.20/0.50  thf('59', plain,
% 0.20/0.50      ((((k1_tops_1 @ sk_D @ sk_F) = (sk_F))
% 0.20/0.50        | ~ (v3_pre_topc @ sk_F @ sk_D)
% 0.20/0.50        | ~ (l1_pre_topc @ sk_D))),
% 0.20/0.50      inference('sup-', [status(thm)], ['47', '58'])).
% 0.20/0.50  thf('60', plain, ((v3_pre_topc @ sk_F @ sk_D)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('61', plain, ((l1_pre_topc @ sk_D)),
% 0.20/0.50      inference('demod', [status(thm)], ['44', '45'])).
% 0.20/0.50  thf('62', plain, (((k1_tops_1 @ sk_D @ sk_F) = (sk_F))),
% 0.20/0.50      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.20/0.50  thf('63', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v2_struct_0 @ sk_D)
% 0.20/0.50          | (m1_connsp_2 @ sk_F @ sk_D @ X0)
% 0.20/0.50          | ~ (r2_hidden @ X0 @ sk_F)
% 0.20/0.50          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D)))),
% 0.20/0.50      inference('demod', [status(thm)], ['35', '41', '46', '62'])).
% 0.20/0.50  thf('64', plain,
% 0.20/0.50      ((~ (r2_hidden @ sk_H @ sk_F)
% 0.20/0.50        | (m1_connsp_2 @ sk_F @ sk_D @ sk_H)
% 0.20/0.50        | (v2_struct_0 @ sk_D))),
% 0.20/0.50      inference('sup-', [status(thm)], ['32', '63'])).
% 0.20/0.50  thf('65', plain, ((r2_hidden @ sk_G @ sk_F)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('66', plain, (((sk_G) = (sk_H))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('67', plain, ((r2_hidden @ sk_H @ sk_F)),
% 0.20/0.50      inference('demod', [status(thm)], ['65', '66'])).
% 0.20/0.50  thf('68', plain,
% 0.20/0.50      (((m1_connsp_2 @ sk_F @ sk_D @ sk_H) | (v2_struct_0 @ sk_D))),
% 0.20/0.50      inference('demod', [status(thm)], ['64', '67'])).
% 0.20/0.50  thf('69', plain, (~ (v2_struct_0 @ sk_D)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('70', plain, ((m1_connsp_2 @ sk_F @ sk_D @ sk_H)),
% 0.20/0.50      inference('clc', [status(thm)], ['68', '69'])).
% 0.20/0.50  thf('71', plain, ((r1_tarski @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('72', plain,
% 0.20/0.50      ((((v2_struct_0 @ sk_B)
% 0.20/0.50         | (v2_struct_0 @ sk_D)
% 0.20/0.50         | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H)
% 0.20/0.50         | (v2_struct_0 @ sk_C)
% 0.20/0.50         | (v2_struct_0 @ sk_A)))
% 0.20/0.50         <= (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.50               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_H)))),
% 0.20/0.50      inference('demod', [status(thm)], ['31', '70', '71'])).
% 0.20/0.50  thf('73', plain,
% 0.20/0.50      ((~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G))
% 0.20/0.50         <= (~ ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G)))),
% 0.20/0.50      inference('split', [status(esa)], ['7'])).
% 0.20/0.50  thf('74', plain, (((sk_G) = (sk_H))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('75', plain,
% 0.20/0.50      ((~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H))
% 0.20/0.50         <= (~ ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G)))),
% 0.20/0.50      inference('demod', [status(thm)], ['73', '74'])).
% 0.20/0.50  thf('76', plain,
% 0.20/0.50      ((((v2_struct_0 @ sk_A)
% 0.20/0.50         | (v2_struct_0 @ sk_C)
% 0.20/0.50         | (v2_struct_0 @ sk_D)
% 0.20/0.50         | (v2_struct_0 @ sk_B)))
% 0.20/0.50         <= (~ ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G)) & 
% 0.20/0.50             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.50               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_H)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['72', '75'])).
% 0.20/0.50  thf('77', plain, (~ (v2_struct_0 @ sk_D)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('78', plain,
% 0.20/0.50      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A)))
% 0.20/0.50         <= (~ ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G)) & 
% 0.20/0.50             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.50               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_H)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['76', '77'])).
% 0.20/0.50  thf('79', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('80', plain,
% 0.20/0.50      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C)))
% 0.20/0.50         <= (~ ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G)) & 
% 0.20/0.50             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.50               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_H)))),
% 0.20/0.50      inference('clc', [status(thm)], ['78', '79'])).
% 0.20/0.50  thf('81', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('82', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_C))
% 0.20/0.50         <= (~ ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G)) & 
% 0.20/0.50             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.50               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_H)))),
% 0.20/0.50      inference('clc', [status(thm)], ['80', '81'])).
% 0.20/0.50  thf('83', plain, (~ (v2_struct_0 @ sk_C)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('84', plain,
% 0.20/0.50      (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G)) | 
% 0.20/0.50       ~
% 0.20/0.50       ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.50         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_H))),
% 0.20/0.50      inference('sup-', [status(thm)], ['82', '83'])).
% 0.20/0.50  thf('85', plain,
% 0.20/0.50      (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G)) | 
% 0.20/0.50       ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.50         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_H))),
% 0.20/0.50      inference('split', [status(esa)], ['3'])).
% 0.20/0.50  thf('86', plain, (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_G))),
% 0.20/0.50      inference('sat_resolution*', [status(thm)], ['8', '84', '85'])).
% 0.20/0.50  thf('87', plain, ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_H)),
% 0.20/0.50      inference('simpl_trail', [status(thm)], ['6', '86'])).
% 0.20/0.50  thf('88', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('89', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_E @ 
% 0.20/0.50        (k1_zfmisc_1 @ 
% 0.20/0.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('90', plain,
% 0.20/0.50      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, 
% 0.20/0.50         X21 : $i]:
% 0.20/0.50         ((v2_struct_0 @ X14)
% 0.20/0.50          | ~ (v2_pre_topc @ X14)
% 0.20/0.50          | ~ (l1_pre_topc @ X14)
% 0.20/0.50          | (v2_struct_0 @ X15)
% 0.20/0.50          | ~ (m1_pre_topc @ X15 @ X16)
% 0.20/0.50          | ~ (m1_pre_topc @ X17 @ X15)
% 0.20/0.50          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.20/0.50          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X17))
% 0.20/0.50          | ~ (r1_tmap_1 @ X15 @ X14 @ X20 @ X21)
% 0.20/0.50          | (r1_tmap_1 @ X17 @ X14 @ 
% 0.20/0.50             (k3_tmap_1 @ X16 @ X14 @ X15 @ X17 @ X20) @ X19)
% 0.20/0.50          | ((X21) != (X19))
% 0.20/0.50          | ~ (m1_connsp_2 @ X18 @ X15 @ X21)
% 0.20/0.50          | ~ (r1_tarski @ X18 @ (u1_struct_0 @ X17))
% 0.20/0.50          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X15))
% 0.20/0.50          | ~ (m1_subset_1 @ X20 @ 
% 0.20/0.50               (k1_zfmisc_1 @ 
% 0.20/0.50                (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X14))))
% 0.20/0.50          | ~ (v1_funct_2 @ X20 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X14))
% 0.20/0.50          | ~ (v1_funct_1 @ X20)
% 0.20/0.50          | ~ (m1_pre_topc @ X17 @ X16)
% 0.20/0.50          | (v2_struct_0 @ X17)
% 0.20/0.50          | ~ (l1_pre_topc @ X16)
% 0.20/0.50          | ~ (v2_pre_topc @ X16)
% 0.20/0.50          | (v2_struct_0 @ X16))),
% 0.20/0.50      inference('cnf', [status(esa)], [t83_tmap_1])).
% 0.20/0.50  thf('91', plain,
% 0.20/0.50      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.20/0.50         ((v2_struct_0 @ X16)
% 0.20/0.50          | ~ (v2_pre_topc @ X16)
% 0.20/0.50          | ~ (l1_pre_topc @ X16)
% 0.20/0.50          | (v2_struct_0 @ X17)
% 0.20/0.50          | ~ (m1_pre_topc @ X17 @ X16)
% 0.20/0.50          | ~ (v1_funct_1 @ X20)
% 0.20/0.50          | ~ (v1_funct_2 @ X20 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X14))
% 0.20/0.50          | ~ (m1_subset_1 @ X20 @ 
% 0.20/0.50               (k1_zfmisc_1 @ 
% 0.20/0.50                (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X14))))
% 0.20/0.50          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X15))
% 0.20/0.50          | ~ (r1_tarski @ X18 @ (u1_struct_0 @ X17))
% 0.20/0.50          | ~ (m1_connsp_2 @ X18 @ X15 @ X19)
% 0.20/0.50          | (r1_tmap_1 @ X17 @ X14 @ 
% 0.20/0.50             (k3_tmap_1 @ X16 @ X14 @ X15 @ X17 @ X20) @ X19)
% 0.20/0.50          | ~ (r1_tmap_1 @ X15 @ X14 @ X20 @ X19)
% 0.20/0.50          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X17))
% 0.20/0.50          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.20/0.50          | ~ (m1_pre_topc @ X17 @ X15)
% 0.20/0.50          | ~ (m1_pre_topc @ X15 @ X16)
% 0.20/0.50          | (v2_struct_0 @ X15)
% 0.20/0.50          | ~ (l1_pre_topc @ X14)
% 0.20/0.50          | ~ (v2_pre_topc @ X14)
% 0.20/0.50          | (v2_struct_0 @ X14))),
% 0.20/0.50      inference('simplify', [status(thm)], ['90'])).
% 0.20/0.50  thf('92', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.50         ((v2_struct_0 @ sk_B)
% 0.20/0.50          | ~ (v2_pre_topc @ sk_B)
% 0.20/0.50          | ~ (l1_pre_topc @ sk_B)
% 0.20/0.50          | (v2_struct_0 @ sk_D)
% 0.20/0.50          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.20/0.50          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.20/0.50          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.20/0.50          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.20/0.50          | ~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X3)
% 0.20/0.50          | (r1_tmap_1 @ X1 @ sk_B @ 
% 0.20/0.50             (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X3)
% 0.20/0.50          | ~ (m1_connsp_2 @ X2 @ sk_D @ X3)
% 0.20/0.50          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X1))
% 0.20/0.50          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_D))
% 0.20/0.50          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.20/0.50          | ~ (v1_funct_1 @ sk_E)
% 0.20/0.50          | ~ (m1_pre_topc @ X1 @ X0)
% 0.20/0.50          | (v2_struct_0 @ X1)
% 0.20/0.50          | ~ (l1_pre_topc @ X0)
% 0.20/0.50          | ~ (v2_pre_topc @ X0)
% 0.20/0.50          | (v2_struct_0 @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['89', '91'])).
% 0.20/0.50  thf('93', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('94', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('95', plain,
% 0.20/0.50      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('96', plain, ((v1_funct_1 @ sk_E)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('97', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.50         ((v2_struct_0 @ sk_B)
% 0.20/0.50          | (v2_struct_0 @ sk_D)
% 0.20/0.50          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.20/0.50          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.20/0.50          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.20/0.50          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.20/0.50          | ~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X3)
% 0.20/0.50          | (r1_tmap_1 @ X1 @ sk_B @ 
% 0.20/0.50             (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X3)
% 0.20/0.50          | ~ (m1_connsp_2 @ X2 @ sk_D @ X3)
% 0.20/0.50          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X1))
% 0.20/0.50          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_D))
% 0.20/0.50          | ~ (m1_pre_topc @ X1 @ X0)
% 0.20/0.50          | (v2_struct_0 @ X1)
% 0.20/0.50          | ~ (l1_pre_topc @ X0)
% 0.20/0.50          | ~ (v2_pre_topc @ X0)
% 0.20/0.50          | (v2_struct_0 @ X0))),
% 0.20/0.50      inference('demod', [status(thm)], ['92', '93', '94', '95', '96'])).
% 0.20/0.50  thf('98', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         ((v2_struct_0 @ X0)
% 0.20/0.50          | ~ (v2_pre_topc @ X0)
% 0.20/0.50          | ~ (l1_pre_topc @ X0)
% 0.20/0.50          | (v2_struct_0 @ X1)
% 0.20/0.50          | ~ (m1_pre_topc @ X1 @ X0)
% 0.20/0.50          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 0.20/0.50          | ~ (r1_tarski @ sk_F @ (u1_struct_0 @ X1))
% 0.20/0.50          | ~ (m1_connsp_2 @ sk_F @ sk_D @ X2)
% 0.20/0.50          | (r1_tmap_1 @ X1 @ sk_B @ 
% 0.20/0.50             (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X2)
% 0.20/0.50          | ~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2)
% 0.20/0.50          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.20/0.50          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.20/0.50          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.20/0.50          | (v2_struct_0 @ sk_D)
% 0.20/0.50          | (v2_struct_0 @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['88', '97'])).
% 0.20/0.50  thf('99', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((v2_struct_0 @ sk_B)
% 0.20/0.50          | (v2_struct_0 @ sk_D)
% 0.20/0.50          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.20/0.50          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.20/0.50          | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ X1))
% 0.20/0.50          | (r1_tmap_1 @ X1 @ sk_B @ 
% 0.20/0.50             (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ sk_H)
% 0.20/0.50          | ~ (m1_connsp_2 @ sk_F @ sk_D @ sk_H)
% 0.20/0.50          | ~ (r1_tarski @ sk_F @ (u1_struct_0 @ X1))
% 0.20/0.50          | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D))
% 0.20/0.50          | ~ (m1_pre_topc @ X1 @ X0)
% 0.20/0.50          | (v2_struct_0 @ X1)
% 0.20/0.50          | ~ (l1_pre_topc @ X0)
% 0.20/0.50          | ~ (v2_pre_topc @ X0)
% 0.20/0.50          | (v2_struct_0 @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['87', '98'])).
% 0.20/0.50  thf('100', plain, ((m1_connsp_2 @ sk_F @ sk_D @ sk_H)),
% 0.20/0.50      inference('clc', [status(thm)], ['68', '69'])).
% 0.20/0.50  thf('101', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D))),
% 0.20/0.50      inference('demod', [status(thm)], ['24', '25'])).
% 0.20/0.50  thf('102', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((v2_struct_0 @ sk_B)
% 0.20/0.50          | (v2_struct_0 @ sk_D)
% 0.20/0.50          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.20/0.50          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.20/0.50          | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ X1))
% 0.20/0.50          | (r1_tmap_1 @ X1 @ sk_B @ 
% 0.20/0.50             (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ sk_H)
% 0.20/0.50          | ~ (r1_tarski @ sk_F @ (u1_struct_0 @ X1))
% 0.20/0.50          | ~ (m1_pre_topc @ X1 @ X0)
% 0.20/0.50          | (v2_struct_0 @ X1)
% 0.20/0.50          | ~ (l1_pre_topc @ X0)
% 0.20/0.50          | ~ (v2_pre_topc @ X0)
% 0.20/0.50          | (v2_struct_0 @ X0))),
% 0.20/0.50      inference('demod', [status(thm)], ['99', '100', '101'])).
% 0.20/0.50  thf('103', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v2_struct_0 @ X0)
% 0.20/0.50          | ~ (v2_pre_topc @ X0)
% 0.20/0.50          | ~ (l1_pre_topc @ X0)
% 0.20/0.50          | (v2_struct_0 @ sk_C)
% 0.20/0.50          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.20/0.50          | ~ (r1_tarski @ sk_F @ (u1_struct_0 @ sk_C))
% 0.20/0.50          | (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.50             (k3_tmap_1 @ X0 @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_H)
% 0.20/0.50          | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.20/0.50          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.20/0.50          | (v2_struct_0 @ sk_D)
% 0.20/0.50          | (v2_struct_0 @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['2', '102'])).
% 0.20/0.50  thf('104', plain, ((r1_tarski @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('105', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('106', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v2_struct_0 @ X0)
% 0.20/0.50          | ~ (v2_pre_topc @ X0)
% 0.20/0.50          | ~ (l1_pre_topc @ X0)
% 0.20/0.50          | (v2_struct_0 @ sk_C)
% 0.20/0.50          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.20/0.50          | (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.50             (k3_tmap_1 @ X0 @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_H)
% 0.20/0.50          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.20/0.50          | (v2_struct_0 @ sk_D)
% 0.20/0.50          | (v2_struct_0 @ sk_B))),
% 0.20/0.50      inference('demod', [status(thm)], ['103', '104', '105'])).
% 0.20/0.50  thf('107', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_B)
% 0.20/0.50        | (v2_struct_0 @ sk_D)
% 0.20/0.50        | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.20/0.50        | (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.50           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_H)
% 0.20/0.50        | (v2_struct_0 @ sk_C)
% 0.20/0.50        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.50        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.50        | (v2_struct_0 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['1', '106'])).
% 0.20/0.50  thf('108', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('109', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('110', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('111', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_B)
% 0.20/0.50        | (v2_struct_0 @ sk_D)
% 0.20/0.50        | (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.50           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_H)
% 0.20/0.50        | (v2_struct_0 @ sk_C)
% 0.20/0.50        | (v2_struct_0 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['107', '108', '109', '110'])).
% 0.20/0.50  thf('112', plain,
% 0.20/0.50      ((~ (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.50           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_H))
% 0.20/0.50         <= (~
% 0.20/0.50             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.50               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_H)))),
% 0.20/0.50      inference('split', [status(esa)], ['7'])).
% 0.20/0.50  thf('113', plain,
% 0.20/0.50      (~
% 0.20/0.50       ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.50         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_H))),
% 0.20/0.50      inference('sat_resolution*', [status(thm)], ['8', '84'])).
% 0.20/0.50  thf('114', plain,
% 0.20/0.50      (~ (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.50          (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_H)),
% 0.20/0.50      inference('simpl_trail', [status(thm)], ['112', '113'])).
% 0.20/0.50  thf('115', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_A)
% 0.20/0.50        | (v2_struct_0 @ sk_C)
% 0.20/0.50        | (v2_struct_0 @ sk_D)
% 0.20/0.50        | (v2_struct_0 @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['111', '114'])).
% 0.20/0.50  thf('116', plain, (~ (v2_struct_0 @ sk_D)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('117', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['115', '116'])).
% 0.20/0.50  thf('118', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('119', plain, (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C))),
% 0.20/0.50      inference('clc', [status(thm)], ['117', '118'])).
% 0.20/0.50  thf('120', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('121', plain, ((v2_struct_0 @ sk_C)),
% 0.20/0.50      inference('clc', [status(thm)], ['119', '120'])).
% 0.20/0.50  thf('122', plain, ($false), inference('demod', [status(thm)], ['0', '121'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
