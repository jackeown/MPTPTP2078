%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YGdOE9c90H

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:19 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  158 ( 697 expanded)
%              Number of leaves         :   32 ( 210 expanded)
%              Depth                    :   32
%              Number of atoms          : 1992 (27782 expanded)
%              Number of equality atoms :   11 ( 312 expanded)
%              Maximal formula depth    :   32 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_F_type,type,(
    sk_F: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t85_tmap_1,conjecture,(
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
                & ( m1_pre_topc @ C @ B ) )
             => ! [D: $i] :
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( m1_pre_topc @ D @ B ) )
                 => ! [E: $i] :
                      ( ( ( v1_funct_1 @ E )
                        & ( v1_funct_2 @ E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) ) ) )
                     => ( ( m1_pre_topc @ C @ D )
                       => ! [F: $i] :
                            ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                           => ! [G: $i] :
                                ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) )
                               => ! [H: $i] :
                                    ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) )
                                   => ( ( ( v3_pre_topc @ F @ B )
                                        & ( r2_hidden @ G @ F )
                                        & ( r1_tarski @ F @ ( u1_struct_0 @ C ) )
                                        & ( G = H ) )
                                     => ( ( r1_tmap_1 @ D @ A @ E @ G )
                                      <=> ( r1_tmap_1 @ C @ A @ ( k3_tmap_1 @ B @ A @ D @ C @ E ) @ H ) ) ) ) ) ) ) ) ) ) ) ) )).

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
                  & ( m1_pre_topc @ C @ B ) )
               => ! [D: $i] :
                    ( ( ~ ( v2_struct_0 @ D )
                      & ( m1_pre_topc @ D @ B ) )
                   => ! [E: $i] :
                        ( ( ( v1_funct_1 @ E )
                          & ( v1_funct_2 @ E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) )
                          & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) ) ) )
                       => ( ( m1_pre_topc @ C @ D )
                         => ! [F: $i] :
                              ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                             => ! [G: $i] :
                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) )
                                 => ! [H: $i] :
                                      ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) )
                                     => ( ( ( v3_pre_topc @ F @ B )
                                          & ( r2_hidden @ G @ F )
                                          & ( r1_tarski @ F @ ( u1_struct_0 @ C ) )
                                          & ( G = H ) )
                                       => ( ( r1_tmap_1 @ D @ A @ E @ G )
                                        <=> ( r1_tmap_1 @ C @ A @ ( k3_tmap_1 @ B @ A @ D @ C @ E ) @ H ) ) ) ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t85_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H )
    | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H )
    | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G ) ),
    inference(split,[status(esa)],['7'])).

thf('9',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    r1_tarski @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('11',plain,(
    ! [X0: $i,X2: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X2 ) )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('12',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t39_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
             => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('13',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X7 @ X8 )
      | ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[t39_pre_topc])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
    | ~ ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf('16',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('17',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_pre_topc @ X5 @ X6 )
      | ( l1_pre_topc @ X5 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('18',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['15','20'])).

thf('22',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H )
   <= ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H ) ),
    inference(split,[status(esa)],['3'])).

thf('23',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ) ) ),
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

thf('24',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( v2_struct_0 @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ~ ( l1_pre_topc @ X20 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_pre_topc @ X21 @ X22 )
      | ~ ( m1_pre_topc @ X23 @ X21 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X23 ) )
      | ~ ( r1_tmap_1 @ X23 @ X20 @ ( k3_tmap_1 @ X22 @ X20 @ X21 @ X23 @ X26 ) @ X25 )
      | ( r1_tmap_1 @ X21 @ X20 @ X26 @ X27 )
      | ( X27 != X25 )
      | ~ ( m1_connsp_2 @ X24 @ X21 @ X27 )
      | ~ ( r1_tarski @ X24 @ ( u1_struct_0 @ X23 ) )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X21 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X20 ) ) ) )
      | ~ ( v1_funct_2 @ X26 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X20 ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( m1_pre_topc @ X23 @ X22 )
      | ( v2_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t83_tmap_1])).

thf('25',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( v2_struct_0 @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ~ ( l1_pre_topc @ X22 )
      | ( v2_struct_0 @ X23 )
      | ~ ( m1_pre_topc @ X23 @ X22 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_funct_2 @ X26 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X20 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X20 ) ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X21 ) )
      | ~ ( r1_tarski @ X24 @ ( u1_struct_0 @ X23 ) )
      | ~ ( m1_connsp_2 @ X24 @ X21 @ X25 )
      | ( r1_tmap_1 @ X21 @ X20 @ X26 @ X25 )
      | ~ ( r1_tmap_1 @ X23 @ X20 @ ( k3_tmap_1 @ X22 @ X20 @ X21 @ X23 @ X26 ) @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X23 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( m1_pre_topc @ X23 @ X21 )
      | ~ ( m1_pre_topc @ X21 @ X22 )
      | ( v2_struct_0 @ X21 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_tmap_1 @ X1 @ sk_A @ ( k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E ) @ X3 )
      | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X3 )
      | ~ ( m1_connsp_2 @ X2 @ sk_D @ X3 )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_tmap_1 @ X1 @ sk_A @ ( k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E ) @ X3 )
      | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X3 )
      | ~ ( m1_connsp_2 @ X2 @ sk_D @ X3 )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['26','27','28','29','30'])).

thf('32',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ~ ( v2_pre_topc @ sk_B )
        | ~ ( l1_pre_topc @ sk_B )
        | ( v2_struct_0 @ sk_C )
        | ~ ( m1_pre_topc @ sk_C @ sk_B )
        | ~ ( m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_D ) )
        | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_C ) )
        | ~ ( m1_connsp_2 @ X0 @ sk_D @ sk_H )
        | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H )
        | ~ ( m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_C ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
        | ~ ( m1_pre_topc @ sk_C @ sk_D )
        | ~ ( m1_pre_topc @ sk_D @ sk_B )
        | ( v2_struct_0 @ sk_D )
        | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H ) ),
    inference('sup-',[status(thm)],['22','31'])).

thf('33',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_C )
        | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_C ) )
        | ~ ( m1_connsp_2 @ X0 @ sk_D @ sk_H )
        | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
        | ( v2_struct_0 @ sk_D )
        | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H ) ),
    inference(demod,[status(thm)],['32','33','34','35','38','39','40','41'])).

thf('43',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H )
      | ~ ( m1_connsp_2 @ sk_F @ sk_D @ sk_H )
      | ~ ( r1_tarski @ sk_F @ ( u1_struct_0 @ sk_C ) )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H ) ),
    inference('sup-',[status(thm)],['21','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('45',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['15','20'])).

thf(t5_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( ( v3_pre_topc @ B @ A )
                  & ( r2_hidden @ C @ B ) )
               => ( m1_connsp_2 @ B @ A @ C ) ) ) ) ) )).

thf('46',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( v3_pre_topc @ X14 @ X15 )
      | ~ ( r2_hidden @ X16 @ X14 )
      | ( m1_connsp_2 @ X14 @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X15 ) )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t5_connsp_2])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D ) )
      | ( m1_connsp_2 @ sk_F @ sk_D @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_F )
      | ~ ( v3_pre_topc @ sk_F @ sk_D ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('49',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_pre_topc @ X3 @ X4 )
      | ( v2_pre_topc @ X3 )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( v2_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('50',plain,
    ( ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['18','19'])).

thf('55',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['15','20'])).

thf(t33_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_pre_topc @ C @ A )
             => ( ( v3_pre_topc @ B @ A )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) )
                   => ( ( D = B )
                     => ( v3_pre_topc @ D @ C ) ) ) ) ) ) ) )).

thf('57',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( v3_pre_topc @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( v3_pre_topc @ X12 @ X13 )
      | ( X12 != X10 )
      | ~ ( m1_pre_topc @ X13 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t33_tops_2])).

thf('58',plain,(
    ! [X10: $i,X11: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( m1_pre_topc @ X13 @ X11 )
      | ( v3_pre_topc @ X10 @ X13 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( v3_pre_topc @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v3_pre_topc @ sk_F @ X0 )
      | ( v3_pre_topc @ sk_F @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','58'])).

thf('60',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ~ ( m1_pre_topc @ sk_D @ sk_B )
    | ( v3_pre_topc @ sk_F @ sk_D )
    | ~ ( v3_pre_topc @ sk_F @ sk_B ) ),
    inference('sup-',[status(thm)],['55','59'])).

thf('61',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v3_pre_topc @ sk_F @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v3_pre_topc @ sk_F @ sk_D ),
    inference(demod,[status(thm)],['60','61','62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D ) )
      | ( m1_connsp_2 @ sk_F @ sk_D @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_F ) ) ),
    inference(demod,[status(thm)],['47','53','54','64'])).

thf('66',plain,
    ( ~ ( r2_hidden @ sk_H @ sk_F )
    | ( m1_connsp_2 @ sk_F @ sk_D @ sk_H )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['44','65'])).

thf('67',plain,(
    r2_hidden @ sk_G @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    r2_hidden @ sk_H @ sk_F ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( m1_connsp_2 @ sk_F @ sk_D @ sk_H )
    | ( v2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['66','69'])).

thf('71',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    m1_connsp_2 @ sk_F @ sk_D @ sk_H ),
    inference(clc,[status(thm)],['70','71'])).

thf('73',plain,(
    r1_tarski @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H ) ),
    inference(demod,[status(thm)],['43','72','73'])).

thf('75',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G )
   <= ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G ) ),
    inference(split,[status(esa)],['7'])).

thf('76',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H )
   <= ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G )
      & ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H ) ) ),
    inference('sup-',[status(thm)],['74','77'])).

thf('79',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G )
      & ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G )
      & ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H ) ) ),
    inference(clc,[status(thm)],['80','81'])).

thf('83',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( v2_struct_0 @ sk_C )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G )
      & ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H ) ) ),
    inference(clc,[status(thm)],['82','83'])).

thf('85',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G )
    | ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G )
    | ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H ) ),
    inference(split,[status(esa)],['3'])).

thf('88',plain,(
    r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G ),
    inference('sat_resolution*',[status(thm)],['8','86','87'])).

thf('89',plain,(
    r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H ),
    inference(simpl_trail,[status(thm)],['6','88'])).

thf('90',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['15','20'])).

thf('91',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( v2_struct_0 @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ~ ( l1_pre_topc @ X20 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_pre_topc @ X21 @ X22 )
      | ~ ( m1_pre_topc @ X23 @ X21 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X23 ) )
      | ~ ( r1_tmap_1 @ X21 @ X20 @ X26 @ X27 )
      | ( r1_tmap_1 @ X23 @ X20 @ ( k3_tmap_1 @ X22 @ X20 @ X21 @ X23 @ X26 ) @ X25 )
      | ( X27 != X25 )
      | ~ ( m1_connsp_2 @ X24 @ X21 @ X27 )
      | ~ ( r1_tarski @ X24 @ ( u1_struct_0 @ X23 ) )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X21 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X20 ) ) ) )
      | ~ ( v1_funct_2 @ X26 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X20 ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( m1_pre_topc @ X23 @ X22 )
      | ( v2_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t83_tmap_1])).

thf('93',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( v2_struct_0 @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ~ ( l1_pre_topc @ X22 )
      | ( v2_struct_0 @ X23 )
      | ~ ( m1_pre_topc @ X23 @ X22 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_funct_2 @ X26 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X20 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X20 ) ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X21 ) )
      | ~ ( r1_tarski @ X24 @ ( u1_struct_0 @ X23 ) )
      | ~ ( m1_connsp_2 @ X24 @ X21 @ X25 )
      | ( r1_tmap_1 @ X23 @ X20 @ ( k3_tmap_1 @ X22 @ X20 @ X21 @ X23 @ X26 ) @ X25 )
      | ~ ( r1_tmap_1 @ X21 @ X20 @ X26 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X23 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( m1_pre_topc @ X23 @ X21 )
      | ~ ( m1_pre_topc @ X21 @ X22 )
      | ( v2_struct_0 @ X21 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X3 )
      | ( r1_tmap_1 @ X1 @ sk_A @ ( k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E ) @ X3 )
      | ~ ( m1_connsp_2 @ X2 @ sk_D @ X3 )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['91','93'])).

thf('95',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X3 )
      | ( r1_tmap_1 @ X1 @ sk_A @ ( k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E ) @ X3 )
      | ~ ( m1_connsp_2 @ X2 @ sk_D @ X3 )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['94','95','96','97','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( r1_tarski @ sk_F @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_connsp_2 @ sk_F @ sk_D @ X2 )
      | ( r1_tmap_1 @ X1 @ sk_A @ ( k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E ) @ X2 )
      | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['90','99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_subset_1 @ sk_H @ ( u1_struct_0 @ X1 ) )
      | ( r1_tmap_1 @ X1 @ sk_A @ ( k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E ) @ sk_H )
      | ~ ( m1_connsp_2 @ sk_F @ sk_D @ sk_H )
      | ~ ( r1_tarski @ sk_F @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_D ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['89','100'])).

thf('102',plain,(
    m1_connsp_2 @ sk_F @ sk_D @ sk_H ),
    inference(clc,[status(thm)],['70','71'])).

thf('103',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_subset_1 @ sk_H @ ( u1_struct_0 @ X1 ) )
      | ( r1_tmap_1 @ X1 @ sk_A @ ( k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E ) @ sk_H )
      | ~ ( r1_tarski @ sk_F @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['101','102','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ~ ( r1_tarski @ sk_F @ ( u1_struct_0 @ sk_C ) )
      | ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ X0 @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H )
      | ~ ( m1_pre_topc @ sk_C @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','104'])).

thf('106',plain,(
    r1_tarski @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ X0 @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['105','106','107'])).

thf('109',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ~ ( m1_pre_topc @ sk_D @ sk_B )
    | ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H )
    | ( v2_struct_0 @ sk_C )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','108'])).

thf('110',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['109','110','111','112'])).

thf('114',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H )
   <= ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H ) ),
    inference(split,[status(esa)],['7'])).

thf('115',plain,(
    ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H ) ),
    inference('sat_resolution*',[status(thm)],['8','86'])).

thf('116',plain,(
    ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H ) ),
    inference(simpl_trail,[status(thm)],['114','115'])).

thf('117',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['113','116'])).

thf('118',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['119','120'])).

thf('122',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    v2_struct_0 @ sk_C ),
    inference(clc,[status(thm)],['121','122'])).

thf('124',plain,(
    $false ),
    inference(demod,[status(thm)],['0','123'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YGdOE9c90H
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:20:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.52  % Solved by: fo/fo7.sh
% 0.21/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.52  % done 89 iterations in 0.051s
% 0.21/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.52  % SZS output start Refutation
% 0.21/0.52  thf(sk_F_type, type, sk_F: $i).
% 0.21/0.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.52  thf(sk_G_type, type, sk_G: $i).
% 0.21/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.52  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.21/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.52  thf(sk_E_type, type, sk_E: $i).
% 0.21/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.52  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.21/0.52  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.52  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.52  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.21/0.52  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.21/0.52  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.21/0.52  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.52  thf(sk_H_type, type, sk_H: $i).
% 0.21/0.52  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.52  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.52  thf(t85_tmap_1, conjecture,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.52             ( l1_pre_topc @ B ) ) =>
% 0.21/0.52           ( ![C:$i]:
% 0.21/0.52             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.21/0.52               ( ![D:$i]:
% 0.21/0.52                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.21/0.52                   ( ![E:$i]:
% 0.21/0.52                     ( ( ( v1_funct_1 @ E ) & 
% 0.21/0.52                         ( v1_funct_2 @
% 0.21/0.52                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.52                         ( m1_subset_1 @
% 0.21/0.52                           E @ 
% 0.21/0.52                           ( k1_zfmisc_1 @
% 0.21/0.52                             ( k2_zfmisc_1 @
% 0.21/0.52                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.21/0.52                       ( ( m1_pre_topc @ C @ D ) =>
% 0.21/0.52                         ( ![F:$i]:
% 0.21/0.52                           ( ( m1_subset_1 @
% 0.21/0.52                               F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.21/0.52                             ( ![G:$i]:
% 0.21/0.52                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.21/0.52                                 ( ![H:$i]:
% 0.21/0.52                                   ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) ) =>
% 0.21/0.52                                     ( ( ( v3_pre_topc @ F @ B ) & 
% 0.21/0.52                                         ( r2_hidden @ G @ F ) & 
% 0.21/0.52                                         ( r1_tarski @ F @ ( u1_struct_0 @ C ) ) & 
% 0.21/0.52                                         ( ( G ) = ( H ) ) ) =>
% 0.21/0.52                                       ( ( r1_tmap_1 @ D @ A @ E @ G ) <=>
% 0.21/0.52                                         ( r1_tmap_1 @
% 0.21/0.52                                           C @ A @ 
% 0.21/0.52                                           ( k3_tmap_1 @ B @ A @ D @ C @ E ) @ 
% 0.21/0.52                                           H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.52    (~( ![A:$i]:
% 0.21/0.52        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.52            ( l1_pre_topc @ A ) ) =>
% 0.21/0.52          ( ![B:$i]:
% 0.21/0.52            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.52                ( l1_pre_topc @ B ) ) =>
% 0.21/0.52              ( ![C:$i]:
% 0.21/0.52                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.21/0.52                  ( ![D:$i]:
% 0.21/0.52                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.21/0.52                      ( ![E:$i]:
% 0.21/0.52                        ( ( ( v1_funct_1 @ E ) & 
% 0.21/0.52                            ( v1_funct_2 @
% 0.21/0.52                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.52                            ( m1_subset_1 @
% 0.21/0.52                              E @ 
% 0.21/0.52                              ( k1_zfmisc_1 @
% 0.21/0.52                                ( k2_zfmisc_1 @
% 0.21/0.52                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.21/0.52                          ( ( m1_pre_topc @ C @ D ) =>
% 0.21/0.52                            ( ![F:$i]:
% 0.21/0.52                              ( ( m1_subset_1 @
% 0.21/0.52                                  F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.21/0.52                                ( ![G:$i]:
% 0.21/0.52                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.21/0.52                                    ( ![H:$i]:
% 0.21/0.52                                      ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) ) =>
% 0.21/0.52                                        ( ( ( v3_pre_topc @ F @ B ) & 
% 0.21/0.52                                            ( r2_hidden @ G @ F ) & 
% 0.21/0.52                                            ( r1_tarski @
% 0.21/0.52                                              F @ ( u1_struct_0 @ C ) ) & 
% 0.21/0.52                                            ( ( G ) = ( H ) ) ) =>
% 0.21/0.52                                          ( ( r1_tmap_1 @ D @ A @ E @ G ) <=>
% 0.21/0.52                                            ( r1_tmap_1 @
% 0.21/0.52                                              C @ A @ 
% 0.21/0.52                                              ( k3_tmap_1 @ B @ A @ D @ C @ E ) @ 
% 0.21/0.52                                              H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.52    inference('cnf.neg', [status(esa)], [t85_tmap_1])).
% 0.21/0.52  thf('0', plain, (~ (v2_struct_0 @ sk_C)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('1', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('2', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_C))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('3', plain,
% 0.21/0.52      (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.52         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H)
% 0.21/0.52        | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('4', plain,
% 0.21/0.52      (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G))
% 0.21/0.52         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G)))),
% 0.21/0.52      inference('split', [status(esa)], ['3'])).
% 0.21/0.52  thf('5', plain, (((sk_G) = (sk_H))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('6', plain,
% 0.21/0.52      (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H))
% 0.21/0.52         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G)))),
% 0.21/0.52      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.52  thf('7', plain,
% 0.21/0.52      ((~ (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.52           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H)
% 0.21/0.52        | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('8', plain,
% 0.21/0.52      (~
% 0.21/0.52       ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.52         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H)) | 
% 0.21/0.52       ~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G))),
% 0.21/0.52      inference('split', [status(esa)], ['7'])).
% 0.21/0.52  thf('9', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('10', plain, ((r1_tarski @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(t3_subset, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.52  thf('11', plain,
% 0.21/0.52      (![X0 : $i, X2 : $i]:
% 0.21/0.52         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X2)) | ~ (r1_tarski @ X0 @ X2))),
% 0.21/0.52      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.52  thf('12', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.52  thf(t39_pre_topc, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( l1_pre_topc @ A ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.52           ( ![C:$i]:
% 0.21/0.52             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.21/0.52               ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ))).
% 0.21/0.52  thf('13', plain,
% 0.21/0.52      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.52         (~ (m1_pre_topc @ X7 @ X8)
% 0.21/0.52          | (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.21/0.52          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.21/0.52          | ~ (l1_pre_topc @ X8))),
% 0.21/0.52      inference('cnf', [status(esa)], [t39_pre_topc])).
% 0.21/0.52  thf('14', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (l1_pre_topc @ X0)
% 0.21/0.52          | (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.21/0.52          | ~ (m1_pre_topc @ sk_C @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.52  thf('15', plain,
% 0.21/0.52      (((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.21/0.52        | ~ (l1_pre_topc @ sk_D))),
% 0.21/0.52      inference('sup-', [status(thm)], ['9', '14'])).
% 0.21/0.52  thf('16', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(dt_m1_pre_topc, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( l1_pre_topc @ A ) =>
% 0.21/0.52       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.21/0.52  thf('17', plain,
% 0.21/0.52      (![X5 : $i, X6 : $i]:
% 0.21/0.52         (~ (m1_pre_topc @ X5 @ X6) | (l1_pre_topc @ X5) | ~ (l1_pre_topc @ X6))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.21/0.52  thf('18', plain, ((~ (l1_pre_topc @ sk_B) | (l1_pre_topc @ sk_D))),
% 0.21/0.52      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.52  thf('19', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('20', plain, ((l1_pre_topc @ sk_D)),
% 0.21/0.52      inference('demod', [status(thm)], ['18', '19'])).
% 0.21/0.52  thf('21', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.21/0.52      inference('demod', [status(thm)], ['15', '20'])).
% 0.21/0.52  thf('22', plain,
% 0.21/0.52      (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.52         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H))
% 0.21/0.52         <= (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.52               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H)))),
% 0.21/0.52      inference('split', [status(esa)], ['3'])).
% 0.21/0.52  thf('23', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_E @ 
% 0.21/0.52        (k1_zfmisc_1 @ 
% 0.21/0.52         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(t83_tmap_1, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.52             ( l1_pre_topc @ B ) ) =>
% 0.21/0.52           ( ![C:$i]:
% 0.21/0.52             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.21/0.52               ( ![D:$i]:
% 0.21/0.52                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.21/0.52                   ( ![E:$i]:
% 0.21/0.52                     ( ( ( v1_funct_1 @ E ) & 
% 0.21/0.52                         ( v1_funct_2 @
% 0.21/0.52                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.52                         ( m1_subset_1 @
% 0.21/0.52                           E @ 
% 0.21/0.52                           ( k1_zfmisc_1 @
% 0.21/0.52                             ( k2_zfmisc_1 @
% 0.21/0.52                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.52                       ( ( m1_pre_topc @ C @ D ) =>
% 0.21/0.52                         ( ![F:$i]:
% 0.21/0.52                           ( ( m1_subset_1 @
% 0.21/0.52                               F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ D ) ) ) =>
% 0.21/0.52                             ( ![G:$i]:
% 0.21/0.52                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.21/0.52                                 ( ![H:$i]:
% 0.21/0.52                                   ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) ) =>
% 0.21/0.52                                     ( ( ( r1_tarski @ F @ ( u1_struct_0 @ C ) ) & 
% 0.21/0.52                                         ( m1_connsp_2 @ F @ D @ G ) & 
% 0.21/0.52                                         ( ( G ) = ( H ) ) ) =>
% 0.21/0.52                                       ( ( r1_tmap_1 @ D @ B @ E @ G ) <=>
% 0.21/0.52                                         ( r1_tmap_1 @
% 0.21/0.52                                           C @ B @ 
% 0.21/0.52                                           ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ 
% 0.21/0.52                                           H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.52  thf('24', plain,
% 0.21/0.52      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, 
% 0.21/0.52         X27 : $i]:
% 0.21/0.52         ((v2_struct_0 @ X20)
% 0.21/0.52          | ~ (v2_pre_topc @ X20)
% 0.21/0.52          | ~ (l1_pre_topc @ X20)
% 0.21/0.52          | (v2_struct_0 @ X21)
% 0.21/0.52          | ~ (m1_pre_topc @ X21 @ X22)
% 0.21/0.52          | ~ (m1_pre_topc @ X23 @ X21)
% 0.21/0.52          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.21/0.52          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X23))
% 0.21/0.52          | ~ (r1_tmap_1 @ X23 @ X20 @ 
% 0.21/0.52               (k3_tmap_1 @ X22 @ X20 @ X21 @ X23 @ X26) @ X25)
% 0.21/0.52          | (r1_tmap_1 @ X21 @ X20 @ X26 @ X27)
% 0.21/0.52          | ((X27) != (X25))
% 0.21/0.52          | ~ (m1_connsp_2 @ X24 @ X21 @ X27)
% 0.21/0.52          | ~ (r1_tarski @ X24 @ (u1_struct_0 @ X23))
% 0.21/0.52          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X21))
% 0.21/0.52          | ~ (m1_subset_1 @ X26 @ 
% 0.21/0.52               (k1_zfmisc_1 @ 
% 0.21/0.52                (k2_zfmisc_1 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X20))))
% 0.21/0.52          | ~ (v1_funct_2 @ X26 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X20))
% 0.21/0.52          | ~ (v1_funct_1 @ X26)
% 0.21/0.52          | ~ (m1_pre_topc @ X23 @ X22)
% 0.21/0.52          | (v2_struct_0 @ X23)
% 0.21/0.52          | ~ (l1_pre_topc @ X22)
% 0.21/0.52          | ~ (v2_pre_topc @ X22)
% 0.21/0.52          | (v2_struct_0 @ X22))),
% 0.21/0.52      inference('cnf', [status(esa)], [t83_tmap_1])).
% 0.21/0.52  thf('25', plain,
% 0.21/0.52      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.21/0.52         ((v2_struct_0 @ X22)
% 0.21/0.52          | ~ (v2_pre_topc @ X22)
% 0.21/0.52          | ~ (l1_pre_topc @ X22)
% 0.21/0.52          | (v2_struct_0 @ X23)
% 0.21/0.52          | ~ (m1_pre_topc @ X23 @ X22)
% 0.21/0.52          | ~ (v1_funct_1 @ X26)
% 0.21/0.52          | ~ (v1_funct_2 @ X26 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X20))
% 0.21/0.52          | ~ (m1_subset_1 @ X26 @ 
% 0.21/0.52               (k1_zfmisc_1 @ 
% 0.21/0.52                (k2_zfmisc_1 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X20))))
% 0.21/0.52          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X21))
% 0.21/0.52          | ~ (r1_tarski @ X24 @ (u1_struct_0 @ X23))
% 0.21/0.52          | ~ (m1_connsp_2 @ X24 @ X21 @ X25)
% 0.21/0.52          | (r1_tmap_1 @ X21 @ X20 @ X26 @ X25)
% 0.21/0.52          | ~ (r1_tmap_1 @ X23 @ X20 @ 
% 0.21/0.52               (k3_tmap_1 @ X22 @ X20 @ X21 @ X23 @ X26) @ X25)
% 0.21/0.52          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X23))
% 0.21/0.52          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.21/0.52          | ~ (m1_pre_topc @ X23 @ X21)
% 0.21/0.52          | ~ (m1_pre_topc @ X21 @ X22)
% 0.21/0.52          | (v2_struct_0 @ X21)
% 0.21/0.52          | ~ (l1_pre_topc @ X20)
% 0.21/0.52          | ~ (v2_pre_topc @ X20)
% 0.21/0.52          | (v2_struct_0 @ X20))),
% 0.21/0.52      inference('simplify', [status(thm)], ['24'])).
% 0.21/0.52  thf('26', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.52         ((v2_struct_0 @ sk_A)
% 0.21/0.52          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.52          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.52          | (v2_struct_0 @ sk_D)
% 0.21/0.52          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.21/0.52          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.21/0.52          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.21/0.52          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.21/0.52          | ~ (r1_tmap_1 @ X1 @ sk_A @ 
% 0.21/0.52               (k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E) @ X3)
% 0.21/0.52          | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X3)
% 0.21/0.52          | ~ (m1_connsp_2 @ X2 @ sk_D @ X3)
% 0.21/0.52          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X1))
% 0.21/0.52          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_D))
% 0.21/0.52          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))
% 0.21/0.52          | ~ (v1_funct_1 @ sk_E)
% 0.21/0.52          | ~ (m1_pre_topc @ X1 @ X0)
% 0.21/0.52          | (v2_struct_0 @ X1)
% 0.21/0.52          | ~ (l1_pre_topc @ X0)
% 0.21/0.52          | ~ (v2_pre_topc @ X0)
% 0.21/0.52          | (v2_struct_0 @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['23', '25'])).
% 0.21/0.52  thf('27', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('29', plain,
% 0.21/0.52      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('30', plain, ((v1_funct_1 @ sk_E)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('31', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.52         ((v2_struct_0 @ sk_A)
% 0.21/0.52          | (v2_struct_0 @ sk_D)
% 0.21/0.52          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.21/0.52          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.21/0.52          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.21/0.52          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.21/0.52          | ~ (r1_tmap_1 @ X1 @ sk_A @ 
% 0.21/0.52               (k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E) @ X3)
% 0.21/0.52          | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X3)
% 0.21/0.52          | ~ (m1_connsp_2 @ X2 @ sk_D @ X3)
% 0.21/0.52          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X1))
% 0.21/0.52          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_D))
% 0.21/0.52          | ~ (m1_pre_topc @ X1 @ X0)
% 0.21/0.52          | (v2_struct_0 @ X1)
% 0.21/0.52          | ~ (l1_pre_topc @ X0)
% 0.21/0.52          | ~ (v2_pre_topc @ X0)
% 0.21/0.52          | (v2_struct_0 @ X0))),
% 0.21/0.52      inference('demod', [status(thm)], ['26', '27', '28', '29', '30'])).
% 0.21/0.52  thf('32', plain,
% 0.21/0.52      ((![X0 : $i]:
% 0.21/0.52          ((v2_struct_0 @ sk_B)
% 0.21/0.52           | ~ (v2_pre_topc @ sk_B)
% 0.21/0.52           | ~ (l1_pre_topc @ sk_B)
% 0.21/0.52           | (v2_struct_0 @ sk_C)
% 0.21/0.52           | ~ (m1_pre_topc @ sk_C @ sk_B)
% 0.21/0.52           | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D))
% 0.21/0.52           | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C))
% 0.21/0.52           | ~ (m1_connsp_2 @ X0 @ sk_D @ sk_H)
% 0.21/0.52           | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)
% 0.21/0.52           | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_C))
% 0.21/0.52           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.21/0.52           | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.21/0.52           | ~ (m1_pre_topc @ sk_D @ sk_B)
% 0.21/0.52           | (v2_struct_0 @ sk_D)
% 0.21/0.52           | (v2_struct_0 @ sk_A)))
% 0.21/0.52         <= (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.52               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['22', '31'])).
% 0.21/0.52  thf('33', plain, ((v2_pre_topc @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('34', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('35', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('36', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_D))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('37', plain, (((sk_G) = (sk_H))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('38', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D))),
% 0.21/0.52      inference('demod', [status(thm)], ['36', '37'])).
% 0.21/0.52  thf('39', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_C))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('40', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('41', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('42', plain,
% 0.21/0.52      ((![X0 : $i]:
% 0.21/0.52          ((v2_struct_0 @ sk_B)
% 0.21/0.52           | (v2_struct_0 @ sk_C)
% 0.21/0.52           | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C))
% 0.21/0.52           | ~ (m1_connsp_2 @ X0 @ sk_D @ sk_H)
% 0.21/0.52           | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)
% 0.21/0.52           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.21/0.52           | (v2_struct_0 @ sk_D)
% 0.21/0.52           | (v2_struct_0 @ sk_A)))
% 0.21/0.52         <= (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.52               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H)))),
% 0.21/0.52      inference('demod', [status(thm)],
% 0.21/0.52                ['32', '33', '34', '35', '38', '39', '40', '41'])).
% 0.21/0.52  thf('43', plain,
% 0.21/0.52      ((((v2_struct_0 @ sk_A)
% 0.21/0.52         | (v2_struct_0 @ sk_D)
% 0.21/0.52         | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)
% 0.21/0.52         | ~ (m1_connsp_2 @ sk_F @ sk_D @ sk_H)
% 0.21/0.52         | ~ (r1_tarski @ sk_F @ (u1_struct_0 @ sk_C))
% 0.21/0.52         | (v2_struct_0 @ sk_C)
% 0.21/0.52         | (v2_struct_0 @ sk_B)))
% 0.21/0.52         <= (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.52               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['21', '42'])).
% 0.21/0.52  thf('44', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D))),
% 0.21/0.52      inference('demod', [status(thm)], ['36', '37'])).
% 0.21/0.52  thf('45', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.21/0.52      inference('demod', [status(thm)], ['15', '20'])).
% 0.21/0.52  thf(t5_connsp_2, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.52           ( ![C:$i]:
% 0.21/0.52             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.52               ( ( ( v3_pre_topc @ B @ A ) & ( r2_hidden @ C @ B ) ) =>
% 0.21/0.52                 ( m1_connsp_2 @ B @ A @ C ) ) ) ) ) ) ))).
% 0.21/0.52  thf('46', plain,
% 0.21/0.52      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.21/0.52          | ~ (v3_pre_topc @ X14 @ X15)
% 0.21/0.52          | ~ (r2_hidden @ X16 @ X14)
% 0.21/0.52          | (m1_connsp_2 @ X14 @ X15 @ X16)
% 0.21/0.52          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X15))
% 0.21/0.52          | ~ (l1_pre_topc @ X15)
% 0.21/0.52          | ~ (v2_pre_topc @ X15)
% 0.21/0.52          | (v2_struct_0 @ X15))),
% 0.21/0.52      inference('cnf', [status(esa)], [t5_connsp_2])).
% 0.21/0.52  thf('47', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((v2_struct_0 @ sk_D)
% 0.21/0.52          | ~ (v2_pre_topc @ sk_D)
% 0.21/0.52          | ~ (l1_pre_topc @ sk_D)
% 0.21/0.52          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D))
% 0.21/0.52          | (m1_connsp_2 @ sk_F @ sk_D @ X0)
% 0.21/0.52          | ~ (r2_hidden @ X0 @ sk_F)
% 0.21/0.52          | ~ (v3_pre_topc @ sk_F @ sk_D))),
% 0.21/0.52      inference('sup-', [status(thm)], ['45', '46'])).
% 0.21/0.52  thf('48', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(cc1_pre_topc, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.52       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.21/0.52  thf('49', plain,
% 0.21/0.52      (![X3 : $i, X4 : $i]:
% 0.21/0.52         (~ (m1_pre_topc @ X3 @ X4)
% 0.21/0.52          | (v2_pre_topc @ X3)
% 0.21/0.52          | ~ (l1_pre_topc @ X4)
% 0.21/0.52          | ~ (v2_pre_topc @ X4))),
% 0.21/0.52      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.21/0.52  thf('50', plain,
% 0.21/0.52      ((~ (v2_pre_topc @ sk_B) | ~ (l1_pre_topc @ sk_B) | (v2_pre_topc @ sk_D))),
% 0.21/0.52      inference('sup-', [status(thm)], ['48', '49'])).
% 0.21/0.52  thf('51', plain, ((v2_pre_topc @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('52', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('53', plain, ((v2_pre_topc @ sk_D)),
% 0.21/0.52      inference('demod', [status(thm)], ['50', '51', '52'])).
% 0.21/0.52  thf('54', plain, ((l1_pre_topc @ sk_D)),
% 0.21/0.52      inference('demod', [status(thm)], ['18', '19'])).
% 0.21/0.52  thf('55', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('56', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.21/0.52      inference('demod', [status(thm)], ['15', '20'])).
% 0.21/0.52  thf(t33_tops_2, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( l1_pre_topc @ A ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.52           ( ![C:$i]:
% 0.21/0.52             ( ( m1_pre_topc @ C @ A ) =>
% 0.21/0.52               ( ( v3_pre_topc @ B @ A ) =>
% 0.21/0.52                 ( ![D:$i]:
% 0.21/0.52                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) ) =>
% 0.21/0.52                     ( ( ( D ) = ( B ) ) => ( v3_pre_topc @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.52  thf('57', plain,
% 0.21/0.52      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.21/0.52          | ~ (v3_pre_topc @ X10 @ X11)
% 0.21/0.52          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.21/0.52          | (v3_pre_topc @ X12 @ X13)
% 0.21/0.52          | ((X12) != (X10))
% 0.21/0.52          | ~ (m1_pre_topc @ X13 @ X11)
% 0.21/0.52          | ~ (l1_pre_topc @ X11))),
% 0.21/0.52      inference('cnf', [status(esa)], [t33_tops_2])).
% 0.21/0.52  thf('58', plain,
% 0.21/0.52      (![X10 : $i, X11 : $i, X13 : $i]:
% 0.21/0.52         (~ (l1_pre_topc @ X11)
% 0.21/0.52          | ~ (m1_pre_topc @ X13 @ X11)
% 0.21/0.52          | (v3_pre_topc @ X10 @ X13)
% 0.21/0.52          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.21/0.52          | ~ (v3_pre_topc @ X10 @ X11)
% 0.21/0.52          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11))))),
% 0.21/0.52      inference('simplify', [status(thm)], ['57'])).
% 0.21/0.52  thf('59', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.21/0.52          | ~ (v3_pre_topc @ sk_F @ X0)
% 0.21/0.52          | (v3_pre_topc @ sk_F @ sk_D)
% 0.21/0.52          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.21/0.52          | ~ (l1_pre_topc @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['56', '58'])).
% 0.21/0.52  thf('60', plain,
% 0.21/0.52      ((~ (l1_pre_topc @ sk_B)
% 0.21/0.52        | ~ (m1_pre_topc @ sk_D @ sk_B)
% 0.21/0.52        | (v3_pre_topc @ sk_F @ sk_D)
% 0.21/0.52        | ~ (v3_pre_topc @ sk_F @ sk_B))),
% 0.21/0.52      inference('sup-', [status(thm)], ['55', '59'])).
% 0.21/0.52  thf('61', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('62', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('63', plain, ((v3_pre_topc @ sk_F @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('64', plain, ((v3_pre_topc @ sk_F @ sk_D)),
% 0.21/0.52      inference('demod', [status(thm)], ['60', '61', '62', '63'])).
% 0.21/0.52  thf('65', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((v2_struct_0 @ sk_D)
% 0.21/0.52          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D))
% 0.21/0.52          | (m1_connsp_2 @ sk_F @ sk_D @ X0)
% 0.21/0.52          | ~ (r2_hidden @ X0 @ sk_F))),
% 0.21/0.52      inference('demod', [status(thm)], ['47', '53', '54', '64'])).
% 0.21/0.52  thf('66', plain,
% 0.21/0.52      ((~ (r2_hidden @ sk_H @ sk_F)
% 0.21/0.52        | (m1_connsp_2 @ sk_F @ sk_D @ sk_H)
% 0.21/0.52        | (v2_struct_0 @ sk_D))),
% 0.21/0.52      inference('sup-', [status(thm)], ['44', '65'])).
% 0.21/0.52  thf('67', plain, ((r2_hidden @ sk_G @ sk_F)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('68', plain, (((sk_G) = (sk_H))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('69', plain, ((r2_hidden @ sk_H @ sk_F)),
% 0.21/0.52      inference('demod', [status(thm)], ['67', '68'])).
% 0.21/0.52  thf('70', plain,
% 0.21/0.52      (((m1_connsp_2 @ sk_F @ sk_D @ sk_H) | (v2_struct_0 @ sk_D))),
% 0.21/0.52      inference('demod', [status(thm)], ['66', '69'])).
% 0.21/0.52  thf('71', plain, (~ (v2_struct_0 @ sk_D)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('72', plain, ((m1_connsp_2 @ sk_F @ sk_D @ sk_H)),
% 0.21/0.52      inference('clc', [status(thm)], ['70', '71'])).
% 0.21/0.52  thf('73', plain, ((r1_tarski @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('74', plain,
% 0.21/0.52      ((((v2_struct_0 @ sk_A)
% 0.21/0.52         | (v2_struct_0 @ sk_D)
% 0.21/0.52         | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)
% 0.21/0.52         | (v2_struct_0 @ sk_C)
% 0.21/0.52         | (v2_struct_0 @ sk_B)))
% 0.21/0.52         <= (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.52               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H)))),
% 0.21/0.52      inference('demod', [status(thm)], ['43', '72', '73'])).
% 0.21/0.52  thf('75', plain,
% 0.21/0.52      ((~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G))
% 0.21/0.52         <= (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G)))),
% 0.21/0.52      inference('split', [status(esa)], ['7'])).
% 0.21/0.52  thf('76', plain, (((sk_G) = (sk_H))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('77', plain,
% 0.21/0.52      ((~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H))
% 0.21/0.52         <= (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G)))),
% 0.21/0.52      inference('demod', [status(thm)], ['75', '76'])).
% 0.21/0.52  thf('78', plain,
% 0.21/0.52      ((((v2_struct_0 @ sk_B)
% 0.21/0.52         | (v2_struct_0 @ sk_C)
% 0.21/0.52         | (v2_struct_0 @ sk_D)
% 0.21/0.52         | (v2_struct_0 @ sk_A)))
% 0.21/0.52         <= (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G)) & 
% 0.21/0.52             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.52               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['74', '77'])).
% 0.21/0.52  thf('79', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('80', plain,
% 0.21/0.52      ((((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B)))
% 0.21/0.52         <= (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G)) & 
% 0.21/0.52             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.52               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['78', '79'])).
% 0.21/0.52  thf('81', plain, (~ (v2_struct_0 @ sk_D)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('82', plain,
% 0.21/0.52      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C)))
% 0.21/0.52         <= (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G)) & 
% 0.21/0.52             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.52               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H)))),
% 0.21/0.52      inference('clc', [status(thm)], ['80', '81'])).
% 0.21/0.52  thf('83', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('84', plain,
% 0.21/0.52      (((v2_struct_0 @ sk_C))
% 0.21/0.52         <= (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G)) & 
% 0.21/0.52             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.52               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H)))),
% 0.21/0.52      inference('clc', [status(thm)], ['82', '83'])).
% 0.21/0.52  thf('85', plain, (~ (v2_struct_0 @ sk_C)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('86', plain,
% 0.21/0.52      (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G)) | 
% 0.21/0.52       ~
% 0.21/0.52       ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.52         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H))),
% 0.21/0.52      inference('sup-', [status(thm)], ['84', '85'])).
% 0.21/0.52  thf('87', plain,
% 0.21/0.52      (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G)) | 
% 0.21/0.52       ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.52         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H))),
% 0.21/0.52      inference('split', [status(esa)], ['3'])).
% 0.21/0.52  thf('88', plain, (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G))),
% 0.21/0.52      inference('sat_resolution*', [status(thm)], ['8', '86', '87'])).
% 0.21/0.52  thf('89', plain, ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)),
% 0.21/0.52      inference('simpl_trail', [status(thm)], ['6', '88'])).
% 0.21/0.52  thf('90', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.21/0.52      inference('demod', [status(thm)], ['15', '20'])).
% 0.21/0.52  thf('91', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_E @ 
% 0.21/0.52        (k1_zfmisc_1 @ 
% 0.21/0.52         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('92', plain,
% 0.21/0.52      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, 
% 0.21/0.52         X27 : $i]:
% 0.21/0.52         ((v2_struct_0 @ X20)
% 0.21/0.52          | ~ (v2_pre_topc @ X20)
% 0.21/0.52          | ~ (l1_pre_topc @ X20)
% 0.21/0.52          | (v2_struct_0 @ X21)
% 0.21/0.52          | ~ (m1_pre_topc @ X21 @ X22)
% 0.21/0.52          | ~ (m1_pre_topc @ X23 @ X21)
% 0.21/0.52          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.21/0.52          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X23))
% 0.21/0.52          | ~ (r1_tmap_1 @ X21 @ X20 @ X26 @ X27)
% 0.21/0.52          | (r1_tmap_1 @ X23 @ X20 @ 
% 0.21/0.52             (k3_tmap_1 @ X22 @ X20 @ X21 @ X23 @ X26) @ X25)
% 0.21/0.52          | ((X27) != (X25))
% 0.21/0.52          | ~ (m1_connsp_2 @ X24 @ X21 @ X27)
% 0.21/0.52          | ~ (r1_tarski @ X24 @ (u1_struct_0 @ X23))
% 0.21/0.52          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X21))
% 0.21/0.52          | ~ (m1_subset_1 @ X26 @ 
% 0.21/0.52               (k1_zfmisc_1 @ 
% 0.21/0.52                (k2_zfmisc_1 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X20))))
% 0.21/0.52          | ~ (v1_funct_2 @ X26 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X20))
% 0.21/0.52          | ~ (v1_funct_1 @ X26)
% 0.21/0.52          | ~ (m1_pre_topc @ X23 @ X22)
% 0.21/0.52          | (v2_struct_0 @ X23)
% 0.21/0.52          | ~ (l1_pre_topc @ X22)
% 0.21/0.52          | ~ (v2_pre_topc @ X22)
% 0.21/0.52          | (v2_struct_0 @ X22))),
% 0.21/0.52      inference('cnf', [status(esa)], [t83_tmap_1])).
% 0.21/0.52  thf('93', plain,
% 0.21/0.52      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.21/0.52         ((v2_struct_0 @ X22)
% 0.21/0.52          | ~ (v2_pre_topc @ X22)
% 0.21/0.52          | ~ (l1_pre_topc @ X22)
% 0.21/0.52          | (v2_struct_0 @ X23)
% 0.21/0.52          | ~ (m1_pre_topc @ X23 @ X22)
% 0.21/0.52          | ~ (v1_funct_1 @ X26)
% 0.21/0.52          | ~ (v1_funct_2 @ X26 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X20))
% 0.21/0.52          | ~ (m1_subset_1 @ X26 @ 
% 0.21/0.52               (k1_zfmisc_1 @ 
% 0.21/0.52                (k2_zfmisc_1 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X20))))
% 0.21/0.52          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X21))
% 0.21/0.52          | ~ (r1_tarski @ X24 @ (u1_struct_0 @ X23))
% 0.21/0.52          | ~ (m1_connsp_2 @ X24 @ X21 @ X25)
% 0.21/0.52          | (r1_tmap_1 @ X23 @ X20 @ 
% 0.21/0.52             (k3_tmap_1 @ X22 @ X20 @ X21 @ X23 @ X26) @ X25)
% 0.21/0.52          | ~ (r1_tmap_1 @ X21 @ X20 @ X26 @ X25)
% 0.21/0.52          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X23))
% 0.21/0.52          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.21/0.52          | ~ (m1_pre_topc @ X23 @ X21)
% 0.21/0.52          | ~ (m1_pre_topc @ X21 @ X22)
% 0.21/0.52          | (v2_struct_0 @ X21)
% 0.21/0.52          | ~ (l1_pre_topc @ X20)
% 0.21/0.52          | ~ (v2_pre_topc @ X20)
% 0.21/0.52          | (v2_struct_0 @ X20))),
% 0.21/0.52      inference('simplify', [status(thm)], ['92'])).
% 0.21/0.52  thf('94', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.52         ((v2_struct_0 @ sk_A)
% 0.21/0.52          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.52          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.52          | (v2_struct_0 @ sk_D)
% 0.21/0.52          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.21/0.52          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.21/0.52          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.21/0.52          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.21/0.52          | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X3)
% 0.21/0.52          | (r1_tmap_1 @ X1 @ sk_A @ 
% 0.21/0.52             (k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E) @ X3)
% 0.21/0.52          | ~ (m1_connsp_2 @ X2 @ sk_D @ X3)
% 0.21/0.52          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X1))
% 0.21/0.52          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_D))
% 0.21/0.52          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))
% 0.21/0.52          | ~ (v1_funct_1 @ sk_E)
% 0.21/0.52          | ~ (m1_pre_topc @ X1 @ X0)
% 0.21/0.52          | (v2_struct_0 @ X1)
% 0.21/0.52          | ~ (l1_pre_topc @ X0)
% 0.21/0.52          | ~ (v2_pre_topc @ X0)
% 0.21/0.52          | (v2_struct_0 @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['91', '93'])).
% 0.21/0.52  thf('95', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('96', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('97', plain,
% 0.21/0.52      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('98', plain, ((v1_funct_1 @ sk_E)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('99', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.52         ((v2_struct_0 @ sk_A)
% 0.21/0.52          | (v2_struct_0 @ sk_D)
% 0.21/0.52          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.21/0.52          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.21/0.52          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.21/0.52          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.21/0.52          | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X3)
% 0.21/0.52          | (r1_tmap_1 @ X1 @ sk_A @ 
% 0.21/0.52             (k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E) @ X3)
% 0.21/0.52          | ~ (m1_connsp_2 @ X2 @ sk_D @ X3)
% 0.21/0.52          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X1))
% 0.21/0.52          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_D))
% 0.21/0.52          | ~ (m1_pre_topc @ X1 @ X0)
% 0.21/0.52          | (v2_struct_0 @ X1)
% 0.21/0.52          | ~ (l1_pre_topc @ X0)
% 0.21/0.52          | ~ (v2_pre_topc @ X0)
% 0.21/0.52          | (v2_struct_0 @ X0))),
% 0.21/0.52      inference('demod', [status(thm)], ['94', '95', '96', '97', '98'])).
% 0.21/0.52  thf('100', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         ((v2_struct_0 @ X0)
% 0.21/0.52          | ~ (v2_pre_topc @ X0)
% 0.21/0.52          | ~ (l1_pre_topc @ X0)
% 0.21/0.52          | (v2_struct_0 @ X1)
% 0.21/0.52          | ~ (m1_pre_topc @ X1 @ X0)
% 0.21/0.52          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 0.21/0.52          | ~ (r1_tarski @ sk_F @ (u1_struct_0 @ X1))
% 0.21/0.52          | ~ (m1_connsp_2 @ sk_F @ sk_D @ X2)
% 0.21/0.52          | (r1_tmap_1 @ X1 @ sk_A @ 
% 0.21/0.52             (k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E) @ X2)
% 0.21/0.52          | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X2)
% 0.21/0.52          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.21/0.52          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.21/0.52          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.21/0.52          | (v2_struct_0 @ sk_D)
% 0.21/0.52          | (v2_struct_0 @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['90', '99'])).
% 0.21/0.52  thf('101', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((v2_struct_0 @ sk_A)
% 0.21/0.52          | (v2_struct_0 @ sk_D)
% 0.21/0.52          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.21/0.52          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.21/0.52          | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ X1))
% 0.21/0.52          | (r1_tmap_1 @ X1 @ sk_A @ 
% 0.21/0.52             (k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E) @ sk_H)
% 0.21/0.52          | ~ (m1_connsp_2 @ sk_F @ sk_D @ sk_H)
% 0.21/0.52          | ~ (r1_tarski @ sk_F @ (u1_struct_0 @ X1))
% 0.21/0.52          | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D))
% 0.21/0.52          | ~ (m1_pre_topc @ X1 @ X0)
% 0.21/0.52          | (v2_struct_0 @ X1)
% 0.21/0.52          | ~ (l1_pre_topc @ X0)
% 0.21/0.52          | ~ (v2_pre_topc @ X0)
% 0.21/0.52          | (v2_struct_0 @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['89', '100'])).
% 0.21/0.52  thf('102', plain, ((m1_connsp_2 @ sk_F @ sk_D @ sk_H)),
% 0.21/0.52      inference('clc', [status(thm)], ['70', '71'])).
% 0.21/0.52  thf('103', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D))),
% 0.21/0.52      inference('demod', [status(thm)], ['36', '37'])).
% 0.21/0.52  thf('104', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((v2_struct_0 @ sk_A)
% 0.21/0.52          | (v2_struct_0 @ sk_D)
% 0.21/0.52          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.21/0.52          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.21/0.52          | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ X1))
% 0.21/0.52          | (r1_tmap_1 @ X1 @ sk_A @ 
% 0.21/0.52             (k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E) @ sk_H)
% 0.21/0.52          | ~ (r1_tarski @ sk_F @ (u1_struct_0 @ X1))
% 0.21/0.52          | ~ (m1_pre_topc @ X1 @ X0)
% 0.21/0.52          | (v2_struct_0 @ X1)
% 0.21/0.52          | ~ (l1_pre_topc @ X0)
% 0.21/0.52          | ~ (v2_pre_topc @ X0)
% 0.21/0.52          | (v2_struct_0 @ X0))),
% 0.21/0.52      inference('demod', [status(thm)], ['101', '102', '103'])).
% 0.21/0.52  thf('105', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((v2_struct_0 @ X0)
% 0.21/0.52          | ~ (v2_pre_topc @ X0)
% 0.21/0.52          | ~ (l1_pre_topc @ X0)
% 0.21/0.52          | (v2_struct_0 @ sk_C)
% 0.21/0.52          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.21/0.52          | ~ (r1_tarski @ sk_F @ (u1_struct_0 @ sk_C))
% 0.21/0.52          | (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.52             (k3_tmap_1 @ X0 @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H)
% 0.21/0.52          | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.21/0.52          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.21/0.52          | (v2_struct_0 @ sk_D)
% 0.21/0.52          | (v2_struct_0 @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['2', '104'])).
% 0.21/0.52  thf('106', plain, ((r1_tarski @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('107', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('108', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((v2_struct_0 @ X0)
% 0.21/0.52          | ~ (v2_pre_topc @ X0)
% 0.21/0.52          | ~ (l1_pre_topc @ X0)
% 0.21/0.52          | (v2_struct_0 @ sk_C)
% 0.21/0.52          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.21/0.52          | (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.52             (k3_tmap_1 @ X0 @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H)
% 0.21/0.52          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.21/0.52          | (v2_struct_0 @ sk_D)
% 0.21/0.52          | (v2_struct_0 @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['105', '106', '107'])).
% 0.21/0.52  thf('109', plain,
% 0.21/0.52      (((v2_struct_0 @ sk_A)
% 0.21/0.52        | (v2_struct_0 @ sk_D)
% 0.21/0.52        | ~ (m1_pre_topc @ sk_D @ sk_B)
% 0.21/0.52        | (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.52           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H)
% 0.21/0.52        | (v2_struct_0 @ sk_C)
% 0.21/0.52        | ~ (l1_pre_topc @ sk_B)
% 0.21/0.52        | ~ (v2_pre_topc @ sk_B)
% 0.21/0.52        | (v2_struct_0 @ sk_B))),
% 0.21/0.52      inference('sup-', [status(thm)], ['1', '108'])).
% 0.21/0.52  thf('110', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('111', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('112', plain, ((v2_pre_topc @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('113', plain,
% 0.21/0.52      (((v2_struct_0 @ sk_A)
% 0.21/0.52        | (v2_struct_0 @ sk_D)
% 0.21/0.52        | (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.52           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H)
% 0.21/0.52        | (v2_struct_0 @ sk_C)
% 0.21/0.52        | (v2_struct_0 @ sk_B))),
% 0.21/0.52      inference('demod', [status(thm)], ['109', '110', '111', '112'])).
% 0.21/0.52  thf('114', plain,
% 0.21/0.52      ((~ (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.52           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H))
% 0.21/0.52         <= (~
% 0.21/0.52             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.52               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H)))),
% 0.21/0.52      inference('split', [status(esa)], ['7'])).
% 0.21/0.52  thf('115', plain,
% 0.21/0.52      (~
% 0.21/0.52       ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.52         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H))),
% 0.21/0.52      inference('sat_resolution*', [status(thm)], ['8', '86'])).
% 0.21/0.52  thf('116', plain,
% 0.21/0.52      (~ (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.52          (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H)),
% 0.21/0.52      inference('simpl_trail', [status(thm)], ['114', '115'])).
% 0.21/0.52  thf('117', plain,
% 0.21/0.52      (((v2_struct_0 @ sk_B)
% 0.21/0.52        | (v2_struct_0 @ sk_C)
% 0.21/0.52        | (v2_struct_0 @ sk_D)
% 0.21/0.52        | (v2_struct_0 @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['113', '116'])).
% 0.21/0.52  thf('118', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('119', plain,
% 0.21/0.52      (((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B))),
% 0.21/0.52      inference('sup-', [status(thm)], ['117', '118'])).
% 0.21/0.52  thf('120', plain, (~ (v2_struct_0 @ sk_D)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('121', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C))),
% 0.21/0.52      inference('clc', [status(thm)], ['119', '120'])).
% 0.21/0.52  thf('122', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('123', plain, ((v2_struct_0 @ sk_C)),
% 0.21/0.52      inference('clc', [status(thm)], ['121', '122'])).
% 0.21/0.52  thf('124', plain, ($false), inference('demod', [status(thm)], ['0', '123'])).
% 0.21/0.52  
% 0.21/0.52  % SZS output end Refutation
% 0.21/0.52  
% 0.21/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
