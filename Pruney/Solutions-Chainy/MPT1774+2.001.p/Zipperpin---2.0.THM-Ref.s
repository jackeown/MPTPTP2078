%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6lxdX2JcXv

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:16 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  198 ( 493 expanded)
%              Number of leaves         :   38 ( 154 expanded)
%              Depth                    :   30
%              Number of atoms          : 2419 (17246 expanded)
%              Number of equality atoms :   16 ( 202 expanded)
%              Maximal formula depth    :   32 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

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

thf('0',plain,
    ( ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_H )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,
    ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_H )
    | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_H )
    | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H )
   <= ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H ) ),
    inference('sup-',[status(thm)],['3','7'])).

thf('9',plain,
    ( ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_H )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_H )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H ) ),
    inference(split,[status(esa)],['11'])).

thf('13',plain,
    ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_H )
    | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G )
   <= ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G ) ),
    inference(split,[status(esa)],['13'])).

thf('15',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H )
   <= ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G ) ),
    inference('sup-',[status(thm)],['12','16'])).

thf('18',plain,
    ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_H )
    | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H ) ),
    inference(split,[status(esa)],['6'])).

thf('19',plain,(
    m1_pre_topc @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('22',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ) ) ),
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

thf('23',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( v2_struct_0 @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ~ ( l1_pre_topc @ X30 )
      | ( v2_struct_0 @ X31 )
      | ~ ( m1_pre_topc @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X34 ) )
      | ~ ( m1_pre_topc @ X31 @ X34 )
      | ~ ( r1_tmap_1 @ X34 @ X30 @ X35 @ X33 )
      | ( X33 != X36 )
      | ( r1_tmap_1 @ X31 @ X30 @ ( k3_tmap_1 @ X32 @ X30 @ X34 @ X31 @ X35 ) @ X36 )
      | ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ X31 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X30 ) ) ) )
      | ~ ( v1_funct_2 @ X35 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X30 ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( m1_pre_topc @ X34 @ X32 )
      | ( v2_struct_0 @ X34 )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t81_tmap_1])).

thf('24',plain,(
    ! [X30: $i,X31: $i,X32: $i,X34: $i,X35: $i,X36: $i] :
      ( ( v2_struct_0 @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ~ ( l1_pre_topc @ X32 )
      | ( v2_struct_0 @ X34 )
      | ~ ( m1_pre_topc @ X34 @ X32 )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_funct_2 @ X35 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X30 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X30 ) ) ) )
      | ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ X31 ) )
      | ( r1_tmap_1 @ X31 @ X30 @ ( k3_tmap_1 @ X32 @ X30 @ X34 @ X31 @ X35 ) @ X36 )
      | ~ ( r1_tmap_1 @ X34 @ X30 @ X35 @ X36 )
      | ~ ( m1_pre_topc @ X31 @ X34 )
      | ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ X34 ) )
      | ~ ( m1_pre_topc @ X31 @ X32 )
      | ( v2_struct_0 @ X31 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X2 )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k3_tmap_1 @ X1 @ sk_A @ sk_D @ X0 @ sk_E ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf('26',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X2 )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k3_tmap_1 @ X1 @ sk_A @ sk_D @ X0 @ sk_E ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['25','26','27','28','29'])).

thf('31',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ( v2_struct_0 @ sk_D )
        | ~ ( m1_pre_topc @ sk_D @ X0 )
        | ~ ( m1_subset_1 @ sk_H @ ( u1_struct_0 @ X1 ) )
        | ( r1_tmap_1 @ X1 @ sk_A @ ( k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E ) @ sk_H )
        | ~ ( m1_pre_topc @ X1 @ sk_D )
        | ~ ( m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_D ) )
        | ~ ( m1_pre_topc @ X1 @ X0 )
        | ( v2_struct_0 @ X1 )
        | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G ) ),
    inference('sup-',[status(thm)],['21','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ( v2_struct_0 @ sk_D )
        | ~ ( m1_pre_topc @ sk_D @ X0 )
        | ~ ( m1_subset_1 @ sk_H @ ( u1_struct_0 @ X1 ) )
        | ( r1_tmap_1 @ X1 @ sk_A @ ( k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E ) @ sk_H )
        | ~ ( m1_pre_topc @ X1 @ sk_D )
        | ~ ( m1_pre_topc @ X1 @ X0 )
        | ( v2_struct_0 @ X1 )
        | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G ) ),
    inference(demod,[status(thm)],['31','34'])).

thf('36',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C_1 )
        | ~ ( m1_pre_topc @ sk_C_1 @ X0 )
        | ~ ( m1_pre_topc @ sk_C_1 @ sk_D )
        | ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ X0 @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_H )
        | ~ ( m1_pre_topc @ sk_D @ X0 )
        | ( v2_struct_0 @ sk_D )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 ) )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G ) ),
    inference('sup-',[status(thm)],['20','35'])).

thf('37',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C_1 )
        | ~ ( m1_pre_topc @ sk_C_1 @ X0 )
        | ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ X0 @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_H )
        | ~ ( m1_pre_topc @ sk_D @ X0 )
        | ( v2_struct_0 @ sk_D )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 ) )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ sk_B )
      | ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_H )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G ) ),
    inference('sup-',[status(thm)],['19','38'])).

thf('40',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_H )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G ) ),
    inference(demod,[status(thm)],['39','40','41','42'])).

thf('44',plain,
    ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_H )
   <= ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_H ) ),
    inference(split,[status(esa)],['13'])).

thf('45',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_H )
      & ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C_1 ) )
   <= ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_H )
      & ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_H )
      & ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( v2_struct_0 @ sk_D )
   <= ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_H )
      & ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G ) ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G )
    | ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_H ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_H )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H ) ),
    inference(split,[status(esa)],['11'])).

thf('55',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('56',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('57',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['56'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('58',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('59',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf(t39_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
             => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('60',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_pre_topc @ X14 @ X15 )
      | ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t39_pre_topc])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X1 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( m1_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
    | ~ ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['55','61'])).

thf('63',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('64',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_pre_topc @ X12 @ X13 )
      | ( l1_pre_topc @ X12 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('65',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['62','67'])).

thf('69',plain,
    ( ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_H )
   <= ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_H ) ),
    inference(split,[status(esa)],['0'])).

thf('70',plain,(
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

thf('71',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ( v2_struct_0 @ X37 )
      | ~ ( v2_pre_topc @ X37 )
      | ~ ( l1_pre_topc @ X37 )
      | ( v2_struct_0 @ X38 )
      | ~ ( m1_pre_topc @ X38 @ X39 )
      | ~ ( m1_pre_topc @ X40 @ X38 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ~ ( m1_subset_1 @ X42 @ ( u1_struct_0 @ X40 ) )
      | ~ ( r1_tmap_1 @ X40 @ X37 @ ( k3_tmap_1 @ X39 @ X37 @ X38 @ X40 @ X43 ) @ X42 )
      | ( r1_tmap_1 @ X38 @ X37 @ X43 @ X44 )
      | ( X44 != X42 )
      | ~ ( m1_connsp_2 @ X41 @ X38 @ X44 )
      | ~ ( r1_tarski @ X41 @ ( u1_struct_0 @ X40 ) )
      | ~ ( m1_subset_1 @ X44 @ ( u1_struct_0 @ X38 ) )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X38 ) @ ( u1_struct_0 @ X37 ) ) ) )
      | ~ ( v1_funct_2 @ X43 @ ( u1_struct_0 @ X38 ) @ ( u1_struct_0 @ X37 ) )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( m1_pre_topc @ X40 @ X39 )
      | ( v2_struct_0 @ X40 )
      | ~ ( l1_pre_topc @ X39 )
      | ~ ( v2_pre_topc @ X39 )
      | ( v2_struct_0 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t83_tmap_1])).

thf('72',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ( v2_struct_0 @ X39 )
      | ~ ( v2_pre_topc @ X39 )
      | ~ ( l1_pre_topc @ X39 )
      | ( v2_struct_0 @ X40 )
      | ~ ( m1_pre_topc @ X40 @ X39 )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_2 @ X43 @ ( u1_struct_0 @ X38 ) @ ( u1_struct_0 @ X37 ) )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X38 ) @ ( u1_struct_0 @ X37 ) ) ) )
      | ~ ( m1_subset_1 @ X42 @ ( u1_struct_0 @ X38 ) )
      | ~ ( r1_tarski @ X41 @ ( u1_struct_0 @ X40 ) )
      | ~ ( m1_connsp_2 @ X41 @ X38 @ X42 )
      | ( r1_tmap_1 @ X38 @ X37 @ X43 @ X42 )
      | ~ ( r1_tmap_1 @ X40 @ X37 @ ( k3_tmap_1 @ X39 @ X37 @ X38 @ X40 @ X43 ) @ X42 )
      | ~ ( m1_subset_1 @ X42 @ ( u1_struct_0 @ X40 ) )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ~ ( m1_pre_topc @ X40 @ X38 )
      | ~ ( m1_pre_topc @ X38 @ X39 )
      | ( v2_struct_0 @ X38 )
      | ~ ( l1_pre_topc @ X37 )
      | ~ ( v2_pre_topc @ X37 )
      | ( v2_struct_0 @ X37 ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
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
    inference('sup-',[status(thm)],['70','72'])).

thf('74',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
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
    inference(demod,[status(thm)],['73','74','75','76','77'])).

thf('79',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ~ ( v2_pre_topc @ sk_B )
        | ~ ( l1_pre_topc @ sk_B )
        | ( v2_struct_0 @ sk_C_1 )
        | ~ ( m1_pre_topc @ sk_C_1 @ sk_B )
        | ~ ( m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_D ) )
        | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
        | ~ ( m1_connsp_2 @ X0 @ sk_D @ sk_H )
        | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H )
        | ~ ( m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_C_1 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
        | ~ ( m1_pre_topc @ sk_C_1 @ sk_D )
        | ~ ( m1_pre_topc @ sk_D @ sk_B )
        | ( v2_struct_0 @ sk_D )
        | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_H ) ),
    inference('sup-',[status(thm)],['69','78'])).

thf('80',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    m1_pre_topc @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('84',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_C_1 )
        | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
        | ~ ( m1_connsp_2 @ X0 @ sk_D @ sk_H )
        | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
        | ( v2_struct_0 @ sk_D )
        | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_H ) ),
    inference(demod,[status(thm)],['79','80','81','82','83','84','85','86'])).

thf('88',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H )
      | ~ ( m1_connsp_2 @ ( u1_struct_0 @ sk_C_1 ) @ sk_D @ sk_H )
      | ~ ( r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_C_1 ) )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_H ) ),
    inference('sup-',[status(thm)],['68','87'])).

thf('89',plain,(
    r2_hidden @ sk_G @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    r2_hidden @ sk_H @ sk_F ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['62','67'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('93',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('94',plain,(
    r1_tarski @ sk_F @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_F @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_F ) @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['93','96'])).

thf('98',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['62','67'])).

thf('99',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('100',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_F @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_F ) @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['97','102'])).

thf('104',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('105',plain,
    ( ( r1_tarski @ sk_F @ ( u1_struct_0 @ sk_D ) )
    | ( r1_tarski @ sk_F @ ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    r1_tarski @ sk_F @ ( u1_struct_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['105'])).

thf('107',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('108',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf(t56_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v3_pre_topc @ B @ A )
                  & ( r1_tarski @ B @ C ) )
               => ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('109',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v3_pre_topc @ X17 @ X18 )
      | ~ ( r1_tarski @ X17 @ X19 )
      | ( r1_tarski @ X17 @ ( k1_tops_1 @ X18 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t56_tops_1])).

thf('110',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_D )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
      | ( r1_tarski @ sk_F @ ( k1_tops_1 @ sk_D @ X0 ) )
      | ~ ( r1_tarski @ sk_F @ X0 )
      | ~ ( v3_pre_topc @ sk_F @ sk_D ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['65','66'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
      | ( r1_tarski @ sk_F @ ( k1_tops_1 @ sk_D @ X0 ) )
      | ~ ( r1_tarski @ sk_F @ X0 )
      | ~ ( v3_pre_topc @ sk_F @ sk_D ) ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

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

thf('115',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v3_pre_topc @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( v3_pre_topc @ X22 @ X23 )
      | ( X22 != X20 )
      | ~ ( m1_pre_topc @ X23 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t33_tops_2])).

thf('116',plain,(
    ! [X20: $i,X21: $i,X23: $i] :
      ( ~ ( l1_pre_topc @ X21 )
      | ~ ( m1_pre_topc @ X23 @ X21 )
      | ( v3_pre_topc @ X20 @ X23 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( v3_pre_topc @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) ) ) ),
    inference(simplify,[status(thm)],['115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v3_pre_topc @ sk_F @ X0 )
      | ( v3_pre_topc @ sk_F @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['114','116'])).

thf('118',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ~ ( m1_pre_topc @ sk_D @ sk_B )
    | ( v3_pre_topc @ sk_F @ sk_D )
    | ~ ( v3_pre_topc @ sk_F @ sk_B ) ),
    inference('sup-',[status(thm)],['113','117'])).

thf('119',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    v3_pre_topc @ sk_F @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    v3_pre_topc @ sk_F @ sk_D ),
    inference(demod,[status(thm)],['118','119','120','121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
      | ( r1_tarski @ sk_F @ ( k1_tops_1 @ sk_D @ X0 ) )
      | ~ ( r1_tarski @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['112','122'])).

thf('124',plain,
    ( ~ ( r1_tarski @ sk_F @ ( u1_struct_0 @ sk_C_1 ) )
    | ( r1_tarski @ sk_F @ ( k1_tops_1 @ sk_D @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['92','123'])).

thf('125',plain,(
    r1_tarski @ sk_F @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    r1_tarski @ sk_F @ ( k1_tops_1 @ sk_D @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_D @ ( u1_struct_0 @ sk_C_1 ) ) )
      | ~ ( r2_hidden @ X0 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    r2_hidden @ sk_H @ ( k1_tops_1 @ sk_D @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['91','128'])).

thf('130',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['62','67'])).

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

thf('131',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X25 ) )
      | ~ ( r2_hidden @ X24 @ ( k1_tops_1 @ X25 @ X26 ) )
      | ( m1_connsp_2 @ X26 @ X25 @ X24 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ~ ( l1_pre_topc @ sk_D )
      | ( m1_connsp_2 @ ( u1_struct_0 @ sk_C_1 ) @ sk_D @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_D @ ( u1_struct_0 @ sk_C_1 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('134',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X10 @ X11 )
      | ( v2_pre_topc @ X10 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('135',plain,
    ( ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['135','136','137'])).

thf('139',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['65','66'])).

thf('140',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( m1_connsp_2 @ ( u1_struct_0 @ sk_C_1 ) @ sk_D @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_D @ ( u1_struct_0 @ sk_C_1 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['132','138','139'])).

thf('141',plain,
    ( ~ ( m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_D ) )
    | ( m1_connsp_2 @ ( u1_struct_0 @ sk_C_1 ) @ sk_D @ sk_H )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['129','140'])).

thf('142',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('143',plain,
    ( ( m1_connsp_2 @ ( u1_struct_0 @ sk_C_1 ) @ sk_D @ sk_H )
    | ( v2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['141','142'])).

thf('144',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    m1_connsp_2 @ ( u1_struct_0 @ sk_C_1 ) @ sk_D @ sk_H ),
    inference(clc,[status(thm)],['143','144'])).

thf('146',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['56'])).

thf('147',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_H ) ),
    inference(demod,[status(thm)],['88','145','146'])).

thf('148',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H )
   <= ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('149',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G )
      & ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_H ) ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G )
      & ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_H ) ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C_1 ) )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G )
      & ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_H ) ) ),
    inference(clc,[status(thm)],['151','152'])).

thf('154',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,
    ( ( v2_struct_0 @ sk_C_1 )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G )
      & ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_H ) ) ),
    inference(clc,[status(thm)],['153','154'])).

thf('156',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,
    ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_H )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['8','17','18','53','54','157'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6lxdX2JcXv
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:43:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 0.20/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.55  % Solved by: fo/fo7.sh
% 0.20/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.55  % done 282 iterations in 0.098s
% 0.20/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.55  % SZS output start Refutation
% 0.20/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.55  thf(sk_F_type, type, sk_F: $i).
% 0.20/0.55  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.55  thf(sk_H_type, type, sk_H: $i).
% 0.20/0.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.55  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.20/0.55  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.55  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.20/0.55  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.20/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.55  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.20/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.55  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.20/0.55  thf(sk_E_type, type, sk_E: $i).
% 0.20/0.55  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.55  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.55  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.55  thf(sk_G_type, type, sk_G: $i).
% 0.20/0.55  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.55  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.20/0.55  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.55  thf(t85_tmap_1, conjecture,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.55       ( ![B:$i]:
% 0.20/0.55         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.55             ( l1_pre_topc @ B ) ) =>
% 0.20/0.55           ( ![C:$i]:
% 0.20/0.55             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.20/0.55               ( ![D:$i]:
% 0.20/0.55                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.20/0.55                   ( ![E:$i]:
% 0.20/0.55                     ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.55                         ( v1_funct_2 @
% 0.20/0.55                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.55                         ( m1_subset_1 @
% 0.20/0.55                           E @ 
% 0.20/0.55                           ( k1_zfmisc_1 @
% 0.20/0.55                             ( k2_zfmisc_1 @
% 0.20/0.55                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.20/0.55                       ( ( m1_pre_topc @ C @ D ) =>
% 0.20/0.55                         ( ![F:$i]:
% 0.20/0.55                           ( ( m1_subset_1 @
% 0.20/0.55                               F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.20/0.55                             ( ![G:$i]:
% 0.20/0.55                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.20/0.55                                 ( ![H:$i]:
% 0.20/0.55                                   ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) ) =>
% 0.20/0.55                                     ( ( ( v3_pre_topc @ F @ B ) & 
% 0.20/0.55                                         ( r2_hidden @ G @ F ) & 
% 0.20/0.55                                         ( r1_tarski @ F @ ( u1_struct_0 @ C ) ) & 
% 0.20/0.55                                         ( ( G ) = ( H ) ) ) =>
% 0.20/0.55                                       ( ( r1_tmap_1 @ D @ A @ E @ G ) <=>
% 0.20/0.55                                         ( r1_tmap_1 @
% 0.20/0.55                                           C @ A @ 
% 0.20/0.55                                           ( k3_tmap_1 @ B @ A @ D @ C @ E ) @ 
% 0.20/0.55                                           H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.55    (~( ![A:$i]:
% 0.20/0.55        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.55            ( l1_pre_topc @ A ) ) =>
% 0.20/0.55          ( ![B:$i]:
% 0.20/0.55            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.55                ( l1_pre_topc @ B ) ) =>
% 0.20/0.55              ( ![C:$i]:
% 0.20/0.55                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.20/0.55                  ( ![D:$i]:
% 0.20/0.55                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.20/0.55                      ( ![E:$i]:
% 0.20/0.55                        ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.55                            ( v1_funct_2 @
% 0.20/0.55                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.55                            ( m1_subset_1 @
% 0.20/0.55                              E @ 
% 0.20/0.55                              ( k1_zfmisc_1 @
% 0.20/0.55                                ( k2_zfmisc_1 @
% 0.20/0.55                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.20/0.55                          ( ( m1_pre_topc @ C @ D ) =>
% 0.20/0.55                            ( ![F:$i]:
% 0.20/0.55                              ( ( m1_subset_1 @
% 0.20/0.55                                  F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.20/0.55                                ( ![G:$i]:
% 0.20/0.55                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.20/0.55                                    ( ![H:$i]:
% 0.20/0.55                                      ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) ) =>
% 0.20/0.55                                        ( ( ( v3_pre_topc @ F @ B ) & 
% 0.20/0.55                                            ( r2_hidden @ G @ F ) & 
% 0.20/0.55                                            ( r1_tarski @
% 0.20/0.55                                              F @ ( u1_struct_0 @ C ) ) & 
% 0.20/0.55                                            ( ( G ) = ( H ) ) ) =>
% 0.20/0.55                                          ( ( r1_tmap_1 @ D @ A @ E @ G ) <=>
% 0.20/0.55                                            ( r1_tmap_1 @
% 0.20/0.55                                              C @ A @ 
% 0.20/0.55                                              ( k3_tmap_1 @ B @ A @ D @ C @ E ) @ 
% 0.20/0.55                                              H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.55    inference('cnf.neg', [status(esa)], [t85_tmap_1])).
% 0.20/0.55  thf('0', plain,
% 0.20/0.55      (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.55         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H)
% 0.20/0.55        | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('1', plain,
% 0.20/0.55      (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G))
% 0.20/0.55         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G)))),
% 0.20/0.55      inference('split', [status(esa)], ['0'])).
% 0.20/0.55  thf('2', plain, (((sk_G) = (sk_H))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('3', plain,
% 0.20/0.55      (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H))
% 0.20/0.55         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G)))),
% 0.20/0.55      inference('demod', [status(thm)], ['1', '2'])).
% 0.20/0.55  thf('4', plain,
% 0.20/0.55      ((~ (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.55           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H)
% 0.20/0.55        | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('5', plain, (((sk_G) = (sk_H))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('6', plain,
% 0.20/0.55      ((~ (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.55           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H)
% 0.20/0.55        | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H))),
% 0.20/0.55      inference('demod', [status(thm)], ['4', '5'])).
% 0.20/0.55  thf('7', plain,
% 0.20/0.55      ((~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H))
% 0.20/0.55         <= (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)))),
% 0.20/0.55      inference('split', [status(esa)], ['6'])).
% 0.20/0.55  thf('8', plain,
% 0.20/0.55      (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G)) | 
% 0.20/0.55       ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H))),
% 0.20/0.55      inference('sup-', [status(thm)], ['3', '7'])).
% 0.20/0.55  thf('9', plain,
% 0.20/0.55      (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.55         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H)
% 0.20/0.55        | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('10', plain, (((sk_G) = (sk_H))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('11', plain,
% 0.20/0.55      (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.55         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H)
% 0.20/0.55        | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H))),
% 0.20/0.55      inference('demod', [status(thm)], ['9', '10'])).
% 0.20/0.55  thf('12', plain,
% 0.20/0.55      (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H))
% 0.20/0.55         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)))),
% 0.20/0.55      inference('split', [status(esa)], ['11'])).
% 0.20/0.55  thf('13', plain,
% 0.20/0.55      ((~ (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.55           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H)
% 0.20/0.55        | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('14', plain,
% 0.20/0.55      ((~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G))
% 0.20/0.55         <= (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G)))),
% 0.20/0.55      inference('split', [status(esa)], ['13'])).
% 0.20/0.55  thf('15', plain, (((sk_G) = (sk_H))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('16', plain,
% 0.20/0.55      ((~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H))
% 0.20/0.55         <= (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G)))),
% 0.20/0.55      inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.55  thf('17', plain,
% 0.20/0.55      (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)) | 
% 0.20/0.55       ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G))),
% 0.20/0.55      inference('sup-', [status(thm)], ['12', '16'])).
% 0.20/0.55  thf('18', plain,
% 0.20/0.55      (~
% 0.20/0.55       ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.55         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H)) | 
% 0.20/0.55       ~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H))),
% 0.20/0.55      inference('split', [status(esa)], ['6'])).
% 0.20/0.55  thf('19', plain, ((m1_pre_topc @ sk_C_1 @ sk_B)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('20', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_C_1))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('21', plain,
% 0.20/0.55      (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H))
% 0.20/0.55         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G)))),
% 0.20/0.55      inference('demod', [status(thm)], ['1', '2'])).
% 0.20/0.55  thf('22', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_E @ 
% 0.20/0.55        (k1_zfmisc_1 @ 
% 0.20/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(t81_tmap_1, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.55       ( ![B:$i]:
% 0.20/0.55         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.55             ( l1_pre_topc @ B ) ) =>
% 0.20/0.55           ( ![C:$i]:
% 0.20/0.55             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.55               ( ![D:$i]:
% 0.20/0.55                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.20/0.55                   ( ![E:$i]:
% 0.20/0.55                     ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.55                         ( v1_funct_2 @
% 0.20/0.55                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.55                         ( m1_subset_1 @
% 0.20/0.55                           E @ 
% 0.20/0.55                           ( k1_zfmisc_1 @
% 0.20/0.55                             ( k2_zfmisc_1 @
% 0.20/0.55                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.55                       ( ![F:$i]:
% 0.20/0.55                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ C ) ) =>
% 0.20/0.55                           ( ![G:$i]:
% 0.20/0.55                             ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.20/0.55                               ( ( ( ( F ) = ( G ) ) & 
% 0.20/0.55                                   ( m1_pre_topc @ D @ C ) & 
% 0.20/0.55                                   ( r1_tmap_1 @ C @ B @ E @ F ) ) =>
% 0.20/0.55                                 ( r1_tmap_1 @
% 0.20/0.55                                   D @ B @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ 
% 0.20/0.55                                   G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.55  thf('23', plain,
% 0.20/0.55      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.20/0.55         ((v2_struct_0 @ X30)
% 0.20/0.55          | ~ (v2_pre_topc @ X30)
% 0.20/0.55          | ~ (l1_pre_topc @ X30)
% 0.20/0.55          | (v2_struct_0 @ X31)
% 0.20/0.55          | ~ (m1_pre_topc @ X31 @ X32)
% 0.20/0.55          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X34))
% 0.20/0.55          | ~ (m1_pre_topc @ X31 @ X34)
% 0.20/0.55          | ~ (r1_tmap_1 @ X34 @ X30 @ X35 @ X33)
% 0.20/0.55          | ((X33) != (X36))
% 0.20/0.55          | (r1_tmap_1 @ X31 @ X30 @ 
% 0.20/0.55             (k3_tmap_1 @ X32 @ X30 @ X34 @ X31 @ X35) @ X36)
% 0.20/0.55          | ~ (m1_subset_1 @ X36 @ (u1_struct_0 @ X31))
% 0.20/0.55          | ~ (m1_subset_1 @ X35 @ 
% 0.20/0.55               (k1_zfmisc_1 @ 
% 0.20/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X30))))
% 0.20/0.55          | ~ (v1_funct_2 @ X35 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X30))
% 0.20/0.55          | ~ (v1_funct_1 @ X35)
% 0.20/0.55          | ~ (m1_pre_topc @ X34 @ X32)
% 0.20/0.55          | (v2_struct_0 @ X34)
% 0.20/0.55          | ~ (l1_pre_topc @ X32)
% 0.20/0.55          | ~ (v2_pre_topc @ X32)
% 0.20/0.55          | (v2_struct_0 @ X32))),
% 0.20/0.55      inference('cnf', [status(esa)], [t81_tmap_1])).
% 0.20/0.55  thf('24', plain,
% 0.20/0.55      (![X30 : $i, X31 : $i, X32 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.20/0.55         ((v2_struct_0 @ X32)
% 0.20/0.55          | ~ (v2_pre_topc @ X32)
% 0.20/0.55          | ~ (l1_pre_topc @ X32)
% 0.20/0.55          | (v2_struct_0 @ X34)
% 0.20/0.55          | ~ (m1_pre_topc @ X34 @ X32)
% 0.20/0.55          | ~ (v1_funct_1 @ X35)
% 0.20/0.55          | ~ (v1_funct_2 @ X35 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X30))
% 0.20/0.55          | ~ (m1_subset_1 @ X35 @ 
% 0.20/0.55               (k1_zfmisc_1 @ 
% 0.20/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X30))))
% 0.20/0.55          | ~ (m1_subset_1 @ X36 @ (u1_struct_0 @ X31))
% 0.20/0.55          | (r1_tmap_1 @ X31 @ X30 @ 
% 0.20/0.55             (k3_tmap_1 @ X32 @ X30 @ X34 @ X31 @ X35) @ X36)
% 0.20/0.55          | ~ (r1_tmap_1 @ X34 @ X30 @ X35 @ X36)
% 0.20/0.55          | ~ (m1_pre_topc @ X31 @ X34)
% 0.20/0.55          | ~ (m1_subset_1 @ X36 @ (u1_struct_0 @ X34))
% 0.20/0.55          | ~ (m1_pre_topc @ X31 @ X32)
% 0.20/0.55          | (v2_struct_0 @ X31)
% 0.20/0.55          | ~ (l1_pre_topc @ X30)
% 0.20/0.55          | ~ (v2_pre_topc @ X30)
% 0.20/0.55          | (v2_struct_0 @ X30))),
% 0.20/0.55      inference('simplify', [status(thm)], ['23'])).
% 0.20/0.55  thf('25', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.55         ((v2_struct_0 @ sk_A)
% 0.20/0.55          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.55          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.55          | (v2_struct_0 @ X0)
% 0.20/0.55          | ~ (m1_pre_topc @ X0 @ X1)
% 0.20/0.55          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 0.20/0.55          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.20/0.55          | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X2)
% 0.20/0.55          | (r1_tmap_1 @ X0 @ sk_A @ 
% 0.20/0.55             (k3_tmap_1 @ X1 @ sk_A @ sk_D @ X0 @ sk_E) @ X2)
% 0.20/0.55          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.20/0.55          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))
% 0.20/0.55          | ~ (v1_funct_1 @ sk_E)
% 0.20/0.55          | ~ (m1_pre_topc @ sk_D @ X1)
% 0.20/0.55          | (v2_struct_0 @ sk_D)
% 0.20/0.55          | ~ (l1_pre_topc @ X1)
% 0.20/0.55          | ~ (v2_pre_topc @ X1)
% 0.20/0.55          | (v2_struct_0 @ X1))),
% 0.20/0.55      inference('sup-', [status(thm)], ['22', '24'])).
% 0.20/0.55  thf('26', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('28', plain,
% 0.20/0.55      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('29', plain, ((v1_funct_1 @ sk_E)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('30', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.55         ((v2_struct_0 @ sk_A)
% 0.20/0.55          | (v2_struct_0 @ X0)
% 0.20/0.55          | ~ (m1_pre_topc @ X0 @ X1)
% 0.20/0.55          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 0.20/0.55          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.20/0.55          | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X2)
% 0.20/0.55          | (r1_tmap_1 @ X0 @ sk_A @ 
% 0.20/0.55             (k3_tmap_1 @ X1 @ sk_A @ sk_D @ X0 @ sk_E) @ X2)
% 0.20/0.55          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.20/0.55          | ~ (m1_pre_topc @ sk_D @ X1)
% 0.20/0.55          | (v2_struct_0 @ sk_D)
% 0.20/0.55          | ~ (l1_pre_topc @ X1)
% 0.20/0.55          | ~ (v2_pre_topc @ X1)
% 0.20/0.55          | (v2_struct_0 @ X1))),
% 0.20/0.55      inference('demod', [status(thm)], ['25', '26', '27', '28', '29'])).
% 0.20/0.55  thf('31', plain,
% 0.20/0.55      ((![X0 : $i, X1 : $i]:
% 0.20/0.55          ((v2_struct_0 @ X0)
% 0.20/0.55           | ~ (v2_pre_topc @ X0)
% 0.20/0.55           | ~ (l1_pre_topc @ X0)
% 0.20/0.55           | (v2_struct_0 @ sk_D)
% 0.20/0.55           | ~ (m1_pre_topc @ sk_D @ X0)
% 0.20/0.55           | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ X1))
% 0.20/0.55           | (r1_tmap_1 @ X1 @ sk_A @ 
% 0.20/0.55              (k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E) @ sk_H)
% 0.20/0.55           | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.20/0.55           | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D))
% 0.20/0.55           | ~ (m1_pre_topc @ X1 @ X0)
% 0.20/0.55           | (v2_struct_0 @ X1)
% 0.20/0.55           | (v2_struct_0 @ sk_A)))
% 0.20/0.55         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['21', '30'])).
% 0.20/0.55  thf('32', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_D))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('33', plain, (((sk_G) = (sk_H))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('34', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D))),
% 0.20/0.55      inference('demod', [status(thm)], ['32', '33'])).
% 0.20/0.55  thf('35', plain,
% 0.20/0.55      ((![X0 : $i, X1 : $i]:
% 0.20/0.55          ((v2_struct_0 @ X0)
% 0.20/0.55           | ~ (v2_pre_topc @ X0)
% 0.20/0.55           | ~ (l1_pre_topc @ X0)
% 0.20/0.55           | (v2_struct_0 @ sk_D)
% 0.20/0.55           | ~ (m1_pre_topc @ sk_D @ X0)
% 0.20/0.55           | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ X1))
% 0.20/0.55           | (r1_tmap_1 @ X1 @ sk_A @ 
% 0.20/0.55              (k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E) @ sk_H)
% 0.20/0.55           | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.20/0.55           | ~ (m1_pre_topc @ X1 @ X0)
% 0.20/0.55           | (v2_struct_0 @ X1)
% 0.20/0.55           | (v2_struct_0 @ sk_A)))
% 0.20/0.55         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G)))),
% 0.20/0.55      inference('demod', [status(thm)], ['31', '34'])).
% 0.20/0.55  thf('36', plain,
% 0.20/0.55      ((![X0 : $i]:
% 0.20/0.55          ((v2_struct_0 @ sk_A)
% 0.20/0.55           | (v2_struct_0 @ sk_C_1)
% 0.20/0.55           | ~ (m1_pre_topc @ sk_C_1 @ X0)
% 0.20/0.55           | ~ (m1_pre_topc @ sk_C_1 @ sk_D)
% 0.20/0.55           | (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.55              (k3_tmap_1 @ X0 @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H)
% 0.20/0.55           | ~ (m1_pre_topc @ sk_D @ X0)
% 0.20/0.55           | (v2_struct_0 @ sk_D)
% 0.20/0.55           | ~ (l1_pre_topc @ X0)
% 0.20/0.55           | ~ (v2_pre_topc @ X0)
% 0.20/0.55           | (v2_struct_0 @ X0)))
% 0.20/0.55         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['20', '35'])).
% 0.20/0.55  thf('37', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('38', plain,
% 0.20/0.55      ((![X0 : $i]:
% 0.20/0.55          ((v2_struct_0 @ sk_A)
% 0.20/0.55           | (v2_struct_0 @ sk_C_1)
% 0.20/0.55           | ~ (m1_pre_topc @ sk_C_1 @ X0)
% 0.20/0.55           | (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.55              (k3_tmap_1 @ X0 @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H)
% 0.20/0.55           | ~ (m1_pre_topc @ sk_D @ X0)
% 0.20/0.55           | (v2_struct_0 @ sk_D)
% 0.20/0.55           | ~ (l1_pre_topc @ X0)
% 0.20/0.55           | ~ (v2_pre_topc @ X0)
% 0.20/0.55           | (v2_struct_0 @ X0)))
% 0.20/0.55         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G)))),
% 0.20/0.55      inference('demod', [status(thm)], ['36', '37'])).
% 0.20/0.55  thf('39', plain,
% 0.20/0.55      ((((v2_struct_0 @ sk_B)
% 0.20/0.55         | ~ (v2_pre_topc @ sk_B)
% 0.20/0.55         | ~ (l1_pre_topc @ sk_B)
% 0.20/0.55         | (v2_struct_0 @ sk_D)
% 0.20/0.55         | ~ (m1_pre_topc @ sk_D @ sk_B)
% 0.20/0.55         | (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.55            (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H)
% 0.20/0.55         | (v2_struct_0 @ sk_C_1)
% 0.20/0.55         | (v2_struct_0 @ sk_A)))
% 0.20/0.55         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['19', '38'])).
% 0.20/0.55  thf('40', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('41', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('42', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('43', plain,
% 0.20/0.55      ((((v2_struct_0 @ sk_B)
% 0.20/0.55         | (v2_struct_0 @ sk_D)
% 0.20/0.55         | (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.55            (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H)
% 0.20/0.55         | (v2_struct_0 @ sk_C_1)
% 0.20/0.55         | (v2_struct_0 @ sk_A)))
% 0.20/0.55         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G)))),
% 0.20/0.55      inference('demod', [status(thm)], ['39', '40', '41', '42'])).
% 0.20/0.55  thf('44', plain,
% 0.20/0.55      ((~ (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.55           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H))
% 0.20/0.55         <= (~
% 0.20/0.55             ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.55               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H)))),
% 0.20/0.55      inference('split', [status(esa)], ['13'])).
% 0.20/0.55  thf('45', plain,
% 0.20/0.55      ((((v2_struct_0 @ sk_A)
% 0.20/0.55         | (v2_struct_0 @ sk_C_1)
% 0.20/0.55         | (v2_struct_0 @ sk_D)
% 0.20/0.55         | (v2_struct_0 @ sk_B)))
% 0.20/0.55         <= (~
% 0.20/0.55             ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.55               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H)) & 
% 0.20/0.55             ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['43', '44'])).
% 0.20/0.55  thf('46', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('47', plain,
% 0.20/0.55      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C_1)))
% 0.20/0.55         <= (~
% 0.20/0.55             ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.55               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H)) & 
% 0.20/0.55             ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['45', '46'])).
% 0.20/0.55  thf('48', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('49', plain,
% 0.20/0.55      ((((v2_struct_0 @ sk_C_1) | (v2_struct_0 @ sk_D)))
% 0.20/0.55         <= (~
% 0.20/0.55             ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.55               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H)) & 
% 0.20/0.55             ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G)))),
% 0.20/0.55      inference('clc', [status(thm)], ['47', '48'])).
% 0.20/0.55  thf('50', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('51', plain,
% 0.20/0.55      (((v2_struct_0 @ sk_D))
% 0.20/0.55         <= (~
% 0.20/0.55             ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.55               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H)) & 
% 0.20/0.55             ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G)))),
% 0.20/0.55      inference('clc', [status(thm)], ['49', '50'])).
% 0.20/0.55  thf('52', plain, (~ (v2_struct_0 @ sk_D)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('53', plain,
% 0.20/0.55      (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G)) | 
% 0.20/0.55       ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.55         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H))),
% 0.20/0.55      inference('sup-', [status(thm)], ['51', '52'])).
% 0.20/0.55  thf('54', plain,
% 0.20/0.55      (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.55         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H)) | 
% 0.20/0.55       ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H))),
% 0.20/0.55      inference('split', [status(esa)], ['11'])).
% 0.20/0.55  thf('55', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(d10_xboole_0, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.55  thf('56', plain,
% 0.20/0.55      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.20/0.55      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.55  thf('57', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.20/0.55      inference('simplify', [status(thm)], ['56'])).
% 0.20/0.55  thf(t3_subset, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.55  thf('58', plain,
% 0.20/0.55      (![X7 : $i, X9 : $i]:
% 0.20/0.55         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 0.20/0.55      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.55  thf('59', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['57', '58'])).
% 0.20/0.55  thf(t39_pre_topc, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( l1_pre_topc @ A ) =>
% 0.20/0.55       ( ![B:$i]:
% 0.20/0.55         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.55           ( ![C:$i]:
% 0.20/0.55             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.20/0.55               ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ))).
% 0.20/0.55  thf('60', plain,
% 0.20/0.55      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.55         (~ (m1_pre_topc @ X14 @ X15)
% 0.20/0.55          | (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.20/0.55          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.20/0.55          | ~ (l1_pre_topc @ X15))),
% 0.20/0.55      inference('cnf', [status(esa)], [t39_pre_topc])).
% 0.20/0.55  thf('61', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         (~ (l1_pre_topc @ X1)
% 0.20/0.55          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.20/0.55             (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.20/0.55          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.20/0.55      inference('sup-', [status(thm)], ['59', '60'])).
% 0.20/0.55  thf('62', plain,
% 0.20/0.55      (((m1_subset_1 @ (u1_struct_0 @ sk_C_1) @ 
% 0.20/0.55         (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.20/0.55        | ~ (l1_pre_topc @ sk_D))),
% 0.20/0.55      inference('sup-', [status(thm)], ['55', '61'])).
% 0.20/0.55  thf('63', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(dt_m1_pre_topc, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( l1_pre_topc @ A ) =>
% 0.20/0.55       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.20/0.55  thf('64', plain,
% 0.20/0.55      (![X12 : $i, X13 : $i]:
% 0.20/0.55         (~ (m1_pre_topc @ X12 @ X13)
% 0.20/0.55          | (l1_pre_topc @ X12)
% 0.20/0.55          | ~ (l1_pre_topc @ X13))),
% 0.20/0.55      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.20/0.55  thf('65', plain, ((~ (l1_pre_topc @ sk_B) | (l1_pre_topc @ sk_D))),
% 0.20/0.55      inference('sup-', [status(thm)], ['63', '64'])).
% 0.20/0.55  thf('66', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('67', plain, ((l1_pre_topc @ sk_D)),
% 0.20/0.55      inference('demod', [status(thm)], ['65', '66'])).
% 0.20/0.55  thf('68', plain,
% 0.20/0.55      ((m1_subset_1 @ (u1_struct_0 @ sk_C_1) @ 
% 0.20/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.20/0.55      inference('demod', [status(thm)], ['62', '67'])).
% 0.20/0.55  thf('69', plain,
% 0.20/0.55      (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.55         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H))
% 0.20/0.55         <= (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.55               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H)))),
% 0.20/0.55      inference('split', [status(esa)], ['0'])).
% 0.20/0.55  thf('70', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_E @ 
% 0.20/0.55        (k1_zfmisc_1 @ 
% 0.20/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(t83_tmap_1, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.55       ( ![B:$i]:
% 0.20/0.55         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.55             ( l1_pre_topc @ B ) ) =>
% 0.20/0.55           ( ![C:$i]:
% 0.20/0.55             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.55               ( ![D:$i]:
% 0.20/0.55                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.20/0.55                   ( ![E:$i]:
% 0.20/0.55                     ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.55                         ( v1_funct_2 @
% 0.20/0.55                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.55                         ( m1_subset_1 @
% 0.20/0.55                           E @ 
% 0.20/0.55                           ( k1_zfmisc_1 @
% 0.20/0.55                             ( k2_zfmisc_1 @
% 0.20/0.55                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.55                       ( ( m1_pre_topc @ C @ D ) =>
% 0.20/0.55                         ( ![F:$i]:
% 0.20/0.55                           ( ( m1_subset_1 @
% 0.20/0.55                               F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ D ) ) ) =>
% 0.20/0.55                             ( ![G:$i]:
% 0.20/0.55                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.20/0.55                                 ( ![H:$i]:
% 0.20/0.55                                   ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) ) =>
% 0.20/0.55                                     ( ( ( r1_tarski @ F @ ( u1_struct_0 @ C ) ) & 
% 0.20/0.55                                         ( m1_connsp_2 @ F @ D @ G ) & 
% 0.20/0.55                                         ( ( G ) = ( H ) ) ) =>
% 0.20/0.55                                       ( ( r1_tmap_1 @ D @ B @ E @ G ) <=>
% 0.20/0.55                                         ( r1_tmap_1 @
% 0.20/0.55                                           C @ B @ 
% 0.20/0.55                                           ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ 
% 0.20/0.55                                           H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.55  thf('71', plain,
% 0.20/0.55      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, 
% 0.20/0.55         X44 : $i]:
% 0.20/0.55         ((v2_struct_0 @ X37)
% 0.20/0.55          | ~ (v2_pre_topc @ X37)
% 0.20/0.55          | ~ (l1_pre_topc @ X37)
% 0.20/0.55          | (v2_struct_0 @ X38)
% 0.20/0.55          | ~ (m1_pre_topc @ X38 @ X39)
% 0.20/0.55          | ~ (m1_pre_topc @ X40 @ X38)
% 0.20/0.55          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 0.20/0.55          | ~ (m1_subset_1 @ X42 @ (u1_struct_0 @ X40))
% 0.20/0.55          | ~ (r1_tmap_1 @ X40 @ X37 @ 
% 0.20/0.55               (k3_tmap_1 @ X39 @ X37 @ X38 @ X40 @ X43) @ X42)
% 0.20/0.55          | (r1_tmap_1 @ X38 @ X37 @ X43 @ X44)
% 0.20/0.55          | ((X44) != (X42))
% 0.20/0.55          | ~ (m1_connsp_2 @ X41 @ X38 @ X44)
% 0.20/0.55          | ~ (r1_tarski @ X41 @ (u1_struct_0 @ X40))
% 0.20/0.55          | ~ (m1_subset_1 @ X44 @ (u1_struct_0 @ X38))
% 0.20/0.55          | ~ (m1_subset_1 @ X43 @ 
% 0.20/0.55               (k1_zfmisc_1 @ 
% 0.20/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ X38) @ (u1_struct_0 @ X37))))
% 0.20/0.55          | ~ (v1_funct_2 @ X43 @ (u1_struct_0 @ X38) @ (u1_struct_0 @ X37))
% 0.20/0.55          | ~ (v1_funct_1 @ X43)
% 0.20/0.55          | ~ (m1_pre_topc @ X40 @ X39)
% 0.20/0.55          | (v2_struct_0 @ X40)
% 0.20/0.55          | ~ (l1_pre_topc @ X39)
% 0.20/0.55          | ~ (v2_pre_topc @ X39)
% 0.20/0.55          | (v2_struct_0 @ X39))),
% 0.20/0.55      inference('cnf', [status(esa)], [t83_tmap_1])).
% 0.20/0.55  thf('72', plain,
% 0.20/0.55      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.20/0.55         ((v2_struct_0 @ X39)
% 0.20/0.55          | ~ (v2_pre_topc @ X39)
% 0.20/0.55          | ~ (l1_pre_topc @ X39)
% 0.20/0.55          | (v2_struct_0 @ X40)
% 0.20/0.55          | ~ (m1_pre_topc @ X40 @ X39)
% 0.20/0.55          | ~ (v1_funct_1 @ X43)
% 0.20/0.55          | ~ (v1_funct_2 @ X43 @ (u1_struct_0 @ X38) @ (u1_struct_0 @ X37))
% 0.20/0.55          | ~ (m1_subset_1 @ X43 @ 
% 0.20/0.55               (k1_zfmisc_1 @ 
% 0.20/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ X38) @ (u1_struct_0 @ X37))))
% 0.20/0.55          | ~ (m1_subset_1 @ X42 @ (u1_struct_0 @ X38))
% 0.20/0.55          | ~ (r1_tarski @ X41 @ (u1_struct_0 @ X40))
% 0.20/0.55          | ~ (m1_connsp_2 @ X41 @ X38 @ X42)
% 0.20/0.55          | (r1_tmap_1 @ X38 @ X37 @ X43 @ X42)
% 0.20/0.55          | ~ (r1_tmap_1 @ X40 @ X37 @ 
% 0.20/0.55               (k3_tmap_1 @ X39 @ X37 @ X38 @ X40 @ X43) @ X42)
% 0.20/0.55          | ~ (m1_subset_1 @ X42 @ (u1_struct_0 @ X40))
% 0.20/0.55          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 0.20/0.55          | ~ (m1_pre_topc @ X40 @ X38)
% 0.20/0.55          | ~ (m1_pre_topc @ X38 @ X39)
% 0.20/0.55          | (v2_struct_0 @ X38)
% 0.20/0.55          | ~ (l1_pre_topc @ X37)
% 0.20/0.55          | ~ (v2_pre_topc @ X37)
% 0.20/0.55          | (v2_struct_0 @ X37))),
% 0.20/0.55      inference('simplify', [status(thm)], ['71'])).
% 0.20/0.55  thf('73', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.55         ((v2_struct_0 @ sk_A)
% 0.20/0.55          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.55          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.55          | (v2_struct_0 @ sk_D)
% 0.20/0.55          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.20/0.55          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.20/0.55          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.20/0.55          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.20/0.55          | ~ (r1_tmap_1 @ X1 @ sk_A @ 
% 0.20/0.55               (k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E) @ X3)
% 0.20/0.55          | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X3)
% 0.20/0.55          | ~ (m1_connsp_2 @ X2 @ sk_D @ X3)
% 0.20/0.55          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X1))
% 0.20/0.55          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_D))
% 0.20/0.55          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))
% 0.20/0.55          | ~ (v1_funct_1 @ sk_E)
% 0.20/0.55          | ~ (m1_pre_topc @ X1 @ X0)
% 0.20/0.55          | (v2_struct_0 @ X1)
% 0.20/0.55          | ~ (l1_pre_topc @ X0)
% 0.20/0.55          | ~ (v2_pre_topc @ X0)
% 0.20/0.55          | (v2_struct_0 @ X0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['70', '72'])).
% 0.20/0.55  thf('74', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('75', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('76', plain,
% 0.20/0.55      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('77', plain, ((v1_funct_1 @ sk_E)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('78', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.55         ((v2_struct_0 @ sk_A)
% 0.20/0.55          | (v2_struct_0 @ sk_D)
% 0.20/0.55          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.20/0.55          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.20/0.55          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.20/0.55          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.20/0.55          | ~ (r1_tmap_1 @ X1 @ sk_A @ 
% 0.20/0.55               (k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E) @ X3)
% 0.20/0.55          | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X3)
% 0.20/0.55          | ~ (m1_connsp_2 @ X2 @ sk_D @ X3)
% 0.20/0.55          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X1))
% 0.20/0.55          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_D))
% 0.20/0.55          | ~ (m1_pre_topc @ X1 @ X0)
% 0.20/0.55          | (v2_struct_0 @ X1)
% 0.20/0.55          | ~ (l1_pre_topc @ X0)
% 0.20/0.55          | ~ (v2_pre_topc @ X0)
% 0.20/0.55          | (v2_struct_0 @ X0))),
% 0.20/0.55      inference('demod', [status(thm)], ['73', '74', '75', '76', '77'])).
% 0.20/0.55  thf('79', plain,
% 0.20/0.55      ((![X0 : $i]:
% 0.20/0.55          ((v2_struct_0 @ sk_B)
% 0.20/0.55           | ~ (v2_pre_topc @ sk_B)
% 0.20/0.55           | ~ (l1_pre_topc @ sk_B)
% 0.20/0.55           | (v2_struct_0 @ sk_C_1)
% 0.20/0.55           | ~ (m1_pre_topc @ sk_C_1 @ sk_B)
% 0.20/0.55           | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D))
% 0.20/0.55           | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.20/0.55           | ~ (m1_connsp_2 @ X0 @ sk_D @ sk_H)
% 0.20/0.55           | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)
% 0.20/0.55           | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_C_1))
% 0.20/0.55           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.20/0.55           | ~ (m1_pre_topc @ sk_C_1 @ sk_D)
% 0.20/0.55           | ~ (m1_pre_topc @ sk_D @ sk_B)
% 0.20/0.55           | (v2_struct_0 @ sk_D)
% 0.20/0.55           | (v2_struct_0 @ sk_A)))
% 0.20/0.55         <= (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.55               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['69', '78'])).
% 0.20/0.55  thf('80', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('81', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('82', plain, ((m1_pre_topc @ sk_C_1 @ sk_B)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('83', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D))),
% 0.20/0.55      inference('demod', [status(thm)], ['32', '33'])).
% 0.20/0.55  thf('84', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_C_1))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('85', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('86', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('87', plain,
% 0.20/0.55      ((![X0 : $i]:
% 0.20/0.55          ((v2_struct_0 @ sk_B)
% 0.20/0.55           | (v2_struct_0 @ sk_C_1)
% 0.20/0.55           | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.20/0.55           | ~ (m1_connsp_2 @ X0 @ sk_D @ sk_H)
% 0.20/0.55           | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)
% 0.20/0.55           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.20/0.55           | (v2_struct_0 @ sk_D)
% 0.20/0.55           | (v2_struct_0 @ sk_A)))
% 0.20/0.55         <= (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.55               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H)))),
% 0.20/0.55      inference('demod', [status(thm)],
% 0.20/0.55                ['79', '80', '81', '82', '83', '84', '85', '86'])).
% 0.20/0.55  thf('88', plain,
% 0.20/0.55      ((((v2_struct_0 @ sk_A)
% 0.20/0.55         | (v2_struct_0 @ sk_D)
% 0.20/0.55         | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)
% 0.20/0.55         | ~ (m1_connsp_2 @ (u1_struct_0 @ sk_C_1) @ sk_D @ sk_H)
% 0.20/0.55         | ~ (r1_tarski @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_C_1))
% 0.20/0.55         | (v2_struct_0 @ sk_C_1)
% 0.20/0.55         | (v2_struct_0 @ sk_B)))
% 0.20/0.55         <= (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.55               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['68', '87'])).
% 0.20/0.55  thf('89', plain, ((r2_hidden @ sk_G @ sk_F)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('90', plain, (((sk_G) = (sk_H))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('91', plain, ((r2_hidden @ sk_H @ sk_F)),
% 0.20/0.55      inference('demod', [status(thm)], ['89', '90'])).
% 0.20/0.55  thf('92', plain,
% 0.20/0.55      ((m1_subset_1 @ (u1_struct_0 @ sk_C_1) @ 
% 0.20/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.20/0.55      inference('demod', [status(thm)], ['62', '67'])).
% 0.20/0.55  thf(d3_tarski, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.55       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.55  thf('93', plain,
% 0.20/0.55      (![X1 : $i, X3 : $i]:
% 0.20/0.55         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.20/0.55      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.55  thf('94', plain, ((r1_tarski @ sk_F @ (u1_struct_0 @ sk_C_1))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('95', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.55         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.55          | (r2_hidden @ X0 @ X2)
% 0.20/0.55          | ~ (r1_tarski @ X1 @ X2))),
% 0.20/0.55      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.55  thf('96', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_C_1)) | ~ (r2_hidden @ X0 @ sk_F))),
% 0.20/0.55      inference('sup-', [status(thm)], ['94', '95'])).
% 0.20/0.55  thf('97', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         ((r1_tarski @ sk_F @ X0)
% 0.20/0.55          | (r2_hidden @ (sk_C @ X0 @ sk_F) @ (u1_struct_0 @ sk_C_1)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['93', '96'])).
% 0.20/0.55  thf('98', plain,
% 0.20/0.55      ((m1_subset_1 @ (u1_struct_0 @ sk_C_1) @ 
% 0.20/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.20/0.55      inference('demod', [status(thm)], ['62', '67'])).
% 0.20/0.55  thf('99', plain,
% 0.20/0.55      (![X7 : $i, X8 : $i]:
% 0.20/0.55         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.20/0.55      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.55  thf('100', plain,
% 0.20/0.55      ((r1_tarski @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D))),
% 0.20/0.55      inference('sup-', [status(thm)], ['98', '99'])).
% 0.20/0.55  thf('101', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.55         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.55          | (r2_hidden @ X0 @ X2)
% 0.20/0.55          | ~ (r1_tarski @ X1 @ X2))),
% 0.20/0.55      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.55  thf('102', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_D))
% 0.20/0.55          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_C_1)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['100', '101'])).
% 0.20/0.55  thf('103', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         ((r1_tarski @ sk_F @ X0)
% 0.20/0.55          | (r2_hidden @ (sk_C @ X0 @ sk_F) @ (u1_struct_0 @ sk_D)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['97', '102'])).
% 0.20/0.55  thf('104', plain,
% 0.20/0.55      (![X1 : $i, X3 : $i]:
% 0.20/0.55         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.20/0.55      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.55  thf('105', plain,
% 0.20/0.55      (((r1_tarski @ sk_F @ (u1_struct_0 @ sk_D))
% 0.20/0.55        | (r1_tarski @ sk_F @ (u1_struct_0 @ sk_D)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['103', '104'])).
% 0.20/0.55  thf('106', plain, ((r1_tarski @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.20/0.55      inference('simplify', [status(thm)], ['105'])).
% 0.20/0.55  thf('107', plain,
% 0.20/0.55      (![X7 : $i, X9 : $i]:
% 0.20/0.55         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 0.20/0.55      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.55  thf('108', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['106', '107'])).
% 0.20/0.55  thf(t56_tops_1, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( l1_pre_topc @ A ) =>
% 0.20/0.55       ( ![B:$i]:
% 0.20/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.55           ( ![C:$i]:
% 0.20/0.55             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.55               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.20/0.55                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.20/0.55  thf('109', plain,
% 0.20/0.55      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.20/0.55         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.20/0.55          | ~ (v3_pre_topc @ X17 @ X18)
% 0.20/0.55          | ~ (r1_tarski @ X17 @ X19)
% 0.20/0.55          | (r1_tarski @ X17 @ (k1_tops_1 @ X18 @ X19))
% 0.20/0.55          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.20/0.55          | ~ (l1_pre_topc @ X18))),
% 0.20/0.55      inference('cnf', [status(esa)], [t56_tops_1])).
% 0.20/0.55  thf('110', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (~ (l1_pre_topc @ sk_D)
% 0.20/0.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.20/0.55          | (r1_tarski @ sk_F @ (k1_tops_1 @ sk_D @ X0))
% 0.20/0.55          | ~ (r1_tarski @ sk_F @ X0)
% 0.20/0.55          | ~ (v3_pre_topc @ sk_F @ sk_D))),
% 0.20/0.55      inference('sup-', [status(thm)], ['108', '109'])).
% 0.20/0.55  thf('111', plain, ((l1_pre_topc @ sk_D)),
% 0.20/0.55      inference('demod', [status(thm)], ['65', '66'])).
% 0.20/0.55  thf('112', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.20/0.55          | (r1_tarski @ sk_F @ (k1_tops_1 @ sk_D @ X0))
% 0.20/0.55          | ~ (r1_tarski @ sk_F @ X0)
% 0.20/0.55          | ~ (v3_pre_topc @ sk_F @ sk_D))),
% 0.20/0.55      inference('demod', [status(thm)], ['110', '111'])).
% 0.20/0.55  thf('113', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('114', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['106', '107'])).
% 0.20/0.55  thf(t33_tops_2, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( l1_pre_topc @ A ) =>
% 0.20/0.55       ( ![B:$i]:
% 0.20/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.55           ( ![C:$i]:
% 0.20/0.55             ( ( m1_pre_topc @ C @ A ) =>
% 0.20/0.55               ( ( v3_pre_topc @ B @ A ) =>
% 0.20/0.55                 ( ![D:$i]:
% 0.20/0.55                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) ) =>
% 0.20/0.55                     ( ( ( D ) = ( B ) ) => ( v3_pre_topc @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.55  thf('115', plain,
% 0.20/0.55      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.20/0.55         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.20/0.55          | ~ (v3_pre_topc @ X20 @ X21)
% 0.20/0.55          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.20/0.55          | (v3_pre_topc @ X22 @ X23)
% 0.20/0.55          | ((X22) != (X20))
% 0.20/0.55          | ~ (m1_pre_topc @ X23 @ X21)
% 0.20/0.55          | ~ (l1_pre_topc @ X21))),
% 0.20/0.55      inference('cnf', [status(esa)], [t33_tops_2])).
% 0.20/0.55  thf('116', plain,
% 0.20/0.55      (![X20 : $i, X21 : $i, X23 : $i]:
% 0.20/0.55         (~ (l1_pre_topc @ X21)
% 0.20/0.55          | ~ (m1_pre_topc @ X23 @ X21)
% 0.20/0.55          | (v3_pre_topc @ X20 @ X23)
% 0.20/0.55          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.20/0.55          | ~ (v3_pre_topc @ X20 @ X21)
% 0.20/0.55          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21))))),
% 0.20/0.55      inference('simplify', [status(thm)], ['115'])).
% 0.20/0.55  thf('117', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (~ (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.55          | ~ (v3_pre_topc @ sk_F @ X0)
% 0.20/0.55          | (v3_pre_topc @ sk_F @ sk_D)
% 0.20/0.55          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.20/0.55          | ~ (l1_pre_topc @ X0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['114', '116'])).
% 0.20/0.55  thf('118', plain,
% 0.20/0.55      ((~ (l1_pre_topc @ sk_B)
% 0.20/0.55        | ~ (m1_pre_topc @ sk_D @ sk_B)
% 0.20/0.55        | (v3_pre_topc @ sk_F @ sk_D)
% 0.20/0.55        | ~ (v3_pre_topc @ sk_F @ sk_B))),
% 0.20/0.55      inference('sup-', [status(thm)], ['113', '117'])).
% 0.20/0.55  thf('119', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('120', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('121', plain, ((v3_pre_topc @ sk_F @ sk_B)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('122', plain, ((v3_pre_topc @ sk_F @ sk_D)),
% 0.20/0.55      inference('demod', [status(thm)], ['118', '119', '120', '121'])).
% 0.20/0.55  thf('123', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.20/0.55          | (r1_tarski @ sk_F @ (k1_tops_1 @ sk_D @ X0))
% 0.20/0.55          | ~ (r1_tarski @ sk_F @ X0))),
% 0.20/0.55      inference('demod', [status(thm)], ['112', '122'])).
% 0.20/0.55  thf('124', plain,
% 0.20/0.55      ((~ (r1_tarski @ sk_F @ (u1_struct_0 @ sk_C_1))
% 0.20/0.55        | (r1_tarski @ sk_F @ (k1_tops_1 @ sk_D @ (u1_struct_0 @ sk_C_1))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['92', '123'])).
% 0.20/0.55  thf('125', plain, ((r1_tarski @ sk_F @ (u1_struct_0 @ sk_C_1))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('126', plain,
% 0.20/0.55      ((r1_tarski @ sk_F @ (k1_tops_1 @ sk_D @ (u1_struct_0 @ sk_C_1)))),
% 0.20/0.55      inference('demod', [status(thm)], ['124', '125'])).
% 0.20/0.55  thf('127', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.55         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.55          | (r2_hidden @ X0 @ X2)
% 0.20/0.55          | ~ (r1_tarski @ X1 @ X2))),
% 0.20/0.55      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.55  thf('128', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         ((r2_hidden @ X0 @ (k1_tops_1 @ sk_D @ (u1_struct_0 @ sk_C_1)))
% 0.20/0.55          | ~ (r2_hidden @ X0 @ sk_F))),
% 0.20/0.55      inference('sup-', [status(thm)], ['126', '127'])).
% 0.20/0.55  thf('129', plain,
% 0.20/0.55      ((r2_hidden @ sk_H @ (k1_tops_1 @ sk_D @ (u1_struct_0 @ sk_C_1)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['91', '128'])).
% 0.20/0.55  thf('130', plain,
% 0.20/0.55      ((m1_subset_1 @ (u1_struct_0 @ sk_C_1) @ 
% 0.20/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.20/0.55      inference('demod', [status(thm)], ['62', '67'])).
% 0.20/0.55  thf(d1_connsp_2, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.55       ( ![B:$i]:
% 0.20/0.55         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.55           ( ![C:$i]:
% 0.20/0.55             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.55               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 0.20/0.55                 ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.20/0.55  thf('131', plain,
% 0.20/0.55      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.20/0.55         (~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X25))
% 0.20/0.55          | ~ (r2_hidden @ X24 @ (k1_tops_1 @ X25 @ X26))
% 0.20/0.55          | (m1_connsp_2 @ X26 @ X25 @ X24)
% 0.20/0.55          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.20/0.55          | ~ (l1_pre_topc @ X25)
% 0.20/0.55          | ~ (v2_pre_topc @ X25)
% 0.20/0.55          | (v2_struct_0 @ X25))),
% 0.20/0.55      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.20/0.55  thf('132', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         ((v2_struct_0 @ sk_D)
% 0.20/0.55          | ~ (v2_pre_topc @ sk_D)
% 0.20/0.55          | ~ (l1_pre_topc @ sk_D)
% 0.20/0.55          | (m1_connsp_2 @ (u1_struct_0 @ sk_C_1) @ sk_D @ X0)
% 0.20/0.55          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_D @ (u1_struct_0 @ sk_C_1)))
% 0.20/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['130', '131'])).
% 0.20/0.55  thf('133', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(cc1_pre_topc, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.55       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.20/0.55  thf('134', plain,
% 0.20/0.55      (![X10 : $i, X11 : $i]:
% 0.20/0.55         (~ (m1_pre_topc @ X10 @ X11)
% 0.20/0.55          | (v2_pre_topc @ X10)
% 0.20/0.55          | ~ (l1_pre_topc @ X11)
% 0.20/0.55          | ~ (v2_pre_topc @ X11))),
% 0.20/0.55      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.20/0.55  thf('135', plain,
% 0.20/0.55      ((~ (v2_pre_topc @ sk_B) | ~ (l1_pre_topc @ sk_B) | (v2_pre_topc @ sk_D))),
% 0.20/0.55      inference('sup-', [status(thm)], ['133', '134'])).
% 0.20/0.55  thf('136', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('137', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('138', plain, ((v2_pre_topc @ sk_D)),
% 0.20/0.55      inference('demod', [status(thm)], ['135', '136', '137'])).
% 0.20/0.55  thf('139', plain, ((l1_pre_topc @ sk_D)),
% 0.20/0.55      inference('demod', [status(thm)], ['65', '66'])).
% 0.20/0.55  thf('140', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         ((v2_struct_0 @ sk_D)
% 0.20/0.55          | (m1_connsp_2 @ (u1_struct_0 @ sk_C_1) @ sk_D @ X0)
% 0.20/0.55          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_D @ (u1_struct_0 @ sk_C_1)))
% 0.20/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D)))),
% 0.20/0.55      inference('demod', [status(thm)], ['132', '138', '139'])).
% 0.20/0.55  thf('141', plain,
% 0.20/0.55      ((~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D))
% 0.20/0.55        | (m1_connsp_2 @ (u1_struct_0 @ sk_C_1) @ sk_D @ sk_H)
% 0.20/0.55        | (v2_struct_0 @ sk_D))),
% 0.20/0.55      inference('sup-', [status(thm)], ['129', '140'])).
% 0.20/0.55  thf('142', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D))),
% 0.20/0.55      inference('demod', [status(thm)], ['32', '33'])).
% 0.20/0.55  thf('143', plain,
% 0.20/0.55      (((m1_connsp_2 @ (u1_struct_0 @ sk_C_1) @ sk_D @ sk_H)
% 0.20/0.55        | (v2_struct_0 @ sk_D))),
% 0.20/0.55      inference('demod', [status(thm)], ['141', '142'])).
% 0.20/0.55  thf('144', plain, (~ (v2_struct_0 @ sk_D)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('145', plain, ((m1_connsp_2 @ (u1_struct_0 @ sk_C_1) @ sk_D @ sk_H)),
% 0.20/0.55      inference('clc', [status(thm)], ['143', '144'])).
% 0.20/0.55  thf('146', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.20/0.55      inference('simplify', [status(thm)], ['56'])).
% 0.20/0.55  thf('147', plain,
% 0.20/0.55      ((((v2_struct_0 @ sk_A)
% 0.20/0.55         | (v2_struct_0 @ sk_D)
% 0.20/0.55         | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)
% 0.20/0.55         | (v2_struct_0 @ sk_C_1)
% 0.20/0.55         | (v2_struct_0 @ sk_B)))
% 0.20/0.55         <= (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.55               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H)))),
% 0.20/0.55      inference('demod', [status(thm)], ['88', '145', '146'])).
% 0.20/0.55  thf('148', plain,
% 0.20/0.55      ((~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H))
% 0.20/0.55         <= (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G)))),
% 0.20/0.55      inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.55  thf('149', plain,
% 0.20/0.55      ((((v2_struct_0 @ sk_B)
% 0.20/0.55         | (v2_struct_0 @ sk_C_1)
% 0.20/0.55         | (v2_struct_0 @ sk_D)
% 0.20/0.55         | (v2_struct_0 @ sk_A)))
% 0.20/0.55         <= (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G)) & 
% 0.20/0.55             ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.55               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['147', '148'])).
% 0.20/0.55  thf('150', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('151', plain,
% 0.20/0.55      ((((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C_1) | (v2_struct_0 @ sk_B)))
% 0.20/0.55         <= (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G)) & 
% 0.20/0.55             ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.55               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['149', '150'])).
% 0.20/0.55  thf('152', plain, (~ (v2_struct_0 @ sk_D)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('153', plain,
% 0.20/0.55      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C_1)))
% 0.20/0.55         <= (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G)) & 
% 0.20/0.55             ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.55               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H)))),
% 0.20/0.55      inference('clc', [status(thm)], ['151', '152'])).
% 0.20/0.55  thf('154', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('155', plain,
% 0.20/0.55      (((v2_struct_0 @ sk_C_1))
% 0.20/0.55         <= (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G)) & 
% 0.20/0.55             ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.55               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H)))),
% 0.20/0.55      inference('clc', [status(thm)], ['153', '154'])).
% 0.20/0.55  thf('156', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('157', plain,
% 0.20/0.55      (~
% 0.20/0.55       ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.55         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_H)) | 
% 0.20/0.55       ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G))),
% 0.20/0.55      inference('sup-', [status(thm)], ['155', '156'])).
% 0.20/0.55  thf('158', plain, ($false),
% 0.20/0.55      inference('sat_resolution*', [status(thm)],
% 0.20/0.55                ['8', '17', '18', '53', '54', '157'])).
% 0.20/0.55  
% 0.20/0.55  % SZS output end Refutation
% 0.20/0.55  
% 0.20/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
