%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YsoknZYHFG

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:15 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :  153 ( 408 expanded)
%              Number of leaves         :   31 ( 124 expanded)
%              Depth                    :   26
%              Number of atoms          : 1937 (18058 expanded)
%              Number of equality atoms :   14 ( 211 expanded)
%              Maximal formula depth    :   32 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_H )
    | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_H )
   <= ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_H ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_H )
    | ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_H )
    | ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H )
    | ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_H ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_H )
    | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_H )
    | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H ) ),
    inference(split,[status(esa)],['10'])).

thf('12',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_H )
    | ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G )
   <= ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G ) ),
    inference(split,[status(esa)],['12'])).

thf('14',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H )
   <= ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H )
    | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G ) ),
    inference('sup-',[status(thm)],['11','15'])).

thf('17',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G ) ),
    inference(split,[status(esa)],['2'])).

thf('20',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
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

thf('23',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( v2_struct_0 @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ( v2_struct_0 @ X12 )
      | ~ ( m1_pre_topc @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X15 ) )
      | ~ ( m1_pre_topc @ X12 @ X15 )
      | ~ ( r1_tmap_1 @ X15 @ X11 @ X16 @ X14 )
      | ( X14 != X17 )
      | ( r1_tmap_1 @ X12 @ X11 @ ( k3_tmap_1 @ X13 @ X11 @ X15 @ X12 @ X16 ) @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X12 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X11 ) ) ) )
      | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X11 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( m1_pre_topc @ X15 @ X13 )
      | ( v2_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t81_tmap_1])).

thf('24',plain,(
    ! [X11: $i,X12: $i,X13: $i,X15: $i,X16: $i,X17: $i] :
      ( ( v2_struct_0 @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X13 )
      | ( v2_struct_0 @ X15 )
      | ~ ( m1_pre_topc @ X15 @ X13 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X11 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X11 ) ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X12 ) )
      | ( r1_tmap_1 @ X12 @ X11 @ ( k3_tmap_1 @ X13 @ X11 @ X15 @ X12 @ X16 ) @ X17 )
      | ~ ( r1_tmap_1 @ X15 @ X11 @ X16 @ X17 )
      | ~ ( m1_pre_topc @ X12 @ X15 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X15 ) )
      | ~ ( m1_pre_topc @ X12 @ X13 )
      | ( v2_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
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
    inference('sup-',[status(thm)],['22','24'])).

thf('26',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
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
    inference(demod,[status(thm)],['25','26','27','28','29'])).

thf('31',plain,
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
   <= ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G ) ),
    inference('sup-',[status(thm)],['21','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
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
   <= ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G ) ),
    inference(demod,[status(thm)],['31','34'])).

thf('36',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_C )
        | ~ ( m1_pre_topc @ sk_C @ X0 )
        | ~ ( m1_pre_topc @ sk_C @ sk_D_1 )
        | ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_H )
        | ~ ( m1_pre_topc @ sk_D_1 @ X0 )
        | ( v2_struct_0 @ sk_D_1 )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 ) )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G ) ),
    inference('sup-',[status(thm)],['18','35'])).

thf('37',plain,(
    m1_pre_topc @ sk_C @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_C )
        | ~ ( m1_pre_topc @ sk_C @ X0 )
        | ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_H )
        | ~ ( m1_pre_topc @ sk_D_1 @ X0 )
        | ( v2_struct_0 @ sk_D_1 )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 ) )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_D_1 )
      | ~ ( m1_pre_topc @ sk_D_1 @ sk_A )
      | ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_H )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G ) ),
    inference('sup-',[status(thm)],['17','38'])).

thf('40',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    m1_pre_topc @ sk_D_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D_1 )
      | ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_H )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G ) ),
    inference(demod,[status(thm)],['39','40','41','42'])).

thf('44',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_H )
   <= ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_H ) ),
    inference(split,[status(esa)],['12'])).

thf('45',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_H )
      & ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_H )
      & ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_H )
      & ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( v2_struct_0 @ sk_C )
   <= ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_H )
      & ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G ) ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_H )
    | ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_H )
    | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H ) ),
    inference(split,[status(esa)],['10'])).

thf('55',plain,(
    r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_H ),
    inference('sat_resolution*',[status(thm)],['7','16','53','54'])).

thf('56',plain,(
    r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_H ),
    inference(simpl_trail,[status(thm)],['3','55'])).

thf('57',plain,(
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

thf('58',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( v2_struct_0 @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ~ ( l1_pre_topc @ X18 )
      | ( v2_struct_0 @ X19 )
      | ~ ( m1_pre_topc @ X19 @ X20 )
      | ~ ( m1_pre_topc @ X21 @ X19 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X21 ) )
      | ~ ( r1_tmap_1 @ X21 @ X18 @ ( k3_tmap_1 @ X20 @ X18 @ X19 @ X21 @ X24 ) @ X23 )
      | ( r1_tmap_1 @ X19 @ X18 @ X24 @ X25 )
      | ( X25 != X23 )
      | ~ ( m1_connsp_2 @ X22 @ X19 @ X25 )
      | ~ ( r1_tarski @ X22 @ ( u1_struct_0 @ X21 ) )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X19 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X18 ) ) ) )
      | ~ ( v1_funct_2 @ X24 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X18 ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( m1_pre_topc @ X21 @ X20 )
      | ( v2_struct_0 @ X21 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t83_tmap_1])).

thf('59',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( v2_struct_0 @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ~ ( l1_pre_topc @ X20 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_pre_topc @ X21 @ X20 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_2 @ X24 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X18 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X18 ) ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X19 ) )
      | ~ ( r1_tarski @ X22 @ ( u1_struct_0 @ X21 ) )
      | ~ ( m1_connsp_2 @ X22 @ X19 @ X23 )
      | ( r1_tmap_1 @ X19 @ X18 @ X24 @ X23 )
      | ~ ( r1_tmap_1 @ X21 @ X18 @ ( k3_tmap_1 @ X20 @ X18 @ X19 @ X21 @ X24 ) @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X21 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( m1_pre_topc @ X21 @ X19 )
      | ~ ( m1_pre_topc @ X19 @ X20 )
      | ( v2_struct_0 @ X19 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
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
    inference('sup-',[status(thm)],['57','59'])).

thf('61',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
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
    inference(demod,[status(thm)],['60','61','62','63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ sk_A )
      | ~ ( m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ~ ( m1_connsp_2 @ X0 @ sk_D_1 @ sk_H )
      | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H )
      | ~ ( m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_C ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
      | ~ ( m1_pre_topc @ sk_C @ sk_D_1 )
      | ~ ( m1_pre_topc @ sk_D_1 @ sk_A )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['56','65'])).

thf('67',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('71',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    m1_pre_topc @ sk_C @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    m1_pre_topc @ sk_D_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ~ ( m1_connsp_2 @ X0 @ sk_D_1 @ sk_H )
      | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['66','67','68','69','70','71','72','73'])).

thf('75',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 )
    | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H )
    | ~ ( m1_connsp_2 @ sk_F @ sk_D_1 @ sk_H )
    | ~ ( r1_tarski @ sk_F @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','74'])).

thf('76',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('77',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t8_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( m1_connsp_2 @ C @ A @ B )
              <=> ? [D: $i] :
                    ( ( r2_hidden @ B @ D )
                    & ( r1_tarski @ D @ C )
                    & ( v3_pre_topc @ D @ A )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) )).

thf('79',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X8 ) )
      | ~ ( r2_hidden @ X7 @ X10 )
      | ~ ( r1_tarski @ X10 @ X9 )
      | ~ ( v3_pre_topc @ X10 @ X8 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( m1_connsp_2 @ X9 @ X8 @ X7 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t8_connsp_2])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_D_1 )
      | ~ ( v2_pre_topc @ sk_D_1 )
      | ~ ( l1_pre_topc @ sk_D_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
      | ( m1_connsp_2 @ X0 @ sk_D_1 @ X1 )
      | ~ ( v3_pre_topc @ sk_F @ sk_D_1 )
      | ~ ( r1_tarski @ sk_F @ X0 )
      | ~ ( r2_hidden @ X1 @ sk_F )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    m1_pre_topc @ sk_D_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('82',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_pre_topc @ X3 @ X4 )
      | ( v2_pre_topc @ X3 )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( v2_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('83',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v2_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('87',plain,(
    m1_pre_topc @ sk_D_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('88',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_pre_topc @ X5 @ X6 )
      | ( l1_pre_topc @ X5 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('89',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    v3_pre_topc @ sk_F @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_D_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
      | ( m1_connsp_2 @ X0 @ sk_D_1 @ X1 )
      | ~ ( r1_tarski @ sk_F @ X0 )
      | ~ ( r2_hidden @ X1 @ sk_F )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['80','86','91','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_F )
      | ~ ( r1_tarski @ sk_F @ sk_F )
      | ( m1_connsp_2 @ sk_F @ sk_D_1 @ X0 )
      | ( v2_struct_0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['77','93'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('96',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_F )
      | ( m1_connsp_2 @ sk_F @ sk_D_1 @ X0 )
      | ( v2_struct_0 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['94','96'])).

thf('98',plain,
    ( ( v2_struct_0 @ sk_D_1 )
    | ( m1_connsp_2 @ sk_F @ sk_D_1 @ sk_H )
    | ~ ( r2_hidden @ sk_H @ sk_F ) ),
    inference('sup-',[status(thm)],['76','97'])).

thf('99',plain,(
    r2_hidden @ sk_G @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    r2_hidden @ sk_H @ sk_F ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,
    ( ( v2_struct_0 @ sk_D_1 )
    | ( m1_connsp_2 @ sk_F @ sk_D_1 @ sk_H ) ),
    inference(demod,[status(thm)],['98','101'])).

thf('103',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    m1_connsp_2 @ sk_F @ sk_D_1 @ sk_H ),
    inference(clc,[status(thm)],['102','103'])).

thf('105',plain,(
    r1_tarski @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 )
    | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['75','104','105'])).

thf('107',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H )
   <= ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('108',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('109',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H )
   <= ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H ) ),
    inference(split,[status(esa)],['6'])).

thf('110',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G )
    | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G ) ),
    inference('sat_resolution*',[status(thm)],['7','16','53','110'])).

thf('112',plain,(
    ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H ) ),
    inference(simpl_trail,[status(thm)],['107','111'])).

thf('113',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['106','112'])).

thf('114',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['115','116'])).

thf('118',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    v2_struct_0 @ sk_C ),
    inference(clc,[status(thm)],['117','118'])).

thf('120',plain,(
    $false ),
    inference(demod,[status(thm)],['0','119'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YsoknZYHFG
% 0.13/0.35  % Computer   : n013.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:35:25 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.39/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.39/0.58  % Solved by: fo/fo7.sh
% 0.39/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.58  % done 129 iterations in 0.118s
% 0.39/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.39/0.58  % SZS output start Refutation
% 0.39/0.58  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.39/0.58  thf(sk_F_type, type, sk_F: $i).
% 0.39/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.58  thf(sk_G_type, type, sk_G: $i).
% 0.39/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.58  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.39/0.58  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.39/0.58  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.39/0.58  thf(sk_C_type, type, sk_C: $i).
% 0.39/0.58  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.39/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.58  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.39/0.58  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.39/0.58  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.39/0.58  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.39/0.58  thf(sk_E_type, type, sk_E: $i).
% 0.39/0.58  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.39/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.58  thf(sk_H_type, type, sk_H: $i).
% 0.39/0.58  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.39/0.58  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.39/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.58  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.39/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.39/0.58  thf(t84_tmap_1, conjecture,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.58       ( ![B:$i]:
% 0.39/0.58         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.39/0.58             ( l1_pre_topc @ B ) ) =>
% 0.39/0.58           ( ![C:$i]:
% 0.39/0.58             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.39/0.58               ( ![D:$i]:
% 0.39/0.58                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.39/0.58                   ( ![E:$i]:
% 0.39/0.58                     ( ( ( v1_funct_1 @ E ) & 
% 0.39/0.58                         ( v1_funct_2 @
% 0.39/0.58                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.39/0.58                         ( m1_subset_1 @
% 0.39/0.58                           E @ 
% 0.39/0.58                           ( k1_zfmisc_1 @
% 0.39/0.58                             ( k2_zfmisc_1 @
% 0.39/0.58                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.39/0.58                       ( ( m1_pre_topc @ C @ D ) =>
% 0.39/0.58                         ( ![F:$i]:
% 0.39/0.58                           ( ( m1_subset_1 @
% 0.39/0.58                               F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ D ) ) ) =>
% 0.39/0.58                             ( ![G:$i]:
% 0.39/0.58                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.39/0.58                                 ( ![H:$i]:
% 0.39/0.58                                   ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) ) =>
% 0.39/0.58                                     ( ( ( v3_pre_topc @ F @ D ) & 
% 0.39/0.58                                         ( r2_hidden @ G @ F ) & 
% 0.39/0.58                                         ( r1_tarski @ F @ ( u1_struct_0 @ C ) ) & 
% 0.39/0.58                                         ( ( G ) = ( H ) ) ) =>
% 0.39/0.58                                       ( ( r1_tmap_1 @ D @ B @ E @ G ) <=>
% 0.39/0.58                                         ( r1_tmap_1 @
% 0.39/0.58                                           C @ B @ 
% 0.39/0.58                                           ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ 
% 0.39/0.58                                           H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.39/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.58    (~( ![A:$i]:
% 0.39/0.58        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.39/0.58            ( l1_pre_topc @ A ) ) =>
% 0.39/0.58          ( ![B:$i]:
% 0.39/0.58            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.39/0.58                ( l1_pre_topc @ B ) ) =>
% 0.39/0.58              ( ![C:$i]:
% 0.39/0.58                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.39/0.58                  ( ![D:$i]:
% 0.39/0.58                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.39/0.58                      ( ![E:$i]:
% 0.39/0.58                        ( ( ( v1_funct_1 @ E ) & 
% 0.39/0.58                            ( v1_funct_2 @
% 0.39/0.58                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.39/0.58                            ( m1_subset_1 @
% 0.39/0.58                              E @ 
% 0.39/0.58                              ( k1_zfmisc_1 @
% 0.39/0.58                                ( k2_zfmisc_1 @
% 0.39/0.58                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.39/0.58                          ( ( m1_pre_topc @ C @ D ) =>
% 0.39/0.58                            ( ![F:$i]:
% 0.39/0.58                              ( ( m1_subset_1 @
% 0.39/0.58                                  F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ D ) ) ) =>
% 0.39/0.58                                ( ![G:$i]:
% 0.39/0.58                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.39/0.58                                    ( ![H:$i]:
% 0.39/0.58                                      ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) ) =>
% 0.39/0.58                                        ( ( ( v3_pre_topc @ F @ D ) & 
% 0.39/0.58                                            ( r2_hidden @ G @ F ) & 
% 0.39/0.58                                            ( r1_tarski @
% 0.39/0.58                                              F @ ( u1_struct_0 @ C ) ) & 
% 0.39/0.58                                            ( ( G ) = ( H ) ) ) =>
% 0.39/0.58                                          ( ( r1_tmap_1 @ D @ B @ E @ G ) <=>
% 0.39/0.58                                            ( r1_tmap_1 @
% 0.39/0.58                                              C @ B @ 
% 0.39/0.58                                              ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ 
% 0.39/0.58                                              H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.39/0.58    inference('cnf.neg', [status(esa)], [t84_tmap_1])).
% 0.39/0.58  thf('0', plain, (~ (v2_struct_0 @ sk_C)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('1', plain,
% 0.39/0.58      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('2', plain,
% 0.39/0.58      (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.39/0.58         (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_H)
% 0.39/0.58        | (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('3', plain,
% 0.39/0.58      (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.39/0.58         (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_H))
% 0.39/0.58         <= (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.39/0.58               (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_H)))),
% 0.39/0.58      inference('split', [status(esa)], ['2'])).
% 0.39/0.58  thf('4', plain,
% 0.39/0.58      ((~ (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.39/0.58           (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_H)
% 0.39/0.58        | ~ (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('5', plain, (((sk_G) = (sk_H))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('6', plain,
% 0.39/0.58      ((~ (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.39/0.58           (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_H)
% 0.39/0.58        | ~ (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H))),
% 0.39/0.58      inference('demod', [status(thm)], ['4', '5'])).
% 0.39/0.58  thf('7', plain,
% 0.39/0.58      (~ ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H)) | 
% 0.39/0.58       ~
% 0.39/0.58       ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.39/0.58         (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_H))),
% 0.39/0.58      inference('split', [status(esa)], ['6'])).
% 0.39/0.58  thf('8', plain,
% 0.39/0.58      (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.39/0.58         (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_H)
% 0.39/0.58        | (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('9', plain, (((sk_G) = (sk_H))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('10', plain,
% 0.39/0.58      (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.39/0.58         (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_H)
% 0.39/0.58        | (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H))),
% 0.39/0.58      inference('demod', [status(thm)], ['8', '9'])).
% 0.39/0.58  thf('11', plain,
% 0.39/0.58      (((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H))
% 0.39/0.58         <= (((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H)))),
% 0.39/0.58      inference('split', [status(esa)], ['10'])).
% 0.39/0.58  thf('12', plain,
% 0.39/0.58      ((~ (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.39/0.58           (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_H)
% 0.39/0.58        | ~ (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('13', plain,
% 0.39/0.58      ((~ (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G))
% 0.39/0.58         <= (~ ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G)))),
% 0.39/0.58      inference('split', [status(esa)], ['12'])).
% 0.39/0.58  thf('14', plain, (((sk_G) = (sk_H))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('15', plain,
% 0.39/0.58      ((~ (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H))
% 0.39/0.58         <= (~ ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G)))),
% 0.39/0.58      inference('demod', [status(thm)], ['13', '14'])).
% 0.39/0.58  thf('16', plain,
% 0.39/0.58      (~ ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H)) | 
% 0.39/0.58       ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G))),
% 0.39/0.58      inference('sup-', [status(thm)], ['11', '15'])).
% 0.39/0.58  thf('17', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('18', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_C))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('19', plain,
% 0.39/0.58      (((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G))
% 0.39/0.58         <= (((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G)))),
% 0.39/0.58      inference('split', [status(esa)], ['2'])).
% 0.39/0.58  thf('20', plain, (((sk_G) = (sk_H))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('21', plain,
% 0.39/0.58      (((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H))
% 0.39/0.58         <= (((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G)))),
% 0.39/0.58      inference('demod', [status(thm)], ['19', '20'])).
% 0.39/0.58  thf('22', plain,
% 0.39/0.58      ((m1_subset_1 @ sk_E @ 
% 0.39/0.58        (k1_zfmisc_1 @ 
% 0.39/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B))))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf(t81_tmap_1, axiom,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.58       ( ![B:$i]:
% 0.39/0.58         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.39/0.58             ( l1_pre_topc @ B ) ) =>
% 0.39/0.58           ( ![C:$i]:
% 0.39/0.58             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.39/0.58               ( ![D:$i]:
% 0.39/0.58                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.39/0.58                   ( ![E:$i]:
% 0.39/0.58                     ( ( ( v1_funct_1 @ E ) & 
% 0.39/0.58                         ( v1_funct_2 @
% 0.39/0.58                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.39/0.58                         ( m1_subset_1 @
% 0.39/0.58                           E @ 
% 0.39/0.58                           ( k1_zfmisc_1 @
% 0.39/0.58                             ( k2_zfmisc_1 @
% 0.39/0.58                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.39/0.58                       ( ![F:$i]:
% 0.39/0.58                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ C ) ) =>
% 0.39/0.58                           ( ![G:$i]:
% 0.39/0.58                             ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.39/0.58                               ( ( ( ( F ) = ( G ) ) & 
% 0.39/0.58                                   ( m1_pre_topc @ D @ C ) & 
% 0.39/0.58                                   ( r1_tmap_1 @ C @ B @ E @ F ) ) =>
% 0.39/0.58                                 ( r1_tmap_1 @
% 0.39/0.58                                   D @ B @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ 
% 0.39/0.58                                   G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.39/0.58  thf('23', plain,
% 0.39/0.58      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.39/0.58         ((v2_struct_0 @ X11)
% 0.39/0.58          | ~ (v2_pre_topc @ X11)
% 0.39/0.58          | ~ (l1_pre_topc @ X11)
% 0.39/0.58          | (v2_struct_0 @ X12)
% 0.39/0.58          | ~ (m1_pre_topc @ X12 @ X13)
% 0.39/0.58          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X15))
% 0.39/0.58          | ~ (m1_pre_topc @ X12 @ X15)
% 0.39/0.58          | ~ (r1_tmap_1 @ X15 @ X11 @ X16 @ X14)
% 0.39/0.58          | ((X14) != (X17))
% 0.39/0.58          | (r1_tmap_1 @ X12 @ X11 @ 
% 0.39/0.58             (k3_tmap_1 @ X13 @ X11 @ X15 @ X12 @ X16) @ X17)
% 0.39/0.58          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X12))
% 0.39/0.58          | ~ (m1_subset_1 @ X16 @ 
% 0.39/0.58               (k1_zfmisc_1 @ 
% 0.39/0.58                (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X11))))
% 0.39/0.58          | ~ (v1_funct_2 @ X16 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X11))
% 0.39/0.58          | ~ (v1_funct_1 @ X16)
% 0.39/0.58          | ~ (m1_pre_topc @ X15 @ X13)
% 0.39/0.58          | (v2_struct_0 @ X15)
% 0.39/0.58          | ~ (l1_pre_topc @ X13)
% 0.39/0.58          | ~ (v2_pre_topc @ X13)
% 0.39/0.58          | (v2_struct_0 @ X13))),
% 0.39/0.58      inference('cnf', [status(esa)], [t81_tmap_1])).
% 0.39/0.58  thf('24', plain,
% 0.39/0.58      (![X11 : $i, X12 : $i, X13 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.39/0.58         ((v2_struct_0 @ X13)
% 0.39/0.58          | ~ (v2_pre_topc @ X13)
% 0.39/0.58          | ~ (l1_pre_topc @ X13)
% 0.39/0.58          | (v2_struct_0 @ X15)
% 0.39/0.58          | ~ (m1_pre_topc @ X15 @ X13)
% 0.39/0.58          | ~ (v1_funct_1 @ X16)
% 0.39/0.58          | ~ (v1_funct_2 @ X16 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X11))
% 0.39/0.58          | ~ (m1_subset_1 @ X16 @ 
% 0.39/0.58               (k1_zfmisc_1 @ 
% 0.39/0.58                (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X11))))
% 0.39/0.58          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X12))
% 0.39/0.58          | (r1_tmap_1 @ X12 @ X11 @ 
% 0.39/0.58             (k3_tmap_1 @ X13 @ X11 @ X15 @ X12 @ X16) @ X17)
% 0.39/0.58          | ~ (r1_tmap_1 @ X15 @ X11 @ X16 @ X17)
% 0.39/0.58          | ~ (m1_pre_topc @ X12 @ X15)
% 0.39/0.58          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X15))
% 0.39/0.58          | ~ (m1_pre_topc @ X12 @ X13)
% 0.39/0.58          | (v2_struct_0 @ X12)
% 0.39/0.58          | ~ (l1_pre_topc @ X11)
% 0.39/0.58          | ~ (v2_pre_topc @ X11)
% 0.39/0.58          | (v2_struct_0 @ X11))),
% 0.39/0.58      inference('simplify', [status(thm)], ['23'])).
% 0.39/0.58  thf('25', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.58         ((v2_struct_0 @ sk_B)
% 0.39/0.58          | ~ (v2_pre_topc @ sk_B)
% 0.39/0.58          | ~ (l1_pre_topc @ sk_B)
% 0.39/0.58          | (v2_struct_0 @ X0)
% 0.39/0.58          | ~ (m1_pre_topc @ X0 @ X1)
% 0.39/0.58          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D_1))
% 0.39/0.58          | ~ (m1_pre_topc @ X0 @ sk_D_1)
% 0.39/0.58          | ~ (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ X2)
% 0.39/0.58          | (r1_tmap_1 @ X0 @ sk_B @ 
% 0.39/0.58             (k3_tmap_1 @ X1 @ sk_B @ sk_D_1 @ X0 @ sk_E) @ X2)
% 0.39/0.58          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.39/0.58          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D_1) @ 
% 0.39/0.58               (u1_struct_0 @ sk_B))
% 0.39/0.58          | ~ (v1_funct_1 @ sk_E)
% 0.39/0.58          | ~ (m1_pre_topc @ sk_D_1 @ X1)
% 0.39/0.58          | (v2_struct_0 @ sk_D_1)
% 0.39/0.58          | ~ (l1_pre_topc @ X1)
% 0.39/0.58          | ~ (v2_pre_topc @ X1)
% 0.39/0.58          | (v2_struct_0 @ X1))),
% 0.39/0.58      inference('sup-', [status(thm)], ['22', '24'])).
% 0.39/0.58  thf('26', plain, ((v2_pre_topc @ sk_B)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('27', plain, ((l1_pre_topc @ sk_B)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('28', plain,
% 0.39/0.58      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('29', plain, ((v1_funct_1 @ sk_E)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('30', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.58         ((v2_struct_0 @ sk_B)
% 0.39/0.58          | (v2_struct_0 @ X0)
% 0.39/0.58          | ~ (m1_pre_topc @ X0 @ X1)
% 0.39/0.58          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D_1))
% 0.39/0.58          | ~ (m1_pre_topc @ X0 @ sk_D_1)
% 0.39/0.58          | ~ (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ X2)
% 0.39/0.58          | (r1_tmap_1 @ X0 @ sk_B @ 
% 0.39/0.58             (k3_tmap_1 @ X1 @ sk_B @ sk_D_1 @ X0 @ sk_E) @ X2)
% 0.39/0.58          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.39/0.58          | ~ (m1_pre_topc @ sk_D_1 @ X1)
% 0.39/0.58          | (v2_struct_0 @ sk_D_1)
% 0.39/0.58          | ~ (l1_pre_topc @ X1)
% 0.39/0.58          | ~ (v2_pre_topc @ X1)
% 0.39/0.58          | (v2_struct_0 @ X1))),
% 0.39/0.58      inference('demod', [status(thm)], ['25', '26', '27', '28', '29'])).
% 0.39/0.58  thf('31', plain,
% 0.39/0.58      ((![X0 : $i, X1 : $i]:
% 0.39/0.58          ((v2_struct_0 @ X0)
% 0.39/0.58           | ~ (v2_pre_topc @ X0)
% 0.39/0.58           | ~ (l1_pre_topc @ X0)
% 0.39/0.58           | (v2_struct_0 @ sk_D_1)
% 0.39/0.58           | ~ (m1_pre_topc @ sk_D_1 @ X0)
% 0.39/0.58           | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ X1))
% 0.39/0.58           | (r1_tmap_1 @ X1 @ sk_B @ 
% 0.39/0.58              (k3_tmap_1 @ X0 @ sk_B @ sk_D_1 @ X1 @ sk_E) @ sk_H)
% 0.39/0.58           | ~ (m1_pre_topc @ X1 @ sk_D_1)
% 0.39/0.58           | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D_1))
% 0.39/0.58           | ~ (m1_pre_topc @ X1 @ X0)
% 0.39/0.58           | (v2_struct_0 @ X1)
% 0.39/0.58           | (v2_struct_0 @ sk_B)))
% 0.39/0.58         <= (((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['21', '30'])).
% 0.39/0.58  thf('32', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_D_1))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('33', plain, (((sk_G) = (sk_H))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('34', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D_1))),
% 0.39/0.58      inference('demod', [status(thm)], ['32', '33'])).
% 0.39/0.58  thf('35', plain,
% 0.39/0.58      ((![X0 : $i, X1 : $i]:
% 0.39/0.58          ((v2_struct_0 @ X0)
% 0.39/0.58           | ~ (v2_pre_topc @ X0)
% 0.39/0.58           | ~ (l1_pre_topc @ X0)
% 0.39/0.58           | (v2_struct_0 @ sk_D_1)
% 0.39/0.58           | ~ (m1_pre_topc @ sk_D_1 @ X0)
% 0.39/0.58           | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ X1))
% 0.39/0.58           | (r1_tmap_1 @ X1 @ sk_B @ 
% 0.39/0.58              (k3_tmap_1 @ X0 @ sk_B @ sk_D_1 @ X1 @ sk_E) @ sk_H)
% 0.39/0.58           | ~ (m1_pre_topc @ X1 @ sk_D_1)
% 0.39/0.58           | ~ (m1_pre_topc @ X1 @ X0)
% 0.39/0.58           | (v2_struct_0 @ X1)
% 0.39/0.58           | (v2_struct_0 @ sk_B)))
% 0.39/0.58         <= (((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G)))),
% 0.39/0.58      inference('demod', [status(thm)], ['31', '34'])).
% 0.39/0.58  thf('36', plain,
% 0.39/0.58      ((![X0 : $i]:
% 0.39/0.58          ((v2_struct_0 @ sk_B)
% 0.39/0.58           | (v2_struct_0 @ sk_C)
% 0.39/0.58           | ~ (m1_pre_topc @ sk_C @ X0)
% 0.39/0.58           | ~ (m1_pre_topc @ sk_C @ sk_D_1)
% 0.39/0.58           | (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.39/0.58              (k3_tmap_1 @ X0 @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_H)
% 0.39/0.58           | ~ (m1_pre_topc @ sk_D_1 @ X0)
% 0.39/0.58           | (v2_struct_0 @ sk_D_1)
% 0.39/0.58           | ~ (l1_pre_topc @ X0)
% 0.39/0.58           | ~ (v2_pre_topc @ X0)
% 0.39/0.58           | (v2_struct_0 @ X0)))
% 0.39/0.58         <= (((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['18', '35'])).
% 0.39/0.58  thf('37', plain, ((m1_pre_topc @ sk_C @ sk_D_1)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('38', plain,
% 0.39/0.58      ((![X0 : $i]:
% 0.39/0.58          ((v2_struct_0 @ sk_B)
% 0.39/0.58           | (v2_struct_0 @ sk_C)
% 0.39/0.58           | ~ (m1_pre_topc @ sk_C @ X0)
% 0.39/0.58           | (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.39/0.58              (k3_tmap_1 @ X0 @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_H)
% 0.39/0.58           | ~ (m1_pre_topc @ sk_D_1 @ X0)
% 0.39/0.58           | (v2_struct_0 @ sk_D_1)
% 0.39/0.58           | ~ (l1_pre_topc @ X0)
% 0.39/0.58           | ~ (v2_pre_topc @ X0)
% 0.39/0.58           | (v2_struct_0 @ X0)))
% 0.39/0.58         <= (((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G)))),
% 0.39/0.58      inference('demod', [status(thm)], ['36', '37'])).
% 0.39/0.58  thf('39', plain,
% 0.39/0.58      ((((v2_struct_0 @ sk_A)
% 0.39/0.58         | ~ (v2_pre_topc @ sk_A)
% 0.39/0.58         | ~ (l1_pre_topc @ sk_A)
% 0.39/0.58         | (v2_struct_0 @ sk_D_1)
% 0.39/0.58         | ~ (m1_pre_topc @ sk_D_1 @ sk_A)
% 0.39/0.58         | (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.39/0.58            (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_H)
% 0.39/0.58         | (v2_struct_0 @ sk_C)
% 0.39/0.58         | (v2_struct_0 @ sk_B)))
% 0.39/0.58         <= (((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['17', '38'])).
% 0.39/0.58  thf('40', plain, ((v2_pre_topc @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('42', plain, ((m1_pre_topc @ sk_D_1 @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('43', plain,
% 0.39/0.58      ((((v2_struct_0 @ sk_A)
% 0.39/0.58         | (v2_struct_0 @ sk_D_1)
% 0.39/0.58         | (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.39/0.58            (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_H)
% 0.39/0.58         | (v2_struct_0 @ sk_C)
% 0.39/0.58         | (v2_struct_0 @ sk_B)))
% 0.39/0.58         <= (((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G)))),
% 0.39/0.58      inference('demod', [status(thm)], ['39', '40', '41', '42'])).
% 0.39/0.58  thf('44', plain,
% 0.39/0.58      ((~ (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.39/0.58           (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_H))
% 0.39/0.58         <= (~
% 0.39/0.58             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.39/0.58               (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_H)))),
% 0.39/0.58      inference('split', [status(esa)], ['12'])).
% 0.39/0.58  thf('45', plain,
% 0.39/0.58      ((((v2_struct_0 @ sk_B)
% 0.39/0.58         | (v2_struct_0 @ sk_C)
% 0.39/0.58         | (v2_struct_0 @ sk_D_1)
% 0.39/0.58         | (v2_struct_0 @ sk_A)))
% 0.39/0.58         <= (~
% 0.39/0.58             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.39/0.58               (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_H)) & 
% 0.39/0.58             ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['43', '44'])).
% 0.39/0.58  thf('46', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('47', plain,
% 0.39/0.58      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B)))
% 0.39/0.58         <= (~
% 0.39/0.58             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.39/0.58               (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_H)) & 
% 0.39/0.58             ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['45', '46'])).
% 0.39/0.58  thf('48', plain, (~ (v2_struct_0 @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('49', plain,
% 0.39/0.58      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C)))
% 0.39/0.58         <= (~
% 0.39/0.58             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.39/0.58               (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_H)) & 
% 0.39/0.58             ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G)))),
% 0.39/0.58      inference('clc', [status(thm)], ['47', '48'])).
% 0.39/0.58  thf('50', plain, (~ (v2_struct_0 @ sk_B)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('51', plain,
% 0.39/0.58      (((v2_struct_0 @ sk_C))
% 0.39/0.58         <= (~
% 0.39/0.58             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.39/0.58               (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_H)) & 
% 0.39/0.58             ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G)))),
% 0.39/0.58      inference('clc', [status(thm)], ['49', '50'])).
% 0.39/0.58  thf('52', plain, (~ (v2_struct_0 @ sk_C)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('53', plain,
% 0.39/0.58      (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.39/0.58         (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_H)) | 
% 0.39/0.58       ~ ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G))),
% 0.39/0.58      inference('sup-', [status(thm)], ['51', '52'])).
% 0.39/0.58  thf('54', plain,
% 0.39/0.58      (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.39/0.58         (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_H)) | 
% 0.39/0.58       ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H))),
% 0.39/0.58      inference('split', [status(esa)], ['10'])).
% 0.39/0.58  thf('55', plain,
% 0.39/0.58      (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.39/0.58         (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_H))),
% 0.39/0.58      inference('sat_resolution*', [status(thm)], ['7', '16', '53', '54'])).
% 0.39/0.58  thf('56', plain,
% 0.39/0.58      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.39/0.58        (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_H)),
% 0.39/0.58      inference('simpl_trail', [status(thm)], ['3', '55'])).
% 0.39/0.58  thf('57', plain,
% 0.39/0.58      ((m1_subset_1 @ sk_E @ 
% 0.39/0.58        (k1_zfmisc_1 @ 
% 0.39/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B))))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf(t83_tmap_1, axiom,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.58       ( ![B:$i]:
% 0.39/0.58         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.39/0.58             ( l1_pre_topc @ B ) ) =>
% 0.39/0.58           ( ![C:$i]:
% 0.39/0.58             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.39/0.58               ( ![D:$i]:
% 0.39/0.58                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.39/0.58                   ( ![E:$i]:
% 0.39/0.58                     ( ( ( v1_funct_1 @ E ) & 
% 0.39/0.58                         ( v1_funct_2 @
% 0.39/0.58                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.39/0.58                         ( m1_subset_1 @
% 0.39/0.58                           E @ 
% 0.39/0.58                           ( k1_zfmisc_1 @
% 0.39/0.58                             ( k2_zfmisc_1 @
% 0.39/0.58                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.39/0.58                       ( ( m1_pre_topc @ C @ D ) =>
% 0.39/0.58                         ( ![F:$i]:
% 0.39/0.58                           ( ( m1_subset_1 @
% 0.39/0.58                               F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ D ) ) ) =>
% 0.39/0.58                             ( ![G:$i]:
% 0.39/0.58                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.39/0.58                                 ( ![H:$i]:
% 0.39/0.58                                   ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) ) =>
% 0.39/0.58                                     ( ( ( r1_tarski @ F @ ( u1_struct_0 @ C ) ) & 
% 0.39/0.58                                         ( m1_connsp_2 @ F @ D @ G ) & 
% 0.39/0.58                                         ( ( G ) = ( H ) ) ) =>
% 0.39/0.58                                       ( ( r1_tmap_1 @ D @ B @ E @ G ) <=>
% 0.39/0.58                                         ( r1_tmap_1 @
% 0.39/0.58                                           C @ B @ 
% 0.39/0.58                                           ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ 
% 0.39/0.58                                           H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.39/0.58  thf('58', plain,
% 0.39/0.58      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i, 
% 0.39/0.58         X25 : $i]:
% 0.39/0.58         ((v2_struct_0 @ X18)
% 0.39/0.58          | ~ (v2_pre_topc @ X18)
% 0.39/0.58          | ~ (l1_pre_topc @ X18)
% 0.39/0.58          | (v2_struct_0 @ X19)
% 0.39/0.58          | ~ (m1_pre_topc @ X19 @ X20)
% 0.39/0.58          | ~ (m1_pre_topc @ X21 @ X19)
% 0.39/0.58          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.39/0.58          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X21))
% 0.39/0.58          | ~ (r1_tmap_1 @ X21 @ X18 @ 
% 0.39/0.58               (k3_tmap_1 @ X20 @ X18 @ X19 @ X21 @ X24) @ X23)
% 0.39/0.58          | (r1_tmap_1 @ X19 @ X18 @ X24 @ X25)
% 0.39/0.58          | ((X25) != (X23))
% 0.39/0.58          | ~ (m1_connsp_2 @ X22 @ X19 @ X25)
% 0.39/0.58          | ~ (r1_tarski @ X22 @ (u1_struct_0 @ X21))
% 0.39/0.58          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X19))
% 0.39/0.58          | ~ (m1_subset_1 @ X24 @ 
% 0.39/0.58               (k1_zfmisc_1 @ 
% 0.39/0.58                (k2_zfmisc_1 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X18))))
% 0.39/0.58          | ~ (v1_funct_2 @ X24 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X18))
% 0.39/0.58          | ~ (v1_funct_1 @ X24)
% 0.39/0.58          | ~ (m1_pre_topc @ X21 @ X20)
% 0.39/0.58          | (v2_struct_0 @ X21)
% 0.39/0.58          | ~ (l1_pre_topc @ X20)
% 0.39/0.58          | ~ (v2_pre_topc @ X20)
% 0.39/0.58          | (v2_struct_0 @ X20))),
% 0.39/0.58      inference('cnf', [status(esa)], [t83_tmap_1])).
% 0.39/0.58  thf('59', plain,
% 0.39/0.58      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.39/0.58         ((v2_struct_0 @ X20)
% 0.39/0.58          | ~ (v2_pre_topc @ X20)
% 0.39/0.58          | ~ (l1_pre_topc @ X20)
% 0.39/0.58          | (v2_struct_0 @ X21)
% 0.39/0.58          | ~ (m1_pre_topc @ X21 @ X20)
% 0.39/0.58          | ~ (v1_funct_1 @ X24)
% 0.39/0.58          | ~ (v1_funct_2 @ X24 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X18))
% 0.39/0.58          | ~ (m1_subset_1 @ X24 @ 
% 0.39/0.58               (k1_zfmisc_1 @ 
% 0.39/0.58                (k2_zfmisc_1 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X18))))
% 0.39/0.58          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X19))
% 0.39/0.58          | ~ (r1_tarski @ X22 @ (u1_struct_0 @ X21))
% 0.39/0.58          | ~ (m1_connsp_2 @ X22 @ X19 @ X23)
% 0.39/0.58          | (r1_tmap_1 @ X19 @ X18 @ X24 @ X23)
% 0.39/0.58          | ~ (r1_tmap_1 @ X21 @ X18 @ 
% 0.39/0.58               (k3_tmap_1 @ X20 @ X18 @ X19 @ X21 @ X24) @ X23)
% 0.39/0.58          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X21))
% 0.39/0.58          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.39/0.58          | ~ (m1_pre_topc @ X21 @ X19)
% 0.39/0.58          | ~ (m1_pre_topc @ X19 @ X20)
% 0.39/0.58          | (v2_struct_0 @ X19)
% 0.39/0.58          | ~ (l1_pre_topc @ X18)
% 0.39/0.58          | ~ (v2_pre_topc @ X18)
% 0.39/0.58          | (v2_struct_0 @ X18))),
% 0.39/0.58      inference('simplify', [status(thm)], ['58'])).
% 0.39/0.58  thf('60', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.39/0.58         ((v2_struct_0 @ sk_B)
% 0.39/0.58          | ~ (v2_pre_topc @ sk_B)
% 0.39/0.58          | ~ (l1_pre_topc @ sk_B)
% 0.39/0.58          | (v2_struct_0 @ sk_D_1)
% 0.39/0.58          | ~ (m1_pre_topc @ sk_D_1 @ X0)
% 0.39/0.58          | ~ (m1_pre_topc @ X1 @ sk_D_1)
% 0.39/0.58          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.39/0.58          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.39/0.58          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.39/0.58               (k3_tmap_1 @ X0 @ sk_B @ sk_D_1 @ X1 @ sk_E) @ X3)
% 0.39/0.58          | (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ X3)
% 0.39/0.58          | ~ (m1_connsp_2 @ X2 @ sk_D_1 @ X3)
% 0.39/0.58          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X1))
% 0.39/0.58          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_D_1))
% 0.39/0.58          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D_1) @ 
% 0.39/0.58               (u1_struct_0 @ sk_B))
% 0.39/0.58          | ~ (v1_funct_1 @ sk_E)
% 0.39/0.58          | ~ (m1_pre_topc @ X1 @ X0)
% 0.39/0.58          | (v2_struct_0 @ X1)
% 0.39/0.58          | ~ (l1_pre_topc @ X0)
% 0.39/0.58          | ~ (v2_pre_topc @ X0)
% 0.39/0.58          | (v2_struct_0 @ X0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['57', '59'])).
% 0.39/0.58  thf('61', plain, ((v2_pre_topc @ sk_B)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('62', plain, ((l1_pre_topc @ sk_B)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('63', plain,
% 0.39/0.58      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('64', plain, ((v1_funct_1 @ sk_E)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('65', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.39/0.58         ((v2_struct_0 @ sk_B)
% 0.39/0.58          | (v2_struct_0 @ sk_D_1)
% 0.39/0.58          | ~ (m1_pre_topc @ sk_D_1 @ X0)
% 0.39/0.58          | ~ (m1_pre_topc @ X1 @ sk_D_1)
% 0.39/0.58          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.39/0.58          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.39/0.58          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.39/0.58               (k3_tmap_1 @ X0 @ sk_B @ sk_D_1 @ X1 @ sk_E) @ X3)
% 0.39/0.58          | (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ X3)
% 0.39/0.58          | ~ (m1_connsp_2 @ X2 @ sk_D_1 @ X3)
% 0.39/0.58          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X1))
% 0.39/0.58          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_D_1))
% 0.39/0.58          | ~ (m1_pre_topc @ X1 @ X0)
% 0.39/0.58          | (v2_struct_0 @ X1)
% 0.39/0.58          | ~ (l1_pre_topc @ X0)
% 0.39/0.58          | ~ (v2_pre_topc @ X0)
% 0.39/0.58          | (v2_struct_0 @ X0))),
% 0.39/0.58      inference('demod', [status(thm)], ['60', '61', '62', '63', '64'])).
% 0.39/0.58  thf('66', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         ((v2_struct_0 @ sk_A)
% 0.39/0.58          | ~ (v2_pre_topc @ sk_A)
% 0.39/0.58          | ~ (l1_pre_topc @ sk_A)
% 0.39/0.58          | (v2_struct_0 @ sk_C)
% 0.39/0.58          | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.39/0.58          | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D_1))
% 0.39/0.58          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C))
% 0.39/0.58          | ~ (m1_connsp_2 @ X0 @ sk_D_1 @ sk_H)
% 0.39/0.58          | (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H)
% 0.39/0.58          | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_C))
% 0.39/0.58          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.39/0.58          | ~ (m1_pre_topc @ sk_C @ sk_D_1)
% 0.39/0.58          | ~ (m1_pre_topc @ sk_D_1 @ sk_A)
% 0.39/0.58          | (v2_struct_0 @ sk_D_1)
% 0.39/0.58          | (v2_struct_0 @ sk_B))),
% 0.39/0.58      inference('sup-', [status(thm)], ['56', '65'])).
% 0.39/0.58  thf('67', plain, ((v2_pre_topc @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('68', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('69', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('70', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D_1))),
% 0.39/0.58      inference('demod', [status(thm)], ['32', '33'])).
% 0.39/0.58  thf('71', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_C))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('72', plain, ((m1_pre_topc @ sk_C @ sk_D_1)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('73', plain, ((m1_pre_topc @ sk_D_1 @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('74', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         ((v2_struct_0 @ sk_A)
% 0.39/0.58          | (v2_struct_0 @ sk_C)
% 0.39/0.58          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C))
% 0.39/0.58          | ~ (m1_connsp_2 @ X0 @ sk_D_1 @ sk_H)
% 0.39/0.58          | (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H)
% 0.39/0.58          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.39/0.58          | (v2_struct_0 @ sk_D_1)
% 0.39/0.58          | (v2_struct_0 @ sk_B))),
% 0.39/0.58      inference('demod', [status(thm)],
% 0.39/0.58                ['66', '67', '68', '69', '70', '71', '72', '73'])).
% 0.39/0.58  thf('75', plain,
% 0.39/0.58      (((v2_struct_0 @ sk_B)
% 0.39/0.58        | (v2_struct_0 @ sk_D_1)
% 0.39/0.58        | (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H)
% 0.39/0.58        | ~ (m1_connsp_2 @ sk_F @ sk_D_1 @ sk_H)
% 0.39/0.58        | ~ (r1_tarski @ sk_F @ (u1_struct_0 @ sk_C))
% 0.39/0.58        | (v2_struct_0 @ sk_C)
% 0.39/0.58        | (v2_struct_0 @ sk_A))),
% 0.39/0.58      inference('sup-', [status(thm)], ['1', '74'])).
% 0.39/0.58  thf('76', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D_1))),
% 0.39/0.58      inference('demod', [status(thm)], ['32', '33'])).
% 0.39/0.58  thf('77', plain,
% 0.39/0.58      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('78', plain,
% 0.39/0.58      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf(t8_connsp_2, axiom,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.58       ( ![B:$i]:
% 0.39/0.58         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.39/0.58           ( ![C:$i]:
% 0.39/0.58             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.58               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 0.39/0.58                 ( ?[D:$i]:
% 0.39/0.58                   ( ( r2_hidden @ B @ D ) & ( r1_tarski @ D @ C ) & 
% 0.39/0.58                     ( v3_pre_topc @ D @ A ) & 
% 0.39/0.58                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) ) ))).
% 0.39/0.58  thf('79', plain,
% 0.39/0.58      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.39/0.58         (~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X8))
% 0.39/0.58          | ~ (r2_hidden @ X7 @ X10)
% 0.39/0.58          | ~ (r1_tarski @ X10 @ X9)
% 0.39/0.58          | ~ (v3_pre_topc @ X10 @ X8)
% 0.39/0.58          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.39/0.58          | (m1_connsp_2 @ X9 @ X8 @ X7)
% 0.39/0.58          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.39/0.58          | ~ (l1_pre_topc @ X8)
% 0.39/0.58          | ~ (v2_pre_topc @ X8)
% 0.39/0.58          | (v2_struct_0 @ X8))),
% 0.39/0.58      inference('cnf', [status(esa)], [t8_connsp_2])).
% 0.39/0.58  thf('80', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         ((v2_struct_0 @ sk_D_1)
% 0.39/0.58          | ~ (v2_pre_topc @ sk_D_1)
% 0.39/0.58          | ~ (l1_pre_topc @ sk_D_1)
% 0.39/0.58          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.39/0.58          | (m1_connsp_2 @ X0 @ sk_D_1 @ X1)
% 0.39/0.58          | ~ (v3_pre_topc @ sk_F @ sk_D_1)
% 0.39/0.58          | ~ (r1_tarski @ sk_F @ X0)
% 0.39/0.58          | ~ (r2_hidden @ X1 @ sk_F)
% 0.39/0.58          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D_1)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['78', '79'])).
% 0.39/0.58  thf('81', plain, ((m1_pre_topc @ sk_D_1 @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf(cc1_pre_topc, axiom,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.58       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.39/0.58  thf('82', plain,
% 0.39/0.58      (![X3 : $i, X4 : $i]:
% 0.39/0.58         (~ (m1_pre_topc @ X3 @ X4)
% 0.39/0.58          | (v2_pre_topc @ X3)
% 0.39/0.58          | ~ (l1_pre_topc @ X4)
% 0.39/0.58          | ~ (v2_pre_topc @ X4))),
% 0.39/0.58      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.39/0.58  thf('83', plain,
% 0.39/0.58      ((~ (v2_pre_topc @ sk_A)
% 0.39/0.58        | ~ (l1_pre_topc @ sk_A)
% 0.39/0.58        | (v2_pre_topc @ sk_D_1))),
% 0.39/0.58      inference('sup-', [status(thm)], ['81', '82'])).
% 0.39/0.58  thf('84', plain, ((v2_pre_topc @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('85', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('86', plain, ((v2_pre_topc @ sk_D_1)),
% 0.39/0.58      inference('demod', [status(thm)], ['83', '84', '85'])).
% 0.39/0.58  thf('87', plain, ((m1_pre_topc @ sk_D_1 @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf(dt_m1_pre_topc, axiom,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( l1_pre_topc @ A ) =>
% 0.39/0.58       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.39/0.58  thf('88', plain,
% 0.39/0.58      (![X5 : $i, X6 : $i]:
% 0.39/0.58         (~ (m1_pre_topc @ X5 @ X6) | (l1_pre_topc @ X5) | ~ (l1_pre_topc @ X6))),
% 0.39/0.58      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.39/0.58  thf('89', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D_1))),
% 0.39/0.58      inference('sup-', [status(thm)], ['87', '88'])).
% 0.39/0.58  thf('90', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('91', plain, ((l1_pre_topc @ sk_D_1)),
% 0.39/0.58      inference('demod', [status(thm)], ['89', '90'])).
% 0.39/0.58  thf('92', plain, ((v3_pre_topc @ sk_F @ sk_D_1)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('93', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         ((v2_struct_0 @ sk_D_1)
% 0.39/0.58          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.39/0.58          | (m1_connsp_2 @ X0 @ sk_D_1 @ X1)
% 0.39/0.58          | ~ (r1_tarski @ sk_F @ X0)
% 0.39/0.58          | ~ (r2_hidden @ X1 @ sk_F)
% 0.39/0.58          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D_1)))),
% 0.39/0.58      inference('demod', [status(thm)], ['80', '86', '91', '92'])).
% 0.39/0.58  thf('94', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.39/0.58          | ~ (r2_hidden @ X0 @ sk_F)
% 0.39/0.58          | ~ (r1_tarski @ sk_F @ sk_F)
% 0.39/0.58          | (m1_connsp_2 @ sk_F @ sk_D_1 @ X0)
% 0.39/0.58          | (v2_struct_0 @ sk_D_1))),
% 0.39/0.58      inference('sup-', [status(thm)], ['77', '93'])).
% 0.39/0.58  thf(d10_xboole_0, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.39/0.58  thf('95', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.39/0.58      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.39/0.58  thf('96', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.39/0.58      inference('simplify', [status(thm)], ['95'])).
% 0.39/0.58  thf('97', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.39/0.58          | ~ (r2_hidden @ X0 @ sk_F)
% 0.39/0.58          | (m1_connsp_2 @ sk_F @ sk_D_1 @ X0)
% 0.39/0.58          | (v2_struct_0 @ sk_D_1))),
% 0.39/0.58      inference('demod', [status(thm)], ['94', '96'])).
% 0.39/0.58  thf('98', plain,
% 0.39/0.58      (((v2_struct_0 @ sk_D_1)
% 0.39/0.58        | (m1_connsp_2 @ sk_F @ sk_D_1 @ sk_H)
% 0.39/0.58        | ~ (r2_hidden @ sk_H @ sk_F))),
% 0.39/0.58      inference('sup-', [status(thm)], ['76', '97'])).
% 0.39/0.58  thf('99', plain, ((r2_hidden @ sk_G @ sk_F)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('100', plain, (((sk_G) = (sk_H))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('101', plain, ((r2_hidden @ sk_H @ sk_F)),
% 0.39/0.58      inference('demod', [status(thm)], ['99', '100'])).
% 0.39/0.58  thf('102', plain,
% 0.39/0.58      (((v2_struct_0 @ sk_D_1) | (m1_connsp_2 @ sk_F @ sk_D_1 @ sk_H))),
% 0.39/0.58      inference('demod', [status(thm)], ['98', '101'])).
% 0.39/0.58  thf('103', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('104', plain, ((m1_connsp_2 @ sk_F @ sk_D_1 @ sk_H)),
% 0.39/0.58      inference('clc', [status(thm)], ['102', '103'])).
% 0.39/0.58  thf('105', plain, ((r1_tarski @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('106', plain,
% 0.39/0.58      (((v2_struct_0 @ sk_B)
% 0.39/0.58        | (v2_struct_0 @ sk_D_1)
% 0.39/0.58        | (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H)
% 0.39/0.58        | (v2_struct_0 @ sk_C)
% 0.39/0.58        | (v2_struct_0 @ sk_A))),
% 0.39/0.58      inference('demod', [status(thm)], ['75', '104', '105'])).
% 0.39/0.58  thf('107', plain,
% 0.39/0.58      ((~ (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H))
% 0.39/0.58         <= (~ ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G)))),
% 0.39/0.58      inference('demod', [status(thm)], ['13', '14'])).
% 0.39/0.58  thf('108', plain,
% 0.39/0.58      (((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H))
% 0.39/0.58         <= (((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G)))),
% 0.39/0.58      inference('demod', [status(thm)], ['19', '20'])).
% 0.39/0.58  thf('109', plain,
% 0.39/0.58      ((~ (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H))
% 0.39/0.58         <= (~ ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H)))),
% 0.39/0.58      inference('split', [status(esa)], ['6'])).
% 0.39/0.58  thf('110', plain,
% 0.39/0.58      (~ ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G)) | 
% 0.39/0.58       ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H))),
% 0.39/0.58      inference('sup-', [status(thm)], ['108', '109'])).
% 0.39/0.58  thf('111', plain, (~ ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_G))),
% 0.39/0.58      inference('sat_resolution*', [status(thm)], ['7', '16', '53', '110'])).
% 0.39/0.58  thf('112', plain, (~ (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_H)),
% 0.39/0.58      inference('simpl_trail', [status(thm)], ['107', '111'])).
% 0.39/0.58  thf('113', plain,
% 0.39/0.58      (((v2_struct_0 @ sk_A)
% 0.39/0.58        | (v2_struct_0 @ sk_C)
% 0.39/0.58        | (v2_struct_0 @ sk_D_1)
% 0.39/0.58        | (v2_struct_0 @ sk_B))),
% 0.39/0.58      inference('sup-', [status(thm)], ['106', '112'])).
% 0.39/0.58  thf('114', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('115', plain,
% 0.39/0.58      (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A))),
% 0.39/0.58      inference('sup-', [status(thm)], ['113', '114'])).
% 0.39/0.58  thf('116', plain, (~ (v2_struct_0 @ sk_B)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('117', plain, (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C))),
% 0.39/0.58      inference('clc', [status(thm)], ['115', '116'])).
% 0.39/0.58  thf('118', plain, (~ (v2_struct_0 @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('119', plain, ((v2_struct_0 @ sk_C)),
% 0.39/0.58      inference('clc', [status(thm)], ['117', '118'])).
% 0.39/0.58  thf('120', plain, ($false), inference('demod', [status(thm)], ['0', '119'])).
% 0.39/0.58  
% 0.39/0.58  % SZS output end Refutation
% 0.39/0.58  
% 0.39/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
