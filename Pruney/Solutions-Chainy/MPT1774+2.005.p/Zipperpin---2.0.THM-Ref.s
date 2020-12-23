%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Oo23nZ9sGr

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:17 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  216 ( 858 expanded)
%              Number of leaves         :   37 ( 256 expanded)
%              Depth                    :   26
%              Number of atoms          : 2742 (37031 expanded)
%              Number of equality atoms :   43 ( 479 expanded)
%              Maximal formula depth    :   33 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

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
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    r1_tarski @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('4',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t39_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
             => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('5',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X10 @ X11 )
      | ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t39_pre_topc])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
    | ~ ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('9',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( l1_pre_topc @ X8 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('10',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['7','12'])).

thf('14',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H )
   <= ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H ) ),
    inference(split,[status(esa)],['14'])).

thf('16',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( m1_pre_topc @ C @ A )
             => ! [D: $i] :
                  ( ( m1_pre_topc @ D @ A )
                 => ! [E: $i] :
                      ( ( ( v1_funct_1 @ E )
                        & ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) )
                     => ( ( m1_pre_topc @ D @ C )
                       => ( ( k3_tmap_1 @ A @ B @ C @ D @ E )
                          = ( k2_partfun1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) )).

thf('19',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( v2_struct_0 @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( m1_pre_topc @ X25 @ X26 )
      | ~ ( m1_pre_topc @ X25 @ X27 )
      | ( ( k3_tmap_1 @ X26 @ X24 @ X27 @ X25 @ X28 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X24 ) @ X28 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X24 ) ) ) )
      | ~ ( v1_funct_2 @ X28 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X24 ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( m1_pre_topc @ X27 @ X26 )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d5_tmap_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21','22','23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','25'])).

thf('27',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['16','29'])).

thf('31',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_tmap_1,axiom,(
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
                  ( ( m1_pre_topc @ D @ A )
                 => ( ( k2_tmap_1 @ A @ B @ C @ D )
                    = ( k2_partfun1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ ( u1_struct_0 @ D ) ) ) ) ) ) ) )).

thf('33',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( v2_struct_0 @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( m1_pre_topc @ X21 @ X22 )
      | ( ( k2_tmap_1 @ X22 @ X20 @ X23 @ X21 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X20 ) @ X23 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X20 ) ) ) )
      | ~ ( v1_funct_2 @ X23 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X20 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('36',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_pre_topc @ X6 @ X7 )
      | ( v2_pre_topc @ X6 )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('37',plain,
    ( ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['10','11'])).

thf('42',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['34','40','41','42','43','44','45'])).

thf('47',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['31','46'])).

thf('48',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E )
      = ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['30','51','52'])).

thf('54',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E )
      = ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C ) ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('56',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E )
    = ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C ) @ sk_H )
   <= ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H ) ),
    inference(demod,[status(thm)],['15','57'])).

thf('59',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H )
    | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H )
    | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H )
    | ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H ) ),
    inference(split,[status(esa)],['61'])).

thf('63',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H ) ),
    inference(split,[status(esa)],['66'])).

thf('68',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ) ) ),
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

thf('69',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( v2_struct_0 @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ~ ( l1_pre_topc @ X32 )
      | ( v2_struct_0 @ X33 )
      | ~ ( m1_pre_topc @ X33 @ X32 )
      | ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ X33 ) )
      | ( r1_tmap_1 @ X33 @ X35 @ ( k2_tmap_1 @ X32 @ X35 @ X36 @ X33 ) @ X34 )
      | ( X37 != X34 )
      | ~ ( r1_tmap_1 @ X32 @ X35 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ X32 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X35 ) ) ) )
      | ~ ( v1_funct_2 @ X36 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X35 ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t64_tmap_1])).

thf('70',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( v2_struct_0 @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_funct_2 @ X36 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X35 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X35 ) ) ) )
      | ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ X32 ) )
      | ~ ( r1_tmap_1 @ X32 @ X35 @ X36 @ X34 )
      | ( r1_tmap_1 @ X33 @ X35 @ ( k2_tmap_1 @ X32 @ X35 @ X36 @ X33 ) @ X34 )
      | ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ X33 ) )
      | ~ ( m1_pre_topc @ X33 @ X32 )
      | ( v2_struct_0 @ X33 )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ~ ( l1_pre_topc @ sk_D )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0 ) @ X1 )
      | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['68','70'])).

thf('72',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('73',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['10','11'])).

thf('74',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0 ) @ X1 )
      | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_D ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['71','72','73','74','75','76','77'])).

thf('79',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_D ) )
        | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0 ) @ sk_H )
        | ~ ( m1_subset_1 @ sk_H @ ( u1_struct_0 @ X0 ) )
        | ~ ( m1_pre_topc @ X0 @ sk_D )
        | ( v2_struct_0 @ X0 )
        | ( v2_struct_0 @ sk_D ) )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H ) ),
    inference('sup-',[status(thm)],['67','78'])).

thf('80',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0 ) @ sk_H )
        | ~ ( m1_subset_1 @ sk_H @ ( u1_struct_0 @ X0 ) )
        | ~ ( m1_pre_topc @ X0 @ sk_D )
        | ( v2_struct_0 @ X0 )
        | ( v2_struct_0 @ sk_D ) )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H ) ),
    inference(demod,[status(thm)],['79','82'])).

thf('84',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ sk_D )
      | ( r1_tmap_1 @ sk_C @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C ) @ sk_H )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H ) ),
    inference('sup-',[status(thm)],['63','83'])).

thf('85',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( r1_tmap_1 @ sk_C @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C ) @ sk_H )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,
    ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E )
    = ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('88',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H )
    | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H )
   <= ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H ) ),
    inference(split,[status(esa)],['88'])).

thf('90',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C ) @ sk_H )
   <= ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H ) ),
    inference('sup-',[status(thm)],['87','89'])).

thf('91',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H )
      & ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H ) ) ),
    inference('sup-',[status(thm)],['86','90'])).

thf('92',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H )
      & ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H ) ) ),
    inference(clc,[status(thm)],['91','92'])).

thf('94',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( v2_struct_0 @ sk_C )
   <= ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H )
      & ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H ) ) ),
    inference(clc,[status(thm)],['93','94'])).

thf('96',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H )
    | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H ) ),
    inference(split,[status(esa)],['66'])).

thf('99',plain,(
    r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H ),
    inference('sat_resolution*',[status(thm)],['62','97','98'])).

thf('100',plain,(
    r1_tmap_1 @ sk_C @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C ) @ sk_H ),
    inference(simpl_trail,[status(thm)],['58','99'])).

thf('101',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('104',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['103'])).

thf(t4_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_pre_topc @ C @ A )
             => ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) )
              <=> ( m1_pre_topc @ B @ C ) ) ) ) ) )).

thf('105',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_pre_topc @ X29 @ X30 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X31 ) )
      | ( m1_pre_topc @ X29 @ X31 )
      | ~ ( m1_pre_topc @ X31 @ X30 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ( m1_pre_topc @ X0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_pre_topc @ X0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,
    ( ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ( m1_pre_topc @ sk_D @ sk_D ) ),
    inference('sup-',[status(thm)],['102','107'])).

thf('109',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    m1_pre_topc @ sk_D @ sk_D ),
    inference(demod,[status(thm)],['108','109','110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21','22','23','24'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_D @ sk_A @ sk_D @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['10','11'])).

thf('115',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_D @ sk_A @ sk_D @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['113','114','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_D @ sk_A @ sk_D @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['116'])).

thf('118',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_D @ sk_A @ sk_D @ sk_C @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['101','117'])).

thf('119',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( ( k3_tmap_1 @ sk_D @ sk_A @ sk_D @ sk_C @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['118','119'])).

thf('121',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( ( k3_tmap_1 @ sk_D @ sk_A @ sk_D @ sk_C @ sk_E )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['120','121'])).

thf('123',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('124',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C )
    = ( k3_tmap_1 @ sk_D @ sk_A @ sk_D @ sk_C @ sk_E ) ),
    inference('sup+',[status(thm)],['122','123'])).

thf('125',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t84_tmap_1,axiom,(
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

thf('126',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i,X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ( v2_struct_0 @ X41 )
      | ~ ( v2_pre_topc @ X41 )
      | ~ ( l1_pre_topc @ X41 )
      | ( v2_struct_0 @ X42 )
      | ~ ( m1_pre_topc @ X42 @ X43 )
      | ~ ( m1_pre_topc @ X44 @ X42 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) )
      | ~ ( m1_subset_1 @ X46 @ ( u1_struct_0 @ X44 ) )
      | ~ ( r1_tmap_1 @ X44 @ X41 @ ( k3_tmap_1 @ X43 @ X41 @ X42 @ X44 @ X47 ) @ X46 )
      | ( r1_tmap_1 @ X42 @ X41 @ X47 @ X48 )
      | ( X48 != X46 )
      | ~ ( r1_tarski @ X45 @ ( u1_struct_0 @ X44 ) )
      | ~ ( r2_hidden @ X48 @ X45 )
      | ~ ( v3_pre_topc @ X45 @ X42 )
      | ~ ( m1_subset_1 @ X48 @ ( u1_struct_0 @ X42 ) )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X42 ) @ ( u1_struct_0 @ X41 ) ) ) )
      | ~ ( v1_funct_2 @ X47 @ ( u1_struct_0 @ X42 ) @ ( u1_struct_0 @ X41 ) )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( m1_pre_topc @ X44 @ X43 )
      | ( v2_struct_0 @ X44 )
      | ~ ( l1_pre_topc @ X43 )
      | ~ ( v2_pre_topc @ X43 )
      | ( v2_struct_0 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t84_tmap_1])).

thf('127',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ( v2_struct_0 @ X43 )
      | ~ ( v2_pre_topc @ X43 )
      | ~ ( l1_pre_topc @ X43 )
      | ( v2_struct_0 @ X44 )
      | ~ ( m1_pre_topc @ X44 @ X43 )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( v1_funct_2 @ X47 @ ( u1_struct_0 @ X42 ) @ ( u1_struct_0 @ X41 ) )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X42 ) @ ( u1_struct_0 @ X41 ) ) ) )
      | ~ ( m1_subset_1 @ X46 @ ( u1_struct_0 @ X42 ) )
      | ~ ( v3_pre_topc @ X45 @ X42 )
      | ~ ( r2_hidden @ X46 @ X45 )
      | ~ ( r1_tarski @ X45 @ ( u1_struct_0 @ X44 ) )
      | ( r1_tmap_1 @ X42 @ X41 @ X47 @ X46 )
      | ~ ( r1_tmap_1 @ X44 @ X41 @ ( k3_tmap_1 @ X43 @ X41 @ X42 @ X44 @ X47 ) @ X46 )
      | ~ ( m1_subset_1 @ X46 @ ( u1_struct_0 @ X44 ) )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) )
      | ~ ( m1_pre_topc @ X44 @ X42 )
      | ~ ( m1_pre_topc @ X42 @ X43 )
      | ( v2_struct_0 @ X42 )
      | ~ ( l1_pre_topc @ X41 )
      | ~ ( v2_pre_topc @ X41 )
      | ( v2_struct_0 @ X41 ) ) ),
    inference(simplify,[status(thm)],['126'])).

thf('128',plain,(
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
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ~ ( v3_pre_topc @ X2 @ sk_D )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['125','127'])).

thf('129',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_tmap_1 @ X1 @ sk_A @ ( k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E ) @ X3 )
      | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X3 )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ~ ( v3_pre_topc @ X2 @ sk_D )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['128','129','130','131','132'])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C ) @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ~ ( l1_pre_topc @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ sk_D )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( v3_pre_topc @ X1 @ sk_D )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ ( u1_struct_0 @ sk_C ) )
      | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
      | ~ ( m1_pre_topc @ sk_C @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ sk_D )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['124','133'])).

thf('135',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('136',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['10','11'])).

thf('137',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    m1_pre_topc @ sk_D @ sk_D ),
    inference(demod,[status(thm)],['108','109','110'])).

thf('140',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C ) @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( v3_pre_topc @ X1 @ sk_D )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ ( u1_struct_0 @ sk_C ) )
      | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['134','135','136','137','138','139'])).

thf('141',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X0 )
      | ~ ( r1_tarski @ X1 @ ( u1_struct_0 @ sk_C ) )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v3_pre_topc @ X1 @ sk_D )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D ) )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D )
      | ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['140'])).

thf('142',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_D ) )
      | ~ ( v3_pre_topc @ X0 @ sk_D )
      | ~ ( r2_hidden @ sk_H @ X0 )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H )
      | ~ ( m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_C ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['100','141'])).

thf('143',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('144',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ~ ( v3_pre_topc @ X0 @ sk_D )
      | ~ ( r2_hidden @ sk_H @ X0 )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['142','143','144'])).

thf('146',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H )
    | ~ ( r1_tarski @ sk_F @ ( u1_struct_0 @ sk_C ) )
    | ~ ( r2_hidden @ sk_H @ sk_F )
    | ~ ( v3_pre_topc @ sk_F @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['13','145'])).

thf('147',plain,(
    r1_tarski @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    r2_hidden @ sk_G @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    r2_hidden @ sk_H @ sk_F ),
    inference(demod,[status(thm)],['148','149'])).

thf('151',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['7','12'])).

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

thf('153',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v3_pre_topc @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( v3_pre_topc @ X18 @ X19 )
      | ( X18 != X16 )
      | ~ ( m1_pre_topc @ X19 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t33_tops_2])).

thf('154',plain,(
    ! [X16: $i,X17: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X17 )
      | ~ ( m1_pre_topc @ X19 @ X17 )
      | ( v3_pre_topc @ X16 @ X19 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v3_pre_topc @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) ) ) ),
    inference(simplify,[status(thm)],['153'])).

thf('155',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v3_pre_topc @ sk_F @ X0 )
      | ( v3_pre_topc @ sk_F @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['152','154'])).

thf('156',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ~ ( m1_pre_topc @ sk_D @ sk_B )
    | ( v3_pre_topc @ sk_F @ sk_D )
    | ~ ( v3_pre_topc @ sk_F @ sk_B ) ),
    inference('sup-',[status(thm)],['151','155'])).

thf('157',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    v3_pre_topc @ sk_F @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    v3_pre_topc @ sk_F @ sk_D ),
    inference(demod,[status(thm)],['156','157','158','159'])).

thf('161',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['146','147','150','160'])).

thf('162',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G )
   <= ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G ) ),
    inference(split,[status(esa)],['88'])).

thf('163',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H )
   <= ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G ) ),
    inference(demod,[status(thm)],['162','163'])).

thf('165',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G ) ),
    inference(split,[status(esa)],['14'])).

thf('166',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G ) ),
    inference(demod,[status(thm)],['165','166'])).

thf('168',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H )
   <= ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H ) ),
    inference(split,[status(esa)],['61'])).

thf('169',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H ) ),
    inference('sup-',[status(thm)],['167','168'])).

thf('170',plain,(
    ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G ) ),
    inference('sat_resolution*',[status(thm)],['62','97','169'])).

thf('171',plain,(
    ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H ) ),
    inference(simpl_trail,[status(thm)],['164','170'])).

thf('172',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['161','171'])).

thf('173',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['172','173'])).

thf('175',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,(
    v2_struct_0 @ sk_C ),
    inference(clc,[status(thm)],['174','175'])).

thf('177',plain,(
    $false ),
    inference(demod,[status(thm)],['0','176'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Oo23nZ9sGr
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:50:57 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.33  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.19/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.55  % Solved by: fo/fo7.sh
% 0.19/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.55  % done 172 iterations in 0.101s
% 0.19/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.55  % SZS output start Refutation
% 0.19/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.55  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.19/0.55  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.19/0.55  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.19/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.55  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.19/0.55  thf(sk_F_type, type, sk_F: $i).
% 0.19/0.55  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.19/0.55  thf(sk_E_type, type, sk_E: $i).
% 0.19/0.55  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.19/0.55  thf(sk_D_type, type, sk_D: $i).
% 0.19/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.55  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.19/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.55  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.19/0.55  thf(sk_G_type, type, sk_G: $i).
% 0.19/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.19/0.55  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.19/0.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.55  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.19/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.55  thf(sk_H_type, type, sk_H: $i).
% 0.19/0.55  thf(t85_tmap_1, conjecture,
% 0.19/0.55    (![A:$i]:
% 0.19/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.55       ( ![B:$i]:
% 0.19/0.55         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.19/0.55             ( l1_pre_topc @ B ) ) =>
% 0.19/0.55           ( ![C:$i]:
% 0.19/0.55             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.19/0.55               ( ![D:$i]:
% 0.19/0.55                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.19/0.55                   ( ![E:$i]:
% 0.19/0.55                     ( ( ( v1_funct_1 @ E ) & 
% 0.19/0.55                         ( v1_funct_2 @
% 0.19/0.55                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) & 
% 0.19/0.55                         ( m1_subset_1 @
% 0.19/0.55                           E @ 
% 0.19/0.55                           ( k1_zfmisc_1 @
% 0.19/0.55                             ( k2_zfmisc_1 @
% 0.19/0.55                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.19/0.55                       ( ( m1_pre_topc @ C @ D ) =>
% 0.19/0.55                         ( ![F:$i]:
% 0.19/0.55                           ( ( m1_subset_1 @
% 0.19/0.55                               F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.19/0.55                             ( ![G:$i]:
% 0.19/0.55                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.19/0.55                                 ( ![H:$i]:
% 0.19/0.55                                   ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) ) =>
% 0.19/0.55                                     ( ( ( v3_pre_topc @ F @ B ) & 
% 0.19/0.55                                         ( r2_hidden @ G @ F ) & 
% 0.19/0.55                                         ( r1_tarski @ F @ ( u1_struct_0 @ C ) ) & 
% 0.19/0.55                                         ( ( G ) = ( H ) ) ) =>
% 0.19/0.55                                       ( ( r1_tmap_1 @ D @ A @ E @ G ) <=>
% 0.19/0.55                                         ( r1_tmap_1 @
% 0.19/0.55                                           C @ A @ 
% 0.19/0.55                                           ( k3_tmap_1 @ B @ A @ D @ C @ E ) @ 
% 0.19/0.55                                           H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.55    (~( ![A:$i]:
% 0.19/0.55        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.19/0.55            ( l1_pre_topc @ A ) ) =>
% 0.19/0.55          ( ![B:$i]:
% 0.19/0.55            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.19/0.55                ( l1_pre_topc @ B ) ) =>
% 0.19/0.55              ( ![C:$i]:
% 0.19/0.55                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.19/0.55                  ( ![D:$i]:
% 0.19/0.55                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.19/0.55                      ( ![E:$i]:
% 0.19/0.55                        ( ( ( v1_funct_1 @ E ) & 
% 0.19/0.55                            ( v1_funct_2 @
% 0.19/0.55                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) & 
% 0.19/0.55                            ( m1_subset_1 @
% 0.19/0.55                              E @ 
% 0.19/0.55                              ( k1_zfmisc_1 @
% 0.19/0.55                                ( k2_zfmisc_1 @
% 0.19/0.55                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.19/0.55                          ( ( m1_pre_topc @ C @ D ) =>
% 0.19/0.55                            ( ![F:$i]:
% 0.19/0.55                              ( ( m1_subset_1 @
% 0.19/0.55                                  F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.19/0.55                                ( ![G:$i]:
% 0.19/0.55                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.19/0.55                                    ( ![H:$i]:
% 0.19/0.55                                      ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) ) =>
% 0.19/0.55                                        ( ( ( v3_pre_topc @ F @ B ) & 
% 0.19/0.55                                            ( r2_hidden @ G @ F ) & 
% 0.19/0.55                                            ( r1_tarski @
% 0.19/0.55                                              F @ ( u1_struct_0 @ C ) ) & 
% 0.19/0.55                                            ( ( G ) = ( H ) ) ) =>
% 0.19/0.55                                          ( ( r1_tmap_1 @ D @ A @ E @ G ) <=>
% 0.19/0.55                                            ( r1_tmap_1 @
% 0.19/0.55                                              C @ A @ 
% 0.19/0.55                                              ( k3_tmap_1 @ B @ A @ D @ C @ E ) @ 
% 0.19/0.55                                              H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.19/0.55    inference('cnf.neg', [status(esa)], [t85_tmap_1])).
% 0.19/0.55  thf('0', plain, (~ (v2_struct_0 @ sk_C)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('1', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('2', plain, ((r1_tarski @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf(t3_subset, axiom,
% 0.19/0.55    (![A:$i,B:$i]:
% 0.19/0.55     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.19/0.55  thf('3', plain,
% 0.19/0.55      (![X3 : $i, X5 : $i]:
% 0.19/0.55         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 0.19/0.55      inference('cnf', [status(esa)], [t3_subset])).
% 0.19/0.55  thf('4', plain,
% 0.19/0.55      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))),
% 0.19/0.55      inference('sup-', [status(thm)], ['2', '3'])).
% 0.19/0.55  thf(t39_pre_topc, axiom,
% 0.19/0.55    (![A:$i]:
% 0.19/0.55     ( ( l1_pre_topc @ A ) =>
% 0.19/0.55       ( ![B:$i]:
% 0.19/0.55         ( ( m1_pre_topc @ B @ A ) =>
% 0.19/0.55           ( ![C:$i]:
% 0.19/0.55             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.19/0.55               ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ))).
% 0.19/0.55  thf('5', plain,
% 0.19/0.55      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.19/0.55         (~ (m1_pre_topc @ X10 @ X11)
% 0.19/0.55          | (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.19/0.55          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.19/0.55          | ~ (l1_pre_topc @ X11))),
% 0.19/0.55      inference('cnf', [status(esa)], [t39_pre_topc])).
% 0.19/0.55  thf('6', plain,
% 0.19/0.55      (![X0 : $i]:
% 0.19/0.55         (~ (l1_pre_topc @ X0)
% 0.19/0.55          | (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.19/0.55          | ~ (m1_pre_topc @ sk_C @ X0))),
% 0.19/0.55      inference('sup-', [status(thm)], ['4', '5'])).
% 0.19/0.55  thf('7', plain,
% 0.19/0.55      (((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.19/0.55        | ~ (l1_pre_topc @ sk_D))),
% 0.19/0.55      inference('sup-', [status(thm)], ['1', '6'])).
% 0.19/0.55  thf('8', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf(dt_m1_pre_topc, axiom,
% 0.19/0.55    (![A:$i]:
% 0.19/0.55     ( ( l1_pre_topc @ A ) =>
% 0.19/0.55       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.19/0.55  thf('9', plain,
% 0.19/0.55      (![X8 : $i, X9 : $i]:
% 0.19/0.55         (~ (m1_pre_topc @ X8 @ X9) | (l1_pre_topc @ X8) | ~ (l1_pre_topc @ X9))),
% 0.19/0.55      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.19/0.55  thf('10', plain, ((~ (l1_pre_topc @ sk_B) | (l1_pre_topc @ sk_D))),
% 0.19/0.55      inference('sup-', [status(thm)], ['8', '9'])).
% 0.19/0.55  thf('11', plain, ((l1_pre_topc @ sk_B)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('12', plain, ((l1_pre_topc @ sk_D)),
% 0.19/0.55      inference('demod', [status(thm)], ['10', '11'])).
% 0.19/0.55  thf('13', plain,
% 0.19/0.55      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.19/0.55      inference('demod', [status(thm)], ['7', '12'])).
% 0.19/0.55  thf('14', plain,
% 0.19/0.55      (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.19/0.55         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H)
% 0.19/0.55        | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('15', plain,
% 0.19/0.55      (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.19/0.55         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H))
% 0.19/0.55         <= (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.19/0.55               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H)))),
% 0.19/0.55      inference('split', [status(esa)], ['14'])).
% 0.19/0.55  thf('16', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('17', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('18', plain,
% 0.19/0.55      ((m1_subset_1 @ sk_E @ 
% 0.19/0.55        (k1_zfmisc_1 @ 
% 0.19/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf(d5_tmap_1, axiom,
% 0.19/0.55    (![A:$i]:
% 0.19/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.55       ( ![B:$i]:
% 0.19/0.55         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.19/0.55             ( l1_pre_topc @ B ) ) =>
% 0.19/0.55           ( ![C:$i]:
% 0.19/0.55             ( ( m1_pre_topc @ C @ A ) =>
% 0.19/0.55               ( ![D:$i]:
% 0.19/0.55                 ( ( m1_pre_topc @ D @ A ) =>
% 0.19/0.55                   ( ![E:$i]:
% 0.19/0.55                     ( ( ( v1_funct_1 @ E ) & 
% 0.19/0.55                         ( v1_funct_2 @
% 0.19/0.55                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.19/0.55                         ( m1_subset_1 @
% 0.19/0.55                           E @ 
% 0.19/0.55                           ( k1_zfmisc_1 @
% 0.19/0.55                             ( k2_zfmisc_1 @
% 0.19/0.55                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.19/0.55                       ( ( m1_pre_topc @ D @ C ) =>
% 0.19/0.55                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 0.19/0.55                           ( k2_partfun1 @
% 0.19/0.55                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 0.19/0.55                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.55  thf('19', plain,
% 0.19/0.55      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.19/0.55         ((v2_struct_0 @ X24)
% 0.19/0.55          | ~ (v2_pre_topc @ X24)
% 0.19/0.55          | ~ (l1_pre_topc @ X24)
% 0.19/0.55          | ~ (m1_pre_topc @ X25 @ X26)
% 0.19/0.55          | ~ (m1_pre_topc @ X25 @ X27)
% 0.19/0.55          | ((k3_tmap_1 @ X26 @ X24 @ X27 @ X25 @ X28)
% 0.19/0.55              = (k2_partfun1 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X24) @ 
% 0.19/0.55                 X28 @ (u1_struct_0 @ X25)))
% 0.19/0.55          | ~ (m1_subset_1 @ X28 @ 
% 0.19/0.55               (k1_zfmisc_1 @ 
% 0.19/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X24))))
% 0.19/0.55          | ~ (v1_funct_2 @ X28 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X24))
% 0.19/0.55          | ~ (v1_funct_1 @ X28)
% 0.19/0.55          | ~ (m1_pre_topc @ X27 @ X26)
% 0.19/0.55          | ~ (l1_pre_topc @ X26)
% 0.19/0.55          | ~ (v2_pre_topc @ X26)
% 0.19/0.55          | (v2_struct_0 @ X26))),
% 0.19/0.55      inference('cnf', [status(esa)], [d5_tmap_1])).
% 0.19/0.55  thf('20', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i]:
% 0.19/0.55         ((v2_struct_0 @ X0)
% 0.19/0.55          | ~ (v2_pre_topc @ X0)
% 0.19/0.55          | ~ (l1_pre_topc @ X0)
% 0.19/0.55          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.19/0.55          | ~ (v1_funct_1 @ sk_E)
% 0.19/0.55          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))
% 0.19/0.55          | ((k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E)
% 0.19/0.55              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.55                 sk_E @ (u1_struct_0 @ X1)))
% 0.19/0.55          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.19/0.55          | ~ (m1_pre_topc @ X1 @ X0)
% 0.19/0.55          | ~ (l1_pre_topc @ sk_A)
% 0.19/0.55          | ~ (v2_pre_topc @ sk_A)
% 0.19/0.55          | (v2_struct_0 @ sk_A))),
% 0.19/0.55      inference('sup-', [status(thm)], ['18', '19'])).
% 0.19/0.55  thf('21', plain, ((v1_funct_1 @ sk_E)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('22', plain,
% 0.19/0.55      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('24', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('25', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i]:
% 0.19/0.55         ((v2_struct_0 @ X0)
% 0.19/0.55          | ~ (v2_pre_topc @ X0)
% 0.19/0.55          | ~ (l1_pre_topc @ X0)
% 0.19/0.55          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.19/0.55          | ((k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E)
% 0.19/0.55              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.55                 sk_E @ (u1_struct_0 @ X1)))
% 0.19/0.55          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.19/0.55          | ~ (m1_pre_topc @ X1 @ X0)
% 0.19/0.55          | (v2_struct_0 @ sk_A))),
% 0.19/0.55      inference('demod', [status(thm)], ['20', '21', '22', '23', '24'])).
% 0.19/0.55  thf('26', plain,
% 0.19/0.55      (![X0 : $i]:
% 0.19/0.55         ((v2_struct_0 @ sk_A)
% 0.19/0.55          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.19/0.55          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.19/0.55          | ((k3_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 @ sk_E)
% 0.19/0.55              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.55                 sk_E @ (u1_struct_0 @ X0)))
% 0.19/0.55          | ~ (l1_pre_topc @ sk_B)
% 0.19/0.55          | ~ (v2_pre_topc @ sk_B)
% 0.19/0.55          | (v2_struct_0 @ sk_B))),
% 0.19/0.55      inference('sup-', [status(thm)], ['17', '25'])).
% 0.19/0.55  thf('27', plain, ((l1_pre_topc @ sk_B)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('28', plain, ((v2_pre_topc @ sk_B)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('29', plain,
% 0.19/0.55      (![X0 : $i]:
% 0.19/0.55         ((v2_struct_0 @ sk_A)
% 0.19/0.55          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.19/0.55          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.19/0.55          | ((k3_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 @ sk_E)
% 0.19/0.55              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.55                 sk_E @ (u1_struct_0 @ X0)))
% 0.19/0.55          | (v2_struct_0 @ sk_B))),
% 0.19/0.55      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.19/0.55  thf('30', plain,
% 0.19/0.55      (((v2_struct_0 @ sk_B)
% 0.19/0.55        | ((k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E)
% 0.19/0.55            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.55               sk_E @ (u1_struct_0 @ sk_C)))
% 0.19/0.55        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.19/0.55        | (v2_struct_0 @ sk_A))),
% 0.19/0.55      inference('sup-', [status(thm)], ['16', '29'])).
% 0.19/0.55  thf('31', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('32', plain,
% 0.19/0.55      ((m1_subset_1 @ sk_E @ 
% 0.19/0.55        (k1_zfmisc_1 @ 
% 0.19/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf(d4_tmap_1, axiom,
% 0.19/0.55    (![A:$i]:
% 0.19/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.55       ( ![B:$i]:
% 0.19/0.55         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.19/0.55             ( l1_pre_topc @ B ) ) =>
% 0.19/0.55           ( ![C:$i]:
% 0.19/0.55             ( ( ( v1_funct_1 @ C ) & 
% 0.19/0.55                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.19/0.55                 ( m1_subset_1 @
% 0.19/0.55                   C @ 
% 0.19/0.55                   ( k1_zfmisc_1 @
% 0.19/0.55                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.19/0.55               ( ![D:$i]:
% 0.19/0.55                 ( ( m1_pre_topc @ D @ A ) =>
% 0.19/0.55                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 0.19/0.55                     ( k2_partfun1 @
% 0.19/0.55                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.19/0.55                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.55  thf('33', plain,
% 0.19/0.55      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.19/0.55         ((v2_struct_0 @ X20)
% 0.19/0.55          | ~ (v2_pre_topc @ X20)
% 0.19/0.55          | ~ (l1_pre_topc @ X20)
% 0.19/0.55          | ~ (m1_pre_topc @ X21 @ X22)
% 0.19/0.55          | ((k2_tmap_1 @ X22 @ X20 @ X23 @ X21)
% 0.19/0.55              = (k2_partfun1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X20) @ 
% 0.19/0.55                 X23 @ (u1_struct_0 @ X21)))
% 0.19/0.55          | ~ (m1_subset_1 @ X23 @ 
% 0.19/0.55               (k1_zfmisc_1 @ 
% 0.19/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X20))))
% 0.19/0.55          | ~ (v1_funct_2 @ X23 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X20))
% 0.19/0.55          | ~ (v1_funct_1 @ X23)
% 0.19/0.55          | ~ (l1_pre_topc @ X22)
% 0.19/0.55          | ~ (v2_pre_topc @ X22)
% 0.19/0.55          | (v2_struct_0 @ X22))),
% 0.19/0.55      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.19/0.55  thf('34', plain,
% 0.19/0.55      (![X0 : $i]:
% 0.19/0.55         ((v2_struct_0 @ sk_D)
% 0.19/0.55          | ~ (v2_pre_topc @ sk_D)
% 0.19/0.55          | ~ (l1_pre_topc @ sk_D)
% 0.19/0.55          | ~ (v1_funct_1 @ sk_E)
% 0.19/0.55          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))
% 0.19/0.55          | ((k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0)
% 0.19/0.55              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.55                 sk_E @ (u1_struct_0 @ X0)))
% 0.19/0.55          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.19/0.55          | ~ (l1_pre_topc @ sk_A)
% 0.19/0.55          | ~ (v2_pre_topc @ sk_A)
% 0.19/0.55          | (v2_struct_0 @ sk_A))),
% 0.19/0.55      inference('sup-', [status(thm)], ['32', '33'])).
% 0.19/0.55  thf('35', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf(cc1_pre_topc, axiom,
% 0.19/0.55    (![A:$i]:
% 0.19/0.55     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.55       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.19/0.55  thf('36', plain,
% 0.19/0.55      (![X6 : $i, X7 : $i]:
% 0.19/0.55         (~ (m1_pre_topc @ X6 @ X7)
% 0.19/0.55          | (v2_pre_topc @ X6)
% 0.19/0.55          | ~ (l1_pre_topc @ X7)
% 0.19/0.55          | ~ (v2_pre_topc @ X7))),
% 0.19/0.55      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.19/0.55  thf('37', plain,
% 0.19/0.55      ((~ (v2_pre_topc @ sk_B) | ~ (l1_pre_topc @ sk_B) | (v2_pre_topc @ sk_D))),
% 0.19/0.55      inference('sup-', [status(thm)], ['35', '36'])).
% 0.19/0.55  thf('38', plain, ((v2_pre_topc @ sk_B)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('39', plain, ((l1_pre_topc @ sk_B)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('40', plain, ((v2_pre_topc @ sk_D)),
% 0.19/0.55      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.19/0.55  thf('41', plain, ((l1_pre_topc @ sk_D)),
% 0.19/0.55      inference('demod', [status(thm)], ['10', '11'])).
% 0.19/0.55  thf('42', plain, ((v1_funct_1 @ sk_E)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('43', plain,
% 0.19/0.55      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('45', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('46', plain,
% 0.19/0.55      (![X0 : $i]:
% 0.19/0.55         ((v2_struct_0 @ sk_D)
% 0.19/0.55          | ((k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0)
% 0.19/0.55              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.55                 sk_E @ (u1_struct_0 @ X0)))
% 0.19/0.55          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.19/0.55          | (v2_struct_0 @ sk_A))),
% 0.19/0.55      inference('demod', [status(thm)],
% 0.19/0.55                ['34', '40', '41', '42', '43', '44', '45'])).
% 0.19/0.55  thf('47', plain,
% 0.19/0.55      (((v2_struct_0 @ sk_A)
% 0.19/0.55        | ((k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C)
% 0.19/0.55            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.55               sk_E @ (u1_struct_0 @ sk_C)))
% 0.19/0.55        | (v2_struct_0 @ sk_D))),
% 0.19/0.55      inference('sup-', [status(thm)], ['31', '46'])).
% 0.19/0.55  thf('48', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('49', plain,
% 0.19/0.55      (((v2_struct_0 @ sk_D)
% 0.19/0.55        | ((k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C)
% 0.19/0.55            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.55               sk_E @ (u1_struct_0 @ sk_C))))),
% 0.19/0.55      inference('clc', [status(thm)], ['47', '48'])).
% 0.19/0.55  thf('50', plain, (~ (v2_struct_0 @ sk_D)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('51', plain,
% 0.19/0.55      (((k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C)
% 0.19/0.55         = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ sk_E @ 
% 0.19/0.55            (u1_struct_0 @ sk_C)))),
% 0.19/0.55      inference('clc', [status(thm)], ['49', '50'])).
% 0.19/0.55  thf('52', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('53', plain,
% 0.19/0.55      (((v2_struct_0 @ sk_B)
% 0.19/0.55        | ((k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E)
% 0.19/0.55            = (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C))
% 0.19/0.55        | (v2_struct_0 @ sk_A))),
% 0.19/0.55      inference('demod', [status(thm)], ['30', '51', '52'])).
% 0.19/0.55  thf('54', plain, (~ (v2_struct_0 @ sk_B)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('55', plain,
% 0.19/0.55      (((v2_struct_0 @ sk_A)
% 0.19/0.55        | ((k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E)
% 0.19/0.55            = (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C)))),
% 0.19/0.55      inference('clc', [status(thm)], ['53', '54'])).
% 0.19/0.55  thf('56', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('57', plain,
% 0.19/0.55      (((k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E)
% 0.19/0.55         = (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C))),
% 0.19/0.55      inference('clc', [status(thm)], ['55', '56'])).
% 0.19/0.55  thf('58', plain,
% 0.19/0.55      (((r1_tmap_1 @ sk_C @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C) @ 
% 0.19/0.55         sk_H))
% 0.19/0.55         <= (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.19/0.55               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H)))),
% 0.19/0.55      inference('demod', [status(thm)], ['15', '57'])).
% 0.19/0.55  thf('59', plain,
% 0.19/0.55      ((~ (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.19/0.55           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H)
% 0.19/0.55        | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('60', plain, (((sk_G) = (sk_H))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('61', plain,
% 0.19/0.55      ((~ (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.19/0.55           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H)
% 0.19/0.55        | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H))),
% 0.19/0.55      inference('demod', [status(thm)], ['59', '60'])).
% 0.19/0.55  thf('62', plain,
% 0.19/0.55      (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)) | 
% 0.19/0.55       ~
% 0.19/0.55       ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.19/0.55         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H))),
% 0.19/0.55      inference('split', [status(esa)], ['61'])).
% 0.19/0.55  thf('63', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_C))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('64', plain,
% 0.19/0.55      (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.19/0.55         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H)
% 0.19/0.55        | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('65', plain, (((sk_G) = (sk_H))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('66', plain,
% 0.19/0.55      (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.19/0.55         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H)
% 0.19/0.55        | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H))),
% 0.19/0.55      inference('demod', [status(thm)], ['64', '65'])).
% 0.19/0.55  thf('67', plain,
% 0.19/0.55      (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H))
% 0.19/0.55         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)))),
% 0.19/0.55      inference('split', [status(esa)], ['66'])).
% 0.19/0.55  thf('68', plain,
% 0.19/0.55      ((m1_subset_1 @ sk_E @ 
% 0.19/0.55        (k1_zfmisc_1 @ 
% 0.19/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf(t64_tmap_1, axiom,
% 0.19/0.55    (![A:$i]:
% 0.19/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.55       ( ![B:$i]:
% 0.19/0.55         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.19/0.55             ( l1_pre_topc @ B ) ) =>
% 0.19/0.55           ( ![C:$i]:
% 0.19/0.55             ( ( ( v1_funct_1 @ C ) & 
% 0.19/0.55                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.19/0.55                 ( m1_subset_1 @
% 0.19/0.55                   C @ 
% 0.19/0.55                   ( k1_zfmisc_1 @
% 0.19/0.55                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.19/0.55               ( ![D:$i]:
% 0.19/0.55                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.19/0.55                   ( ![E:$i]:
% 0.19/0.55                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.19/0.55                       ( ![F:$i]:
% 0.19/0.55                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.19/0.55                           ( ( ( ( E ) = ( F ) ) & 
% 0.19/0.55                               ( r1_tmap_1 @ B @ A @ C @ E ) ) =>
% 0.19/0.55                             ( r1_tmap_1 @
% 0.19/0.55                               D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.55  thf('69', plain,
% 0.19/0.55      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.19/0.55         ((v2_struct_0 @ X32)
% 0.19/0.55          | ~ (v2_pre_topc @ X32)
% 0.19/0.55          | ~ (l1_pre_topc @ X32)
% 0.19/0.55          | (v2_struct_0 @ X33)
% 0.19/0.55          | ~ (m1_pre_topc @ X33 @ X32)
% 0.19/0.55          | ~ (m1_subset_1 @ X34 @ (u1_struct_0 @ X33))
% 0.19/0.55          | (r1_tmap_1 @ X33 @ X35 @ (k2_tmap_1 @ X32 @ X35 @ X36 @ X33) @ X34)
% 0.19/0.55          | ((X37) != (X34))
% 0.19/0.55          | ~ (r1_tmap_1 @ X32 @ X35 @ X36 @ X37)
% 0.19/0.55          | ~ (m1_subset_1 @ X37 @ (u1_struct_0 @ X32))
% 0.19/0.55          | ~ (m1_subset_1 @ X36 @ 
% 0.19/0.55               (k1_zfmisc_1 @ 
% 0.19/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X35))))
% 0.19/0.55          | ~ (v1_funct_2 @ X36 @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X35))
% 0.19/0.55          | ~ (v1_funct_1 @ X36)
% 0.19/0.55          | ~ (l1_pre_topc @ X35)
% 0.19/0.55          | ~ (v2_pre_topc @ X35)
% 0.19/0.55          | (v2_struct_0 @ X35))),
% 0.19/0.55      inference('cnf', [status(esa)], [t64_tmap_1])).
% 0.19/0.55  thf('70', plain,
% 0.19/0.55      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.19/0.55         ((v2_struct_0 @ X35)
% 0.19/0.55          | ~ (v2_pre_topc @ X35)
% 0.19/0.55          | ~ (l1_pre_topc @ X35)
% 0.19/0.55          | ~ (v1_funct_1 @ X36)
% 0.19/0.55          | ~ (v1_funct_2 @ X36 @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X35))
% 0.19/0.55          | ~ (m1_subset_1 @ X36 @ 
% 0.19/0.55               (k1_zfmisc_1 @ 
% 0.19/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X35))))
% 0.19/0.55          | ~ (m1_subset_1 @ X34 @ (u1_struct_0 @ X32))
% 0.19/0.55          | ~ (r1_tmap_1 @ X32 @ X35 @ X36 @ X34)
% 0.19/0.55          | (r1_tmap_1 @ X33 @ X35 @ (k2_tmap_1 @ X32 @ X35 @ X36 @ X33) @ X34)
% 0.19/0.55          | ~ (m1_subset_1 @ X34 @ (u1_struct_0 @ X33))
% 0.19/0.55          | ~ (m1_pre_topc @ X33 @ X32)
% 0.19/0.55          | (v2_struct_0 @ X33)
% 0.19/0.55          | ~ (l1_pre_topc @ X32)
% 0.19/0.55          | ~ (v2_pre_topc @ X32)
% 0.19/0.55          | (v2_struct_0 @ X32))),
% 0.19/0.55      inference('simplify', [status(thm)], ['69'])).
% 0.19/0.55  thf('71', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i]:
% 0.19/0.55         ((v2_struct_0 @ sk_D)
% 0.19/0.55          | ~ (v2_pre_topc @ sk_D)
% 0.19/0.55          | ~ (l1_pre_topc @ sk_D)
% 0.19/0.55          | (v2_struct_0 @ X0)
% 0.19/0.55          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.19/0.55          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.19/0.55          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0) @ X1)
% 0.19/0.55          | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X1)
% 0.19/0.55          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D))
% 0.19/0.55          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))
% 0.19/0.55          | ~ (v1_funct_1 @ sk_E)
% 0.19/0.55          | ~ (l1_pre_topc @ sk_A)
% 0.19/0.55          | ~ (v2_pre_topc @ sk_A)
% 0.19/0.55          | (v2_struct_0 @ sk_A))),
% 0.19/0.55      inference('sup-', [status(thm)], ['68', '70'])).
% 0.19/0.55  thf('72', plain, ((v2_pre_topc @ sk_D)),
% 0.19/0.55      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.19/0.55  thf('73', plain, ((l1_pre_topc @ sk_D)),
% 0.19/0.55      inference('demod', [status(thm)], ['10', '11'])).
% 0.19/0.55  thf('74', plain,
% 0.19/0.55      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('75', plain, ((v1_funct_1 @ sk_E)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('76', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('77', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('78', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i]:
% 0.19/0.55         ((v2_struct_0 @ sk_D)
% 0.19/0.55          | (v2_struct_0 @ X0)
% 0.19/0.55          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.19/0.55          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.19/0.55          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0) @ X1)
% 0.19/0.55          | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X1)
% 0.19/0.55          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D))
% 0.19/0.55          | (v2_struct_0 @ sk_A))),
% 0.19/0.55      inference('demod', [status(thm)],
% 0.19/0.55                ['71', '72', '73', '74', '75', '76', '77'])).
% 0.19/0.55  thf('79', plain,
% 0.19/0.55      ((![X0 : $i]:
% 0.19/0.55          ((v2_struct_0 @ sk_A)
% 0.19/0.55           | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D))
% 0.19/0.55           | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0) @ 
% 0.19/0.55              sk_H)
% 0.19/0.55           | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ X0))
% 0.19/0.55           | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.19/0.55           | (v2_struct_0 @ X0)
% 0.19/0.55           | (v2_struct_0 @ sk_D)))
% 0.19/0.55         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)))),
% 0.19/0.55      inference('sup-', [status(thm)], ['67', '78'])).
% 0.19/0.55  thf('80', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_D))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('81', plain, (((sk_G) = (sk_H))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('82', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D))),
% 0.19/0.55      inference('demod', [status(thm)], ['80', '81'])).
% 0.19/0.55  thf('83', plain,
% 0.19/0.55      ((![X0 : $i]:
% 0.19/0.55          ((v2_struct_0 @ sk_A)
% 0.19/0.55           | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0) @ 
% 0.19/0.55              sk_H)
% 0.19/0.55           | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ X0))
% 0.19/0.55           | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.19/0.55           | (v2_struct_0 @ X0)
% 0.19/0.55           | (v2_struct_0 @ sk_D)))
% 0.19/0.55         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)))),
% 0.19/0.55      inference('demod', [status(thm)], ['79', '82'])).
% 0.19/0.55  thf('84', plain,
% 0.19/0.55      ((((v2_struct_0 @ sk_D)
% 0.19/0.55         | (v2_struct_0 @ sk_C)
% 0.19/0.55         | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.19/0.55         | (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.19/0.55            (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C) @ sk_H)
% 0.19/0.55         | (v2_struct_0 @ sk_A)))
% 0.19/0.55         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)))),
% 0.19/0.55      inference('sup-', [status(thm)], ['63', '83'])).
% 0.19/0.55  thf('85', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('86', plain,
% 0.19/0.55      ((((v2_struct_0 @ sk_D)
% 0.19/0.55         | (v2_struct_0 @ sk_C)
% 0.19/0.55         | (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.19/0.55            (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C) @ sk_H)
% 0.19/0.55         | (v2_struct_0 @ sk_A)))
% 0.19/0.55         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)))),
% 0.19/0.55      inference('demod', [status(thm)], ['84', '85'])).
% 0.19/0.55  thf('87', plain,
% 0.19/0.55      (((k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E)
% 0.19/0.55         = (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C))),
% 0.19/0.55      inference('clc', [status(thm)], ['55', '56'])).
% 0.19/0.55  thf('88', plain,
% 0.19/0.55      ((~ (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.19/0.55           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H)
% 0.19/0.55        | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('89', plain,
% 0.19/0.55      ((~ (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.19/0.55           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H))
% 0.19/0.55         <= (~
% 0.19/0.55             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.19/0.55               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H)))),
% 0.19/0.55      inference('split', [status(esa)], ['88'])).
% 0.19/0.55  thf('90', plain,
% 0.19/0.55      ((~ (r1_tmap_1 @ sk_C @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C) @ 
% 0.19/0.55           sk_H))
% 0.19/0.55         <= (~
% 0.19/0.55             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.19/0.55               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H)))),
% 0.19/0.55      inference('sup-', [status(thm)], ['87', '89'])).
% 0.19/0.55  thf('91', plain,
% 0.19/0.55      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_D)))
% 0.19/0.55         <= (~
% 0.19/0.55             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.19/0.55               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H)) & 
% 0.19/0.55             ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)))),
% 0.19/0.55      inference('sup-', [status(thm)], ['86', '90'])).
% 0.19/0.55  thf('92', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('93', plain,
% 0.19/0.55      ((((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C)))
% 0.19/0.55         <= (~
% 0.19/0.55             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.19/0.55               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H)) & 
% 0.19/0.55             ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)))),
% 0.19/0.55      inference('clc', [status(thm)], ['91', '92'])).
% 0.19/0.55  thf('94', plain, (~ (v2_struct_0 @ sk_D)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('95', plain,
% 0.19/0.55      (((v2_struct_0 @ sk_C))
% 0.19/0.55         <= (~
% 0.19/0.55             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.19/0.55               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H)) & 
% 0.19/0.55             ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)))),
% 0.19/0.55      inference('clc', [status(thm)], ['93', '94'])).
% 0.19/0.55  thf('96', plain, (~ (v2_struct_0 @ sk_C)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('97', plain,
% 0.19/0.55      (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.19/0.55         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H)) | 
% 0.19/0.55       ~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H))),
% 0.19/0.55      inference('sup-', [status(thm)], ['95', '96'])).
% 0.19/0.55  thf('98', plain,
% 0.19/0.55      (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.19/0.55         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H)) | 
% 0.19/0.55       ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H))),
% 0.19/0.55      inference('split', [status(esa)], ['66'])).
% 0.19/0.55  thf('99', plain,
% 0.19/0.55      (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.19/0.55         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H))),
% 0.19/0.55      inference('sat_resolution*', [status(thm)], ['62', '97', '98'])).
% 0.19/0.55  thf('100', plain,
% 0.19/0.55      ((r1_tmap_1 @ sk_C @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C) @ 
% 0.19/0.55        sk_H)),
% 0.19/0.55      inference('simpl_trail', [status(thm)], ['58', '99'])).
% 0.19/0.55  thf('101', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('102', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf(d10_xboole_0, axiom,
% 0.19/0.55    (![A:$i,B:$i]:
% 0.19/0.55     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.19/0.55  thf('103', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.19/0.55      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.19/0.55  thf('104', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.19/0.55      inference('simplify', [status(thm)], ['103'])).
% 0.19/0.55  thf(t4_tsep_1, axiom,
% 0.19/0.55    (![A:$i]:
% 0.19/0.55     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.55       ( ![B:$i]:
% 0.19/0.55         ( ( m1_pre_topc @ B @ A ) =>
% 0.19/0.55           ( ![C:$i]:
% 0.19/0.55             ( ( m1_pre_topc @ C @ A ) =>
% 0.19/0.55               ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) <=>
% 0.19/0.55                 ( m1_pre_topc @ B @ C ) ) ) ) ) ) ))).
% 0.19/0.55  thf('105', plain,
% 0.19/0.55      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.19/0.55         (~ (m1_pre_topc @ X29 @ X30)
% 0.19/0.55          | ~ (r1_tarski @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X31))
% 0.19/0.55          | (m1_pre_topc @ X29 @ X31)
% 0.19/0.55          | ~ (m1_pre_topc @ X31 @ X30)
% 0.19/0.55          | ~ (l1_pre_topc @ X30)
% 0.19/0.55          | ~ (v2_pre_topc @ X30))),
% 0.19/0.55      inference('cnf', [status(esa)], [t4_tsep_1])).
% 0.19/0.55  thf('106', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i]:
% 0.19/0.55         (~ (v2_pre_topc @ X1)
% 0.19/0.55          | ~ (l1_pre_topc @ X1)
% 0.19/0.55          | ~ (m1_pre_topc @ X0 @ X1)
% 0.19/0.55          | (m1_pre_topc @ X0 @ X0)
% 0.19/0.55          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.19/0.55      inference('sup-', [status(thm)], ['104', '105'])).
% 0.19/0.55  thf('107', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i]:
% 0.19/0.55         ((m1_pre_topc @ X0 @ X0)
% 0.19/0.55          | ~ (m1_pre_topc @ X0 @ X1)
% 0.19/0.55          | ~ (l1_pre_topc @ X1)
% 0.19/0.55          | ~ (v2_pre_topc @ X1))),
% 0.19/0.55      inference('simplify', [status(thm)], ['106'])).
% 0.19/0.55  thf('108', plain,
% 0.19/0.55      ((~ (v2_pre_topc @ sk_B)
% 0.19/0.55        | ~ (l1_pre_topc @ sk_B)
% 0.19/0.55        | (m1_pre_topc @ sk_D @ sk_D))),
% 0.19/0.55      inference('sup-', [status(thm)], ['102', '107'])).
% 0.19/0.55  thf('109', plain, ((v2_pre_topc @ sk_B)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('110', plain, ((l1_pre_topc @ sk_B)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('111', plain, ((m1_pre_topc @ sk_D @ sk_D)),
% 0.19/0.55      inference('demod', [status(thm)], ['108', '109', '110'])).
% 0.19/0.55  thf('112', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i]:
% 0.19/0.55         ((v2_struct_0 @ X0)
% 0.19/0.55          | ~ (v2_pre_topc @ X0)
% 0.19/0.55          | ~ (l1_pre_topc @ X0)
% 0.19/0.55          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.19/0.55          | ((k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E)
% 0.19/0.55              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.55                 sk_E @ (u1_struct_0 @ X1)))
% 0.19/0.55          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.19/0.55          | ~ (m1_pre_topc @ X1 @ X0)
% 0.19/0.55          | (v2_struct_0 @ sk_A))),
% 0.19/0.55      inference('demod', [status(thm)], ['20', '21', '22', '23', '24'])).
% 0.19/0.55  thf('113', plain,
% 0.19/0.55      (![X0 : $i]:
% 0.19/0.55         ((v2_struct_0 @ sk_A)
% 0.19/0.55          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.19/0.55          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.19/0.55          | ((k3_tmap_1 @ sk_D @ sk_A @ sk_D @ X0 @ sk_E)
% 0.19/0.55              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.55                 sk_E @ (u1_struct_0 @ X0)))
% 0.19/0.55          | ~ (l1_pre_topc @ sk_D)
% 0.19/0.55          | ~ (v2_pre_topc @ sk_D)
% 0.19/0.55          | (v2_struct_0 @ sk_D))),
% 0.19/0.55      inference('sup-', [status(thm)], ['111', '112'])).
% 0.19/0.55  thf('114', plain, ((l1_pre_topc @ sk_D)),
% 0.19/0.55      inference('demod', [status(thm)], ['10', '11'])).
% 0.19/0.55  thf('115', plain, ((v2_pre_topc @ sk_D)),
% 0.19/0.55      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.19/0.55  thf('116', plain,
% 0.19/0.55      (![X0 : $i]:
% 0.19/0.55         ((v2_struct_0 @ sk_A)
% 0.19/0.55          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.19/0.55          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.19/0.55          | ((k3_tmap_1 @ sk_D @ sk_A @ sk_D @ X0 @ sk_E)
% 0.19/0.55              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.55                 sk_E @ (u1_struct_0 @ X0)))
% 0.19/0.55          | (v2_struct_0 @ sk_D))),
% 0.19/0.55      inference('demod', [status(thm)], ['113', '114', '115'])).
% 0.19/0.55  thf('117', plain,
% 0.19/0.55      (![X0 : $i]:
% 0.19/0.55         ((v2_struct_0 @ sk_D)
% 0.19/0.55          | ((k3_tmap_1 @ sk_D @ sk_A @ sk_D @ X0 @ sk_E)
% 0.19/0.55              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.55                 sk_E @ (u1_struct_0 @ X0)))
% 0.19/0.55          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.19/0.55          | (v2_struct_0 @ sk_A))),
% 0.19/0.55      inference('simplify', [status(thm)], ['116'])).
% 0.19/0.55  thf('118', plain,
% 0.19/0.55      (((v2_struct_0 @ sk_A)
% 0.19/0.55        | ((k3_tmap_1 @ sk_D @ sk_A @ sk_D @ sk_C @ sk_E)
% 0.19/0.55            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.55               sk_E @ (u1_struct_0 @ sk_C)))
% 0.19/0.55        | (v2_struct_0 @ sk_D))),
% 0.19/0.55      inference('sup-', [status(thm)], ['101', '117'])).
% 0.19/0.55  thf('119', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('120', plain,
% 0.19/0.55      (((v2_struct_0 @ sk_D)
% 0.19/0.55        | ((k3_tmap_1 @ sk_D @ sk_A @ sk_D @ sk_C @ sk_E)
% 0.19/0.55            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.55               sk_E @ (u1_struct_0 @ sk_C))))),
% 0.19/0.55      inference('clc', [status(thm)], ['118', '119'])).
% 0.19/0.55  thf('121', plain, (~ (v2_struct_0 @ sk_D)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('122', plain,
% 0.19/0.55      (((k3_tmap_1 @ sk_D @ sk_A @ sk_D @ sk_C @ sk_E)
% 0.19/0.55         = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ sk_E @ 
% 0.19/0.55            (u1_struct_0 @ sk_C)))),
% 0.19/0.55      inference('clc', [status(thm)], ['120', '121'])).
% 0.19/0.55  thf('123', plain,
% 0.19/0.55      (((k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C)
% 0.19/0.55         = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ sk_E @ 
% 0.19/0.55            (u1_struct_0 @ sk_C)))),
% 0.19/0.55      inference('clc', [status(thm)], ['49', '50'])).
% 0.19/0.55  thf('124', plain,
% 0.19/0.55      (((k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C)
% 0.19/0.55         = (k3_tmap_1 @ sk_D @ sk_A @ sk_D @ sk_C @ sk_E))),
% 0.19/0.55      inference('sup+', [status(thm)], ['122', '123'])).
% 0.19/0.55  thf('125', plain,
% 0.19/0.55      ((m1_subset_1 @ sk_E @ 
% 0.19/0.55        (k1_zfmisc_1 @ 
% 0.19/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf(t84_tmap_1, axiom,
% 0.19/0.55    (![A:$i]:
% 0.19/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.55       ( ![B:$i]:
% 0.19/0.55         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.19/0.55             ( l1_pre_topc @ B ) ) =>
% 0.19/0.55           ( ![C:$i]:
% 0.19/0.55             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.19/0.55               ( ![D:$i]:
% 0.19/0.55                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.19/0.55                   ( ![E:$i]:
% 0.19/0.55                     ( ( ( v1_funct_1 @ E ) & 
% 0.19/0.55                         ( v1_funct_2 @
% 0.19/0.55                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.19/0.55                         ( m1_subset_1 @
% 0.19/0.55                           E @ 
% 0.19/0.55                           ( k1_zfmisc_1 @
% 0.19/0.55                             ( k2_zfmisc_1 @
% 0.19/0.55                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.19/0.55                       ( ( m1_pre_topc @ C @ D ) =>
% 0.19/0.55                         ( ![F:$i]:
% 0.19/0.55                           ( ( m1_subset_1 @
% 0.19/0.55                               F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ D ) ) ) =>
% 0.19/0.55                             ( ![G:$i]:
% 0.19/0.55                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.19/0.55                                 ( ![H:$i]:
% 0.19/0.55                                   ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) ) =>
% 0.19/0.55                                     ( ( ( v3_pre_topc @ F @ D ) & 
% 0.19/0.55                                         ( r2_hidden @ G @ F ) & 
% 0.19/0.55                                         ( r1_tarski @ F @ ( u1_struct_0 @ C ) ) & 
% 0.19/0.55                                         ( ( G ) = ( H ) ) ) =>
% 0.19/0.55                                       ( ( r1_tmap_1 @ D @ B @ E @ G ) <=>
% 0.19/0.55                                         ( r1_tmap_1 @
% 0.19/0.55                                           C @ B @ 
% 0.19/0.55                                           ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ 
% 0.19/0.55                                           H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.55  thf('126', plain,
% 0.19/0.55      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i, 
% 0.19/0.55         X48 : $i]:
% 0.19/0.55         ((v2_struct_0 @ X41)
% 0.19/0.55          | ~ (v2_pre_topc @ X41)
% 0.19/0.55          | ~ (l1_pre_topc @ X41)
% 0.19/0.55          | (v2_struct_0 @ X42)
% 0.19/0.55          | ~ (m1_pre_topc @ X42 @ X43)
% 0.19/0.55          | ~ (m1_pre_topc @ X44 @ X42)
% 0.19/0.55          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (u1_struct_0 @ X42)))
% 0.19/0.55          | ~ (m1_subset_1 @ X46 @ (u1_struct_0 @ X44))
% 0.19/0.55          | ~ (r1_tmap_1 @ X44 @ X41 @ 
% 0.19/0.55               (k3_tmap_1 @ X43 @ X41 @ X42 @ X44 @ X47) @ X46)
% 0.19/0.55          | (r1_tmap_1 @ X42 @ X41 @ X47 @ X48)
% 0.19/0.55          | ((X48) != (X46))
% 0.19/0.55          | ~ (r1_tarski @ X45 @ (u1_struct_0 @ X44))
% 0.19/0.55          | ~ (r2_hidden @ X48 @ X45)
% 0.19/0.55          | ~ (v3_pre_topc @ X45 @ X42)
% 0.19/0.55          | ~ (m1_subset_1 @ X48 @ (u1_struct_0 @ X42))
% 0.19/0.55          | ~ (m1_subset_1 @ X47 @ 
% 0.19/0.55               (k1_zfmisc_1 @ 
% 0.19/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ X42) @ (u1_struct_0 @ X41))))
% 0.19/0.55          | ~ (v1_funct_2 @ X47 @ (u1_struct_0 @ X42) @ (u1_struct_0 @ X41))
% 0.19/0.55          | ~ (v1_funct_1 @ X47)
% 0.19/0.55          | ~ (m1_pre_topc @ X44 @ X43)
% 0.19/0.55          | (v2_struct_0 @ X44)
% 0.19/0.55          | ~ (l1_pre_topc @ X43)
% 0.19/0.55          | ~ (v2_pre_topc @ X43)
% 0.19/0.55          | (v2_struct_0 @ X43))),
% 0.19/0.55      inference('cnf', [status(esa)], [t84_tmap_1])).
% 0.19/0.55  thf('127', plain,
% 0.19/0.55      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 0.19/0.55         ((v2_struct_0 @ X43)
% 0.19/0.55          | ~ (v2_pre_topc @ X43)
% 0.19/0.55          | ~ (l1_pre_topc @ X43)
% 0.19/0.55          | (v2_struct_0 @ X44)
% 0.19/0.55          | ~ (m1_pre_topc @ X44 @ X43)
% 0.19/0.55          | ~ (v1_funct_1 @ X47)
% 0.19/0.55          | ~ (v1_funct_2 @ X47 @ (u1_struct_0 @ X42) @ (u1_struct_0 @ X41))
% 0.19/0.55          | ~ (m1_subset_1 @ X47 @ 
% 0.19/0.55               (k1_zfmisc_1 @ 
% 0.19/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ X42) @ (u1_struct_0 @ X41))))
% 0.19/0.55          | ~ (m1_subset_1 @ X46 @ (u1_struct_0 @ X42))
% 0.19/0.55          | ~ (v3_pre_topc @ X45 @ X42)
% 0.19/0.55          | ~ (r2_hidden @ X46 @ X45)
% 0.19/0.55          | ~ (r1_tarski @ X45 @ (u1_struct_0 @ X44))
% 0.19/0.55          | (r1_tmap_1 @ X42 @ X41 @ X47 @ X46)
% 0.19/0.55          | ~ (r1_tmap_1 @ X44 @ X41 @ 
% 0.19/0.55               (k3_tmap_1 @ X43 @ X41 @ X42 @ X44 @ X47) @ X46)
% 0.19/0.55          | ~ (m1_subset_1 @ X46 @ (u1_struct_0 @ X44))
% 0.19/0.55          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (u1_struct_0 @ X42)))
% 0.19/0.55          | ~ (m1_pre_topc @ X44 @ X42)
% 0.19/0.55          | ~ (m1_pre_topc @ X42 @ X43)
% 0.19/0.55          | (v2_struct_0 @ X42)
% 0.19/0.55          | ~ (l1_pre_topc @ X41)
% 0.19/0.55          | ~ (v2_pre_topc @ X41)
% 0.19/0.55          | (v2_struct_0 @ X41))),
% 0.19/0.55      inference('simplify', [status(thm)], ['126'])).
% 0.19/0.55  thf('128', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.55         ((v2_struct_0 @ sk_A)
% 0.19/0.55          | ~ (v2_pre_topc @ sk_A)
% 0.19/0.55          | ~ (l1_pre_topc @ sk_A)
% 0.19/0.55          | (v2_struct_0 @ sk_D)
% 0.19/0.55          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.19/0.55          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.19/0.55          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.19/0.55          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.19/0.55          | ~ (r1_tmap_1 @ X1 @ sk_A @ 
% 0.19/0.55               (k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E) @ X3)
% 0.19/0.55          | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X3)
% 0.19/0.55          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X1))
% 0.19/0.55          | ~ (r2_hidden @ X3 @ X2)
% 0.19/0.55          | ~ (v3_pre_topc @ X2 @ sk_D)
% 0.19/0.55          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_D))
% 0.19/0.55          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))
% 0.19/0.55          | ~ (v1_funct_1 @ sk_E)
% 0.19/0.55          | ~ (m1_pre_topc @ X1 @ X0)
% 0.19/0.55          | (v2_struct_0 @ X1)
% 0.19/0.55          | ~ (l1_pre_topc @ X0)
% 0.19/0.55          | ~ (v2_pre_topc @ X0)
% 0.19/0.55          | (v2_struct_0 @ X0))),
% 0.19/0.55      inference('sup-', [status(thm)], ['125', '127'])).
% 0.19/0.55  thf('129', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('130', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('131', plain,
% 0.19/0.55      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('132', plain, ((v1_funct_1 @ sk_E)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('133', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.55         ((v2_struct_0 @ sk_A)
% 0.19/0.55          | (v2_struct_0 @ sk_D)
% 0.19/0.55          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.19/0.55          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.19/0.55          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.19/0.55          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.19/0.55          | ~ (r1_tmap_1 @ X1 @ sk_A @ 
% 0.19/0.55               (k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E) @ X3)
% 0.19/0.55          | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X3)
% 0.19/0.55          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X1))
% 0.19/0.55          | ~ (r2_hidden @ X3 @ X2)
% 0.19/0.55          | ~ (v3_pre_topc @ X2 @ sk_D)
% 0.19/0.55          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_D))
% 0.19/0.55          | ~ (m1_pre_topc @ X1 @ X0)
% 0.19/0.55          | (v2_struct_0 @ X1)
% 0.19/0.55          | ~ (l1_pre_topc @ X0)
% 0.19/0.55          | ~ (v2_pre_topc @ X0)
% 0.19/0.55          | (v2_struct_0 @ X0))),
% 0.19/0.55      inference('demod', [status(thm)], ['128', '129', '130', '131', '132'])).
% 0.19/0.55  thf('134', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i]:
% 0.19/0.55         (~ (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.19/0.55             (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C) @ X0)
% 0.19/0.55          | (v2_struct_0 @ sk_D)
% 0.19/0.55          | ~ (v2_pre_topc @ sk_D)
% 0.19/0.55          | ~ (l1_pre_topc @ sk_D)
% 0.19/0.55          | (v2_struct_0 @ sk_C)
% 0.19/0.55          | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.19/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D))
% 0.19/0.55          | ~ (v3_pre_topc @ X1 @ sk_D)
% 0.19/0.55          | ~ (r2_hidden @ X0 @ X1)
% 0.19/0.55          | ~ (r1_tarski @ X1 @ (u1_struct_0 @ sk_C))
% 0.19/0.55          | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X0)
% 0.19/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C))
% 0.19/0.55          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.19/0.55          | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.19/0.55          | ~ (m1_pre_topc @ sk_D @ sk_D)
% 0.19/0.55          | (v2_struct_0 @ sk_D)
% 0.19/0.55          | (v2_struct_0 @ sk_A))),
% 0.19/0.55      inference('sup-', [status(thm)], ['124', '133'])).
% 0.19/0.55  thf('135', plain, ((v2_pre_topc @ sk_D)),
% 0.19/0.55      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.19/0.55  thf('136', plain, ((l1_pre_topc @ sk_D)),
% 0.19/0.55      inference('demod', [status(thm)], ['10', '11'])).
% 0.19/0.55  thf('137', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('138', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('139', plain, ((m1_pre_topc @ sk_D @ sk_D)),
% 0.19/0.55      inference('demod', [status(thm)], ['108', '109', '110'])).
% 0.19/0.55  thf('140', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i]:
% 0.19/0.55         (~ (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.19/0.55             (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C) @ X0)
% 0.19/0.55          | (v2_struct_0 @ sk_D)
% 0.19/0.55          | (v2_struct_0 @ sk_C)
% 0.19/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D))
% 0.19/0.55          | ~ (v3_pre_topc @ X1 @ sk_D)
% 0.19/0.55          | ~ (r2_hidden @ X0 @ X1)
% 0.19/0.55          | ~ (r1_tarski @ X1 @ (u1_struct_0 @ sk_C))
% 0.19/0.55          | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X0)
% 0.19/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C))
% 0.19/0.55          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.19/0.55          | (v2_struct_0 @ sk_D)
% 0.19/0.55          | (v2_struct_0 @ sk_A))),
% 0.19/0.55      inference('demod', [status(thm)],
% 0.19/0.55                ['134', '135', '136', '137', '138', '139'])).
% 0.19/0.55  thf('141', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i]:
% 0.19/0.55         ((v2_struct_0 @ sk_A)
% 0.19/0.55          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.19/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C))
% 0.19/0.55          | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X0)
% 0.19/0.55          | ~ (r1_tarski @ X1 @ (u1_struct_0 @ sk_C))
% 0.19/0.55          | ~ (r2_hidden @ X0 @ X1)
% 0.19/0.55          | ~ (v3_pre_topc @ X1 @ sk_D)
% 0.19/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D))
% 0.19/0.55          | (v2_struct_0 @ sk_C)
% 0.19/0.55          | (v2_struct_0 @ sk_D)
% 0.19/0.55          | ~ (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.19/0.55               (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C) @ X0))),
% 0.19/0.55      inference('simplify', [status(thm)], ['140'])).
% 0.19/0.55  thf('142', plain,
% 0.19/0.55      (![X0 : $i]:
% 0.19/0.55         ((v2_struct_0 @ sk_D)
% 0.19/0.55          | (v2_struct_0 @ sk_C)
% 0.19/0.55          | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D))
% 0.19/0.55          | ~ (v3_pre_topc @ X0 @ sk_D)
% 0.19/0.55          | ~ (r2_hidden @ sk_H @ X0)
% 0.19/0.55          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C))
% 0.19/0.55          | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)
% 0.19/0.55          | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_C))
% 0.19/0.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.19/0.55          | (v2_struct_0 @ sk_A))),
% 0.19/0.55      inference('sup-', [status(thm)], ['100', '141'])).
% 0.19/0.55  thf('143', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D))),
% 0.19/0.55      inference('demod', [status(thm)], ['80', '81'])).
% 0.19/0.55  thf('144', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_C))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('145', plain,
% 0.19/0.55      (![X0 : $i]:
% 0.19/0.55         ((v2_struct_0 @ sk_D)
% 0.19/0.55          | (v2_struct_0 @ sk_C)
% 0.19/0.55          | ~ (v3_pre_topc @ X0 @ sk_D)
% 0.19/0.55          | ~ (r2_hidden @ sk_H @ X0)
% 0.19/0.55          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C))
% 0.19/0.55          | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)
% 0.19/0.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.19/0.55          | (v2_struct_0 @ sk_A))),
% 0.19/0.55      inference('demod', [status(thm)], ['142', '143', '144'])).
% 0.19/0.55  thf('146', plain,
% 0.19/0.55      (((v2_struct_0 @ sk_A)
% 0.19/0.55        | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)
% 0.19/0.55        | ~ (r1_tarski @ sk_F @ (u1_struct_0 @ sk_C))
% 0.19/0.55        | ~ (r2_hidden @ sk_H @ sk_F)
% 0.19/0.55        | ~ (v3_pre_topc @ sk_F @ sk_D)
% 0.19/0.55        | (v2_struct_0 @ sk_C)
% 0.19/0.55        | (v2_struct_0 @ sk_D))),
% 0.19/0.55      inference('sup-', [status(thm)], ['13', '145'])).
% 0.19/0.55  thf('147', plain, ((r1_tarski @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('148', plain, ((r2_hidden @ sk_G @ sk_F)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('149', plain, (((sk_G) = (sk_H))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('150', plain, ((r2_hidden @ sk_H @ sk_F)),
% 0.19/0.55      inference('demod', [status(thm)], ['148', '149'])).
% 0.19/0.55  thf('151', plain,
% 0.19/0.55      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('152', plain,
% 0.19/0.55      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.19/0.55      inference('demod', [status(thm)], ['7', '12'])).
% 0.19/0.55  thf(t33_tops_2, axiom,
% 0.19/0.55    (![A:$i]:
% 0.19/0.55     ( ( l1_pre_topc @ A ) =>
% 0.19/0.55       ( ![B:$i]:
% 0.19/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.55           ( ![C:$i]:
% 0.19/0.55             ( ( m1_pre_topc @ C @ A ) =>
% 0.19/0.55               ( ( v3_pre_topc @ B @ A ) =>
% 0.19/0.55                 ( ![D:$i]:
% 0.19/0.55                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) ) =>
% 0.19/0.55                     ( ( ( D ) = ( B ) ) => ( v3_pre_topc @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.55  thf('153', plain,
% 0.19/0.55      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.19/0.55         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.19/0.55          | ~ (v3_pre_topc @ X16 @ X17)
% 0.19/0.55          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.19/0.55          | (v3_pre_topc @ X18 @ X19)
% 0.19/0.55          | ((X18) != (X16))
% 0.19/0.55          | ~ (m1_pre_topc @ X19 @ X17)
% 0.19/0.55          | ~ (l1_pre_topc @ X17))),
% 0.19/0.55      inference('cnf', [status(esa)], [t33_tops_2])).
% 0.19/0.55  thf('154', plain,
% 0.19/0.55      (![X16 : $i, X17 : $i, X19 : $i]:
% 0.19/0.55         (~ (l1_pre_topc @ X17)
% 0.19/0.55          | ~ (m1_pre_topc @ X19 @ X17)
% 0.19/0.55          | (v3_pre_topc @ X16 @ X19)
% 0.19/0.55          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.19/0.55          | ~ (v3_pre_topc @ X16 @ X17)
% 0.19/0.55          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17))))),
% 0.19/0.55      inference('simplify', [status(thm)], ['153'])).
% 0.19/0.55  thf('155', plain,
% 0.19/0.55      (![X0 : $i]:
% 0.19/0.55         (~ (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.19/0.55          | ~ (v3_pre_topc @ sk_F @ X0)
% 0.19/0.55          | (v3_pre_topc @ sk_F @ sk_D)
% 0.19/0.55          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.19/0.55          | ~ (l1_pre_topc @ X0))),
% 0.19/0.55      inference('sup-', [status(thm)], ['152', '154'])).
% 0.19/0.55  thf('156', plain,
% 0.19/0.55      ((~ (l1_pre_topc @ sk_B)
% 0.19/0.55        | ~ (m1_pre_topc @ sk_D @ sk_B)
% 0.19/0.55        | (v3_pre_topc @ sk_F @ sk_D)
% 0.19/0.55        | ~ (v3_pre_topc @ sk_F @ sk_B))),
% 0.19/0.55      inference('sup-', [status(thm)], ['151', '155'])).
% 0.19/0.55  thf('157', plain, ((l1_pre_topc @ sk_B)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('158', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('159', plain, ((v3_pre_topc @ sk_F @ sk_B)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('160', plain, ((v3_pre_topc @ sk_F @ sk_D)),
% 0.19/0.55      inference('demod', [status(thm)], ['156', '157', '158', '159'])).
% 0.19/0.55  thf('161', plain,
% 0.19/0.55      (((v2_struct_0 @ sk_A)
% 0.19/0.55        | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)
% 0.19/0.55        | (v2_struct_0 @ sk_C)
% 0.19/0.55        | (v2_struct_0 @ sk_D))),
% 0.19/0.55      inference('demod', [status(thm)], ['146', '147', '150', '160'])).
% 0.19/0.55  thf('162', plain,
% 0.19/0.55      ((~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G))
% 0.19/0.55         <= (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G)))),
% 0.19/0.55      inference('split', [status(esa)], ['88'])).
% 0.19/0.55  thf('163', plain, (((sk_G) = (sk_H))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('164', plain,
% 0.19/0.55      ((~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H))
% 0.19/0.55         <= (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G)))),
% 0.19/0.55      inference('demod', [status(thm)], ['162', '163'])).
% 0.19/0.55  thf('165', plain,
% 0.19/0.55      (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G))
% 0.19/0.55         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G)))),
% 0.19/0.55      inference('split', [status(esa)], ['14'])).
% 0.19/0.55  thf('166', plain, (((sk_G) = (sk_H))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('167', plain,
% 0.19/0.55      (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H))
% 0.19/0.55         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G)))),
% 0.19/0.55      inference('demod', [status(thm)], ['165', '166'])).
% 0.19/0.55  thf('168', plain,
% 0.19/0.55      ((~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H))
% 0.19/0.55         <= (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)))),
% 0.19/0.55      inference('split', [status(esa)], ['61'])).
% 0.19/0.55  thf('169', plain,
% 0.19/0.55      (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G)) | 
% 0.19/0.55       ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H))),
% 0.19/0.55      inference('sup-', [status(thm)], ['167', '168'])).
% 0.19/0.55  thf('170', plain, (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G))),
% 0.19/0.55      inference('sat_resolution*', [status(thm)], ['62', '97', '169'])).
% 0.19/0.55  thf('171', plain, (~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)),
% 0.19/0.55      inference('simpl_trail', [status(thm)], ['164', '170'])).
% 0.19/0.55  thf('172', plain,
% 0.19/0.55      (((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A))),
% 0.19/0.55      inference('sup-', [status(thm)], ['161', '171'])).
% 0.19/0.55  thf('173', plain, (~ (v2_struct_0 @ sk_D)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('174', plain, (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C))),
% 0.19/0.55      inference('clc', [status(thm)], ['172', '173'])).
% 0.19/0.55  thf('175', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('176', plain, ((v2_struct_0 @ sk_C)),
% 0.19/0.55      inference('clc', [status(thm)], ['174', '175'])).
% 0.19/0.55  thf('177', plain, ($false), inference('demod', [status(thm)], ['0', '176'])).
% 0.19/0.55  
% 0.19/0.55  % SZS output end Refutation
% 0.19/0.55  
% 0.19/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
