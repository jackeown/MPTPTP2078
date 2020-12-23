%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GLEIdMPxmC

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:13 EST 2020

% Result     : Theorem 1.95s
% Output     : Refutation 1.95s
% Verified   : 
% Statistics : Number of formulae       :  308 (2333 expanded)
%              Number of leaves         :   30 ( 684 expanded)
%              Depth                    :   31
%              Number of atoms          : 4546 (97549 expanded)
%              Number of equality atoms :   49 (1464 expanded)
%              Maximal formula depth    :   28 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(t82_tmap_1,conjecture,(
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
                        & ( v1_funct_2 @ E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
                     => ( ( m1_pre_topc @ C @ D )
                       => ! [F: $i] :
                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) )
                           => ! [G: $i] :
                                ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) )
                               => ( ( ( F = G )
                                    & ( r1_tmap_1 @ D @ B @ ( k2_tmap_1 @ A @ B @ E @ D ) @ F ) )
                                 => ( r1_tmap_1 @ C @ B @ ( k2_tmap_1 @ A @ B @ E @ C ) @ G ) ) ) ) ) ) ) ) ) ) )).

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
                          & ( v1_funct_2 @ E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                          & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
                       => ( ( m1_pre_topc @ C @ D )
                         => ! [F: $i] :
                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) )
                             => ! [G: $i] :
                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) )
                                 => ( ( ( F = G )
                                      & ( r1_tmap_1 @ D @ B @ ( k2_tmap_1 @ A @ B @ E @ D ) @ F ) )
                                   => ( r1_tmap_1 @ C @ B @ ( k2_tmap_1 @ A @ B @ E @ C ) @ G ) ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t82_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('3',plain,(
    ! [X18: $i] :
      ( ( m1_pre_topc @ X18 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('4',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t79_tmap_1,axiom,(
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
                      ( ( ~ ( v2_struct_0 @ E )
                        & ( m1_pre_topc @ E @ A ) )
                     => ( ( ( m1_pre_topc @ D @ C )
                          & ( m1_pre_topc @ E @ D ) )
                       => ! [F: $i] :
                            ( ( ( v1_funct_1 @ F )
                              & ( v1_funct_2 @ F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
                              & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) )
                           => ( r2_funct_2 @ ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) @ ( k3_tmap_1 @ A @ B @ D @ E @ ( k3_tmap_1 @ A @ B @ C @ D @ F ) ) @ ( k3_tmap_1 @ A @ B @ C @ E @ F ) ) ) ) ) ) ) ) ) )).

thf('5',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( v2_struct_0 @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ~ ( l1_pre_topc @ X19 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_pre_topc @ X20 @ X21 )
      | ~ ( m1_pre_topc @ X20 @ X22 )
      | ~ ( m1_pre_topc @ X23 @ X20 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_2 @ X24 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X19 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X19 ) ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X19 ) @ ( k3_tmap_1 @ X21 @ X19 @ X20 @ X23 @ ( k3_tmap_1 @ X21 @ X19 @ X22 @ X20 @ X24 ) ) @ ( k3_tmap_1 @ X21 @ X19 @ X22 @ X23 @ X24 ) )
      | ~ ( m1_pre_topc @ X23 @ X21 )
      | ( v2_struct_0 @ X23 )
      | ~ ( m1_pre_topc @ X22 @ X21 )
      | ( v2_struct_0 @ X22 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t79_tmap_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ sk_A @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ X0 @ sk_B @ X2 @ X1 @ ( k3_tmap_1 @ X0 @ sk_B @ sk_A @ X2 @ sk_E ) ) @ ( k3_tmap_1 @ X0 @ sk_B @ sk_A @ X1 @ sk_E ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ~ ( m1_pre_topc @ X2 @ sk_A )
      | ~ ( m1_pre_topc @ X2 @ X0 )
      | ( v2_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ sk_A @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ X0 @ sk_B @ X2 @ X1 @ ( k3_tmap_1 @ X0 @ sk_B @ sk_A @ X2 @ sk_E ) ) @ ( k3_tmap_1 @ X0 @ sk_B @ sk_A @ X1 @ sk_E ) )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ~ ( m1_pre_topc @ X2 @ sk_A )
      | ~ ( m1_pre_topc @ X2 @ X0 )
      | ( v2_struct_0 @ X2 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['6','7','8','9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ X0 @ X1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E ) ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X1 @ sk_E ) )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ X0 @ X1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E ) ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X1 @ sk_E ) )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13','14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( r2_funct_2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ X0 @ X1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E ) ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X1 @ sk_E ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ X0 @ sk_C @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E ) ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E ) )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','17'])).

thf('19',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X18: $i] :
      ( ( m1_pre_topc @ X18 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('21',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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

thf('22',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( v2_struct_0 @ X8 )
      | ~ ( v2_pre_topc @ X8 )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( m1_pre_topc @ X9 @ X10 )
      | ~ ( m1_pre_topc @ X9 @ X11 )
      | ( ( k3_tmap_1 @ X10 @ X8 @ X11 @ X9 @ X12 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X8 ) @ X12 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X8 ) ) ) )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X8 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( m1_pre_topc @ X11 @ X10 )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d5_tmap_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_A @ X0 )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_A @ X1 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_A @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_A @ X1 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['23','24','25','26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','28'])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['29','30','31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['19','34'])).

thf('36',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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

thf('42',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( v2_struct_0 @ X4 )
      | ~ ( v2_pre_topc @ X4 )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( m1_pre_topc @ X5 @ X6 )
      | ( ( k2_tmap_1 @ X6 @ X4 @ X7 @ X5 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X4 ) @ X7 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X4 ) ) ) )
      | ~ ( v1_funct_2 @ X7 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X4 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( l1_pre_topc @ X6 )
      | ~ ( v2_pre_topc @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['43','44','45','46','47','48','49'])).

thf('51',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['40','50'])).

thf('52',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference('sup+',[status(thm)],['39','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ X0 @ sk_C @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E ) ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','56'])).

thf('58',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','57'])).

thf('59',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('61',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference(clc,[status(thm)],['61','62'])).

thf('64',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['63','64'])).

thf('66',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['43','44','45','46','47','48','49'])).

thf('68',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference(clc,[status(thm)],['68','69'])).

thf('71',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ),
    inference('sup+',[status(thm)],['65','72'])).

thf('74',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['58','73','74'])).

thf('76',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X18: $i] :
      ( ( m1_pre_topc @ X18 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('80',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_tmap_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ~ ( v2_struct_0 @ B )
        & ( v2_pre_topc @ B )
        & ( l1_pre_topc @ B )
        & ( m1_pre_topc @ C @ A )
        & ( m1_pre_topc @ D @ A )
        & ( v1_funct_1 @ E )
        & ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) )
     => ( ( v1_funct_1 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) )
        & ( v1_funct_2 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
        & ( m1_subset_1 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ) )).

thf('81',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X13 @ X14 )
      | ~ ( m1_pre_topc @ X15 @ X14 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_funct_2 @ X17 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X16 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X16 ) ) ) )
      | ( m1_subset_1 @ ( k3_tmap_1 @ X14 @ X16 @ X15 @ X13 @ X17 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X16 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_tmap_1])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_pre_topc @ sk_A @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_A @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['82','83','84','85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['79','87'])).

thf('89',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['88','89','90','91'])).

thf('93',plain,
    ( ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['78','92'])).

thf('94',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['93','94'])).

thf('96',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X13 @ X14 )
      | ~ ( m1_pre_topc @ X15 @ X14 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_funct_2 @ X17 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X16 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X16 ) ) ) )
      | ( m1_subset_1 @ ( k3_tmap_1 @ X14 @ X16 @ X15 @ X13 @ X17 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X16 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_tmap_1])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['99','100','101'])).

thf('103',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    ! [X18: $i] :
      ( ( m1_pre_topc @ X18 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('105',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X13 @ X14 )
      | ~ ( m1_pre_topc @ X15 @ X14 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_funct_2 @ X17 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X16 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X16 ) ) ) )
      | ( v1_funct_1 @ ( k3_tmap_1 @ X14 @ X16 @ X15 @ X13 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_tmap_1])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_pre_topc @ sk_A @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_A @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['107','108','109','110','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['104','112'])).

thf('114',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['113','114','115','116'])).

thf('118',plain,
    ( ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['103','117'])).

thf('119',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ) ),
    inference(clc,[status(thm)],['118','119'])).

thf('121',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ),
    inference(clc,[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['102','122'])).

thf('124',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ),
    inference('sup+',[status(thm)],['65','72'])).

thf('125',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ),
    inference('sup+',[status(thm)],['65','72'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['123','124','125'])).

thf('127',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    ! [X18: $i] :
      ( ( m1_pre_topc @ X18 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('129',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X13 @ X14 )
      | ~ ( m1_pre_topc @ X15 @ X14 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_funct_2 @ X17 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X16 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X16 ) ) ) )
      | ( v1_funct_2 @ ( k3_tmap_1 @ X14 @ X16 @ X15 @ X13 @ X17 ) @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_tmap_1])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_pre_topc @ sk_A @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_A @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['131','132','133','134','135'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['128','136'])).

thf('138',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['137','138','139','140'])).

thf('142',plain,
    ( ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['127','141'])).

thf('143',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ),
    inference('sup+',[status(thm)],['65','72'])).

thf('144',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['142','143'])).

thf('145',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['144','145'])).

thf('147',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['146','147'])).

thf('149',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['126','148'])).

thf('150',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['77','149'])).

thf('151',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['150','151','152'])).

thf('154',plain,
    ( ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['76','153'])).

thf('155',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['154','155'])).

thf('157',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,(
    m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['156','157'])).

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

thf('159',plain,(
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

thf('160',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ X0 )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['158','159'])).

thf('161',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,(
    m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['95','96'])).

thf('164',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X13 @ X14 )
      | ~ ( m1_pre_topc @ X15 @ X14 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_funct_2 @ X17 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X16 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X16 ) ) ) )
      | ( v1_funct_1 @ ( k3_tmap_1 @ X14 @ X16 @ X15 @ X13 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_tmap_1])).

thf('165',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ) )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ) )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['165','166','167'])).

thf('169',plain,(
    v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ),
    inference(clc,[status(thm)],['120','121'])).

thf('170',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ) )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['168','169'])).

thf('171',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ),
    inference('sup+',[status(thm)],['65','72'])).

thf('172',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ),
    inference('sup+',[status(thm)],['65','72'])).

thf('173',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['170','171','172'])).

thf('174',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['146','147'])).

thf('175',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['173','174'])).

thf('176',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) ) ) ),
    inference('sup-',[status(thm)],['162','175'])).

thf('177',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) ) ) ),
    inference(demod,[status(thm)],['176','177','178'])).

thf('180',plain,
    ( ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['161','179'])).

thf('181',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) ) ),
    inference(clc,[status(thm)],['180','181'])).

thf('183',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,(
    v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) ),
    inference(clc,[status(thm)],['182','183'])).

thf('185',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,(
    m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['95','96'])).

thf('188',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ),
    inference('sup+',[status(thm)],['65','72'])).

thf('189',plain,(
    m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['187','188'])).

thf('190',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X13 @ X14 )
      | ~ ( m1_pre_topc @ X15 @ X14 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_funct_2 @ X17 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X16 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X16 ) ) ) )
      | ( v1_funct_2 @ ( k3_tmap_1 @ X14 @ X16 @ X15 @ X13 @ X17 ) @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_tmap_1])).

thf('191',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['189','190'])).

thf('192',plain,(
    v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ),
    inference(clc,[status(thm)],['120','121'])).

thf('193',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ),
    inference('sup+',[status(thm)],['65','72'])).

thf('194',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ),
    inference(demod,[status(thm)],['192','193'])).

thf('195',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['191','194','195','196'])).

thf('198',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['146','147'])).

thf('199',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['197','198'])).

thf('200',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['186','199'])).

thf('201',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('202',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('203',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['200','201','202'])).

thf('204',plain,
    ( ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['185','203'])).

thf('205',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['204','205'])).

thf('207',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,(
    v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['206','207'])).

thf('209',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ X0 )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['160','184','208'])).

thf('210',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) )
      = ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) ) ),
    inference('sup-',[status(thm)],['75','209'])).

thf('211',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('212',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['113','114','115','116'])).

thf('213',plain,
    ( ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['211','212'])).

thf('214',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('215',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E ) ) ),
    inference(clc,[status(thm)],['213','214'])).

thf('216',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('217',plain,(
    v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference(clc,[status(thm)],['215','216'])).

thf('218',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference('sup+',[status(thm)],['39','55'])).

thf('219',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) ),
    inference(demod,[status(thm)],['217','218'])).

thf('220',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('221',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['137','138','139','140'])).

thf('222',plain,
    ( ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['220','221'])).

thf('223',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference('sup+',[status(thm)],['39','55'])).

thf('224',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['222','223'])).

thf('225',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('226',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['224','225'])).

thf('227',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('228',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['226','227'])).

thf('229',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('230',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['88','89','90','91'])).

thf('231',plain,
    ( ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['229','230'])).

thf('232',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('233',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['231','232'])).

thf('234',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('235',plain,(
    m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['233','234'])).

thf('236',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference('sup+',[status(thm)],['39','55'])).

thf('237',plain,(
    m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['235','236'])).

thf('238',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) )
      = ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) ) ),
    inference(demod,[status(thm)],['210','219','228','237'])).

thf('239',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('240',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('241',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('242',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['240','241'])).

thf('243',plain,(
    r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('244',plain,(
    m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['187','188'])).

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

thf('245',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( v2_struct_0 @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ~ ( l1_pre_topc @ X28 )
      | ( v2_struct_0 @ X29 )
      | ~ ( m1_pre_topc @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X32 ) )
      | ~ ( m1_pre_topc @ X29 @ X32 )
      | ~ ( r1_tmap_1 @ X32 @ X28 @ X33 @ X31 )
      | ( X31 != X34 )
      | ( r1_tmap_1 @ X29 @ X28 @ ( k3_tmap_1 @ X30 @ X28 @ X32 @ X29 @ X33 ) @ X34 )
      | ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ X29 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X28 ) ) ) )
      | ~ ( v1_funct_2 @ X33 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X28 ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( m1_pre_topc @ X32 @ X30 )
      | ( v2_struct_0 @ X32 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t81_tmap_1])).

thf('246',plain,(
    ! [X28: $i,X29: $i,X30: $i,X32: $i,X33: $i,X34: $i] :
      ( ( v2_struct_0 @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ~ ( l1_pre_topc @ X30 )
      | ( v2_struct_0 @ X32 )
      | ~ ( m1_pre_topc @ X32 @ X30 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_funct_2 @ X33 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X28 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X28 ) ) ) )
      | ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ X29 ) )
      | ( r1_tmap_1 @ X29 @ X28 @ ( k3_tmap_1 @ X30 @ X28 @ X32 @ X29 @ X33 ) @ X34 )
      | ~ ( r1_tmap_1 @ X32 @ X28 @ X33 @ X34 )
      | ~ ( m1_pre_topc @ X29 @ X32 )
      | ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ X32 ) )
      | ~ ( m1_pre_topc @ X29 @ X30 )
      | ( v2_struct_0 @ X29 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(simplify,[status(thm)],['245'])).

thf('247',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ X2 )
      | ( r1_tmap_1 @ X0 @ sk_B @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['244','246'])).

thf('248',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('249',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('250',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['146','147'])).

thf('251',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ),
    inference(demod,[status(thm)],['192','193'])).

thf('252',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ X2 )
      | ( r1_tmap_1 @ X0 @ sk_B @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['247','248','249','250','251'])).

thf('253',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ X1 ) )
      | ( r1_tmap_1 @ X1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ sk_F )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['243','252'])).

thf('254',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('255',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ X1 ) )
      | ( r1_tmap_1 @ X1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ sk_F )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['253','254'])).

thf('256',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ~ ( m1_pre_topc @ sk_C @ sk_D )
      | ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ sk_F )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['242','255'])).

thf('257',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('258',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ sk_F )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['256','257'])).

thf('259',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ~ ( m1_pre_topc @ sk_D @ sk_A )
    | ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ sk_F )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['239','258'])).

thf('260',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('261',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('262',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('263',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ sk_F )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['259','260','261','262'])).

thf('264',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['238','263'])).

thf('265',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_C @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F ) ),
    inference(simplify,[status(thm)],['264'])).

thf('266',plain,(
    ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('267',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('268',plain,(
    ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F ) ),
    inference(demod,[status(thm)],['266','267'])).

thf('269',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['265','268'])).

thf('270',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('271',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['269','270'])).

thf('272',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('273',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['271','272'])).

thf('274',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('275',plain,(
    v2_struct_0 @ sk_C ),
    inference(clc,[status(thm)],['273','274'])).

thf('276',plain,(
    $false ),
    inference(demod,[status(thm)],['0','275'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GLEIdMPxmC
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:46:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.95/2.11  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.95/2.11  % Solved by: fo/fo7.sh
% 1.95/2.11  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.95/2.11  % done 2319 iterations in 1.648s
% 1.95/2.11  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.95/2.11  % SZS output start Refutation
% 1.95/2.11  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.95/2.11  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 1.95/2.11  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.95/2.11  thf(sk_C_type, type, sk_C: $i).
% 1.95/2.11  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.95/2.11  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.95/2.11  thf(sk_B_type, type, sk_B: $i).
% 1.95/2.11  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.95/2.11  thf(sk_A_type, type, sk_A: $i).
% 1.95/2.11  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 1.95/2.11  thf(sk_E_type, type, sk_E: $i).
% 1.95/2.11  thf(sk_F_type, type, sk_F: $i).
% 1.95/2.11  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 1.95/2.11  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 1.95/2.11  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 1.95/2.11  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 1.95/2.11  thf(sk_D_type, type, sk_D: $i).
% 1.95/2.11  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.95/2.11  thf(sk_G_type, type, sk_G: $i).
% 1.95/2.11  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.95/2.11  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.95/2.11  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.95/2.11  thf(t82_tmap_1, conjecture,
% 1.95/2.11    (![A:$i]:
% 1.95/2.11     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.95/2.11       ( ![B:$i]:
% 1.95/2.11         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.95/2.11             ( l1_pre_topc @ B ) ) =>
% 1.95/2.11           ( ![C:$i]:
% 1.95/2.11             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.95/2.11               ( ![D:$i]:
% 1.95/2.11                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 1.95/2.11                   ( ![E:$i]:
% 1.95/2.11                     ( ( ( v1_funct_1 @ E ) & 
% 1.95/2.11                         ( v1_funct_2 @
% 1.95/2.11                           E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.95/2.11                         ( m1_subset_1 @
% 1.95/2.11                           E @ 
% 1.95/2.11                           ( k1_zfmisc_1 @
% 1.95/2.11                             ( k2_zfmisc_1 @
% 1.95/2.11                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.95/2.11                       ( ( m1_pre_topc @ C @ D ) =>
% 1.95/2.11                         ( ![F:$i]:
% 1.95/2.11                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 1.95/2.11                             ( ![G:$i]:
% 1.95/2.11                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 1.95/2.11                                 ( ( ( ( F ) = ( G ) ) & 
% 1.95/2.11                                     ( r1_tmap_1 @
% 1.95/2.11                                       D @ B @ ( k2_tmap_1 @ A @ B @ E @ D ) @ 
% 1.95/2.11                                       F ) ) =>
% 1.95/2.11                                   ( r1_tmap_1 @
% 1.95/2.11                                     C @ B @ ( k2_tmap_1 @ A @ B @ E @ C ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.95/2.11  thf(zf_stmt_0, negated_conjecture,
% 1.95/2.11    (~( ![A:$i]:
% 1.95/2.11        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.95/2.11            ( l1_pre_topc @ A ) ) =>
% 1.95/2.11          ( ![B:$i]:
% 1.95/2.11            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.95/2.11                ( l1_pre_topc @ B ) ) =>
% 1.95/2.11              ( ![C:$i]:
% 1.95/2.11                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.95/2.11                  ( ![D:$i]:
% 1.95/2.11                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 1.95/2.11                      ( ![E:$i]:
% 1.95/2.11                        ( ( ( v1_funct_1 @ E ) & 
% 1.95/2.11                            ( v1_funct_2 @
% 1.95/2.11                              E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.95/2.11                            ( m1_subset_1 @
% 1.95/2.11                              E @ 
% 1.95/2.11                              ( k1_zfmisc_1 @
% 1.95/2.11                                ( k2_zfmisc_1 @
% 1.95/2.11                                  ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.95/2.11                          ( ( m1_pre_topc @ C @ D ) =>
% 1.95/2.11                            ( ![F:$i]:
% 1.95/2.11                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 1.95/2.11                                ( ![G:$i]:
% 1.95/2.11                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 1.95/2.11                                    ( ( ( ( F ) = ( G ) ) & 
% 1.95/2.11                                        ( r1_tmap_1 @
% 1.95/2.11                                          D @ B @ 
% 1.95/2.11                                          ( k2_tmap_1 @ A @ B @ E @ D ) @ F ) ) =>
% 1.95/2.11                                      ( r1_tmap_1 @
% 1.95/2.11                                        C @ B @ 
% 1.95/2.11                                        ( k2_tmap_1 @ A @ B @ E @ C ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 1.95/2.11    inference('cnf.neg', [status(esa)], [t82_tmap_1])).
% 1.95/2.11  thf('0', plain, (~ (v2_struct_0 @ sk_C)),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('1', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('2', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf(t2_tsep_1, axiom,
% 1.95/2.11    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 1.95/2.11  thf('3', plain,
% 1.95/2.11      (![X18 : $i]: ((m1_pre_topc @ X18 @ X18) | ~ (l1_pre_topc @ X18))),
% 1.95/2.11      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.95/2.11  thf('4', plain,
% 1.95/2.11      ((m1_subset_1 @ sk_E @ 
% 1.95/2.11        (k1_zfmisc_1 @ 
% 1.95/2.11         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf(t79_tmap_1, axiom,
% 1.95/2.11    (![A:$i]:
% 1.95/2.11     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.95/2.11       ( ![B:$i]:
% 1.95/2.11         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.95/2.11             ( l1_pre_topc @ B ) ) =>
% 1.95/2.11           ( ![C:$i]:
% 1.95/2.11             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.95/2.11               ( ![D:$i]:
% 1.95/2.11                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 1.95/2.11                   ( ![E:$i]:
% 1.95/2.11                     ( ( ( ~( v2_struct_0 @ E ) ) & ( m1_pre_topc @ E @ A ) ) =>
% 1.95/2.11                       ( ( ( m1_pre_topc @ D @ C ) & ( m1_pre_topc @ E @ D ) ) =>
% 1.95/2.11                         ( ![F:$i]:
% 1.95/2.11                           ( ( ( v1_funct_1 @ F ) & 
% 1.95/2.11                               ( v1_funct_2 @
% 1.95/2.11                                 F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 1.95/2.11                               ( m1_subset_1 @
% 1.95/2.11                                 F @ 
% 1.95/2.11                                 ( k1_zfmisc_1 @
% 1.95/2.11                                   ( k2_zfmisc_1 @
% 1.95/2.11                                     ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.95/2.11                             ( r2_funct_2 @
% 1.95/2.11                               ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) @ 
% 1.95/2.11                               ( k3_tmap_1 @
% 1.95/2.11                                 A @ B @ D @ E @ 
% 1.95/2.11                                 ( k3_tmap_1 @ A @ B @ C @ D @ F ) ) @ 
% 1.95/2.11                               ( k3_tmap_1 @ A @ B @ C @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.95/2.11  thf('5', plain,
% 1.95/2.11      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 1.95/2.11         ((v2_struct_0 @ X19)
% 1.95/2.11          | ~ (v2_pre_topc @ X19)
% 1.95/2.11          | ~ (l1_pre_topc @ X19)
% 1.95/2.11          | (v2_struct_0 @ X20)
% 1.95/2.11          | ~ (m1_pre_topc @ X20 @ X21)
% 1.95/2.11          | ~ (m1_pre_topc @ X20 @ X22)
% 1.95/2.11          | ~ (m1_pre_topc @ X23 @ X20)
% 1.95/2.11          | ~ (v1_funct_1 @ X24)
% 1.95/2.11          | ~ (v1_funct_2 @ X24 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X19))
% 1.95/2.11          | ~ (m1_subset_1 @ X24 @ 
% 1.95/2.11               (k1_zfmisc_1 @ 
% 1.95/2.11                (k2_zfmisc_1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X19))))
% 1.95/2.11          | (r2_funct_2 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X19) @ 
% 1.95/2.11             (k3_tmap_1 @ X21 @ X19 @ X20 @ X23 @ 
% 1.95/2.11              (k3_tmap_1 @ X21 @ X19 @ X22 @ X20 @ X24)) @ 
% 1.95/2.11             (k3_tmap_1 @ X21 @ X19 @ X22 @ X23 @ X24))
% 1.95/2.11          | ~ (m1_pre_topc @ X23 @ X21)
% 1.95/2.11          | (v2_struct_0 @ X23)
% 1.95/2.11          | ~ (m1_pre_topc @ X22 @ X21)
% 1.95/2.11          | (v2_struct_0 @ X22)
% 1.95/2.11          | ~ (l1_pre_topc @ X21)
% 1.95/2.11          | ~ (v2_pre_topc @ X21)
% 1.95/2.11          | (v2_struct_0 @ X21))),
% 1.95/2.11      inference('cnf', [status(esa)], [t79_tmap_1])).
% 1.95/2.11  thf('6', plain,
% 1.95/2.11      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.95/2.11         ((v2_struct_0 @ X0)
% 1.95/2.11          | ~ (v2_pre_topc @ X0)
% 1.95/2.11          | ~ (l1_pre_topc @ X0)
% 1.95/2.11          | (v2_struct_0 @ sk_A)
% 1.95/2.11          | ~ (m1_pre_topc @ sk_A @ X0)
% 1.95/2.11          | (v2_struct_0 @ X1)
% 1.95/2.11          | ~ (m1_pre_topc @ X1 @ X0)
% 1.95/2.11          | (r2_funct_2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B) @ 
% 1.95/2.11             (k3_tmap_1 @ X0 @ sk_B @ X2 @ X1 @ 
% 1.95/2.11              (k3_tmap_1 @ X0 @ sk_B @ sk_A @ X2 @ sk_E)) @ 
% 1.95/2.11             (k3_tmap_1 @ X0 @ sk_B @ sk_A @ X1 @ sk_E))
% 1.95/2.11          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 1.95/2.11          | ~ (v1_funct_1 @ sk_E)
% 1.95/2.11          | ~ (m1_pre_topc @ X1 @ X2)
% 1.95/2.11          | ~ (m1_pre_topc @ X2 @ sk_A)
% 1.95/2.11          | ~ (m1_pre_topc @ X2 @ X0)
% 1.95/2.11          | (v2_struct_0 @ X2)
% 1.95/2.11          | ~ (l1_pre_topc @ sk_B)
% 1.95/2.11          | ~ (v2_pre_topc @ sk_B)
% 1.95/2.11          | (v2_struct_0 @ sk_B))),
% 1.95/2.11      inference('sup-', [status(thm)], ['4', '5'])).
% 1.95/2.11  thf('7', plain,
% 1.95/2.11      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('8', plain, ((v1_funct_1 @ sk_E)),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('9', plain, ((l1_pre_topc @ sk_B)),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('10', plain, ((v2_pre_topc @ sk_B)),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('11', plain,
% 1.95/2.11      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.95/2.11         ((v2_struct_0 @ X0)
% 1.95/2.11          | ~ (v2_pre_topc @ X0)
% 1.95/2.11          | ~ (l1_pre_topc @ X0)
% 1.95/2.11          | (v2_struct_0 @ sk_A)
% 1.95/2.11          | ~ (m1_pre_topc @ sk_A @ X0)
% 1.95/2.11          | (v2_struct_0 @ X1)
% 1.95/2.11          | ~ (m1_pre_topc @ X1 @ X0)
% 1.95/2.11          | (r2_funct_2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B) @ 
% 1.95/2.11             (k3_tmap_1 @ X0 @ sk_B @ X2 @ X1 @ 
% 1.95/2.11              (k3_tmap_1 @ X0 @ sk_B @ sk_A @ X2 @ sk_E)) @ 
% 1.95/2.11             (k3_tmap_1 @ X0 @ sk_B @ sk_A @ X1 @ sk_E))
% 1.95/2.11          | ~ (m1_pre_topc @ X1 @ X2)
% 1.95/2.11          | ~ (m1_pre_topc @ X2 @ sk_A)
% 1.95/2.11          | ~ (m1_pre_topc @ X2 @ X0)
% 1.95/2.11          | (v2_struct_0 @ X2)
% 1.95/2.11          | (v2_struct_0 @ sk_B))),
% 1.95/2.11      inference('demod', [status(thm)], ['6', '7', '8', '9', '10'])).
% 1.95/2.11  thf('12', plain,
% 1.95/2.11      (![X0 : $i, X1 : $i]:
% 1.95/2.11         (~ (l1_pre_topc @ sk_A)
% 1.95/2.11          | (v2_struct_0 @ sk_B)
% 1.95/2.11          | (v2_struct_0 @ X0)
% 1.95/2.11          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.95/2.11          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.95/2.11          | ~ (m1_pre_topc @ X1 @ X0)
% 1.95/2.11          | (r2_funct_2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B) @ 
% 1.95/2.11             (k3_tmap_1 @ sk_A @ sk_B @ X0 @ X1 @ 
% 1.95/2.11              (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E)) @ 
% 1.95/2.11             (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X1 @ sk_E))
% 1.95/2.11          | ~ (m1_pre_topc @ X1 @ sk_A)
% 1.95/2.11          | (v2_struct_0 @ X1)
% 1.95/2.11          | (v2_struct_0 @ sk_A)
% 1.95/2.11          | ~ (l1_pre_topc @ sk_A)
% 1.95/2.11          | ~ (v2_pre_topc @ sk_A)
% 1.95/2.11          | (v2_struct_0 @ sk_A))),
% 1.95/2.11      inference('sup-', [status(thm)], ['3', '11'])).
% 1.95/2.11  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('15', plain, ((v2_pre_topc @ sk_A)),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('16', plain,
% 1.95/2.11      (![X0 : $i, X1 : $i]:
% 1.95/2.11         ((v2_struct_0 @ sk_B)
% 1.95/2.11          | (v2_struct_0 @ X0)
% 1.95/2.11          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.95/2.11          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.95/2.11          | ~ (m1_pre_topc @ X1 @ X0)
% 1.95/2.11          | (r2_funct_2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B) @ 
% 1.95/2.11             (k3_tmap_1 @ sk_A @ sk_B @ X0 @ X1 @ 
% 1.95/2.11              (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E)) @ 
% 1.95/2.11             (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X1 @ sk_E))
% 1.95/2.11          | ~ (m1_pre_topc @ X1 @ sk_A)
% 1.95/2.11          | (v2_struct_0 @ X1)
% 1.95/2.11          | (v2_struct_0 @ sk_A)
% 1.95/2.11          | (v2_struct_0 @ sk_A))),
% 1.95/2.11      inference('demod', [status(thm)], ['12', '13', '14', '15'])).
% 1.95/2.11  thf('17', plain,
% 1.95/2.11      (![X0 : $i, X1 : $i]:
% 1.95/2.11         ((v2_struct_0 @ sk_A)
% 1.95/2.11          | (v2_struct_0 @ X1)
% 1.95/2.11          | ~ (m1_pre_topc @ X1 @ sk_A)
% 1.95/2.11          | (r2_funct_2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B) @ 
% 1.95/2.11             (k3_tmap_1 @ sk_A @ sk_B @ X0 @ X1 @ 
% 1.95/2.11              (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E)) @ 
% 1.95/2.11             (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X1 @ sk_E))
% 1.95/2.11          | ~ (m1_pre_topc @ X1 @ X0)
% 1.95/2.11          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.95/2.11          | (v2_struct_0 @ X0)
% 1.95/2.11          | (v2_struct_0 @ sk_B))),
% 1.95/2.11      inference('simplify', [status(thm)], ['16'])).
% 1.95/2.11  thf('18', plain,
% 1.95/2.11      (![X0 : $i]:
% 1.95/2.11         ((v2_struct_0 @ sk_B)
% 1.95/2.11          | (v2_struct_0 @ X0)
% 1.95/2.11          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.95/2.11          | ~ (m1_pre_topc @ sk_C @ X0)
% 1.95/2.11          | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.95/2.11             (k3_tmap_1 @ sk_A @ sk_B @ X0 @ sk_C @ 
% 1.95/2.11              (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E)) @ 
% 1.95/2.11             (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E))
% 1.95/2.11          | (v2_struct_0 @ sk_C)
% 1.95/2.11          | (v2_struct_0 @ sk_A))),
% 1.95/2.11      inference('sup-', [status(thm)], ['2', '17'])).
% 1.95/2.11  thf('19', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('20', plain,
% 1.95/2.11      (![X18 : $i]: ((m1_pre_topc @ X18 @ X18) | ~ (l1_pre_topc @ X18))),
% 1.95/2.11      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.95/2.11  thf('21', plain,
% 1.95/2.11      ((m1_subset_1 @ sk_E @ 
% 1.95/2.11        (k1_zfmisc_1 @ 
% 1.95/2.11         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf(d5_tmap_1, axiom,
% 1.95/2.11    (![A:$i]:
% 1.95/2.11     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.95/2.11       ( ![B:$i]:
% 1.95/2.11         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.95/2.11             ( l1_pre_topc @ B ) ) =>
% 1.95/2.11           ( ![C:$i]:
% 1.95/2.11             ( ( m1_pre_topc @ C @ A ) =>
% 1.95/2.11               ( ![D:$i]:
% 1.95/2.11                 ( ( m1_pre_topc @ D @ A ) =>
% 1.95/2.11                   ( ![E:$i]:
% 1.95/2.11                     ( ( ( v1_funct_1 @ E ) & 
% 1.95/2.11                         ( v1_funct_2 @
% 1.95/2.11                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 1.95/2.11                         ( m1_subset_1 @
% 1.95/2.11                           E @ 
% 1.95/2.11                           ( k1_zfmisc_1 @
% 1.95/2.11                             ( k2_zfmisc_1 @
% 1.95/2.11                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.95/2.11                       ( ( m1_pre_topc @ D @ C ) =>
% 1.95/2.11                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 1.95/2.11                           ( k2_partfun1 @
% 1.95/2.11                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 1.95/2.11                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.95/2.11  thf('22', plain,
% 1.95/2.11      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 1.95/2.11         ((v2_struct_0 @ X8)
% 1.95/2.11          | ~ (v2_pre_topc @ X8)
% 1.95/2.11          | ~ (l1_pre_topc @ X8)
% 1.95/2.11          | ~ (m1_pre_topc @ X9 @ X10)
% 1.95/2.11          | ~ (m1_pre_topc @ X9 @ X11)
% 1.95/2.11          | ((k3_tmap_1 @ X10 @ X8 @ X11 @ X9 @ X12)
% 1.95/2.11              = (k2_partfun1 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X8) @ 
% 1.95/2.11                 X12 @ (u1_struct_0 @ X9)))
% 1.95/2.11          | ~ (m1_subset_1 @ X12 @ 
% 1.95/2.11               (k1_zfmisc_1 @ 
% 1.95/2.11                (k2_zfmisc_1 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X8))))
% 1.95/2.11          | ~ (v1_funct_2 @ X12 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X8))
% 1.95/2.11          | ~ (v1_funct_1 @ X12)
% 1.95/2.11          | ~ (m1_pre_topc @ X11 @ X10)
% 1.95/2.11          | ~ (l1_pre_topc @ X10)
% 1.95/2.11          | ~ (v2_pre_topc @ X10)
% 1.95/2.11          | (v2_struct_0 @ X10))),
% 1.95/2.11      inference('cnf', [status(esa)], [d5_tmap_1])).
% 1.95/2.11  thf('23', plain,
% 1.95/2.11      (![X0 : $i, X1 : $i]:
% 1.95/2.11         ((v2_struct_0 @ X0)
% 1.95/2.11          | ~ (v2_pre_topc @ X0)
% 1.95/2.11          | ~ (l1_pre_topc @ X0)
% 1.95/2.11          | ~ (m1_pre_topc @ sk_A @ X0)
% 1.95/2.11          | ~ (v1_funct_1 @ sk_E)
% 1.95/2.11          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 1.95/2.11          | ((k3_tmap_1 @ X0 @ sk_B @ sk_A @ X1 @ sk_E)
% 1.95/2.11              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 1.95/2.11                 sk_E @ (u1_struct_0 @ X1)))
% 1.95/2.11          | ~ (m1_pre_topc @ X1 @ sk_A)
% 1.95/2.11          | ~ (m1_pre_topc @ X1 @ X0)
% 1.95/2.11          | ~ (l1_pre_topc @ sk_B)
% 1.95/2.11          | ~ (v2_pre_topc @ sk_B)
% 1.95/2.11          | (v2_struct_0 @ sk_B))),
% 1.95/2.11      inference('sup-', [status(thm)], ['21', '22'])).
% 1.95/2.11  thf('24', plain, ((v1_funct_1 @ sk_E)),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('25', plain,
% 1.95/2.11      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('26', plain, ((l1_pre_topc @ sk_B)),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('27', plain, ((v2_pre_topc @ sk_B)),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('28', plain,
% 1.95/2.11      (![X0 : $i, X1 : $i]:
% 1.95/2.11         ((v2_struct_0 @ X0)
% 1.95/2.11          | ~ (v2_pre_topc @ X0)
% 1.95/2.11          | ~ (l1_pre_topc @ X0)
% 1.95/2.11          | ~ (m1_pre_topc @ sk_A @ X0)
% 1.95/2.11          | ((k3_tmap_1 @ X0 @ sk_B @ sk_A @ X1 @ sk_E)
% 1.95/2.11              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 1.95/2.11                 sk_E @ (u1_struct_0 @ X1)))
% 1.95/2.11          | ~ (m1_pre_topc @ X1 @ sk_A)
% 1.95/2.11          | ~ (m1_pre_topc @ X1 @ X0)
% 1.95/2.11          | (v2_struct_0 @ sk_B))),
% 1.95/2.11      inference('demod', [status(thm)], ['23', '24', '25', '26', '27'])).
% 1.95/2.11  thf('29', plain,
% 1.95/2.11      (![X0 : $i]:
% 1.95/2.11         (~ (l1_pre_topc @ sk_A)
% 1.95/2.11          | (v2_struct_0 @ sk_B)
% 1.95/2.11          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.95/2.11          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.95/2.11          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E)
% 1.95/2.11              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 1.95/2.11                 sk_E @ (u1_struct_0 @ X0)))
% 1.95/2.11          | ~ (l1_pre_topc @ sk_A)
% 1.95/2.11          | ~ (v2_pre_topc @ sk_A)
% 1.95/2.11          | (v2_struct_0 @ sk_A))),
% 1.95/2.11      inference('sup-', [status(thm)], ['20', '28'])).
% 1.95/2.11  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('32', plain, ((v2_pre_topc @ sk_A)),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('33', plain,
% 1.95/2.11      (![X0 : $i]:
% 1.95/2.11         ((v2_struct_0 @ sk_B)
% 1.95/2.11          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.95/2.11          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.95/2.11          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E)
% 1.95/2.11              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 1.95/2.11                 sk_E @ (u1_struct_0 @ X0)))
% 1.95/2.11          | (v2_struct_0 @ sk_A))),
% 1.95/2.11      inference('demod', [status(thm)], ['29', '30', '31', '32'])).
% 1.95/2.11  thf('34', plain,
% 1.95/2.11      (![X0 : $i]:
% 1.95/2.11         ((v2_struct_0 @ sk_A)
% 1.95/2.11          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E)
% 1.95/2.11              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 1.95/2.11                 sk_E @ (u1_struct_0 @ X0)))
% 1.95/2.11          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.95/2.11          | (v2_struct_0 @ sk_B))),
% 1.95/2.11      inference('simplify', [status(thm)], ['33'])).
% 1.95/2.11  thf('35', plain,
% 1.95/2.11      (((v2_struct_0 @ sk_B)
% 1.95/2.11        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E)
% 1.95/2.11            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 1.95/2.11               sk_E @ (u1_struct_0 @ sk_C)))
% 1.95/2.11        | (v2_struct_0 @ sk_A))),
% 1.95/2.11      inference('sup-', [status(thm)], ['19', '34'])).
% 1.95/2.11  thf('36', plain, (~ (v2_struct_0 @ sk_B)),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('37', plain,
% 1.95/2.11      (((v2_struct_0 @ sk_A)
% 1.95/2.11        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E)
% 1.95/2.11            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 1.95/2.11               sk_E @ (u1_struct_0 @ sk_C))))),
% 1.95/2.11      inference('clc', [status(thm)], ['35', '36'])).
% 1.95/2.11  thf('38', plain, (~ (v2_struct_0 @ sk_A)),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('39', plain,
% 1.95/2.11      (((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E)
% 1.95/2.11         = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 1.95/2.11            (u1_struct_0 @ sk_C)))),
% 1.95/2.11      inference('clc', [status(thm)], ['37', '38'])).
% 1.95/2.11  thf('40', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('41', plain,
% 1.95/2.11      ((m1_subset_1 @ sk_E @ 
% 1.95/2.11        (k1_zfmisc_1 @ 
% 1.95/2.11         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf(d4_tmap_1, axiom,
% 1.95/2.11    (![A:$i]:
% 1.95/2.11     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.95/2.11       ( ![B:$i]:
% 1.95/2.11         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.95/2.11             ( l1_pre_topc @ B ) ) =>
% 1.95/2.11           ( ![C:$i]:
% 1.95/2.11             ( ( ( v1_funct_1 @ C ) & 
% 1.95/2.11                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.95/2.11                 ( m1_subset_1 @
% 1.95/2.11                   C @ 
% 1.95/2.11                   ( k1_zfmisc_1 @
% 1.95/2.11                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.95/2.11               ( ![D:$i]:
% 1.95/2.11                 ( ( m1_pre_topc @ D @ A ) =>
% 1.95/2.11                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 1.95/2.11                     ( k2_partfun1 @
% 1.95/2.11                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 1.95/2.11                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 1.95/2.11  thf('42', plain,
% 1.95/2.11      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 1.95/2.11         ((v2_struct_0 @ X4)
% 1.95/2.11          | ~ (v2_pre_topc @ X4)
% 1.95/2.11          | ~ (l1_pre_topc @ X4)
% 1.95/2.11          | ~ (m1_pre_topc @ X5 @ X6)
% 1.95/2.11          | ((k2_tmap_1 @ X6 @ X4 @ X7 @ X5)
% 1.95/2.11              = (k2_partfun1 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X4) @ X7 @ 
% 1.95/2.11                 (u1_struct_0 @ X5)))
% 1.95/2.11          | ~ (m1_subset_1 @ X7 @ 
% 1.95/2.11               (k1_zfmisc_1 @ 
% 1.95/2.11                (k2_zfmisc_1 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X4))))
% 1.95/2.11          | ~ (v1_funct_2 @ X7 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X4))
% 1.95/2.11          | ~ (v1_funct_1 @ X7)
% 1.95/2.11          | ~ (l1_pre_topc @ X6)
% 1.95/2.11          | ~ (v2_pre_topc @ X6)
% 1.95/2.11          | (v2_struct_0 @ X6))),
% 1.95/2.11      inference('cnf', [status(esa)], [d4_tmap_1])).
% 1.95/2.11  thf('43', plain,
% 1.95/2.11      (![X0 : $i]:
% 1.95/2.11         ((v2_struct_0 @ sk_A)
% 1.95/2.11          | ~ (v2_pre_topc @ sk_A)
% 1.95/2.11          | ~ (l1_pre_topc @ sk_A)
% 1.95/2.11          | ~ (v1_funct_1 @ sk_E)
% 1.95/2.11          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 1.95/2.11          | ((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0)
% 1.95/2.11              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 1.95/2.11                 sk_E @ (u1_struct_0 @ X0)))
% 1.95/2.11          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.95/2.11          | ~ (l1_pre_topc @ sk_B)
% 1.95/2.11          | ~ (v2_pre_topc @ sk_B)
% 1.95/2.11          | (v2_struct_0 @ sk_B))),
% 1.95/2.11      inference('sup-', [status(thm)], ['41', '42'])).
% 1.95/2.11  thf('44', plain, ((v2_pre_topc @ sk_A)),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('46', plain, ((v1_funct_1 @ sk_E)),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('47', plain,
% 1.95/2.11      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('48', plain, ((l1_pre_topc @ sk_B)),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('49', plain, ((v2_pre_topc @ sk_B)),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('50', plain,
% 1.95/2.11      (![X0 : $i]:
% 1.95/2.11         ((v2_struct_0 @ sk_A)
% 1.95/2.11          | ((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0)
% 1.95/2.11              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 1.95/2.11                 sk_E @ (u1_struct_0 @ X0)))
% 1.95/2.11          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.95/2.11          | (v2_struct_0 @ sk_B))),
% 1.95/2.11      inference('demod', [status(thm)],
% 1.95/2.11                ['43', '44', '45', '46', '47', '48', '49'])).
% 1.95/2.11  thf('51', plain,
% 1.95/2.11      (((v2_struct_0 @ sk_B)
% 1.95/2.11        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C)
% 1.95/2.11            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 1.95/2.11               sk_E @ (u1_struct_0 @ sk_C)))
% 1.95/2.11        | (v2_struct_0 @ sk_A))),
% 1.95/2.11      inference('sup-', [status(thm)], ['40', '50'])).
% 1.95/2.11  thf('52', plain, (~ (v2_struct_0 @ sk_B)),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('53', plain,
% 1.95/2.11      (((v2_struct_0 @ sk_A)
% 1.95/2.11        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C)
% 1.95/2.11            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 1.95/2.11               sk_E @ (u1_struct_0 @ sk_C))))),
% 1.95/2.11      inference('clc', [status(thm)], ['51', '52'])).
% 1.95/2.11  thf('54', plain, (~ (v2_struct_0 @ sk_A)),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('55', plain,
% 1.95/2.11      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C)
% 1.95/2.11         = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 1.95/2.11            (u1_struct_0 @ sk_C)))),
% 1.95/2.11      inference('clc', [status(thm)], ['53', '54'])).
% 1.95/2.11  thf('56', plain,
% 1.95/2.11      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C)
% 1.95/2.11         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E))),
% 1.95/2.11      inference('sup+', [status(thm)], ['39', '55'])).
% 1.95/2.11  thf('57', plain,
% 1.95/2.11      (![X0 : $i]:
% 1.95/2.11         ((v2_struct_0 @ sk_B)
% 1.95/2.11          | (v2_struct_0 @ X0)
% 1.95/2.11          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.95/2.11          | ~ (m1_pre_topc @ sk_C @ X0)
% 1.95/2.11          | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.95/2.11             (k3_tmap_1 @ sk_A @ sk_B @ X0 @ sk_C @ 
% 1.95/2.11              (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E)) @ 
% 1.95/2.11             (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C))
% 1.95/2.11          | (v2_struct_0 @ sk_C)
% 1.95/2.11          | (v2_struct_0 @ sk_A))),
% 1.95/2.11      inference('demod', [status(thm)], ['18', '56'])).
% 1.95/2.11  thf('58', plain,
% 1.95/2.11      (((v2_struct_0 @ sk_A)
% 1.95/2.11        | (v2_struct_0 @ sk_C)
% 1.95/2.11        | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.95/2.11           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ 
% 1.95/2.11            (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E)) @ 
% 1.95/2.11           (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C))
% 1.95/2.11        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 1.95/2.11        | (v2_struct_0 @ sk_D)
% 1.95/2.11        | (v2_struct_0 @ sk_B))),
% 1.95/2.11      inference('sup-', [status(thm)], ['1', '57'])).
% 1.95/2.11  thf('59', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('60', plain,
% 1.95/2.11      (![X0 : $i]:
% 1.95/2.11         ((v2_struct_0 @ sk_A)
% 1.95/2.11          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E)
% 1.95/2.11              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 1.95/2.11                 sk_E @ (u1_struct_0 @ X0)))
% 1.95/2.11          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.95/2.11          | (v2_struct_0 @ sk_B))),
% 1.95/2.11      inference('simplify', [status(thm)], ['33'])).
% 1.95/2.11  thf('61', plain,
% 1.95/2.11      (((v2_struct_0 @ sk_B)
% 1.95/2.11        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E)
% 1.95/2.11            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 1.95/2.11               sk_E @ (u1_struct_0 @ sk_D)))
% 1.95/2.11        | (v2_struct_0 @ sk_A))),
% 1.95/2.11      inference('sup-', [status(thm)], ['59', '60'])).
% 1.95/2.11  thf('62', plain, (~ (v2_struct_0 @ sk_B)),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('63', plain,
% 1.95/2.11      (((v2_struct_0 @ sk_A)
% 1.95/2.11        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E)
% 1.95/2.11            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 1.95/2.11               sk_E @ (u1_struct_0 @ sk_D))))),
% 1.95/2.11      inference('clc', [status(thm)], ['61', '62'])).
% 1.95/2.11  thf('64', plain, (~ (v2_struct_0 @ sk_A)),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('65', plain,
% 1.95/2.11      (((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E)
% 1.95/2.11         = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 1.95/2.11            (u1_struct_0 @ sk_D)))),
% 1.95/2.11      inference('clc', [status(thm)], ['63', '64'])).
% 1.95/2.11  thf('66', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('67', plain,
% 1.95/2.11      (![X0 : $i]:
% 1.95/2.11         ((v2_struct_0 @ sk_A)
% 1.95/2.11          | ((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0)
% 1.95/2.11              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 1.95/2.11                 sk_E @ (u1_struct_0 @ X0)))
% 1.95/2.11          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.95/2.11          | (v2_struct_0 @ sk_B))),
% 1.95/2.11      inference('demod', [status(thm)],
% 1.95/2.11                ['43', '44', '45', '46', '47', '48', '49'])).
% 1.95/2.11  thf('68', plain,
% 1.95/2.11      (((v2_struct_0 @ sk_B)
% 1.95/2.11        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 1.95/2.11            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 1.95/2.11               sk_E @ (u1_struct_0 @ sk_D)))
% 1.95/2.11        | (v2_struct_0 @ sk_A))),
% 1.95/2.11      inference('sup-', [status(thm)], ['66', '67'])).
% 1.95/2.11  thf('69', plain, (~ (v2_struct_0 @ sk_B)),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('70', plain,
% 1.95/2.11      (((v2_struct_0 @ sk_A)
% 1.95/2.11        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 1.95/2.11            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 1.95/2.11               sk_E @ (u1_struct_0 @ sk_D))))),
% 1.95/2.11      inference('clc', [status(thm)], ['68', '69'])).
% 1.95/2.11  thf('71', plain, (~ (v2_struct_0 @ sk_A)),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('72', plain,
% 1.95/2.11      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 1.95/2.11         = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 1.95/2.11            (u1_struct_0 @ sk_D)))),
% 1.95/2.11      inference('clc', [status(thm)], ['70', '71'])).
% 1.95/2.11  thf('73', plain,
% 1.95/2.11      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 1.95/2.11         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))),
% 1.95/2.11      inference('sup+', [status(thm)], ['65', '72'])).
% 1.95/2.11  thf('74', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('75', plain,
% 1.95/2.11      (((v2_struct_0 @ sk_A)
% 1.95/2.11        | (v2_struct_0 @ sk_C)
% 1.95/2.11        | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.95/2.11           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ 
% 1.95/2.11            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 1.95/2.11           (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C))
% 1.95/2.11        | (v2_struct_0 @ sk_D)
% 1.95/2.11        | (v2_struct_0 @ sk_B))),
% 1.95/2.11      inference('demod', [status(thm)], ['58', '73', '74'])).
% 1.95/2.11  thf('76', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('77', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('78', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('79', plain,
% 1.95/2.11      (![X18 : $i]: ((m1_pre_topc @ X18 @ X18) | ~ (l1_pre_topc @ X18))),
% 1.95/2.11      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.95/2.11  thf('80', plain,
% 1.95/2.11      ((m1_subset_1 @ sk_E @ 
% 1.95/2.11        (k1_zfmisc_1 @ 
% 1.95/2.11         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf(dt_k3_tmap_1, axiom,
% 1.95/2.11    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 1.95/2.11     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.95/2.11         ( l1_pre_topc @ A ) & ( ~( v2_struct_0 @ B ) ) & 
% 1.95/2.11         ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) & ( m1_pre_topc @ C @ A ) & 
% 1.95/2.11         ( m1_pre_topc @ D @ A ) & ( v1_funct_1 @ E ) & 
% 1.95/2.11         ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 1.95/2.11         ( m1_subset_1 @
% 1.95/2.11           E @ 
% 1.95/2.11           ( k1_zfmisc_1 @
% 1.95/2.11             ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.95/2.11       ( ( v1_funct_1 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) ) & 
% 1.95/2.11         ( v1_funct_2 @
% 1.95/2.11           ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ ( u1_struct_0 @ D ) @ 
% 1.95/2.11           ( u1_struct_0 @ B ) ) & 
% 1.95/2.11         ( m1_subset_1 @
% 1.95/2.11           ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ 
% 1.95/2.11           ( k1_zfmisc_1 @
% 1.95/2.11             ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 1.95/2.11  thf('81', plain,
% 1.95/2.11      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 1.95/2.11         (~ (m1_pre_topc @ X13 @ X14)
% 1.95/2.11          | ~ (m1_pre_topc @ X15 @ X14)
% 1.95/2.11          | ~ (l1_pre_topc @ X16)
% 1.95/2.11          | ~ (v2_pre_topc @ X16)
% 1.95/2.11          | (v2_struct_0 @ X16)
% 1.95/2.11          | ~ (l1_pre_topc @ X14)
% 1.95/2.11          | ~ (v2_pre_topc @ X14)
% 1.95/2.11          | (v2_struct_0 @ X14)
% 1.95/2.11          | ~ (v1_funct_1 @ X17)
% 1.95/2.11          | ~ (v1_funct_2 @ X17 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X16))
% 1.95/2.11          | ~ (m1_subset_1 @ X17 @ 
% 1.95/2.11               (k1_zfmisc_1 @ 
% 1.95/2.11                (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X16))))
% 1.95/2.11          | (m1_subset_1 @ (k3_tmap_1 @ X14 @ X16 @ X15 @ X13 @ X17) @ 
% 1.95/2.11             (k1_zfmisc_1 @ 
% 1.95/2.11              (k2_zfmisc_1 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X16)))))),
% 1.95/2.11      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 1.95/2.11  thf('82', plain,
% 1.95/2.11      (![X0 : $i, X1 : $i]:
% 1.95/2.11         ((m1_subset_1 @ (k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 1.95/2.11           (k1_zfmisc_1 @ 
% 1.95/2.11            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 1.95/2.11          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 1.95/2.11          | ~ (v1_funct_1 @ sk_E)
% 1.95/2.11          | (v2_struct_0 @ X1)
% 1.95/2.11          | ~ (v2_pre_topc @ X1)
% 1.95/2.11          | ~ (l1_pre_topc @ X1)
% 1.95/2.11          | (v2_struct_0 @ sk_B)
% 1.95/2.11          | ~ (v2_pre_topc @ sk_B)
% 1.95/2.11          | ~ (l1_pre_topc @ sk_B)
% 1.95/2.11          | ~ (m1_pre_topc @ sk_A @ X1)
% 1.95/2.11          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.95/2.11      inference('sup-', [status(thm)], ['80', '81'])).
% 1.95/2.11  thf('83', plain,
% 1.95/2.11      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('84', plain, ((v1_funct_1 @ sk_E)),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('85', plain, ((v2_pre_topc @ sk_B)),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('86', plain, ((l1_pre_topc @ sk_B)),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('87', plain,
% 1.95/2.11      (![X0 : $i, X1 : $i]:
% 1.95/2.11         ((m1_subset_1 @ (k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 1.95/2.11           (k1_zfmisc_1 @ 
% 1.95/2.11            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 1.95/2.11          | (v2_struct_0 @ X1)
% 1.95/2.11          | ~ (v2_pre_topc @ X1)
% 1.95/2.11          | ~ (l1_pre_topc @ X1)
% 1.95/2.11          | (v2_struct_0 @ sk_B)
% 1.95/2.11          | ~ (m1_pre_topc @ sk_A @ X1)
% 1.95/2.11          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.95/2.11      inference('demod', [status(thm)], ['82', '83', '84', '85', '86'])).
% 1.95/2.11  thf('88', plain,
% 1.95/2.11      (![X0 : $i]:
% 1.95/2.11         (~ (l1_pre_topc @ sk_A)
% 1.95/2.11          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.95/2.11          | (v2_struct_0 @ sk_B)
% 1.95/2.11          | ~ (l1_pre_topc @ sk_A)
% 1.95/2.11          | ~ (v2_pre_topc @ sk_A)
% 1.95/2.11          | (v2_struct_0 @ sk_A)
% 1.95/2.11          | (m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 1.95/2.11             (k1_zfmisc_1 @ 
% 1.95/2.11              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))))),
% 1.95/2.11      inference('sup-', [status(thm)], ['79', '87'])).
% 1.95/2.11  thf('89', plain, ((l1_pre_topc @ sk_A)),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('90', plain, ((l1_pre_topc @ sk_A)),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('91', plain, ((v2_pre_topc @ sk_A)),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('92', plain,
% 1.95/2.11      (![X0 : $i]:
% 1.95/2.11         (~ (m1_pre_topc @ X0 @ sk_A)
% 1.95/2.11          | (v2_struct_0 @ sk_B)
% 1.95/2.11          | (v2_struct_0 @ sk_A)
% 1.95/2.11          | (m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 1.95/2.11             (k1_zfmisc_1 @ 
% 1.95/2.11              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))))),
% 1.95/2.11      inference('demod', [status(thm)], ['88', '89', '90', '91'])).
% 1.95/2.11  thf('93', plain,
% 1.95/2.11      (((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E) @ 
% 1.95/2.11         (k1_zfmisc_1 @ 
% 1.95/2.11          (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 1.95/2.11        | (v2_struct_0 @ sk_A)
% 1.95/2.11        | (v2_struct_0 @ sk_B))),
% 1.95/2.11      inference('sup-', [status(thm)], ['78', '92'])).
% 1.95/2.11  thf('94', plain, (~ (v2_struct_0 @ sk_A)),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('95', plain,
% 1.95/2.11      (((v2_struct_0 @ sk_B)
% 1.95/2.11        | (m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E) @ 
% 1.95/2.11           (k1_zfmisc_1 @ 
% 1.95/2.11            (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))))),
% 1.95/2.11      inference('clc', [status(thm)], ['93', '94'])).
% 1.95/2.11  thf('96', plain, (~ (v2_struct_0 @ sk_B)),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('97', plain,
% 1.95/2.11      ((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E) @ 
% 1.95/2.11        (k1_zfmisc_1 @ 
% 1.95/2.11         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.95/2.11      inference('clc', [status(thm)], ['95', '96'])).
% 1.95/2.11  thf('98', plain,
% 1.95/2.11      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 1.95/2.11         (~ (m1_pre_topc @ X13 @ X14)
% 1.95/2.11          | ~ (m1_pre_topc @ X15 @ X14)
% 1.95/2.11          | ~ (l1_pre_topc @ X16)
% 1.95/2.11          | ~ (v2_pre_topc @ X16)
% 1.95/2.11          | (v2_struct_0 @ X16)
% 1.95/2.11          | ~ (l1_pre_topc @ X14)
% 1.95/2.11          | ~ (v2_pre_topc @ X14)
% 1.95/2.11          | (v2_struct_0 @ X14)
% 1.95/2.11          | ~ (v1_funct_1 @ X17)
% 1.95/2.11          | ~ (v1_funct_2 @ X17 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X16))
% 1.95/2.11          | ~ (m1_subset_1 @ X17 @ 
% 1.95/2.11               (k1_zfmisc_1 @ 
% 1.95/2.11                (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X16))))
% 1.95/2.11          | (m1_subset_1 @ (k3_tmap_1 @ X14 @ X16 @ X15 @ X13 @ X17) @ 
% 1.95/2.11             (k1_zfmisc_1 @ 
% 1.95/2.11              (k2_zfmisc_1 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X16)))))),
% 1.95/2.11      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 1.95/2.11  thf('99', plain,
% 1.95/2.11      (![X0 : $i, X1 : $i]:
% 1.95/2.11         ((m1_subset_1 @ 
% 1.95/2.11           (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ 
% 1.95/2.11            (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E)) @ 
% 1.95/2.11           (k1_zfmisc_1 @ 
% 1.95/2.11            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 1.95/2.11          | ~ (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E) @ 
% 1.95/2.11               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 1.95/2.11          | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))
% 1.95/2.11          | (v2_struct_0 @ X1)
% 1.95/2.11          | ~ (v2_pre_topc @ X1)
% 1.95/2.11          | ~ (l1_pre_topc @ X1)
% 1.95/2.11          | (v2_struct_0 @ sk_B)
% 1.95/2.11          | ~ (v2_pre_topc @ sk_B)
% 1.95/2.11          | ~ (l1_pre_topc @ sk_B)
% 1.95/2.11          | ~ (m1_pre_topc @ sk_D @ X1)
% 1.95/2.11          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.95/2.11      inference('sup-', [status(thm)], ['97', '98'])).
% 1.95/2.11  thf('100', plain, ((v2_pre_topc @ sk_B)),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('101', plain, ((l1_pre_topc @ sk_B)),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('102', plain,
% 1.95/2.11      (![X0 : $i, X1 : $i]:
% 1.95/2.11         ((m1_subset_1 @ 
% 1.95/2.11           (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ 
% 1.95/2.11            (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E)) @ 
% 1.95/2.11           (k1_zfmisc_1 @ 
% 1.95/2.11            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 1.95/2.11          | ~ (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E) @ 
% 1.95/2.11               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 1.95/2.11          | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))
% 1.95/2.11          | (v2_struct_0 @ X1)
% 1.95/2.11          | ~ (v2_pre_topc @ X1)
% 1.95/2.11          | ~ (l1_pre_topc @ X1)
% 1.95/2.11          | (v2_struct_0 @ sk_B)
% 1.95/2.11          | ~ (m1_pre_topc @ sk_D @ X1)
% 1.95/2.11          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.95/2.11      inference('demod', [status(thm)], ['99', '100', '101'])).
% 1.95/2.11  thf('103', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('104', plain,
% 1.95/2.11      (![X18 : $i]: ((m1_pre_topc @ X18 @ X18) | ~ (l1_pre_topc @ X18))),
% 1.95/2.11      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.95/2.11  thf('105', plain,
% 1.95/2.11      ((m1_subset_1 @ sk_E @ 
% 1.95/2.11        (k1_zfmisc_1 @ 
% 1.95/2.11         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('106', plain,
% 1.95/2.11      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 1.95/2.11         (~ (m1_pre_topc @ X13 @ X14)
% 1.95/2.11          | ~ (m1_pre_topc @ X15 @ X14)
% 1.95/2.11          | ~ (l1_pre_topc @ X16)
% 1.95/2.11          | ~ (v2_pre_topc @ X16)
% 1.95/2.11          | (v2_struct_0 @ X16)
% 1.95/2.11          | ~ (l1_pre_topc @ X14)
% 1.95/2.11          | ~ (v2_pre_topc @ X14)
% 1.95/2.11          | (v2_struct_0 @ X14)
% 1.95/2.11          | ~ (v1_funct_1 @ X17)
% 1.95/2.11          | ~ (v1_funct_2 @ X17 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X16))
% 1.95/2.11          | ~ (m1_subset_1 @ X17 @ 
% 1.95/2.11               (k1_zfmisc_1 @ 
% 1.95/2.11                (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X16))))
% 1.95/2.11          | (v1_funct_1 @ (k3_tmap_1 @ X14 @ X16 @ X15 @ X13 @ X17)))),
% 1.95/2.11      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 1.95/2.11  thf('107', plain,
% 1.95/2.11      (![X0 : $i, X1 : $i]:
% 1.95/2.11         ((v1_funct_1 @ (k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E))
% 1.95/2.11          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 1.95/2.11          | ~ (v1_funct_1 @ sk_E)
% 1.95/2.11          | (v2_struct_0 @ X1)
% 1.95/2.11          | ~ (v2_pre_topc @ X1)
% 1.95/2.11          | ~ (l1_pre_topc @ X1)
% 1.95/2.11          | (v2_struct_0 @ sk_B)
% 1.95/2.11          | ~ (v2_pre_topc @ sk_B)
% 1.95/2.11          | ~ (l1_pre_topc @ sk_B)
% 1.95/2.11          | ~ (m1_pre_topc @ sk_A @ X1)
% 1.95/2.11          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.95/2.11      inference('sup-', [status(thm)], ['105', '106'])).
% 1.95/2.11  thf('108', plain,
% 1.95/2.11      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('109', plain, ((v1_funct_1 @ sk_E)),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('110', plain, ((v2_pre_topc @ sk_B)),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('111', plain, ((l1_pre_topc @ sk_B)),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('112', plain,
% 1.95/2.11      (![X0 : $i, X1 : $i]:
% 1.95/2.11         ((v1_funct_1 @ (k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E))
% 1.95/2.11          | (v2_struct_0 @ X1)
% 1.95/2.11          | ~ (v2_pre_topc @ X1)
% 1.95/2.11          | ~ (l1_pre_topc @ X1)
% 1.95/2.11          | (v2_struct_0 @ sk_B)
% 1.95/2.11          | ~ (m1_pre_topc @ sk_A @ X1)
% 1.95/2.11          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.95/2.11      inference('demod', [status(thm)], ['107', '108', '109', '110', '111'])).
% 1.95/2.11  thf('113', plain,
% 1.95/2.11      (![X0 : $i]:
% 1.95/2.11         (~ (l1_pre_topc @ sk_A)
% 1.95/2.11          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.95/2.11          | (v2_struct_0 @ sk_B)
% 1.95/2.11          | ~ (l1_pre_topc @ sk_A)
% 1.95/2.11          | ~ (v2_pre_topc @ sk_A)
% 1.95/2.11          | (v2_struct_0 @ sk_A)
% 1.95/2.11          | (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E)))),
% 1.95/2.11      inference('sup-', [status(thm)], ['104', '112'])).
% 1.95/2.11  thf('114', plain, ((l1_pre_topc @ sk_A)),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('115', plain, ((l1_pre_topc @ sk_A)),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('116', plain, ((v2_pre_topc @ sk_A)),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('117', plain,
% 1.95/2.11      (![X0 : $i]:
% 1.95/2.11         (~ (m1_pre_topc @ X0 @ sk_A)
% 1.95/2.11          | (v2_struct_0 @ sk_B)
% 1.95/2.11          | (v2_struct_0 @ sk_A)
% 1.95/2.11          | (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E)))),
% 1.95/2.11      inference('demod', [status(thm)], ['113', '114', '115', '116'])).
% 1.95/2.11  thf('118', plain,
% 1.95/2.11      (((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))
% 1.95/2.11        | (v2_struct_0 @ sk_A)
% 1.95/2.11        | (v2_struct_0 @ sk_B))),
% 1.95/2.11      inference('sup-', [status(thm)], ['103', '117'])).
% 1.95/2.11  thf('119', plain, (~ (v2_struct_0 @ sk_A)),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('120', plain,
% 1.95/2.11      (((v2_struct_0 @ sk_B)
% 1.95/2.11        | (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E)))),
% 1.95/2.11      inference('clc', [status(thm)], ['118', '119'])).
% 1.95/2.11  thf('121', plain, (~ (v2_struct_0 @ sk_B)),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('122', plain,
% 1.95/2.11      ((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))),
% 1.95/2.11      inference('clc', [status(thm)], ['120', '121'])).
% 1.95/2.11  thf('123', plain,
% 1.95/2.11      (![X0 : $i, X1 : $i]:
% 1.95/2.11         ((m1_subset_1 @ 
% 1.95/2.11           (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ 
% 1.95/2.11            (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E)) @ 
% 1.95/2.11           (k1_zfmisc_1 @ 
% 1.95/2.11            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 1.95/2.11          | ~ (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E) @ 
% 1.95/2.11               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 1.95/2.11          | (v2_struct_0 @ X1)
% 1.95/2.11          | ~ (v2_pre_topc @ X1)
% 1.95/2.11          | ~ (l1_pre_topc @ X1)
% 1.95/2.11          | (v2_struct_0 @ sk_B)
% 1.95/2.11          | ~ (m1_pre_topc @ sk_D @ X1)
% 1.95/2.11          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.95/2.11      inference('demod', [status(thm)], ['102', '122'])).
% 1.95/2.11  thf('124', plain,
% 1.95/2.11      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 1.95/2.11         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))),
% 1.95/2.11      inference('sup+', [status(thm)], ['65', '72'])).
% 1.95/2.11  thf('125', plain,
% 1.95/2.11      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 1.95/2.11         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))),
% 1.95/2.11      inference('sup+', [status(thm)], ['65', '72'])).
% 1.95/2.11  thf('126', plain,
% 1.95/2.11      (![X0 : $i, X1 : $i]:
% 1.95/2.11         ((m1_subset_1 @ 
% 1.95/2.11           (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ 
% 1.95/2.11            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 1.95/2.11           (k1_zfmisc_1 @ 
% 1.95/2.11            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 1.95/2.11          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 1.95/2.11               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 1.95/2.11          | (v2_struct_0 @ X1)
% 1.95/2.11          | ~ (v2_pre_topc @ X1)
% 1.95/2.11          | ~ (l1_pre_topc @ X1)
% 1.95/2.11          | (v2_struct_0 @ sk_B)
% 1.95/2.11          | ~ (m1_pre_topc @ sk_D @ X1)
% 1.95/2.11          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.95/2.11      inference('demod', [status(thm)], ['123', '124', '125'])).
% 1.95/2.11  thf('127', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('128', plain,
% 1.95/2.11      (![X18 : $i]: ((m1_pre_topc @ X18 @ X18) | ~ (l1_pre_topc @ X18))),
% 1.95/2.11      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.95/2.11  thf('129', plain,
% 1.95/2.11      ((m1_subset_1 @ sk_E @ 
% 1.95/2.11        (k1_zfmisc_1 @ 
% 1.95/2.11         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('130', plain,
% 1.95/2.11      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 1.95/2.12         (~ (m1_pre_topc @ X13 @ X14)
% 1.95/2.12          | ~ (m1_pre_topc @ X15 @ X14)
% 1.95/2.12          | ~ (l1_pre_topc @ X16)
% 1.95/2.12          | ~ (v2_pre_topc @ X16)
% 1.95/2.12          | (v2_struct_0 @ X16)
% 1.95/2.12          | ~ (l1_pre_topc @ X14)
% 1.95/2.12          | ~ (v2_pre_topc @ X14)
% 1.95/2.12          | (v2_struct_0 @ X14)
% 1.95/2.12          | ~ (v1_funct_1 @ X17)
% 1.95/2.12          | ~ (v1_funct_2 @ X17 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X16))
% 1.95/2.12          | ~ (m1_subset_1 @ X17 @ 
% 1.95/2.12               (k1_zfmisc_1 @ 
% 1.95/2.12                (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X16))))
% 1.95/2.12          | (v1_funct_2 @ (k3_tmap_1 @ X14 @ X16 @ X15 @ X13 @ X17) @ 
% 1.95/2.12             (u1_struct_0 @ X13) @ (u1_struct_0 @ X16)))),
% 1.95/2.12      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 1.95/2.12  thf('131', plain,
% 1.95/2.12      (![X0 : $i, X1 : $i]:
% 1.95/2.12         ((v1_funct_2 @ (k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 1.95/2.12           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 1.95/2.12          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 1.95/2.12          | ~ (v1_funct_1 @ sk_E)
% 1.95/2.12          | (v2_struct_0 @ X1)
% 1.95/2.12          | ~ (v2_pre_topc @ X1)
% 1.95/2.12          | ~ (l1_pre_topc @ X1)
% 1.95/2.12          | (v2_struct_0 @ sk_B)
% 1.95/2.12          | ~ (v2_pre_topc @ sk_B)
% 1.95/2.12          | ~ (l1_pre_topc @ sk_B)
% 1.95/2.12          | ~ (m1_pre_topc @ sk_A @ X1)
% 1.95/2.12          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.95/2.12      inference('sup-', [status(thm)], ['129', '130'])).
% 1.95/2.12  thf('132', plain,
% 1.95/2.12      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.12  thf('133', plain, ((v1_funct_1 @ sk_E)),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.12  thf('134', plain, ((v2_pre_topc @ sk_B)),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.12  thf('135', plain, ((l1_pre_topc @ sk_B)),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.12  thf('136', plain,
% 1.95/2.12      (![X0 : $i, X1 : $i]:
% 1.95/2.12         ((v1_funct_2 @ (k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 1.95/2.12           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 1.95/2.12          | (v2_struct_0 @ X1)
% 1.95/2.12          | ~ (v2_pre_topc @ X1)
% 1.95/2.12          | ~ (l1_pre_topc @ X1)
% 1.95/2.12          | (v2_struct_0 @ sk_B)
% 1.95/2.12          | ~ (m1_pre_topc @ sk_A @ X1)
% 1.95/2.12          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.95/2.12      inference('demod', [status(thm)], ['131', '132', '133', '134', '135'])).
% 1.95/2.12  thf('137', plain,
% 1.95/2.12      (![X0 : $i]:
% 1.95/2.12         (~ (l1_pre_topc @ sk_A)
% 1.95/2.12          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.95/2.12          | (v2_struct_0 @ sk_B)
% 1.95/2.12          | ~ (l1_pre_topc @ sk_A)
% 1.95/2.12          | ~ (v2_pre_topc @ sk_A)
% 1.95/2.12          | (v2_struct_0 @ sk_A)
% 1.95/2.12          | (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 1.95/2.12             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 1.95/2.12      inference('sup-', [status(thm)], ['128', '136'])).
% 1.95/2.12  thf('138', plain, ((l1_pre_topc @ sk_A)),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.12  thf('139', plain, ((l1_pre_topc @ sk_A)),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.12  thf('140', plain, ((v2_pre_topc @ sk_A)),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.12  thf('141', plain,
% 1.95/2.12      (![X0 : $i]:
% 1.95/2.12         (~ (m1_pre_topc @ X0 @ sk_A)
% 1.95/2.12          | (v2_struct_0 @ sk_B)
% 1.95/2.12          | (v2_struct_0 @ sk_A)
% 1.95/2.12          | (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 1.95/2.12             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 1.95/2.12      inference('demod', [status(thm)], ['137', '138', '139', '140'])).
% 1.95/2.12  thf('142', plain,
% 1.95/2.12      (((v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E) @ 
% 1.95/2.12         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 1.95/2.12        | (v2_struct_0 @ sk_A)
% 1.95/2.12        | (v2_struct_0 @ sk_B))),
% 1.95/2.12      inference('sup-', [status(thm)], ['127', '141'])).
% 1.95/2.12  thf('143', plain,
% 1.95/2.12      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 1.95/2.12         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))),
% 1.95/2.12      inference('sup+', [status(thm)], ['65', '72'])).
% 1.95/2.12  thf('144', plain,
% 1.95/2.12      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 1.95/2.12         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 1.95/2.12        | (v2_struct_0 @ sk_A)
% 1.95/2.12        | (v2_struct_0 @ sk_B))),
% 1.95/2.12      inference('demod', [status(thm)], ['142', '143'])).
% 1.95/2.12  thf('145', plain, (~ (v2_struct_0 @ sk_A)),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.12  thf('146', plain,
% 1.95/2.12      (((v2_struct_0 @ sk_B)
% 1.95/2.12        | (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 1.95/2.12           (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))),
% 1.95/2.12      inference('clc', [status(thm)], ['144', '145'])).
% 1.95/2.12  thf('147', plain, (~ (v2_struct_0 @ sk_B)),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.12  thf('148', plain,
% 1.95/2.12      ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 1.95/2.12        (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 1.95/2.12      inference('clc', [status(thm)], ['146', '147'])).
% 1.95/2.12  thf('149', plain,
% 1.95/2.12      (![X0 : $i, X1 : $i]:
% 1.95/2.12         ((m1_subset_1 @ 
% 1.95/2.12           (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ 
% 1.95/2.12            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 1.95/2.12           (k1_zfmisc_1 @ 
% 1.95/2.12            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 1.95/2.12          | (v2_struct_0 @ X1)
% 1.95/2.12          | ~ (v2_pre_topc @ X1)
% 1.95/2.12          | ~ (l1_pre_topc @ X1)
% 1.95/2.12          | (v2_struct_0 @ sk_B)
% 1.95/2.12          | ~ (m1_pre_topc @ sk_D @ X1)
% 1.95/2.12          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.95/2.12      inference('demod', [status(thm)], ['126', '148'])).
% 1.95/2.12  thf('150', plain,
% 1.95/2.12      (![X0 : $i]:
% 1.95/2.12         (~ (m1_pre_topc @ X0 @ sk_A)
% 1.95/2.12          | (v2_struct_0 @ sk_B)
% 1.95/2.12          | ~ (l1_pre_topc @ sk_A)
% 1.95/2.12          | ~ (v2_pre_topc @ sk_A)
% 1.95/2.12          | (v2_struct_0 @ sk_A)
% 1.95/2.12          | (m1_subset_1 @ 
% 1.95/2.12             (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ 
% 1.95/2.12              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 1.95/2.12             (k1_zfmisc_1 @ 
% 1.95/2.12              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))))),
% 1.95/2.12      inference('sup-', [status(thm)], ['77', '149'])).
% 1.95/2.12  thf('151', plain, ((l1_pre_topc @ sk_A)),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.12  thf('152', plain, ((v2_pre_topc @ sk_A)),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.12  thf('153', plain,
% 1.95/2.12      (![X0 : $i]:
% 1.95/2.12         (~ (m1_pre_topc @ X0 @ sk_A)
% 1.95/2.12          | (v2_struct_0 @ sk_B)
% 1.95/2.12          | (v2_struct_0 @ sk_A)
% 1.95/2.12          | (m1_subset_1 @ 
% 1.95/2.12             (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ 
% 1.95/2.12              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 1.95/2.12             (k1_zfmisc_1 @ 
% 1.95/2.12              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))))),
% 1.95/2.12      inference('demod', [status(thm)], ['150', '151', '152'])).
% 1.95/2.12  thf('154', plain,
% 1.95/2.12      (((m1_subset_1 @ 
% 1.95/2.12         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ 
% 1.95/2.12          (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 1.95/2.12         (k1_zfmisc_1 @ 
% 1.95/2.12          (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 1.95/2.12        | (v2_struct_0 @ sk_A)
% 1.95/2.12        | (v2_struct_0 @ sk_B))),
% 1.95/2.12      inference('sup-', [status(thm)], ['76', '153'])).
% 1.95/2.12  thf('155', plain, (~ (v2_struct_0 @ sk_A)),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.12  thf('156', plain,
% 1.95/2.12      (((v2_struct_0 @ sk_B)
% 1.95/2.12        | (m1_subset_1 @ 
% 1.95/2.12           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ 
% 1.95/2.12            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 1.95/2.12           (k1_zfmisc_1 @ 
% 1.95/2.12            (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))))),
% 1.95/2.12      inference('clc', [status(thm)], ['154', '155'])).
% 1.95/2.12  thf('157', plain, (~ (v2_struct_0 @ sk_B)),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.12  thf('158', plain,
% 1.95/2.12      ((m1_subset_1 @ 
% 1.95/2.12        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ 
% 1.95/2.12         (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 1.95/2.12        (k1_zfmisc_1 @ 
% 1.95/2.12         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 1.95/2.12      inference('clc', [status(thm)], ['156', '157'])).
% 1.95/2.12  thf(redefinition_r2_funct_2, axiom,
% 1.95/2.12    (![A:$i,B:$i,C:$i,D:$i]:
% 1.95/2.12     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.95/2.12         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.95/2.12         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.95/2.12         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.95/2.12       ( ( r2_funct_2 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.95/2.12  thf('159', plain,
% 1.95/2.12      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.95/2.12         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 1.95/2.12          | ~ (v1_funct_2 @ X0 @ X1 @ X2)
% 1.95/2.12          | ~ (v1_funct_1 @ X0)
% 1.95/2.12          | ~ (v1_funct_1 @ X3)
% 1.95/2.12          | ~ (v1_funct_2 @ X3 @ X1 @ X2)
% 1.95/2.12          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 1.95/2.12          | ((X0) = (X3))
% 1.95/2.12          | ~ (r2_funct_2 @ X1 @ X2 @ X0 @ X3))),
% 1.95/2.12      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 1.95/2.12  thf('160', plain,
% 1.95/2.12      (![X0 : $i]:
% 1.95/2.12         (~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.95/2.12             (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ 
% 1.95/2.12              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 1.95/2.12             X0)
% 1.95/2.12          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ 
% 1.95/2.12              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) = (X0))
% 1.95/2.12          | ~ (m1_subset_1 @ X0 @ 
% 1.95/2.12               (k1_zfmisc_1 @ 
% 1.95/2.12                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 1.95/2.12          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.95/2.12          | ~ (v1_funct_1 @ X0)
% 1.95/2.12          | ~ (v1_funct_1 @ 
% 1.95/2.12               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ 
% 1.95/2.12                (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)))
% 1.95/2.12          | ~ (v1_funct_2 @ 
% 1.95/2.12               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ 
% 1.95/2.12                (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 1.95/2.12               (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 1.95/2.12      inference('sup-', [status(thm)], ['158', '159'])).
% 1.95/2.12  thf('161', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.12  thf('162', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.12  thf('163', plain,
% 1.95/2.12      ((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E) @ 
% 1.95/2.12        (k1_zfmisc_1 @ 
% 1.95/2.12         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.95/2.12      inference('clc', [status(thm)], ['95', '96'])).
% 1.95/2.12  thf('164', plain,
% 1.95/2.12      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 1.95/2.12         (~ (m1_pre_topc @ X13 @ X14)
% 1.95/2.12          | ~ (m1_pre_topc @ X15 @ X14)
% 1.95/2.12          | ~ (l1_pre_topc @ X16)
% 1.95/2.12          | ~ (v2_pre_topc @ X16)
% 1.95/2.12          | (v2_struct_0 @ X16)
% 1.95/2.12          | ~ (l1_pre_topc @ X14)
% 1.95/2.12          | ~ (v2_pre_topc @ X14)
% 1.95/2.12          | (v2_struct_0 @ X14)
% 1.95/2.12          | ~ (v1_funct_1 @ X17)
% 1.95/2.12          | ~ (v1_funct_2 @ X17 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X16))
% 1.95/2.12          | ~ (m1_subset_1 @ X17 @ 
% 1.95/2.12               (k1_zfmisc_1 @ 
% 1.95/2.12                (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X16))))
% 1.95/2.12          | (v1_funct_1 @ (k3_tmap_1 @ X14 @ X16 @ X15 @ X13 @ X17)))),
% 1.95/2.12      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 1.95/2.12  thf('165', plain,
% 1.95/2.12      (![X0 : $i, X1 : $i]:
% 1.95/2.12         ((v1_funct_1 @ 
% 1.95/2.12           (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ 
% 1.95/2.12            (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E)))
% 1.95/2.12          | ~ (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E) @ 
% 1.95/2.12               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 1.95/2.12          | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))
% 1.95/2.12          | (v2_struct_0 @ X1)
% 1.95/2.12          | ~ (v2_pre_topc @ X1)
% 1.95/2.12          | ~ (l1_pre_topc @ X1)
% 1.95/2.12          | (v2_struct_0 @ sk_B)
% 1.95/2.12          | ~ (v2_pre_topc @ sk_B)
% 1.95/2.12          | ~ (l1_pre_topc @ sk_B)
% 1.95/2.12          | ~ (m1_pre_topc @ sk_D @ X1)
% 1.95/2.12          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.95/2.12      inference('sup-', [status(thm)], ['163', '164'])).
% 1.95/2.12  thf('166', plain, ((v2_pre_topc @ sk_B)),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.12  thf('167', plain, ((l1_pre_topc @ sk_B)),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.12  thf('168', plain,
% 1.95/2.12      (![X0 : $i, X1 : $i]:
% 1.95/2.12         ((v1_funct_1 @ 
% 1.95/2.12           (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ 
% 1.95/2.12            (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E)))
% 1.95/2.12          | ~ (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E) @ 
% 1.95/2.12               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 1.95/2.12          | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))
% 1.95/2.12          | (v2_struct_0 @ X1)
% 1.95/2.12          | ~ (v2_pre_topc @ X1)
% 1.95/2.12          | ~ (l1_pre_topc @ X1)
% 1.95/2.12          | (v2_struct_0 @ sk_B)
% 1.95/2.12          | ~ (m1_pre_topc @ sk_D @ X1)
% 1.95/2.12          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.95/2.12      inference('demod', [status(thm)], ['165', '166', '167'])).
% 1.95/2.12  thf('169', plain,
% 1.95/2.12      ((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))),
% 1.95/2.12      inference('clc', [status(thm)], ['120', '121'])).
% 1.95/2.12  thf('170', plain,
% 1.95/2.12      (![X0 : $i, X1 : $i]:
% 1.95/2.12         ((v1_funct_1 @ 
% 1.95/2.12           (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ 
% 1.95/2.12            (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E)))
% 1.95/2.12          | ~ (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E) @ 
% 1.95/2.12               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 1.95/2.12          | (v2_struct_0 @ X1)
% 1.95/2.12          | ~ (v2_pre_topc @ X1)
% 1.95/2.12          | ~ (l1_pre_topc @ X1)
% 1.95/2.12          | (v2_struct_0 @ sk_B)
% 1.95/2.12          | ~ (m1_pre_topc @ sk_D @ X1)
% 1.95/2.12          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.95/2.12      inference('demod', [status(thm)], ['168', '169'])).
% 1.95/2.12  thf('171', plain,
% 1.95/2.12      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 1.95/2.12         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))),
% 1.95/2.12      inference('sup+', [status(thm)], ['65', '72'])).
% 1.95/2.12  thf('172', plain,
% 1.95/2.12      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 1.95/2.12         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))),
% 1.95/2.12      inference('sup+', [status(thm)], ['65', '72'])).
% 1.95/2.12  thf('173', plain,
% 1.95/2.12      (![X0 : $i, X1 : $i]:
% 1.95/2.12         ((v1_funct_1 @ 
% 1.95/2.12           (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ 
% 1.95/2.12            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)))
% 1.95/2.12          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 1.95/2.12               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 1.95/2.12          | (v2_struct_0 @ X1)
% 1.95/2.12          | ~ (v2_pre_topc @ X1)
% 1.95/2.12          | ~ (l1_pre_topc @ X1)
% 1.95/2.12          | (v2_struct_0 @ sk_B)
% 1.95/2.12          | ~ (m1_pre_topc @ sk_D @ X1)
% 1.95/2.12          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.95/2.12      inference('demod', [status(thm)], ['170', '171', '172'])).
% 1.95/2.12  thf('174', plain,
% 1.95/2.12      ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 1.95/2.12        (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 1.95/2.12      inference('clc', [status(thm)], ['146', '147'])).
% 1.95/2.12  thf('175', plain,
% 1.95/2.12      (![X0 : $i, X1 : $i]:
% 1.95/2.12         ((v1_funct_1 @ 
% 1.95/2.12           (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ 
% 1.95/2.12            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)))
% 1.95/2.12          | (v2_struct_0 @ X1)
% 1.95/2.12          | ~ (v2_pre_topc @ X1)
% 1.95/2.12          | ~ (l1_pre_topc @ X1)
% 1.95/2.12          | (v2_struct_0 @ sk_B)
% 1.95/2.12          | ~ (m1_pre_topc @ sk_D @ X1)
% 1.95/2.12          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.95/2.12      inference('demod', [status(thm)], ['173', '174'])).
% 1.95/2.12  thf('176', plain,
% 1.95/2.12      (![X0 : $i]:
% 1.95/2.12         (~ (m1_pre_topc @ X0 @ sk_A)
% 1.95/2.12          | (v2_struct_0 @ sk_B)
% 1.95/2.12          | ~ (l1_pre_topc @ sk_A)
% 1.95/2.12          | ~ (v2_pre_topc @ sk_A)
% 1.95/2.12          | (v2_struct_0 @ sk_A)
% 1.95/2.12          | (v1_funct_1 @ 
% 1.95/2.12             (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ 
% 1.95/2.12              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))))),
% 1.95/2.12      inference('sup-', [status(thm)], ['162', '175'])).
% 1.95/2.12  thf('177', plain, ((l1_pre_topc @ sk_A)),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.12  thf('178', plain, ((v2_pre_topc @ sk_A)),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.12  thf('179', plain,
% 1.95/2.12      (![X0 : $i]:
% 1.95/2.12         (~ (m1_pre_topc @ X0 @ sk_A)
% 1.95/2.12          | (v2_struct_0 @ sk_B)
% 1.95/2.12          | (v2_struct_0 @ sk_A)
% 1.95/2.12          | (v1_funct_1 @ 
% 1.95/2.12             (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ 
% 1.95/2.12              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))))),
% 1.95/2.12      inference('demod', [status(thm)], ['176', '177', '178'])).
% 1.95/2.12  thf('180', plain,
% 1.95/2.12      (((v1_funct_1 @ 
% 1.95/2.12         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ 
% 1.95/2.12          (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)))
% 1.95/2.12        | (v2_struct_0 @ sk_A)
% 1.95/2.12        | (v2_struct_0 @ sk_B))),
% 1.95/2.12      inference('sup-', [status(thm)], ['161', '179'])).
% 1.95/2.12  thf('181', plain, (~ (v2_struct_0 @ sk_A)),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.12  thf('182', plain,
% 1.95/2.12      (((v2_struct_0 @ sk_B)
% 1.95/2.12        | (v1_funct_1 @ 
% 1.95/2.12           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ 
% 1.95/2.12            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))))),
% 1.95/2.12      inference('clc', [status(thm)], ['180', '181'])).
% 1.95/2.12  thf('183', plain, (~ (v2_struct_0 @ sk_B)),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.12  thf('184', plain,
% 1.95/2.12      ((v1_funct_1 @ 
% 1.95/2.12        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ 
% 1.95/2.12         (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)))),
% 1.95/2.12      inference('clc', [status(thm)], ['182', '183'])).
% 1.95/2.12  thf('185', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.12  thf('186', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.12  thf('187', plain,
% 1.95/2.12      ((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E) @ 
% 1.95/2.12        (k1_zfmisc_1 @ 
% 1.95/2.12         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.95/2.12      inference('clc', [status(thm)], ['95', '96'])).
% 1.95/2.12  thf('188', plain,
% 1.95/2.12      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 1.95/2.12         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))),
% 1.95/2.12      inference('sup+', [status(thm)], ['65', '72'])).
% 1.95/2.12  thf('189', plain,
% 1.95/2.12      ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 1.95/2.12        (k1_zfmisc_1 @ 
% 1.95/2.12         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.95/2.12      inference('demod', [status(thm)], ['187', '188'])).
% 1.95/2.12  thf('190', plain,
% 1.95/2.12      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 1.95/2.12         (~ (m1_pre_topc @ X13 @ X14)
% 1.95/2.12          | ~ (m1_pre_topc @ X15 @ X14)
% 1.95/2.12          | ~ (l1_pre_topc @ X16)
% 1.95/2.12          | ~ (v2_pre_topc @ X16)
% 1.95/2.12          | (v2_struct_0 @ X16)
% 1.95/2.12          | ~ (l1_pre_topc @ X14)
% 1.95/2.12          | ~ (v2_pre_topc @ X14)
% 1.95/2.12          | (v2_struct_0 @ X14)
% 1.95/2.12          | ~ (v1_funct_1 @ X17)
% 1.95/2.12          | ~ (v1_funct_2 @ X17 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X16))
% 1.95/2.12          | ~ (m1_subset_1 @ X17 @ 
% 1.95/2.12               (k1_zfmisc_1 @ 
% 1.95/2.12                (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X16))))
% 1.95/2.12          | (v1_funct_2 @ (k3_tmap_1 @ X14 @ X16 @ X15 @ X13 @ X17) @ 
% 1.95/2.12             (u1_struct_0 @ X13) @ (u1_struct_0 @ X16)))),
% 1.95/2.12      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 1.95/2.12  thf('191', plain,
% 1.95/2.12      (![X0 : $i, X1 : $i]:
% 1.95/2.12         ((v1_funct_2 @ 
% 1.95/2.12           (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ 
% 1.95/2.12            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 1.95/2.12           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 1.95/2.12          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 1.95/2.12               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 1.95/2.12          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))
% 1.95/2.12          | (v2_struct_0 @ X1)
% 1.95/2.12          | ~ (v2_pre_topc @ X1)
% 1.95/2.12          | ~ (l1_pre_topc @ X1)
% 1.95/2.12          | (v2_struct_0 @ sk_B)
% 1.95/2.12          | ~ (v2_pre_topc @ sk_B)
% 1.95/2.12          | ~ (l1_pre_topc @ sk_B)
% 1.95/2.12          | ~ (m1_pre_topc @ sk_D @ X1)
% 1.95/2.12          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.95/2.12      inference('sup-', [status(thm)], ['189', '190'])).
% 1.95/2.12  thf('192', plain,
% 1.95/2.12      ((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))),
% 1.95/2.12      inference('clc', [status(thm)], ['120', '121'])).
% 1.95/2.12  thf('193', plain,
% 1.95/2.12      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 1.95/2.12         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))),
% 1.95/2.12      inference('sup+', [status(thm)], ['65', '72'])).
% 1.95/2.12  thf('194', plain, ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))),
% 1.95/2.12      inference('demod', [status(thm)], ['192', '193'])).
% 1.95/2.12  thf('195', plain, ((v2_pre_topc @ sk_B)),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.12  thf('196', plain, ((l1_pre_topc @ sk_B)),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.12  thf('197', plain,
% 1.95/2.12      (![X0 : $i, X1 : $i]:
% 1.95/2.12         ((v1_funct_2 @ 
% 1.95/2.12           (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ 
% 1.95/2.12            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 1.95/2.12           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 1.95/2.12          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 1.95/2.12               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 1.95/2.12          | (v2_struct_0 @ X1)
% 1.95/2.12          | ~ (v2_pre_topc @ X1)
% 1.95/2.12          | ~ (l1_pre_topc @ X1)
% 1.95/2.12          | (v2_struct_0 @ sk_B)
% 1.95/2.12          | ~ (m1_pre_topc @ sk_D @ X1)
% 1.95/2.12          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.95/2.12      inference('demod', [status(thm)], ['191', '194', '195', '196'])).
% 1.95/2.12  thf('198', plain,
% 1.95/2.12      ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 1.95/2.12        (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 1.95/2.12      inference('clc', [status(thm)], ['146', '147'])).
% 1.95/2.12  thf('199', plain,
% 1.95/2.12      (![X0 : $i, X1 : $i]:
% 1.95/2.12         ((v1_funct_2 @ 
% 1.95/2.12           (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ 
% 1.95/2.12            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 1.95/2.12           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 1.95/2.12          | (v2_struct_0 @ X1)
% 1.95/2.12          | ~ (v2_pre_topc @ X1)
% 1.95/2.12          | ~ (l1_pre_topc @ X1)
% 1.95/2.12          | (v2_struct_0 @ sk_B)
% 1.95/2.12          | ~ (m1_pre_topc @ sk_D @ X1)
% 1.95/2.12          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.95/2.12      inference('demod', [status(thm)], ['197', '198'])).
% 1.95/2.12  thf('200', plain,
% 1.95/2.12      (![X0 : $i]:
% 1.95/2.12         (~ (m1_pre_topc @ X0 @ sk_A)
% 1.95/2.12          | (v2_struct_0 @ sk_B)
% 1.95/2.12          | ~ (l1_pre_topc @ sk_A)
% 1.95/2.12          | ~ (v2_pre_topc @ sk_A)
% 1.95/2.12          | (v2_struct_0 @ sk_A)
% 1.95/2.12          | (v1_funct_2 @ 
% 1.95/2.12             (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ 
% 1.95/2.12              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 1.95/2.12             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 1.95/2.12      inference('sup-', [status(thm)], ['186', '199'])).
% 1.95/2.12  thf('201', plain, ((l1_pre_topc @ sk_A)),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.12  thf('202', plain, ((v2_pre_topc @ sk_A)),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.12  thf('203', plain,
% 1.95/2.12      (![X0 : $i]:
% 1.95/2.12         (~ (m1_pre_topc @ X0 @ sk_A)
% 1.95/2.12          | (v2_struct_0 @ sk_B)
% 1.95/2.12          | (v2_struct_0 @ sk_A)
% 1.95/2.12          | (v1_funct_2 @ 
% 1.95/2.12             (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ 
% 1.95/2.12              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 1.95/2.12             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 1.95/2.12      inference('demod', [status(thm)], ['200', '201', '202'])).
% 1.95/2.12  thf('204', plain,
% 1.95/2.12      (((v1_funct_2 @ 
% 1.95/2.12         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ 
% 1.95/2.12          (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 1.95/2.12         (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.95/2.12        | (v2_struct_0 @ sk_A)
% 1.95/2.12        | (v2_struct_0 @ sk_B))),
% 1.95/2.12      inference('sup-', [status(thm)], ['185', '203'])).
% 1.95/2.12  thf('205', plain, (~ (v2_struct_0 @ sk_A)),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.12  thf('206', plain,
% 1.95/2.12      (((v2_struct_0 @ sk_B)
% 1.95/2.12        | (v1_funct_2 @ 
% 1.95/2.12           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ 
% 1.95/2.12            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 1.95/2.12           (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 1.95/2.12      inference('clc', [status(thm)], ['204', '205'])).
% 1.95/2.12  thf('207', plain, (~ (v2_struct_0 @ sk_B)),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.12  thf('208', plain,
% 1.95/2.12      ((v1_funct_2 @ 
% 1.95/2.12        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ 
% 1.95/2.12         (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 1.95/2.12        (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 1.95/2.12      inference('clc', [status(thm)], ['206', '207'])).
% 1.95/2.12  thf('209', plain,
% 1.95/2.12      (![X0 : $i]:
% 1.95/2.12         (~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.95/2.12             (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ 
% 1.95/2.12              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 1.95/2.12             X0)
% 1.95/2.12          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ 
% 1.95/2.12              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) = (X0))
% 1.95/2.12          | ~ (m1_subset_1 @ X0 @ 
% 1.95/2.12               (k1_zfmisc_1 @ 
% 1.95/2.12                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 1.95/2.12          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.95/2.12          | ~ (v1_funct_1 @ X0))),
% 1.95/2.12      inference('demod', [status(thm)], ['160', '184', '208'])).
% 1.95/2.12  thf('210', plain,
% 1.95/2.12      (((v2_struct_0 @ sk_B)
% 1.95/2.12        | (v2_struct_0 @ sk_D)
% 1.95/2.12        | (v2_struct_0 @ sk_C)
% 1.95/2.12        | (v2_struct_0 @ sk_A)
% 1.95/2.12        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C))
% 1.95/2.12        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 1.95/2.12             (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.95/2.12        | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 1.95/2.12             (k1_zfmisc_1 @ 
% 1.95/2.12              (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 1.95/2.12        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ 
% 1.95/2.12            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))
% 1.95/2.12            = (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C)))),
% 1.95/2.12      inference('sup-', [status(thm)], ['75', '209'])).
% 1.95/2.12  thf('211', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.12  thf('212', plain,
% 1.95/2.12      (![X0 : $i]:
% 1.95/2.12         (~ (m1_pre_topc @ X0 @ sk_A)
% 1.95/2.12          | (v2_struct_0 @ sk_B)
% 1.95/2.12          | (v2_struct_0 @ sk_A)
% 1.95/2.12          | (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E)))),
% 1.95/2.12      inference('demod', [status(thm)], ['113', '114', '115', '116'])).
% 1.95/2.12  thf('213', plain,
% 1.95/2.12      (((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E))
% 1.95/2.12        | (v2_struct_0 @ sk_A)
% 1.95/2.12        | (v2_struct_0 @ sk_B))),
% 1.95/2.12      inference('sup-', [status(thm)], ['211', '212'])).
% 1.95/2.12  thf('214', plain, (~ (v2_struct_0 @ sk_A)),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.12  thf('215', plain,
% 1.95/2.12      (((v2_struct_0 @ sk_B)
% 1.95/2.12        | (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E)))),
% 1.95/2.12      inference('clc', [status(thm)], ['213', '214'])).
% 1.95/2.12  thf('216', plain, (~ (v2_struct_0 @ sk_B)),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.12  thf('217', plain,
% 1.95/2.12      ((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E))),
% 1.95/2.12      inference('clc', [status(thm)], ['215', '216'])).
% 1.95/2.12  thf('218', plain,
% 1.95/2.12      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C)
% 1.95/2.12         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E))),
% 1.95/2.12      inference('sup+', [status(thm)], ['39', '55'])).
% 1.95/2.12  thf('219', plain, ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C))),
% 1.95/2.12      inference('demod', [status(thm)], ['217', '218'])).
% 1.95/2.12  thf('220', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.12  thf('221', plain,
% 1.95/2.12      (![X0 : $i]:
% 1.95/2.12         (~ (m1_pre_topc @ X0 @ sk_A)
% 1.95/2.12          | (v2_struct_0 @ sk_B)
% 1.95/2.12          | (v2_struct_0 @ sk_A)
% 1.95/2.12          | (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 1.95/2.12             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 1.95/2.12      inference('demod', [status(thm)], ['137', '138', '139', '140'])).
% 1.95/2.12  thf('222', plain,
% 1.95/2.12      (((v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E) @ 
% 1.95/2.12         (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.95/2.12        | (v2_struct_0 @ sk_A)
% 1.95/2.12        | (v2_struct_0 @ sk_B))),
% 1.95/2.12      inference('sup-', [status(thm)], ['220', '221'])).
% 1.95/2.12  thf('223', plain,
% 1.95/2.12      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C)
% 1.95/2.12         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E))),
% 1.95/2.12      inference('sup+', [status(thm)], ['39', '55'])).
% 1.95/2.12  thf('224', plain,
% 1.95/2.12      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 1.95/2.12         (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.95/2.12        | (v2_struct_0 @ sk_A)
% 1.95/2.12        | (v2_struct_0 @ sk_B))),
% 1.95/2.12      inference('demod', [status(thm)], ['222', '223'])).
% 1.95/2.12  thf('225', plain, (~ (v2_struct_0 @ sk_A)),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.12  thf('226', plain,
% 1.95/2.12      (((v2_struct_0 @ sk_B)
% 1.95/2.12        | (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 1.95/2.12           (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 1.95/2.12      inference('clc', [status(thm)], ['224', '225'])).
% 1.95/2.12  thf('227', plain, (~ (v2_struct_0 @ sk_B)),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.12  thf('228', plain,
% 1.95/2.12      ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 1.95/2.12        (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 1.95/2.12      inference('clc', [status(thm)], ['226', '227'])).
% 1.95/2.12  thf('229', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.12  thf('230', plain,
% 1.95/2.12      (![X0 : $i]:
% 1.95/2.12         (~ (m1_pre_topc @ X0 @ sk_A)
% 1.95/2.12          | (v2_struct_0 @ sk_B)
% 1.95/2.12          | (v2_struct_0 @ sk_A)
% 1.95/2.12          | (m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 1.95/2.12             (k1_zfmisc_1 @ 
% 1.95/2.12              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))))),
% 1.95/2.12      inference('demod', [status(thm)], ['88', '89', '90', '91'])).
% 1.95/2.12  thf('231', plain,
% 1.95/2.12      (((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E) @ 
% 1.95/2.12         (k1_zfmisc_1 @ 
% 1.95/2.12          (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 1.95/2.12        | (v2_struct_0 @ sk_A)
% 1.95/2.12        | (v2_struct_0 @ sk_B))),
% 1.95/2.12      inference('sup-', [status(thm)], ['229', '230'])).
% 1.95/2.12  thf('232', plain, (~ (v2_struct_0 @ sk_A)),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.12  thf('233', plain,
% 1.95/2.12      (((v2_struct_0 @ sk_B)
% 1.95/2.12        | (m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E) @ 
% 1.95/2.12           (k1_zfmisc_1 @ 
% 1.95/2.12            (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))))),
% 1.95/2.12      inference('clc', [status(thm)], ['231', '232'])).
% 1.95/2.12  thf('234', plain, (~ (v2_struct_0 @ sk_B)),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.12  thf('235', plain,
% 1.95/2.12      ((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E) @ 
% 1.95/2.12        (k1_zfmisc_1 @ 
% 1.95/2.12         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 1.95/2.12      inference('clc', [status(thm)], ['233', '234'])).
% 1.95/2.12  thf('236', plain,
% 1.95/2.12      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C)
% 1.95/2.12         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E))),
% 1.95/2.12      inference('sup+', [status(thm)], ['39', '55'])).
% 1.95/2.12  thf('237', plain,
% 1.95/2.12      ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 1.95/2.12        (k1_zfmisc_1 @ 
% 1.95/2.12         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 1.95/2.12      inference('demod', [status(thm)], ['235', '236'])).
% 1.95/2.12  thf('238', plain,
% 1.95/2.12      (((v2_struct_0 @ sk_B)
% 1.95/2.12        | (v2_struct_0 @ sk_D)
% 1.95/2.12        | (v2_struct_0 @ sk_C)
% 1.95/2.12        | (v2_struct_0 @ sk_A)
% 1.95/2.12        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ 
% 1.95/2.12            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))
% 1.95/2.12            = (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C)))),
% 1.95/2.12      inference('demod', [status(thm)], ['210', '219', '228', '237'])).
% 1.95/2.12  thf('239', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.12  thf('240', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C))),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.12  thf('241', plain, (((sk_F) = (sk_G))),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.12  thf('242', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 1.95/2.12      inference('demod', [status(thm)], ['240', '241'])).
% 1.95/2.12  thf('243', plain,
% 1.95/2.12      ((r1_tmap_1 @ sk_D @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 1.95/2.12        sk_F)),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.12  thf('244', plain,
% 1.95/2.12      ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 1.95/2.12        (k1_zfmisc_1 @ 
% 1.95/2.12         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.95/2.12      inference('demod', [status(thm)], ['187', '188'])).
% 1.95/2.12  thf(t81_tmap_1, axiom,
% 1.95/2.12    (![A:$i]:
% 1.95/2.12     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.95/2.12       ( ![B:$i]:
% 1.95/2.12         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.95/2.12             ( l1_pre_topc @ B ) ) =>
% 1.95/2.12           ( ![C:$i]:
% 1.95/2.12             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.95/2.12               ( ![D:$i]:
% 1.95/2.12                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 1.95/2.12                   ( ![E:$i]:
% 1.95/2.12                     ( ( ( v1_funct_1 @ E ) & 
% 1.95/2.12                         ( v1_funct_2 @
% 1.95/2.12                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 1.95/2.12                         ( m1_subset_1 @
% 1.95/2.12                           E @ 
% 1.95/2.12                           ( k1_zfmisc_1 @
% 1.95/2.12                             ( k2_zfmisc_1 @
% 1.95/2.12                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.95/2.12                       ( ![F:$i]:
% 1.95/2.12                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ C ) ) =>
% 1.95/2.12                           ( ![G:$i]:
% 1.95/2.12                             ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 1.95/2.12                               ( ( ( ( F ) = ( G ) ) & 
% 1.95/2.12                                   ( m1_pre_topc @ D @ C ) & 
% 1.95/2.12                                   ( r1_tmap_1 @ C @ B @ E @ F ) ) =>
% 1.95/2.12                                 ( r1_tmap_1 @
% 1.95/2.12                                   D @ B @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ 
% 1.95/2.12                                   G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.95/2.12  thf('245', plain,
% 1.95/2.12      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 1.95/2.12         ((v2_struct_0 @ X28)
% 1.95/2.12          | ~ (v2_pre_topc @ X28)
% 1.95/2.12          | ~ (l1_pre_topc @ X28)
% 1.95/2.12          | (v2_struct_0 @ X29)
% 1.95/2.12          | ~ (m1_pre_topc @ X29 @ X30)
% 1.95/2.12          | ~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X32))
% 1.95/2.12          | ~ (m1_pre_topc @ X29 @ X32)
% 1.95/2.12          | ~ (r1_tmap_1 @ X32 @ X28 @ X33 @ X31)
% 1.95/2.12          | ((X31) != (X34))
% 1.95/2.12          | (r1_tmap_1 @ X29 @ X28 @ 
% 1.95/2.12             (k3_tmap_1 @ X30 @ X28 @ X32 @ X29 @ X33) @ X34)
% 1.95/2.12          | ~ (m1_subset_1 @ X34 @ (u1_struct_0 @ X29))
% 1.95/2.12          | ~ (m1_subset_1 @ X33 @ 
% 1.95/2.12               (k1_zfmisc_1 @ 
% 1.95/2.12                (k2_zfmisc_1 @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X28))))
% 1.95/2.12          | ~ (v1_funct_2 @ X33 @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X28))
% 1.95/2.12          | ~ (v1_funct_1 @ X33)
% 1.95/2.12          | ~ (m1_pre_topc @ X32 @ X30)
% 1.95/2.12          | (v2_struct_0 @ X32)
% 1.95/2.12          | ~ (l1_pre_topc @ X30)
% 1.95/2.12          | ~ (v2_pre_topc @ X30)
% 1.95/2.12          | (v2_struct_0 @ X30))),
% 1.95/2.12      inference('cnf', [status(esa)], [t81_tmap_1])).
% 1.95/2.12  thf('246', plain,
% 1.95/2.12      (![X28 : $i, X29 : $i, X30 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 1.95/2.12         ((v2_struct_0 @ X30)
% 1.95/2.12          | ~ (v2_pre_topc @ X30)
% 1.95/2.12          | ~ (l1_pre_topc @ X30)
% 1.95/2.12          | (v2_struct_0 @ X32)
% 1.95/2.12          | ~ (m1_pre_topc @ X32 @ X30)
% 1.95/2.12          | ~ (v1_funct_1 @ X33)
% 1.95/2.12          | ~ (v1_funct_2 @ X33 @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X28))
% 1.95/2.12          | ~ (m1_subset_1 @ X33 @ 
% 1.95/2.12               (k1_zfmisc_1 @ 
% 1.95/2.12                (k2_zfmisc_1 @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X28))))
% 1.95/2.12          | ~ (m1_subset_1 @ X34 @ (u1_struct_0 @ X29))
% 1.95/2.12          | (r1_tmap_1 @ X29 @ X28 @ 
% 1.95/2.12             (k3_tmap_1 @ X30 @ X28 @ X32 @ X29 @ X33) @ X34)
% 1.95/2.12          | ~ (r1_tmap_1 @ X32 @ X28 @ X33 @ X34)
% 1.95/2.12          | ~ (m1_pre_topc @ X29 @ X32)
% 1.95/2.12          | ~ (m1_subset_1 @ X34 @ (u1_struct_0 @ X32))
% 1.95/2.12          | ~ (m1_pre_topc @ X29 @ X30)
% 1.95/2.12          | (v2_struct_0 @ X29)
% 1.95/2.12          | ~ (l1_pre_topc @ X28)
% 1.95/2.12          | ~ (v2_pre_topc @ X28)
% 1.95/2.12          | (v2_struct_0 @ X28))),
% 1.95/2.12      inference('simplify', [status(thm)], ['245'])).
% 1.95/2.12  thf('247', plain,
% 1.95/2.12      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.95/2.12         ((v2_struct_0 @ sk_B)
% 1.95/2.12          | ~ (v2_pre_topc @ sk_B)
% 1.95/2.12          | ~ (l1_pre_topc @ sk_B)
% 1.95/2.12          | (v2_struct_0 @ X0)
% 1.95/2.12          | ~ (m1_pre_topc @ X0 @ X1)
% 1.95/2.12          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 1.95/2.12          | ~ (m1_pre_topc @ X0 @ sk_D)
% 1.95/2.12          | ~ (r1_tmap_1 @ sk_D @ sk_B @ 
% 1.95/2.12               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ X2)
% 1.95/2.12          | (r1_tmap_1 @ X0 @ sk_B @ 
% 1.95/2.12             (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ 
% 1.95/2.12              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 1.95/2.12             X2)
% 1.95/2.12          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 1.95/2.12          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 1.95/2.12               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 1.95/2.12          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))
% 1.95/2.12          | ~ (m1_pre_topc @ sk_D @ X1)
% 1.95/2.12          | (v2_struct_0 @ sk_D)
% 1.95/2.12          | ~ (l1_pre_topc @ X1)
% 1.95/2.12          | ~ (v2_pre_topc @ X1)
% 1.95/2.12          | (v2_struct_0 @ X1))),
% 1.95/2.12      inference('sup-', [status(thm)], ['244', '246'])).
% 1.95/2.12  thf('248', plain, ((v2_pre_topc @ sk_B)),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.12  thf('249', plain, ((l1_pre_topc @ sk_B)),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.12  thf('250', plain,
% 1.95/2.12      ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 1.95/2.12        (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 1.95/2.12      inference('clc', [status(thm)], ['146', '147'])).
% 1.95/2.12  thf('251', plain, ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))),
% 1.95/2.12      inference('demod', [status(thm)], ['192', '193'])).
% 1.95/2.12  thf('252', plain,
% 1.95/2.12      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.95/2.12         ((v2_struct_0 @ sk_B)
% 1.95/2.12          | (v2_struct_0 @ X0)
% 1.95/2.12          | ~ (m1_pre_topc @ X0 @ X1)
% 1.95/2.12          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 1.95/2.12          | ~ (m1_pre_topc @ X0 @ sk_D)
% 1.95/2.12          | ~ (r1_tmap_1 @ sk_D @ sk_B @ 
% 1.95/2.12               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ X2)
% 1.95/2.12          | (r1_tmap_1 @ X0 @ sk_B @ 
% 1.95/2.12             (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ 
% 1.95/2.12              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 1.95/2.12             X2)
% 1.95/2.12          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 1.95/2.12          | ~ (m1_pre_topc @ sk_D @ X1)
% 1.95/2.12          | (v2_struct_0 @ sk_D)
% 1.95/2.12          | ~ (l1_pre_topc @ X1)
% 1.95/2.12          | ~ (v2_pre_topc @ X1)
% 1.95/2.12          | (v2_struct_0 @ X1))),
% 1.95/2.12      inference('demod', [status(thm)], ['247', '248', '249', '250', '251'])).
% 1.95/2.12  thf('253', plain,
% 1.95/2.12      (![X0 : $i, X1 : $i]:
% 1.95/2.12         ((v2_struct_0 @ X0)
% 1.95/2.12          | ~ (v2_pre_topc @ X0)
% 1.95/2.12          | ~ (l1_pre_topc @ X0)
% 1.95/2.12          | (v2_struct_0 @ sk_D)
% 1.95/2.12          | ~ (m1_pre_topc @ sk_D @ X0)
% 1.95/2.12          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ X1))
% 1.95/2.12          | (r1_tmap_1 @ X1 @ sk_B @ 
% 1.95/2.12             (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ 
% 1.95/2.12              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 1.95/2.12             sk_F)
% 1.95/2.12          | ~ (m1_pre_topc @ X1 @ sk_D)
% 1.95/2.12          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))
% 1.95/2.12          | ~ (m1_pre_topc @ X1 @ X0)
% 1.95/2.12          | (v2_struct_0 @ X1)
% 1.95/2.12          | (v2_struct_0 @ sk_B))),
% 1.95/2.12      inference('sup-', [status(thm)], ['243', '252'])).
% 1.95/2.12  thf('254', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.12  thf('255', plain,
% 1.95/2.12      (![X0 : $i, X1 : $i]:
% 1.95/2.12         ((v2_struct_0 @ X0)
% 1.95/2.12          | ~ (v2_pre_topc @ X0)
% 1.95/2.12          | ~ (l1_pre_topc @ X0)
% 1.95/2.12          | (v2_struct_0 @ sk_D)
% 1.95/2.12          | ~ (m1_pre_topc @ sk_D @ X0)
% 1.95/2.12          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ X1))
% 1.95/2.12          | (r1_tmap_1 @ X1 @ sk_B @ 
% 1.95/2.12             (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ 
% 1.95/2.12              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 1.95/2.12             sk_F)
% 1.95/2.12          | ~ (m1_pre_topc @ X1 @ sk_D)
% 1.95/2.12          | ~ (m1_pre_topc @ X1 @ X0)
% 1.95/2.12          | (v2_struct_0 @ X1)
% 1.95/2.12          | (v2_struct_0 @ sk_B))),
% 1.95/2.12      inference('demod', [status(thm)], ['253', '254'])).
% 1.95/2.12  thf('256', plain,
% 1.95/2.12      (![X0 : $i]:
% 1.95/2.12         ((v2_struct_0 @ sk_B)
% 1.95/2.12          | (v2_struct_0 @ sk_C)
% 1.95/2.12          | ~ (m1_pre_topc @ sk_C @ X0)
% 1.95/2.12          | ~ (m1_pre_topc @ sk_C @ sk_D)
% 1.95/2.12          | (r1_tmap_1 @ sk_C @ sk_B @ 
% 1.95/2.12             (k3_tmap_1 @ X0 @ sk_B @ sk_D @ sk_C @ 
% 1.95/2.12              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 1.95/2.12             sk_F)
% 1.95/2.12          | ~ (m1_pre_topc @ sk_D @ X0)
% 1.95/2.12          | (v2_struct_0 @ sk_D)
% 1.95/2.12          | ~ (l1_pre_topc @ X0)
% 1.95/2.12          | ~ (v2_pre_topc @ X0)
% 1.95/2.12          | (v2_struct_0 @ X0))),
% 1.95/2.12      inference('sup-', [status(thm)], ['242', '255'])).
% 1.95/2.12  thf('257', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.12  thf('258', plain,
% 1.95/2.12      (![X0 : $i]:
% 1.95/2.12         ((v2_struct_0 @ sk_B)
% 1.95/2.12          | (v2_struct_0 @ sk_C)
% 1.95/2.12          | ~ (m1_pre_topc @ sk_C @ X0)
% 1.95/2.12          | (r1_tmap_1 @ sk_C @ sk_B @ 
% 1.95/2.12             (k3_tmap_1 @ X0 @ sk_B @ sk_D @ sk_C @ 
% 1.95/2.12              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 1.95/2.12             sk_F)
% 1.95/2.12          | ~ (m1_pre_topc @ sk_D @ X0)
% 1.95/2.12          | (v2_struct_0 @ sk_D)
% 1.95/2.12          | ~ (l1_pre_topc @ X0)
% 1.95/2.12          | ~ (v2_pre_topc @ X0)
% 1.95/2.12          | (v2_struct_0 @ X0))),
% 1.95/2.12      inference('demod', [status(thm)], ['256', '257'])).
% 1.95/2.12  thf('259', plain,
% 1.95/2.12      (((v2_struct_0 @ sk_A)
% 1.95/2.12        | ~ (v2_pre_topc @ sk_A)
% 1.95/2.12        | ~ (l1_pre_topc @ sk_A)
% 1.95/2.12        | (v2_struct_0 @ sk_D)
% 1.95/2.12        | ~ (m1_pre_topc @ sk_D @ sk_A)
% 1.95/2.12        | (r1_tmap_1 @ sk_C @ sk_B @ 
% 1.95/2.12           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ 
% 1.95/2.12            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 1.95/2.12           sk_F)
% 1.95/2.12        | (v2_struct_0 @ sk_C)
% 1.95/2.12        | (v2_struct_0 @ sk_B))),
% 1.95/2.12      inference('sup-', [status(thm)], ['239', '258'])).
% 1.95/2.12  thf('260', plain, ((v2_pre_topc @ sk_A)),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.12  thf('261', plain, ((l1_pre_topc @ sk_A)),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.12  thf('262', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.12  thf('263', plain,
% 1.95/2.12      (((v2_struct_0 @ sk_A)
% 1.95/2.12        | (v2_struct_0 @ sk_D)
% 1.95/2.12        | (r1_tmap_1 @ sk_C @ sk_B @ 
% 1.95/2.12           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ 
% 1.95/2.12            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 1.95/2.12           sk_F)
% 1.95/2.12        | (v2_struct_0 @ sk_C)
% 1.95/2.12        | (v2_struct_0 @ sk_B))),
% 1.95/2.12      inference('demod', [status(thm)], ['259', '260', '261', '262'])).
% 1.95/2.12  thf('264', plain,
% 1.95/2.12      (((r1_tmap_1 @ sk_C @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 1.95/2.12         sk_F)
% 1.95/2.12        | (v2_struct_0 @ sk_A)
% 1.95/2.12        | (v2_struct_0 @ sk_C)
% 1.95/2.12        | (v2_struct_0 @ sk_D)
% 1.95/2.12        | (v2_struct_0 @ sk_B)
% 1.95/2.12        | (v2_struct_0 @ sk_B)
% 1.95/2.12        | (v2_struct_0 @ sk_C)
% 1.95/2.12        | (v2_struct_0 @ sk_D)
% 1.95/2.12        | (v2_struct_0 @ sk_A))),
% 1.95/2.12      inference('sup+', [status(thm)], ['238', '263'])).
% 1.95/2.12  thf('265', plain,
% 1.95/2.12      (((v2_struct_0 @ sk_B)
% 1.95/2.12        | (v2_struct_0 @ sk_D)
% 1.95/2.12        | (v2_struct_0 @ sk_C)
% 1.95/2.12        | (v2_struct_0 @ sk_A)
% 1.95/2.12        | (r1_tmap_1 @ sk_C @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 1.95/2.12           sk_F))),
% 1.95/2.12      inference('simplify', [status(thm)], ['264'])).
% 1.95/2.12  thf('266', plain,
% 1.95/2.12      (~ (r1_tmap_1 @ sk_C @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 1.95/2.12          sk_G)),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.12  thf('267', plain, (((sk_F) = (sk_G))),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.12  thf('268', plain,
% 1.95/2.12      (~ (r1_tmap_1 @ sk_C @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 1.95/2.12          sk_F)),
% 1.95/2.12      inference('demod', [status(thm)], ['266', '267'])).
% 1.95/2.12  thf('269', plain,
% 1.95/2.12      (((v2_struct_0 @ sk_A)
% 1.95/2.12        | (v2_struct_0 @ sk_C)
% 1.95/2.12        | (v2_struct_0 @ sk_D)
% 1.95/2.12        | (v2_struct_0 @ sk_B))),
% 1.95/2.12      inference('sup-', [status(thm)], ['265', '268'])).
% 1.95/2.12  thf('270', plain, (~ (v2_struct_0 @ sk_B)),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.12  thf('271', plain,
% 1.95/2.12      (((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A))),
% 1.95/2.12      inference('sup-', [status(thm)], ['269', '270'])).
% 1.95/2.12  thf('272', plain, (~ (v2_struct_0 @ sk_D)),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.12  thf('273', plain, (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C))),
% 1.95/2.12      inference('clc', [status(thm)], ['271', '272'])).
% 1.95/2.12  thf('274', plain, (~ (v2_struct_0 @ sk_A)),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.12  thf('275', plain, ((v2_struct_0 @ sk_C)),
% 1.95/2.12      inference('clc', [status(thm)], ['273', '274'])).
% 1.95/2.12  thf('276', plain, ($false), inference('demod', [status(thm)], ['0', '275'])).
% 1.95/2.12  
% 1.95/2.12  % SZS output end Refutation
% 1.95/2.12  
% 1.95/2.12  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
