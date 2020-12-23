%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.w47P5zETGf

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:05 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  258 (1947 expanded)
%              Number of leaves         :   28 ( 559 expanded)
%              Depth                    :   31
%              Number of atoms          : 3722 (98511 expanded)
%              Number of equality atoms :   70 (3336 expanded)
%              Maximal formula depth    :   32 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(k1_tsep_1_type,type,(
    k1_tsep_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

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
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H )
    | ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H )
   <= ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H ) ),
    inference(split,[status(esa)],['1'])).

thf('3',plain,(
    sk_F = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    sk_H = sk_G ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_G )
   <= ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('7',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_G )
    | ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference(split,[status(esa)],['7'])).

thf('9',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t123_tmap_1,axiom,(
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
                     => ! [F: $i] :
                          ( ( m1_subset_1 @ F @ ( u1_struct_0 @ C ) )
                         => ! [G: $i] :
                              ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) )
                             => ! [H: $i] :
                                  ( ( m1_subset_1 @ H @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) )
                                 => ( ( ( H = F )
                                      & ( H = G ) )
                                   => ( ( r1_tmap_1 @ ( k1_tsep_1 @ A @ C @ D ) @ B @ E @ H )
                                    <=> ( ( r1_tmap_1 @ C @ B @ ( k3_tmap_1 @ A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ C @ E ) @ F )
                                        & ( r1_tmap_1 @ D @ B @ ( k3_tmap_1 @ A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ D @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ) )).

thf('13',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( v2_struct_0 @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ~ ( l1_pre_topc @ X9 )
      | ( v2_struct_0 @ X10 )
      | ~ ( m1_pre_topc @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X13 ) )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) )
      | ~ ( r1_tmap_1 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X9 @ X15 @ X14 )
      | ( r1_tmap_1 @ X13 @ X9 @ ( k3_tmap_1 @ X11 @ X9 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X13 @ X15 ) @ X12 )
      | ( X14 != X16 )
      | ( X14 != X12 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X10 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( v1_funct_2 @ X15 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( m1_pre_topc @ X13 @ X11 )
      | ( v2_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t123_tmap_1])).

thf('14',plain,(
    ! [X9: $i,X10: $i,X11: $i,X13: $i,X15: $i,X16: $i] :
      ( ( v2_struct_0 @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ( v2_struct_0 @ X13 )
      | ~ ( m1_pre_topc @ X13 @ X11 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_funct_2 @ X15 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X10 ) )
      | ( r1_tmap_1 @ X13 @ X9 @ ( k3_tmap_1 @ X11 @ X9 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X13 @ X15 ) @ X16 )
      | ~ ( r1_tmap_1 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X9 @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X13 ) )
      | ~ ( m1_pre_topc @ X10 @ X11 )
      | ( v2_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_E )
      | ~ ( m1_pre_topc @ sk_E @ sk_A )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      | ~ ( r1_tmap_1 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ X0 @ X1 @ X2 )
      | ( r1_tmap_1 @ sk_D @ X0 @ ( k3_tmap_1 @ sk_A @ X0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_D @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_E ) )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_E )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_tmap_1 @ sk_A @ X0 @ X1 @ X2 )
      | ( r1_tmap_1 @ sk_D @ X0 @ ( k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_D @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_E ) )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16','17','18','19','20','21','22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_E ) )
      | ( r1_tmap_1 @ sk_D @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C ) @ X0 )
      | ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D ) )
      | ( v2_struct_0 @ sk_E )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','24'])).

thf('26',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('29',plain,(
    ! [X17: $i] :
      ( ( m1_pre_topc @ X17 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('30',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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

thf('31',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( v2_struct_0 @ X4 )
      | ~ ( v2_pre_topc @ X4 )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( m1_pre_topc @ X5 @ X6 )
      | ~ ( m1_pre_topc @ X5 @ X7 )
      | ( ( k3_tmap_1 @ X6 @ X4 @ X7 @ X5 @ X8 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X4 ) @ X8 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X4 ) ) ) )
      | ~ ( v1_funct_2 @ X8 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X4 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( m1_pre_topc @ X7 @ X6 )
      | ~ ( l1_pre_topc @ X6 )
      | ~ ( v2_pre_topc @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d5_tmap_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_A @ X0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_A @ X1 @ sk_C )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_A @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_A @ X1 @ sk_C )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['32','33','34','35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_C )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','37'])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_C )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','39','40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_C )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ sk_D ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['28','43'])).

thf('45',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ( ( k2_tmap_1 @ X2 @ X0 @ X3 @ X1 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) @ X3 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_2 @ X3 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['52','53','54','55','56','57','58'])).

thf('60',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ sk_D ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['49','59'])).

thf('61',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference(clc,[status(thm)],['60','61'])).

thf('63',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C ) ),
    inference('sup+',[status(thm)],['48','64'])).

thf('66',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_E ) )
      | ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ X0 )
      | ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D ) )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['25','26','27','65','66','67'])).

thf('69',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_E )
      | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_D ) )
      | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_G )
      | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_E ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference('sup-',[status(thm)],['10','68'])).

thf('70',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    sk_H = sk_G ),
    inference('sup+',[status(thm)],['3','4'])).

thf('76',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_E ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_E )
      | ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_G )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference(demod,[status(thm)],['69','70','73','76'])).

thf('78',plain,
    ( ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('79',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( v2_struct_0 @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ~ ( l1_pre_topc @ X9 )
      | ( v2_struct_0 @ X10 )
      | ~ ( m1_pre_topc @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X13 ) )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) )
      | ~ ( r1_tmap_1 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X9 @ X15 @ X14 )
      | ( r1_tmap_1 @ X10 @ X9 @ ( k3_tmap_1 @ X11 @ X9 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X10 @ X15 ) @ X16 )
      | ( X14 != X16 )
      | ( X14 != X12 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X10 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( v1_funct_2 @ X15 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( m1_pre_topc @ X13 @ X11 )
      | ( v2_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t123_tmap_1])).

thf('82',plain,(
    ! [X9: $i,X10: $i,X11: $i,X13: $i,X15: $i,X16: $i] :
      ( ( v2_struct_0 @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ( v2_struct_0 @ X13 )
      | ~ ( m1_pre_topc @ X13 @ X11 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_funct_2 @ X15 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X10 ) )
      | ( r1_tmap_1 @ X10 @ X9 @ ( k3_tmap_1 @ X11 @ X9 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X10 @ X15 ) @ X16 )
      | ~ ( r1_tmap_1 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X9 @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X13 ) )
      | ~ ( m1_pre_topc @ X10 @ X11 )
      | ( v2_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_E )
      | ~ ( m1_pre_topc @ sk_E @ sk_A )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      | ~ ( r1_tmap_1 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ X0 @ X1 @ X2 )
      | ( r1_tmap_1 @ sk_E @ X0 @ ( k3_tmap_1 @ sk_A @ X0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_E @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_E ) )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['80','82'])).

thf('84',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_E )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_tmap_1 @ sk_A @ X0 @ X1 @ X2 )
      | ( r1_tmap_1 @ sk_E @ X0 @ ( k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_E @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_E ) )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['83','84','85','86','87','88','89','90','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_E ) )
      | ( r1_tmap_1 @ sk_E @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C ) @ X0 )
      | ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D ) )
      | ( v2_struct_0 @ sk_E )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['79','92'])).

thf('94',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_C )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('98',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ sk_E ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ sk_E ) ) ) ),
    inference(clc,[status(thm)],['98','99'])).

thf('101',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['100','101'])).

thf('103',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['52','53','54','55','56','57','58'])).

thf('105',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ sk_E ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ sk_E ) ) ) ),
    inference(clc,[status(thm)],['105','106'])).

thf('108',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['107','108'])).

thf('110',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C ) ),
    inference('sup+',[status(thm)],['102','109'])).

thf('111',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_E ) )
      | ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ X0 )
      | ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D ) )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['93','94','95','110','111','112'])).

thf('114',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_E )
      | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_D ) )
      | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_G )
      | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_E ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference('sup-',[status(thm)],['78','113'])).

thf('115',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('117',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_E ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('118',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_E )
      | ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_G )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference(demod,[status(thm)],['114','115','116','117'])).

thf('119',plain,
    ( ~ ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H )
    | ~ ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    sk_H = sk_G ),
    inference('sup+',[status(thm)],['3','4'])).

thf('121',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( ~ ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G ) ),
    inference(demod,[status(thm)],['119','120','121'])).

thf('123',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_B )
      | ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G )
      | ~ ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_G ) )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference('sup-',[status(thm)],['118','122'])).

thf('124',plain,
    ( ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('125',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_B )
      | ~ ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_G ) )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference('sup-',[status(thm)],['77','125'])).

thf('127',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference(simplify,[status(thm)],['126'])).

thf('128',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_E ) )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference(clc,[status(thm)],['129','130'])).

thf('132',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,
    ( ( v2_struct_0 @ sk_E )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference(clc,[status(thm)],['131','132'])).

thf('134',plain,(
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,
    ( ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H )
    | ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference(split,[status(esa)],['1'])).

thf('137',plain,(
    r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H ),
    inference('sat_resolution*',[status(thm)],['135','136'])).

thf('138',plain,(
    r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_G ),
    inference(simpl_trail,[status(thm)],['6','137'])).

thf('139',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( v2_struct_0 @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ~ ( l1_pre_topc @ X9 )
      | ( v2_struct_0 @ X10 )
      | ~ ( m1_pre_topc @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X13 ) )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) )
      | ~ ( r1_tmap_1 @ X13 @ X9 @ ( k3_tmap_1 @ X11 @ X9 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X13 @ X15 ) @ X12 )
      | ~ ( r1_tmap_1 @ X10 @ X9 @ ( k3_tmap_1 @ X11 @ X9 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X10 @ X15 ) @ X16 )
      | ( r1_tmap_1 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X9 @ X15 @ X14 )
      | ( X14 != X16 )
      | ( X14 != X12 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X10 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( v1_funct_2 @ X15 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( m1_pre_topc @ X13 @ X11 )
      | ( v2_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t123_tmap_1])).

thf('142',plain,(
    ! [X9: $i,X10: $i,X11: $i,X13: $i,X15: $i,X16: $i] :
      ( ( v2_struct_0 @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ( v2_struct_0 @ X13 )
      | ~ ( m1_pre_topc @ X13 @ X11 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_funct_2 @ X15 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X10 ) )
      | ( r1_tmap_1 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X9 @ X15 @ X16 )
      | ~ ( r1_tmap_1 @ X10 @ X9 @ ( k3_tmap_1 @ X11 @ X9 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X10 @ X15 ) @ X16 )
      | ~ ( r1_tmap_1 @ X13 @ X9 @ ( k3_tmap_1 @ X11 @ X9 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X13 @ X15 ) @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X13 ) )
      | ~ ( m1_pre_topc @ X10 @ X11 )
      | ( v2_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(simplify,[status(thm)],['141'])).

thf('143',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_E )
      | ~ ( m1_pre_topc @ sk_E @ sk_A )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      | ~ ( r1_tmap_1 @ sk_D @ X0 @ ( k3_tmap_1 @ sk_A @ X0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_D @ X1 ) @ X2 )
      | ~ ( r1_tmap_1 @ sk_E @ X0 @ ( k3_tmap_1 @ sk_A @ X0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_E @ X1 ) @ X2 )
      | ( r1_tmap_1 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ X0 @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_E ) )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['140','142'])).

thf('144',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_E )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_tmap_1 @ sk_D @ X0 @ ( k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_D @ X1 ) @ X2 )
      | ~ ( r1_tmap_1 @ sk_E @ X0 @ ( k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_E @ X1 ) @ X2 )
      | ( r1_tmap_1 @ sk_A @ X0 @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_E ) )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['143','144','145','146','147','148','149','150','151','152'])).

thf('154',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_E ) )
      | ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 )
      | ~ ( r1_tmap_1 @ sk_E @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C ) @ X0 )
      | ~ ( r1_tmap_1 @ sk_D @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D ) )
      | ( v2_struct_0 @ sk_E )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['139','153'])).

thf('155',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C ) ),
    inference('sup+',[status(thm)],['102','109'])).

thf('158',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C ) ),
    inference('sup+',[status(thm)],['48','64'])).

thf('159',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_E ) )
      | ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 )
      | ~ ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ X0 )
      | ~ ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D ) )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['154','155','156','157','158','159','160'])).

thf('162',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_D ) )
    | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_G )
    | ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G )
    | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_E ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['138','161'])).

thf('163',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('165',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_G )
   <= ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_G ) ),
    inference(split,[status(esa)],['7'])).

thf('166',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_G )
    | ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_G )
    | ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G ) ),
    inference(demod,[status(thm)],['166','167'])).

thf('169',plain,
    ( ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G ) ),
    inference(split,[status(esa)],['168'])).

thf('170',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_E ) )
      | ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ X0 )
      | ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D ) )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['25','26','27','65','66','67'])).

thf('171',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_E )
      | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_D ) )
      | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_G )
      | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_E ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G ) ),
    inference('sup-',[status(thm)],['169','170'])).

thf('172',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('174',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_E ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('175',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_E )
      | ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_G )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G ) ),
    inference(demod,[status(thm)],['171','172','173','174'])).

thf('176',plain,
    ( ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_G )
   <= ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('177',plain,
    ( ~ ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G ) ),
    inference(demod,[status(thm)],['119','120','121'])).

thf('178',plain,
    ( ( ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G )
      | ~ ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_G ) )
   <= ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H ) ),
    inference('sup-',[status(thm)],['176','177'])).

thf('179',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_B )
      | ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G ) )
   <= ( ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H )
      & ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G ) ) ),
    inference('sup-',[status(thm)],['175','178'])).

thf('180',plain,
    ( ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G ) ),
    inference(split,[status(esa)],['168'])).

thf('181',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H )
      & ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G ) ) ),
    inference(demod,[status(thm)],['179','180'])).

thf('182',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H )
      & ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G ) ) ),
    inference('sup-',[status(thm)],['181','182'])).

thf('184',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_E ) )
   <= ( ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H )
      & ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G ) ) ),
    inference(clc,[status(thm)],['183','184'])).

thf('186',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,
    ( ( v2_struct_0 @ sk_E )
   <= ( ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H )
      & ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G ) ) ),
    inference(clc,[status(thm)],['185','186'])).

thf('188',plain,(
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,
    ( ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G )
    | ~ ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H ) ),
    inference('sup-',[status(thm)],['187','188'])).

thf('190',plain,
    ( ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G ) ),
    inference(split,[status(esa)],['168'])).

thf('191',plain,
    ( ~ ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H )
    | ~ ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,
    ( ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference(split,[status(esa)],['191'])).

thf('193',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,
    ( ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G )
   <= ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference(demod,[status(thm)],['192','193'])).

thf('195',plain,
    ( ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G )
    | ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference('sup-',[status(thm)],['190','194'])).

thf('196',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_E )
      | ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_G )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference(demod,[status(thm)],['114','115','116','117'])).

thf('197',plain,
    ( ~ ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H )
   <= ~ ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H ) ),
    inference(split,[status(esa)],['191'])).

thf('198',plain,(
    sk_H = sk_G ),
    inference('sup+',[status(thm)],['3','4'])).

thf('199',plain,
    ( ~ ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_G )
   <= ~ ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H ) ),
    inference(demod,[status(thm)],['197','198'])).

thf('200',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H )
      & ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ) ),
    inference('sup-',[status(thm)],['196','199'])).

thf('201',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('202',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ~ ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H )
      & ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ) ),
    inference('sup-',[status(thm)],['200','201'])).

thf('203',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_E ) )
   <= ( ~ ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H )
      & ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ) ),
    inference(clc,[status(thm)],['202','203'])).

thf('205',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,
    ( ( v2_struct_0 @ sk_E )
   <= ( ~ ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H )
      & ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ) ),
    inference(clc,[status(thm)],['204','205'])).

thf('207',plain,(
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,
    ( ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H )
    | ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference('sup-',[status(thm)],['206','207'])).

thf('209',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_G )
    | ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G ) ),
    inference(split,[status(esa)],['168'])).

thf('210',plain,(
    r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_G ),
    inference('sat_resolution*',[status(thm)],['189','195','208','209'])).

thf('211',plain,(
    r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_G ),
    inference(simpl_trail,[status(thm)],['165','210'])).

thf('212',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_E ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('213',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['162','163','164','211','212'])).

thf('214',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_G )
   <= ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_G ) ),
    inference(split,[status(esa)],['7'])).

thf('215',plain,
    ( ( ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G )
      | ~ ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_G ) )
   <= ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H ) ),
    inference('sup-',[status(thm)],['176','177'])).

thf('216',plain,
    ( ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G )
   <= ( ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_G )
      & ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H ) ) ),
    inference('sup-',[status(thm)],['214','215'])).

thf('217',plain,(
    r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_G ),
    inference('sat_resolution*',[status(thm)],['189','195','208','209'])).

thf('218',plain,
    ( ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G )
   <= ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H ) ),
    inference(simpl_trail,[status(thm)],['216','217'])).

thf('219',plain,(
    r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H ),
    inference('sat_resolution*',[status(thm)],['135','136'])).

thf('220',plain,(
    ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G ) ),
    inference(simpl_trail,[status(thm)],['218','219'])).

thf('221',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['213','220'])).

thf('222',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('223',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['221','222'])).

thf('224',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('225',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_E ) ),
    inference(clc,[status(thm)],['223','224'])).

thf('226',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('227',plain,(
    v2_struct_0 @ sk_E ),
    inference(clc,[status(thm)],['225','226'])).

thf('228',plain,(
    $false ),
    inference(demod,[status(thm)],['0','227'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.w47P5zETGf
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:03:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.51  % Solved by: fo/fo7.sh
% 0.20/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.51  % done 99 iterations in 0.054s
% 0.20/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.51  % SZS output start Refutation
% 0.20/0.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.51  thf(sk_E_type, type, sk_E: $i).
% 0.20/0.51  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.51  thf(sk_G_type, type, sk_G: $i).
% 0.20/0.51  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.51  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.20/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.51  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.51  thf(sk_H_type, type, sk_H: $i).
% 0.20/0.51  thf(sk_F_type, type, sk_F: $i).
% 0.20/0.51  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.20/0.51  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.51  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.20/0.51  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.20/0.51  thf(k1_tsep_1_type, type, k1_tsep_1: $i > $i > $i > $i).
% 0.20/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.51  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.51  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.20/0.51  thf(t125_tmap_1, conjecture,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.51             ( l1_pre_topc @ B ) ) =>
% 0.20/0.51           ( ![C:$i]:
% 0.20/0.51             ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.51                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.51                 ( m1_subset_1 @
% 0.20/0.51                   C @ 
% 0.20/0.51                   ( k1_zfmisc_1 @
% 0.20/0.51                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.51               ( ![D:$i]:
% 0.20/0.51                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.20/0.51                   ( ![E:$i]:
% 0.20/0.51                     ( ( ( ~( v2_struct_0 @ E ) ) & ( m1_pre_topc @ E @ A ) ) =>
% 0.20/0.51                       ( ( ( A ) = ( k1_tsep_1 @ A @ D @ E ) ) =>
% 0.20/0.51                         ( ![F:$i]:
% 0.20/0.51                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.51                             ( ![G:$i]:
% 0.20/0.51                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.20/0.51                                 ( ![H:$i]:
% 0.20/0.51                                   ( ( m1_subset_1 @ H @ ( u1_struct_0 @ E ) ) =>
% 0.20/0.51                                     ( ( ( ( F ) = ( G ) ) & ( ( F ) = ( H ) ) ) =>
% 0.20/0.51                                       ( ( r1_tmap_1 @ A @ B @ C @ F ) <=>
% 0.20/0.51                                         ( ( r1_tmap_1 @
% 0.20/0.51                                             D @ B @ 
% 0.20/0.51                                             ( k2_tmap_1 @ A @ B @ C @ D ) @ G ) & 
% 0.20/0.51                                           ( r1_tmap_1 @
% 0.20/0.51                                             E @ B @ 
% 0.20/0.51                                             ( k2_tmap_1 @ A @ B @ C @ E ) @ H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.51    (~( ![A:$i]:
% 0.20/0.51        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.51            ( l1_pre_topc @ A ) ) =>
% 0.20/0.51          ( ![B:$i]:
% 0.20/0.51            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.51                ( l1_pre_topc @ B ) ) =>
% 0.20/0.51              ( ![C:$i]:
% 0.20/0.51                ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.51                    ( v1_funct_2 @
% 0.20/0.51                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.51                    ( m1_subset_1 @
% 0.20/0.51                      C @ 
% 0.20/0.51                      ( k1_zfmisc_1 @
% 0.20/0.51                        ( k2_zfmisc_1 @
% 0.20/0.51                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.51                  ( ![D:$i]:
% 0.20/0.51                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.20/0.51                      ( ![E:$i]:
% 0.20/0.51                        ( ( ( ~( v2_struct_0 @ E ) ) & ( m1_pre_topc @ E @ A ) ) =>
% 0.20/0.51                          ( ( ( A ) = ( k1_tsep_1 @ A @ D @ E ) ) =>
% 0.20/0.51                            ( ![F:$i]:
% 0.20/0.51                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.51                                ( ![G:$i]:
% 0.20/0.51                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.20/0.51                                    ( ![H:$i]:
% 0.20/0.51                                      ( ( m1_subset_1 @ H @ ( u1_struct_0 @ E ) ) =>
% 0.20/0.51                                        ( ( ( ( F ) = ( G ) ) & 
% 0.20/0.51                                            ( ( F ) = ( H ) ) ) =>
% 0.20/0.51                                          ( ( r1_tmap_1 @ A @ B @ C @ F ) <=>
% 0.20/0.51                                            ( ( r1_tmap_1 @
% 0.20/0.51                                                D @ B @ 
% 0.20/0.51                                                ( k2_tmap_1 @ A @ B @ C @ D ) @ 
% 0.20/0.51                                                G ) & 
% 0.20/0.51                                              ( r1_tmap_1 @
% 0.20/0.51                                                E @ B @ 
% 0.20/0.51                                                ( k2_tmap_1 @ A @ B @ C @ E ) @ 
% 0.20/0.51                                                H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.51    inference('cnf.neg', [status(esa)], [t125_tmap_1])).
% 0.20/0.51  thf('0', plain, (~ (v2_struct_0 @ sk_E)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('1', plain,
% 0.20/0.51      (((r1_tmap_1 @ sk_E @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.20/0.51         sk_H)
% 0.20/0.51        | (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('2', plain,
% 0.20/0.51      (((r1_tmap_1 @ sk_E @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.20/0.51         sk_H))
% 0.20/0.51         <= (((r1_tmap_1 @ sk_E @ sk_B @ 
% 0.20/0.51               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_H)))),
% 0.20/0.51      inference('split', [status(esa)], ['1'])).
% 0.20/0.51  thf('3', plain, (((sk_F) = (sk_H))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('4', plain, (((sk_F) = (sk_G))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('5', plain, (((sk_H) = (sk_G))),
% 0.20/0.51      inference('sup+', [status(thm)], ['3', '4'])).
% 0.20/0.51  thf('6', plain,
% 0.20/0.51      (((r1_tmap_1 @ sk_E @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.20/0.51         sk_G))
% 0.20/0.51         <= (((r1_tmap_1 @ sk_E @ sk_B @ 
% 0.20/0.51               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_H)))),
% 0.20/0.51      inference('demod', [status(thm)], ['2', '5'])).
% 0.20/0.51  thf('7', plain,
% 0.20/0.51      (((r1_tmap_1 @ sk_D @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.20/0.51         sk_G)
% 0.20/0.51        | (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('8', plain,
% 0.20/0.51      (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F))
% 0.20/0.51         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F)))),
% 0.20/0.51      inference('split', [status(esa)], ['7'])).
% 0.20/0.51  thf('9', plain, (((sk_F) = (sk_G))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('10', plain,
% 0.20/0.51      (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G))
% 0.20/0.51         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F)))),
% 0.20/0.51      inference('demod', [status(thm)], ['8', '9'])).
% 0.20/0.51  thf('11', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_C @ 
% 0.20/0.51        (k1_zfmisc_1 @ 
% 0.20/0.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('12', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(t123_tmap_1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.51             ( l1_pre_topc @ B ) ) =>
% 0.20/0.51           ( ![C:$i]:
% 0.20/0.51             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.51               ( ![D:$i]:
% 0.20/0.51                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.20/0.51                   ( ![E:$i]:
% 0.20/0.51                     ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.51                         ( v1_funct_2 @
% 0.20/0.51                           E @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 0.20/0.51                           ( u1_struct_0 @ B ) ) & 
% 0.20/0.51                         ( m1_subset_1 @
% 0.20/0.51                           E @ 
% 0.20/0.51                           ( k1_zfmisc_1 @
% 0.20/0.51                             ( k2_zfmisc_1 @
% 0.20/0.51                               ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 0.20/0.51                               ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.51                       ( ![F:$i]:
% 0.20/0.51                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ C ) ) =>
% 0.20/0.51                           ( ![G:$i]:
% 0.20/0.51                             ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.20/0.51                               ( ![H:$i]:
% 0.20/0.51                                 ( ( m1_subset_1 @
% 0.20/0.51                                     H @ 
% 0.20/0.51                                     ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) ) =>
% 0.20/0.51                                   ( ( ( ( H ) = ( F ) ) & ( ( H ) = ( G ) ) ) =>
% 0.20/0.51                                     ( ( r1_tmap_1 @
% 0.20/0.51                                         ( k1_tsep_1 @ A @ C @ D ) @ B @ E @ H ) <=>
% 0.20/0.51                                       ( ( r1_tmap_1 @
% 0.20/0.51                                           C @ B @ 
% 0.20/0.51                                           ( k3_tmap_1 @
% 0.20/0.51                                             A @ B @ 
% 0.20/0.51                                             ( k1_tsep_1 @ A @ C @ D ) @ C @ E ) @ 
% 0.20/0.51                                           F ) & 
% 0.20/0.51                                         ( r1_tmap_1 @
% 0.20/0.51                                           D @ B @ 
% 0.20/0.51                                           ( k3_tmap_1 @
% 0.20/0.51                                             A @ B @ 
% 0.20/0.51                                             ( k1_tsep_1 @ A @ C @ D ) @ D @ E ) @ 
% 0.20/0.51                                           G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.51  thf('13', plain,
% 0.20/0.51      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i, 
% 0.20/0.51         X16 : $i]:
% 0.20/0.51         ((v2_struct_0 @ X9)
% 0.20/0.51          | ~ (v2_pre_topc @ X9)
% 0.20/0.51          | ~ (l1_pre_topc @ X9)
% 0.20/0.51          | (v2_struct_0 @ X10)
% 0.20/0.51          | ~ (m1_pre_topc @ X10 @ X11)
% 0.20/0.51          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X13))
% 0.20/0.51          | ~ (m1_subset_1 @ X14 @ 
% 0.20/0.51               (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)))
% 0.20/0.51          | ~ (r1_tmap_1 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X9 @ X15 @ X14)
% 0.20/0.51          | (r1_tmap_1 @ X13 @ X9 @ 
% 0.20/0.51             (k3_tmap_1 @ X11 @ X9 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X13 @ X15) @ 
% 0.20/0.51             X12)
% 0.20/0.51          | ((X14) != (X16))
% 0.20/0.51          | ((X14) != (X12))
% 0.20/0.51          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X10))
% 0.20/0.51          | ~ (m1_subset_1 @ X15 @ 
% 0.20/0.51               (k1_zfmisc_1 @ 
% 0.20/0.51                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.20/0.51                 (u1_struct_0 @ X9))))
% 0.20/0.51          | ~ (v1_funct_2 @ X15 @ 
% 0.20/0.51               (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.20/0.51               (u1_struct_0 @ X9))
% 0.20/0.51          | ~ (v1_funct_1 @ X15)
% 0.20/0.51          | ~ (m1_pre_topc @ X13 @ X11)
% 0.20/0.51          | (v2_struct_0 @ X13)
% 0.20/0.51          | ~ (l1_pre_topc @ X11)
% 0.20/0.51          | ~ (v2_pre_topc @ X11)
% 0.20/0.51          | (v2_struct_0 @ X11))),
% 0.20/0.51      inference('cnf', [status(esa)], [t123_tmap_1])).
% 0.20/0.51  thf('14', plain,
% 0.20/0.51      (![X9 : $i, X10 : $i, X11 : $i, X13 : $i, X15 : $i, X16 : $i]:
% 0.20/0.51         ((v2_struct_0 @ X11)
% 0.20/0.51          | ~ (v2_pre_topc @ X11)
% 0.20/0.51          | ~ (l1_pre_topc @ X11)
% 0.20/0.51          | (v2_struct_0 @ X13)
% 0.20/0.51          | ~ (m1_pre_topc @ X13 @ X11)
% 0.20/0.51          | ~ (v1_funct_1 @ X15)
% 0.20/0.51          | ~ (v1_funct_2 @ X15 @ 
% 0.20/0.51               (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.20/0.51               (u1_struct_0 @ X9))
% 0.20/0.51          | ~ (m1_subset_1 @ X15 @ 
% 0.20/0.51               (k1_zfmisc_1 @ 
% 0.20/0.51                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.20/0.51                 (u1_struct_0 @ X9))))
% 0.20/0.51          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X10))
% 0.20/0.51          | (r1_tmap_1 @ X13 @ X9 @ 
% 0.20/0.51             (k3_tmap_1 @ X11 @ X9 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X13 @ X15) @ 
% 0.20/0.51             X16)
% 0.20/0.51          | ~ (r1_tmap_1 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X9 @ X15 @ X16)
% 0.20/0.51          | ~ (m1_subset_1 @ X16 @ 
% 0.20/0.51               (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)))
% 0.20/0.51          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X13))
% 0.20/0.51          | ~ (m1_pre_topc @ X10 @ X11)
% 0.20/0.51          | (v2_struct_0 @ X10)
% 0.20/0.51          | ~ (l1_pre_topc @ X9)
% 0.20/0.51          | ~ (v2_pre_topc @ X9)
% 0.20/0.51          | (v2_struct_0 @ X9))),
% 0.20/0.51      inference('simplify', [status(thm)], ['13'])).
% 0.20/0.51  thf('15', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X1 @ 
% 0.20/0.51             (k1_zfmisc_1 @ 
% 0.20/0.51              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 0.20/0.51          | (v2_struct_0 @ X0)
% 0.20/0.51          | ~ (v2_pre_topc @ X0)
% 0.20/0.51          | ~ (l1_pre_topc @ X0)
% 0.20/0.51          | (v2_struct_0 @ sk_E)
% 0.20/0.51          | ~ (m1_pre_topc @ sk_E @ sk_A)
% 0.20/0.51          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 0.20/0.51          | ~ (m1_subset_1 @ X2 @ 
% 0.20/0.51               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))
% 0.20/0.51          | ~ (r1_tmap_1 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ X0 @ X1 @ X2)
% 0.20/0.51          | (r1_tmap_1 @ sk_D @ X0 @ 
% 0.20/0.51             (k3_tmap_1 @ sk_A @ X0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ 
% 0.20/0.51              sk_D @ X1) @ 
% 0.20/0.51             X2)
% 0.20/0.51          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_E))
% 0.20/0.51          | ~ (v1_funct_2 @ X1 @ 
% 0.20/0.51               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 0.20/0.51               (u1_struct_0 @ X0))
% 0.20/0.51          | ~ (v1_funct_1 @ X1)
% 0.20/0.51          | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.20/0.51          | (v2_struct_0 @ sk_D)
% 0.20/0.51          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.51          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.51          | (v2_struct_0 @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['12', '14'])).
% 0.20/0.51  thf('16', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('17', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('18', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('19', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('20', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('21', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('23', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('24', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X1 @ 
% 0.20/0.51             (k1_zfmisc_1 @ 
% 0.20/0.51              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 0.20/0.51          | (v2_struct_0 @ X0)
% 0.20/0.51          | ~ (v2_pre_topc @ X0)
% 0.20/0.51          | ~ (l1_pre_topc @ X0)
% 0.20/0.51          | (v2_struct_0 @ sk_E)
% 0.20/0.51          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 0.20/0.51          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_A))
% 0.20/0.51          | ~ (r1_tmap_1 @ sk_A @ X0 @ X1 @ X2)
% 0.20/0.51          | (r1_tmap_1 @ sk_D @ X0 @ 
% 0.20/0.51             (k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_D @ X1) @ X2)
% 0.20/0.51          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_E))
% 0.20/0.51          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))
% 0.20/0.51          | ~ (v1_funct_1 @ X1)
% 0.20/0.51          | (v2_struct_0 @ sk_D)
% 0.20/0.51          | (v2_struct_0 @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)],
% 0.20/0.51                ['15', '16', '17', '18', '19', '20', '21', '22', '23'])).
% 0.20/0.51  thf('25', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v2_struct_0 @ sk_A)
% 0.20/0.51          | (v2_struct_0 @ sk_D)
% 0.20/0.51          | ~ (v1_funct_1 @ sk_C)
% 0.20/0.51          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_E))
% 0.20/0.51          | (r1_tmap_1 @ sk_D @ sk_B @ 
% 0.20/0.51             (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C) @ X0)
% 0.20/0.51          | ~ (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ X0)
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D))
% 0.20/0.51          | (v2_struct_0 @ sk_E)
% 0.20/0.51          | ~ (l1_pre_topc @ sk_B)
% 0.20/0.51          | ~ (v2_pre_topc @ sk_B)
% 0.20/0.51          | (v2_struct_0 @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['11', '24'])).
% 0.20/0.51  thf('26', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('27', plain,
% 0.20/0.51      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('28', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(t2_tsep_1, axiom,
% 0.20/0.51    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.20/0.51  thf('29', plain,
% 0.20/0.51      (![X17 : $i]: ((m1_pre_topc @ X17 @ X17) | ~ (l1_pre_topc @ X17))),
% 0.20/0.51      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.20/0.51  thf('30', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_C @ 
% 0.20/0.51        (k1_zfmisc_1 @ 
% 0.20/0.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(d5_tmap_1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.51             ( l1_pre_topc @ B ) ) =>
% 0.20/0.51           ( ![C:$i]:
% 0.20/0.51             ( ( m1_pre_topc @ C @ A ) =>
% 0.20/0.51               ( ![D:$i]:
% 0.20/0.51                 ( ( m1_pre_topc @ D @ A ) =>
% 0.20/0.51                   ( ![E:$i]:
% 0.20/0.51                     ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.51                         ( v1_funct_2 @
% 0.20/0.51                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.51                         ( m1_subset_1 @
% 0.20/0.51                           E @ 
% 0.20/0.51                           ( k1_zfmisc_1 @
% 0.20/0.51                             ( k2_zfmisc_1 @
% 0.20/0.51                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.51                       ( ( m1_pre_topc @ D @ C ) =>
% 0.20/0.51                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 0.20/0.51                           ( k2_partfun1 @
% 0.20/0.51                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 0.20/0.51                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.51  thf('31', plain,
% 0.20/0.51      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.51         ((v2_struct_0 @ X4)
% 0.20/0.51          | ~ (v2_pre_topc @ X4)
% 0.20/0.51          | ~ (l1_pre_topc @ X4)
% 0.20/0.51          | ~ (m1_pre_topc @ X5 @ X6)
% 0.20/0.51          | ~ (m1_pre_topc @ X5 @ X7)
% 0.20/0.51          | ((k3_tmap_1 @ X6 @ X4 @ X7 @ X5 @ X8)
% 0.20/0.51              = (k2_partfun1 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X4) @ X8 @ 
% 0.20/0.51                 (u1_struct_0 @ X5)))
% 0.20/0.51          | ~ (m1_subset_1 @ X8 @ 
% 0.20/0.51               (k1_zfmisc_1 @ 
% 0.20/0.51                (k2_zfmisc_1 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X4))))
% 0.20/0.51          | ~ (v1_funct_2 @ X8 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X4))
% 0.20/0.51          | ~ (v1_funct_1 @ X8)
% 0.20/0.51          | ~ (m1_pre_topc @ X7 @ X6)
% 0.20/0.51          | ~ (l1_pre_topc @ X6)
% 0.20/0.51          | ~ (v2_pre_topc @ X6)
% 0.20/0.51          | (v2_struct_0 @ X6))),
% 0.20/0.51      inference('cnf', [status(esa)], [d5_tmap_1])).
% 0.20/0.51  thf('32', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((v2_struct_0 @ X0)
% 0.20/0.51          | ~ (v2_pre_topc @ X0)
% 0.20/0.51          | ~ (l1_pre_topc @ X0)
% 0.20/0.51          | ~ (m1_pre_topc @ sk_A @ X0)
% 0.20/0.51          | ~ (v1_funct_1 @ sk_C)
% 0.20/0.51          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.20/0.51          | ((k3_tmap_1 @ X0 @ sk_B @ sk_A @ X1 @ sk_C)
% 0.20/0.51              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.51                 sk_C @ (u1_struct_0 @ X1)))
% 0.20/0.51          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.20/0.51          | ~ (m1_pre_topc @ X1 @ X0)
% 0.20/0.51          | ~ (l1_pre_topc @ sk_B)
% 0.20/0.51          | ~ (v2_pre_topc @ sk_B)
% 0.20/0.51          | (v2_struct_0 @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['30', '31'])).
% 0.20/0.51  thf('33', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('34', plain,
% 0.20/0.51      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('35', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('36', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('37', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((v2_struct_0 @ X0)
% 0.20/0.51          | ~ (v2_pre_topc @ X0)
% 0.20/0.51          | ~ (l1_pre_topc @ X0)
% 0.20/0.51          | ~ (m1_pre_topc @ sk_A @ X0)
% 0.20/0.51          | ((k3_tmap_1 @ X0 @ sk_B @ sk_A @ X1 @ sk_C)
% 0.20/0.51              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.51                 sk_C @ (u1_struct_0 @ X1)))
% 0.20/0.51          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.20/0.51          | ~ (m1_pre_topc @ X1 @ X0)
% 0.20/0.51          | (v2_struct_0 @ sk_B))),
% 0.20/0.51      inference('demod', [status(thm)], ['32', '33', '34', '35', '36'])).
% 0.20/0.51  thf('38', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (l1_pre_topc @ sk_A)
% 0.20/0.51          | (v2_struct_0 @ sk_B)
% 0.20/0.51          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.20/0.51          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.20/0.51          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_C)
% 0.20/0.51              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.51                 sk_C @ (u1_struct_0 @ X0)))
% 0.20/0.51          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.51          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.51          | (v2_struct_0 @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['29', '37'])).
% 0.20/0.51  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('41', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('42', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v2_struct_0 @ sk_B)
% 0.20/0.51          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.20/0.51          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.20/0.51          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_C)
% 0.20/0.51              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.51                 sk_C @ (u1_struct_0 @ X0)))
% 0.20/0.51          | (v2_struct_0 @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['38', '39', '40', '41'])).
% 0.20/0.51  thf('43', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v2_struct_0 @ sk_A)
% 0.20/0.51          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_C)
% 0.20/0.51              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.51                 sk_C @ (u1_struct_0 @ X0)))
% 0.20/0.51          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.20/0.51          | (v2_struct_0 @ sk_B))),
% 0.20/0.51      inference('simplify', [status(thm)], ['42'])).
% 0.20/0.51  thf('44', plain,
% 0.20/0.51      (((v2_struct_0 @ sk_B)
% 0.20/0.51        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.20/0.51            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.51               sk_C @ (u1_struct_0 @ sk_D)))
% 0.20/0.51        | (v2_struct_0 @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['28', '43'])).
% 0.20/0.51  thf('45', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('46', plain,
% 0.20/0.51      (((v2_struct_0 @ sk_A)
% 0.20/0.51        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.20/0.51            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.51               sk_C @ (u1_struct_0 @ sk_D))))),
% 0.20/0.51      inference('clc', [status(thm)], ['44', '45'])).
% 0.20/0.51  thf('47', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('48', plain,
% 0.20/0.51      (((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.20/0.51         = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.20/0.51            (u1_struct_0 @ sk_D)))),
% 0.20/0.51      inference('clc', [status(thm)], ['46', '47'])).
% 0.20/0.51  thf('49', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('50', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_C @ 
% 0.20/0.51        (k1_zfmisc_1 @ 
% 0.20/0.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(d4_tmap_1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.51             ( l1_pre_topc @ B ) ) =>
% 0.20/0.51           ( ![C:$i]:
% 0.20/0.51             ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.51                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.51                 ( m1_subset_1 @
% 0.20/0.51                   C @ 
% 0.20/0.51                   ( k1_zfmisc_1 @
% 0.20/0.51                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.51               ( ![D:$i]:
% 0.20/0.51                 ( ( m1_pre_topc @ D @ A ) =>
% 0.20/0.51                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 0.20/0.51                     ( k2_partfun1 @
% 0.20/0.51                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.20/0.51                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.51  thf('51', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.51         ((v2_struct_0 @ X0)
% 0.20/0.51          | ~ (v2_pre_topc @ X0)
% 0.20/0.51          | ~ (l1_pre_topc @ X0)
% 0.20/0.51          | ~ (m1_pre_topc @ X1 @ X2)
% 0.20/0.51          | ((k2_tmap_1 @ X2 @ X0 @ X3 @ X1)
% 0.20/0.51              = (k2_partfun1 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0) @ X3 @ 
% 0.20/0.51                 (u1_struct_0 @ X1)))
% 0.20/0.51          | ~ (m1_subset_1 @ X3 @ 
% 0.20/0.51               (k1_zfmisc_1 @ 
% 0.20/0.51                (k2_zfmisc_1 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))))
% 0.20/0.51          | ~ (v1_funct_2 @ X3 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))
% 0.20/0.51          | ~ (v1_funct_1 @ X3)
% 0.20/0.51          | ~ (l1_pre_topc @ X2)
% 0.20/0.51          | ~ (v2_pre_topc @ X2)
% 0.20/0.51          | (v2_struct_0 @ X2))),
% 0.20/0.51      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.20/0.51  thf('52', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v2_struct_0 @ sk_A)
% 0.20/0.51          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.51          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.51          | ~ (v1_funct_1 @ sk_C)
% 0.20/0.51          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.20/0.51          | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0)
% 0.20/0.51              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.51                 sk_C @ (u1_struct_0 @ X0)))
% 0.20/0.51          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.20/0.51          | ~ (l1_pre_topc @ sk_B)
% 0.20/0.51          | ~ (v2_pre_topc @ sk_B)
% 0.20/0.51          | (v2_struct_0 @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['50', '51'])).
% 0.20/0.51  thf('53', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('55', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('56', plain,
% 0.20/0.51      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('57', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('58', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('59', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v2_struct_0 @ sk_A)
% 0.20/0.51          | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0)
% 0.20/0.51              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.51                 sk_C @ (u1_struct_0 @ X0)))
% 0.20/0.51          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.20/0.51          | (v2_struct_0 @ sk_B))),
% 0.20/0.51      inference('demod', [status(thm)],
% 0.20/0.51                ['52', '53', '54', '55', '56', '57', '58'])).
% 0.20/0.51  thf('60', plain,
% 0.20/0.51      (((v2_struct_0 @ sk_B)
% 0.20/0.51        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.20/0.51            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.51               sk_C @ (u1_struct_0 @ sk_D)))
% 0.20/0.51        | (v2_struct_0 @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['49', '59'])).
% 0.20/0.51  thf('61', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('62', plain,
% 0.20/0.51      (((v2_struct_0 @ sk_A)
% 0.20/0.51        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.20/0.51            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.51               sk_C @ (u1_struct_0 @ sk_D))))),
% 0.20/0.51      inference('clc', [status(thm)], ['60', '61'])).
% 0.20/0.51  thf('63', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('64', plain,
% 0.20/0.51      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.20/0.51         = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.20/0.51            (u1_struct_0 @ sk_D)))),
% 0.20/0.51      inference('clc', [status(thm)], ['62', '63'])).
% 0.20/0.51  thf('65', plain,
% 0.20/0.51      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.20/0.51         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C))),
% 0.20/0.51      inference('sup+', [status(thm)], ['48', '64'])).
% 0.20/0.51  thf('66', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('67', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('68', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v2_struct_0 @ sk_A)
% 0.20/0.51          | (v2_struct_0 @ sk_D)
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_E))
% 0.20/0.51          | (r1_tmap_1 @ sk_D @ sk_B @ 
% 0.20/0.51             (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ X0)
% 0.20/0.51          | ~ (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ X0)
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D))
% 0.20/0.51          | (v2_struct_0 @ sk_E)
% 0.20/0.51          | (v2_struct_0 @ sk_B))),
% 0.20/0.51      inference('demod', [status(thm)], ['25', '26', '27', '65', '66', '67'])).
% 0.20/0.51  thf('69', plain,
% 0.20/0.51      ((((v2_struct_0 @ sk_B)
% 0.20/0.51         | (v2_struct_0 @ sk_E)
% 0.20/0.51         | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_D))
% 0.20/0.51         | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_A))
% 0.20/0.51         | (r1_tmap_1 @ sk_D @ sk_B @ 
% 0.20/0.51            (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_G)
% 0.20/0.51         | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_E))
% 0.20/0.51         | (v2_struct_0 @ sk_D)
% 0.20/0.51         | (v2_struct_0 @ sk_A)))
% 0.20/0.51         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['10', '68'])).
% 0.20/0.51  thf('70', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_D))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('71', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_A))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('72', plain, (((sk_F) = (sk_G))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('73', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['71', '72'])).
% 0.20/0.51  thf('74', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_E))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('75', plain, (((sk_H) = (sk_G))),
% 0.20/0.51      inference('sup+', [status(thm)], ['3', '4'])).
% 0.20/0.51  thf('76', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_E))),
% 0.20/0.51      inference('demod', [status(thm)], ['74', '75'])).
% 0.20/0.51  thf('77', plain,
% 0.20/0.51      ((((v2_struct_0 @ sk_B)
% 0.20/0.51         | (v2_struct_0 @ sk_E)
% 0.20/0.51         | (r1_tmap_1 @ sk_D @ sk_B @ 
% 0.20/0.51            (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_G)
% 0.20/0.51         | (v2_struct_0 @ sk_D)
% 0.20/0.51         | (v2_struct_0 @ sk_A)))
% 0.20/0.51         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F)))),
% 0.20/0.51      inference('demod', [status(thm)], ['69', '70', '73', '76'])).
% 0.20/0.51  thf('78', plain,
% 0.20/0.51      (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G))
% 0.20/0.51         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F)))),
% 0.20/0.51      inference('demod', [status(thm)], ['8', '9'])).
% 0.20/0.51  thf('79', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_C @ 
% 0.20/0.51        (k1_zfmisc_1 @ 
% 0.20/0.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('80', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('81', plain,
% 0.20/0.51      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i, 
% 0.20/0.51         X16 : $i]:
% 0.20/0.51         ((v2_struct_0 @ X9)
% 0.20/0.51          | ~ (v2_pre_topc @ X9)
% 0.20/0.51          | ~ (l1_pre_topc @ X9)
% 0.20/0.51          | (v2_struct_0 @ X10)
% 0.20/0.51          | ~ (m1_pre_topc @ X10 @ X11)
% 0.20/0.51          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X13))
% 0.20/0.51          | ~ (m1_subset_1 @ X14 @ 
% 0.20/0.51               (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)))
% 0.20/0.51          | ~ (r1_tmap_1 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X9 @ X15 @ X14)
% 0.20/0.51          | (r1_tmap_1 @ X10 @ X9 @ 
% 0.20/0.51             (k3_tmap_1 @ X11 @ X9 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X10 @ X15) @ 
% 0.20/0.51             X16)
% 0.20/0.51          | ((X14) != (X16))
% 0.20/0.51          | ((X14) != (X12))
% 0.20/0.51          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X10))
% 0.20/0.51          | ~ (m1_subset_1 @ X15 @ 
% 0.20/0.51               (k1_zfmisc_1 @ 
% 0.20/0.51                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.20/0.51                 (u1_struct_0 @ X9))))
% 0.20/0.51          | ~ (v1_funct_2 @ X15 @ 
% 0.20/0.51               (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.20/0.51               (u1_struct_0 @ X9))
% 0.20/0.51          | ~ (v1_funct_1 @ X15)
% 0.20/0.51          | ~ (m1_pre_topc @ X13 @ X11)
% 0.20/0.51          | (v2_struct_0 @ X13)
% 0.20/0.51          | ~ (l1_pre_topc @ X11)
% 0.20/0.51          | ~ (v2_pre_topc @ X11)
% 0.20/0.51          | (v2_struct_0 @ X11))),
% 0.20/0.51      inference('cnf', [status(esa)], [t123_tmap_1])).
% 0.20/0.51  thf('82', plain,
% 0.20/0.51      (![X9 : $i, X10 : $i, X11 : $i, X13 : $i, X15 : $i, X16 : $i]:
% 0.20/0.51         ((v2_struct_0 @ X11)
% 0.20/0.51          | ~ (v2_pre_topc @ X11)
% 0.20/0.51          | ~ (l1_pre_topc @ X11)
% 0.20/0.51          | (v2_struct_0 @ X13)
% 0.20/0.51          | ~ (m1_pre_topc @ X13 @ X11)
% 0.20/0.51          | ~ (v1_funct_1 @ X15)
% 0.20/0.51          | ~ (v1_funct_2 @ X15 @ 
% 0.20/0.51               (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.20/0.51               (u1_struct_0 @ X9))
% 0.20/0.51          | ~ (m1_subset_1 @ X15 @ 
% 0.20/0.51               (k1_zfmisc_1 @ 
% 0.20/0.51                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.20/0.51                 (u1_struct_0 @ X9))))
% 0.20/0.51          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X10))
% 0.20/0.51          | (r1_tmap_1 @ X10 @ X9 @ 
% 0.20/0.51             (k3_tmap_1 @ X11 @ X9 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X10 @ X15) @ 
% 0.20/0.51             X16)
% 0.20/0.51          | ~ (r1_tmap_1 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X9 @ X15 @ X16)
% 0.20/0.51          | ~ (m1_subset_1 @ X16 @ 
% 0.20/0.51               (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)))
% 0.20/0.51          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X13))
% 0.20/0.51          | ~ (m1_pre_topc @ X10 @ X11)
% 0.20/0.51          | (v2_struct_0 @ X10)
% 0.20/0.51          | ~ (l1_pre_topc @ X9)
% 0.20/0.51          | ~ (v2_pre_topc @ X9)
% 0.20/0.51          | (v2_struct_0 @ X9))),
% 0.20/0.51      inference('simplify', [status(thm)], ['81'])).
% 0.20/0.51  thf('83', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X1 @ 
% 0.20/0.51             (k1_zfmisc_1 @ 
% 0.20/0.51              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 0.20/0.51          | (v2_struct_0 @ X0)
% 0.20/0.51          | ~ (v2_pre_topc @ X0)
% 0.20/0.51          | ~ (l1_pre_topc @ X0)
% 0.20/0.51          | (v2_struct_0 @ sk_E)
% 0.20/0.51          | ~ (m1_pre_topc @ sk_E @ sk_A)
% 0.20/0.51          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 0.20/0.51          | ~ (m1_subset_1 @ X2 @ 
% 0.20/0.51               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))
% 0.20/0.51          | ~ (r1_tmap_1 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ X0 @ X1 @ X2)
% 0.20/0.51          | (r1_tmap_1 @ sk_E @ X0 @ 
% 0.20/0.51             (k3_tmap_1 @ sk_A @ X0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ 
% 0.20/0.51              sk_E @ X1) @ 
% 0.20/0.51             X2)
% 0.20/0.51          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_E))
% 0.20/0.51          | ~ (v1_funct_2 @ X1 @ 
% 0.20/0.51               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 0.20/0.51               (u1_struct_0 @ X0))
% 0.20/0.51          | ~ (v1_funct_1 @ X1)
% 0.20/0.51          | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.20/0.51          | (v2_struct_0 @ sk_D)
% 0.20/0.51          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.51          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.51          | (v2_struct_0 @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['80', '82'])).
% 0.20/0.51  thf('84', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('85', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('86', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('87', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('88', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('89', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('90', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('91', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('92', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X1 @ 
% 0.20/0.51             (k1_zfmisc_1 @ 
% 0.20/0.51              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 0.20/0.51          | (v2_struct_0 @ X0)
% 0.20/0.51          | ~ (v2_pre_topc @ X0)
% 0.20/0.51          | ~ (l1_pre_topc @ X0)
% 0.20/0.51          | (v2_struct_0 @ sk_E)
% 0.20/0.51          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 0.20/0.51          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_A))
% 0.20/0.51          | ~ (r1_tmap_1 @ sk_A @ X0 @ X1 @ X2)
% 0.20/0.51          | (r1_tmap_1 @ sk_E @ X0 @ 
% 0.20/0.51             (k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_E @ X1) @ X2)
% 0.20/0.51          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_E))
% 0.20/0.51          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))
% 0.20/0.51          | ~ (v1_funct_1 @ X1)
% 0.20/0.51          | (v2_struct_0 @ sk_D)
% 0.20/0.51          | (v2_struct_0 @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)],
% 0.20/0.51                ['83', '84', '85', '86', '87', '88', '89', '90', '91'])).
% 0.20/0.51  thf('93', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v2_struct_0 @ sk_A)
% 0.20/0.51          | (v2_struct_0 @ sk_D)
% 0.20/0.51          | ~ (v1_funct_1 @ sk_C)
% 0.20/0.51          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_E))
% 0.20/0.51          | (r1_tmap_1 @ sk_E @ sk_B @ 
% 0.20/0.51             (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C) @ X0)
% 0.20/0.51          | ~ (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ X0)
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D))
% 0.20/0.51          | (v2_struct_0 @ sk_E)
% 0.20/0.51          | ~ (l1_pre_topc @ sk_B)
% 0.20/0.51          | ~ (v2_pre_topc @ sk_B)
% 0.20/0.51          | (v2_struct_0 @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['79', '92'])).
% 0.20/0.51  thf('94', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('95', plain,
% 0.20/0.51      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('96', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('97', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v2_struct_0 @ sk_A)
% 0.20/0.51          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_C)
% 0.20/0.51              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.51                 sk_C @ (u1_struct_0 @ X0)))
% 0.20/0.51          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.20/0.51          | (v2_struct_0 @ sk_B))),
% 0.20/0.51      inference('simplify', [status(thm)], ['42'])).
% 0.20/0.51  thf('98', plain,
% 0.20/0.51      (((v2_struct_0 @ sk_B)
% 0.20/0.51        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C)
% 0.20/0.51            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.51               sk_C @ (u1_struct_0 @ sk_E)))
% 0.20/0.51        | (v2_struct_0 @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['96', '97'])).
% 0.20/0.51  thf('99', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('100', plain,
% 0.20/0.51      (((v2_struct_0 @ sk_A)
% 0.20/0.51        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C)
% 0.20/0.51            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.51               sk_C @ (u1_struct_0 @ sk_E))))),
% 0.20/0.51      inference('clc', [status(thm)], ['98', '99'])).
% 0.20/0.51  thf('101', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('102', plain,
% 0.20/0.51      (((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C)
% 0.20/0.51         = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.20/0.51            (u1_struct_0 @ sk_E)))),
% 0.20/0.51      inference('clc', [status(thm)], ['100', '101'])).
% 0.20/0.51  thf('103', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('104', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v2_struct_0 @ sk_A)
% 0.20/0.51          | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0)
% 0.20/0.51              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.51                 sk_C @ (u1_struct_0 @ X0)))
% 0.20/0.51          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.20/0.51          | (v2_struct_0 @ sk_B))),
% 0.20/0.51      inference('demod', [status(thm)],
% 0.20/0.51                ['52', '53', '54', '55', '56', '57', '58'])).
% 0.20/0.51  thf('105', plain,
% 0.20/0.51      (((v2_struct_0 @ sk_B)
% 0.20/0.51        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 0.20/0.51            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.51               sk_C @ (u1_struct_0 @ sk_E)))
% 0.20/0.51        | (v2_struct_0 @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['103', '104'])).
% 0.20/0.51  thf('106', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('107', plain,
% 0.20/0.51      (((v2_struct_0 @ sk_A)
% 0.20/0.51        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 0.20/0.51            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.51               sk_C @ (u1_struct_0 @ sk_E))))),
% 0.20/0.51      inference('clc', [status(thm)], ['105', '106'])).
% 0.20/0.51  thf('108', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('109', plain,
% 0.20/0.51      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 0.20/0.52         = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.20/0.52            (u1_struct_0 @ sk_E)))),
% 0.20/0.52      inference('clc', [status(thm)], ['107', '108'])).
% 0.20/0.52  thf('110', plain,
% 0.20/0.52      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 0.20/0.52         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C))),
% 0.20/0.52      inference('sup+', [status(thm)], ['102', '109'])).
% 0.20/0.52  thf('111', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('112', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('113', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((v2_struct_0 @ sk_A)
% 0.20/0.52          | (v2_struct_0 @ sk_D)
% 0.20/0.52          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_E))
% 0.20/0.52          | (r1_tmap_1 @ sk_E @ sk_B @ 
% 0.20/0.52             (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ X0)
% 0.20/0.52          | ~ (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ X0)
% 0.20/0.52          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.52          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D))
% 0.20/0.52          | (v2_struct_0 @ sk_E)
% 0.20/0.52          | (v2_struct_0 @ sk_B))),
% 0.20/0.52      inference('demod', [status(thm)], ['93', '94', '95', '110', '111', '112'])).
% 0.20/0.52  thf('114', plain,
% 0.20/0.52      ((((v2_struct_0 @ sk_B)
% 0.20/0.52         | (v2_struct_0 @ sk_E)
% 0.20/0.52         | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_D))
% 0.20/0.52         | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_A))
% 0.20/0.52         | (r1_tmap_1 @ sk_E @ sk_B @ 
% 0.20/0.52            (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_G)
% 0.20/0.52         | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_E))
% 0.20/0.52         | (v2_struct_0 @ sk_D)
% 0.20/0.52         | (v2_struct_0 @ sk_A)))
% 0.20/0.52         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['78', '113'])).
% 0.20/0.52  thf('115', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_D))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('116', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['71', '72'])).
% 0.20/0.52  thf('117', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_E))),
% 0.20/0.52      inference('demod', [status(thm)], ['74', '75'])).
% 0.20/0.52  thf('118', plain,
% 0.20/0.52      ((((v2_struct_0 @ sk_B)
% 0.20/0.52         | (v2_struct_0 @ sk_E)
% 0.20/0.52         | (r1_tmap_1 @ sk_E @ sk_B @ 
% 0.20/0.52            (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_G)
% 0.20/0.52         | (v2_struct_0 @ sk_D)
% 0.20/0.52         | (v2_struct_0 @ sk_A)))
% 0.20/0.52         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F)))),
% 0.20/0.52      inference('demod', [status(thm)], ['114', '115', '116', '117'])).
% 0.20/0.52  thf('119', plain,
% 0.20/0.52      ((~ (r1_tmap_1 @ sk_E @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.20/0.52           sk_H)
% 0.20/0.52        | ~ (r1_tmap_1 @ sk_D @ sk_B @ 
% 0.20/0.52             (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_G)
% 0.20/0.52        | ~ (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('120', plain, (((sk_H) = (sk_G))),
% 0.20/0.52      inference('sup+', [status(thm)], ['3', '4'])).
% 0.20/0.52  thf('121', plain, (((sk_F) = (sk_G))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('122', plain,
% 0.20/0.52      ((~ (r1_tmap_1 @ sk_E @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.20/0.52           sk_G)
% 0.20/0.52        | ~ (r1_tmap_1 @ sk_D @ sk_B @ 
% 0.20/0.52             (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_G)
% 0.20/0.52        | ~ (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G))),
% 0.20/0.52      inference('demod', [status(thm)], ['119', '120', '121'])).
% 0.20/0.52  thf('123', plain,
% 0.20/0.52      ((((v2_struct_0 @ sk_A)
% 0.20/0.52         | (v2_struct_0 @ sk_D)
% 0.20/0.52         | (v2_struct_0 @ sk_E)
% 0.20/0.52         | (v2_struct_0 @ sk_B)
% 0.20/0.52         | ~ (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G)
% 0.20/0.52         | ~ (r1_tmap_1 @ sk_D @ sk_B @ 
% 0.20/0.52              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_G)))
% 0.20/0.52         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['118', '122'])).
% 0.20/0.52  thf('124', plain,
% 0.20/0.52      (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G))
% 0.20/0.52         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F)))),
% 0.20/0.52      inference('demod', [status(thm)], ['8', '9'])).
% 0.20/0.52  thf('125', plain,
% 0.20/0.52      ((((v2_struct_0 @ sk_A)
% 0.20/0.52         | (v2_struct_0 @ sk_D)
% 0.20/0.52         | (v2_struct_0 @ sk_E)
% 0.20/0.52         | (v2_struct_0 @ sk_B)
% 0.20/0.52         | ~ (r1_tmap_1 @ sk_D @ sk_B @ 
% 0.20/0.52              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_G)))
% 0.20/0.52         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F)))),
% 0.20/0.52      inference('demod', [status(thm)], ['123', '124'])).
% 0.20/0.52  thf('126', plain,
% 0.20/0.52      ((((v2_struct_0 @ sk_A)
% 0.20/0.52         | (v2_struct_0 @ sk_D)
% 0.20/0.52         | (v2_struct_0 @ sk_E)
% 0.20/0.52         | (v2_struct_0 @ sk_B)
% 0.20/0.52         | (v2_struct_0 @ sk_B)
% 0.20/0.52         | (v2_struct_0 @ sk_E)
% 0.20/0.52         | (v2_struct_0 @ sk_D)
% 0.20/0.52         | (v2_struct_0 @ sk_A)))
% 0.20/0.52         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['77', '125'])).
% 0.20/0.52  thf('127', plain,
% 0.20/0.52      ((((v2_struct_0 @ sk_B)
% 0.20/0.52         | (v2_struct_0 @ sk_E)
% 0.20/0.52         | (v2_struct_0 @ sk_D)
% 0.20/0.52         | (v2_struct_0 @ sk_A)))
% 0.20/0.52         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F)))),
% 0.20/0.52      inference('simplify', [status(thm)], ['126'])).
% 0.20/0.52  thf('128', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('129', plain,
% 0.20/0.52      ((((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_E) | (v2_struct_0 @ sk_B)))
% 0.20/0.52         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['127', '128'])).
% 0.20/0.52  thf('130', plain, (~ (v2_struct_0 @ sk_D)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('131', plain,
% 0.20/0.52      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_E)))
% 0.20/0.52         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F)))),
% 0.20/0.52      inference('clc', [status(thm)], ['129', '130'])).
% 0.20/0.52  thf('132', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('133', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_E)) <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F)))),
% 0.20/0.52      inference('clc', [status(thm)], ['131', '132'])).
% 0.20/0.52  thf('134', plain, (~ (v2_struct_0 @ sk_E)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('135', plain, (~ ((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F))),
% 0.20/0.52      inference('sup-', [status(thm)], ['133', '134'])).
% 0.20/0.52  thf('136', plain,
% 0.20/0.52      (((r1_tmap_1 @ sk_E @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.20/0.52         sk_H)) | 
% 0.20/0.52       ((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F))),
% 0.20/0.52      inference('split', [status(esa)], ['1'])).
% 0.20/0.52  thf('137', plain,
% 0.20/0.52      (((r1_tmap_1 @ sk_E @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.20/0.52         sk_H))),
% 0.20/0.52      inference('sat_resolution*', [status(thm)], ['135', '136'])).
% 0.20/0.52  thf('138', plain,
% 0.20/0.52      ((r1_tmap_1 @ sk_E @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.20/0.52        sk_G)),
% 0.20/0.52      inference('simpl_trail', [status(thm)], ['6', '137'])).
% 0.20/0.52  thf('139', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_C @ 
% 0.20/0.52        (k1_zfmisc_1 @ 
% 0.20/0.52         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('140', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('141', plain,
% 0.20/0.52      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i, 
% 0.20/0.52         X16 : $i]:
% 0.20/0.52         ((v2_struct_0 @ X9)
% 0.20/0.52          | ~ (v2_pre_topc @ X9)
% 0.20/0.52          | ~ (l1_pre_topc @ X9)
% 0.20/0.52          | (v2_struct_0 @ X10)
% 0.20/0.52          | ~ (m1_pre_topc @ X10 @ X11)
% 0.20/0.52          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X13))
% 0.20/0.52          | ~ (m1_subset_1 @ X14 @ 
% 0.20/0.52               (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)))
% 0.20/0.52          | ~ (r1_tmap_1 @ X13 @ X9 @ 
% 0.20/0.52               (k3_tmap_1 @ X11 @ X9 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X13 @ 
% 0.20/0.52                X15) @ 
% 0.20/0.52               X12)
% 0.20/0.52          | ~ (r1_tmap_1 @ X10 @ X9 @ 
% 0.20/0.52               (k3_tmap_1 @ X11 @ X9 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X10 @ 
% 0.20/0.52                X15) @ 
% 0.20/0.52               X16)
% 0.20/0.52          | (r1_tmap_1 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X9 @ X15 @ X14)
% 0.20/0.52          | ((X14) != (X16))
% 0.20/0.52          | ((X14) != (X12))
% 0.20/0.52          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X10))
% 0.20/0.52          | ~ (m1_subset_1 @ X15 @ 
% 0.20/0.52               (k1_zfmisc_1 @ 
% 0.20/0.52                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.20/0.52                 (u1_struct_0 @ X9))))
% 0.20/0.52          | ~ (v1_funct_2 @ X15 @ 
% 0.20/0.52               (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.20/0.52               (u1_struct_0 @ X9))
% 0.20/0.52          | ~ (v1_funct_1 @ X15)
% 0.20/0.52          | ~ (m1_pre_topc @ X13 @ X11)
% 0.20/0.52          | (v2_struct_0 @ X13)
% 0.20/0.52          | ~ (l1_pre_topc @ X11)
% 0.20/0.52          | ~ (v2_pre_topc @ X11)
% 0.20/0.52          | (v2_struct_0 @ X11))),
% 0.20/0.52      inference('cnf', [status(esa)], [t123_tmap_1])).
% 0.20/0.52  thf('142', plain,
% 0.20/0.52      (![X9 : $i, X10 : $i, X11 : $i, X13 : $i, X15 : $i, X16 : $i]:
% 0.20/0.52         ((v2_struct_0 @ X11)
% 0.20/0.52          | ~ (v2_pre_topc @ X11)
% 0.20/0.52          | ~ (l1_pre_topc @ X11)
% 0.20/0.52          | (v2_struct_0 @ X13)
% 0.20/0.52          | ~ (m1_pre_topc @ X13 @ X11)
% 0.20/0.52          | ~ (v1_funct_1 @ X15)
% 0.20/0.52          | ~ (v1_funct_2 @ X15 @ 
% 0.20/0.52               (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.20/0.52               (u1_struct_0 @ X9))
% 0.20/0.52          | ~ (m1_subset_1 @ X15 @ 
% 0.20/0.52               (k1_zfmisc_1 @ 
% 0.20/0.52                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.20/0.52                 (u1_struct_0 @ X9))))
% 0.20/0.52          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X10))
% 0.20/0.52          | (r1_tmap_1 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X9 @ X15 @ X16)
% 0.20/0.52          | ~ (r1_tmap_1 @ X10 @ X9 @ 
% 0.20/0.52               (k3_tmap_1 @ X11 @ X9 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X10 @ 
% 0.20/0.52                X15) @ 
% 0.20/0.52               X16)
% 0.20/0.52          | ~ (r1_tmap_1 @ X13 @ X9 @ 
% 0.20/0.52               (k3_tmap_1 @ X11 @ X9 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X13 @ 
% 0.20/0.52                X15) @ 
% 0.20/0.52               X16)
% 0.20/0.52          | ~ (m1_subset_1 @ X16 @ 
% 0.20/0.52               (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)))
% 0.20/0.52          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X13))
% 0.20/0.52          | ~ (m1_pre_topc @ X10 @ X11)
% 0.20/0.52          | (v2_struct_0 @ X10)
% 0.20/0.52          | ~ (l1_pre_topc @ X9)
% 0.20/0.52          | ~ (v2_pre_topc @ X9)
% 0.20/0.52          | (v2_struct_0 @ X9))),
% 0.20/0.52      inference('simplify', [status(thm)], ['141'])).
% 0.20/0.52  thf('143', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X1 @ 
% 0.20/0.52             (k1_zfmisc_1 @ 
% 0.20/0.52              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 0.20/0.52          | (v2_struct_0 @ X0)
% 0.20/0.52          | ~ (v2_pre_topc @ X0)
% 0.20/0.52          | ~ (l1_pre_topc @ X0)
% 0.20/0.52          | (v2_struct_0 @ sk_E)
% 0.20/0.52          | ~ (m1_pre_topc @ sk_E @ sk_A)
% 0.20/0.52          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 0.20/0.52          | ~ (m1_subset_1 @ X2 @ 
% 0.20/0.52               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))
% 0.20/0.52          | ~ (r1_tmap_1 @ sk_D @ X0 @ 
% 0.20/0.52               (k3_tmap_1 @ sk_A @ X0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ 
% 0.20/0.52                sk_D @ X1) @ 
% 0.20/0.52               X2)
% 0.20/0.52          | ~ (r1_tmap_1 @ sk_E @ X0 @ 
% 0.20/0.52               (k3_tmap_1 @ sk_A @ X0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ 
% 0.20/0.52                sk_E @ X1) @ 
% 0.20/0.52               X2)
% 0.20/0.52          | (r1_tmap_1 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ X0 @ X1 @ X2)
% 0.20/0.52          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_E))
% 0.20/0.52          | ~ (v1_funct_2 @ X1 @ 
% 0.20/0.52               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 0.20/0.52               (u1_struct_0 @ X0))
% 0.20/0.52          | ~ (v1_funct_1 @ X1)
% 0.20/0.52          | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.20/0.52          | (v2_struct_0 @ sk_D)
% 0.20/0.52          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.52          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.52          | (v2_struct_0 @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['140', '142'])).
% 0.20/0.52  thf('144', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('145', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('146', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('147', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('148', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('149', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('150', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('151', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('152', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('153', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X1 @ 
% 0.20/0.52             (k1_zfmisc_1 @ 
% 0.20/0.52              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 0.20/0.52          | (v2_struct_0 @ X0)
% 0.20/0.52          | ~ (v2_pre_topc @ X0)
% 0.20/0.52          | ~ (l1_pre_topc @ X0)
% 0.20/0.52          | (v2_struct_0 @ sk_E)
% 0.20/0.52          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 0.20/0.52          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_A))
% 0.20/0.52          | ~ (r1_tmap_1 @ sk_D @ X0 @ 
% 0.20/0.52               (k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_D @ X1) @ X2)
% 0.20/0.52          | ~ (r1_tmap_1 @ sk_E @ X0 @ 
% 0.20/0.52               (k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_E @ X1) @ X2)
% 0.20/0.52          | (r1_tmap_1 @ sk_A @ X0 @ X1 @ X2)
% 0.20/0.52          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_E))
% 0.20/0.52          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))
% 0.20/0.52          | ~ (v1_funct_1 @ X1)
% 0.20/0.52          | (v2_struct_0 @ sk_D)
% 0.20/0.52          | (v2_struct_0 @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)],
% 0.20/0.52                ['143', '144', '145', '146', '147', '148', '149', '150', 
% 0.20/0.52                 '151', '152'])).
% 0.20/0.52  thf('154', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((v2_struct_0 @ sk_A)
% 0.20/0.52          | (v2_struct_0 @ sk_D)
% 0.20/0.52          | ~ (v1_funct_1 @ sk_C)
% 0.20/0.52          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.20/0.52          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_E))
% 0.20/0.52          | (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ X0)
% 0.20/0.52          | ~ (r1_tmap_1 @ sk_E @ sk_B @ 
% 0.20/0.52               (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C) @ X0)
% 0.20/0.52          | ~ (r1_tmap_1 @ sk_D @ sk_B @ 
% 0.20/0.52               (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C) @ X0)
% 0.20/0.52          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.52          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D))
% 0.20/0.52          | (v2_struct_0 @ sk_E)
% 0.20/0.52          | ~ (l1_pre_topc @ sk_B)
% 0.20/0.52          | ~ (v2_pre_topc @ sk_B)
% 0.20/0.52          | (v2_struct_0 @ sk_B))),
% 0.20/0.52      inference('sup-', [status(thm)], ['139', '153'])).
% 0.20/0.52  thf('155', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('156', plain,
% 0.20/0.52      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('157', plain,
% 0.20/0.52      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 0.20/0.52         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C))),
% 0.20/0.52      inference('sup+', [status(thm)], ['102', '109'])).
% 0.20/0.52  thf('158', plain,
% 0.20/0.52      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.20/0.52         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C))),
% 0.20/0.52      inference('sup+', [status(thm)], ['48', '64'])).
% 0.20/0.52  thf('159', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('160', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('161', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((v2_struct_0 @ sk_A)
% 0.20/0.52          | (v2_struct_0 @ sk_D)
% 0.20/0.52          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_E))
% 0.20/0.52          | (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ X0)
% 0.20/0.52          | ~ (r1_tmap_1 @ sk_E @ sk_B @ 
% 0.20/0.52               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ X0)
% 0.20/0.52          | ~ (r1_tmap_1 @ sk_D @ sk_B @ 
% 0.20/0.52               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ X0)
% 0.20/0.52          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.52          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D))
% 0.20/0.52          | (v2_struct_0 @ sk_E)
% 0.20/0.52          | (v2_struct_0 @ sk_B))),
% 0.20/0.52      inference('demod', [status(thm)],
% 0.20/0.52                ['154', '155', '156', '157', '158', '159', '160'])).
% 0.20/0.52  thf('162', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_B)
% 0.20/0.52        | (v2_struct_0 @ sk_E)
% 0.20/0.52        | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_D))
% 0.20/0.52        | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_A))
% 0.20/0.52        | ~ (r1_tmap_1 @ sk_D @ sk_B @ 
% 0.20/0.52             (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_G)
% 0.20/0.52        | (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G)
% 0.20/0.52        | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_E))
% 0.20/0.52        | (v2_struct_0 @ sk_D)
% 0.20/0.52        | (v2_struct_0 @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['138', '161'])).
% 0.20/0.52  thf('163', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_D))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('164', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['71', '72'])).
% 0.20/0.52  thf('165', plain,
% 0.20/0.52      (((r1_tmap_1 @ sk_D @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.20/0.52         sk_G))
% 0.20/0.52         <= (((r1_tmap_1 @ sk_D @ sk_B @ 
% 0.20/0.52               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_G)))),
% 0.20/0.52      inference('split', [status(esa)], ['7'])).
% 0.20/0.52  thf('166', plain,
% 0.20/0.52      (((r1_tmap_1 @ sk_D @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.20/0.52         sk_G)
% 0.20/0.52        | (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('167', plain, (((sk_F) = (sk_G))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('168', plain,
% 0.20/0.52      (((r1_tmap_1 @ sk_D @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.20/0.52         sk_G)
% 0.20/0.52        | (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G))),
% 0.20/0.52      inference('demod', [status(thm)], ['166', '167'])).
% 0.20/0.52  thf('169', plain,
% 0.20/0.52      (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G))
% 0.20/0.52         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G)))),
% 0.20/0.52      inference('split', [status(esa)], ['168'])).
% 0.20/0.52  thf('170', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((v2_struct_0 @ sk_A)
% 0.20/0.52          | (v2_struct_0 @ sk_D)
% 0.20/0.52          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_E))
% 0.20/0.52          | (r1_tmap_1 @ sk_D @ sk_B @ 
% 0.20/0.52             (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ X0)
% 0.20/0.52          | ~ (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ X0)
% 0.20/0.52          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.52          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D))
% 0.20/0.52          | (v2_struct_0 @ sk_E)
% 0.20/0.52          | (v2_struct_0 @ sk_B))),
% 0.20/0.52      inference('demod', [status(thm)], ['25', '26', '27', '65', '66', '67'])).
% 0.20/0.52  thf('171', plain,
% 0.20/0.52      ((((v2_struct_0 @ sk_B)
% 0.20/0.52         | (v2_struct_0 @ sk_E)
% 0.20/0.52         | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_D))
% 0.20/0.52         | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_A))
% 0.20/0.52         | (r1_tmap_1 @ sk_D @ sk_B @ 
% 0.20/0.52            (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_G)
% 0.20/0.52         | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_E))
% 0.20/0.52         | (v2_struct_0 @ sk_D)
% 0.20/0.52         | (v2_struct_0 @ sk_A)))
% 0.20/0.52         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['169', '170'])).
% 0.20/0.52  thf('172', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_D))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('173', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['71', '72'])).
% 0.20/0.52  thf('174', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_E))),
% 0.20/0.52      inference('demod', [status(thm)], ['74', '75'])).
% 0.20/0.52  thf('175', plain,
% 0.20/0.52      ((((v2_struct_0 @ sk_B)
% 0.20/0.52         | (v2_struct_0 @ sk_E)
% 0.20/0.52         | (r1_tmap_1 @ sk_D @ sk_B @ 
% 0.20/0.52            (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_G)
% 0.20/0.52         | (v2_struct_0 @ sk_D)
% 0.20/0.52         | (v2_struct_0 @ sk_A)))
% 0.20/0.52         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G)))),
% 0.20/0.52      inference('demod', [status(thm)], ['171', '172', '173', '174'])).
% 0.20/0.52  thf('176', plain,
% 0.20/0.52      (((r1_tmap_1 @ sk_E @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.20/0.52         sk_G))
% 0.20/0.52         <= (((r1_tmap_1 @ sk_E @ sk_B @ 
% 0.20/0.52               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_H)))),
% 0.20/0.52      inference('demod', [status(thm)], ['2', '5'])).
% 0.20/0.52  thf('177', plain,
% 0.20/0.52      ((~ (r1_tmap_1 @ sk_E @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.20/0.52           sk_G)
% 0.20/0.52        | ~ (r1_tmap_1 @ sk_D @ sk_B @ 
% 0.20/0.52             (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_G)
% 0.20/0.52        | ~ (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G))),
% 0.20/0.52      inference('demod', [status(thm)], ['119', '120', '121'])).
% 0.20/0.52  thf('178', plain,
% 0.20/0.52      (((~ (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G)
% 0.20/0.52         | ~ (r1_tmap_1 @ sk_D @ sk_B @ 
% 0.20/0.52              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_G)))
% 0.20/0.52         <= (((r1_tmap_1 @ sk_E @ sk_B @ 
% 0.20/0.52               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_H)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['176', '177'])).
% 0.20/0.52  thf('179', plain,
% 0.20/0.52      ((((v2_struct_0 @ sk_A)
% 0.20/0.52         | (v2_struct_0 @ sk_D)
% 0.20/0.52         | (v2_struct_0 @ sk_E)
% 0.20/0.52         | (v2_struct_0 @ sk_B)
% 0.20/0.52         | ~ (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G)))
% 0.20/0.52         <= (((r1_tmap_1 @ sk_E @ sk_B @ 
% 0.20/0.52               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_H)) & 
% 0.20/0.52             ((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['175', '178'])).
% 0.20/0.52  thf('180', plain,
% 0.20/0.52      (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G))
% 0.20/0.52         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G)))),
% 0.20/0.52      inference('split', [status(esa)], ['168'])).
% 0.20/0.52  thf('181', plain,
% 0.20/0.52      ((((v2_struct_0 @ sk_A)
% 0.20/0.52         | (v2_struct_0 @ sk_D)
% 0.20/0.52         | (v2_struct_0 @ sk_E)
% 0.20/0.52         | (v2_struct_0 @ sk_B)))
% 0.20/0.52         <= (((r1_tmap_1 @ sk_E @ sk_B @ 
% 0.20/0.52               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_H)) & 
% 0.20/0.52             ((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G)))),
% 0.20/0.52      inference('demod', [status(thm)], ['179', '180'])).
% 0.20/0.52  thf('182', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('183', plain,
% 0.20/0.52      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_E) | (v2_struct_0 @ sk_D)))
% 0.20/0.52         <= (((r1_tmap_1 @ sk_E @ sk_B @ 
% 0.20/0.52               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_H)) & 
% 0.20/0.52             ((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['181', '182'])).
% 0.20/0.52  thf('184', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('185', plain,
% 0.20/0.52      ((((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_E)))
% 0.20/0.52         <= (((r1_tmap_1 @ sk_E @ sk_B @ 
% 0.20/0.52               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_H)) & 
% 0.20/0.52             ((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G)))),
% 0.20/0.52      inference('clc', [status(thm)], ['183', '184'])).
% 0.20/0.52  thf('186', plain, (~ (v2_struct_0 @ sk_D)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('187', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_E))
% 0.20/0.52         <= (((r1_tmap_1 @ sk_E @ sk_B @ 
% 0.20/0.52               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_H)) & 
% 0.20/0.52             ((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G)))),
% 0.20/0.52      inference('clc', [status(thm)], ['185', '186'])).
% 0.20/0.52  thf('188', plain, (~ (v2_struct_0 @ sk_E)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('189', plain,
% 0.20/0.52      (~ ((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G)) | 
% 0.20/0.52       ~
% 0.20/0.52       ((r1_tmap_1 @ sk_E @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.20/0.52         sk_H))),
% 0.20/0.52      inference('sup-', [status(thm)], ['187', '188'])).
% 0.20/0.52  thf('190', plain,
% 0.20/0.52      (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G))
% 0.20/0.52         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G)))),
% 0.20/0.52      inference('split', [status(esa)], ['168'])).
% 0.20/0.52  thf('191', plain,
% 0.20/0.52      ((~ (r1_tmap_1 @ sk_E @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.20/0.52           sk_H)
% 0.20/0.52        | ~ (r1_tmap_1 @ sk_D @ sk_B @ 
% 0.20/0.52             (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_G)
% 0.20/0.52        | ~ (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('192', plain,
% 0.20/0.52      ((~ (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F))
% 0.20/0.52         <= (~ ((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F)))),
% 0.20/0.52      inference('split', [status(esa)], ['191'])).
% 0.20/0.52  thf('193', plain, (((sk_F) = (sk_G))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('194', plain,
% 0.20/0.52      ((~ (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G))
% 0.20/0.52         <= (~ ((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F)))),
% 0.20/0.52      inference('demod', [status(thm)], ['192', '193'])).
% 0.20/0.52  thf('195', plain,
% 0.20/0.52      (~ ((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G)) | 
% 0.20/0.52       ((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F))),
% 0.20/0.52      inference('sup-', [status(thm)], ['190', '194'])).
% 0.20/0.52  thf('196', plain,
% 0.20/0.52      ((((v2_struct_0 @ sk_B)
% 0.20/0.52         | (v2_struct_0 @ sk_E)
% 0.20/0.52         | (r1_tmap_1 @ sk_E @ sk_B @ 
% 0.20/0.52            (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_G)
% 0.20/0.52         | (v2_struct_0 @ sk_D)
% 0.20/0.52         | (v2_struct_0 @ sk_A)))
% 0.20/0.52         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F)))),
% 0.20/0.52      inference('demod', [status(thm)], ['114', '115', '116', '117'])).
% 0.20/0.52  thf('197', plain,
% 0.20/0.52      ((~ (r1_tmap_1 @ sk_E @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.20/0.52           sk_H))
% 0.20/0.52         <= (~
% 0.20/0.52             ((r1_tmap_1 @ sk_E @ sk_B @ 
% 0.20/0.52               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_H)))),
% 0.20/0.52      inference('split', [status(esa)], ['191'])).
% 0.20/0.52  thf('198', plain, (((sk_H) = (sk_G))),
% 0.20/0.52      inference('sup+', [status(thm)], ['3', '4'])).
% 0.20/0.52  thf('199', plain,
% 0.20/0.52      ((~ (r1_tmap_1 @ sk_E @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.20/0.52           sk_G))
% 0.20/0.52         <= (~
% 0.20/0.52             ((r1_tmap_1 @ sk_E @ sk_B @ 
% 0.20/0.52               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_H)))),
% 0.20/0.52      inference('demod', [status(thm)], ['197', '198'])).
% 0.20/0.52  thf('200', plain,
% 0.20/0.52      ((((v2_struct_0 @ sk_A)
% 0.20/0.52         | (v2_struct_0 @ sk_D)
% 0.20/0.52         | (v2_struct_0 @ sk_E)
% 0.20/0.52         | (v2_struct_0 @ sk_B)))
% 0.20/0.52         <= (~
% 0.20/0.52             ((r1_tmap_1 @ sk_E @ sk_B @ 
% 0.20/0.52               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_H)) & 
% 0.20/0.52             ((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['196', '199'])).
% 0.20/0.52  thf('201', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('202', plain,
% 0.20/0.52      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_E) | (v2_struct_0 @ sk_D)))
% 0.20/0.52         <= (~
% 0.20/0.52             ((r1_tmap_1 @ sk_E @ sk_B @ 
% 0.20/0.52               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_H)) & 
% 0.20/0.52             ((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['200', '201'])).
% 0.20/0.52  thf('203', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('204', plain,
% 0.20/0.52      ((((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_E)))
% 0.20/0.52         <= (~
% 0.20/0.52             ((r1_tmap_1 @ sk_E @ sk_B @ 
% 0.20/0.52               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_H)) & 
% 0.20/0.52             ((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F)))),
% 0.20/0.52      inference('clc', [status(thm)], ['202', '203'])).
% 0.20/0.52  thf('205', plain, (~ (v2_struct_0 @ sk_D)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('206', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_E))
% 0.20/0.52         <= (~
% 0.20/0.52             ((r1_tmap_1 @ sk_E @ sk_B @ 
% 0.20/0.52               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_H)) & 
% 0.20/0.52             ((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F)))),
% 0.20/0.52      inference('clc', [status(thm)], ['204', '205'])).
% 0.20/0.52  thf('207', plain, (~ (v2_struct_0 @ sk_E)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('208', plain,
% 0.20/0.52      (((r1_tmap_1 @ sk_E @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.20/0.52         sk_H)) | 
% 0.20/0.52       ~ ((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F))),
% 0.20/0.52      inference('sup-', [status(thm)], ['206', '207'])).
% 0.20/0.52  thf('209', plain,
% 0.20/0.52      (((r1_tmap_1 @ sk_D @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.20/0.52         sk_G)) | 
% 0.20/0.52       ((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G))),
% 0.20/0.52      inference('split', [status(esa)], ['168'])).
% 0.20/0.52  thf('210', plain,
% 0.20/0.52      (((r1_tmap_1 @ sk_D @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.20/0.52         sk_G))),
% 0.20/0.52      inference('sat_resolution*', [status(thm)], ['189', '195', '208', '209'])).
% 0.20/0.52  thf('211', plain,
% 0.20/0.52      ((r1_tmap_1 @ sk_D @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.20/0.52        sk_G)),
% 0.20/0.52      inference('simpl_trail', [status(thm)], ['165', '210'])).
% 0.20/0.52  thf('212', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_E))),
% 0.20/0.52      inference('demod', [status(thm)], ['74', '75'])).
% 0.20/0.52  thf('213', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_B)
% 0.20/0.52        | (v2_struct_0 @ sk_E)
% 0.20/0.52        | (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G)
% 0.20/0.52        | (v2_struct_0 @ sk_D)
% 0.20/0.52        | (v2_struct_0 @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['162', '163', '164', '211', '212'])).
% 0.20/0.52  thf('214', plain,
% 0.20/0.52      (((r1_tmap_1 @ sk_D @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.20/0.52         sk_G))
% 0.20/0.52         <= (((r1_tmap_1 @ sk_D @ sk_B @ 
% 0.20/0.52               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_G)))),
% 0.20/0.52      inference('split', [status(esa)], ['7'])).
% 0.20/0.52  thf('215', plain,
% 0.20/0.52      (((~ (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G)
% 0.20/0.52         | ~ (r1_tmap_1 @ sk_D @ sk_B @ 
% 0.20/0.52              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_G)))
% 0.20/0.52         <= (((r1_tmap_1 @ sk_E @ sk_B @ 
% 0.20/0.52               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_H)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['176', '177'])).
% 0.20/0.52  thf('216', plain,
% 0.20/0.52      ((~ (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G))
% 0.20/0.52         <= (((r1_tmap_1 @ sk_D @ sk_B @ 
% 0.20/0.52               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_G)) & 
% 0.20/0.52             ((r1_tmap_1 @ sk_E @ sk_B @ 
% 0.20/0.52               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_H)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['214', '215'])).
% 0.20/0.52  thf('217', plain,
% 0.20/0.52      (((r1_tmap_1 @ sk_D @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.20/0.52         sk_G))),
% 0.20/0.52      inference('sat_resolution*', [status(thm)], ['189', '195', '208', '209'])).
% 0.20/0.52  thf('218', plain,
% 0.20/0.52      ((~ (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G))
% 0.20/0.52         <= (((r1_tmap_1 @ sk_E @ sk_B @ 
% 0.20/0.52               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_H)))),
% 0.20/0.52      inference('simpl_trail', [status(thm)], ['216', '217'])).
% 0.20/0.52  thf('219', plain,
% 0.20/0.52      (((r1_tmap_1 @ sk_E @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.20/0.52         sk_H))),
% 0.20/0.52      inference('sat_resolution*', [status(thm)], ['135', '136'])).
% 0.20/0.52  thf('220', plain, (~ (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G)),
% 0.20/0.52      inference('simpl_trail', [status(thm)], ['218', '219'])).
% 0.20/0.52  thf('221', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_A)
% 0.20/0.52        | (v2_struct_0 @ sk_D)
% 0.20/0.52        | (v2_struct_0 @ sk_E)
% 0.20/0.52        | (v2_struct_0 @ sk_B))),
% 0.20/0.52      inference('sup-', [status(thm)], ['213', '220'])).
% 0.20/0.52  thf('222', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('223', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_E) | (v2_struct_0 @ sk_D))),
% 0.20/0.52      inference('sup-', [status(thm)], ['221', '222'])).
% 0.20/0.52  thf('224', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('225', plain, (((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_E))),
% 0.20/0.52      inference('clc', [status(thm)], ['223', '224'])).
% 0.20/0.52  thf('226', plain, (~ (v2_struct_0 @ sk_D)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('227', plain, ((v2_struct_0 @ sk_E)),
% 0.20/0.52      inference('clc', [status(thm)], ['225', '226'])).
% 0.20/0.52  thf('228', plain, ($false), inference('demod', [status(thm)], ['0', '227'])).
% 0.20/0.52  
% 0.20/0.52  % SZS output end Refutation
% 0.20/0.52  
% 0.20/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
