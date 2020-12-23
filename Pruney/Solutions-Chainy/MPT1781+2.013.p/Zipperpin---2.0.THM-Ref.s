%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6809xz2uUt

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:43 EST 2020

% Result     : Theorem 1.13s
% Output     : Refutation 1.13s
% Verified   : 
% Statistics : Number of formulae       :  369 (7215 expanded)
%              Number of leaves         :   36 (2139 expanded)
%              Depth                    :   55
%              Number of atoms          : 6279 (186349 expanded)
%              Number of equality atoms :  135 (3285 expanded)
%              Maximal formula depth    :   23 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(k4_tmap_1_type,type,(
    k4_tmap_1: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t96_tmap_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )
             => ( ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( ( r2_hidden @ D @ ( u1_struct_0 @ B ) )
                     => ( D
                        = ( k1_funct_1 @ C @ D ) ) ) )
               => ( r2_funct_2 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k4_tmap_1 @ A @ B ) @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( m1_pre_topc @ B @ A ) )
           => ! [C: $i] :
                ( ( ( v1_funct_1 @ C )
                  & ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )
               => ( ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                     => ( ( r2_hidden @ D @ ( u1_struct_0 @ B ) )
                       => ( D
                          = ( k1_funct_1 @ C @ D ) ) ) )
                 => ( r2_funct_2 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k4_tmap_1 @ A @ B ) @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t96_tmap_1])).

thf('0',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tmap_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( l1_struct_0 @ A )
        & ( l1_struct_0 @ B )
        & ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) )
        & ( l1_struct_0 @ D ) )
     => ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) )
        & ( v1_funct_2 @ ( k2_tmap_1 @ A @ B @ C @ D ) @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
        & ( m1_subset_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X21 ) ) ) )
      | ~ ( v1_funct_2 @ X19 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X21 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( l1_struct_0 @ X21 )
      | ~ ( l1_struct_0 @ X20 )
      | ~ ( l1_struct_0 @ X22 )
      | ( v1_funct_1 @ ( k2_tmap_1 @ X20 @ X21 @ X19 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tmap_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('5',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_pre_topc @ X14 @ X15 )
      | ( l1_pre_topc @ X14 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('6',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['6','7'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('9',plain,(
    ! [X13: $i] :
      ( ( l1_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('10',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X13: $i] :
      ( ( l1_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('13',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','10','13','14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X21 ) ) ) )
      | ~ ( v1_funct_2 @ X19 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X21 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( l1_struct_0 @ X21 )
      | ~ ( l1_struct_0 @ X20 )
      | ~ ( l1_struct_0 @ X22 )
      | ( v1_funct_2 @ ( k2_tmap_1 @ X20 @ X21 @ X19 @ X22 ) @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tmap_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['8','9'])).

thf('21',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['11','12'])).

thf('22',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['19','20','21','22','23'])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('25',plain,(
    ! [X27: $i] :
      ( ( m1_pre_topc @ X27 @ X27 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('26',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_tmap_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_pre_topc @ B @ A ) )
     => ( ( v1_funct_1 @ ( k4_tmap_1 @ A @ B ) )
        & ( v1_funct_2 @ ( k4_tmap_1 @ A @ B ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ ( k4_tmap_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('27',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 )
      | ~ ( m1_pre_topc @ X24 @ X23 )
      | ( m1_subset_1 @ ( k4_tmap_1 @ X23 @ X24 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X23 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_tmap_1])).

thf('28',plain,
    ( ( m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t59_tmap_1,axiom,(
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
                  ( ( ( v1_funct_1 @ D )
                    & ( v1_funct_2 @ D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )
                 => ! [E: $i] :
                      ( ( ( v1_funct_1 @ E )
                        & ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) ) ) ) )
                     => ( ! [F: $i] :
                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) )
                           => ( ( r2_hidden @ F @ ( u1_struct_0 @ C ) )
                             => ( ( k3_funct_2 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ D @ F )
                                = ( k1_funct_1 @ E @ F ) ) ) )
                       => ( r2_funct_2 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ ( k2_tmap_1 @ B @ A @ D @ C ) @ E ) ) ) ) ) ) ) )).

thf('35',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( v2_struct_0 @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_2 @ X29 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X30 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X30 ) ) ) )
      | ( r2_hidden @ ( sk_F @ X31 @ X29 @ X32 @ X28 @ X30 ) @ ( u1_struct_0 @ X32 ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X30 ) @ ( k2_tmap_1 @ X28 @ X30 @ X29 @ X32 ) @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X30 ) ) ) )
      | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X30 ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( m1_pre_topc @ X32 @ X28 )
      | ( v2_struct_0 @ X32 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t59_tmap_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_F @ X1 @ sk_C @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['6','7'])).

thf('42',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('43',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ( v2_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('44',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v2_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_F @ X1 @ sk_C @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['36','37','38','39','40','41','47'])).

thf('49',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['33','48'])).

thf('50',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 )
      | ~ ( m1_pre_topc @ X24 @ X23 )
      | ( v1_funct_2 @ ( k4_tmap_1 @ X23 @ X24 ) @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_tmap_1])).

thf('52',plain,
    ( ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('58',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 )
      | ~ ( m1_pre_topc @ X24 @ X23 )
      | ( v1_funct_1 @ ( k4_tmap_1 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_tmap_1])).

thf('60',plain,
    ( ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['49','57','65'])).

thf('67',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( r2_hidden @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['25','67'])).

thf('69',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['6','7'])).

thf('70',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X21 ) ) ) )
      | ~ ( v1_funct_2 @ X19 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X21 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( l1_struct_0 @ X21 )
      | ~ ( l1_struct_0 @ X20 )
      | ~ ( l1_struct_0 @ X22 )
      | ( m1_subset_1 @ ( k2_tmap_1 @ X20 @ X21 @ X19 @ X22 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X21 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tmap_1])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['8','9'])).

thf('75',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['11','12'])).

thf('76',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['73','74','75','76','77'])).

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

thf('79',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) )
      | ~ ( v1_funct_2 @ X7 @ X8 @ X9 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_funct_2 @ X10 @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) )
      | ( X7 = X10 )
      | ~ ( r2_funct_2 @ X8 @ X9 @ X7 @ X10 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) @ X1 )
      | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 )
        = X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
      = ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['70','80'])).

thf('82',plain,(
    v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['63','64'])).

thf('83',plain,(
    v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('84',plain,(
    m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('85',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['8','9'])).

thf('86',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
      = ( k4_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['81','82','83','84','85'])).

thf('87',plain,
    ( ~ ( l1_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
      = ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['24','86'])).

thf('88',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['8','9'])).

thf('89',plain,
    ( ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
      = ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,
    ( ~ ( l1_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
      = ( k4_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','89'])).

thf('91',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['8','9'])).

thf('92',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
      = ( k4_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','10','13','14','15'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['19','20','21','22','23'])).

thf('95',plain,(
    ! [X27: $i] :
      ( ( m1_pre_topc @ X27 @ X27 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('96',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_F @ X1 @ sk_C @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['36','37','38','39','40','41','47'])).

thf('98',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ ( sk_F @ sk_C @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( m1_pre_topc @ sk_B @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ ( sk_F @ sk_C @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) @ sk_C )
    | ~ ( m1_pre_topc @ sk_B @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['98','99','100'])).

thf('102',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) @ sk_C )
    | ( r2_hidden @ ( sk_F @ sk_C @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ ( sk_F @ sk_C @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['95','102'])).

thf('104',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['6','7'])).

thf('105',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ ( sk_F @ sk_C @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) @ X1 )
      | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 )
        = X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('107',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_F @ sk_C @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
      = sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['8','9'])).

thf('112',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_F @ sk_C @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
      = sk_C ) ),
    inference(demod,[status(thm)],['107','108','109','110','111'])).

thf('113',plain,
    ( ~ ( l1_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
      = sk_C )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ ( sk_F @ sk_C @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['94','112'])).

thf('114',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['8','9'])).

thf('115',plain,
    ( ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
      = sk_C )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ ( sk_F @ sk_C @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,
    ( ~ ( l1_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_F @ sk_C @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
      = sk_C ) ),
    inference('sup-',[status(thm)],['93','115'])).

thf('117',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['8','9'])).

thf('118',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_F @ sk_C @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
      = sk_C ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','10','13','14','15'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['19','20','21','22','23'])).

thf('121',plain,(
    ! [X27: $i] :
      ( ( m1_pre_topc @ X27 @ X27 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','10','13','14','15'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['19','20','21','22','23'])).

thf('124',plain,(
    ! [X27: $i] :
      ( ( m1_pre_topc @ X27 @ X27 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('125',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( v2_struct_0 @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_2 @ X29 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X30 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X30 ) ) ) )
      | ( m1_subset_1 @ ( sk_F @ X31 @ X29 @ X32 @ X28 @ X30 ) @ ( u1_struct_0 @ X28 ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X30 ) @ ( k2_tmap_1 @ X28 @ X30 @ X29 @ X32 ) @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X30 ) ) ) )
      | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X30 ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( m1_pre_topc @ X32 @ X28 )
      | ( v2_struct_0 @ X32 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t59_tmap_1])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) @ X1 )
      | ( m1_subset_1 @ ( sk_F @ X1 @ sk_C @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['6','7'])).

thf('134',plain,(
    v2_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('135',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) @ X1 )
      | ( m1_subset_1 @ ( sk_F @ X1 @ sk_C @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['128','129','130','131','132','133','134'])).

thf('136',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_F @ sk_C @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( m1_pre_topc @ sk_B @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['125','135'])).

thf('137',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_F @ sk_C @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) @ sk_C )
    | ~ ( m1_pre_topc @ sk_B @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['136','137','138'])).

thf('140',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) @ sk_C )
    | ( m1_subset_1 @ ( sk_F @ sk_C @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['139'])).

thf('141',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_F @ sk_C @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['124','140'])).

thf('142',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['6','7'])).

thf('143',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_F @ sk_C @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['141','142'])).

thf('144',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) @ X1 )
      | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 )
        = X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('145',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_F @ sk_C @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
      = sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['8','9'])).

thf('150',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_F @ sk_C @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
      = sk_C ) ),
    inference(demod,[status(thm)],['145','146','147','148','149'])).

thf('151',plain,
    ( ~ ( l1_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
      = sk_C )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_F @ sk_C @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['123','150'])).

thf('152',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['8','9'])).

thf('153',plain,
    ( ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
      = sk_C )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_F @ sk_C @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['151','152'])).

thf('154',plain,
    ( ~ ( l1_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_F @ sk_C @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
      = sk_C ) ),
    inference('sup-',[status(thm)],['122','153'])).

thf('155',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['8','9'])).

thf('156',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_F @ sk_C @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
      = sk_C ) ),
    inference(demod,[status(thm)],['154','155'])).

thf('157',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k3_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ A ) )
     => ( ( k3_funct_2 @ A @ B @ C @ D )
        = ( k1_funct_1 @ C @ D ) ) ) )).

thf('158',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) )
      | ~ ( v1_funct_2 @ X3 @ X4 @ X5 )
      | ~ ( v1_funct_1 @ X3 )
      | ( v1_xboole_0 @ X4 )
      | ~ ( m1_subset_1 @ X6 @ X4 )
      | ( ( k3_funct_2 @ X4 @ X5 @ X3 @ X6 )
        = ( k1_funct_1 @ X3 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('159',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 )
        = ( k1_funct_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 )
        = ( k1_funct_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['159','160','161'])).

thf('163',plain,
    ( ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
      = sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( sk_F @ sk_C @ sk_C @ sk_B @ sk_B @ sk_A ) )
      = ( k1_funct_1 @ sk_C @ ( sk_F @ sk_C @ sk_C @ sk_B @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['156','162'])).

thf('164',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( v2_struct_0 @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_2 @ X29 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X30 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X30 ) ) ) )
      | ( ( k3_funct_2 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X30 ) @ X29 @ ( sk_F @ X31 @ X29 @ X32 @ X28 @ X30 ) )
       != ( k1_funct_1 @ X31 @ ( sk_F @ X31 @ X29 @ X32 @ X28 @ X30 ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X30 ) @ ( k2_tmap_1 @ X28 @ X30 @ X29 @ X32 ) @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X30 ) ) ) )
      | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X30 ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( m1_pre_topc @ X32 @ X28 )
      | ( v2_struct_0 @ X32 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t59_tmap_1])).

thf('165',plain,
    ( ( ( k1_funct_1 @ sk_C @ ( sk_F @ sk_C @ sk_C @ sk_B @ sk_B @ sk_A ) )
     != ( k1_funct_1 @ sk_C @ ( sk_F @ sk_C @ sk_C @ sk_B @ sk_B @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
      = sk_C )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) @ sk_C )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['6','7'])).

thf('175',plain,(
    v2_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('176',plain,
    ( ( ( k1_funct_1 @ sk_C @ ( sk_F @ sk_C @ sk_C @ sk_B @ sk_B @ sk_A ) )
     != ( k1_funct_1 @ sk_C @ ( sk_F @ sk_C @ sk_C @ sk_B @ sk_B @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
      = sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['165','166','167','168','169','170','171','172','173','174','175'])).

thf('177',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) @ sk_C )
    | ~ ( m1_pre_topc @ sk_B @ sk_B )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
      = sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['176'])).

thf('178',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
      = sk_C )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['121','177'])).

thf('179',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['6','7'])).

thf('180',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
      = sk_C )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['178','179'])).

thf('181',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) @ X1 )
      | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 )
        = X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('182',plain,
    ( ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
      = sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
      = sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['180','181'])).

thf('183',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['8','9'])).

thf('187',plain,
    ( ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
      = sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
      = sk_C ) ),
    inference(demod,[status(thm)],['182','183','184','185','186'])).

thf('188',plain,
    ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
      = sk_C ) ),
    inference(simplify,[status(thm)],['187'])).

thf('189',plain,
    ( ~ ( l1_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
      = sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['120','188'])).

thf('190',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['8','9'])).

thf('191',plain,
    ( ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
      = sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) ) ),
    inference(demod,[status(thm)],['189','190'])).

thf('192',plain,
    ( ~ ( l1_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
      = sk_C ) ),
    inference('sup-',[status(thm)],['119','191'])).

thf('193',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['8','9'])).

thf('194',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
      = sk_C ) ),
    inference(demod,[status(thm)],['192','193'])).

thf('195',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
      = sk_C ) ),
    inference(demod,[status(thm)],['192','193'])).

thf('196',plain,(
    ! [X27: $i] :
      ( ( m1_pre_topc @ X27 @ X27 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('197',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','10','13','14','15'])).

thf('199',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['19','20','21','22','23'])).

thf('200',plain,(
    ! [X27: $i] :
      ( ( m1_pre_topc @ X27 @ X27 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('201',plain,(
    m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('202',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) @ X1 )
      | ( m1_subset_1 @ ( sk_F @ X1 @ sk_C @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['128','129','130','131','132','133','134'])).

thf('203',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['201','202'])).

thf('204',plain,(
    v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('205',plain,(
    v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['63','64'])).

thf('206',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['203','204','205'])).

thf('207',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( m1_subset_1 @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['206'])).

thf('208',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['200','207'])).

thf('209',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['6','7'])).

thf('210',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['208','209'])).

thf('211',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) @ X1 )
      | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 )
        = X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('212',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
      = ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['210','211'])).

thf('213',plain,(
    v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['63','64'])).

thf('214',plain,(
    v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('215',plain,(
    m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('216',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['8','9'])).

thf('217',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
      = ( k4_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['212','213','214','215','216'])).

thf('218',plain,
    ( ~ ( l1_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
      = ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['199','217'])).

thf('219',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['8','9'])).

thf('220',plain,
    ( ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
      = ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['218','219'])).

thf('221',plain,
    ( ~ ( l1_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
      = ( k4_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['198','220'])).

thf('222',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['8','9'])).

thf('223',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
      = ( k4_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['221','222'])).

thf(t55_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) )
             => ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('224',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v2_struct_0 @ X16 )
      | ~ ( m1_pre_topc @ X16 @ X17 )
      | ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X17 ) )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X16 ) )
      | ~ ( l1_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t55_pre_topc])).

thf('225',plain,(
    ! [X0: $i] :
      ( ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
        = ( k4_tmap_1 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['223','224'])).

thf('226',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
        = ( k4_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['225'])).

thf('227',plain,
    ( ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
      = ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['197','226'])).

thf('228',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('229',plain,
    ( ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
      = ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['227','228'])).

thf('230',plain,
    ( ( m1_subset_1 @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
      = ( k4_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['229'])).

thf('231',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
      = ( k4_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('232',plain,(
    ! [X36: $i] :
      ( ~ ( r2_hidden @ X36 @ ( u1_struct_0 @ sk_B ) )
      | ( X36
        = ( k1_funct_1 @ sk_C @ X36 ) )
      | ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('233',plain,
    ( ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
      = ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A )
      = ( k1_funct_1 @ sk_C @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['231','232'])).

thf('234',plain,
    ( ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
      = ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A )
      = ( k1_funct_1 @ sk_C @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
      = ( k4_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['230','233'])).

thf('235',plain,
    ( ( ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A )
      = ( k1_funct_1 @ sk_C @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
      = ( k4_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['234'])).

thf('236',plain,
    ( ( m1_subset_1 @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
      = ( k4_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['229'])).

thf('237',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
      = ( k4_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf(t95_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r2_hidden @ C @ ( u1_struct_0 @ B ) )
               => ( ( k1_funct_1 @ ( k4_tmap_1 @ A @ B ) @ C )
                  = C ) ) ) ) ) )).

thf('238',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( v2_struct_0 @ X33 )
      | ~ ( m1_pre_topc @ X33 @ X34 )
      | ~ ( r2_hidden @ X35 @ ( u1_struct_0 @ X33 ) )
      | ( ( k1_funct_1 @ ( k4_tmap_1 @ X34 @ X33 ) @ X35 )
        = X35 )
      | ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ X34 ) )
      | ~ ( l1_pre_topc @ X34 )
      | ~ ( v2_pre_topc @ X34 )
      | ( v2_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t95_tmap_1])).

thf('239',plain,(
    ! [X0: $i] :
      ( ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
        = ( k4_tmap_1 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ( ( k1_funct_1 @ ( k4_tmap_1 @ X0 @ sk_B ) @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) )
        = ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['237','238'])).

thf('240',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( ( k1_funct_1 @ ( k4_tmap_1 @ X0 @ sk_B ) @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) )
        = ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
        = ( k4_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['239'])).

thf('241',plain,
    ( ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
      = ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
      = ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) )
      = ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['236','240'])).

thf('242',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('243',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('244',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('245',plain,
    ( ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
      = ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
      = ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( ( k1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) )
      = ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['241','242','243','244'])).

thf('246',plain,
    ( ( ( k1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) )
      = ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
      = ( k4_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['245'])).

thf('247',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
      = ( k4_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['221','222'])).

thf('248',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 )
        = ( k1_funct_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['159','160','161'])).

thf('249',plain,
    ( ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
      = ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) )
      = ( k1_funct_1 @ sk_C @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['247','248'])).

thf('250',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( v2_struct_0 @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_2 @ X29 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X30 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X30 ) ) ) )
      | ( ( k3_funct_2 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X30 ) @ X29 @ ( sk_F @ X31 @ X29 @ X32 @ X28 @ X30 ) )
       != ( k1_funct_1 @ X31 @ ( sk_F @ X31 @ X29 @ X32 @ X28 @ X30 ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X30 ) @ ( k2_tmap_1 @ X28 @ X30 @ X29 @ X32 ) @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X30 ) ) ) )
      | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X30 ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( m1_pre_topc @ X32 @ X28 )
      | ( v2_struct_0 @ X32 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t59_tmap_1])).

thf('251',plain,
    ( ( ( k1_funct_1 @ sk_C @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) )
     != ( k1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
      = ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_B )
    | ~ ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['249','250'])).

thf('252',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('253',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('254',plain,(
    v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['63','64'])).

thf('255',plain,(
    v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('256',plain,(
    m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('257',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('258',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('259',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('260',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['6','7'])).

thf('261',plain,(
    v2_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('262',plain,
    ( ( ( k1_funct_1 @ sk_C @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) )
     != ( k1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
      = ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['251','252','253','254','255','256','257','258','259','260','261'])).

thf('263',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_B )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
      = ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k1_funct_1 @ sk_C @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) )
     != ( k1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['262'])).

thf('264',plain,
    ( ( ( k1_funct_1 @ sk_C @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) )
     != ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
      = ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
      = ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) @ ( k4_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['246','263'])).

thf('265',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
      = ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( ( k1_funct_1 @ sk_C @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) )
     != ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['264'])).

thf('266',plain,
    ( ( ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A )
     != ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
      = ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
      = ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) @ ( k4_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['235','265'])).

thf('267',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
      = ( k4_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['266'])).

thf('268',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
      = ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) @ ( k4_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['196','267'])).

thf('269',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['6','7'])).

thf('270',plain,
    ( ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
      = ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) @ ( k4_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['268','269'])).

thf('271',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
      = ( k4_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['195','270'])).

thf('272',plain,
    ( ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
      = ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['271'])).

thf('273',plain,(
    m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('274',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','10','13','14','15'])).

thf('275',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['19','20','21','22','23'])).

thf('276',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
      = sk_C ) ),
    inference(demod,[status(thm)],['192','193'])).

thf('277',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) @ X1 )
      | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 )
        = X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('278',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
        = X0 )
      | ~ ( l1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['276','277'])).

thf('279',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['8','9'])).

thf('280',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
        = X0 ) ) ),
    inference(demod,[status(thm)],['278','279'])).

thf('281',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ sk_B )
      | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['275','280'])).

thf('282',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['8','9'])).

thf('283',plain,(
    ! [X0: $i] :
      ( ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['281','282'])).

thf('284',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ sk_B )
      | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['274','283'])).

thf('285',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['8','9'])).

thf('286',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
        = X0 ) ) ),
    inference(demod,[status(thm)],['284','285'])).

thf('287',plain,
    ( ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
      = ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['273','286'])).

thf('288',plain,(
    v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('289',plain,(
    v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['63','64'])).

thf('290',plain,
    ( ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
      = ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['287','288','289'])).

thf('291',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
      = ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
      = ( k4_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['272','290'])).

thf('292',plain,
    ( ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
      = ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['291'])).

thf('293',plain,
    ( ( sk_C
      = ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['194','292'])).

thf('294',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( sk_C
      = ( k4_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['293'])).

thf('295',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('296',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['294','295'])).

thf('297',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('298',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) )
      | ~ ( v1_funct_2 @ X7 @ X8 @ X9 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_funct_2 @ X10 @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) )
      | ( r2_funct_2 @ X8 @ X9 @ X7 @ X10 )
      | ( X7 != X10 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('299',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r2_funct_2 @ X8 @ X9 @ X10 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_funct_2 @ X10 @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(simplify,[status(thm)],['298'])).

thf('300',plain,
    ( ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_C ) ),
    inference('sup-',[status(thm)],['297','299'])).

thf('301',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('302',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('303',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['300','301','302'])).

thf('304',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['296','303'])).

thf('305',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('306',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['304','305'])).

thf('307',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('308',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['306','307'])).

thf('309',plain,(
    ! [X27: $i] :
      ( ( m1_pre_topc @ X27 @ X27 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('310',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_pre_topc @ X25 @ X26 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X25 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('311',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['309','310'])).

thf('312',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['311'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('313',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('314',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['312','313'])).

thf('315',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_pre_topc @ sk_B ) ) ),
    inference('sup-',[status(thm)],['308','314'])).

thf('316',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['6','7'])).

thf('317',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['315','316'])).

thf('318',plain,
    ( ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
      = sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['118','317'])).

thf('319',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('320',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
      = sk_C ) ),
    inference(clc,[status(thm)],['318','319'])).

thf('321',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('322',plain,
    ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
    = sk_C ),
    inference(clc,[status(thm)],['320','321'])).

thf('323',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( sk_C
      = ( k4_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['92','322'])).

thf('324',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['315','316'])).

thf('325',plain,
    ( ( sk_C
      = ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['323','324'])).

thf('326',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('327',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_C
      = ( k4_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['325','326'])).

thf('328',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('329',plain,
    ( sk_C
    = ( k4_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['327','328'])).

thf('330',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['300','301','302'])).

thf('331',plain,(
    $false ),
    inference(demod,[status(thm)],['0','329','330'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6809xz2uUt
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:54:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.13/1.36  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.13/1.36  % Solved by: fo/fo7.sh
% 1.13/1.36  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.13/1.36  % done 1072 iterations in 0.898s
% 1.13/1.36  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.13/1.36  % SZS output start Refutation
% 1.13/1.36  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 1.13/1.36  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.13/1.36  thf(sk_F_type, type, sk_F: $i > $i > $i > $i > $i > $i).
% 1.13/1.36  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 1.13/1.36  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.13/1.36  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.13/1.36  thf(sk_A_type, type, sk_A: $i).
% 1.13/1.36  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.13/1.36  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 1.13/1.36  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.13/1.36  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.13/1.36  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.13/1.36  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.13/1.36  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 1.13/1.36  thf(k4_tmap_1_type, type, k4_tmap_1: $i > $i > $i).
% 1.13/1.36  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.13/1.36  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.13/1.36  thf(sk_B_type, type, sk_B: $i).
% 1.13/1.36  thf(sk_C_type, type, sk_C: $i).
% 1.13/1.36  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 1.13/1.36  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.13/1.36  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.13/1.36  thf(t96_tmap_1, conjecture,
% 1.13/1.36    (![A:$i]:
% 1.13/1.36     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.13/1.36       ( ![B:$i]:
% 1.13/1.36         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 1.13/1.36           ( ![C:$i]:
% 1.13/1.36             ( ( ( v1_funct_1 @ C ) & 
% 1.13/1.36                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 1.13/1.36                 ( m1_subset_1 @
% 1.13/1.36                   C @ 
% 1.13/1.36                   ( k1_zfmisc_1 @
% 1.13/1.36                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 1.13/1.36               ( ( ![D:$i]:
% 1.13/1.36                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 1.13/1.36                     ( ( r2_hidden @ D @ ( u1_struct_0 @ B ) ) =>
% 1.13/1.36                       ( ( D ) = ( k1_funct_1 @ C @ D ) ) ) ) ) =>
% 1.13/1.36                 ( r2_funct_2 @
% 1.13/1.36                   ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.13/1.36                   ( k4_tmap_1 @ A @ B ) @ C ) ) ) ) ) ) ))).
% 1.13/1.36  thf(zf_stmt_0, negated_conjecture,
% 1.13/1.36    (~( ![A:$i]:
% 1.13/1.36        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.13/1.36            ( l1_pre_topc @ A ) ) =>
% 1.13/1.36          ( ![B:$i]:
% 1.13/1.36            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 1.13/1.36              ( ![C:$i]:
% 1.13/1.36                ( ( ( v1_funct_1 @ C ) & 
% 1.13/1.36                    ( v1_funct_2 @
% 1.13/1.36                      C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 1.13/1.36                    ( m1_subset_1 @
% 1.13/1.36                      C @ 
% 1.13/1.36                      ( k1_zfmisc_1 @
% 1.13/1.36                        ( k2_zfmisc_1 @
% 1.13/1.36                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 1.13/1.36                  ( ( ![D:$i]:
% 1.13/1.36                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 1.13/1.36                        ( ( r2_hidden @ D @ ( u1_struct_0 @ B ) ) =>
% 1.13/1.36                          ( ( D ) = ( k1_funct_1 @ C @ D ) ) ) ) ) =>
% 1.13/1.36                    ( r2_funct_2 @
% 1.13/1.36                      ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.13/1.36                      ( k4_tmap_1 @ A @ B ) @ C ) ) ) ) ) ) ) )),
% 1.13/1.36    inference('cnf.neg', [status(esa)], [t96_tmap_1])).
% 1.13/1.36  thf('0', plain,
% 1.13/1.36      (~ (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.13/1.36          (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)),
% 1.13/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.36  thf('1', plain,
% 1.13/1.36      ((m1_subset_1 @ sk_C @ 
% 1.13/1.36        (k1_zfmisc_1 @ 
% 1.13/1.36         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.13/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.36  thf(dt_k2_tmap_1, axiom,
% 1.13/1.36    (![A:$i,B:$i,C:$i,D:$i]:
% 1.13/1.36     ( ( ( l1_struct_0 @ A ) & ( l1_struct_0 @ B ) & ( v1_funct_1 @ C ) & 
% 1.13/1.36         ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.13/1.36         ( m1_subset_1 @
% 1.13/1.36           C @ 
% 1.13/1.36           ( k1_zfmisc_1 @
% 1.13/1.36             ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 1.13/1.36         ( l1_struct_0 @ D ) ) =>
% 1.13/1.36       ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) ) & 
% 1.13/1.36         ( v1_funct_2 @
% 1.13/1.36           ( k2_tmap_1 @ A @ B @ C @ D ) @ ( u1_struct_0 @ D ) @ 
% 1.13/1.36           ( u1_struct_0 @ B ) ) & 
% 1.13/1.36         ( m1_subset_1 @
% 1.13/1.36           ( k2_tmap_1 @ A @ B @ C @ D ) @ 
% 1.13/1.36           ( k1_zfmisc_1 @
% 1.13/1.36             ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 1.13/1.36  thf('2', plain,
% 1.13/1.36      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 1.13/1.36         (~ (m1_subset_1 @ X19 @ 
% 1.13/1.36             (k1_zfmisc_1 @ 
% 1.13/1.36              (k2_zfmisc_1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X21))))
% 1.13/1.36          | ~ (v1_funct_2 @ X19 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X21))
% 1.13/1.36          | ~ (v1_funct_1 @ X19)
% 1.13/1.36          | ~ (l1_struct_0 @ X21)
% 1.13/1.36          | ~ (l1_struct_0 @ X20)
% 1.13/1.36          | ~ (l1_struct_0 @ X22)
% 1.13/1.36          | (v1_funct_1 @ (k2_tmap_1 @ X20 @ X21 @ X19 @ X22)))),
% 1.13/1.36      inference('cnf', [status(esa)], [dt_k2_tmap_1])).
% 1.13/1.36  thf('3', plain,
% 1.13/1.36      (![X0 : $i]:
% 1.13/1.36         ((v1_funct_1 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0))
% 1.13/1.36          | ~ (l1_struct_0 @ X0)
% 1.13/1.36          | ~ (l1_struct_0 @ sk_B)
% 1.13/1.36          | ~ (l1_struct_0 @ sk_A)
% 1.13/1.36          | ~ (v1_funct_1 @ sk_C)
% 1.13/1.36          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 1.13/1.36      inference('sup-', [status(thm)], ['1', '2'])).
% 1.13/1.36  thf('4', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.13/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.36  thf(dt_m1_pre_topc, axiom,
% 1.13/1.36    (![A:$i]:
% 1.13/1.36     ( ( l1_pre_topc @ A ) =>
% 1.13/1.36       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 1.13/1.36  thf('5', plain,
% 1.13/1.36      (![X14 : $i, X15 : $i]:
% 1.13/1.36         (~ (m1_pre_topc @ X14 @ X15)
% 1.13/1.36          | (l1_pre_topc @ X14)
% 1.13/1.36          | ~ (l1_pre_topc @ X15))),
% 1.13/1.36      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 1.13/1.36  thf('6', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 1.13/1.36      inference('sup-', [status(thm)], ['4', '5'])).
% 1.13/1.36  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 1.13/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.36  thf('8', plain, ((l1_pre_topc @ sk_B)),
% 1.13/1.36      inference('demod', [status(thm)], ['6', '7'])).
% 1.13/1.36  thf(dt_l1_pre_topc, axiom,
% 1.13/1.36    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 1.13/1.36  thf('9', plain, (![X13 : $i]: ((l1_struct_0 @ X13) | ~ (l1_pre_topc @ X13))),
% 1.13/1.36      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.13/1.36  thf('10', plain, ((l1_struct_0 @ sk_B)),
% 1.13/1.36      inference('sup-', [status(thm)], ['8', '9'])).
% 1.13/1.36  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 1.13/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.36  thf('12', plain,
% 1.13/1.36      (![X13 : $i]: ((l1_struct_0 @ X13) | ~ (l1_pre_topc @ X13))),
% 1.13/1.36      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.13/1.36  thf('13', plain, ((l1_struct_0 @ sk_A)),
% 1.13/1.36      inference('sup-', [status(thm)], ['11', '12'])).
% 1.13/1.36  thf('14', plain, ((v1_funct_1 @ sk_C)),
% 1.13/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.36  thf('15', plain,
% 1.13/1.36      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 1.13/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.36  thf('16', plain,
% 1.13/1.36      (![X0 : $i]:
% 1.13/1.36         ((v1_funct_1 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0))
% 1.13/1.36          | ~ (l1_struct_0 @ X0))),
% 1.13/1.36      inference('demod', [status(thm)], ['3', '10', '13', '14', '15'])).
% 1.13/1.36  thf('17', plain,
% 1.13/1.36      ((m1_subset_1 @ sk_C @ 
% 1.13/1.36        (k1_zfmisc_1 @ 
% 1.13/1.36         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.13/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.36  thf('18', plain,
% 1.13/1.36      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 1.13/1.36         (~ (m1_subset_1 @ X19 @ 
% 1.13/1.36             (k1_zfmisc_1 @ 
% 1.13/1.36              (k2_zfmisc_1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X21))))
% 1.13/1.36          | ~ (v1_funct_2 @ X19 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X21))
% 1.13/1.36          | ~ (v1_funct_1 @ X19)
% 1.13/1.36          | ~ (l1_struct_0 @ X21)
% 1.13/1.36          | ~ (l1_struct_0 @ X20)
% 1.13/1.36          | ~ (l1_struct_0 @ X22)
% 1.13/1.36          | (v1_funct_2 @ (k2_tmap_1 @ X20 @ X21 @ X19 @ X22) @ 
% 1.13/1.36             (u1_struct_0 @ X22) @ (u1_struct_0 @ X21)))),
% 1.13/1.36      inference('cnf', [status(esa)], [dt_k2_tmap_1])).
% 1.13/1.36  thf('19', plain,
% 1.13/1.36      (![X0 : $i]:
% 1.13/1.36         ((v1_funct_2 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ 
% 1.13/1.36           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 1.13/1.36          | ~ (l1_struct_0 @ X0)
% 1.13/1.36          | ~ (l1_struct_0 @ sk_B)
% 1.13/1.36          | ~ (l1_struct_0 @ sk_A)
% 1.13/1.36          | ~ (v1_funct_1 @ sk_C)
% 1.13/1.36          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 1.13/1.36      inference('sup-', [status(thm)], ['17', '18'])).
% 1.13/1.36  thf('20', plain, ((l1_struct_0 @ sk_B)),
% 1.13/1.36      inference('sup-', [status(thm)], ['8', '9'])).
% 1.13/1.36  thf('21', plain, ((l1_struct_0 @ sk_A)),
% 1.13/1.36      inference('sup-', [status(thm)], ['11', '12'])).
% 1.13/1.36  thf('22', plain, ((v1_funct_1 @ sk_C)),
% 1.13/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.36  thf('23', plain,
% 1.13/1.36      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 1.13/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.36  thf('24', plain,
% 1.13/1.36      (![X0 : $i]:
% 1.13/1.36         ((v1_funct_2 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ 
% 1.13/1.36           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 1.13/1.36          | ~ (l1_struct_0 @ X0))),
% 1.13/1.36      inference('demod', [status(thm)], ['19', '20', '21', '22', '23'])).
% 1.13/1.36  thf(t2_tsep_1, axiom,
% 1.13/1.36    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 1.13/1.36  thf('25', plain,
% 1.13/1.36      (![X27 : $i]: ((m1_pre_topc @ X27 @ X27) | ~ (l1_pre_topc @ X27))),
% 1.13/1.36      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.13/1.36  thf('26', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.13/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.36  thf(dt_k4_tmap_1, axiom,
% 1.13/1.36    (![A:$i,B:$i]:
% 1.13/1.36     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.13/1.36         ( l1_pre_topc @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 1.13/1.36       ( ( v1_funct_1 @ ( k4_tmap_1 @ A @ B ) ) & 
% 1.13/1.36         ( v1_funct_2 @
% 1.13/1.36           ( k4_tmap_1 @ A @ B ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 1.13/1.36         ( m1_subset_1 @
% 1.13/1.36           ( k4_tmap_1 @ A @ B ) @ 
% 1.13/1.36           ( k1_zfmisc_1 @
% 1.13/1.36             ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 1.13/1.36  thf('27', plain,
% 1.13/1.36      (![X23 : $i, X24 : $i]:
% 1.13/1.36         (~ (l1_pre_topc @ X23)
% 1.13/1.36          | ~ (v2_pre_topc @ X23)
% 1.13/1.36          | (v2_struct_0 @ X23)
% 1.13/1.36          | ~ (m1_pre_topc @ X24 @ X23)
% 1.13/1.36          | (m1_subset_1 @ (k4_tmap_1 @ X23 @ X24) @ 
% 1.13/1.36             (k1_zfmisc_1 @ 
% 1.13/1.36              (k2_zfmisc_1 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X23)))))),
% 1.13/1.36      inference('cnf', [status(esa)], [dt_k4_tmap_1])).
% 1.13/1.36  thf('28', plain,
% 1.13/1.36      (((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 1.13/1.36         (k1_zfmisc_1 @ 
% 1.13/1.36          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 1.13/1.36        | (v2_struct_0 @ sk_A)
% 1.13/1.36        | ~ (v2_pre_topc @ sk_A)
% 1.13/1.36        | ~ (l1_pre_topc @ sk_A))),
% 1.13/1.36      inference('sup-', [status(thm)], ['26', '27'])).
% 1.13/1.36  thf('29', plain, ((v2_pre_topc @ sk_A)),
% 1.13/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.36  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 1.13/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.36  thf('31', plain,
% 1.13/1.36      (((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 1.13/1.36         (k1_zfmisc_1 @ 
% 1.13/1.36          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 1.13/1.36        | (v2_struct_0 @ sk_A))),
% 1.13/1.36      inference('demod', [status(thm)], ['28', '29', '30'])).
% 1.13/1.36  thf('32', plain, (~ (v2_struct_0 @ sk_A)),
% 1.13/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.36  thf('33', plain,
% 1.13/1.36      ((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 1.13/1.36        (k1_zfmisc_1 @ 
% 1.13/1.36         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.13/1.36      inference('clc', [status(thm)], ['31', '32'])).
% 1.13/1.36  thf('34', plain,
% 1.13/1.36      ((m1_subset_1 @ sk_C @ 
% 1.13/1.36        (k1_zfmisc_1 @ 
% 1.13/1.36         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.13/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.36  thf(t59_tmap_1, axiom,
% 1.13/1.36    (![A:$i]:
% 1.13/1.36     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.13/1.36       ( ![B:$i]:
% 1.13/1.36         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.13/1.36             ( l1_pre_topc @ B ) ) =>
% 1.13/1.36           ( ![C:$i]:
% 1.13/1.36             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 1.13/1.36               ( ![D:$i]:
% 1.13/1.36                 ( ( ( v1_funct_1 @ D ) & 
% 1.13/1.36                     ( v1_funct_2 @
% 1.13/1.36                       D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 1.13/1.36                     ( m1_subset_1 @
% 1.13/1.36                       D @ 
% 1.13/1.36                       ( k1_zfmisc_1 @
% 1.13/1.36                         ( k2_zfmisc_1 @
% 1.13/1.36                           ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 1.13/1.36                   ( ![E:$i]:
% 1.13/1.36                     ( ( ( v1_funct_1 @ E ) & 
% 1.13/1.36                         ( v1_funct_2 @
% 1.13/1.36                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) ) & 
% 1.13/1.36                         ( m1_subset_1 @
% 1.13/1.36                           E @ 
% 1.13/1.36                           ( k1_zfmisc_1 @
% 1.13/1.36                             ( k2_zfmisc_1 @
% 1.13/1.36                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 1.13/1.36                       ( ( ![F:$i]:
% 1.13/1.36                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 1.13/1.36                             ( ( r2_hidden @ F @ ( u1_struct_0 @ C ) ) =>
% 1.13/1.36                               ( ( k3_funct_2 @
% 1.13/1.36                                   ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.13/1.36                                   D @ F ) =
% 1.13/1.36                                 ( k1_funct_1 @ E @ F ) ) ) ) ) =>
% 1.13/1.36                         ( r2_funct_2 @
% 1.13/1.36                           ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ 
% 1.13/1.36                           ( k2_tmap_1 @ B @ A @ D @ C ) @ E ) ) ) ) ) ) ) ) ) ) ))).
% 1.13/1.36  thf('35', plain,
% 1.13/1.36      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 1.13/1.36         ((v2_struct_0 @ X28)
% 1.13/1.36          | ~ (v2_pre_topc @ X28)
% 1.13/1.36          | ~ (l1_pre_topc @ X28)
% 1.13/1.36          | ~ (v1_funct_1 @ X29)
% 1.13/1.36          | ~ (v1_funct_2 @ X29 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X30))
% 1.13/1.36          | ~ (m1_subset_1 @ X29 @ 
% 1.13/1.36               (k1_zfmisc_1 @ 
% 1.13/1.36                (k2_zfmisc_1 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X30))))
% 1.13/1.36          | (r2_hidden @ (sk_F @ X31 @ X29 @ X32 @ X28 @ X30) @ 
% 1.13/1.36             (u1_struct_0 @ X32))
% 1.13/1.36          | (r2_funct_2 @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X30) @ 
% 1.13/1.36             (k2_tmap_1 @ X28 @ X30 @ X29 @ X32) @ X31)
% 1.13/1.36          | ~ (m1_subset_1 @ X31 @ 
% 1.13/1.36               (k1_zfmisc_1 @ 
% 1.13/1.36                (k2_zfmisc_1 @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X30))))
% 1.13/1.36          | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X30))
% 1.13/1.36          | ~ (v1_funct_1 @ X31)
% 1.13/1.36          | ~ (m1_pre_topc @ X32 @ X28)
% 1.13/1.36          | (v2_struct_0 @ X32)
% 1.13/1.36          | ~ (l1_pre_topc @ X30)
% 1.13/1.36          | ~ (v2_pre_topc @ X30)
% 1.13/1.36          | (v2_struct_0 @ X30))),
% 1.13/1.36      inference('cnf', [status(esa)], [t59_tmap_1])).
% 1.13/1.36  thf('36', plain,
% 1.13/1.36      (![X0 : $i, X1 : $i]:
% 1.13/1.36         ((v2_struct_0 @ sk_A)
% 1.13/1.36          | ~ (v2_pre_topc @ sk_A)
% 1.13/1.36          | ~ (l1_pre_topc @ sk_A)
% 1.13/1.36          | (v2_struct_0 @ X0)
% 1.13/1.36          | ~ (m1_pre_topc @ X0 @ sk_B)
% 1.13/1.36          | ~ (v1_funct_1 @ X1)
% 1.13/1.36          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 1.13/1.36          | ~ (m1_subset_1 @ X1 @ 
% 1.13/1.36               (k1_zfmisc_1 @ 
% 1.13/1.36                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 1.13/1.36          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 1.13/1.36             (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ X1)
% 1.13/1.36          | (r2_hidden @ (sk_F @ X1 @ sk_C @ X0 @ sk_B @ sk_A) @ 
% 1.13/1.36             (u1_struct_0 @ X0))
% 1.13/1.36          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.13/1.36          | ~ (v1_funct_1 @ sk_C)
% 1.13/1.36          | ~ (l1_pre_topc @ sk_B)
% 1.13/1.36          | ~ (v2_pre_topc @ sk_B)
% 1.13/1.36          | (v2_struct_0 @ sk_B))),
% 1.13/1.36      inference('sup-', [status(thm)], ['34', '35'])).
% 1.13/1.36  thf('37', plain, ((v2_pre_topc @ sk_A)),
% 1.13/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.36  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 1.13/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.36  thf('39', plain,
% 1.13/1.36      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 1.13/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.36  thf('40', plain, ((v1_funct_1 @ sk_C)),
% 1.13/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.36  thf('41', plain, ((l1_pre_topc @ sk_B)),
% 1.13/1.36      inference('demod', [status(thm)], ['6', '7'])).
% 1.13/1.36  thf('42', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.13/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.36  thf(cc1_pre_topc, axiom,
% 1.13/1.36    (![A:$i]:
% 1.13/1.36     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.13/1.36       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 1.13/1.36  thf('43', plain,
% 1.13/1.36      (![X11 : $i, X12 : $i]:
% 1.13/1.36         (~ (m1_pre_topc @ X11 @ X12)
% 1.13/1.36          | (v2_pre_topc @ X11)
% 1.13/1.36          | ~ (l1_pre_topc @ X12)
% 1.13/1.36          | ~ (v2_pre_topc @ X12))),
% 1.13/1.36      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 1.13/1.36  thf('44', plain,
% 1.13/1.36      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_B))),
% 1.13/1.36      inference('sup-', [status(thm)], ['42', '43'])).
% 1.13/1.36  thf('45', plain, ((v2_pre_topc @ sk_A)),
% 1.13/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.36  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 1.13/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.36  thf('47', plain, ((v2_pre_topc @ sk_B)),
% 1.13/1.36      inference('demod', [status(thm)], ['44', '45', '46'])).
% 1.13/1.36  thf('48', plain,
% 1.13/1.36      (![X0 : $i, X1 : $i]:
% 1.13/1.36         ((v2_struct_0 @ sk_A)
% 1.13/1.36          | (v2_struct_0 @ X0)
% 1.13/1.36          | ~ (m1_pre_topc @ X0 @ sk_B)
% 1.13/1.36          | ~ (v1_funct_1 @ X1)
% 1.13/1.36          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 1.13/1.36          | ~ (m1_subset_1 @ X1 @ 
% 1.13/1.36               (k1_zfmisc_1 @ 
% 1.13/1.36                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 1.13/1.36          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 1.13/1.36             (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ X1)
% 1.13/1.36          | (r2_hidden @ (sk_F @ X1 @ sk_C @ X0 @ sk_B @ sk_A) @ 
% 1.13/1.36             (u1_struct_0 @ X0))
% 1.13/1.36          | (v2_struct_0 @ sk_B))),
% 1.13/1.36      inference('demod', [status(thm)],
% 1.13/1.36                ['36', '37', '38', '39', '40', '41', '47'])).
% 1.13/1.36  thf('49', plain,
% 1.13/1.36      (((v2_struct_0 @ sk_B)
% 1.13/1.36        | (r2_hidden @ 
% 1.13/1.36           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 1.13/1.36           (u1_struct_0 @ sk_B))
% 1.13/1.36        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.13/1.36           (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) @ (k4_tmap_1 @ sk_A @ sk_B))
% 1.13/1.36        | ~ (v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 1.13/1.36             (u1_struct_0 @ sk_A))
% 1.13/1.36        | ~ (v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))
% 1.13/1.36        | ~ (m1_pre_topc @ sk_B @ sk_B)
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | (v2_struct_0 @ sk_A))),
% 1.13/1.36      inference('sup-', [status(thm)], ['33', '48'])).
% 1.13/1.36  thf('50', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.13/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.36  thf('51', plain,
% 1.13/1.36      (![X23 : $i, X24 : $i]:
% 1.13/1.36         (~ (l1_pre_topc @ X23)
% 1.13/1.36          | ~ (v2_pre_topc @ X23)
% 1.13/1.36          | (v2_struct_0 @ X23)
% 1.13/1.36          | ~ (m1_pre_topc @ X24 @ X23)
% 1.13/1.36          | (v1_funct_2 @ (k4_tmap_1 @ X23 @ X24) @ (u1_struct_0 @ X24) @ 
% 1.13/1.36             (u1_struct_0 @ X23)))),
% 1.13/1.36      inference('cnf', [status(esa)], [dt_k4_tmap_1])).
% 1.13/1.36  thf('52', plain,
% 1.13/1.36      (((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 1.13/1.36         (u1_struct_0 @ sk_A))
% 1.13/1.36        | (v2_struct_0 @ sk_A)
% 1.13/1.36        | ~ (v2_pre_topc @ sk_A)
% 1.13/1.36        | ~ (l1_pre_topc @ sk_A))),
% 1.13/1.36      inference('sup-', [status(thm)], ['50', '51'])).
% 1.13/1.36  thf('53', plain, ((v2_pre_topc @ sk_A)),
% 1.13/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.36  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 1.13/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.36  thf('55', plain,
% 1.13/1.36      (((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 1.13/1.36         (u1_struct_0 @ sk_A))
% 1.13/1.36        | (v2_struct_0 @ sk_A))),
% 1.13/1.36      inference('demod', [status(thm)], ['52', '53', '54'])).
% 1.13/1.36  thf('56', plain, (~ (v2_struct_0 @ sk_A)),
% 1.13/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.36  thf('57', plain,
% 1.13/1.36      ((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 1.13/1.36        (u1_struct_0 @ sk_A))),
% 1.13/1.36      inference('clc', [status(thm)], ['55', '56'])).
% 1.13/1.36  thf('58', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.13/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.36  thf('59', plain,
% 1.13/1.36      (![X23 : $i, X24 : $i]:
% 1.13/1.36         (~ (l1_pre_topc @ X23)
% 1.13/1.36          | ~ (v2_pre_topc @ X23)
% 1.13/1.36          | (v2_struct_0 @ X23)
% 1.13/1.36          | ~ (m1_pre_topc @ X24 @ X23)
% 1.13/1.36          | (v1_funct_1 @ (k4_tmap_1 @ X23 @ X24)))),
% 1.13/1.36      inference('cnf', [status(esa)], [dt_k4_tmap_1])).
% 1.13/1.36  thf('60', plain,
% 1.13/1.36      (((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))
% 1.13/1.36        | (v2_struct_0 @ sk_A)
% 1.13/1.36        | ~ (v2_pre_topc @ sk_A)
% 1.13/1.36        | ~ (l1_pre_topc @ sk_A))),
% 1.13/1.36      inference('sup-', [status(thm)], ['58', '59'])).
% 1.13/1.36  thf('61', plain, ((v2_pre_topc @ sk_A)),
% 1.13/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.36  thf('62', plain, ((l1_pre_topc @ sk_A)),
% 1.13/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.36  thf('63', plain,
% 1.13/1.36      (((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 1.13/1.36      inference('demod', [status(thm)], ['60', '61', '62'])).
% 1.13/1.36  thf('64', plain, (~ (v2_struct_0 @ sk_A)),
% 1.13/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.36  thf('65', plain, ((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))),
% 1.13/1.36      inference('clc', [status(thm)], ['63', '64'])).
% 1.13/1.36  thf('66', plain,
% 1.13/1.36      (((v2_struct_0 @ sk_B)
% 1.13/1.36        | (r2_hidden @ 
% 1.13/1.36           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 1.13/1.36           (u1_struct_0 @ sk_B))
% 1.13/1.36        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.13/1.36           (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) @ (k4_tmap_1 @ sk_A @ sk_B))
% 1.13/1.36        | ~ (m1_pre_topc @ sk_B @ sk_B)
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | (v2_struct_0 @ sk_A))),
% 1.13/1.36      inference('demod', [status(thm)], ['49', '57', '65'])).
% 1.13/1.36  thf('67', plain,
% 1.13/1.36      (((v2_struct_0 @ sk_A)
% 1.13/1.36        | ~ (m1_pre_topc @ sk_B @ sk_B)
% 1.13/1.36        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.13/1.36           (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) @ (k4_tmap_1 @ sk_A @ sk_B))
% 1.13/1.36        | (r2_hidden @ 
% 1.13/1.36           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 1.13/1.36           (u1_struct_0 @ sk_B))
% 1.13/1.36        | (v2_struct_0 @ sk_B))),
% 1.13/1.36      inference('simplify', [status(thm)], ['66'])).
% 1.13/1.36  thf('68', plain,
% 1.13/1.36      ((~ (l1_pre_topc @ sk_B)
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | (r2_hidden @ 
% 1.13/1.36           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 1.13/1.36           (u1_struct_0 @ sk_B))
% 1.13/1.36        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.13/1.36           (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) @ (k4_tmap_1 @ sk_A @ sk_B))
% 1.13/1.36        | (v2_struct_0 @ sk_A))),
% 1.13/1.36      inference('sup-', [status(thm)], ['25', '67'])).
% 1.13/1.36  thf('69', plain, ((l1_pre_topc @ sk_B)),
% 1.13/1.36      inference('demod', [status(thm)], ['6', '7'])).
% 1.13/1.36  thf('70', plain,
% 1.13/1.36      (((v2_struct_0 @ sk_B)
% 1.13/1.36        | (r2_hidden @ 
% 1.13/1.36           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 1.13/1.36           (u1_struct_0 @ sk_B))
% 1.13/1.36        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.13/1.36           (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) @ (k4_tmap_1 @ sk_A @ sk_B))
% 1.13/1.36        | (v2_struct_0 @ sk_A))),
% 1.13/1.36      inference('demod', [status(thm)], ['68', '69'])).
% 1.13/1.36  thf('71', plain,
% 1.13/1.36      ((m1_subset_1 @ sk_C @ 
% 1.13/1.36        (k1_zfmisc_1 @ 
% 1.13/1.36         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.13/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.36  thf('72', plain,
% 1.13/1.36      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 1.13/1.36         (~ (m1_subset_1 @ X19 @ 
% 1.13/1.36             (k1_zfmisc_1 @ 
% 1.13/1.36              (k2_zfmisc_1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X21))))
% 1.13/1.36          | ~ (v1_funct_2 @ X19 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X21))
% 1.13/1.36          | ~ (v1_funct_1 @ X19)
% 1.13/1.36          | ~ (l1_struct_0 @ X21)
% 1.13/1.36          | ~ (l1_struct_0 @ X20)
% 1.13/1.36          | ~ (l1_struct_0 @ X22)
% 1.13/1.36          | (m1_subset_1 @ (k2_tmap_1 @ X20 @ X21 @ X19 @ X22) @ 
% 1.13/1.36             (k1_zfmisc_1 @ 
% 1.13/1.36              (k2_zfmisc_1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X21)))))),
% 1.13/1.36      inference('cnf', [status(esa)], [dt_k2_tmap_1])).
% 1.13/1.36  thf('73', plain,
% 1.13/1.36      (![X0 : $i]:
% 1.13/1.36         ((m1_subset_1 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ 
% 1.13/1.36           (k1_zfmisc_1 @ 
% 1.13/1.36            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 1.13/1.36          | ~ (l1_struct_0 @ X0)
% 1.13/1.36          | ~ (l1_struct_0 @ sk_B)
% 1.13/1.36          | ~ (l1_struct_0 @ sk_A)
% 1.13/1.36          | ~ (v1_funct_1 @ sk_C)
% 1.13/1.36          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 1.13/1.36      inference('sup-', [status(thm)], ['71', '72'])).
% 1.13/1.36  thf('74', plain, ((l1_struct_0 @ sk_B)),
% 1.13/1.36      inference('sup-', [status(thm)], ['8', '9'])).
% 1.13/1.36  thf('75', plain, ((l1_struct_0 @ sk_A)),
% 1.13/1.36      inference('sup-', [status(thm)], ['11', '12'])).
% 1.13/1.36  thf('76', plain, ((v1_funct_1 @ sk_C)),
% 1.13/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.36  thf('77', plain,
% 1.13/1.36      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 1.13/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.36  thf('78', plain,
% 1.13/1.36      (![X0 : $i]:
% 1.13/1.36         ((m1_subset_1 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ 
% 1.13/1.36           (k1_zfmisc_1 @ 
% 1.13/1.36            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 1.13/1.36          | ~ (l1_struct_0 @ X0))),
% 1.13/1.36      inference('demod', [status(thm)], ['73', '74', '75', '76', '77'])).
% 1.13/1.36  thf(redefinition_r2_funct_2, axiom,
% 1.13/1.36    (![A:$i,B:$i,C:$i,D:$i]:
% 1.13/1.36     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.13/1.36         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.13/1.36         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.13/1.36         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.13/1.36       ( ( r2_funct_2 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.13/1.36  thf('79', plain,
% 1.13/1.36      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 1.13/1.36         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9)))
% 1.13/1.36          | ~ (v1_funct_2 @ X7 @ X8 @ X9)
% 1.13/1.36          | ~ (v1_funct_1 @ X7)
% 1.13/1.36          | ~ (v1_funct_1 @ X10)
% 1.13/1.36          | ~ (v1_funct_2 @ X10 @ X8 @ X9)
% 1.13/1.36          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9)))
% 1.13/1.36          | ((X7) = (X10))
% 1.13/1.36          | ~ (r2_funct_2 @ X8 @ X9 @ X7 @ X10))),
% 1.13/1.36      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 1.13/1.36  thf('80', plain,
% 1.13/1.36      (![X0 : $i, X1 : $i]:
% 1.13/1.36         (~ (l1_struct_0 @ X0)
% 1.13/1.36          | ~ (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 1.13/1.36               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ X1)
% 1.13/1.36          | ((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) = (X1))
% 1.13/1.36          | ~ (m1_subset_1 @ X1 @ 
% 1.13/1.36               (k1_zfmisc_1 @ 
% 1.13/1.36                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 1.13/1.36          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 1.13/1.36          | ~ (v1_funct_1 @ X1)
% 1.13/1.36          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0))
% 1.13/1.36          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ 
% 1.13/1.36               (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A)))),
% 1.13/1.36      inference('sup-', [status(thm)], ['78', '79'])).
% 1.13/1.36  thf('81', plain,
% 1.13/1.36      (((v2_struct_0 @ sk_A)
% 1.13/1.36        | (r2_hidden @ 
% 1.13/1.36           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 1.13/1.36           (u1_struct_0 @ sk_B))
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) @ 
% 1.13/1.36             (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.13/1.36        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 1.13/1.36        | ~ (v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))
% 1.13/1.36        | ~ (v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 1.13/1.36             (u1_struct_0 @ sk_A))
% 1.13/1.36        | ~ (m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 1.13/1.36             (k1_zfmisc_1 @ 
% 1.13/1.36              (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 1.13/1.36        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) = (k4_tmap_1 @ sk_A @ sk_B))
% 1.13/1.36        | ~ (l1_struct_0 @ sk_B))),
% 1.13/1.36      inference('sup-', [status(thm)], ['70', '80'])).
% 1.13/1.36  thf('82', plain, ((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))),
% 1.13/1.36      inference('clc', [status(thm)], ['63', '64'])).
% 1.13/1.36  thf('83', plain,
% 1.13/1.36      ((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 1.13/1.36        (u1_struct_0 @ sk_A))),
% 1.13/1.36      inference('clc', [status(thm)], ['55', '56'])).
% 1.13/1.36  thf('84', plain,
% 1.13/1.36      ((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 1.13/1.36        (k1_zfmisc_1 @ 
% 1.13/1.36         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.13/1.36      inference('clc', [status(thm)], ['31', '32'])).
% 1.13/1.36  thf('85', plain, ((l1_struct_0 @ sk_B)),
% 1.13/1.36      inference('sup-', [status(thm)], ['8', '9'])).
% 1.13/1.36  thf('86', plain,
% 1.13/1.36      (((v2_struct_0 @ sk_A)
% 1.13/1.36        | (r2_hidden @ 
% 1.13/1.36           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 1.13/1.36           (u1_struct_0 @ sk_B))
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) @ 
% 1.13/1.36             (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.13/1.36        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 1.13/1.36        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) = (k4_tmap_1 @ sk_A @ sk_B)))),
% 1.13/1.36      inference('demod', [status(thm)], ['81', '82', '83', '84', '85'])).
% 1.13/1.36  thf('87', plain,
% 1.13/1.36      ((~ (l1_struct_0 @ sk_B)
% 1.13/1.36        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) = (k4_tmap_1 @ sk_A @ sk_B))
% 1.13/1.36        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | (r2_hidden @ 
% 1.13/1.36           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 1.13/1.36           (u1_struct_0 @ sk_B))
% 1.13/1.36        | (v2_struct_0 @ sk_A))),
% 1.13/1.36      inference('sup-', [status(thm)], ['24', '86'])).
% 1.13/1.36  thf('88', plain, ((l1_struct_0 @ sk_B)),
% 1.13/1.36      inference('sup-', [status(thm)], ['8', '9'])).
% 1.13/1.36  thf('89', plain,
% 1.13/1.36      ((((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) = (k4_tmap_1 @ sk_A @ sk_B))
% 1.13/1.36        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | (r2_hidden @ 
% 1.13/1.36           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 1.13/1.36           (u1_struct_0 @ sk_B))
% 1.13/1.36        | (v2_struct_0 @ sk_A))),
% 1.13/1.36      inference('demod', [status(thm)], ['87', '88'])).
% 1.13/1.36  thf('90', plain,
% 1.13/1.36      ((~ (l1_struct_0 @ sk_B)
% 1.13/1.36        | (v2_struct_0 @ sk_A)
% 1.13/1.36        | (r2_hidden @ 
% 1.13/1.36           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 1.13/1.36           (u1_struct_0 @ sk_B))
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) = (k4_tmap_1 @ sk_A @ sk_B)))),
% 1.13/1.36      inference('sup-', [status(thm)], ['16', '89'])).
% 1.13/1.36  thf('91', plain, ((l1_struct_0 @ sk_B)),
% 1.13/1.36      inference('sup-', [status(thm)], ['8', '9'])).
% 1.13/1.36  thf('92', plain,
% 1.13/1.36      (((v2_struct_0 @ sk_A)
% 1.13/1.36        | (r2_hidden @ 
% 1.13/1.36           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 1.13/1.36           (u1_struct_0 @ sk_B))
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) = (k4_tmap_1 @ sk_A @ sk_B)))),
% 1.13/1.36      inference('demod', [status(thm)], ['90', '91'])).
% 1.13/1.36  thf('93', plain,
% 1.13/1.36      (![X0 : $i]:
% 1.13/1.36         ((v1_funct_1 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0))
% 1.13/1.36          | ~ (l1_struct_0 @ X0))),
% 1.13/1.36      inference('demod', [status(thm)], ['3', '10', '13', '14', '15'])).
% 1.13/1.36  thf('94', plain,
% 1.13/1.36      (![X0 : $i]:
% 1.13/1.36         ((v1_funct_2 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ 
% 1.13/1.36           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 1.13/1.36          | ~ (l1_struct_0 @ X0))),
% 1.13/1.36      inference('demod', [status(thm)], ['19', '20', '21', '22', '23'])).
% 1.13/1.36  thf('95', plain,
% 1.13/1.36      (![X27 : $i]: ((m1_pre_topc @ X27 @ X27) | ~ (l1_pre_topc @ X27))),
% 1.13/1.36      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.13/1.36  thf('96', plain,
% 1.13/1.36      ((m1_subset_1 @ sk_C @ 
% 1.13/1.36        (k1_zfmisc_1 @ 
% 1.13/1.36         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.13/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.36  thf('97', plain,
% 1.13/1.36      (![X0 : $i, X1 : $i]:
% 1.13/1.36         ((v2_struct_0 @ sk_A)
% 1.13/1.36          | (v2_struct_0 @ X0)
% 1.13/1.36          | ~ (m1_pre_topc @ X0 @ sk_B)
% 1.13/1.36          | ~ (v1_funct_1 @ X1)
% 1.13/1.36          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 1.13/1.36          | ~ (m1_subset_1 @ X1 @ 
% 1.13/1.36               (k1_zfmisc_1 @ 
% 1.13/1.36                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 1.13/1.36          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 1.13/1.36             (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ X1)
% 1.13/1.36          | (r2_hidden @ (sk_F @ X1 @ sk_C @ X0 @ sk_B @ sk_A) @ 
% 1.13/1.36             (u1_struct_0 @ X0))
% 1.13/1.36          | (v2_struct_0 @ sk_B))),
% 1.13/1.36      inference('demod', [status(thm)],
% 1.13/1.36                ['36', '37', '38', '39', '40', '41', '47'])).
% 1.13/1.36  thf('98', plain,
% 1.13/1.36      (((v2_struct_0 @ sk_B)
% 1.13/1.36        | (r2_hidden @ (sk_F @ sk_C @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 1.13/1.36           (u1_struct_0 @ sk_B))
% 1.13/1.36        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.13/1.36           (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) @ sk_C)
% 1.13/1.36        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.13/1.36        | ~ (v1_funct_1 @ sk_C)
% 1.13/1.36        | ~ (m1_pre_topc @ sk_B @ sk_B)
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | (v2_struct_0 @ sk_A))),
% 1.13/1.36      inference('sup-', [status(thm)], ['96', '97'])).
% 1.13/1.36  thf('99', plain,
% 1.13/1.36      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 1.13/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.36  thf('100', plain, ((v1_funct_1 @ sk_C)),
% 1.13/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.36  thf('101', plain,
% 1.13/1.36      (((v2_struct_0 @ sk_B)
% 1.13/1.36        | (r2_hidden @ (sk_F @ sk_C @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 1.13/1.36           (u1_struct_0 @ sk_B))
% 1.13/1.36        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.13/1.36           (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) @ sk_C)
% 1.13/1.36        | ~ (m1_pre_topc @ sk_B @ sk_B)
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | (v2_struct_0 @ sk_A))),
% 1.13/1.36      inference('demod', [status(thm)], ['98', '99', '100'])).
% 1.13/1.36  thf('102', plain,
% 1.13/1.36      (((v2_struct_0 @ sk_A)
% 1.13/1.36        | ~ (m1_pre_topc @ sk_B @ sk_B)
% 1.13/1.36        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.13/1.36           (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) @ sk_C)
% 1.13/1.36        | (r2_hidden @ (sk_F @ sk_C @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 1.13/1.36           (u1_struct_0 @ sk_B))
% 1.13/1.36        | (v2_struct_0 @ sk_B))),
% 1.13/1.36      inference('simplify', [status(thm)], ['101'])).
% 1.13/1.36  thf('103', plain,
% 1.13/1.36      ((~ (l1_pre_topc @ sk_B)
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | (r2_hidden @ (sk_F @ sk_C @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 1.13/1.36           (u1_struct_0 @ sk_B))
% 1.13/1.36        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.13/1.36           (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) @ sk_C)
% 1.13/1.36        | (v2_struct_0 @ sk_A))),
% 1.13/1.36      inference('sup-', [status(thm)], ['95', '102'])).
% 1.13/1.36  thf('104', plain, ((l1_pre_topc @ sk_B)),
% 1.13/1.36      inference('demod', [status(thm)], ['6', '7'])).
% 1.13/1.36  thf('105', plain,
% 1.13/1.36      (((v2_struct_0 @ sk_B)
% 1.13/1.36        | (r2_hidden @ (sk_F @ sk_C @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 1.13/1.36           (u1_struct_0 @ sk_B))
% 1.13/1.36        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.13/1.36           (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) @ sk_C)
% 1.13/1.36        | (v2_struct_0 @ sk_A))),
% 1.13/1.36      inference('demod', [status(thm)], ['103', '104'])).
% 1.13/1.36  thf('106', plain,
% 1.13/1.36      (![X0 : $i, X1 : $i]:
% 1.13/1.36         (~ (l1_struct_0 @ X0)
% 1.13/1.36          | ~ (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 1.13/1.36               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ X1)
% 1.13/1.36          | ((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) = (X1))
% 1.13/1.36          | ~ (m1_subset_1 @ X1 @ 
% 1.13/1.36               (k1_zfmisc_1 @ 
% 1.13/1.36                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 1.13/1.36          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 1.13/1.36          | ~ (v1_funct_1 @ X1)
% 1.13/1.36          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0))
% 1.13/1.36          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ 
% 1.13/1.36               (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A)))),
% 1.13/1.36      inference('sup-', [status(thm)], ['78', '79'])).
% 1.13/1.36  thf('107', plain,
% 1.13/1.36      (((v2_struct_0 @ sk_A)
% 1.13/1.36        | (r2_hidden @ (sk_F @ sk_C @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 1.13/1.36           (u1_struct_0 @ sk_B))
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) @ 
% 1.13/1.36             (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.13/1.36        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 1.13/1.36        | ~ (v1_funct_1 @ sk_C)
% 1.13/1.36        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.13/1.36        | ~ (m1_subset_1 @ sk_C @ 
% 1.13/1.36             (k1_zfmisc_1 @ 
% 1.13/1.36              (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 1.13/1.36        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) = (sk_C))
% 1.13/1.36        | ~ (l1_struct_0 @ sk_B))),
% 1.13/1.36      inference('sup-', [status(thm)], ['105', '106'])).
% 1.13/1.36  thf('108', plain, ((v1_funct_1 @ sk_C)),
% 1.13/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.36  thf('109', plain,
% 1.13/1.36      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 1.13/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.36  thf('110', plain,
% 1.13/1.36      ((m1_subset_1 @ sk_C @ 
% 1.13/1.36        (k1_zfmisc_1 @ 
% 1.13/1.36         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.13/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.36  thf('111', plain, ((l1_struct_0 @ sk_B)),
% 1.13/1.36      inference('sup-', [status(thm)], ['8', '9'])).
% 1.13/1.36  thf('112', plain,
% 1.13/1.36      (((v2_struct_0 @ sk_A)
% 1.13/1.36        | (r2_hidden @ (sk_F @ sk_C @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 1.13/1.36           (u1_struct_0 @ sk_B))
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) @ 
% 1.13/1.36             (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.13/1.36        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 1.13/1.36        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) = (sk_C)))),
% 1.13/1.36      inference('demod', [status(thm)], ['107', '108', '109', '110', '111'])).
% 1.13/1.36  thf('113', plain,
% 1.13/1.36      ((~ (l1_struct_0 @ sk_B)
% 1.13/1.36        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) = (sk_C))
% 1.13/1.36        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | (r2_hidden @ (sk_F @ sk_C @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 1.13/1.36           (u1_struct_0 @ sk_B))
% 1.13/1.36        | (v2_struct_0 @ sk_A))),
% 1.13/1.36      inference('sup-', [status(thm)], ['94', '112'])).
% 1.13/1.36  thf('114', plain, ((l1_struct_0 @ sk_B)),
% 1.13/1.36      inference('sup-', [status(thm)], ['8', '9'])).
% 1.13/1.36  thf('115', plain,
% 1.13/1.36      ((((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) = (sk_C))
% 1.13/1.36        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | (r2_hidden @ (sk_F @ sk_C @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 1.13/1.36           (u1_struct_0 @ sk_B))
% 1.13/1.36        | (v2_struct_0 @ sk_A))),
% 1.13/1.36      inference('demod', [status(thm)], ['113', '114'])).
% 1.13/1.36  thf('116', plain,
% 1.13/1.36      ((~ (l1_struct_0 @ sk_B)
% 1.13/1.36        | (v2_struct_0 @ sk_A)
% 1.13/1.36        | (r2_hidden @ (sk_F @ sk_C @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 1.13/1.36           (u1_struct_0 @ sk_B))
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) = (sk_C)))),
% 1.13/1.36      inference('sup-', [status(thm)], ['93', '115'])).
% 1.13/1.36  thf('117', plain, ((l1_struct_0 @ sk_B)),
% 1.13/1.36      inference('sup-', [status(thm)], ['8', '9'])).
% 1.13/1.36  thf('118', plain,
% 1.13/1.36      (((v2_struct_0 @ sk_A)
% 1.13/1.36        | (r2_hidden @ (sk_F @ sk_C @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 1.13/1.36           (u1_struct_0 @ sk_B))
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) = (sk_C)))),
% 1.13/1.36      inference('demod', [status(thm)], ['116', '117'])).
% 1.13/1.36  thf('119', plain,
% 1.13/1.36      (![X0 : $i]:
% 1.13/1.36         ((v1_funct_1 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0))
% 1.13/1.36          | ~ (l1_struct_0 @ X0))),
% 1.13/1.36      inference('demod', [status(thm)], ['3', '10', '13', '14', '15'])).
% 1.13/1.36  thf('120', plain,
% 1.13/1.36      (![X0 : $i]:
% 1.13/1.36         ((v1_funct_2 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ 
% 1.13/1.36           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 1.13/1.36          | ~ (l1_struct_0 @ X0))),
% 1.13/1.36      inference('demod', [status(thm)], ['19', '20', '21', '22', '23'])).
% 1.13/1.36  thf('121', plain,
% 1.13/1.36      (![X27 : $i]: ((m1_pre_topc @ X27 @ X27) | ~ (l1_pre_topc @ X27))),
% 1.13/1.36      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.13/1.36  thf('122', plain,
% 1.13/1.36      (![X0 : $i]:
% 1.13/1.36         ((v1_funct_1 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0))
% 1.13/1.36          | ~ (l1_struct_0 @ X0))),
% 1.13/1.36      inference('demod', [status(thm)], ['3', '10', '13', '14', '15'])).
% 1.13/1.36  thf('123', plain,
% 1.13/1.36      (![X0 : $i]:
% 1.13/1.36         ((v1_funct_2 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ 
% 1.13/1.36           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 1.13/1.36          | ~ (l1_struct_0 @ X0))),
% 1.13/1.36      inference('demod', [status(thm)], ['19', '20', '21', '22', '23'])).
% 1.13/1.36  thf('124', plain,
% 1.13/1.36      (![X27 : $i]: ((m1_pre_topc @ X27 @ X27) | ~ (l1_pre_topc @ X27))),
% 1.13/1.36      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.13/1.36  thf('125', plain,
% 1.13/1.36      ((m1_subset_1 @ sk_C @ 
% 1.13/1.36        (k1_zfmisc_1 @ 
% 1.13/1.36         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.13/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.36  thf('126', plain,
% 1.13/1.36      ((m1_subset_1 @ sk_C @ 
% 1.13/1.36        (k1_zfmisc_1 @ 
% 1.13/1.36         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.13/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.36  thf('127', plain,
% 1.13/1.36      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 1.13/1.36         ((v2_struct_0 @ X28)
% 1.13/1.36          | ~ (v2_pre_topc @ X28)
% 1.13/1.36          | ~ (l1_pre_topc @ X28)
% 1.13/1.36          | ~ (v1_funct_1 @ X29)
% 1.13/1.36          | ~ (v1_funct_2 @ X29 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X30))
% 1.13/1.36          | ~ (m1_subset_1 @ X29 @ 
% 1.13/1.36               (k1_zfmisc_1 @ 
% 1.13/1.36                (k2_zfmisc_1 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X30))))
% 1.13/1.36          | (m1_subset_1 @ (sk_F @ X31 @ X29 @ X32 @ X28 @ X30) @ 
% 1.13/1.36             (u1_struct_0 @ X28))
% 1.13/1.36          | (r2_funct_2 @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X30) @ 
% 1.13/1.36             (k2_tmap_1 @ X28 @ X30 @ X29 @ X32) @ X31)
% 1.13/1.36          | ~ (m1_subset_1 @ X31 @ 
% 1.13/1.36               (k1_zfmisc_1 @ 
% 1.13/1.36                (k2_zfmisc_1 @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X30))))
% 1.13/1.36          | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X30))
% 1.13/1.36          | ~ (v1_funct_1 @ X31)
% 1.13/1.36          | ~ (m1_pre_topc @ X32 @ X28)
% 1.13/1.36          | (v2_struct_0 @ X32)
% 1.13/1.36          | ~ (l1_pre_topc @ X30)
% 1.13/1.36          | ~ (v2_pre_topc @ X30)
% 1.13/1.36          | (v2_struct_0 @ X30))),
% 1.13/1.36      inference('cnf', [status(esa)], [t59_tmap_1])).
% 1.13/1.36  thf('128', plain,
% 1.13/1.36      (![X0 : $i, X1 : $i]:
% 1.13/1.36         ((v2_struct_0 @ sk_A)
% 1.13/1.36          | ~ (v2_pre_topc @ sk_A)
% 1.13/1.36          | ~ (l1_pre_topc @ sk_A)
% 1.13/1.36          | (v2_struct_0 @ X0)
% 1.13/1.36          | ~ (m1_pre_topc @ X0 @ sk_B)
% 1.13/1.36          | ~ (v1_funct_1 @ X1)
% 1.13/1.36          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 1.13/1.36          | ~ (m1_subset_1 @ X1 @ 
% 1.13/1.36               (k1_zfmisc_1 @ 
% 1.13/1.36                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 1.13/1.36          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 1.13/1.36             (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ X1)
% 1.13/1.36          | (m1_subset_1 @ (sk_F @ X1 @ sk_C @ X0 @ sk_B @ sk_A) @ 
% 1.13/1.36             (u1_struct_0 @ sk_B))
% 1.13/1.36          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.13/1.36          | ~ (v1_funct_1 @ sk_C)
% 1.13/1.36          | ~ (l1_pre_topc @ sk_B)
% 1.13/1.36          | ~ (v2_pre_topc @ sk_B)
% 1.13/1.36          | (v2_struct_0 @ sk_B))),
% 1.13/1.36      inference('sup-', [status(thm)], ['126', '127'])).
% 1.13/1.36  thf('129', plain, ((v2_pre_topc @ sk_A)),
% 1.13/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.36  thf('130', plain, ((l1_pre_topc @ sk_A)),
% 1.13/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.36  thf('131', plain,
% 1.13/1.36      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 1.13/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.36  thf('132', plain, ((v1_funct_1 @ sk_C)),
% 1.13/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.36  thf('133', plain, ((l1_pre_topc @ sk_B)),
% 1.13/1.36      inference('demod', [status(thm)], ['6', '7'])).
% 1.13/1.36  thf('134', plain, ((v2_pre_topc @ sk_B)),
% 1.13/1.36      inference('demod', [status(thm)], ['44', '45', '46'])).
% 1.13/1.36  thf('135', plain,
% 1.13/1.36      (![X0 : $i, X1 : $i]:
% 1.13/1.36         ((v2_struct_0 @ sk_A)
% 1.13/1.36          | (v2_struct_0 @ X0)
% 1.13/1.36          | ~ (m1_pre_topc @ X0 @ sk_B)
% 1.13/1.36          | ~ (v1_funct_1 @ X1)
% 1.13/1.36          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 1.13/1.36          | ~ (m1_subset_1 @ X1 @ 
% 1.13/1.36               (k1_zfmisc_1 @ 
% 1.13/1.36                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 1.13/1.36          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 1.13/1.36             (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ X1)
% 1.13/1.36          | (m1_subset_1 @ (sk_F @ X1 @ sk_C @ X0 @ sk_B @ sk_A) @ 
% 1.13/1.36             (u1_struct_0 @ sk_B))
% 1.13/1.36          | (v2_struct_0 @ sk_B))),
% 1.13/1.36      inference('demod', [status(thm)],
% 1.13/1.36                ['128', '129', '130', '131', '132', '133', '134'])).
% 1.13/1.36  thf('136', plain,
% 1.13/1.36      (((v2_struct_0 @ sk_B)
% 1.13/1.36        | (m1_subset_1 @ (sk_F @ sk_C @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 1.13/1.36           (u1_struct_0 @ sk_B))
% 1.13/1.36        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.13/1.36           (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) @ sk_C)
% 1.13/1.36        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.13/1.36        | ~ (v1_funct_1 @ sk_C)
% 1.13/1.36        | ~ (m1_pre_topc @ sk_B @ sk_B)
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | (v2_struct_0 @ sk_A))),
% 1.13/1.36      inference('sup-', [status(thm)], ['125', '135'])).
% 1.13/1.36  thf('137', plain,
% 1.13/1.36      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 1.13/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.36  thf('138', plain, ((v1_funct_1 @ sk_C)),
% 1.13/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.36  thf('139', plain,
% 1.13/1.36      (((v2_struct_0 @ sk_B)
% 1.13/1.36        | (m1_subset_1 @ (sk_F @ sk_C @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 1.13/1.36           (u1_struct_0 @ sk_B))
% 1.13/1.36        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.13/1.36           (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) @ sk_C)
% 1.13/1.36        | ~ (m1_pre_topc @ sk_B @ sk_B)
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | (v2_struct_0 @ sk_A))),
% 1.13/1.36      inference('demod', [status(thm)], ['136', '137', '138'])).
% 1.13/1.36  thf('140', plain,
% 1.13/1.36      (((v2_struct_0 @ sk_A)
% 1.13/1.36        | ~ (m1_pre_topc @ sk_B @ sk_B)
% 1.13/1.36        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.13/1.36           (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) @ sk_C)
% 1.13/1.36        | (m1_subset_1 @ (sk_F @ sk_C @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 1.13/1.36           (u1_struct_0 @ sk_B))
% 1.13/1.36        | (v2_struct_0 @ sk_B))),
% 1.13/1.36      inference('simplify', [status(thm)], ['139'])).
% 1.13/1.36  thf('141', plain,
% 1.13/1.36      ((~ (l1_pre_topc @ sk_B)
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | (m1_subset_1 @ (sk_F @ sk_C @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 1.13/1.36           (u1_struct_0 @ sk_B))
% 1.13/1.36        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.13/1.36           (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) @ sk_C)
% 1.13/1.36        | (v2_struct_0 @ sk_A))),
% 1.13/1.36      inference('sup-', [status(thm)], ['124', '140'])).
% 1.13/1.36  thf('142', plain, ((l1_pre_topc @ sk_B)),
% 1.13/1.36      inference('demod', [status(thm)], ['6', '7'])).
% 1.13/1.36  thf('143', plain,
% 1.13/1.36      (((v2_struct_0 @ sk_B)
% 1.13/1.36        | (m1_subset_1 @ (sk_F @ sk_C @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 1.13/1.36           (u1_struct_0 @ sk_B))
% 1.13/1.36        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.13/1.36           (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) @ sk_C)
% 1.13/1.36        | (v2_struct_0 @ sk_A))),
% 1.13/1.36      inference('demod', [status(thm)], ['141', '142'])).
% 1.13/1.36  thf('144', plain,
% 1.13/1.36      (![X0 : $i, X1 : $i]:
% 1.13/1.36         (~ (l1_struct_0 @ X0)
% 1.13/1.36          | ~ (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 1.13/1.36               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ X1)
% 1.13/1.36          | ((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) = (X1))
% 1.13/1.36          | ~ (m1_subset_1 @ X1 @ 
% 1.13/1.36               (k1_zfmisc_1 @ 
% 1.13/1.36                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 1.13/1.36          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 1.13/1.36          | ~ (v1_funct_1 @ X1)
% 1.13/1.36          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0))
% 1.13/1.36          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ 
% 1.13/1.36               (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A)))),
% 1.13/1.36      inference('sup-', [status(thm)], ['78', '79'])).
% 1.13/1.36  thf('145', plain,
% 1.13/1.36      (((v2_struct_0 @ sk_A)
% 1.13/1.36        | (m1_subset_1 @ (sk_F @ sk_C @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 1.13/1.36           (u1_struct_0 @ sk_B))
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) @ 
% 1.13/1.36             (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.13/1.36        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 1.13/1.36        | ~ (v1_funct_1 @ sk_C)
% 1.13/1.36        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.13/1.36        | ~ (m1_subset_1 @ sk_C @ 
% 1.13/1.36             (k1_zfmisc_1 @ 
% 1.13/1.36              (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 1.13/1.36        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) = (sk_C))
% 1.13/1.36        | ~ (l1_struct_0 @ sk_B))),
% 1.13/1.36      inference('sup-', [status(thm)], ['143', '144'])).
% 1.13/1.36  thf('146', plain, ((v1_funct_1 @ sk_C)),
% 1.13/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.36  thf('147', plain,
% 1.13/1.36      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 1.13/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.36  thf('148', plain,
% 1.13/1.36      ((m1_subset_1 @ sk_C @ 
% 1.13/1.36        (k1_zfmisc_1 @ 
% 1.13/1.36         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.13/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.36  thf('149', plain, ((l1_struct_0 @ sk_B)),
% 1.13/1.36      inference('sup-', [status(thm)], ['8', '9'])).
% 1.13/1.36  thf('150', plain,
% 1.13/1.36      (((v2_struct_0 @ sk_A)
% 1.13/1.36        | (m1_subset_1 @ (sk_F @ sk_C @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 1.13/1.36           (u1_struct_0 @ sk_B))
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) @ 
% 1.13/1.36             (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.13/1.36        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 1.13/1.36        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) = (sk_C)))),
% 1.13/1.36      inference('demod', [status(thm)], ['145', '146', '147', '148', '149'])).
% 1.13/1.36  thf('151', plain,
% 1.13/1.36      ((~ (l1_struct_0 @ sk_B)
% 1.13/1.36        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) = (sk_C))
% 1.13/1.36        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | (m1_subset_1 @ (sk_F @ sk_C @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 1.13/1.36           (u1_struct_0 @ sk_B))
% 1.13/1.36        | (v2_struct_0 @ sk_A))),
% 1.13/1.36      inference('sup-', [status(thm)], ['123', '150'])).
% 1.13/1.36  thf('152', plain, ((l1_struct_0 @ sk_B)),
% 1.13/1.36      inference('sup-', [status(thm)], ['8', '9'])).
% 1.13/1.36  thf('153', plain,
% 1.13/1.36      ((((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) = (sk_C))
% 1.13/1.36        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | (m1_subset_1 @ (sk_F @ sk_C @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 1.13/1.36           (u1_struct_0 @ sk_B))
% 1.13/1.36        | (v2_struct_0 @ sk_A))),
% 1.13/1.36      inference('demod', [status(thm)], ['151', '152'])).
% 1.13/1.36  thf('154', plain,
% 1.13/1.36      ((~ (l1_struct_0 @ sk_B)
% 1.13/1.36        | (v2_struct_0 @ sk_A)
% 1.13/1.36        | (m1_subset_1 @ (sk_F @ sk_C @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 1.13/1.36           (u1_struct_0 @ sk_B))
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) = (sk_C)))),
% 1.13/1.36      inference('sup-', [status(thm)], ['122', '153'])).
% 1.13/1.36  thf('155', plain, ((l1_struct_0 @ sk_B)),
% 1.13/1.36      inference('sup-', [status(thm)], ['8', '9'])).
% 1.13/1.36  thf('156', plain,
% 1.13/1.36      (((v2_struct_0 @ sk_A)
% 1.13/1.36        | (m1_subset_1 @ (sk_F @ sk_C @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 1.13/1.36           (u1_struct_0 @ sk_B))
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) = (sk_C)))),
% 1.13/1.36      inference('demod', [status(thm)], ['154', '155'])).
% 1.13/1.36  thf('157', plain,
% 1.13/1.36      ((m1_subset_1 @ sk_C @ 
% 1.13/1.36        (k1_zfmisc_1 @ 
% 1.13/1.36         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.13/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.36  thf(redefinition_k3_funct_2, axiom,
% 1.13/1.36    (![A:$i,B:$i,C:$i,D:$i]:
% 1.13/1.36     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 1.13/1.36         ( v1_funct_2 @ C @ A @ B ) & 
% 1.13/1.36         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.13/1.36         ( m1_subset_1 @ D @ A ) ) =>
% 1.13/1.36       ( ( k3_funct_2 @ A @ B @ C @ D ) = ( k1_funct_1 @ C @ D ) ) ))).
% 1.13/1.36  thf('158', plain,
% 1.13/1.36      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.13/1.36         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5)))
% 1.13/1.36          | ~ (v1_funct_2 @ X3 @ X4 @ X5)
% 1.13/1.36          | ~ (v1_funct_1 @ X3)
% 1.13/1.36          | (v1_xboole_0 @ X4)
% 1.13/1.36          | ~ (m1_subset_1 @ X6 @ X4)
% 1.13/1.36          | ((k3_funct_2 @ X4 @ X5 @ X3 @ X6) = (k1_funct_1 @ X3 @ X6)))),
% 1.13/1.36      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 1.13/1.36  thf('159', plain,
% 1.13/1.36      (![X0 : $i]:
% 1.13/1.36         (((k3_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.13/1.36            X0) = (k1_funct_1 @ sk_C @ X0))
% 1.13/1.36          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 1.13/1.36          | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.13/1.36          | ~ (v1_funct_1 @ sk_C)
% 1.13/1.36          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 1.13/1.36      inference('sup-', [status(thm)], ['157', '158'])).
% 1.13/1.36  thf('160', plain, ((v1_funct_1 @ sk_C)),
% 1.13/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.36  thf('161', plain,
% 1.13/1.36      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 1.13/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.36  thf('162', plain,
% 1.13/1.36      (![X0 : $i]:
% 1.13/1.36         (((k3_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.13/1.36            X0) = (k1_funct_1 @ sk_C @ X0))
% 1.13/1.36          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 1.13/1.36          | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 1.13/1.36      inference('demod', [status(thm)], ['159', '160', '161'])).
% 1.13/1.36  thf('163', plain,
% 1.13/1.36      ((((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) = (sk_C))
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | (v2_struct_0 @ sk_A)
% 1.13/1.36        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.13/1.36        | ((k3_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.13/1.36            (sk_F @ sk_C @ sk_C @ sk_B @ sk_B @ sk_A))
% 1.13/1.36            = (k1_funct_1 @ sk_C @ (sk_F @ sk_C @ sk_C @ sk_B @ sk_B @ sk_A))))),
% 1.13/1.36      inference('sup-', [status(thm)], ['156', '162'])).
% 1.13/1.36  thf('164', plain,
% 1.13/1.36      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 1.13/1.36         ((v2_struct_0 @ X28)
% 1.13/1.36          | ~ (v2_pre_topc @ X28)
% 1.13/1.36          | ~ (l1_pre_topc @ X28)
% 1.13/1.36          | ~ (v1_funct_1 @ X29)
% 1.13/1.36          | ~ (v1_funct_2 @ X29 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X30))
% 1.13/1.36          | ~ (m1_subset_1 @ X29 @ 
% 1.13/1.36               (k1_zfmisc_1 @ 
% 1.13/1.36                (k2_zfmisc_1 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X30))))
% 1.13/1.36          | ((k3_funct_2 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X30) @ X29 @ 
% 1.13/1.36              (sk_F @ X31 @ X29 @ X32 @ X28 @ X30))
% 1.13/1.36              != (k1_funct_1 @ X31 @ (sk_F @ X31 @ X29 @ X32 @ X28 @ X30)))
% 1.13/1.36          | (r2_funct_2 @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X30) @ 
% 1.13/1.36             (k2_tmap_1 @ X28 @ X30 @ X29 @ X32) @ X31)
% 1.13/1.36          | ~ (m1_subset_1 @ X31 @ 
% 1.13/1.36               (k1_zfmisc_1 @ 
% 1.13/1.36                (k2_zfmisc_1 @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X30))))
% 1.13/1.36          | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X30))
% 1.13/1.36          | ~ (v1_funct_1 @ X31)
% 1.13/1.36          | ~ (m1_pre_topc @ X32 @ X28)
% 1.13/1.36          | (v2_struct_0 @ X32)
% 1.13/1.36          | ~ (l1_pre_topc @ X30)
% 1.13/1.36          | ~ (v2_pre_topc @ X30)
% 1.13/1.36          | (v2_struct_0 @ X30))),
% 1.13/1.36      inference('cnf', [status(esa)], [t59_tmap_1])).
% 1.13/1.36  thf('165', plain,
% 1.13/1.36      ((((k1_funct_1 @ sk_C @ (sk_F @ sk_C @ sk_C @ sk_B @ sk_B @ sk_A))
% 1.13/1.36          != (k1_funct_1 @ sk_C @ (sk_F @ sk_C @ sk_C @ sk_B @ sk_B @ sk_A)))
% 1.13/1.36        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.13/1.36        | (v2_struct_0 @ sk_A)
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) = (sk_C))
% 1.13/1.36        | (v2_struct_0 @ sk_A)
% 1.13/1.36        | ~ (v2_pre_topc @ sk_A)
% 1.13/1.36        | ~ (l1_pre_topc @ sk_A)
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | ~ (m1_pre_topc @ sk_B @ sk_B)
% 1.13/1.36        | ~ (v1_funct_1 @ sk_C)
% 1.13/1.36        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.13/1.36        | ~ (m1_subset_1 @ sk_C @ 
% 1.13/1.36             (k1_zfmisc_1 @ 
% 1.13/1.36              (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 1.13/1.36        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.13/1.36           (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) @ sk_C)
% 1.13/1.36        | ~ (m1_subset_1 @ sk_C @ 
% 1.13/1.36             (k1_zfmisc_1 @ 
% 1.13/1.36              (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 1.13/1.36        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.13/1.36        | ~ (v1_funct_1 @ sk_C)
% 1.13/1.36        | ~ (l1_pre_topc @ sk_B)
% 1.13/1.36        | ~ (v2_pre_topc @ sk_B)
% 1.13/1.36        | (v2_struct_0 @ sk_B))),
% 1.13/1.36      inference('sup-', [status(thm)], ['163', '164'])).
% 1.13/1.36  thf('166', plain, ((v2_pre_topc @ sk_A)),
% 1.13/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.36  thf('167', plain, ((l1_pre_topc @ sk_A)),
% 1.13/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.36  thf('168', plain, ((v1_funct_1 @ sk_C)),
% 1.13/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.36  thf('169', plain,
% 1.13/1.36      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 1.13/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.36  thf('170', plain,
% 1.13/1.36      ((m1_subset_1 @ sk_C @ 
% 1.13/1.36        (k1_zfmisc_1 @ 
% 1.13/1.36         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.13/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.36  thf('171', plain,
% 1.13/1.36      ((m1_subset_1 @ sk_C @ 
% 1.13/1.36        (k1_zfmisc_1 @ 
% 1.13/1.36         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.13/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.36  thf('172', plain,
% 1.13/1.36      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 1.13/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.36  thf('173', plain, ((v1_funct_1 @ sk_C)),
% 1.13/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.36  thf('174', plain, ((l1_pre_topc @ sk_B)),
% 1.13/1.36      inference('demod', [status(thm)], ['6', '7'])).
% 1.13/1.36  thf('175', plain, ((v2_pre_topc @ sk_B)),
% 1.13/1.36      inference('demod', [status(thm)], ['44', '45', '46'])).
% 1.13/1.36  thf('176', plain,
% 1.13/1.36      ((((k1_funct_1 @ sk_C @ (sk_F @ sk_C @ sk_C @ sk_B @ sk_B @ sk_A))
% 1.13/1.36          != (k1_funct_1 @ sk_C @ (sk_F @ sk_C @ sk_C @ sk_B @ sk_B @ sk_A)))
% 1.13/1.36        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.13/1.36        | (v2_struct_0 @ sk_A)
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) = (sk_C))
% 1.13/1.36        | (v2_struct_0 @ sk_A)
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | ~ (m1_pre_topc @ sk_B @ sk_B)
% 1.13/1.36        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.13/1.36           (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) @ sk_C)
% 1.13/1.36        | (v2_struct_0 @ sk_B))),
% 1.13/1.36      inference('demod', [status(thm)],
% 1.13/1.36                ['165', '166', '167', '168', '169', '170', '171', '172', 
% 1.13/1.36                 '173', '174', '175'])).
% 1.13/1.36  thf('177', plain,
% 1.13/1.36      (((r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.13/1.36         (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) @ sk_C)
% 1.13/1.36        | ~ (m1_pre_topc @ sk_B @ sk_B)
% 1.13/1.36        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) = (sk_C))
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | (v2_struct_0 @ sk_A)
% 1.13/1.36        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 1.13/1.36      inference('simplify', [status(thm)], ['176'])).
% 1.13/1.36  thf('178', plain,
% 1.13/1.36      ((~ (l1_pre_topc @ sk_B)
% 1.13/1.36        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.13/1.36        | (v2_struct_0 @ sk_A)
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) = (sk_C))
% 1.13/1.36        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.13/1.36           (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) @ sk_C))),
% 1.13/1.36      inference('sup-', [status(thm)], ['121', '177'])).
% 1.13/1.36  thf('179', plain, ((l1_pre_topc @ sk_B)),
% 1.13/1.36      inference('demod', [status(thm)], ['6', '7'])).
% 1.13/1.36  thf('180', plain,
% 1.13/1.36      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.13/1.36        | (v2_struct_0 @ sk_A)
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) = (sk_C))
% 1.13/1.36        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.13/1.36           (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) @ sk_C))),
% 1.13/1.36      inference('demod', [status(thm)], ['178', '179'])).
% 1.13/1.36  thf('181', plain,
% 1.13/1.36      (![X0 : $i, X1 : $i]:
% 1.13/1.36         (~ (l1_struct_0 @ X0)
% 1.13/1.36          | ~ (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 1.13/1.36               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ X1)
% 1.13/1.36          | ((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) = (X1))
% 1.13/1.36          | ~ (m1_subset_1 @ X1 @ 
% 1.13/1.36               (k1_zfmisc_1 @ 
% 1.13/1.36                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 1.13/1.36          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 1.13/1.36          | ~ (v1_funct_1 @ X1)
% 1.13/1.36          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0))
% 1.13/1.36          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ 
% 1.13/1.36               (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A)))),
% 1.13/1.36      inference('sup-', [status(thm)], ['78', '79'])).
% 1.13/1.36  thf('182', plain,
% 1.13/1.36      ((((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) = (sk_C))
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | (v2_struct_0 @ sk_A)
% 1.13/1.36        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.13/1.36        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) @ 
% 1.13/1.36             (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.13/1.36        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 1.13/1.36        | ~ (v1_funct_1 @ sk_C)
% 1.13/1.36        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.13/1.36        | ~ (m1_subset_1 @ sk_C @ 
% 1.13/1.36             (k1_zfmisc_1 @ 
% 1.13/1.36              (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 1.13/1.36        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) = (sk_C))
% 1.13/1.36        | ~ (l1_struct_0 @ sk_B))),
% 1.13/1.36      inference('sup-', [status(thm)], ['180', '181'])).
% 1.13/1.36  thf('183', plain, ((v1_funct_1 @ sk_C)),
% 1.13/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.36  thf('184', plain,
% 1.13/1.36      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 1.13/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.36  thf('185', plain,
% 1.13/1.36      ((m1_subset_1 @ sk_C @ 
% 1.13/1.36        (k1_zfmisc_1 @ 
% 1.13/1.36         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.13/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.36  thf('186', plain, ((l1_struct_0 @ sk_B)),
% 1.13/1.36      inference('sup-', [status(thm)], ['8', '9'])).
% 1.13/1.36  thf('187', plain,
% 1.13/1.36      ((((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) = (sk_C))
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | (v2_struct_0 @ sk_A)
% 1.13/1.36        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.13/1.36        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) @ 
% 1.13/1.36             (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.13/1.36        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 1.13/1.36        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) = (sk_C)))),
% 1.13/1.36      inference('demod', [status(thm)], ['182', '183', '184', '185', '186'])).
% 1.13/1.36  thf('188', plain,
% 1.13/1.36      ((~ (v1_funct_1 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 1.13/1.36        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) @ 
% 1.13/1.36             (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.13/1.36        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.13/1.36        | (v2_struct_0 @ sk_A)
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) = (sk_C)))),
% 1.13/1.36      inference('simplify', [status(thm)], ['187'])).
% 1.13/1.36  thf('189', plain,
% 1.13/1.36      ((~ (l1_struct_0 @ sk_B)
% 1.13/1.36        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) = (sk_C))
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | (v2_struct_0 @ sk_A)
% 1.13/1.36        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.13/1.36        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B)))),
% 1.13/1.36      inference('sup-', [status(thm)], ['120', '188'])).
% 1.13/1.36  thf('190', plain, ((l1_struct_0 @ sk_B)),
% 1.13/1.36      inference('sup-', [status(thm)], ['8', '9'])).
% 1.13/1.36  thf('191', plain,
% 1.13/1.36      ((((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) = (sk_C))
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | (v2_struct_0 @ sk_A)
% 1.13/1.36        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.13/1.36        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B)))),
% 1.13/1.36      inference('demod', [status(thm)], ['189', '190'])).
% 1.13/1.36  thf('192', plain,
% 1.13/1.36      ((~ (l1_struct_0 @ sk_B)
% 1.13/1.36        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.13/1.36        | (v2_struct_0 @ sk_A)
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) = (sk_C)))),
% 1.13/1.36      inference('sup-', [status(thm)], ['119', '191'])).
% 1.13/1.36  thf('193', plain, ((l1_struct_0 @ sk_B)),
% 1.13/1.36      inference('sup-', [status(thm)], ['8', '9'])).
% 1.13/1.36  thf('194', plain,
% 1.13/1.36      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.13/1.36        | (v2_struct_0 @ sk_A)
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) = (sk_C)))),
% 1.13/1.36      inference('demod', [status(thm)], ['192', '193'])).
% 1.13/1.36  thf('195', plain,
% 1.13/1.36      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.13/1.36        | (v2_struct_0 @ sk_A)
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) = (sk_C)))),
% 1.13/1.36      inference('demod', [status(thm)], ['192', '193'])).
% 1.13/1.36  thf('196', plain,
% 1.13/1.36      (![X27 : $i]: ((m1_pre_topc @ X27 @ X27) | ~ (l1_pre_topc @ X27))),
% 1.13/1.36      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.13/1.36  thf('197', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.13/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.36  thf('198', plain,
% 1.13/1.36      (![X0 : $i]:
% 1.13/1.36         ((v1_funct_1 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0))
% 1.13/1.36          | ~ (l1_struct_0 @ X0))),
% 1.13/1.36      inference('demod', [status(thm)], ['3', '10', '13', '14', '15'])).
% 1.13/1.36  thf('199', plain,
% 1.13/1.36      (![X0 : $i]:
% 1.13/1.36         ((v1_funct_2 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ 
% 1.13/1.36           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 1.13/1.36          | ~ (l1_struct_0 @ X0))),
% 1.13/1.36      inference('demod', [status(thm)], ['19', '20', '21', '22', '23'])).
% 1.13/1.36  thf('200', plain,
% 1.13/1.36      (![X27 : $i]: ((m1_pre_topc @ X27 @ X27) | ~ (l1_pre_topc @ X27))),
% 1.13/1.36      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.13/1.36  thf('201', plain,
% 1.13/1.36      ((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 1.13/1.36        (k1_zfmisc_1 @ 
% 1.13/1.36         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.13/1.36      inference('clc', [status(thm)], ['31', '32'])).
% 1.13/1.36  thf('202', plain,
% 1.13/1.36      (![X0 : $i, X1 : $i]:
% 1.13/1.36         ((v2_struct_0 @ sk_A)
% 1.13/1.36          | (v2_struct_0 @ X0)
% 1.13/1.36          | ~ (m1_pre_topc @ X0 @ sk_B)
% 1.13/1.36          | ~ (v1_funct_1 @ X1)
% 1.13/1.36          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 1.13/1.36          | ~ (m1_subset_1 @ X1 @ 
% 1.13/1.36               (k1_zfmisc_1 @ 
% 1.13/1.36                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 1.13/1.36          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 1.13/1.36             (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ X1)
% 1.13/1.36          | (m1_subset_1 @ (sk_F @ X1 @ sk_C @ X0 @ sk_B @ sk_A) @ 
% 1.13/1.36             (u1_struct_0 @ sk_B))
% 1.13/1.36          | (v2_struct_0 @ sk_B))),
% 1.13/1.36      inference('demod', [status(thm)],
% 1.13/1.36                ['128', '129', '130', '131', '132', '133', '134'])).
% 1.13/1.36  thf('203', plain,
% 1.13/1.36      (((v2_struct_0 @ sk_B)
% 1.13/1.36        | (m1_subset_1 @ 
% 1.13/1.36           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 1.13/1.36           (u1_struct_0 @ sk_B))
% 1.13/1.36        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.13/1.36           (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) @ (k4_tmap_1 @ sk_A @ sk_B))
% 1.13/1.36        | ~ (v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 1.13/1.36             (u1_struct_0 @ sk_A))
% 1.13/1.36        | ~ (v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))
% 1.13/1.36        | ~ (m1_pre_topc @ sk_B @ sk_B)
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | (v2_struct_0 @ sk_A))),
% 1.13/1.36      inference('sup-', [status(thm)], ['201', '202'])).
% 1.13/1.36  thf('204', plain,
% 1.13/1.36      ((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 1.13/1.36        (u1_struct_0 @ sk_A))),
% 1.13/1.36      inference('clc', [status(thm)], ['55', '56'])).
% 1.13/1.36  thf('205', plain, ((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))),
% 1.13/1.36      inference('clc', [status(thm)], ['63', '64'])).
% 1.13/1.36  thf('206', plain,
% 1.13/1.36      (((v2_struct_0 @ sk_B)
% 1.13/1.36        | (m1_subset_1 @ 
% 1.13/1.36           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 1.13/1.36           (u1_struct_0 @ sk_B))
% 1.13/1.36        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.13/1.36           (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) @ (k4_tmap_1 @ sk_A @ sk_B))
% 1.13/1.36        | ~ (m1_pre_topc @ sk_B @ sk_B)
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | (v2_struct_0 @ sk_A))),
% 1.13/1.36      inference('demod', [status(thm)], ['203', '204', '205'])).
% 1.13/1.36  thf('207', plain,
% 1.13/1.36      (((v2_struct_0 @ sk_A)
% 1.13/1.36        | ~ (m1_pre_topc @ sk_B @ sk_B)
% 1.13/1.36        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.13/1.36           (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) @ (k4_tmap_1 @ sk_A @ sk_B))
% 1.13/1.36        | (m1_subset_1 @ 
% 1.13/1.36           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 1.13/1.36           (u1_struct_0 @ sk_B))
% 1.13/1.36        | (v2_struct_0 @ sk_B))),
% 1.13/1.36      inference('simplify', [status(thm)], ['206'])).
% 1.13/1.36  thf('208', plain,
% 1.13/1.36      ((~ (l1_pre_topc @ sk_B)
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | (m1_subset_1 @ 
% 1.13/1.36           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 1.13/1.36           (u1_struct_0 @ sk_B))
% 1.13/1.36        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.13/1.36           (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) @ (k4_tmap_1 @ sk_A @ sk_B))
% 1.13/1.36        | (v2_struct_0 @ sk_A))),
% 1.13/1.36      inference('sup-', [status(thm)], ['200', '207'])).
% 1.13/1.36  thf('209', plain, ((l1_pre_topc @ sk_B)),
% 1.13/1.36      inference('demod', [status(thm)], ['6', '7'])).
% 1.13/1.36  thf('210', plain,
% 1.13/1.36      (((v2_struct_0 @ sk_B)
% 1.13/1.36        | (m1_subset_1 @ 
% 1.13/1.36           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 1.13/1.36           (u1_struct_0 @ sk_B))
% 1.13/1.36        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.13/1.36           (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) @ (k4_tmap_1 @ sk_A @ sk_B))
% 1.13/1.36        | (v2_struct_0 @ sk_A))),
% 1.13/1.36      inference('demod', [status(thm)], ['208', '209'])).
% 1.13/1.36  thf('211', plain,
% 1.13/1.36      (![X0 : $i, X1 : $i]:
% 1.13/1.36         (~ (l1_struct_0 @ X0)
% 1.13/1.36          | ~ (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 1.13/1.36               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ X1)
% 1.13/1.36          | ((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) = (X1))
% 1.13/1.36          | ~ (m1_subset_1 @ X1 @ 
% 1.13/1.36               (k1_zfmisc_1 @ 
% 1.13/1.36                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 1.13/1.36          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 1.13/1.36          | ~ (v1_funct_1 @ X1)
% 1.13/1.36          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0))
% 1.13/1.36          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ 
% 1.13/1.36               (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A)))),
% 1.13/1.36      inference('sup-', [status(thm)], ['78', '79'])).
% 1.13/1.36  thf('212', plain,
% 1.13/1.36      (((v2_struct_0 @ sk_A)
% 1.13/1.36        | (m1_subset_1 @ 
% 1.13/1.36           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 1.13/1.36           (u1_struct_0 @ sk_B))
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) @ 
% 1.13/1.36             (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.13/1.36        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 1.13/1.36        | ~ (v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))
% 1.13/1.36        | ~ (v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 1.13/1.36             (u1_struct_0 @ sk_A))
% 1.13/1.36        | ~ (m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 1.13/1.36             (k1_zfmisc_1 @ 
% 1.13/1.36              (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 1.13/1.36        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) = (k4_tmap_1 @ sk_A @ sk_B))
% 1.13/1.36        | ~ (l1_struct_0 @ sk_B))),
% 1.13/1.36      inference('sup-', [status(thm)], ['210', '211'])).
% 1.13/1.36  thf('213', plain, ((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))),
% 1.13/1.36      inference('clc', [status(thm)], ['63', '64'])).
% 1.13/1.36  thf('214', plain,
% 1.13/1.36      ((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 1.13/1.36        (u1_struct_0 @ sk_A))),
% 1.13/1.36      inference('clc', [status(thm)], ['55', '56'])).
% 1.13/1.36  thf('215', plain,
% 1.13/1.36      ((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 1.13/1.36        (k1_zfmisc_1 @ 
% 1.13/1.36         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.13/1.36      inference('clc', [status(thm)], ['31', '32'])).
% 1.13/1.36  thf('216', plain, ((l1_struct_0 @ sk_B)),
% 1.13/1.36      inference('sup-', [status(thm)], ['8', '9'])).
% 1.13/1.36  thf('217', plain,
% 1.13/1.36      (((v2_struct_0 @ sk_A)
% 1.13/1.36        | (m1_subset_1 @ 
% 1.13/1.36           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 1.13/1.36           (u1_struct_0 @ sk_B))
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) @ 
% 1.13/1.36             (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.13/1.36        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 1.13/1.36        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) = (k4_tmap_1 @ sk_A @ sk_B)))),
% 1.13/1.36      inference('demod', [status(thm)], ['212', '213', '214', '215', '216'])).
% 1.13/1.36  thf('218', plain,
% 1.13/1.36      ((~ (l1_struct_0 @ sk_B)
% 1.13/1.36        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) = (k4_tmap_1 @ sk_A @ sk_B))
% 1.13/1.36        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | (m1_subset_1 @ 
% 1.13/1.36           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 1.13/1.36           (u1_struct_0 @ sk_B))
% 1.13/1.36        | (v2_struct_0 @ sk_A))),
% 1.13/1.36      inference('sup-', [status(thm)], ['199', '217'])).
% 1.13/1.36  thf('219', plain, ((l1_struct_0 @ sk_B)),
% 1.13/1.36      inference('sup-', [status(thm)], ['8', '9'])).
% 1.13/1.36  thf('220', plain,
% 1.13/1.36      ((((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) = (k4_tmap_1 @ sk_A @ sk_B))
% 1.13/1.36        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | (m1_subset_1 @ 
% 1.13/1.36           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 1.13/1.36           (u1_struct_0 @ sk_B))
% 1.13/1.36        | (v2_struct_0 @ sk_A))),
% 1.13/1.36      inference('demod', [status(thm)], ['218', '219'])).
% 1.13/1.36  thf('221', plain,
% 1.13/1.36      ((~ (l1_struct_0 @ sk_B)
% 1.13/1.36        | (v2_struct_0 @ sk_A)
% 1.13/1.36        | (m1_subset_1 @ 
% 1.13/1.36           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 1.13/1.36           (u1_struct_0 @ sk_B))
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) = (k4_tmap_1 @ sk_A @ sk_B)))),
% 1.13/1.36      inference('sup-', [status(thm)], ['198', '220'])).
% 1.13/1.36  thf('222', plain, ((l1_struct_0 @ sk_B)),
% 1.13/1.36      inference('sup-', [status(thm)], ['8', '9'])).
% 1.13/1.36  thf('223', plain,
% 1.13/1.36      (((v2_struct_0 @ sk_A)
% 1.13/1.36        | (m1_subset_1 @ 
% 1.13/1.36           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 1.13/1.36           (u1_struct_0 @ sk_B))
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) = (k4_tmap_1 @ sk_A @ sk_B)))),
% 1.13/1.36      inference('demod', [status(thm)], ['221', '222'])).
% 1.13/1.36  thf(t55_pre_topc, axiom,
% 1.13/1.36    (![A:$i]:
% 1.13/1.36     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 1.13/1.36       ( ![B:$i]:
% 1.13/1.36         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 1.13/1.36           ( ![C:$i]:
% 1.13/1.36             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) =>
% 1.13/1.36               ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 1.13/1.36  thf('224', plain,
% 1.13/1.36      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.13/1.36         ((v2_struct_0 @ X16)
% 1.13/1.36          | ~ (m1_pre_topc @ X16 @ X17)
% 1.13/1.36          | (m1_subset_1 @ X18 @ (u1_struct_0 @ X17))
% 1.13/1.36          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X16))
% 1.13/1.36          | ~ (l1_pre_topc @ X17)
% 1.13/1.36          | (v2_struct_0 @ X17))),
% 1.13/1.36      inference('cnf', [status(esa)], [t55_pre_topc])).
% 1.13/1.36  thf('225', plain,
% 1.13/1.36      (![X0 : $i]:
% 1.13/1.36         (((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) = (k4_tmap_1 @ sk_A @ sk_B))
% 1.13/1.36          | (v2_struct_0 @ sk_B)
% 1.13/1.36          | (v2_struct_0 @ sk_A)
% 1.13/1.36          | (v2_struct_0 @ X0)
% 1.13/1.36          | ~ (l1_pre_topc @ X0)
% 1.13/1.36          | (m1_subset_1 @ 
% 1.13/1.36             (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 1.13/1.36             (u1_struct_0 @ X0))
% 1.13/1.36          | ~ (m1_pre_topc @ sk_B @ X0)
% 1.13/1.36          | (v2_struct_0 @ sk_B))),
% 1.13/1.36      inference('sup-', [status(thm)], ['223', '224'])).
% 1.13/1.36  thf('226', plain,
% 1.13/1.36      (![X0 : $i]:
% 1.13/1.36         (~ (m1_pre_topc @ sk_B @ X0)
% 1.13/1.36          | (m1_subset_1 @ 
% 1.13/1.36             (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 1.13/1.36             (u1_struct_0 @ X0))
% 1.13/1.36          | ~ (l1_pre_topc @ X0)
% 1.13/1.36          | (v2_struct_0 @ X0)
% 1.13/1.36          | (v2_struct_0 @ sk_A)
% 1.13/1.36          | (v2_struct_0 @ sk_B)
% 1.13/1.36          | ((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B)
% 1.13/1.36              = (k4_tmap_1 @ sk_A @ sk_B)))),
% 1.13/1.36      inference('simplify', [status(thm)], ['225'])).
% 1.13/1.36  thf('227', plain,
% 1.13/1.36      ((((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) = (k4_tmap_1 @ sk_A @ sk_B))
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | (v2_struct_0 @ sk_A)
% 1.13/1.36        | (v2_struct_0 @ sk_A)
% 1.13/1.36        | ~ (l1_pre_topc @ sk_A)
% 1.13/1.36        | (m1_subset_1 @ 
% 1.13/1.36           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 1.13/1.36           (u1_struct_0 @ sk_A)))),
% 1.13/1.36      inference('sup-', [status(thm)], ['197', '226'])).
% 1.13/1.36  thf('228', plain, ((l1_pre_topc @ sk_A)),
% 1.13/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.36  thf('229', plain,
% 1.13/1.36      ((((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) = (k4_tmap_1 @ sk_A @ sk_B))
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | (v2_struct_0 @ sk_A)
% 1.13/1.36        | (v2_struct_0 @ sk_A)
% 1.13/1.36        | (m1_subset_1 @ 
% 1.13/1.36           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 1.13/1.36           (u1_struct_0 @ sk_A)))),
% 1.13/1.36      inference('demod', [status(thm)], ['227', '228'])).
% 1.13/1.36  thf('230', plain,
% 1.13/1.36      (((m1_subset_1 @ 
% 1.13/1.36         (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 1.13/1.36         (u1_struct_0 @ sk_A))
% 1.13/1.36        | (v2_struct_0 @ sk_A)
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) = (k4_tmap_1 @ sk_A @ sk_B)))),
% 1.13/1.36      inference('simplify', [status(thm)], ['229'])).
% 1.13/1.36  thf('231', plain,
% 1.13/1.36      (((v2_struct_0 @ sk_A)
% 1.13/1.36        | (r2_hidden @ 
% 1.13/1.36           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 1.13/1.36           (u1_struct_0 @ sk_B))
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) = (k4_tmap_1 @ sk_A @ sk_B)))),
% 1.13/1.36      inference('demod', [status(thm)], ['90', '91'])).
% 1.13/1.36  thf('232', plain,
% 1.13/1.36      (![X36 : $i]:
% 1.13/1.36         (~ (r2_hidden @ X36 @ (u1_struct_0 @ sk_B))
% 1.13/1.36          | ((X36) = (k1_funct_1 @ sk_C @ X36))
% 1.13/1.36          | ~ (m1_subset_1 @ X36 @ (u1_struct_0 @ sk_A)))),
% 1.13/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.36  thf('233', plain,
% 1.13/1.36      ((((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) = (k4_tmap_1 @ sk_A @ sk_B))
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | (v2_struct_0 @ sk_A)
% 1.13/1.36        | ~ (m1_subset_1 @ 
% 1.13/1.36             (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 1.13/1.36             (u1_struct_0 @ sk_A))
% 1.13/1.36        | ((sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A)
% 1.13/1.36            = (k1_funct_1 @ sk_C @ 
% 1.13/1.36               (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))))),
% 1.13/1.36      inference('sup-', [status(thm)], ['231', '232'])).
% 1.13/1.36  thf('234', plain,
% 1.13/1.36      ((((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) = (k4_tmap_1 @ sk_A @ sk_B))
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | (v2_struct_0 @ sk_A)
% 1.13/1.36        | ((sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A)
% 1.13/1.36            = (k1_funct_1 @ sk_C @ 
% 1.13/1.36               (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A)))
% 1.13/1.36        | (v2_struct_0 @ sk_A)
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) = (k4_tmap_1 @ sk_A @ sk_B)))),
% 1.13/1.36      inference('sup-', [status(thm)], ['230', '233'])).
% 1.13/1.36  thf('235', plain,
% 1.13/1.36      ((((sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A)
% 1.13/1.36          = (k1_funct_1 @ sk_C @ 
% 1.13/1.36             (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A)))
% 1.13/1.36        | (v2_struct_0 @ sk_A)
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) = (k4_tmap_1 @ sk_A @ sk_B)))),
% 1.13/1.36      inference('simplify', [status(thm)], ['234'])).
% 1.13/1.36  thf('236', plain,
% 1.13/1.36      (((m1_subset_1 @ 
% 1.13/1.36         (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 1.13/1.36         (u1_struct_0 @ sk_A))
% 1.13/1.36        | (v2_struct_0 @ sk_A)
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) = (k4_tmap_1 @ sk_A @ sk_B)))),
% 1.13/1.36      inference('simplify', [status(thm)], ['229'])).
% 1.13/1.36  thf('237', plain,
% 1.13/1.36      (((v2_struct_0 @ sk_A)
% 1.13/1.36        | (r2_hidden @ 
% 1.13/1.36           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 1.13/1.36           (u1_struct_0 @ sk_B))
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) = (k4_tmap_1 @ sk_A @ sk_B)))),
% 1.13/1.36      inference('demod', [status(thm)], ['90', '91'])).
% 1.13/1.36  thf(t95_tmap_1, axiom,
% 1.13/1.36    (![A:$i]:
% 1.13/1.36     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.13/1.36       ( ![B:$i]:
% 1.13/1.36         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 1.13/1.36           ( ![C:$i]:
% 1.13/1.36             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 1.13/1.36               ( ( r2_hidden @ C @ ( u1_struct_0 @ B ) ) =>
% 1.13/1.36                 ( ( k1_funct_1 @ ( k4_tmap_1 @ A @ B ) @ C ) = ( C ) ) ) ) ) ) ) ))).
% 1.13/1.36  thf('238', plain,
% 1.13/1.36      (![X33 : $i, X34 : $i, X35 : $i]:
% 1.13/1.36         ((v2_struct_0 @ X33)
% 1.13/1.36          | ~ (m1_pre_topc @ X33 @ X34)
% 1.13/1.36          | ~ (r2_hidden @ X35 @ (u1_struct_0 @ X33))
% 1.13/1.36          | ((k1_funct_1 @ (k4_tmap_1 @ X34 @ X33) @ X35) = (X35))
% 1.13/1.36          | ~ (m1_subset_1 @ X35 @ (u1_struct_0 @ X34))
% 1.13/1.36          | ~ (l1_pre_topc @ X34)
% 1.13/1.36          | ~ (v2_pre_topc @ X34)
% 1.13/1.36          | (v2_struct_0 @ X34))),
% 1.13/1.36      inference('cnf', [status(esa)], [t95_tmap_1])).
% 1.13/1.36  thf('239', plain,
% 1.13/1.36      (![X0 : $i]:
% 1.13/1.36         (((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) = (k4_tmap_1 @ sk_A @ sk_B))
% 1.13/1.36          | (v2_struct_0 @ sk_B)
% 1.13/1.36          | (v2_struct_0 @ sk_A)
% 1.13/1.36          | (v2_struct_0 @ X0)
% 1.13/1.36          | ~ (v2_pre_topc @ X0)
% 1.13/1.36          | ~ (l1_pre_topc @ X0)
% 1.13/1.36          | ~ (m1_subset_1 @ 
% 1.13/1.36               (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 1.13/1.36               (u1_struct_0 @ X0))
% 1.13/1.36          | ((k1_funct_1 @ (k4_tmap_1 @ X0 @ sk_B) @ 
% 1.13/1.36              (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))
% 1.13/1.36              = (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))
% 1.13/1.36          | ~ (m1_pre_topc @ sk_B @ X0)
% 1.13/1.36          | (v2_struct_0 @ sk_B))),
% 1.13/1.36      inference('sup-', [status(thm)], ['237', '238'])).
% 1.13/1.36  thf('240', plain,
% 1.13/1.36      (![X0 : $i]:
% 1.13/1.36         (~ (m1_pre_topc @ sk_B @ X0)
% 1.13/1.36          | ((k1_funct_1 @ (k4_tmap_1 @ X0 @ sk_B) @ 
% 1.13/1.36              (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))
% 1.13/1.36              = (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))
% 1.13/1.36          | ~ (m1_subset_1 @ 
% 1.13/1.36               (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 1.13/1.36               (u1_struct_0 @ X0))
% 1.13/1.36          | ~ (l1_pre_topc @ X0)
% 1.13/1.36          | ~ (v2_pre_topc @ X0)
% 1.13/1.36          | (v2_struct_0 @ X0)
% 1.13/1.36          | (v2_struct_0 @ sk_A)
% 1.13/1.36          | (v2_struct_0 @ sk_B)
% 1.13/1.36          | ((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B)
% 1.13/1.36              = (k4_tmap_1 @ sk_A @ sk_B)))),
% 1.13/1.36      inference('simplify', [status(thm)], ['239'])).
% 1.13/1.36  thf('241', plain,
% 1.13/1.36      ((((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) = (k4_tmap_1 @ sk_A @ sk_B))
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | (v2_struct_0 @ sk_A)
% 1.13/1.36        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) = (k4_tmap_1 @ sk_A @ sk_B))
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | (v2_struct_0 @ sk_A)
% 1.13/1.36        | (v2_struct_0 @ sk_A)
% 1.13/1.36        | ~ (v2_pre_topc @ sk_A)
% 1.13/1.36        | ~ (l1_pre_topc @ sk_A)
% 1.13/1.36        | ((k1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 1.13/1.36            (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))
% 1.13/1.36            = (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))
% 1.13/1.36        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 1.13/1.36      inference('sup-', [status(thm)], ['236', '240'])).
% 1.13/1.36  thf('242', plain, ((v2_pre_topc @ sk_A)),
% 1.13/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.36  thf('243', plain, ((l1_pre_topc @ sk_A)),
% 1.13/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.36  thf('244', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.13/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.36  thf('245', plain,
% 1.13/1.36      ((((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) = (k4_tmap_1 @ sk_A @ sk_B))
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | (v2_struct_0 @ sk_A)
% 1.13/1.36        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) = (k4_tmap_1 @ sk_A @ sk_B))
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | (v2_struct_0 @ sk_A)
% 1.13/1.36        | (v2_struct_0 @ sk_A)
% 1.13/1.36        | ((k1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 1.13/1.36            (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))
% 1.13/1.36            = (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A)))),
% 1.13/1.36      inference('demod', [status(thm)], ['241', '242', '243', '244'])).
% 1.13/1.36  thf('246', plain,
% 1.13/1.36      ((((k1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 1.13/1.36          (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))
% 1.13/1.36          = (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))
% 1.13/1.36        | (v2_struct_0 @ sk_A)
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) = (k4_tmap_1 @ sk_A @ sk_B)))),
% 1.13/1.36      inference('simplify', [status(thm)], ['245'])).
% 1.13/1.36  thf('247', plain,
% 1.13/1.36      (((v2_struct_0 @ sk_A)
% 1.13/1.36        | (m1_subset_1 @ 
% 1.13/1.36           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 1.13/1.36           (u1_struct_0 @ sk_B))
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) = (k4_tmap_1 @ sk_A @ sk_B)))),
% 1.13/1.36      inference('demod', [status(thm)], ['221', '222'])).
% 1.13/1.36  thf('248', plain,
% 1.13/1.36      (![X0 : $i]:
% 1.13/1.36         (((k3_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.13/1.36            X0) = (k1_funct_1 @ sk_C @ X0))
% 1.13/1.36          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 1.13/1.36          | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 1.13/1.36      inference('demod', [status(thm)], ['159', '160', '161'])).
% 1.13/1.36  thf('249', plain,
% 1.13/1.36      ((((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) = (k4_tmap_1 @ sk_A @ sk_B))
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | (v2_struct_0 @ sk_A)
% 1.13/1.36        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.13/1.36        | ((k3_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.13/1.36            (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))
% 1.13/1.36            = (k1_funct_1 @ sk_C @ 
% 1.13/1.36               (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))))),
% 1.13/1.36      inference('sup-', [status(thm)], ['247', '248'])).
% 1.13/1.36  thf('250', plain,
% 1.13/1.36      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 1.13/1.36         ((v2_struct_0 @ X28)
% 1.13/1.36          | ~ (v2_pre_topc @ X28)
% 1.13/1.36          | ~ (l1_pre_topc @ X28)
% 1.13/1.36          | ~ (v1_funct_1 @ X29)
% 1.13/1.36          | ~ (v1_funct_2 @ X29 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X30))
% 1.13/1.36          | ~ (m1_subset_1 @ X29 @ 
% 1.13/1.36               (k1_zfmisc_1 @ 
% 1.13/1.36                (k2_zfmisc_1 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X30))))
% 1.13/1.36          | ((k3_funct_2 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X30) @ X29 @ 
% 1.13/1.36              (sk_F @ X31 @ X29 @ X32 @ X28 @ X30))
% 1.13/1.36              != (k1_funct_1 @ X31 @ (sk_F @ X31 @ X29 @ X32 @ X28 @ X30)))
% 1.13/1.36          | (r2_funct_2 @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X30) @ 
% 1.13/1.36             (k2_tmap_1 @ X28 @ X30 @ X29 @ X32) @ X31)
% 1.13/1.36          | ~ (m1_subset_1 @ X31 @ 
% 1.13/1.36               (k1_zfmisc_1 @ 
% 1.13/1.36                (k2_zfmisc_1 @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X30))))
% 1.13/1.36          | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X30))
% 1.13/1.36          | ~ (v1_funct_1 @ X31)
% 1.13/1.36          | ~ (m1_pre_topc @ X32 @ X28)
% 1.13/1.36          | (v2_struct_0 @ X32)
% 1.13/1.36          | ~ (l1_pre_topc @ X30)
% 1.13/1.36          | ~ (v2_pre_topc @ X30)
% 1.13/1.36          | (v2_struct_0 @ X30))),
% 1.13/1.36      inference('cnf', [status(esa)], [t59_tmap_1])).
% 1.13/1.36  thf('251', plain,
% 1.13/1.36      ((((k1_funct_1 @ sk_C @ 
% 1.13/1.36          (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))
% 1.13/1.36          != (k1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 1.13/1.36              (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A)))
% 1.13/1.36        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.13/1.36        | (v2_struct_0 @ sk_A)
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) = (k4_tmap_1 @ sk_A @ sk_B))
% 1.13/1.36        | (v2_struct_0 @ sk_A)
% 1.13/1.36        | ~ (v2_pre_topc @ sk_A)
% 1.13/1.36        | ~ (l1_pre_topc @ sk_A)
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | ~ (m1_pre_topc @ sk_B @ sk_B)
% 1.13/1.36        | ~ (v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))
% 1.13/1.36        | ~ (v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 1.13/1.36             (u1_struct_0 @ sk_A))
% 1.13/1.36        | ~ (m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 1.13/1.36             (k1_zfmisc_1 @ 
% 1.13/1.36              (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 1.13/1.36        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.13/1.36           (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) @ (k4_tmap_1 @ sk_A @ sk_B))
% 1.13/1.36        | ~ (m1_subset_1 @ sk_C @ 
% 1.13/1.36             (k1_zfmisc_1 @ 
% 1.13/1.36              (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 1.13/1.36        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.13/1.36        | ~ (v1_funct_1 @ sk_C)
% 1.13/1.36        | ~ (l1_pre_topc @ sk_B)
% 1.13/1.36        | ~ (v2_pre_topc @ sk_B)
% 1.13/1.36        | (v2_struct_0 @ sk_B))),
% 1.13/1.36      inference('sup-', [status(thm)], ['249', '250'])).
% 1.13/1.36  thf('252', plain, ((v2_pre_topc @ sk_A)),
% 1.13/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.36  thf('253', plain, ((l1_pre_topc @ sk_A)),
% 1.13/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.36  thf('254', plain, ((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))),
% 1.13/1.36      inference('clc', [status(thm)], ['63', '64'])).
% 1.13/1.36  thf('255', plain,
% 1.13/1.36      ((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 1.13/1.36        (u1_struct_0 @ sk_A))),
% 1.13/1.36      inference('clc', [status(thm)], ['55', '56'])).
% 1.13/1.36  thf('256', plain,
% 1.13/1.36      ((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 1.13/1.36        (k1_zfmisc_1 @ 
% 1.13/1.36         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.13/1.36      inference('clc', [status(thm)], ['31', '32'])).
% 1.13/1.36  thf('257', plain,
% 1.13/1.36      ((m1_subset_1 @ sk_C @ 
% 1.13/1.36        (k1_zfmisc_1 @ 
% 1.13/1.36         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.13/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.36  thf('258', plain,
% 1.13/1.36      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 1.13/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.36  thf('259', plain, ((v1_funct_1 @ sk_C)),
% 1.13/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.36  thf('260', plain, ((l1_pre_topc @ sk_B)),
% 1.13/1.36      inference('demod', [status(thm)], ['6', '7'])).
% 1.13/1.36  thf('261', plain, ((v2_pre_topc @ sk_B)),
% 1.13/1.36      inference('demod', [status(thm)], ['44', '45', '46'])).
% 1.13/1.36  thf('262', plain,
% 1.13/1.36      ((((k1_funct_1 @ sk_C @ 
% 1.13/1.36          (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))
% 1.13/1.36          != (k1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 1.13/1.36              (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A)))
% 1.13/1.36        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.13/1.36        | (v2_struct_0 @ sk_A)
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) = (k4_tmap_1 @ sk_A @ sk_B))
% 1.13/1.36        | (v2_struct_0 @ sk_A)
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | ~ (m1_pre_topc @ sk_B @ sk_B)
% 1.13/1.36        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.13/1.36           (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) @ (k4_tmap_1 @ sk_A @ sk_B))
% 1.13/1.36        | (v2_struct_0 @ sk_B))),
% 1.13/1.36      inference('demod', [status(thm)],
% 1.13/1.36                ['251', '252', '253', '254', '255', '256', '257', '258', 
% 1.13/1.36                 '259', '260', '261'])).
% 1.13/1.36  thf('263', plain,
% 1.13/1.36      (((r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.13/1.36         (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) @ (k4_tmap_1 @ sk_A @ sk_B))
% 1.13/1.36        | ~ (m1_pre_topc @ sk_B @ sk_B)
% 1.13/1.36        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) = (k4_tmap_1 @ sk_A @ sk_B))
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | (v2_struct_0 @ sk_A)
% 1.13/1.36        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.13/1.36        | ((k1_funct_1 @ sk_C @ 
% 1.13/1.36            (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))
% 1.13/1.36            != (k1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 1.13/1.36                (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))))),
% 1.13/1.36      inference('simplify', [status(thm)], ['262'])).
% 1.13/1.36  thf('264', plain,
% 1.13/1.36      ((((k1_funct_1 @ sk_C @ 
% 1.13/1.36          (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))
% 1.13/1.36          != (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))
% 1.13/1.36        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) = (k4_tmap_1 @ sk_A @ sk_B))
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | (v2_struct_0 @ sk_A)
% 1.13/1.36        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.13/1.36        | (v2_struct_0 @ sk_A)
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) = (k4_tmap_1 @ sk_A @ sk_B))
% 1.13/1.36        | ~ (m1_pre_topc @ sk_B @ sk_B)
% 1.13/1.36        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.13/1.36           (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) @ (k4_tmap_1 @ sk_A @ sk_B)))),
% 1.13/1.36      inference('sup-', [status(thm)], ['246', '263'])).
% 1.13/1.36  thf('265', plain,
% 1.13/1.36      (((r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.13/1.36         (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) @ (k4_tmap_1 @ sk_A @ sk_B))
% 1.13/1.36        | ~ (m1_pre_topc @ sk_B @ sk_B)
% 1.13/1.36        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.13/1.36        | (v2_struct_0 @ sk_A)
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) = (k4_tmap_1 @ sk_A @ sk_B))
% 1.13/1.36        | ((k1_funct_1 @ sk_C @ 
% 1.13/1.36            (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))
% 1.13/1.36            != (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A)))),
% 1.13/1.36      inference('simplify', [status(thm)], ['264'])).
% 1.13/1.36  thf('266', plain,
% 1.13/1.36      ((((sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A)
% 1.13/1.36          != (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))
% 1.13/1.36        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) = (k4_tmap_1 @ sk_A @ sk_B))
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | (v2_struct_0 @ sk_A)
% 1.13/1.36        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) = (k4_tmap_1 @ sk_A @ sk_B))
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | (v2_struct_0 @ sk_A)
% 1.13/1.36        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.13/1.36        | ~ (m1_pre_topc @ sk_B @ sk_B)
% 1.13/1.36        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.13/1.36           (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) @ (k4_tmap_1 @ sk_A @ sk_B)))),
% 1.13/1.36      inference('sup-', [status(thm)], ['235', '265'])).
% 1.13/1.36  thf('267', plain,
% 1.13/1.36      (((r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.13/1.36         (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) @ (k4_tmap_1 @ sk_A @ sk_B))
% 1.13/1.36        | ~ (m1_pre_topc @ sk_B @ sk_B)
% 1.13/1.36        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.13/1.36        | (v2_struct_0 @ sk_A)
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) = (k4_tmap_1 @ sk_A @ sk_B)))),
% 1.13/1.36      inference('simplify', [status(thm)], ['266'])).
% 1.13/1.36  thf('268', plain,
% 1.13/1.36      ((~ (l1_pre_topc @ sk_B)
% 1.13/1.36        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) = (k4_tmap_1 @ sk_A @ sk_B))
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | (v2_struct_0 @ sk_A)
% 1.13/1.36        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.13/1.36        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.13/1.36           (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) @ (k4_tmap_1 @ sk_A @ sk_B)))),
% 1.13/1.36      inference('sup-', [status(thm)], ['196', '267'])).
% 1.13/1.36  thf('269', plain, ((l1_pre_topc @ sk_B)),
% 1.13/1.36      inference('demod', [status(thm)], ['6', '7'])).
% 1.13/1.36  thf('270', plain,
% 1.13/1.36      ((((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) = (k4_tmap_1 @ sk_A @ sk_B))
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | (v2_struct_0 @ sk_A)
% 1.13/1.36        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.13/1.36        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.13/1.36           (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) @ (k4_tmap_1 @ sk_A @ sk_B)))),
% 1.13/1.36      inference('demod', [status(thm)], ['268', '269'])).
% 1.13/1.36  thf('271', plain,
% 1.13/1.36      (((r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.13/1.36         (k4_tmap_1 @ sk_A @ sk_B))
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | (v2_struct_0 @ sk_A)
% 1.13/1.36        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.13/1.36        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.13/1.36        | (v2_struct_0 @ sk_A)
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) = (k4_tmap_1 @ sk_A @ sk_B)))),
% 1.13/1.36      inference('sup+', [status(thm)], ['195', '270'])).
% 1.13/1.36  thf('272', plain,
% 1.13/1.36      ((((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) = (k4_tmap_1 @ sk_A @ sk_B))
% 1.13/1.36        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.13/1.36        | (v2_struct_0 @ sk_A)
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.13/1.36           (k4_tmap_1 @ sk_A @ sk_B)))),
% 1.13/1.36      inference('simplify', [status(thm)], ['271'])).
% 1.13/1.36  thf('273', plain,
% 1.13/1.36      ((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 1.13/1.36        (k1_zfmisc_1 @ 
% 1.13/1.36         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.13/1.36      inference('clc', [status(thm)], ['31', '32'])).
% 1.13/1.36  thf('274', plain,
% 1.13/1.36      (![X0 : $i]:
% 1.13/1.36         ((v1_funct_1 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0))
% 1.13/1.36          | ~ (l1_struct_0 @ X0))),
% 1.13/1.36      inference('demod', [status(thm)], ['3', '10', '13', '14', '15'])).
% 1.13/1.36  thf('275', plain,
% 1.13/1.36      (![X0 : $i]:
% 1.13/1.36         ((v1_funct_2 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ 
% 1.13/1.36           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 1.13/1.36          | ~ (l1_struct_0 @ X0))),
% 1.13/1.36      inference('demod', [status(thm)], ['19', '20', '21', '22', '23'])).
% 1.13/1.36  thf('276', plain,
% 1.13/1.36      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.13/1.36        | (v2_struct_0 @ sk_A)
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) = (sk_C)))),
% 1.13/1.36      inference('demod', [status(thm)], ['192', '193'])).
% 1.13/1.36  thf('277', plain,
% 1.13/1.36      (![X0 : $i, X1 : $i]:
% 1.13/1.36         (~ (l1_struct_0 @ X0)
% 1.13/1.36          | ~ (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 1.13/1.36               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ X1)
% 1.13/1.36          | ((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) = (X1))
% 1.13/1.36          | ~ (m1_subset_1 @ X1 @ 
% 1.13/1.36               (k1_zfmisc_1 @ 
% 1.13/1.36                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 1.13/1.36          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 1.13/1.36          | ~ (v1_funct_1 @ X1)
% 1.13/1.36          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0))
% 1.13/1.36          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ 
% 1.13/1.36               (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A)))),
% 1.13/1.36      inference('sup-', [status(thm)], ['78', '79'])).
% 1.13/1.36  thf('278', plain,
% 1.13/1.36      (![X0 : $i]:
% 1.13/1.36         (~ (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.13/1.36             X0)
% 1.13/1.36          | (v2_struct_0 @ sk_B)
% 1.13/1.36          | (v2_struct_0 @ sk_A)
% 1.13/1.36          | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.13/1.36          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) @ 
% 1.13/1.36               (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.13/1.36          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 1.13/1.36          | ~ (v1_funct_1 @ X0)
% 1.13/1.36          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.13/1.36          | ~ (m1_subset_1 @ X0 @ 
% 1.13/1.36               (k1_zfmisc_1 @ 
% 1.13/1.36                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 1.13/1.36          | ((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) = (X0))
% 1.13/1.36          | ~ (l1_struct_0 @ sk_B))),
% 1.13/1.36      inference('sup-', [status(thm)], ['276', '277'])).
% 1.13/1.36  thf('279', plain, ((l1_struct_0 @ sk_B)),
% 1.13/1.36      inference('sup-', [status(thm)], ['8', '9'])).
% 1.13/1.36  thf('280', plain,
% 1.13/1.36      (![X0 : $i]:
% 1.13/1.36         (~ (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.13/1.36             X0)
% 1.13/1.36          | (v2_struct_0 @ sk_B)
% 1.13/1.36          | (v2_struct_0 @ sk_A)
% 1.13/1.36          | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.13/1.36          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) @ 
% 1.13/1.36               (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.13/1.36          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 1.13/1.36          | ~ (v1_funct_1 @ X0)
% 1.13/1.36          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.13/1.36          | ~ (m1_subset_1 @ X0 @ 
% 1.13/1.36               (k1_zfmisc_1 @ 
% 1.13/1.36                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 1.13/1.36          | ((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) = (X0)))),
% 1.13/1.36      inference('demod', [status(thm)], ['278', '279'])).
% 1.13/1.36  thf('281', plain,
% 1.13/1.36      (![X0 : $i]:
% 1.13/1.36         (~ (l1_struct_0 @ sk_B)
% 1.13/1.36          | ((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) = (X0))
% 1.13/1.36          | ~ (m1_subset_1 @ X0 @ 
% 1.13/1.36               (k1_zfmisc_1 @ 
% 1.13/1.36                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 1.13/1.36          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.13/1.36          | ~ (v1_funct_1 @ X0)
% 1.13/1.36          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 1.13/1.36          | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.13/1.36          | (v2_struct_0 @ sk_A)
% 1.13/1.36          | (v2_struct_0 @ sk_B)
% 1.13/1.36          | ~ (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.13/1.36               sk_C @ X0))),
% 1.13/1.36      inference('sup-', [status(thm)], ['275', '280'])).
% 1.13/1.36  thf('282', plain, ((l1_struct_0 @ sk_B)),
% 1.13/1.36      inference('sup-', [status(thm)], ['8', '9'])).
% 1.13/1.36  thf('283', plain,
% 1.13/1.36      (![X0 : $i]:
% 1.13/1.36         (((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) = (X0))
% 1.13/1.36          | ~ (m1_subset_1 @ X0 @ 
% 1.13/1.36               (k1_zfmisc_1 @ 
% 1.13/1.36                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 1.13/1.36          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.13/1.36          | ~ (v1_funct_1 @ X0)
% 1.13/1.36          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 1.13/1.36          | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.13/1.36          | (v2_struct_0 @ sk_A)
% 1.13/1.36          | (v2_struct_0 @ sk_B)
% 1.13/1.36          | ~ (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.13/1.36               sk_C @ X0))),
% 1.13/1.36      inference('demod', [status(thm)], ['281', '282'])).
% 1.13/1.36  thf('284', plain,
% 1.13/1.36      (![X0 : $i]:
% 1.13/1.36         (~ (l1_struct_0 @ sk_B)
% 1.13/1.36          | ~ (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.13/1.36               sk_C @ X0)
% 1.13/1.36          | (v2_struct_0 @ sk_B)
% 1.13/1.36          | (v2_struct_0 @ sk_A)
% 1.13/1.36          | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.13/1.36          | ~ (v1_funct_1 @ X0)
% 1.13/1.36          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.13/1.36          | ~ (m1_subset_1 @ X0 @ 
% 1.13/1.36               (k1_zfmisc_1 @ 
% 1.13/1.36                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 1.13/1.36          | ((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) = (X0)))),
% 1.13/1.36      inference('sup-', [status(thm)], ['274', '283'])).
% 1.13/1.36  thf('285', plain, ((l1_struct_0 @ sk_B)),
% 1.13/1.36      inference('sup-', [status(thm)], ['8', '9'])).
% 1.13/1.36  thf('286', plain,
% 1.13/1.36      (![X0 : $i]:
% 1.13/1.36         (~ (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.13/1.36             X0)
% 1.13/1.36          | (v2_struct_0 @ sk_B)
% 1.13/1.36          | (v2_struct_0 @ sk_A)
% 1.13/1.36          | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.13/1.36          | ~ (v1_funct_1 @ X0)
% 1.13/1.36          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.13/1.36          | ~ (m1_subset_1 @ X0 @ 
% 1.13/1.36               (k1_zfmisc_1 @ 
% 1.13/1.36                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 1.13/1.36          | ((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) = (X0)))),
% 1.13/1.36      inference('demod', [status(thm)], ['284', '285'])).
% 1.13/1.36  thf('287', plain,
% 1.13/1.36      ((((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) = (k4_tmap_1 @ sk_A @ sk_B))
% 1.13/1.36        | ~ (v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 1.13/1.36             (u1_struct_0 @ sk_A))
% 1.13/1.36        | ~ (v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))
% 1.13/1.36        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.13/1.36        | (v2_struct_0 @ sk_A)
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | ~ (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.13/1.36             (k4_tmap_1 @ sk_A @ sk_B)))),
% 1.13/1.36      inference('sup-', [status(thm)], ['273', '286'])).
% 1.13/1.36  thf('288', plain,
% 1.13/1.36      ((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 1.13/1.36        (u1_struct_0 @ sk_A))),
% 1.13/1.36      inference('clc', [status(thm)], ['55', '56'])).
% 1.13/1.36  thf('289', plain, ((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))),
% 1.13/1.36      inference('clc', [status(thm)], ['63', '64'])).
% 1.13/1.36  thf('290', plain,
% 1.13/1.36      ((((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) = (k4_tmap_1 @ sk_A @ sk_B))
% 1.13/1.36        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.13/1.36        | (v2_struct_0 @ sk_A)
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | ~ (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.13/1.36             (k4_tmap_1 @ sk_A @ sk_B)))),
% 1.13/1.36      inference('demod', [status(thm)], ['287', '288', '289'])).
% 1.13/1.36  thf('291', plain,
% 1.13/1.36      (((v2_struct_0 @ sk_B)
% 1.13/1.36        | (v2_struct_0 @ sk_A)
% 1.13/1.36        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.13/1.36        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) = (k4_tmap_1 @ sk_A @ sk_B))
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | (v2_struct_0 @ sk_A)
% 1.13/1.36        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.13/1.36        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) = (k4_tmap_1 @ sk_A @ sk_B)))),
% 1.13/1.36      inference('sup-', [status(thm)], ['272', '290'])).
% 1.13/1.36  thf('292', plain,
% 1.13/1.36      ((((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) = (k4_tmap_1 @ sk_A @ sk_B))
% 1.13/1.36        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.13/1.36        | (v2_struct_0 @ sk_A)
% 1.13/1.36        | (v2_struct_0 @ sk_B))),
% 1.13/1.36      inference('simplify', [status(thm)], ['291'])).
% 1.13/1.36  thf('293', plain,
% 1.13/1.36      ((((sk_C) = (k4_tmap_1 @ sk_A @ sk_B))
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | (v2_struct_0 @ sk_A)
% 1.13/1.36        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | (v2_struct_0 @ sk_A)
% 1.13/1.36        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 1.13/1.36      inference('sup+', [status(thm)], ['194', '292'])).
% 1.13/1.36  thf('294', plain,
% 1.13/1.36      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.13/1.36        | (v2_struct_0 @ sk_A)
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | ((sk_C) = (k4_tmap_1 @ sk_A @ sk_B)))),
% 1.13/1.36      inference('simplify', [status(thm)], ['293'])).
% 1.13/1.36  thf('295', plain,
% 1.13/1.36      (~ (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.13/1.36          (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)),
% 1.13/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.36  thf('296', plain,
% 1.13/1.36      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.13/1.36           sk_C)
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | (v2_struct_0 @ sk_A)
% 1.13/1.36        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 1.13/1.36      inference('sup-', [status(thm)], ['294', '295'])).
% 1.13/1.36  thf('297', plain,
% 1.13/1.36      ((m1_subset_1 @ sk_C @ 
% 1.13/1.36        (k1_zfmisc_1 @ 
% 1.13/1.36         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.13/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.36  thf('298', plain,
% 1.13/1.36      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 1.13/1.36         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9)))
% 1.13/1.36          | ~ (v1_funct_2 @ X7 @ X8 @ X9)
% 1.13/1.36          | ~ (v1_funct_1 @ X7)
% 1.13/1.36          | ~ (v1_funct_1 @ X10)
% 1.13/1.36          | ~ (v1_funct_2 @ X10 @ X8 @ X9)
% 1.13/1.36          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9)))
% 1.13/1.36          | (r2_funct_2 @ X8 @ X9 @ X7 @ X10)
% 1.13/1.36          | ((X7) != (X10)))),
% 1.13/1.36      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 1.13/1.36  thf('299', plain,
% 1.13/1.36      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.13/1.36         ((r2_funct_2 @ X8 @ X9 @ X10 @ X10)
% 1.13/1.36          | ~ (v1_funct_1 @ X10)
% 1.13/1.36          | ~ (v1_funct_2 @ X10 @ X8 @ X9)
% 1.13/1.36          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 1.13/1.36      inference('simplify', [status(thm)], ['298'])).
% 1.13/1.36  thf('300', plain,
% 1.13/1.36      ((~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.13/1.36        | ~ (v1_funct_1 @ sk_C)
% 1.13/1.36        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.13/1.36           sk_C))),
% 1.13/1.36      inference('sup-', [status(thm)], ['297', '299'])).
% 1.13/1.36  thf('301', plain,
% 1.13/1.36      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 1.13/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.36  thf('302', plain, ((v1_funct_1 @ sk_C)),
% 1.13/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.36  thf('303', plain,
% 1.13/1.36      ((r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ sk_C)),
% 1.13/1.36      inference('demod', [status(thm)], ['300', '301', '302'])).
% 1.13/1.36  thf('304', plain,
% 1.13/1.36      (((v2_struct_0 @ sk_B)
% 1.13/1.36        | (v2_struct_0 @ sk_A)
% 1.13/1.36        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 1.13/1.36      inference('demod', [status(thm)], ['296', '303'])).
% 1.13/1.36  thf('305', plain, (~ (v2_struct_0 @ sk_B)),
% 1.13/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.36  thf('306', plain,
% 1.13/1.36      (((v1_xboole_0 @ (u1_struct_0 @ sk_B)) | (v2_struct_0 @ sk_A))),
% 1.13/1.36      inference('clc', [status(thm)], ['304', '305'])).
% 1.13/1.36  thf('307', plain, (~ (v2_struct_0 @ sk_A)),
% 1.13/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.36  thf('308', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_B))),
% 1.13/1.36      inference('clc', [status(thm)], ['306', '307'])).
% 1.13/1.36  thf('309', plain,
% 1.13/1.36      (![X27 : $i]: ((m1_pre_topc @ X27 @ X27) | ~ (l1_pre_topc @ X27))),
% 1.13/1.36      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.13/1.36  thf(t1_tsep_1, axiom,
% 1.13/1.36    (![A:$i]:
% 1.13/1.36     ( ( l1_pre_topc @ A ) =>
% 1.13/1.36       ( ![B:$i]:
% 1.13/1.36         ( ( m1_pre_topc @ B @ A ) =>
% 1.13/1.36           ( m1_subset_1 @
% 1.13/1.36             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 1.13/1.36  thf('310', plain,
% 1.13/1.36      (![X25 : $i, X26 : $i]:
% 1.13/1.36         (~ (m1_pre_topc @ X25 @ X26)
% 1.13/1.36          | (m1_subset_1 @ (u1_struct_0 @ X25) @ 
% 1.13/1.36             (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 1.13/1.36          | ~ (l1_pre_topc @ X26))),
% 1.13/1.36      inference('cnf', [status(esa)], [t1_tsep_1])).
% 1.13/1.36  thf('311', plain,
% 1.13/1.36      (![X0 : $i]:
% 1.13/1.36         (~ (l1_pre_topc @ X0)
% 1.13/1.36          | ~ (l1_pre_topc @ X0)
% 1.13/1.36          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 1.13/1.36             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 1.13/1.36      inference('sup-', [status(thm)], ['309', '310'])).
% 1.13/1.36  thf('312', plain,
% 1.13/1.36      (![X0 : $i]:
% 1.13/1.36         ((m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 1.13/1.36           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 1.13/1.36          | ~ (l1_pre_topc @ X0))),
% 1.13/1.36      inference('simplify', [status(thm)], ['311'])).
% 1.13/1.36  thf(t5_subset, axiom,
% 1.13/1.36    (![A:$i,B:$i,C:$i]:
% 1.13/1.36     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 1.13/1.36          ( v1_xboole_0 @ C ) ) ))).
% 1.13/1.36  thf('313', plain,
% 1.13/1.36      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.13/1.36         (~ (r2_hidden @ X0 @ X1)
% 1.13/1.36          | ~ (v1_xboole_0 @ X2)
% 1.13/1.36          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 1.13/1.36      inference('cnf', [status(esa)], [t5_subset])).
% 1.13/1.36  thf('314', plain,
% 1.13/1.36      (![X0 : $i, X1 : $i]:
% 1.13/1.36         (~ (l1_pre_topc @ X0)
% 1.13/1.36          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0))
% 1.13/1.36          | ~ (r2_hidden @ X1 @ (u1_struct_0 @ X0)))),
% 1.13/1.36      inference('sup-', [status(thm)], ['312', '313'])).
% 1.13/1.36  thf('315', plain,
% 1.13/1.36      (![X0 : $i]:
% 1.13/1.36         (~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_B)) | ~ (l1_pre_topc @ sk_B))),
% 1.13/1.36      inference('sup-', [status(thm)], ['308', '314'])).
% 1.13/1.36  thf('316', plain, ((l1_pre_topc @ sk_B)),
% 1.13/1.36      inference('demod', [status(thm)], ['6', '7'])).
% 1.13/1.36  thf('317', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_B))),
% 1.13/1.36      inference('demod', [status(thm)], ['315', '316'])).
% 1.13/1.36  thf('318', plain,
% 1.13/1.36      ((((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) = (sk_C))
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | (v2_struct_0 @ sk_A))),
% 1.13/1.36      inference('sup-', [status(thm)], ['118', '317'])).
% 1.13/1.36  thf('319', plain, (~ (v2_struct_0 @ sk_B)),
% 1.13/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.36  thf('320', plain,
% 1.13/1.36      (((v2_struct_0 @ sk_A)
% 1.13/1.36        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) = (sk_C)))),
% 1.13/1.36      inference('clc', [status(thm)], ['318', '319'])).
% 1.13/1.36  thf('321', plain, (~ (v2_struct_0 @ sk_A)),
% 1.13/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.36  thf('322', plain, (((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) = (sk_C))),
% 1.13/1.36      inference('clc', [status(thm)], ['320', '321'])).
% 1.13/1.36  thf('323', plain,
% 1.13/1.36      (((v2_struct_0 @ sk_A)
% 1.13/1.36        | (r2_hidden @ 
% 1.13/1.36           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 1.13/1.36           (u1_struct_0 @ sk_B))
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | ((sk_C) = (k4_tmap_1 @ sk_A @ sk_B)))),
% 1.13/1.36      inference('demod', [status(thm)], ['92', '322'])).
% 1.13/1.36  thf('324', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_B))),
% 1.13/1.36      inference('demod', [status(thm)], ['315', '316'])).
% 1.13/1.36  thf('325', plain,
% 1.13/1.36      ((((sk_C) = (k4_tmap_1 @ sk_A @ sk_B))
% 1.13/1.36        | (v2_struct_0 @ sk_B)
% 1.13/1.36        | (v2_struct_0 @ sk_A))),
% 1.13/1.36      inference('sup-', [status(thm)], ['323', '324'])).
% 1.13/1.36  thf('326', plain, (~ (v2_struct_0 @ sk_B)),
% 1.13/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.36  thf('327', plain,
% 1.13/1.36      (((v2_struct_0 @ sk_A) | ((sk_C) = (k4_tmap_1 @ sk_A @ sk_B)))),
% 1.13/1.36      inference('clc', [status(thm)], ['325', '326'])).
% 1.13/1.36  thf('328', plain, (~ (v2_struct_0 @ sk_A)),
% 1.13/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.36  thf('329', plain, (((sk_C) = (k4_tmap_1 @ sk_A @ sk_B))),
% 1.13/1.36      inference('clc', [status(thm)], ['327', '328'])).
% 1.13/1.36  thf('330', plain,
% 1.13/1.36      ((r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ sk_C)),
% 1.13/1.36      inference('demod', [status(thm)], ['300', '301', '302'])).
% 1.13/1.36  thf('331', plain, ($false),
% 1.13/1.36      inference('demod', [status(thm)], ['0', '329', '330'])).
% 1.13/1.36  
% 1.13/1.36  % SZS output end Refutation
% 1.13/1.36  
% 1.13/1.37  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
