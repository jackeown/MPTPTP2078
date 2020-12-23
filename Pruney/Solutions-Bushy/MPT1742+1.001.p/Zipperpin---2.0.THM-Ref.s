%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1742+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.I21ohnr2T6

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:54:10 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :  280 (2580 expanded)
%              Number of leaves         :   35 ( 759 expanded)
%              Depth                    :   39
%              Number of atoms          : 4841 (140897 expanded)
%              Number of equality atoms :   42 (2909 expanded)
%              Maximal formula depth    :   27 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_E_1_type,type,(
    sk_E_1: $i )).

thf(sk_F_1_type,type,(
    sk_F_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i > $i > $i )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(r1_funct_2_type,type,(
    r1_funct_2: $i > $i > $i > $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t51_tmap_1,conjecture,(
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
                & ( v2_pre_topc @ C )
                & ( l1_pre_topc @ C ) )
             => ( ( ( ( u1_struct_0 @ A )
                    = ( u1_struct_0 @ B ) )
                  & ( r1_tarski @ ( u1_pre_topc @ B ) @ ( u1_pre_topc @ A ) ) )
               => ! [D: $i] :
                    ( ( ( v1_funct_1 @ D )
                      & ( v1_funct_2 @ D @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ C ) )
                      & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ C ) ) ) ) )
                   => ! [E: $i] :
                        ( ( ( v1_funct_1 @ E )
                          & ( v1_funct_2 @ E @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) )
                          & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) ) ) )
                       => ( ( r1_funct_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) @ D @ E )
                         => ! [F: $i] :
                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ A ) )
                             => ! [G: $i] :
                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ B ) )
                                 => ( ( ( F = G )
                                      & ( r1_tmap_1 @ B @ C @ E @ G ) )
                                   => ( r1_tmap_1 @ A @ C @ D @ F ) ) ) ) ) ) ) ) ) ) ) )).

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
                  & ( v2_pre_topc @ C )
                  & ( l1_pre_topc @ C ) )
               => ( ( ( ( u1_struct_0 @ A )
                      = ( u1_struct_0 @ B ) )
                    & ( r1_tarski @ ( u1_pre_topc @ B ) @ ( u1_pre_topc @ A ) ) )
                 => ! [D: $i] :
                      ( ( ( v1_funct_1 @ D )
                        & ( v1_funct_2 @ D @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ C ) )
                        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ C ) ) ) ) )
                     => ! [E: $i] :
                          ( ( ( v1_funct_1 @ E )
                            & ( v1_funct_2 @ E @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) )
                            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) ) ) )
                         => ( ( r1_funct_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) @ D @ E )
                           => ! [F: $i] :
                                ( ( m1_subset_1 @ F @ ( u1_struct_0 @ A ) )
                               => ! [G: $i] :
                                    ( ( m1_subset_1 @ G @ ( u1_struct_0 @ B ) )
                                   => ( ( ( F = G )
                                        & ( r1_tmap_1 @ B @ C @ E @ G ) )
                                     => ( r1_tmap_1 @ A @ C @ D @ F ) ) ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t51_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    sk_F_1 = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ sk_F_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['1','2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_tmap_1,axiom,(
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
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                 => ( ( r1_tmap_1 @ A @ B @ C @ D )
                  <=> ! [E: $i] :
                        ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                       => ~ ( ( v3_pre_topc @ E @ B )
                            & ( r2_hidden @ ( k3_funct_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ E )
                            & ! [F: $i] :
                                ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                               => ~ ( ( v3_pre_topc @ F @ A )
                                    & ( r2_hidden @ D @ F )
                                    & ( r1_tarski @ ( k7_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ F ) @ E ) ) ) ) ) ) ) ) ) ) )).

thf('6',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( v2_struct_0 @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X15 ) )
      | ( v3_pre_topc @ ( sk_E @ X14 @ X16 @ X13 @ X15 ) @ X13 )
      | ( r1_tmap_1 @ X15 @ X13 @ X16 @ X14 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X13 ) ) ) )
      | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X13 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_tmap_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) )
      | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ X0 )
      | ( v3_pre_topc @ ( sk_E @ X0 @ sk_D @ sk_C @ sk_A ) @ sk_C )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_C )
      | ~ ( v2_pre_topc @ sk_C )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    l1_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v2_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ X0 )
      | ( v3_pre_topc @ ( sk_E @ X0 @ sk_D @ sk_C @ sk_A ) @ sk_C )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['7','8','9','10','11','12','13'])).

thf('15',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v3_pre_topc @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_C )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_F_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['1','2','3'])).

thf('17',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( v2_struct_0 @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X15 ) )
      | ( m1_subset_1 @ ( sk_E @ X14 @ X16 @ X13 @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( r1_tmap_1 @ X15 @ X13 @ X16 @ X14 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X13 ) ) ) )
      | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X13 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_tmap_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) )
      | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ X0 )
      | ( m1_subset_1 @ ( sk_E @ X0 @ sk_D @ sk_C @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_C )
      | ~ ( v2_pre_topc @ sk_C )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    l1_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v2_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ X0 )
      | ( m1_subset_1 @ ( sk_E @ X0 @ sk_D @ sk_C @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['19','20','21','22','23','24','25'])).

thf('27',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( m1_subset_1 @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['16','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_F_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['1','2','3'])).

thf('29',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( v2_struct_0 @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X15 ) )
      | ( r2_hidden @ ( k3_funct_2 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X13 ) @ X16 @ X14 ) @ ( sk_E @ X14 @ X16 @ X13 @ X15 ) )
      | ( r1_tmap_1 @ X15 @ X13 @ X16 @ X14 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X13 ) ) ) )
      | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X13 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_tmap_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) )
      | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ X0 )
      | ( r2_hidden @ ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ sk_D @ X0 ) @ ( sk_E @ X0 @ sk_D @ sk_C @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_C )
      | ~ ( v2_pre_topc @ sk_C )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    l1_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v2_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ X0 )
      | ( r2_hidden @ ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ sk_D @ X0 ) @ ( sk_E @ X0 @ sk_D @ sk_C @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['31','32','33','34','35','36','37'])).

thf('39',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( r2_hidden @ ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ sk_D @ sk_F_1 ) @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['28','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X18: $i] :
      ( ( v2_struct_0 @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X15 ) )
      | ~ ( r1_tmap_1 @ X15 @ X13 @ X16 @ X14 )
      | ( v3_pre_topc @ ( sk_F @ X18 @ X14 @ X16 @ X13 @ X15 ) @ X15 )
      | ~ ( r2_hidden @ ( k3_funct_2 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X13 ) @ X16 @ X14 ) @ X18 )
      | ~ ( v3_pre_topc @ X18 @ X13 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X13 ) ) ) )
      | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X13 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_tmap_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v3_pre_topc @ X2 @ X0 )
      | ~ ( r2_hidden @ ( k3_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X0 ) @ X1 @ X3 ) @ X2 )
      | ( v3_pre_topc @ ( sk_F @ X2 @ X3 @ X1 @ X0 @ sk_B ) @ sk_B )
      | ~ ( r1_tmap_1 @ sk_B @ X0 @ X1 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v3_pre_topc @ X2 @ X0 )
      | ~ ( r2_hidden @ ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) @ X1 @ X3 ) @ X2 )
      | ( v3_pre_topc @ ( sk_F @ X2 @ X3 @ X1 @ X0 @ sk_B ) @ sk_B )
      | ~ ( r1_tmap_1 @ sk_B @ X0 @ X1 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['43','44','45','46','47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ~ ( v2_pre_topc @ sk_C )
      | ~ ( l1_pre_topc @ sk_C )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_tmap_1 @ sk_B @ sk_C @ sk_D @ X0 )
      | ( v3_pre_topc @ ( sk_F @ X1 @ X0 @ sk_D @ sk_C @ sk_B ) @ sk_B )
      | ~ ( r2_hidden @ ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ sk_D @ X0 ) @ X1 )
      | ~ ( v3_pre_topc @ X1 @ sk_C )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) )
      | ~ ( v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) )
      | ~ ( v1_funct_1 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['40','49'])).

thf('51',plain,(
    v2_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    l1_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_tmap_1 @ sk_B @ sk_C @ sk_D @ X0 )
      | ( v3_pre_topc @ ( sk_F @ X1 @ X0 @ sk_D @ sk_C @ sk_B ) @ sk_B )
      | ~ ( r2_hidden @ ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ sk_D @ X0 ) @ X1 )
      | ~ ( v3_pre_topc @ X1 @ sk_C )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['50','51','52','53','54'])).

thf('56',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_subset_1 @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( v3_pre_topc @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_C )
    | ( v3_pre_topc @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_C @ sk_B ) @ sk_B )
    | ~ ( r1_tmap_1 @ sk_B @ sk_C @ sk_D @ sk_F_1 )
    | ~ ( m1_subset_1 @ sk_F_1 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['39','55'])).

thf('57',plain,(
    r1_tmap_1 @ sk_B @ sk_C @ sk_E_1 @ sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    sk_F_1 = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    r1_tmap_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F_1 ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( r2_hidden @ ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ sk_D @ sk_F_1 ) @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['28','38'])).

thf('61',plain,(
    r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) @ sk_D @ sk_E_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ sk_D @ sk_E_1 ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_r1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ~ ( v1_xboole_0 @ B )
        & ~ ( v1_xboole_0 @ D )
        & ( v1_funct_1 @ E )
        & ( v1_funct_2 @ E @ A @ B )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( v1_funct_2 @ F @ C @ D )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( r1_funct_2 @ A @ B @ C @ D @ E @ F )
      <=> ( E = F ) ) ) )).

thf('65',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) )
      | ~ ( v1_funct_2 @ X2 @ X3 @ X4 )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_xboole_0 @ X5 )
      | ( v1_xboole_0 @ X4 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_funct_2 @ X6 @ X7 @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X5 ) ) )
      | ( X2 = X6 )
      | ~ ( r1_funct_2 @ X3 @ X4 @ X7 @ X5 @ X2 @ X6 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_funct_2])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ X2 @ X1 @ sk_D @ X0 )
      | ( sk_D = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_2 @ X0 @ X2 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
      | ( v1_xboole_0 @ X1 )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ X2 @ X1 @ sk_D @ X0 )
      | ( sk_D = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_2 @ X0 @ X2 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_E_1 )
    | ~ ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) )
    | ~ ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) ) ) )
    | ( sk_D = sk_E_1 ) ),
    inference('sup-',[status(thm)],['63','69'])).

thf('71',plain,(
    v1_funct_1 @ sk_E_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( sk_D = sk_E_1 ) ),
    inference(demod,[status(thm)],['70','71','74','77'])).

thf('79',plain,
    ( ( sk_D = sk_E_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( m1_subset_1 @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['16','26'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('81',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X22 @ X23 )
      | ~ ( v1_xboole_0 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
      | ( v2_struct_0 @ sk_C )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
      | ~ ( r2_hidden @ X0 @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( sk_D = sk_E_1 )
      | ~ ( r2_hidden @ X0 @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) )
      | ( v2_struct_0 @ sk_C )
      | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['79','82'])).

thf('84',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_C )
    | ( sk_D = sk_E_1 ) ),
    inference('sup-',[status(thm)],['60','83'])).

thf('85',plain,
    ( ( sk_D = sk_E_1 )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    ~ ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( sk_D = sk_E_1 ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( sk_D = sk_E_1 )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['87','88'])).

thf('90',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    sk_D = sk_E_1 ),
    inference(clc,[status(thm)],['89','90'])).

thf('92',plain,(
    r1_tmap_1 @ sk_B @ sk_C @ sk_D @ sk_F_1 ),
    inference(demod,[status(thm)],['59','91'])).

thf('93',plain,(
    m1_subset_1 @ sk_F_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['1','2','3'])).

thf('94',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_subset_1 @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( v3_pre_topc @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_C )
    | ( v3_pre_topc @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_C @ sk_B ) @ sk_B )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['56','92','93'])).

thf('95',plain,
    ( ( v3_pre_topc @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_C @ sk_B ) @ sk_B )
    | ~ ( v3_pre_topc @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_C )
    | ~ ( m1_subset_1 @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ~ ( v3_pre_topc @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_C )
    | ( v3_pre_topc @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_C @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['27','95'])).

thf('97',plain,
    ( ( v3_pre_topc @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_C @ sk_B ) @ sk_B )
    | ~ ( v3_pre_topc @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v3_pre_topc @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_C @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['15','97'])).

thf('99',plain,
    ( ( v3_pre_topc @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_C @ sk_B ) @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v3_pre_topc @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_C )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','14'])).

thf('101',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( m1_subset_1 @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['16','26'])).

thf('102',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( r2_hidden @ ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ sk_D @ sk_F_1 ) @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['28','38'])).

thf('103',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X18: $i] :
      ( ( v2_struct_0 @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X15 ) )
      | ~ ( r1_tmap_1 @ X15 @ X13 @ X16 @ X14 )
      | ( m1_subset_1 @ ( sk_F @ X18 @ X14 @ X16 @ X13 @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( r2_hidden @ ( k3_funct_2 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X13 ) @ X16 @ X14 ) @ X18 )
      | ~ ( v3_pre_topc @ X18 @ X13 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X13 ) ) ) )
      | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X13 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_tmap_1])).

thf('106',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v3_pre_topc @ X2 @ X0 )
      | ~ ( r2_hidden @ ( k3_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X0 ) @ X1 @ X3 ) @ X2 )
      | ( m1_subset_1 @ ( sk_F @ X2 @ X3 @ X1 @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( r1_tmap_1 @ sk_B @ X0 @ X1 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v3_pre_topc @ X2 @ X0 )
      | ~ ( r2_hidden @ ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) @ X1 @ X3 ) @ X2 )
      | ( m1_subset_1 @ ( sk_F @ X2 @ X3 @ X1 @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tmap_1 @ sk_B @ X0 @ X1 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['106','107','108','109','110','111','112'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ~ ( v2_pre_topc @ sk_C )
      | ~ ( l1_pre_topc @ sk_C )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_tmap_1 @ sk_B @ sk_C @ sk_D @ X0 )
      | ( m1_subset_1 @ ( sk_F @ X1 @ X0 @ sk_D @ sk_C @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ sk_D @ X0 ) @ X1 )
      | ~ ( v3_pre_topc @ X1 @ sk_C )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) )
      | ~ ( v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) )
      | ~ ( v1_funct_1 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['103','113'])).

thf('115',plain,(
    v2_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    l1_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_tmap_1 @ sk_B @ sk_C @ sk_D @ X0 )
      | ( m1_subset_1 @ ( sk_F @ X1 @ X0 @ sk_D @ sk_C @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ sk_D @ X0 ) @ X1 )
      | ~ ( v3_pre_topc @ X1 @ sk_C )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['114','115','116','117','118'])).

thf('120',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_subset_1 @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( v3_pre_topc @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_C )
    | ( m1_subset_1 @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_C @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r1_tmap_1 @ sk_B @ sk_C @ sk_D @ sk_F_1 )
    | ~ ( m1_subset_1 @ sk_F_1 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['102','119'])).

thf('121',plain,(
    r1_tmap_1 @ sk_B @ sk_C @ sk_D @ sk_F_1 ),
    inference(demod,[status(thm)],['59','91'])).

thf('122',plain,(
    m1_subset_1 @ sk_F_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['1','2','3'])).

thf('123',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_subset_1 @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( v3_pre_topc @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_C )
    | ( m1_subset_1 @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_C @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['120','121','122'])).

thf('124',plain,
    ( ( m1_subset_1 @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_C @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v3_pre_topc @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_C )
    | ~ ( m1_subset_1 @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ~ ( v3_pre_topc @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_C )
    | ( m1_subset_1 @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_C @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['101','124'])).

thf('126',plain,
    ( ( m1_subset_1 @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_C @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v3_pre_topc @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['125'])).

thf('127',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_C @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['100','126'])).

thf('128',plain,
    ( ( m1_subset_1 @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_C @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['127'])).

thf('129',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( v3_pre_topc @ X0 @ X1 )
      | ( r2_hidden @ X0 @ ( u1_pre_topc @ X1 ) )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('131',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_B )
      | ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_B ) )
      | ~ ( v3_pre_topc @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_B ) )
      | ~ ( v3_pre_topc @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('134',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ~ ( v3_pre_topc @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_C @ sk_B ) @ sk_B )
    | ( r2_hidden @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_C @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference('sup-',[status(thm)],['128','133'])).

thf('135',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_C @ sk_B ) @ ( u1_pre_topc @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['99','134'])).

thf('136',plain,
    ( ( r2_hidden @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_C @ sk_B ) @ ( u1_pre_topc @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['135'])).

thf('137',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v3_pre_topc @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_C )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','14'])).

thf('138',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( m1_subset_1 @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['16','26'])).

thf('139',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( r2_hidden @ ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ sk_D @ sk_F_1 ) @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['28','38'])).

thf('140',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X18: $i] :
      ( ( v2_struct_0 @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X15 ) )
      | ~ ( r1_tmap_1 @ X15 @ X13 @ X16 @ X14 )
      | ( r2_hidden @ X14 @ ( sk_F @ X18 @ X14 @ X16 @ X13 @ X15 ) )
      | ~ ( r2_hidden @ ( k3_funct_2 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X13 ) @ X16 @ X14 ) @ X18 )
      | ~ ( v3_pre_topc @ X18 @ X13 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X13 ) ) ) )
      | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X13 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_tmap_1])).

thf('143',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v3_pre_topc @ X2 @ X0 )
      | ~ ( r2_hidden @ ( k3_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X0 ) @ X1 @ X3 ) @ X2 )
      | ( r2_hidden @ X3 @ ( sk_F @ X2 @ X3 @ X1 @ X0 @ sk_B ) )
      | ~ ( r1_tmap_1 @ sk_B @ X0 @ X1 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v3_pre_topc @ X2 @ X0 )
      | ~ ( r2_hidden @ ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) @ X1 @ X3 ) @ X2 )
      | ( r2_hidden @ X3 @ ( sk_F @ X2 @ X3 @ X1 @ X0 @ sk_B ) )
      | ~ ( r1_tmap_1 @ sk_B @ X0 @ X1 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['143','144','145','146','147','148'])).

thf('150',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ~ ( v2_pre_topc @ sk_C )
      | ~ ( l1_pre_topc @ sk_C )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_tmap_1 @ sk_B @ sk_C @ sk_D @ X0 )
      | ( r2_hidden @ X0 @ ( sk_F @ X1 @ X0 @ sk_D @ sk_C @ sk_B ) )
      | ~ ( r2_hidden @ ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ sk_D @ X0 ) @ X1 )
      | ~ ( v3_pre_topc @ X1 @ sk_C )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) )
      | ~ ( v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) )
      | ~ ( v1_funct_1 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['140','149'])).

thf('151',plain,(
    v2_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    l1_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_tmap_1 @ sk_B @ sk_C @ sk_D @ X0 )
      | ( r2_hidden @ X0 @ ( sk_F @ X1 @ X0 @ sk_D @ sk_C @ sk_B ) )
      | ~ ( r2_hidden @ ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ sk_D @ X0 ) @ X1 )
      | ~ ( v3_pre_topc @ X1 @ sk_C )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['150','151','152','153','154'])).

thf('156',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_subset_1 @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( v3_pre_topc @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_C )
    | ( r2_hidden @ sk_F_1 @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_C @ sk_B ) )
    | ~ ( r1_tmap_1 @ sk_B @ sk_C @ sk_D @ sk_F_1 )
    | ~ ( m1_subset_1 @ sk_F_1 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['139','155'])).

thf('157',plain,(
    r1_tmap_1 @ sk_B @ sk_C @ sk_D @ sk_F_1 ),
    inference(demod,[status(thm)],['59','91'])).

thf('158',plain,(
    m1_subset_1 @ sk_F_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['1','2','3'])).

thf('159',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_subset_1 @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( v3_pre_topc @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_C )
    | ( r2_hidden @ sk_F_1 @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_C @ sk_B ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['156','157','158'])).

thf('160',plain,
    ( ( r2_hidden @ sk_F_1 @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_C @ sk_B ) )
    | ~ ( v3_pre_topc @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_C )
    | ~ ( m1_subset_1 @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['159'])).

thf('161',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ~ ( v3_pre_topc @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_C )
    | ( r2_hidden @ sk_F_1 @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['138','160'])).

thf('162',plain,
    ( ( r2_hidden @ sk_F_1 @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_C @ sk_B ) )
    | ~ ( v3_pre_topc @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['161'])).

thf('163',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ sk_F_1 @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['137','162'])).

thf('164',plain,
    ( ( r2_hidden @ sk_F_1 @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_C @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['163'])).

thf('165',plain,
    ( ( r2_hidden @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_C @ sk_B ) @ ( u1_pre_topc @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['135'])).

thf('166',plain,(
    r1_tarski @ ( u1_pre_topc @ sk_B ) @ ( u1_pre_topc @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('167',plain,(
    ! [X10: $i,X12: $i] :
      ( ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('168',plain,(
    m1_subset_1 @ ( u1_pre_topc @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['166','167'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('169',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) )
      | ( m1_subset_1 @ X19 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('170',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_pre_topc @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['168','169'])).

thf('171',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_C @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['165','170'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('172',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r2_hidden @ X8 @ X9 )
      | ( v1_xboole_0 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('173',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_pre_topc @ sk_A ) )
    | ( r2_hidden @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_C @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['171','172'])).

thf('174',plain,
    ( ( m1_subset_1 @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_C @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['127'])).

thf('175',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( r2_hidden @ X0 @ ( u1_pre_topc @ X1 ) )
      | ( v3_pre_topc @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('176',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_C @ sk_B ) @ sk_A )
    | ~ ( r2_hidden @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_C @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['174','175'])).

thf('177',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v3_pre_topc @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_C @ sk_B ) @ sk_A )
    | ~ ( r2_hidden @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_C @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['176','177'])).

thf('179',plain,
    ( ( v1_xboole_0 @ ( u1_pre_topc @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v3_pre_topc @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_C @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['173','178'])).

thf('180',plain,
    ( ( v3_pre_topc @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_C @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_pre_topc @ sk_A ) ) ),
    inference(simplify,[status(thm)],['179'])).

thf('181',plain,
    ( ( m1_subset_1 @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_C @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['127'])).

thf('182',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v3_pre_topc @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_C )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','14'])).

thf('183',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( m1_subset_1 @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['16','26'])).

thf('184',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( r2_hidden @ ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ sk_D @ sk_F_1 ) @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['28','38'])).

thf('185',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X18: $i] :
      ( ( v2_struct_0 @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X15 ) )
      | ~ ( r1_tmap_1 @ X15 @ X13 @ X16 @ X14 )
      | ( r1_tarski @ ( k7_relset_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X13 ) @ X16 @ ( sk_F @ X18 @ X14 @ X16 @ X13 @ X15 ) ) @ X18 )
      | ~ ( r2_hidden @ ( k3_funct_2 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X13 ) @ X16 @ X14 ) @ X18 )
      | ~ ( v3_pre_topc @ X18 @ X13 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X13 ) ) ) )
      | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X13 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_tmap_1])).

thf('188',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v3_pre_topc @ X2 @ X0 )
      | ~ ( r2_hidden @ ( k3_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X0 ) @ X1 @ X3 ) @ X2 )
      | ( r1_tarski @ ( k7_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X0 ) @ X1 @ ( sk_F @ X2 @ X3 @ X1 @ X0 @ sk_B ) ) @ X2 )
      | ~ ( r1_tmap_1 @ sk_B @ X0 @ X1 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['186','187'])).

thf('189',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v3_pre_topc @ X2 @ X0 )
      | ~ ( r2_hidden @ ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) @ X1 @ X3 ) @ X2 )
      | ( r1_tarski @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) @ X1 @ ( sk_F @ X2 @ X3 @ X1 @ X0 @ sk_B ) ) @ X2 )
      | ~ ( r1_tmap_1 @ sk_B @ X0 @ X1 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['188','189','190','191','192','193','194'])).

thf('196',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ~ ( v2_pre_topc @ sk_C )
      | ~ ( l1_pre_topc @ sk_C )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_tmap_1 @ sk_B @ sk_C @ sk_D @ X0 )
      | ( r1_tarski @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ sk_D @ ( sk_F @ X1 @ X0 @ sk_D @ sk_C @ sk_B ) ) @ X1 )
      | ~ ( r2_hidden @ ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ sk_D @ X0 ) @ X1 )
      | ~ ( v3_pre_topc @ X1 @ sk_C )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) )
      | ~ ( v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) )
      | ~ ( v1_funct_1 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['185','195'])).

thf('197',plain,(
    v2_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,(
    l1_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_tmap_1 @ sk_B @ sk_C @ sk_D @ X0 )
      | ( r1_tarski @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ sk_D @ ( sk_F @ X1 @ X0 @ sk_D @ sk_C @ sk_B ) ) @ X1 )
      | ~ ( r2_hidden @ ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ sk_D @ X0 ) @ X1 )
      | ~ ( v3_pre_topc @ X1 @ sk_C )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['196','197','198','199','200'])).

thf('202',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_subset_1 @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( v3_pre_topc @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_C )
    | ( r1_tarski @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ sk_D @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_C @ sk_B ) ) @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) )
    | ~ ( r1_tmap_1 @ sk_B @ sk_C @ sk_D @ sk_F_1 )
    | ~ ( m1_subset_1 @ sk_F_1 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['184','201'])).

thf('203',plain,(
    r1_tmap_1 @ sk_B @ sk_C @ sk_D @ sk_F_1 ),
    inference(demod,[status(thm)],['59','91'])).

thf('204',plain,(
    m1_subset_1 @ sk_F_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['1','2','3'])).

thf('205',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_subset_1 @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( v3_pre_topc @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_C )
    | ( r1_tarski @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ sk_D @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_C @ sk_B ) ) @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['202','203','204'])).

thf('206',plain,
    ( ( r1_tarski @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ sk_D @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_C @ sk_B ) ) @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) )
    | ~ ( v3_pre_topc @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_C )
    | ~ ( m1_subset_1 @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['205'])).

thf('207',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ~ ( v3_pre_topc @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_C )
    | ( r1_tarski @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ sk_D @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_C @ sk_B ) ) @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['183','206'])).

thf('208',plain,
    ( ( r1_tarski @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ sk_D @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_C @ sk_B ) ) @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) )
    | ~ ( v3_pre_topc @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['207'])).

thf('209',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tarski @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ sk_D @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_C @ sk_B ) ) @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['182','208'])).

thf('210',plain,
    ( ( r1_tarski @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ sk_D @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_C @ sk_B ) ) @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['209'])).

thf('211',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( v2_struct_0 @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X15 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( v3_pre_topc @ X17 @ X15 )
      | ~ ( r2_hidden @ X14 @ X17 )
      | ~ ( r1_tarski @ ( k7_relset_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X13 ) @ X16 @ X17 ) @ ( sk_E @ X14 @ X16 @ X13 @ X15 ) )
      | ( r1_tmap_1 @ X15 @ X13 @ X16 @ X14 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X13 ) ) ) )
      | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X13 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_tmap_1])).

thf('212',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) ) ) )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ~ ( r2_hidden @ sk_F_1 @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_C @ sk_B ) )
    | ~ ( v3_pre_topc @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_C @ sk_B ) @ sk_A )
    | ~ ( m1_subset_1 @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_C @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( m1_subset_1 @ sk_F_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_C )
    | ~ ( v2_pre_topc @ sk_C )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['210','211'])).

thf('213',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('214',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('215',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('216',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('217',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('218',plain,(
    m1_subset_1 @ sk_F_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['1','2','3'])).

thf('219',plain,(
    l1_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('220',plain,(
    v2_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('221',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ~ ( r2_hidden @ sk_F_1 @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_C @ sk_B ) )
    | ~ ( v3_pre_topc @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_C @ sk_B ) @ sk_A )
    | ~ ( m1_subset_1 @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_C @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['212','213','214','215','216','217','218','219','220'])).

thf('222',plain,
    ( ~ ( m1_subset_1 @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_C @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v3_pre_topc @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_C @ sk_B ) @ sk_A )
    | ~ ( r2_hidden @ sk_F_1 @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_C @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['221'])).

thf('223',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ~ ( r2_hidden @ sk_F_1 @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_C @ sk_B ) )
    | ~ ( v3_pre_topc @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_C @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['181','222'])).

thf('224',plain,
    ( ~ ( v3_pre_topc @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_C @ sk_B ) @ sk_A )
    | ~ ( r2_hidden @ sk_F_1 @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_C @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['223'])).

thf('225',plain,
    ( ( v1_xboole_0 @ ( u1_pre_topc @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ~ ( r2_hidden @ sk_F_1 @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['180','224'])).

thf('226',plain,
    ( ~ ( r2_hidden @ sk_F_1 @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_C @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_pre_topc @ sk_A ) ) ),
    inference(simplify,[status(thm)],['225'])).

thf('227',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_pre_topc @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['164','226'])).

thf('228',plain,
    ( ( v1_xboole_0 @ ( u1_pre_topc @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['227'])).

thf('229',plain,(
    ~ ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('230',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['228','229'])).

thf('231',plain,(
    m1_subset_1 @ ( u1_pre_topc @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['166','167'])).

thf('232',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X22 @ X23 )
      | ~ ( v1_xboole_0 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('233',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_pre_topc @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['231','232'])).

thf('234',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['230','233'])).

thf('235',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['136','234'])).

thf('236',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['235'])).

thf('237',plain,(
    ~ ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('238',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['236','237'])).

thf('239',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('240',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['238','239'])).

thf('241',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('242',plain,(
    v2_struct_0 @ sk_C ),
    inference(clc,[status(thm)],['240','241'])).

thf('243',plain,(
    $false ),
    inference(demod,[status(thm)],['0','242'])).


%------------------------------------------------------------------------------
