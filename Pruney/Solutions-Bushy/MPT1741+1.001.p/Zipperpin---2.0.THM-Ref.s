%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1741+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VXyGLPNuUU

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:54:10 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  285 (1584 expanded)
%              Number of leaves         :   34 ( 470 expanded)
%              Depth                    :   33
%              Number of atoms          : 4870 (79571 expanded)
%              Number of equality atoms :   30 ( 893 expanded)
%              Maximal formula depth    :   27 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_F_1_type,type,(
    sk_F_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(r1_funct_2_type,type,(
    r1_funct_2: $i > $i > $i > $i > $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_E_1_type,type,(
    sk_E_1: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t50_tmap_1,conjecture,(
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
             => ( ( ( ( u1_struct_0 @ B )
                    = ( u1_struct_0 @ C ) )
                  & ( r1_tarski @ ( u1_pre_topc @ C ) @ ( u1_pre_topc @ B ) ) )
               => ! [D: $i] :
                    ( ( ( v1_funct_1 @ D )
                      & ( v1_funct_2 @ D @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                      & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
                   => ! [E: $i] :
                        ( ( ( v1_funct_1 @ E )
                          & ( v1_funct_2 @ E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ C ) )
                          & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ C ) ) ) ) )
                       => ( ( r1_funct_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ C ) @ D @ E )
                         => ! [F: $i] :
                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ A ) )
                             => ( ( r1_tmap_1 @ A @ B @ D @ F )
                               => ( r1_tmap_1 @ A @ C @ E @ F ) ) ) ) ) ) ) ) ) ) )).

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
               => ( ( ( ( u1_struct_0 @ B )
                      = ( u1_struct_0 @ C ) )
                    & ( r1_tarski @ ( u1_pre_topc @ C ) @ ( u1_pre_topc @ B ) ) )
                 => ! [D: $i] :
                      ( ( ( v1_funct_1 @ D )
                        & ( v1_funct_2 @ D @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
                     => ! [E: $i] :
                          ( ( ( v1_funct_1 @ E )
                            & ( v1_funct_2 @ E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ C ) )
                            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ C ) ) ) ) )
                         => ( ( r1_funct_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ C ) @ D @ E )
                           => ! [F: $i] :
                                ( ( m1_subset_1 @ F @ ( u1_struct_0 @ A ) )
                               => ( ( r1_tmap_1 @ A @ B @ D @ F )
                                 => ( r1_tmap_1 @ A @ C @ E @ F ) ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t50_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_F_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
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

thf('4',plain,(
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

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_C ) )
      | ( r1_tmap_1 @ X0 @ sk_C @ X1 @ X2 )
      | ( v3_pre_topc @ ( sk_E @ X2 @ X1 @ sk_C @ X0 ) @ sk_C )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ sk_C )
      | ~ ( v2_pre_topc @ sk_C )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    l1_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v2_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ( r1_tmap_1 @ X0 @ sk_C @ X1 @ X2 )
      | ( v3_pre_topc @ ( sk_E @ X2 @ X1 @ sk_C @ X0 ) @ sk_C )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['5','6','7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v3_pre_topc @ ( sk_E @ X0 @ sk_D @ sk_C @ sk_A ) @ sk_C )
      | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ X0 )
      | ~ ( v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','9'])).

thf('11',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v3_pre_topc @ ( sk_E @ X0 @ sk_D @ sk_C @ sk_A ) @ sk_C )
      | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11','12','13','14'])).

thf('16',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v3_pre_topc @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_C )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['1','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_F_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
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

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_C ) )
      | ( r1_tmap_1 @ X0 @ sk_C @ X1 @ X2 )
      | ( m1_subset_1 @ ( sk_E @ X2 @ X1 @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ sk_C )
      | ~ ( v2_pre_topc @ sk_C )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    l1_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v2_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ( r1_tmap_1 @ X0 @ sk_C @ X1 @ X2 )
      | ( m1_subset_1 @ ( sk_E @ X2 @ X1 @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['21','22','23','24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_subset_1 @ ( sk_E @ X0 @ sk_D @ sk_C @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ X0 )
      | ~ ( v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','26'])).

thf('28',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_subset_1 @ ( sk_E @ X0 @ sk_D @ sk_C @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','28','29','30','31'])).

thf('33',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( m1_subset_1 @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['17','32'])).

thf('34',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( v3_pre_topc @ X0 @ X1 )
      | ( r2_hidden @ X0 @ ( u1_pre_topc @ X1 ) )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( l1_pre_topc @ sk_C )
      | ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_C ) )
      | ~ ( v3_pre_topc @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    l1_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_C ) )
      | ~ ( v3_pre_topc @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v3_pre_topc @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_C )
    | ( r2_hidden @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ ( u1_pre_topc @ sk_C ) ) ),
    inference('sup-',[status(thm)],['33','38'])).

thf('40',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ ( u1_pre_topc @ sk_C ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['16','39'])).

thf('41',plain,
    ( ( r2_hidden @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ ( u1_pre_topc @ sk_C ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,
    ( ( r2_hidden @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ ( u1_pre_topc @ sk_C ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['40'])).

thf('43',plain,(
    r1_tarski @ ( u1_pre_topc @ sk_C ) @ ( u1_pre_topc @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('44',plain,(
    ! [X10: $i,X12: $i] :
      ( ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('45',plain,(
    m1_subset_1 @ ( u1_pre_topc @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_pre_topc @ sk_B ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('46',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) )
      | ( m1_subset_1 @ X19 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_pre_topc @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference('sup-',[status(thm)],['42','47'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('49',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r2_hidden @ X8 @ X9 )
      | ( v1_xboole_0 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('50',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_C )
    | ( v1_xboole_0 @ ( u1_pre_topc @ sk_B ) )
    | ( r2_hidden @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( m1_subset_1 @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['17','32'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( r2_hidden @ X0 @ ( u1_pre_topc @ X1 ) )
      | ( v3_pre_topc @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('53',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v3_pre_topc @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_B )
    | ~ ( r2_hidden @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v3_pre_topc @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_B )
    | ~ ( r2_hidden @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( v1_xboole_0 @ ( u1_pre_topc @ sk_B ) )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v3_pre_topc @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['50','55'])).

thf('57',plain,
    ( ( v3_pre_topc @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_C )
    | ( v1_xboole_0 @ ( u1_pre_topc @ sk_B ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( m1_subset_1 @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['17','32'])).

thf('59',plain,(
    m1_subset_1 @ sk_F_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
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

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_C ) )
      | ( r1_tmap_1 @ X0 @ sk_C @ X1 @ X2 )
      | ( r2_hidden @ ( k3_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_C ) @ X1 @ X2 ) @ ( sk_E @ X2 @ X1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ sk_C )
      | ~ ( v2_pre_topc @ sk_C )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    l1_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v2_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ( r1_tmap_1 @ X0 @ sk_C @ X1 @ X2 )
      | ( r2_hidden @ ( k3_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ X1 @ X2 ) @ ( sk_E @ X2 @ X1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['63','64','65','66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_D @ X0 ) @ ( sk_E @ X0 @ sk_D @ sk_C @ sk_A ) )
      | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ X0 )
      | ~ ( v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['60','68'])).

thf('70',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_D @ X0 ) @ ( sk_E @ X0 @ sk_D @ sk_C @ sk_A ) )
      | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['69','70','71','72','73'])).

thf('75',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( r2_hidden @ ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_D @ sk_F_1 ) @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['59','74'])).

thf('76',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
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

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( v3_pre_topc @ X0 @ sk_B )
      | ~ ( r2_hidden @ ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_D @ X1 ) @ X0 )
      | ( v3_pre_topc @ ( sk_F @ X0 @ X1 @ sk_D @ sk_B @ sk_A ) @ sk_A )
      | ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_D @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( v3_pre_topc @ X0 @ sk_B )
      | ~ ( r2_hidden @ ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_D @ X1 ) @ X0 )
      | ( v3_pre_topc @ ( sk_F @ X0 @ X1 @ sk_D @ sk_B @ sk_A ) @ sk_A )
      | ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_D @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['78','79','80','81','82','83','84'])).

thf('86',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_subset_1 @ sk_F_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_F_1 )
    | ( v3_pre_topc @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_B @ sk_A ) @ sk_A )
    | ~ ( v3_pre_topc @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_B )
    | ~ ( m1_subset_1 @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['75','85'])).

thf('87',plain,(
    m1_subset_1 @ sk_F_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    r1_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_F_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v3_pre_topc @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_B @ sk_A ) @ sk_A )
    | ~ ( v3_pre_topc @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_B )
    | ~ ( m1_subset_1 @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['86','87','88'])).

thf('90',plain,
    ( ~ ( m1_subset_1 @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( v3_pre_topc @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_B )
    | ( v3_pre_topc @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_B @ sk_A ) @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v3_pre_topc @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_B @ sk_A ) @ sk_A )
    | ~ ( v3_pre_topc @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['58','90'])).

thf('92',plain,
    ( ~ ( v3_pre_topc @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_B )
    | ( v3_pre_topc @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_B @ sk_A ) @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,
    ( ( v1_xboole_0 @ ( u1_pre_topc @ sk_B ) )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v3_pre_topc @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['57','92'])).

thf('94',plain,
    ( ( v3_pre_topc @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_B @ sk_A ) @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_C )
    | ( v1_xboole_0 @ ( u1_pre_topc @ sk_B ) ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,
    ( ( v3_pre_topc @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_C )
    | ( v1_xboole_0 @ ( u1_pre_topc @ sk_B ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('96',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( m1_subset_1 @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['17','32'])).

thf('97',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( r2_hidden @ ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_D @ sk_F_1 ) @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['59','74'])).

thf('98',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
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

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( v3_pre_topc @ X0 @ sk_B )
      | ~ ( r2_hidden @ ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_D @ X1 ) @ X0 )
      | ( r2_hidden @ X1 @ ( sk_F @ X0 @ X1 @ sk_D @ sk_B @ sk_A ) )
      | ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_D @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( v3_pre_topc @ X0 @ sk_B )
      | ~ ( r2_hidden @ ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_D @ X1 ) @ X0 )
      | ( r2_hidden @ X1 @ ( sk_F @ X0 @ X1 @ sk_D @ sk_B @ sk_A ) )
      | ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_D @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['100','101','102','103','104','105','106'])).

thf('108',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_subset_1 @ sk_F_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_F_1 )
    | ( r2_hidden @ sk_F_1 @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_B @ sk_A ) )
    | ~ ( v3_pre_topc @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_B )
    | ~ ( m1_subset_1 @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['97','107'])).

thf('109',plain,(
    m1_subset_1 @ sk_F_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    r1_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_F_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ sk_F_1 @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_B @ sk_A ) )
    | ~ ( v3_pre_topc @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_B )
    | ~ ( m1_subset_1 @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['108','109','110'])).

thf('112',plain,
    ( ~ ( m1_subset_1 @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( v3_pre_topc @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_B )
    | ( r2_hidden @ sk_F_1 @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ sk_F_1 @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_B @ sk_A ) )
    | ~ ( v3_pre_topc @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['96','112'])).

thf('114',plain,
    ( ~ ( v3_pre_topc @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_B )
    | ( r2_hidden @ sk_F_1 @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,
    ( ( v1_xboole_0 @ ( u1_pre_topc @ sk_B ) )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ sk_F_1 @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['95','114'])).

thf('116',plain,
    ( ( r2_hidden @ sk_F_1 @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_C )
    | ( v1_xboole_0 @ ( u1_pre_topc @ sk_B ) ) ),
    inference(simplify,[status(thm)],['115'])).

thf('117',plain,
    ( ( v3_pre_topc @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_C )
    | ( v1_xboole_0 @ ( u1_pre_topc @ sk_B ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('118',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( m1_subset_1 @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['17','32'])).

thf('119',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( r2_hidden @ ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_D @ sk_F_1 ) @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['59','74'])).

thf('120',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
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

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( v3_pre_topc @ X0 @ sk_B )
      | ~ ( r2_hidden @ ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_D @ X1 ) @ X0 )
      | ( m1_subset_1 @ ( sk_F @ X0 @ X1 @ sk_D @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_D @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( v3_pre_topc @ X0 @ sk_B )
      | ~ ( r2_hidden @ ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_D @ X1 ) @ X0 )
      | ( m1_subset_1 @ ( sk_F @ X0 @ X1 @ sk_D @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_D @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['122','123','124','125','126','127','128'])).

thf('130',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_subset_1 @ sk_F_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_F_1 )
    | ( m1_subset_1 @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v3_pre_topc @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_B )
    | ~ ( m1_subset_1 @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['119','129'])).

thf('131',plain,(
    m1_subset_1 @ sk_F_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    r1_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_F_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v3_pre_topc @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_B )
    | ~ ( m1_subset_1 @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['130','131','132'])).

thf('134',plain,
    ( ~ ( m1_subset_1 @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( v3_pre_topc @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_B )
    | ( m1_subset_1 @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['133'])).

thf('135',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v3_pre_topc @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['118','134'])).

thf('136',plain,
    ( ~ ( v3_pre_topc @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_B )
    | ( m1_subset_1 @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['135'])).

thf('137',plain,
    ( ( v1_xboole_0 @ ( u1_pre_topc @ sk_B ) )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['117','136'])).

thf('138',plain,
    ( ( m1_subset_1 @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_C )
    | ( v1_xboole_0 @ ( u1_pre_topc @ sk_B ) ) ),
    inference(simplify,[status(thm)],['137'])).

thf('139',plain,
    ( ( v3_pre_topc @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_C )
    | ( v1_xboole_0 @ ( u1_pre_topc @ sk_B ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('140',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( m1_subset_1 @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['17','32'])).

thf('141',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( r2_hidden @ ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_D @ sk_F_1 ) @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['59','74'])).

thf('142',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
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

thf('144',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( v3_pre_topc @ X0 @ sk_B )
      | ~ ( r2_hidden @ ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_D @ X1 ) @ X0 )
      | ( r1_tarski @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_D @ ( sk_F @ X0 @ X1 @ sk_D @ sk_B @ sk_A ) ) @ X0 )
      | ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_D @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( v3_pre_topc @ X0 @ sk_B )
      | ~ ( r2_hidden @ ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_D @ X1 ) @ X0 )
      | ( r1_tarski @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_D @ ( sk_F @ X0 @ X1 @ sk_D @ sk_B @ sk_A ) ) @ X0 )
      | ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_D @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['144','145','146','147','148','149','150'])).

thf('152',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_subset_1 @ sk_F_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_F_1 )
    | ( r1_tarski @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_D @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_B @ sk_A ) ) @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) )
    | ~ ( v3_pre_topc @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_B )
    | ~ ( m1_subset_1 @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['141','151'])).

thf('153',plain,(
    m1_subset_1 @ sk_F_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    r1_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_F_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tarski @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_D @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_B @ sk_A ) ) @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) )
    | ~ ( v3_pre_topc @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_B )
    | ~ ( m1_subset_1 @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['152','153','154'])).

thf('156',plain,
    ( ~ ( m1_subset_1 @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( v3_pre_topc @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_B )
    | ( r1_tarski @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_D @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_B @ sk_A ) ) @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['155'])).

thf('157',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tarski @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_D @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_B @ sk_A ) ) @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) )
    | ~ ( v3_pre_topc @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['140','156'])).

thf('158',plain,
    ( ~ ( v3_pre_topc @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_B )
    | ( r1_tarski @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_D @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_B @ sk_A ) ) @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['157'])).

thf('159',plain,
    ( ( v1_xboole_0 @ ( u1_pre_topc @ sk_B ) )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tarski @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_D @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_B @ sk_A ) ) @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['139','158'])).

thf('160',plain,
    ( ( r1_tarski @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_D @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_B @ sk_A ) ) @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_C )
    | ( v1_xboole_0 @ ( u1_pre_topc @ sk_B ) ) ),
    inference(simplify,[status(thm)],['159'])).

thf('161',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,(
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

thf('163',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ ( k7_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ X1 @ X3 ) @ ( sk_E @ X2 @ X1 @ sk_C @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_C ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_C ) ) ) )
      | ( r1_tmap_1 @ X0 @ sk_C @ X1 @ X2 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( v3_pre_topc @ X3 @ X0 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ sk_C )
      | ~ ( v2_pre_topc @ sk_C )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['161','162'])).

thf('164',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    l1_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,(
    v2_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ ( k7_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ X1 @ X3 ) @ ( sk_E @ X2 @ X1 @ sk_C @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( r1_tmap_1 @ X0 @ sk_C @ X1 @ X2 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( v3_pre_topc @ X3 @ X0 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['163','164','165','166','167'])).

thf('169',plain,
    ( ( v1_xboole_0 @ ( u1_pre_topc @ sk_B ) )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ~ ( m1_subset_1 @ sk_F_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v3_pre_topc @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_B @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ sk_F_1 @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_B @ sk_A ) )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['160','168'])).

thf('170',plain,(
    m1_subset_1 @ sk_F_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,
    ( ( v1_xboole_0 @ ( u1_pre_topc @ sk_B ) )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ~ ( m1_subset_1 @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v3_pre_topc @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_B @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ sk_F_1 @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_B @ sk_A ) )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['169','170','171','172','173','174','175'])).

thf('177',plain,
    ( ~ ( r2_hidden @ sk_F_1 @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_B @ sk_A ) )
    | ~ ( v3_pre_topc @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_B @ sk_A ) @ sk_A )
    | ~ ( m1_subset_1 @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_C )
    | ( v1_xboole_0 @ ( u1_pre_topc @ sk_B ) ) ),
    inference(simplify,[status(thm)],['176'])).

thf('178',plain,
    ( ( v1_xboole_0 @ ( u1_pre_topc @ sk_B ) )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_pre_topc @ sk_B ) )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( v3_pre_topc @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_B @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ sk_F_1 @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['138','177'])).

thf('179',plain,
    ( ~ ( r2_hidden @ sk_F_1 @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_B @ sk_A ) )
    | ~ ( v3_pre_topc @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_B @ sk_A ) @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_C )
    | ( v1_xboole_0 @ ( u1_pre_topc @ sk_B ) ) ),
    inference(simplify,[status(thm)],['178'])).

thf('180',plain,
    ( ( v1_xboole_0 @ ( u1_pre_topc @ sk_B ) )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_pre_topc @ sk_B ) )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( v3_pre_topc @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['116','179'])).

thf('181',plain,
    ( ~ ( v3_pre_topc @ ( sk_F @ ( sk_E @ sk_F_1 @ sk_D @ sk_C @ sk_A ) @ sk_F_1 @ sk_D @ sk_B @ sk_A ) @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_C )
    | ( v1_xboole_0 @ ( u1_pre_topc @ sk_B ) ) ),
    inference(simplify,[status(thm)],['180'])).

thf('182',plain,
    ( ( v1_xboole_0 @ ( u1_pre_topc @ sk_B ) )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_pre_topc @ sk_B ) )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['94','181'])).

thf('183',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_C )
    | ( v1_xboole_0 @ ( u1_pre_topc @ sk_B ) ) ),
    inference(simplify,[status(thm)],['182'])).

thf('184',plain,(
    ~ ( r1_tmap_1 @ sk_A @ sk_C @ sk_E_1 @ sk_F_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,(
    m1_subset_1 @ sk_F_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,(
    m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,(
    m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['186','187'])).

thf('189',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ( r1_tmap_1 @ X0 @ sk_C @ X1 @ X2 )
      | ( r2_hidden @ ( k3_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ X1 @ X2 ) @ ( sk_E @ X2 @ X1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['63','64','65','66','67'])).

thf('190',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E_1 @ X0 ) @ ( sk_E @ X0 @ sk_E_1 @ sk_C @ sk_A ) )
      | ( r1_tmap_1 @ sk_A @ sk_C @ sk_E_1 @ X0 )
      | ~ ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E_1 )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['188','189'])).

thf('191',plain,(
    v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,(
    v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['191','192'])).

thf('194',plain,(
    v1_funct_1 @ sk_E_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E_1 @ X0 ) @ ( sk_E @ X0 @ sk_E_1 @ sk_C @ sk_A ) )
      | ( r1_tmap_1 @ sk_A @ sk_C @ sk_E_1 @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['190','193','194','195','196'])).

thf('198',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_E_1 @ sk_F_1 )
    | ( r2_hidden @ ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E_1 @ sk_F_1 ) @ ( sk_E @ sk_F_1 @ sk_E_1 @ sk_C @ sk_A ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['185','197'])).

thf('199',plain,(
    r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ sk_D @ sk_E_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,(
    r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_D @ sk_E_1 ),
    inference(demod,[status(thm)],['199','200'])).

thf('202',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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

thf('203',plain,(
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

thf('204',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ X2 @ X1 @ sk_D @ X0 )
      | ( sk_D = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_2 @ X0 @ X2 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ( v1_xboole_0 @ X1 )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['202','203'])).

thf('205',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ X2 @ X1 @ sk_D @ X0 )
      | ( sk_D = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_2 @ X0 @ X2 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['204','205','206'])).

thf('208',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_E_1 )
    | ~ ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( sk_D = sk_E_1 ) ),
    inference('sup-',[status(thm)],['201','207'])).

thf('209',plain,(
    v1_funct_1 @ sk_E_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('210',plain,(
    v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['191','192'])).

thf('211',plain,(
    m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['186','187'])).

thf('212',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( sk_D = sk_E_1 ) ),
    inference(demod,[status(thm)],['208','209','210','211'])).

thf('213',plain,
    ( ( sk_D = sk_E_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['212'])).

thf('214',plain,(
    m1_subset_1 @ sk_F_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('215',plain,(
    m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['186','187'])).

thf('216',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ( r1_tmap_1 @ X0 @ sk_C @ X1 @ X2 )
      | ( m1_subset_1 @ ( sk_E @ X2 @ X1 @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['21','22','23','24','25'])).

thf('217',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_subset_1 @ ( sk_E @ X0 @ sk_E_1 @ sk_C @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( r1_tmap_1 @ sk_A @ sk_C @ sk_E_1 @ X0 )
      | ~ ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E_1 )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['215','216'])).

thf('218',plain,(
    v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['191','192'])).

thf('219',plain,(
    v1_funct_1 @ sk_E_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('220',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('221',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('222',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_subset_1 @ ( sk_E @ X0 @ sk_E_1 @ sk_C @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( r1_tmap_1 @ sk_A @ sk_C @ sk_E_1 @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['217','218','219','220','221'])).

thf('223',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_E_1 @ sk_F_1 )
    | ( m1_subset_1 @ ( sk_E @ sk_F_1 @ sk_E_1 @ sk_C @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['214','222'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('224',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X22 @ X23 )
      | ~ ( v1_xboole_0 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('225',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ( r1_tmap_1 @ sk_A @ sk_C @ sk_E_1 @ sk_F_1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( sk_E @ sk_F_1 @ sk_E_1 @ sk_C @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['223','224'])).

thf('226',plain,(
    ! [X0: $i] :
      ( ( sk_D = sk_E_1 )
      | ~ ( r2_hidden @ X0 @ ( sk_E @ sk_F_1 @ sk_E_1 @ sk_C @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_tmap_1 @ sk_A @ sk_C @ sk_E_1 @ sk_F_1 )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['213','225'])).

thf('227',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_E_1 @ sk_F_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_E_1 @ sk_F_1 )
    | ( v2_struct_0 @ sk_A )
    | ( sk_D = sk_E_1 ) ),
    inference('sup-',[status(thm)],['198','226'])).

thf('228',plain,
    ( ( sk_D = sk_E_1 )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_E_1 @ sk_F_1 )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['227'])).

thf('229',plain,(
    ~ ( r1_tmap_1 @ sk_A @ sk_C @ sk_E_1 @ sk_F_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('230',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( sk_D = sk_E_1 ) ),
    inference('sup-',[status(thm)],['228','229'])).

thf('231',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('232',plain,
    ( ( sk_D = sk_E_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['230','231'])).

thf('233',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('234',plain,(
    sk_D = sk_E_1 ),
    inference(clc,[status(thm)],['232','233'])).

thf('235',plain,(
    ~ ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 ) ),
    inference(demod,[status(thm)],['184','234'])).

thf('236',plain,
    ( ( v1_xboole_0 @ ( u1_pre_topc @ sk_B ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['183','235'])).

thf('237',plain,(
    m1_subset_1 @ ( u1_pre_topc @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_pre_topc @ sk_B ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('238',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X22 @ X23 )
      | ~ ( v1_xboole_0 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('239',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_pre_topc @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['237','238'])).

thf('240',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['236','239'])).

thf('241',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['41','240'])).

thf('242',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['241'])).

thf('243',plain,(
    ~ ( r1_tmap_1 @ sk_A @ sk_C @ sk_D @ sk_F_1 ) ),
    inference(demod,[status(thm)],['184','234'])).

thf('244',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['242','243'])).

thf('245',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('246',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['244','245'])).

thf('247',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('248',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['246','247'])).

thf('249',plain,(
    $false ),
    inference(demod,[status(thm)],['0','248'])).


%------------------------------------------------------------------------------
