%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LCxLopGXfs

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:41 EST 2020

% Result     : Theorem 1.06s
% Output     : Refutation 1.06s
% Verified   : 
% Statistics : Number of formulae       :  309 (3746 expanded)
%              Number of leaves         :   43 (1112 expanded)
%              Depth                    :   45
%              Number of atoms          : 4175 (93554 expanded)
%              Number of equality atoms :   62 (1686 expanded)
%              Maximal formula depth    :   23 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k4_tmap_1_type,type,(
    k4_tmap_1: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
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

thf('2',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 )
      | ~ ( m1_pre_topc @ X31 @ X30 )
      | ( m1_subset_1 @ ( k4_tmap_1 @ X30 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X30 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_tmap_1])).

thf('3',plain,
    ( ( m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('9',plain,(
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

thf('10',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( v2_struct_0 @ X38 )
      | ~ ( v2_pre_topc @ X38 )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_funct_2 @ X39 @ ( u1_struct_0 @ X38 ) @ ( u1_struct_0 @ X40 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X38 ) @ ( u1_struct_0 @ X40 ) ) ) )
      | ( r2_hidden @ ( sk_F @ X41 @ X39 @ X42 @ X38 @ X40 ) @ ( u1_struct_0 @ X42 ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X42 ) @ ( u1_struct_0 @ X40 ) @ ( k2_tmap_1 @ X38 @ X40 @ X39 @ X42 ) @ X41 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X42 ) @ ( u1_struct_0 @ X40 ) ) ) )
      | ~ ( v1_funct_2 @ X41 @ ( u1_struct_0 @ X42 ) @ ( u1_struct_0 @ X40 ) )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( m1_pre_topc @ X42 @ X38 )
      | ( v2_struct_0 @ X42 )
      | ~ ( l1_pre_topc @ X40 )
      | ~ ( v2_pre_topc @ X40 )
      | ( v2_struct_0 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t59_tmap_1])).

thf('11',plain,(
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
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('17',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_pre_topc @ X14 @ X15 )
      | ( l1_pre_topc @ X14 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('18',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('22',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ( v2_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('23',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v2_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
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
    inference(demod,[status(thm)],['11','12','13','14','15','20','26'])).

thf('28',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['8','27'])).

thf('29',plain,(
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

thf('30',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X28 ) ) ) )
      | ~ ( v1_funct_2 @ X26 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X28 ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( l1_struct_0 @ X28 )
      | ~ ( l1_struct_0 @ X27 )
      | ~ ( l1_struct_0 @ X29 )
      | ( v1_funct_1 @ ( k2_tmap_1 @ X27 @ X28 @ X26 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tmap_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['18','19'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('33',plain,(
    ! [X13: $i] :
      ( ( l1_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('34',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X13: $i] :
      ( ( l1_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('37',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['31','34','37','38','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X28 ) ) ) )
      | ~ ( v1_funct_2 @ X26 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X28 ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( l1_struct_0 @ X28 )
      | ~ ( l1_struct_0 @ X27 )
      | ~ ( l1_struct_0 @ X29 )
      | ( v1_funct_2 @ ( k2_tmap_1 @ X27 @ X28 @ X26 @ X29 ) @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tmap_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['32','33'])).

thf('45',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['35','36'])).

thf('46',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['43','44','45','46','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X28 ) ) ) )
      | ~ ( v1_funct_2 @ X26 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X28 ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( l1_struct_0 @ X28 )
      | ~ ( l1_struct_0 @ X27 )
      | ~ ( l1_struct_0 @ X29 )
      | ( m1_subset_1 @ ( k2_tmap_1 @ X27 @ X28 @ X26 @ X29 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X28 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tmap_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['32','33'])).

thf('53',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['35','36'])).

thf('54',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['51','52','53','54','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('58',plain,(
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

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 )
      | ( sk_C = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 )
      | ( sk_C = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,
    ( ~ ( l1_struct_0 @ sk_B )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_C
      = ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['56','62'])).

thf('64',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['32','33'])).

thf('65',plain,
    ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_C
      = ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('66',plain,(
    ! [X34: $i] :
      ( ( m1_pre_topc @ X34 @ X34 )
      | ~ ( l1_pre_topc @ X34 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('67',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tmap_1,axiom,(
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
                  ( ( ( v1_funct_1 @ D )
                    & ( v1_funct_2 @ D @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) )
                 => ( r2_funct_2 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ D @ ( k3_tmap_1 @ A @ B @ C @ C @ D ) ) ) ) ) ) )).

thf('68',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ( v2_struct_0 @ X43 )
      | ~ ( v2_pre_topc @ X43 )
      | ~ ( l1_pre_topc @ X43 )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_funct_2 @ X44 @ ( u1_struct_0 @ X45 ) @ ( u1_struct_0 @ X43 ) )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X45 ) @ ( u1_struct_0 @ X43 ) ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X45 ) @ ( u1_struct_0 @ X43 ) @ X44 @ ( k3_tmap_1 @ X46 @ X43 @ X45 @ X45 @ X44 ) )
      | ~ ( m1_pre_topc @ X45 @ X46 )
      | ( v2_struct_0 @ X45 )
      | ~ ( l1_pre_topc @ X46 )
      | ~ ( v2_pre_topc @ X46 )
      | ( v2_struct_0 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t74_tmap_1])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k3_tmap_1 @ X0 @ sk_A @ sk_B @ sk_B @ sk_C ) )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k3_tmap_1 @ X0 @ sk_A @ sk_B @ sk_B @ sk_C ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['69','70','71','72','73'])).

thf('75',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['66','74'])).

thf('76',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['18','19'])).

thf('77',plain,(
    ! [X34: $i] :
      ( ( m1_pre_topc @ X34 @ X34 )
      | ~ ( l1_pre_topc @ X34 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('78',plain,(
    ! [X34: $i] :
      ( ( m1_pre_topc @ X34 @ X34 )
      | ~ ( l1_pre_topc @ X34 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('79',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
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

thf('80',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( v2_struct_0 @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( m1_pre_topc @ X22 @ X23 )
      | ~ ( m1_pre_topc @ X22 @ X24 )
      | ( ( k3_tmap_1 @ X23 @ X21 @ X24 @ X22 @ X25 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X21 ) @ X25 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X21 ) ) ) )
      | ~ ( v1_funct_2 @ X25 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X21 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( m1_pre_topc @ X24 @ X23 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d5_tmap_1])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_tmap_1 @ X0 @ sk_A @ sk_B @ X1 @ sk_C )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_B )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_A @ sk_B @ X1 @ sk_C )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_B )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['81','82','83','84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ X0 @ sk_C )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['78','86'])).

thf('88',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['18','19'])).

thf('89',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['18','19'])).

thf('90',plain,(
    v2_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ X0 @ sk_C )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['87','88','89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ X0 @ sk_C )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['77','92'])).

thf('94',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['18','19'])).

thf('95',plain,(
    ! [X34: $i] :
      ( ( m1_pre_topc @ X34 @ X34 )
      | ~ ( l1_pre_topc @ X34 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('96',plain,(
    ! [X34: $i] :
      ( ( m1_pre_topc @ X34 @ X34 )
      | ~ ( l1_pre_topc @ X34 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('97',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('99',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_pre_topc @ X35 @ X36 )
      | ~ ( m1_pre_topc @ X35 @ X37 )
      | ( r1_tarski @ ( u1_struct_0 @ X35 ) @ ( u1_struct_0 @ X37 ) )
      | ~ ( m1_pre_topc @ X37 @ X36 )
      | ~ ( l1_pre_topc @ X36 )
      | ~ ( v2_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('100',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['100','101','102'])).

thf('104',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_B )
    | ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['97','103'])).

thf('105',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['96','104'])).

thf('106',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['18','19'])).

thf('107',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_pre_topc @ X35 @ X36 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X35 ) @ ( u1_struct_0 @ X37 ) )
      | ( m1_pre_topc @ X35 @ X37 )
      | ~ ( m1_pre_topc @ X37 @ X36 )
      | ~ ( l1_pre_topc @ X36 )
      | ~ ( v2_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('109',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( m1_pre_topc @ sk_B @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ sk_B @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ( m1_pre_topc @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['95','110'])).

thf('112',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['18','19'])).

thf('113',plain,(
    v2_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('114',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['18','19'])).

thf('115',plain,(
    m1_pre_topc @ sk_B @ sk_B ),
    inference(demod,[status(thm)],['111','112','113','114'])).

thf('116',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
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

thf('117',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( v2_struct_0 @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( m1_pre_topc @ X18 @ X19 )
      | ( ( k2_tmap_1 @ X19 @ X17 @ X20 @ X18 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X17 ) @ X20 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X17 ) ) ) )
      | ~ ( v1_funct_2 @ X20 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X17 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    v2_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('120',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['18','19'])).

thf('121',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['118','119','120','121','122','123','124'])).

thf('126',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['115','125'])).

thf('127',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['126','127'])).

thf('129',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,
    ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['128','129'])).

thf('131',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C )
      = ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['93','94','130'])).

thf('132',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C )
      = ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) ) ),
    inference(clc,[status(thm)],['131','132'])).

thf('134',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,
    ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C )
    = ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) ),
    inference(clc,[status(thm)],['133','134'])).

thf('136',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['18','19'])).

thf('137',plain,(
    v2_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('138',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['75','76','135','136','137'])).

thf('139',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['138'])).

thf('140',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) ) ),
    inference(clc,[status(thm)],['139','140'])).

thf('142',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) ),
    inference(clc,[status(thm)],['141','142'])).

thf('144',plain,
    ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_C
      = ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) ) ),
    inference(demod,[status(thm)],['65','143'])).

thf('145',plain,
    ( ~ ( l1_struct_0 @ sk_B )
    | ( sk_C
      = ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['48','144'])).

thf('146',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['32','33'])).

thf('147',plain,
    ( ( sk_C
      = ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) ) ),
    inference(demod,[status(thm)],['145','146'])).

thf('148',plain,
    ( ~ ( l1_struct_0 @ sk_B )
    | ( sk_C
      = ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['40','147'])).

thf('149',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['32','33'])).

thf('150',plain,
    ( sk_C
    = ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['148','149'])).

thf('151',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 )
      | ~ ( m1_pre_topc @ X31 @ X30 )
      | ( v1_funct_2 @ ( k4_tmap_1 @ X30 @ X31 ) @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_tmap_1])).

thf('153',plain,
    ( ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,
    ( ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['153','154','155'])).

thf('157',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,(
    v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['156','157'])).

thf('159',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 )
      | ~ ( m1_pre_topc @ X31 @ X30 )
      | ( v1_funct_1 @ ( k4_tmap_1 @ X30 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_tmap_1])).

thf('161',plain,
    ( ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,
    ( ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['161','162','163'])).

thf('165',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['164','165'])).

thf('167',plain,(
    m1_pre_topc @ sk_B @ sk_B ),
    inference(demod,[status(thm)],['111','112','113','114'])).

thf('168',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['28','150','158','166','167'])).

thf('169',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( r2_hidden @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['168'])).

thf('170',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('171',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( m1_pre_topc @ X32 @ X33 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X32 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ~ ( l1_pre_topc @ X33 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('172',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['170','171'])).

thf('173',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['172','173'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('175',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) )
      | ( m1_subset_1 @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('176',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['174','175'])).

thf('177',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['169','176'])).

thf('178',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( r2_hidden @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['168'])).

thf('179',plain,(
    ! [X53: $i] :
      ( ~ ( r2_hidden @ X53 @ ( u1_struct_0 @ sk_B ) )
      | ( X53
        = ( k1_funct_1 @ sk_C @ X53 ) )
      | ~ ( m1_subset_1 @ X53 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A )
      = ( k1_funct_1 @ sk_C @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['178','179'])).

thf('181',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A )
      = ( k1_funct_1 @ sk_C @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['177','180'])).

thf('182',plain,
    ( ( ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A )
      = ( k1_funct_1 @ sk_C @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['181'])).

thf('183',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['169','176'])).

thf('184',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( r2_hidden @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['168'])).

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

thf('185',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ( v2_struct_0 @ X50 )
      | ~ ( m1_pre_topc @ X50 @ X51 )
      | ~ ( r2_hidden @ X52 @ ( u1_struct_0 @ X50 ) )
      | ( ( k1_funct_1 @ ( k4_tmap_1 @ X51 @ X50 ) @ X52 )
        = X52 )
      | ~ ( m1_subset_1 @ X52 @ ( u1_struct_0 @ X51 ) )
      | ~ ( l1_pre_topc @ X51 )
      | ~ ( v2_pre_topc @ X51 )
      | ( v2_struct_0 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t95_tmap_1])).

thf('186',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ( ( k1_funct_1 @ ( k4_tmap_1 @ X0 @ sk_B ) @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) )
        = ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['184','185'])).

thf('187',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( ( k1_funct_1 @ ( k4_tmap_1 @ X0 @ sk_B ) @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) )
        = ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['186'])).

thf('188',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) )
      = ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['183','187'])).

thf('189',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( ( k1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) )
      = ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['188','189','190','191'])).

thf('193',plain,
    ( ( ( k1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) )
      = ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['192'])).

thf('194',plain,(
    m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('195',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( v2_struct_0 @ X38 )
      | ~ ( v2_pre_topc @ X38 )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_funct_2 @ X39 @ ( u1_struct_0 @ X38 ) @ ( u1_struct_0 @ X40 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X38 ) @ ( u1_struct_0 @ X40 ) ) ) )
      | ( m1_subset_1 @ ( sk_F @ X41 @ X39 @ X42 @ X38 @ X40 ) @ ( u1_struct_0 @ X38 ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X42 ) @ ( u1_struct_0 @ X40 ) @ ( k2_tmap_1 @ X38 @ X40 @ X39 @ X42 ) @ X41 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X42 ) @ ( u1_struct_0 @ X40 ) ) ) )
      | ~ ( v1_funct_2 @ X41 @ ( u1_struct_0 @ X42 ) @ ( u1_struct_0 @ X40 ) )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( m1_pre_topc @ X42 @ X38 )
      | ( v2_struct_0 @ X42 )
      | ~ ( l1_pre_topc @ X40 )
      | ~ ( v2_pre_topc @ X40 )
      | ( v2_struct_0 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t59_tmap_1])).

thf('197',plain,(
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
    inference('sup-',[status(thm)],['195','196'])).

thf('198',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('202',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['18','19'])).

thf('203',plain,(
    v2_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('204',plain,(
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
    inference(demod,[status(thm)],['197','198','199','200','201','202','203'])).

thf('205',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['194','204'])).

thf('206',plain,
    ( sk_C
    = ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['148','149'])).

thf('207',plain,(
    v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['156','157'])).

thf('208',plain,(
    v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['164','165'])).

thf('209',plain,(
    m1_pre_topc @ sk_B @ sk_B ),
    inference(demod,[status(thm)],['111','112','113','114'])).

thf('210',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['205','206','207','208','209'])).

thf('211',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( m1_subset_1 @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['210'])).

thf('212',plain,(
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

thf('213',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) )
      | ~ ( v1_funct_2 @ X3 @ X4 @ X5 )
      | ~ ( v1_funct_1 @ X3 )
      | ( v1_xboole_0 @ X4 )
      | ~ ( m1_subset_1 @ X6 @ X4 )
      | ( ( k3_funct_2 @ X4 @ X5 @ X3 @ X6 )
        = ( k1_funct_1 @ X3 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('214',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 )
        = ( k1_funct_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['212','213'])).

thf('215',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('216',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('217',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 )
        = ( k1_funct_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['214','215','216'])).

thf('218',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) )
      = ( k1_funct_1 @ sk_C @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['211','217'])).

thf('219',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( v2_struct_0 @ X38 )
      | ~ ( v2_pre_topc @ X38 )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_funct_2 @ X39 @ ( u1_struct_0 @ X38 ) @ ( u1_struct_0 @ X40 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X38 ) @ ( u1_struct_0 @ X40 ) ) ) )
      | ( ( k3_funct_2 @ ( u1_struct_0 @ X38 ) @ ( u1_struct_0 @ X40 ) @ X39 @ ( sk_F @ X41 @ X39 @ X42 @ X38 @ X40 ) )
       != ( k1_funct_1 @ X41 @ ( sk_F @ X41 @ X39 @ X42 @ X38 @ X40 ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X42 ) @ ( u1_struct_0 @ X40 ) @ ( k2_tmap_1 @ X38 @ X40 @ X39 @ X42 ) @ X41 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X42 ) @ ( u1_struct_0 @ X40 ) ) ) )
      | ~ ( v1_funct_2 @ X41 @ ( u1_struct_0 @ X42 ) @ ( u1_struct_0 @ X40 ) )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( m1_pre_topc @ X42 @ X38 )
      | ( v2_struct_0 @ X42 )
      | ~ ( l1_pre_topc @ X40 )
      | ~ ( v2_pre_topc @ X40 )
      | ( v2_struct_0 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t59_tmap_1])).

thf('220',plain,
    ( ( ( k1_funct_1 @ sk_C @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) )
     != ( k1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
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
    inference('sup-',[status(thm)],['218','219'])).

thf('221',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('222',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('223',plain,(
    m1_pre_topc @ sk_B @ sk_B ),
    inference(demod,[status(thm)],['111','112','113','114'])).

thf('224',plain,(
    v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['164','165'])).

thf('225',plain,(
    v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['156','157'])).

thf('226',plain,(
    m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('227',plain,
    ( sk_C
    = ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['148','149'])).

thf('228',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('229',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('230',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('231',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['18','19'])).

thf('232',plain,(
    v2_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('233',plain,
    ( ( ( k1_funct_1 @ sk_C @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) )
     != ( k1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['220','221','222','223','224','225','226','227','228','229','230','231','232'])).

thf('234',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k1_funct_1 @ sk_C @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) )
     != ( k1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['233'])).

thf('235',plain,
    ( ( ( k1_funct_1 @ sk_C @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) )
     != ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['193','234'])).

thf('236',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( ( k1_funct_1 @ sk_C @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) )
     != ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['235'])).

thf('237',plain,
    ( ( ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A )
     != ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['182','236'])).

thf('238',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['237'])).

thf('239',plain,(
    m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('240',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 )
      | ( sk_C = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('241',plain,
    ( ~ ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_C
      = ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['239','240'])).

thf('242',plain,(
    v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['164','165'])).

thf('243',plain,(
    v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['156','157'])).

thf('244',plain,
    ( ( sk_C
      = ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['241','242','243'])).

thf('245',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( sk_C
      = ( k4_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['238','244'])).

thf('246',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('247',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_C )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['245','246'])).

thf('248',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('249',plain,(
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

thf('250',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r2_funct_2 @ X8 @ X9 @ X10 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_funct_2 @ X10 @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(simplify,[status(thm)],['249'])).

thf('251',plain,
    ( ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_C ) ),
    inference('sup-',[status(thm)],['248','250'])).

thf('252',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('253',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('254',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['251','252','253'])).

thf('255',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['247','254'])).

thf('256',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('257',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['255','256'])).

thf('258',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('259',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['257','258'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('260',plain,(
    ! [X16: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X16 ) )
      | ~ ( l1_struct_0 @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('261',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['259','260'])).

thf('262',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['32','33'])).

thf('263',plain,(
    v2_struct_0 @ sk_B ),
    inference(demod,[status(thm)],['261','262'])).

thf('264',plain,(
    $false ),
    inference(demod,[status(thm)],['0','263'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LCxLopGXfs
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:25:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.06/1.28  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.06/1.28  % Solved by: fo/fo7.sh
% 1.06/1.28  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.06/1.28  % done 1238 iterations in 0.816s
% 1.06/1.28  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.06/1.28  % SZS output start Refutation
% 1.06/1.28  thf(sk_F_type, type, sk_F: $i > $i > $i > $i > $i > $i).
% 1.06/1.28  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.06/1.28  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 1.06/1.28  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 1.06/1.28  thf(sk_C_type, type, sk_C: $i).
% 1.06/1.28  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.06/1.28  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 1.06/1.28  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.06/1.28  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 1.06/1.28  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.06/1.28  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.06/1.28  thf(k4_tmap_1_type, type, k4_tmap_1: $i > $i > $i).
% 1.06/1.28  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.06/1.28  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.06/1.28  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.06/1.28  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 1.06/1.28  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 1.06/1.28  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.06/1.28  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.06/1.28  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.06/1.28  thf(sk_A_type, type, sk_A: $i).
% 1.06/1.28  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 1.06/1.28  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.06/1.28  thf(sk_B_type, type, sk_B: $i).
% 1.06/1.28  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.06/1.28  thf(t96_tmap_1, conjecture,
% 1.06/1.28    (![A:$i]:
% 1.06/1.28     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.06/1.28       ( ![B:$i]:
% 1.06/1.28         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 1.06/1.28           ( ![C:$i]:
% 1.06/1.28             ( ( ( v1_funct_1 @ C ) & 
% 1.06/1.28                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 1.06/1.28                 ( m1_subset_1 @
% 1.06/1.28                   C @ 
% 1.06/1.28                   ( k1_zfmisc_1 @
% 1.06/1.28                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 1.06/1.28               ( ( ![D:$i]:
% 1.06/1.28                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 1.06/1.28                     ( ( r2_hidden @ D @ ( u1_struct_0 @ B ) ) =>
% 1.06/1.28                       ( ( D ) = ( k1_funct_1 @ C @ D ) ) ) ) ) =>
% 1.06/1.28                 ( r2_funct_2 @
% 1.06/1.28                   ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.06/1.28                   ( k4_tmap_1 @ A @ B ) @ C ) ) ) ) ) ) ))).
% 1.06/1.28  thf(zf_stmt_0, negated_conjecture,
% 1.06/1.28    (~( ![A:$i]:
% 1.06/1.28        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.06/1.28            ( l1_pre_topc @ A ) ) =>
% 1.06/1.28          ( ![B:$i]:
% 1.06/1.28            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 1.06/1.28              ( ![C:$i]:
% 1.06/1.28                ( ( ( v1_funct_1 @ C ) & 
% 1.06/1.28                    ( v1_funct_2 @
% 1.06/1.28                      C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 1.06/1.28                    ( m1_subset_1 @
% 1.06/1.28                      C @ 
% 1.06/1.28                      ( k1_zfmisc_1 @
% 1.06/1.28                        ( k2_zfmisc_1 @
% 1.06/1.28                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 1.06/1.28                  ( ( ![D:$i]:
% 1.06/1.28                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 1.06/1.28                        ( ( r2_hidden @ D @ ( u1_struct_0 @ B ) ) =>
% 1.06/1.28                          ( ( D ) = ( k1_funct_1 @ C @ D ) ) ) ) ) =>
% 1.06/1.28                    ( r2_funct_2 @
% 1.06/1.28                      ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.06/1.28                      ( k4_tmap_1 @ A @ B ) @ C ) ) ) ) ) ) ) )),
% 1.06/1.28    inference('cnf.neg', [status(esa)], [t96_tmap_1])).
% 1.06/1.28  thf('0', plain, (~ (v2_struct_0 @ sk_B)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('1', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf(dt_k4_tmap_1, axiom,
% 1.06/1.28    (![A:$i,B:$i]:
% 1.06/1.28     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.06/1.28         ( l1_pre_topc @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 1.06/1.28       ( ( v1_funct_1 @ ( k4_tmap_1 @ A @ B ) ) & 
% 1.06/1.28         ( v1_funct_2 @
% 1.06/1.28           ( k4_tmap_1 @ A @ B ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 1.06/1.28         ( m1_subset_1 @
% 1.06/1.28           ( k4_tmap_1 @ A @ B ) @ 
% 1.06/1.28           ( k1_zfmisc_1 @
% 1.06/1.28             ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 1.06/1.28  thf('2', plain,
% 1.06/1.28      (![X30 : $i, X31 : $i]:
% 1.06/1.28         (~ (l1_pre_topc @ X30)
% 1.06/1.28          | ~ (v2_pre_topc @ X30)
% 1.06/1.28          | (v2_struct_0 @ X30)
% 1.06/1.28          | ~ (m1_pre_topc @ X31 @ X30)
% 1.06/1.28          | (m1_subset_1 @ (k4_tmap_1 @ X30 @ X31) @ 
% 1.06/1.28             (k1_zfmisc_1 @ 
% 1.06/1.28              (k2_zfmisc_1 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X30)))))),
% 1.06/1.28      inference('cnf', [status(esa)], [dt_k4_tmap_1])).
% 1.06/1.28  thf('3', plain,
% 1.06/1.28      (((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 1.06/1.28         (k1_zfmisc_1 @ 
% 1.06/1.28          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 1.06/1.28        | (v2_struct_0 @ sk_A)
% 1.06/1.28        | ~ (v2_pre_topc @ sk_A)
% 1.06/1.28        | ~ (l1_pre_topc @ sk_A))),
% 1.06/1.28      inference('sup-', [status(thm)], ['1', '2'])).
% 1.06/1.28  thf('4', plain, ((v2_pre_topc @ sk_A)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('6', plain,
% 1.06/1.28      (((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 1.06/1.28         (k1_zfmisc_1 @ 
% 1.06/1.28          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 1.06/1.28        | (v2_struct_0 @ sk_A))),
% 1.06/1.28      inference('demod', [status(thm)], ['3', '4', '5'])).
% 1.06/1.28  thf('7', plain, (~ (v2_struct_0 @ sk_A)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('8', plain,
% 1.06/1.28      ((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 1.06/1.28        (k1_zfmisc_1 @ 
% 1.06/1.28         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.06/1.28      inference('clc', [status(thm)], ['6', '7'])).
% 1.06/1.28  thf('9', plain,
% 1.06/1.28      ((m1_subset_1 @ sk_C @ 
% 1.06/1.28        (k1_zfmisc_1 @ 
% 1.06/1.28         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf(t59_tmap_1, axiom,
% 1.06/1.28    (![A:$i]:
% 1.06/1.28     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.06/1.28       ( ![B:$i]:
% 1.06/1.28         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.06/1.28             ( l1_pre_topc @ B ) ) =>
% 1.06/1.28           ( ![C:$i]:
% 1.06/1.28             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 1.06/1.28               ( ![D:$i]:
% 1.06/1.28                 ( ( ( v1_funct_1 @ D ) & 
% 1.06/1.28                     ( v1_funct_2 @
% 1.06/1.28                       D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 1.06/1.28                     ( m1_subset_1 @
% 1.06/1.28                       D @ 
% 1.06/1.28                       ( k1_zfmisc_1 @
% 1.06/1.28                         ( k2_zfmisc_1 @
% 1.06/1.28                           ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 1.06/1.28                   ( ![E:$i]:
% 1.06/1.28                     ( ( ( v1_funct_1 @ E ) & 
% 1.06/1.28                         ( v1_funct_2 @
% 1.06/1.28                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) ) & 
% 1.06/1.28                         ( m1_subset_1 @
% 1.06/1.28                           E @ 
% 1.06/1.28                           ( k1_zfmisc_1 @
% 1.06/1.28                             ( k2_zfmisc_1 @
% 1.06/1.28                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 1.06/1.28                       ( ( ![F:$i]:
% 1.06/1.28                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 1.06/1.28                             ( ( r2_hidden @ F @ ( u1_struct_0 @ C ) ) =>
% 1.06/1.28                               ( ( k3_funct_2 @
% 1.06/1.28                                   ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.06/1.28                                   D @ F ) =
% 1.06/1.28                                 ( k1_funct_1 @ E @ F ) ) ) ) ) =>
% 1.06/1.28                         ( r2_funct_2 @
% 1.06/1.28                           ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ 
% 1.06/1.28                           ( k2_tmap_1 @ B @ A @ D @ C ) @ E ) ) ) ) ) ) ) ) ) ) ))).
% 1.06/1.28  thf('10', plain,
% 1.06/1.28      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 1.06/1.28         ((v2_struct_0 @ X38)
% 1.06/1.28          | ~ (v2_pre_topc @ X38)
% 1.06/1.28          | ~ (l1_pre_topc @ X38)
% 1.06/1.28          | ~ (v1_funct_1 @ X39)
% 1.06/1.28          | ~ (v1_funct_2 @ X39 @ (u1_struct_0 @ X38) @ (u1_struct_0 @ X40))
% 1.06/1.28          | ~ (m1_subset_1 @ X39 @ 
% 1.06/1.28               (k1_zfmisc_1 @ 
% 1.06/1.28                (k2_zfmisc_1 @ (u1_struct_0 @ X38) @ (u1_struct_0 @ X40))))
% 1.06/1.28          | (r2_hidden @ (sk_F @ X41 @ X39 @ X42 @ X38 @ X40) @ 
% 1.06/1.28             (u1_struct_0 @ X42))
% 1.06/1.28          | (r2_funct_2 @ (u1_struct_0 @ X42) @ (u1_struct_0 @ X40) @ 
% 1.06/1.28             (k2_tmap_1 @ X38 @ X40 @ X39 @ X42) @ X41)
% 1.06/1.28          | ~ (m1_subset_1 @ X41 @ 
% 1.06/1.28               (k1_zfmisc_1 @ 
% 1.06/1.28                (k2_zfmisc_1 @ (u1_struct_0 @ X42) @ (u1_struct_0 @ X40))))
% 1.06/1.28          | ~ (v1_funct_2 @ X41 @ (u1_struct_0 @ X42) @ (u1_struct_0 @ X40))
% 1.06/1.28          | ~ (v1_funct_1 @ X41)
% 1.06/1.28          | ~ (m1_pre_topc @ X42 @ X38)
% 1.06/1.28          | (v2_struct_0 @ X42)
% 1.06/1.28          | ~ (l1_pre_topc @ X40)
% 1.06/1.28          | ~ (v2_pre_topc @ X40)
% 1.06/1.28          | (v2_struct_0 @ X40))),
% 1.06/1.28      inference('cnf', [status(esa)], [t59_tmap_1])).
% 1.06/1.28  thf('11', plain,
% 1.06/1.28      (![X0 : $i, X1 : $i]:
% 1.06/1.28         ((v2_struct_0 @ sk_A)
% 1.06/1.28          | ~ (v2_pre_topc @ sk_A)
% 1.06/1.28          | ~ (l1_pre_topc @ sk_A)
% 1.06/1.28          | (v2_struct_0 @ X0)
% 1.06/1.28          | ~ (m1_pre_topc @ X0 @ sk_B)
% 1.06/1.28          | ~ (v1_funct_1 @ X1)
% 1.06/1.28          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 1.06/1.28          | ~ (m1_subset_1 @ X1 @ 
% 1.06/1.28               (k1_zfmisc_1 @ 
% 1.06/1.28                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 1.06/1.28          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.28             (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ X1)
% 1.06/1.28          | (r2_hidden @ (sk_F @ X1 @ sk_C @ X0 @ sk_B @ sk_A) @ 
% 1.06/1.28             (u1_struct_0 @ X0))
% 1.06/1.28          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.06/1.28          | ~ (v1_funct_1 @ sk_C)
% 1.06/1.28          | ~ (l1_pre_topc @ sk_B)
% 1.06/1.28          | ~ (v2_pre_topc @ sk_B)
% 1.06/1.28          | (v2_struct_0 @ sk_B))),
% 1.06/1.28      inference('sup-', [status(thm)], ['9', '10'])).
% 1.06/1.28  thf('12', plain, ((v2_pre_topc @ sk_A)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('14', plain,
% 1.06/1.28      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('15', plain, ((v1_funct_1 @ sk_C)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('16', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf(dt_m1_pre_topc, axiom,
% 1.06/1.28    (![A:$i]:
% 1.06/1.28     ( ( l1_pre_topc @ A ) =>
% 1.06/1.28       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 1.06/1.28  thf('17', plain,
% 1.06/1.28      (![X14 : $i, X15 : $i]:
% 1.06/1.28         (~ (m1_pre_topc @ X14 @ X15)
% 1.06/1.28          | (l1_pre_topc @ X14)
% 1.06/1.28          | ~ (l1_pre_topc @ X15))),
% 1.06/1.28      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 1.06/1.28  thf('18', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 1.06/1.28      inference('sup-', [status(thm)], ['16', '17'])).
% 1.06/1.28  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('20', plain, ((l1_pre_topc @ sk_B)),
% 1.06/1.28      inference('demod', [status(thm)], ['18', '19'])).
% 1.06/1.28  thf('21', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf(cc1_pre_topc, axiom,
% 1.06/1.28    (![A:$i]:
% 1.06/1.28     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.06/1.28       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 1.06/1.28  thf('22', plain,
% 1.06/1.28      (![X11 : $i, X12 : $i]:
% 1.06/1.28         (~ (m1_pre_topc @ X11 @ X12)
% 1.06/1.28          | (v2_pre_topc @ X11)
% 1.06/1.28          | ~ (l1_pre_topc @ X12)
% 1.06/1.28          | ~ (v2_pre_topc @ X12))),
% 1.06/1.28      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 1.06/1.28  thf('23', plain,
% 1.06/1.28      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_B))),
% 1.06/1.28      inference('sup-', [status(thm)], ['21', '22'])).
% 1.06/1.28  thf('24', plain, ((v2_pre_topc @ sk_A)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('26', plain, ((v2_pre_topc @ sk_B)),
% 1.06/1.28      inference('demod', [status(thm)], ['23', '24', '25'])).
% 1.06/1.28  thf('27', plain,
% 1.06/1.28      (![X0 : $i, X1 : $i]:
% 1.06/1.28         ((v2_struct_0 @ sk_A)
% 1.06/1.28          | (v2_struct_0 @ X0)
% 1.06/1.28          | ~ (m1_pre_topc @ X0 @ sk_B)
% 1.06/1.28          | ~ (v1_funct_1 @ X1)
% 1.06/1.28          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 1.06/1.28          | ~ (m1_subset_1 @ X1 @ 
% 1.06/1.28               (k1_zfmisc_1 @ 
% 1.06/1.28                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 1.06/1.28          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.28             (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ X1)
% 1.06/1.28          | (r2_hidden @ (sk_F @ X1 @ sk_C @ X0 @ sk_B @ sk_A) @ 
% 1.06/1.28             (u1_struct_0 @ X0))
% 1.06/1.28          | (v2_struct_0 @ sk_B))),
% 1.06/1.28      inference('demod', [status(thm)],
% 1.06/1.28                ['11', '12', '13', '14', '15', '20', '26'])).
% 1.06/1.28  thf('28', plain,
% 1.06/1.28      (((v2_struct_0 @ sk_B)
% 1.06/1.28        | (r2_hidden @ 
% 1.06/1.28           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 1.06/1.28           (u1_struct_0 @ sk_B))
% 1.06/1.28        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.28           (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) @ (k4_tmap_1 @ sk_A @ sk_B))
% 1.06/1.28        | ~ (v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.28             (u1_struct_0 @ sk_A))
% 1.06/1.28        | ~ (v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))
% 1.06/1.28        | ~ (m1_pre_topc @ sk_B @ sk_B)
% 1.06/1.28        | (v2_struct_0 @ sk_B)
% 1.06/1.28        | (v2_struct_0 @ sk_A))),
% 1.06/1.28      inference('sup-', [status(thm)], ['8', '27'])).
% 1.06/1.28  thf('29', plain,
% 1.06/1.28      ((m1_subset_1 @ sk_C @ 
% 1.06/1.28        (k1_zfmisc_1 @ 
% 1.06/1.28         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf(dt_k2_tmap_1, axiom,
% 1.06/1.28    (![A:$i,B:$i,C:$i,D:$i]:
% 1.06/1.28     ( ( ( l1_struct_0 @ A ) & ( l1_struct_0 @ B ) & ( v1_funct_1 @ C ) & 
% 1.06/1.28         ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.06/1.28         ( m1_subset_1 @
% 1.06/1.28           C @ 
% 1.06/1.28           ( k1_zfmisc_1 @
% 1.06/1.28             ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 1.06/1.28         ( l1_struct_0 @ D ) ) =>
% 1.06/1.28       ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) ) & 
% 1.06/1.28         ( v1_funct_2 @
% 1.06/1.28           ( k2_tmap_1 @ A @ B @ C @ D ) @ ( u1_struct_0 @ D ) @ 
% 1.06/1.28           ( u1_struct_0 @ B ) ) & 
% 1.06/1.28         ( m1_subset_1 @
% 1.06/1.28           ( k2_tmap_1 @ A @ B @ C @ D ) @ 
% 1.06/1.28           ( k1_zfmisc_1 @
% 1.06/1.28             ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 1.06/1.28  thf('30', plain,
% 1.06/1.28      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 1.06/1.28         (~ (m1_subset_1 @ X26 @ 
% 1.06/1.28             (k1_zfmisc_1 @ 
% 1.06/1.28              (k2_zfmisc_1 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X28))))
% 1.06/1.28          | ~ (v1_funct_2 @ X26 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X28))
% 1.06/1.28          | ~ (v1_funct_1 @ X26)
% 1.06/1.28          | ~ (l1_struct_0 @ X28)
% 1.06/1.28          | ~ (l1_struct_0 @ X27)
% 1.06/1.28          | ~ (l1_struct_0 @ X29)
% 1.06/1.28          | (v1_funct_1 @ (k2_tmap_1 @ X27 @ X28 @ X26 @ X29)))),
% 1.06/1.28      inference('cnf', [status(esa)], [dt_k2_tmap_1])).
% 1.06/1.28  thf('31', plain,
% 1.06/1.28      (![X0 : $i]:
% 1.06/1.28         ((v1_funct_1 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0))
% 1.06/1.28          | ~ (l1_struct_0 @ X0)
% 1.06/1.28          | ~ (l1_struct_0 @ sk_B)
% 1.06/1.28          | ~ (l1_struct_0 @ sk_A)
% 1.06/1.28          | ~ (v1_funct_1 @ sk_C)
% 1.06/1.28          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 1.06/1.28      inference('sup-', [status(thm)], ['29', '30'])).
% 1.06/1.28  thf('32', plain, ((l1_pre_topc @ sk_B)),
% 1.06/1.28      inference('demod', [status(thm)], ['18', '19'])).
% 1.06/1.28  thf(dt_l1_pre_topc, axiom,
% 1.06/1.28    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 1.06/1.28  thf('33', plain,
% 1.06/1.28      (![X13 : $i]: ((l1_struct_0 @ X13) | ~ (l1_pre_topc @ X13))),
% 1.06/1.28      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.06/1.28  thf('34', plain, ((l1_struct_0 @ sk_B)),
% 1.06/1.28      inference('sup-', [status(thm)], ['32', '33'])).
% 1.06/1.28  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('36', plain,
% 1.06/1.28      (![X13 : $i]: ((l1_struct_0 @ X13) | ~ (l1_pre_topc @ X13))),
% 1.06/1.28      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.06/1.28  thf('37', plain, ((l1_struct_0 @ sk_A)),
% 1.06/1.28      inference('sup-', [status(thm)], ['35', '36'])).
% 1.06/1.28  thf('38', plain, ((v1_funct_1 @ sk_C)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('39', plain,
% 1.06/1.28      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('40', plain,
% 1.06/1.28      (![X0 : $i]:
% 1.06/1.28         ((v1_funct_1 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0))
% 1.06/1.28          | ~ (l1_struct_0 @ X0))),
% 1.06/1.28      inference('demod', [status(thm)], ['31', '34', '37', '38', '39'])).
% 1.06/1.28  thf('41', plain,
% 1.06/1.28      ((m1_subset_1 @ sk_C @ 
% 1.06/1.28        (k1_zfmisc_1 @ 
% 1.06/1.28         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('42', plain,
% 1.06/1.28      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 1.06/1.28         (~ (m1_subset_1 @ X26 @ 
% 1.06/1.28             (k1_zfmisc_1 @ 
% 1.06/1.28              (k2_zfmisc_1 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X28))))
% 1.06/1.28          | ~ (v1_funct_2 @ X26 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X28))
% 1.06/1.28          | ~ (v1_funct_1 @ X26)
% 1.06/1.28          | ~ (l1_struct_0 @ X28)
% 1.06/1.28          | ~ (l1_struct_0 @ X27)
% 1.06/1.28          | ~ (l1_struct_0 @ X29)
% 1.06/1.28          | (v1_funct_2 @ (k2_tmap_1 @ X27 @ X28 @ X26 @ X29) @ 
% 1.06/1.28             (u1_struct_0 @ X29) @ (u1_struct_0 @ X28)))),
% 1.06/1.28      inference('cnf', [status(esa)], [dt_k2_tmap_1])).
% 1.06/1.28  thf('43', plain,
% 1.06/1.28      (![X0 : $i]:
% 1.06/1.28         ((v1_funct_2 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ 
% 1.06/1.28           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 1.06/1.28          | ~ (l1_struct_0 @ X0)
% 1.06/1.28          | ~ (l1_struct_0 @ sk_B)
% 1.06/1.28          | ~ (l1_struct_0 @ sk_A)
% 1.06/1.28          | ~ (v1_funct_1 @ sk_C)
% 1.06/1.28          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 1.06/1.28      inference('sup-', [status(thm)], ['41', '42'])).
% 1.06/1.28  thf('44', plain, ((l1_struct_0 @ sk_B)),
% 1.06/1.28      inference('sup-', [status(thm)], ['32', '33'])).
% 1.06/1.28  thf('45', plain, ((l1_struct_0 @ sk_A)),
% 1.06/1.28      inference('sup-', [status(thm)], ['35', '36'])).
% 1.06/1.28  thf('46', plain, ((v1_funct_1 @ sk_C)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('47', plain,
% 1.06/1.28      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('48', plain,
% 1.06/1.28      (![X0 : $i]:
% 1.06/1.28         ((v1_funct_2 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ 
% 1.06/1.28           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 1.06/1.28          | ~ (l1_struct_0 @ X0))),
% 1.06/1.28      inference('demod', [status(thm)], ['43', '44', '45', '46', '47'])).
% 1.06/1.28  thf('49', plain,
% 1.06/1.28      ((m1_subset_1 @ sk_C @ 
% 1.06/1.28        (k1_zfmisc_1 @ 
% 1.06/1.28         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('50', plain,
% 1.06/1.28      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 1.06/1.28         (~ (m1_subset_1 @ X26 @ 
% 1.06/1.28             (k1_zfmisc_1 @ 
% 1.06/1.28              (k2_zfmisc_1 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X28))))
% 1.06/1.28          | ~ (v1_funct_2 @ X26 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X28))
% 1.06/1.28          | ~ (v1_funct_1 @ X26)
% 1.06/1.28          | ~ (l1_struct_0 @ X28)
% 1.06/1.28          | ~ (l1_struct_0 @ X27)
% 1.06/1.28          | ~ (l1_struct_0 @ X29)
% 1.06/1.28          | (m1_subset_1 @ (k2_tmap_1 @ X27 @ X28 @ X26 @ X29) @ 
% 1.06/1.28             (k1_zfmisc_1 @ 
% 1.06/1.28              (k2_zfmisc_1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X28)))))),
% 1.06/1.28      inference('cnf', [status(esa)], [dt_k2_tmap_1])).
% 1.06/1.28  thf('51', plain,
% 1.06/1.28      (![X0 : $i]:
% 1.06/1.28         ((m1_subset_1 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ 
% 1.06/1.28           (k1_zfmisc_1 @ 
% 1.06/1.28            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 1.06/1.28          | ~ (l1_struct_0 @ X0)
% 1.06/1.28          | ~ (l1_struct_0 @ sk_B)
% 1.06/1.28          | ~ (l1_struct_0 @ sk_A)
% 1.06/1.28          | ~ (v1_funct_1 @ sk_C)
% 1.06/1.28          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 1.06/1.28      inference('sup-', [status(thm)], ['49', '50'])).
% 1.06/1.28  thf('52', plain, ((l1_struct_0 @ sk_B)),
% 1.06/1.28      inference('sup-', [status(thm)], ['32', '33'])).
% 1.06/1.28  thf('53', plain, ((l1_struct_0 @ sk_A)),
% 1.06/1.28      inference('sup-', [status(thm)], ['35', '36'])).
% 1.06/1.28  thf('54', plain, ((v1_funct_1 @ sk_C)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('55', plain,
% 1.06/1.28      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('56', plain,
% 1.06/1.28      (![X0 : $i]:
% 1.06/1.28         ((m1_subset_1 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ 
% 1.06/1.28           (k1_zfmisc_1 @ 
% 1.06/1.28            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 1.06/1.28          | ~ (l1_struct_0 @ X0))),
% 1.06/1.28      inference('demod', [status(thm)], ['51', '52', '53', '54', '55'])).
% 1.06/1.28  thf('57', plain,
% 1.06/1.28      ((m1_subset_1 @ sk_C @ 
% 1.06/1.28        (k1_zfmisc_1 @ 
% 1.06/1.28         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf(redefinition_r2_funct_2, axiom,
% 1.06/1.28    (![A:$i,B:$i,C:$i,D:$i]:
% 1.06/1.28     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.06/1.28         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.06/1.28         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.06/1.28         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.06/1.28       ( ( r2_funct_2 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.06/1.28  thf('58', plain,
% 1.06/1.28      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 1.06/1.28         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9)))
% 1.06/1.28          | ~ (v1_funct_2 @ X7 @ X8 @ X9)
% 1.06/1.28          | ~ (v1_funct_1 @ X7)
% 1.06/1.28          | ~ (v1_funct_1 @ X10)
% 1.06/1.28          | ~ (v1_funct_2 @ X10 @ X8 @ X9)
% 1.06/1.28          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9)))
% 1.06/1.28          | ((X7) = (X10))
% 1.06/1.28          | ~ (r2_funct_2 @ X8 @ X9 @ X7 @ X10))),
% 1.06/1.28      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 1.06/1.28  thf('59', plain,
% 1.06/1.28      (![X0 : $i]:
% 1.06/1.28         (~ (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.28             X0)
% 1.06/1.28          | ((sk_C) = (X0))
% 1.06/1.28          | ~ (m1_subset_1 @ X0 @ 
% 1.06/1.28               (k1_zfmisc_1 @ 
% 1.06/1.28                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 1.06/1.28          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.06/1.28          | ~ (v1_funct_1 @ X0)
% 1.06/1.28          | ~ (v1_funct_1 @ sk_C)
% 1.06/1.28          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 1.06/1.28      inference('sup-', [status(thm)], ['57', '58'])).
% 1.06/1.28  thf('60', plain, ((v1_funct_1 @ sk_C)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('61', plain,
% 1.06/1.28      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('62', plain,
% 1.06/1.28      (![X0 : $i]:
% 1.06/1.28         (~ (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.28             X0)
% 1.06/1.28          | ((sk_C) = (X0))
% 1.06/1.28          | ~ (m1_subset_1 @ X0 @ 
% 1.06/1.28               (k1_zfmisc_1 @ 
% 1.06/1.28                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 1.06/1.28          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.06/1.28          | ~ (v1_funct_1 @ X0))),
% 1.06/1.28      inference('demod', [status(thm)], ['59', '60', '61'])).
% 1.06/1.28  thf('63', plain,
% 1.06/1.28      ((~ (l1_struct_0 @ sk_B)
% 1.06/1.28        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 1.06/1.28        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) @ 
% 1.06/1.28             (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.06/1.28        | ((sk_C) = (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 1.06/1.28        | ~ (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.28             (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B)))),
% 1.06/1.28      inference('sup-', [status(thm)], ['56', '62'])).
% 1.06/1.28  thf('64', plain, ((l1_struct_0 @ sk_B)),
% 1.06/1.28      inference('sup-', [status(thm)], ['32', '33'])).
% 1.06/1.28  thf('65', plain,
% 1.06/1.28      ((~ (v1_funct_1 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 1.06/1.28        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) @ 
% 1.06/1.28             (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.06/1.28        | ((sk_C) = (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 1.06/1.28        | ~ (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.28             (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B)))),
% 1.06/1.28      inference('demod', [status(thm)], ['63', '64'])).
% 1.06/1.28  thf(t2_tsep_1, axiom,
% 1.06/1.28    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 1.06/1.28  thf('66', plain,
% 1.06/1.28      (![X34 : $i]: ((m1_pre_topc @ X34 @ X34) | ~ (l1_pre_topc @ X34))),
% 1.06/1.28      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.06/1.28  thf('67', plain,
% 1.06/1.28      ((m1_subset_1 @ sk_C @ 
% 1.06/1.28        (k1_zfmisc_1 @ 
% 1.06/1.28         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf(t74_tmap_1, axiom,
% 1.06/1.28    (![A:$i]:
% 1.06/1.28     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.06/1.28       ( ![B:$i]:
% 1.06/1.28         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.06/1.28             ( l1_pre_topc @ B ) ) =>
% 1.06/1.28           ( ![C:$i]:
% 1.06/1.28             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.06/1.28               ( ![D:$i]:
% 1.06/1.28                 ( ( ( v1_funct_1 @ D ) & 
% 1.06/1.28                     ( v1_funct_2 @
% 1.06/1.28                       D @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 1.06/1.28                     ( m1_subset_1 @
% 1.06/1.28                       D @ 
% 1.06/1.28                       ( k1_zfmisc_1 @
% 1.06/1.28                         ( k2_zfmisc_1 @
% 1.06/1.28                           ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.06/1.28                   ( r2_funct_2 @
% 1.06/1.28                     ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ D @ 
% 1.06/1.28                     ( k3_tmap_1 @ A @ B @ C @ C @ D ) ) ) ) ) ) ) ) ))).
% 1.06/1.28  thf('68', plain,
% 1.06/1.28      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 1.06/1.28         ((v2_struct_0 @ X43)
% 1.06/1.28          | ~ (v2_pre_topc @ X43)
% 1.06/1.28          | ~ (l1_pre_topc @ X43)
% 1.06/1.28          | ~ (v1_funct_1 @ X44)
% 1.06/1.28          | ~ (v1_funct_2 @ X44 @ (u1_struct_0 @ X45) @ (u1_struct_0 @ X43))
% 1.06/1.28          | ~ (m1_subset_1 @ X44 @ 
% 1.06/1.28               (k1_zfmisc_1 @ 
% 1.06/1.28                (k2_zfmisc_1 @ (u1_struct_0 @ X45) @ (u1_struct_0 @ X43))))
% 1.06/1.28          | (r2_funct_2 @ (u1_struct_0 @ X45) @ (u1_struct_0 @ X43) @ X44 @ 
% 1.06/1.28             (k3_tmap_1 @ X46 @ X43 @ X45 @ X45 @ X44))
% 1.06/1.28          | ~ (m1_pre_topc @ X45 @ X46)
% 1.06/1.28          | (v2_struct_0 @ X45)
% 1.06/1.28          | ~ (l1_pre_topc @ X46)
% 1.06/1.28          | ~ (v2_pre_topc @ X46)
% 1.06/1.28          | (v2_struct_0 @ X46))),
% 1.06/1.28      inference('cnf', [status(esa)], [t74_tmap_1])).
% 1.06/1.28  thf('69', plain,
% 1.06/1.28      (![X0 : $i]:
% 1.06/1.28         ((v2_struct_0 @ X0)
% 1.06/1.28          | ~ (v2_pre_topc @ X0)
% 1.06/1.28          | ~ (l1_pre_topc @ X0)
% 1.06/1.28          | (v2_struct_0 @ sk_B)
% 1.06/1.28          | ~ (m1_pre_topc @ sk_B @ X0)
% 1.06/1.28          | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.28             (k3_tmap_1 @ X0 @ sk_A @ sk_B @ sk_B @ sk_C))
% 1.06/1.28          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.06/1.28          | ~ (v1_funct_1 @ sk_C)
% 1.06/1.28          | ~ (l1_pre_topc @ sk_A)
% 1.06/1.28          | ~ (v2_pre_topc @ sk_A)
% 1.06/1.28          | (v2_struct_0 @ sk_A))),
% 1.06/1.28      inference('sup-', [status(thm)], ['67', '68'])).
% 1.06/1.28  thf('70', plain,
% 1.06/1.28      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('71', plain, ((v1_funct_1 @ sk_C)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('72', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('73', plain, ((v2_pre_topc @ sk_A)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('74', plain,
% 1.06/1.28      (![X0 : $i]:
% 1.06/1.28         ((v2_struct_0 @ X0)
% 1.06/1.28          | ~ (v2_pre_topc @ X0)
% 1.06/1.28          | ~ (l1_pre_topc @ X0)
% 1.06/1.28          | (v2_struct_0 @ sk_B)
% 1.06/1.28          | ~ (m1_pre_topc @ sk_B @ X0)
% 1.06/1.28          | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.28             (k3_tmap_1 @ X0 @ sk_A @ sk_B @ sk_B @ sk_C))
% 1.06/1.28          | (v2_struct_0 @ sk_A))),
% 1.06/1.28      inference('demod', [status(thm)], ['69', '70', '71', '72', '73'])).
% 1.06/1.28  thf('75', plain,
% 1.06/1.28      ((~ (l1_pre_topc @ sk_B)
% 1.06/1.28        | (v2_struct_0 @ sk_A)
% 1.06/1.28        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.28           (k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C))
% 1.06/1.28        | (v2_struct_0 @ sk_B)
% 1.06/1.28        | ~ (l1_pre_topc @ sk_B)
% 1.06/1.28        | ~ (v2_pre_topc @ sk_B)
% 1.06/1.28        | (v2_struct_0 @ sk_B))),
% 1.06/1.28      inference('sup-', [status(thm)], ['66', '74'])).
% 1.06/1.28  thf('76', plain, ((l1_pre_topc @ sk_B)),
% 1.06/1.28      inference('demod', [status(thm)], ['18', '19'])).
% 1.06/1.28  thf('77', plain,
% 1.06/1.28      (![X34 : $i]: ((m1_pre_topc @ X34 @ X34) | ~ (l1_pre_topc @ X34))),
% 1.06/1.28      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.06/1.28  thf('78', plain,
% 1.06/1.28      (![X34 : $i]: ((m1_pre_topc @ X34 @ X34) | ~ (l1_pre_topc @ X34))),
% 1.06/1.28      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.06/1.28  thf('79', plain,
% 1.06/1.28      ((m1_subset_1 @ sk_C @ 
% 1.06/1.28        (k1_zfmisc_1 @ 
% 1.06/1.28         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf(d5_tmap_1, axiom,
% 1.06/1.28    (![A:$i]:
% 1.06/1.28     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.06/1.28       ( ![B:$i]:
% 1.06/1.28         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.06/1.28             ( l1_pre_topc @ B ) ) =>
% 1.06/1.28           ( ![C:$i]:
% 1.06/1.28             ( ( m1_pre_topc @ C @ A ) =>
% 1.06/1.28               ( ![D:$i]:
% 1.06/1.28                 ( ( m1_pre_topc @ D @ A ) =>
% 1.06/1.28                   ( ![E:$i]:
% 1.06/1.28                     ( ( ( v1_funct_1 @ E ) & 
% 1.06/1.28                         ( v1_funct_2 @
% 1.06/1.28                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 1.06/1.28                         ( m1_subset_1 @
% 1.06/1.28                           E @ 
% 1.06/1.28                           ( k1_zfmisc_1 @
% 1.06/1.28                             ( k2_zfmisc_1 @
% 1.06/1.28                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.06/1.28                       ( ( m1_pre_topc @ D @ C ) =>
% 1.06/1.28                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 1.06/1.28                           ( k2_partfun1 @
% 1.06/1.28                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 1.06/1.28                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.06/1.28  thf('80', plain,
% 1.06/1.28      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 1.06/1.28         ((v2_struct_0 @ X21)
% 1.06/1.28          | ~ (v2_pre_topc @ X21)
% 1.06/1.28          | ~ (l1_pre_topc @ X21)
% 1.06/1.28          | ~ (m1_pre_topc @ X22 @ X23)
% 1.06/1.28          | ~ (m1_pre_topc @ X22 @ X24)
% 1.06/1.28          | ((k3_tmap_1 @ X23 @ X21 @ X24 @ X22 @ X25)
% 1.06/1.28              = (k2_partfun1 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X21) @ 
% 1.06/1.28                 X25 @ (u1_struct_0 @ X22)))
% 1.06/1.28          | ~ (m1_subset_1 @ X25 @ 
% 1.06/1.28               (k1_zfmisc_1 @ 
% 1.06/1.28                (k2_zfmisc_1 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X21))))
% 1.06/1.28          | ~ (v1_funct_2 @ X25 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X21))
% 1.06/1.28          | ~ (v1_funct_1 @ X25)
% 1.06/1.28          | ~ (m1_pre_topc @ X24 @ X23)
% 1.06/1.28          | ~ (l1_pre_topc @ X23)
% 1.06/1.28          | ~ (v2_pre_topc @ X23)
% 1.06/1.28          | (v2_struct_0 @ X23))),
% 1.06/1.28      inference('cnf', [status(esa)], [d5_tmap_1])).
% 1.06/1.28  thf('81', plain,
% 1.06/1.28      (![X0 : $i, X1 : $i]:
% 1.06/1.28         ((v2_struct_0 @ X0)
% 1.06/1.28          | ~ (v2_pre_topc @ X0)
% 1.06/1.28          | ~ (l1_pre_topc @ X0)
% 1.06/1.28          | ~ (m1_pre_topc @ sk_B @ X0)
% 1.06/1.28          | ~ (v1_funct_1 @ sk_C)
% 1.06/1.28          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.06/1.28          | ((k3_tmap_1 @ X0 @ sk_A @ sk_B @ X1 @ sk_C)
% 1.06/1.28              = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.28                 sk_C @ (u1_struct_0 @ X1)))
% 1.06/1.28          | ~ (m1_pre_topc @ X1 @ sk_B)
% 1.06/1.28          | ~ (m1_pre_topc @ X1 @ X0)
% 1.06/1.28          | ~ (l1_pre_topc @ sk_A)
% 1.06/1.28          | ~ (v2_pre_topc @ sk_A)
% 1.06/1.28          | (v2_struct_0 @ sk_A))),
% 1.06/1.28      inference('sup-', [status(thm)], ['79', '80'])).
% 1.06/1.28  thf('82', plain, ((v1_funct_1 @ sk_C)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('83', plain,
% 1.06/1.28      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('84', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('85', plain, ((v2_pre_topc @ sk_A)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('86', plain,
% 1.06/1.28      (![X0 : $i, X1 : $i]:
% 1.06/1.28         ((v2_struct_0 @ X0)
% 1.06/1.28          | ~ (v2_pre_topc @ X0)
% 1.06/1.28          | ~ (l1_pre_topc @ X0)
% 1.06/1.28          | ~ (m1_pre_topc @ sk_B @ X0)
% 1.06/1.28          | ((k3_tmap_1 @ X0 @ sk_A @ sk_B @ X1 @ sk_C)
% 1.06/1.28              = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.28                 sk_C @ (u1_struct_0 @ X1)))
% 1.06/1.28          | ~ (m1_pre_topc @ X1 @ sk_B)
% 1.06/1.28          | ~ (m1_pre_topc @ X1 @ X0)
% 1.06/1.28          | (v2_struct_0 @ sk_A))),
% 1.06/1.28      inference('demod', [status(thm)], ['81', '82', '83', '84', '85'])).
% 1.06/1.28  thf('87', plain,
% 1.06/1.28      (![X0 : $i]:
% 1.06/1.28         (~ (l1_pre_topc @ sk_B)
% 1.06/1.28          | (v2_struct_0 @ sk_A)
% 1.06/1.28          | ~ (m1_pre_topc @ X0 @ sk_B)
% 1.06/1.28          | ~ (m1_pre_topc @ X0 @ sk_B)
% 1.06/1.28          | ((k3_tmap_1 @ sk_B @ sk_A @ sk_B @ X0 @ sk_C)
% 1.06/1.28              = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.28                 sk_C @ (u1_struct_0 @ X0)))
% 1.06/1.28          | ~ (l1_pre_topc @ sk_B)
% 1.06/1.28          | ~ (v2_pre_topc @ sk_B)
% 1.06/1.28          | (v2_struct_0 @ sk_B))),
% 1.06/1.28      inference('sup-', [status(thm)], ['78', '86'])).
% 1.06/1.28  thf('88', plain, ((l1_pre_topc @ sk_B)),
% 1.06/1.28      inference('demod', [status(thm)], ['18', '19'])).
% 1.06/1.28  thf('89', plain, ((l1_pre_topc @ sk_B)),
% 1.06/1.28      inference('demod', [status(thm)], ['18', '19'])).
% 1.06/1.28  thf('90', plain, ((v2_pre_topc @ sk_B)),
% 1.06/1.28      inference('demod', [status(thm)], ['23', '24', '25'])).
% 1.06/1.28  thf('91', plain,
% 1.06/1.28      (![X0 : $i]:
% 1.06/1.28         ((v2_struct_0 @ sk_A)
% 1.06/1.28          | ~ (m1_pre_topc @ X0 @ sk_B)
% 1.06/1.28          | ~ (m1_pre_topc @ X0 @ sk_B)
% 1.06/1.28          | ((k3_tmap_1 @ sk_B @ sk_A @ sk_B @ X0 @ sk_C)
% 1.06/1.28              = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.28                 sk_C @ (u1_struct_0 @ X0)))
% 1.06/1.28          | (v2_struct_0 @ sk_B))),
% 1.06/1.28      inference('demod', [status(thm)], ['87', '88', '89', '90'])).
% 1.06/1.28  thf('92', plain,
% 1.06/1.28      (![X0 : $i]:
% 1.06/1.28         ((v2_struct_0 @ sk_B)
% 1.06/1.28          | ((k3_tmap_1 @ sk_B @ sk_A @ sk_B @ X0 @ sk_C)
% 1.06/1.28              = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.28                 sk_C @ (u1_struct_0 @ X0)))
% 1.06/1.28          | ~ (m1_pre_topc @ X0 @ sk_B)
% 1.06/1.28          | (v2_struct_0 @ sk_A))),
% 1.06/1.28      inference('simplify', [status(thm)], ['91'])).
% 1.06/1.28  thf('93', plain,
% 1.06/1.28      ((~ (l1_pre_topc @ sk_B)
% 1.06/1.28        | (v2_struct_0 @ sk_A)
% 1.06/1.28        | ((k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C)
% 1.06/1.28            = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.28               sk_C @ (u1_struct_0 @ sk_B)))
% 1.06/1.28        | (v2_struct_0 @ sk_B))),
% 1.06/1.28      inference('sup-', [status(thm)], ['77', '92'])).
% 1.06/1.28  thf('94', plain, ((l1_pre_topc @ sk_B)),
% 1.06/1.28      inference('demod', [status(thm)], ['18', '19'])).
% 1.06/1.28  thf('95', plain,
% 1.06/1.28      (![X34 : $i]: ((m1_pre_topc @ X34 @ X34) | ~ (l1_pre_topc @ X34))),
% 1.06/1.28      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.06/1.28  thf('96', plain,
% 1.06/1.28      (![X34 : $i]: ((m1_pre_topc @ X34 @ X34) | ~ (l1_pre_topc @ X34))),
% 1.06/1.28      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.06/1.28  thf('97', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('98', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf(t4_tsep_1, axiom,
% 1.06/1.28    (![A:$i]:
% 1.06/1.28     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.06/1.28       ( ![B:$i]:
% 1.06/1.28         ( ( m1_pre_topc @ B @ A ) =>
% 1.06/1.28           ( ![C:$i]:
% 1.06/1.28             ( ( m1_pre_topc @ C @ A ) =>
% 1.06/1.28               ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) <=>
% 1.06/1.28                 ( m1_pre_topc @ B @ C ) ) ) ) ) ) ))).
% 1.06/1.28  thf('99', plain,
% 1.06/1.28      (![X35 : $i, X36 : $i, X37 : $i]:
% 1.06/1.28         (~ (m1_pre_topc @ X35 @ X36)
% 1.06/1.28          | ~ (m1_pre_topc @ X35 @ X37)
% 1.06/1.28          | (r1_tarski @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X37))
% 1.06/1.28          | ~ (m1_pre_topc @ X37 @ X36)
% 1.06/1.28          | ~ (l1_pre_topc @ X36)
% 1.06/1.28          | ~ (v2_pre_topc @ X36))),
% 1.06/1.28      inference('cnf', [status(esa)], [t4_tsep_1])).
% 1.06/1.28  thf('100', plain,
% 1.06/1.28      (![X0 : $i]:
% 1.06/1.28         (~ (v2_pre_topc @ sk_A)
% 1.06/1.28          | ~ (l1_pre_topc @ sk_A)
% 1.06/1.28          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.06/1.28          | (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X0))
% 1.06/1.28          | ~ (m1_pre_topc @ sk_B @ X0))),
% 1.06/1.28      inference('sup-', [status(thm)], ['98', '99'])).
% 1.06/1.28  thf('101', plain, ((v2_pre_topc @ sk_A)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('102', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('103', plain,
% 1.06/1.28      (![X0 : $i]:
% 1.06/1.28         (~ (m1_pre_topc @ X0 @ sk_A)
% 1.06/1.28          | (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X0))
% 1.06/1.28          | ~ (m1_pre_topc @ sk_B @ X0))),
% 1.06/1.28      inference('demod', [status(thm)], ['100', '101', '102'])).
% 1.06/1.28  thf('104', plain,
% 1.06/1.28      ((~ (m1_pre_topc @ sk_B @ sk_B)
% 1.06/1.28        | (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_B)))),
% 1.06/1.28      inference('sup-', [status(thm)], ['97', '103'])).
% 1.06/1.28  thf('105', plain,
% 1.06/1.28      ((~ (l1_pre_topc @ sk_B)
% 1.06/1.28        | (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_B)))),
% 1.06/1.28      inference('sup-', [status(thm)], ['96', '104'])).
% 1.06/1.28  thf('106', plain, ((l1_pre_topc @ sk_B)),
% 1.06/1.28      inference('demod', [status(thm)], ['18', '19'])).
% 1.06/1.28  thf('107', plain,
% 1.06/1.28      ((r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_B))),
% 1.06/1.28      inference('demod', [status(thm)], ['105', '106'])).
% 1.06/1.28  thf('108', plain,
% 1.06/1.28      (![X35 : $i, X36 : $i, X37 : $i]:
% 1.06/1.28         (~ (m1_pre_topc @ X35 @ X36)
% 1.06/1.28          | ~ (r1_tarski @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X37))
% 1.06/1.28          | (m1_pre_topc @ X35 @ X37)
% 1.06/1.28          | ~ (m1_pre_topc @ X37 @ X36)
% 1.06/1.28          | ~ (l1_pre_topc @ X36)
% 1.06/1.28          | ~ (v2_pre_topc @ X36))),
% 1.06/1.28      inference('cnf', [status(esa)], [t4_tsep_1])).
% 1.06/1.28  thf('109', plain,
% 1.06/1.28      (![X0 : $i]:
% 1.06/1.28         (~ (v2_pre_topc @ X0)
% 1.06/1.28          | ~ (l1_pre_topc @ X0)
% 1.06/1.28          | ~ (m1_pre_topc @ sk_B @ X0)
% 1.06/1.28          | (m1_pre_topc @ sk_B @ sk_B)
% 1.06/1.28          | ~ (m1_pre_topc @ sk_B @ X0))),
% 1.06/1.28      inference('sup-', [status(thm)], ['107', '108'])).
% 1.06/1.28  thf('110', plain,
% 1.06/1.28      (![X0 : $i]:
% 1.06/1.28         ((m1_pre_topc @ sk_B @ sk_B)
% 1.06/1.28          | ~ (m1_pre_topc @ sk_B @ X0)
% 1.06/1.28          | ~ (l1_pre_topc @ X0)
% 1.06/1.28          | ~ (v2_pre_topc @ X0))),
% 1.06/1.28      inference('simplify', [status(thm)], ['109'])).
% 1.06/1.28  thf('111', plain,
% 1.06/1.28      ((~ (l1_pre_topc @ sk_B)
% 1.06/1.28        | ~ (v2_pre_topc @ sk_B)
% 1.06/1.28        | ~ (l1_pre_topc @ sk_B)
% 1.06/1.28        | (m1_pre_topc @ sk_B @ sk_B))),
% 1.06/1.28      inference('sup-', [status(thm)], ['95', '110'])).
% 1.06/1.28  thf('112', plain, ((l1_pre_topc @ sk_B)),
% 1.06/1.28      inference('demod', [status(thm)], ['18', '19'])).
% 1.06/1.28  thf('113', plain, ((v2_pre_topc @ sk_B)),
% 1.06/1.28      inference('demod', [status(thm)], ['23', '24', '25'])).
% 1.06/1.28  thf('114', plain, ((l1_pre_topc @ sk_B)),
% 1.06/1.28      inference('demod', [status(thm)], ['18', '19'])).
% 1.06/1.28  thf('115', plain, ((m1_pre_topc @ sk_B @ sk_B)),
% 1.06/1.28      inference('demod', [status(thm)], ['111', '112', '113', '114'])).
% 1.06/1.28  thf('116', plain,
% 1.06/1.28      ((m1_subset_1 @ sk_C @ 
% 1.06/1.28        (k1_zfmisc_1 @ 
% 1.06/1.28         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf(d4_tmap_1, axiom,
% 1.06/1.28    (![A:$i]:
% 1.06/1.28     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.06/1.28       ( ![B:$i]:
% 1.06/1.28         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.06/1.28             ( l1_pre_topc @ B ) ) =>
% 1.06/1.28           ( ![C:$i]:
% 1.06/1.28             ( ( ( v1_funct_1 @ C ) & 
% 1.06/1.28                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.06/1.28                 ( m1_subset_1 @
% 1.06/1.28                   C @ 
% 1.06/1.28                   ( k1_zfmisc_1 @
% 1.06/1.28                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.06/1.28               ( ![D:$i]:
% 1.06/1.28                 ( ( m1_pre_topc @ D @ A ) =>
% 1.06/1.28                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 1.06/1.28                     ( k2_partfun1 @
% 1.06/1.28                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 1.06/1.28                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 1.06/1.28  thf('117', plain,
% 1.06/1.28      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 1.06/1.28         ((v2_struct_0 @ X17)
% 1.06/1.28          | ~ (v2_pre_topc @ X17)
% 1.06/1.28          | ~ (l1_pre_topc @ X17)
% 1.06/1.28          | ~ (m1_pre_topc @ X18 @ X19)
% 1.06/1.28          | ((k2_tmap_1 @ X19 @ X17 @ X20 @ X18)
% 1.06/1.28              = (k2_partfun1 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X17) @ 
% 1.06/1.28                 X20 @ (u1_struct_0 @ X18)))
% 1.06/1.28          | ~ (m1_subset_1 @ X20 @ 
% 1.06/1.28               (k1_zfmisc_1 @ 
% 1.06/1.28                (k2_zfmisc_1 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X17))))
% 1.06/1.28          | ~ (v1_funct_2 @ X20 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X17))
% 1.06/1.28          | ~ (v1_funct_1 @ X20)
% 1.06/1.28          | ~ (l1_pre_topc @ X19)
% 1.06/1.28          | ~ (v2_pre_topc @ X19)
% 1.06/1.28          | (v2_struct_0 @ X19))),
% 1.06/1.28      inference('cnf', [status(esa)], [d4_tmap_1])).
% 1.06/1.28  thf('118', plain,
% 1.06/1.28      (![X0 : $i]:
% 1.06/1.28         ((v2_struct_0 @ sk_B)
% 1.06/1.28          | ~ (v2_pre_topc @ sk_B)
% 1.06/1.28          | ~ (l1_pre_topc @ sk_B)
% 1.06/1.28          | ~ (v1_funct_1 @ sk_C)
% 1.06/1.28          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.06/1.28          | ((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0)
% 1.06/1.28              = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.28                 sk_C @ (u1_struct_0 @ X0)))
% 1.06/1.28          | ~ (m1_pre_topc @ X0 @ sk_B)
% 1.06/1.28          | ~ (l1_pre_topc @ sk_A)
% 1.06/1.28          | ~ (v2_pre_topc @ sk_A)
% 1.06/1.28          | (v2_struct_0 @ sk_A))),
% 1.06/1.28      inference('sup-', [status(thm)], ['116', '117'])).
% 1.06/1.28  thf('119', plain, ((v2_pre_topc @ sk_B)),
% 1.06/1.28      inference('demod', [status(thm)], ['23', '24', '25'])).
% 1.06/1.28  thf('120', plain, ((l1_pre_topc @ sk_B)),
% 1.06/1.28      inference('demod', [status(thm)], ['18', '19'])).
% 1.06/1.28  thf('121', plain, ((v1_funct_1 @ sk_C)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('122', plain,
% 1.06/1.28      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('123', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('124', plain, ((v2_pre_topc @ sk_A)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('125', plain,
% 1.06/1.28      (![X0 : $i]:
% 1.06/1.28         ((v2_struct_0 @ sk_B)
% 1.06/1.28          | ((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0)
% 1.06/1.28              = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.28                 sk_C @ (u1_struct_0 @ X0)))
% 1.06/1.28          | ~ (m1_pre_topc @ X0 @ sk_B)
% 1.06/1.28          | (v2_struct_0 @ sk_A))),
% 1.06/1.28      inference('demod', [status(thm)],
% 1.06/1.28                ['118', '119', '120', '121', '122', '123', '124'])).
% 1.06/1.28  thf('126', plain,
% 1.06/1.28      (((v2_struct_0 @ sk_A)
% 1.06/1.28        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B)
% 1.06/1.28            = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.28               sk_C @ (u1_struct_0 @ sk_B)))
% 1.06/1.28        | (v2_struct_0 @ sk_B))),
% 1.06/1.28      inference('sup-', [status(thm)], ['115', '125'])).
% 1.06/1.28  thf('127', plain, (~ (v2_struct_0 @ sk_A)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('128', plain,
% 1.06/1.28      (((v2_struct_0 @ sk_B)
% 1.06/1.28        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B)
% 1.06/1.28            = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.28               sk_C @ (u1_struct_0 @ sk_B))))),
% 1.06/1.28      inference('clc', [status(thm)], ['126', '127'])).
% 1.06/1.28  thf('129', plain, (~ (v2_struct_0 @ sk_B)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('130', plain,
% 1.06/1.28      (((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B)
% 1.06/1.28         = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.28            (u1_struct_0 @ sk_B)))),
% 1.06/1.28      inference('clc', [status(thm)], ['128', '129'])).
% 1.06/1.28  thf('131', plain,
% 1.06/1.28      (((v2_struct_0 @ sk_A)
% 1.06/1.28        | ((k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C)
% 1.06/1.28            = (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 1.06/1.28        | (v2_struct_0 @ sk_B))),
% 1.06/1.28      inference('demod', [status(thm)], ['93', '94', '130'])).
% 1.06/1.28  thf('132', plain, (~ (v2_struct_0 @ sk_A)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('133', plain,
% 1.06/1.28      (((v2_struct_0 @ sk_B)
% 1.06/1.28        | ((k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C)
% 1.06/1.28            = (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B)))),
% 1.06/1.28      inference('clc', [status(thm)], ['131', '132'])).
% 1.06/1.28  thf('134', plain, (~ (v2_struct_0 @ sk_B)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('135', plain,
% 1.06/1.28      (((k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C)
% 1.06/1.28         = (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B))),
% 1.06/1.28      inference('clc', [status(thm)], ['133', '134'])).
% 1.06/1.28  thf('136', plain, ((l1_pre_topc @ sk_B)),
% 1.06/1.28      inference('demod', [status(thm)], ['18', '19'])).
% 1.06/1.28  thf('137', plain, ((v2_pre_topc @ sk_B)),
% 1.06/1.28      inference('demod', [status(thm)], ['23', '24', '25'])).
% 1.06/1.28  thf('138', plain,
% 1.06/1.28      (((v2_struct_0 @ sk_A)
% 1.06/1.28        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.28           (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 1.06/1.28        | (v2_struct_0 @ sk_B)
% 1.06/1.28        | (v2_struct_0 @ sk_B))),
% 1.06/1.28      inference('demod', [status(thm)], ['75', '76', '135', '136', '137'])).
% 1.06/1.28  thf('139', plain,
% 1.06/1.28      (((v2_struct_0 @ sk_B)
% 1.06/1.28        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.28           (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 1.06/1.28        | (v2_struct_0 @ sk_A))),
% 1.06/1.28      inference('simplify', [status(thm)], ['138'])).
% 1.06/1.28  thf('140', plain, (~ (v2_struct_0 @ sk_B)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('141', plain,
% 1.06/1.28      (((v2_struct_0 @ sk_A)
% 1.06/1.28        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.28           (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B)))),
% 1.06/1.28      inference('clc', [status(thm)], ['139', '140'])).
% 1.06/1.28  thf('142', plain, (~ (v2_struct_0 @ sk_A)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('143', plain,
% 1.06/1.28      ((r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.28        (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B))),
% 1.06/1.28      inference('clc', [status(thm)], ['141', '142'])).
% 1.06/1.28  thf('144', plain,
% 1.06/1.28      ((~ (v1_funct_1 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 1.06/1.28        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) @ 
% 1.06/1.28             (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.06/1.28        | ((sk_C) = (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B)))),
% 1.06/1.28      inference('demod', [status(thm)], ['65', '143'])).
% 1.06/1.28  thf('145', plain,
% 1.06/1.28      ((~ (l1_struct_0 @ sk_B)
% 1.06/1.28        | ((sk_C) = (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 1.06/1.28        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B)))),
% 1.06/1.28      inference('sup-', [status(thm)], ['48', '144'])).
% 1.06/1.28  thf('146', plain, ((l1_struct_0 @ sk_B)),
% 1.06/1.28      inference('sup-', [status(thm)], ['32', '33'])).
% 1.06/1.28  thf('147', plain,
% 1.06/1.28      ((((sk_C) = (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 1.06/1.28        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B)))),
% 1.06/1.28      inference('demod', [status(thm)], ['145', '146'])).
% 1.06/1.28  thf('148', plain,
% 1.06/1.28      ((~ (l1_struct_0 @ sk_B)
% 1.06/1.28        | ((sk_C) = (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B)))),
% 1.06/1.28      inference('sup-', [status(thm)], ['40', '147'])).
% 1.06/1.28  thf('149', plain, ((l1_struct_0 @ sk_B)),
% 1.06/1.28      inference('sup-', [status(thm)], ['32', '33'])).
% 1.06/1.28  thf('150', plain, (((sk_C) = (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B))),
% 1.06/1.28      inference('demod', [status(thm)], ['148', '149'])).
% 1.06/1.28  thf('151', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('152', plain,
% 1.06/1.28      (![X30 : $i, X31 : $i]:
% 1.06/1.28         (~ (l1_pre_topc @ X30)
% 1.06/1.28          | ~ (v2_pre_topc @ X30)
% 1.06/1.28          | (v2_struct_0 @ X30)
% 1.06/1.28          | ~ (m1_pre_topc @ X31 @ X30)
% 1.06/1.28          | (v1_funct_2 @ (k4_tmap_1 @ X30 @ X31) @ (u1_struct_0 @ X31) @ 
% 1.06/1.28             (u1_struct_0 @ X30)))),
% 1.06/1.28      inference('cnf', [status(esa)], [dt_k4_tmap_1])).
% 1.06/1.28  thf('153', plain,
% 1.06/1.28      (((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.28         (u1_struct_0 @ sk_A))
% 1.06/1.28        | (v2_struct_0 @ sk_A)
% 1.06/1.28        | ~ (v2_pre_topc @ sk_A)
% 1.06/1.28        | ~ (l1_pre_topc @ sk_A))),
% 1.06/1.28      inference('sup-', [status(thm)], ['151', '152'])).
% 1.06/1.28  thf('154', plain, ((v2_pre_topc @ sk_A)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('155', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('156', plain,
% 1.06/1.28      (((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.28         (u1_struct_0 @ sk_A))
% 1.06/1.28        | (v2_struct_0 @ sk_A))),
% 1.06/1.28      inference('demod', [status(thm)], ['153', '154', '155'])).
% 1.06/1.28  thf('157', plain, (~ (v2_struct_0 @ sk_A)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('158', plain,
% 1.06/1.28      ((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.28        (u1_struct_0 @ sk_A))),
% 1.06/1.28      inference('clc', [status(thm)], ['156', '157'])).
% 1.06/1.28  thf('159', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('160', plain,
% 1.06/1.28      (![X30 : $i, X31 : $i]:
% 1.06/1.28         (~ (l1_pre_topc @ X30)
% 1.06/1.28          | ~ (v2_pre_topc @ X30)
% 1.06/1.28          | (v2_struct_0 @ X30)
% 1.06/1.28          | ~ (m1_pre_topc @ X31 @ X30)
% 1.06/1.28          | (v1_funct_1 @ (k4_tmap_1 @ X30 @ X31)))),
% 1.06/1.28      inference('cnf', [status(esa)], [dt_k4_tmap_1])).
% 1.06/1.28  thf('161', plain,
% 1.06/1.28      (((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))
% 1.06/1.28        | (v2_struct_0 @ sk_A)
% 1.06/1.28        | ~ (v2_pre_topc @ sk_A)
% 1.06/1.28        | ~ (l1_pre_topc @ sk_A))),
% 1.06/1.28      inference('sup-', [status(thm)], ['159', '160'])).
% 1.06/1.28  thf('162', plain, ((v2_pre_topc @ sk_A)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('163', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('164', plain,
% 1.06/1.28      (((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 1.06/1.28      inference('demod', [status(thm)], ['161', '162', '163'])).
% 1.06/1.28  thf('165', plain, (~ (v2_struct_0 @ sk_A)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('166', plain, ((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))),
% 1.06/1.28      inference('clc', [status(thm)], ['164', '165'])).
% 1.06/1.28  thf('167', plain, ((m1_pre_topc @ sk_B @ sk_B)),
% 1.06/1.28      inference('demod', [status(thm)], ['111', '112', '113', '114'])).
% 1.06/1.28  thf('168', plain,
% 1.06/1.28      (((v2_struct_0 @ sk_B)
% 1.06/1.28        | (r2_hidden @ 
% 1.06/1.28           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 1.06/1.28           (u1_struct_0 @ sk_B))
% 1.06/1.28        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.28           (k4_tmap_1 @ sk_A @ sk_B))
% 1.06/1.28        | (v2_struct_0 @ sk_B)
% 1.06/1.28        | (v2_struct_0 @ sk_A))),
% 1.06/1.28      inference('demod', [status(thm)], ['28', '150', '158', '166', '167'])).
% 1.06/1.28  thf('169', plain,
% 1.06/1.28      (((v2_struct_0 @ sk_A)
% 1.06/1.28        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.28           (k4_tmap_1 @ sk_A @ sk_B))
% 1.06/1.28        | (r2_hidden @ 
% 1.06/1.28           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 1.06/1.28           (u1_struct_0 @ sk_B))
% 1.06/1.28        | (v2_struct_0 @ sk_B))),
% 1.06/1.28      inference('simplify', [status(thm)], ['168'])).
% 1.06/1.28  thf('170', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf(t1_tsep_1, axiom,
% 1.06/1.28    (![A:$i]:
% 1.06/1.28     ( ( l1_pre_topc @ A ) =>
% 1.06/1.28       ( ![B:$i]:
% 1.06/1.28         ( ( m1_pre_topc @ B @ A ) =>
% 1.06/1.28           ( m1_subset_1 @
% 1.06/1.28             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 1.06/1.28  thf('171', plain,
% 1.06/1.28      (![X32 : $i, X33 : $i]:
% 1.06/1.28         (~ (m1_pre_topc @ X32 @ X33)
% 1.06/1.28          | (m1_subset_1 @ (u1_struct_0 @ X32) @ 
% 1.06/1.28             (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 1.06/1.28          | ~ (l1_pre_topc @ X33))),
% 1.06/1.28      inference('cnf', [status(esa)], [t1_tsep_1])).
% 1.06/1.28  thf('172', plain,
% 1.06/1.28      ((~ (l1_pre_topc @ sk_A)
% 1.06/1.28        | (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.28           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.06/1.28      inference('sup-', [status(thm)], ['170', '171'])).
% 1.06/1.28  thf('173', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('174', plain,
% 1.06/1.28      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.28        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.28      inference('demod', [status(thm)], ['172', '173'])).
% 1.06/1.28  thf(t4_subset, axiom,
% 1.06/1.28    (![A:$i,B:$i,C:$i]:
% 1.06/1.28     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 1.06/1.28       ( m1_subset_1 @ A @ C ) ))).
% 1.06/1.28  thf('175', plain,
% 1.06/1.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.06/1.28         (~ (r2_hidden @ X0 @ X1)
% 1.06/1.28          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2))
% 1.06/1.28          | (m1_subset_1 @ X0 @ X2))),
% 1.06/1.28      inference('cnf', [status(esa)], [t4_subset])).
% 1.06/1.28  thf('176', plain,
% 1.06/1.28      (![X0 : $i]:
% 1.06/1.28         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.06/1.28          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_B)))),
% 1.06/1.28      inference('sup-', [status(thm)], ['174', '175'])).
% 1.06/1.28  thf('177', plain,
% 1.06/1.28      (((v2_struct_0 @ sk_B)
% 1.06/1.28        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.28           (k4_tmap_1 @ sk_A @ sk_B))
% 1.06/1.28        | (v2_struct_0 @ sk_A)
% 1.06/1.28        | (m1_subset_1 @ 
% 1.06/1.28           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 1.06/1.28           (u1_struct_0 @ sk_A)))),
% 1.06/1.28      inference('sup-', [status(thm)], ['169', '176'])).
% 1.06/1.28  thf('178', plain,
% 1.06/1.28      (((v2_struct_0 @ sk_A)
% 1.06/1.28        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.28           (k4_tmap_1 @ sk_A @ sk_B))
% 1.06/1.28        | (r2_hidden @ 
% 1.06/1.28           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 1.06/1.28           (u1_struct_0 @ sk_B))
% 1.06/1.28        | (v2_struct_0 @ sk_B))),
% 1.06/1.28      inference('simplify', [status(thm)], ['168'])).
% 1.06/1.28  thf('179', plain,
% 1.06/1.28      (![X53 : $i]:
% 1.06/1.28         (~ (r2_hidden @ X53 @ (u1_struct_0 @ sk_B))
% 1.06/1.28          | ((X53) = (k1_funct_1 @ sk_C @ X53))
% 1.06/1.28          | ~ (m1_subset_1 @ X53 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('180', plain,
% 1.06/1.28      (((v2_struct_0 @ sk_B)
% 1.06/1.28        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.28           (k4_tmap_1 @ sk_A @ sk_B))
% 1.06/1.28        | (v2_struct_0 @ sk_A)
% 1.06/1.28        | ~ (m1_subset_1 @ 
% 1.06/1.28             (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 1.06/1.28             (u1_struct_0 @ sk_A))
% 1.06/1.28        | ((sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A)
% 1.06/1.28            = (k1_funct_1 @ sk_C @ 
% 1.06/1.28               (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))))),
% 1.06/1.28      inference('sup-', [status(thm)], ['178', '179'])).
% 1.06/1.28  thf('181', plain,
% 1.06/1.28      (((v2_struct_0 @ sk_A)
% 1.06/1.28        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.28           (k4_tmap_1 @ sk_A @ sk_B))
% 1.06/1.28        | (v2_struct_0 @ sk_B)
% 1.06/1.28        | ((sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A)
% 1.06/1.28            = (k1_funct_1 @ sk_C @ 
% 1.06/1.28               (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A)))
% 1.06/1.28        | (v2_struct_0 @ sk_A)
% 1.06/1.28        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.28           (k4_tmap_1 @ sk_A @ sk_B))
% 1.06/1.28        | (v2_struct_0 @ sk_B))),
% 1.06/1.28      inference('sup-', [status(thm)], ['177', '180'])).
% 1.06/1.28  thf('182', plain,
% 1.06/1.28      ((((sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A)
% 1.06/1.28          = (k1_funct_1 @ sk_C @ 
% 1.06/1.28             (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A)))
% 1.06/1.28        | (v2_struct_0 @ sk_B)
% 1.06/1.28        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.28           (k4_tmap_1 @ sk_A @ sk_B))
% 1.06/1.28        | (v2_struct_0 @ sk_A))),
% 1.06/1.28      inference('simplify', [status(thm)], ['181'])).
% 1.06/1.28  thf('183', plain,
% 1.06/1.28      (((v2_struct_0 @ sk_B)
% 1.06/1.28        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.28           (k4_tmap_1 @ sk_A @ sk_B))
% 1.06/1.28        | (v2_struct_0 @ sk_A)
% 1.06/1.28        | (m1_subset_1 @ 
% 1.06/1.28           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 1.06/1.28           (u1_struct_0 @ sk_A)))),
% 1.06/1.28      inference('sup-', [status(thm)], ['169', '176'])).
% 1.06/1.28  thf('184', plain,
% 1.06/1.28      (((v2_struct_0 @ sk_A)
% 1.06/1.28        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.28           (k4_tmap_1 @ sk_A @ sk_B))
% 1.06/1.28        | (r2_hidden @ 
% 1.06/1.28           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 1.06/1.28           (u1_struct_0 @ sk_B))
% 1.06/1.28        | (v2_struct_0 @ sk_B))),
% 1.06/1.28      inference('simplify', [status(thm)], ['168'])).
% 1.06/1.28  thf(t95_tmap_1, axiom,
% 1.06/1.28    (![A:$i]:
% 1.06/1.28     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.06/1.28       ( ![B:$i]:
% 1.06/1.28         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 1.06/1.28           ( ![C:$i]:
% 1.06/1.28             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 1.06/1.28               ( ( r2_hidden @ C @ ( u1_struct_0 @ B ) ) =>
% 1.06/1.28                 ( ( k1_funct_1 @ ( k4_tmap_1 @ A @ B ) @ C ) = ( C ) ) ) ) ) ) ) ))).
% 1.06/1.28  thf('185', plain,
% 1.06/1.28      (![X50 : $i, X51 : $i, X52 : $i]:
% 1.06/1.28         ((v2_struct_0 @ X50)
% 1.06/1.28          | ~ (m1_pre_topc @ X50 @ X51)
% 1.06/1.28          | ~ (r2_hidden @ X52 @ (u1_struct_0 @ X50))
% 1.06/1.28          | ((k1_funct_1 @ (k4_tmap_1 @ X51 @ X50) @ X52) = (X52))
% 1.06/1.28          | ~ (m1_subset_1 @ X52 @ (u1_struct_0 @ X51))
% 1.06/1.28          | ~ (l1_pre_topc @ X51)
% 1.06/1.28          | ~ (v2_pre_topc @ X51)
% 1.06/1.28          | (v2_struct_0 @ X51))),
% 1.06/1.28      inference('cnf', [status(esa)], [t95_tmap_1])).
% 1.06/1.28  thf('186', plain,
% 1.06/1.28      (![X0 : $i]:
% 1.06/1.28         ((v2_struct_0 @ sk_B)
% 1.06/1.28          | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.28             (k4_tmap_1 @ sk_A @ sk_B))
% 1.06/1.28          | (v2_struct_0 @ sk_A)
% 1.06/1.28          | (v2_struct_0 @ X0)
% 1.06/1.28          | ~ (v2_pre_topc @ X0)
% 1.06/1.28          | ~ (l1_pre_topc @ X0)
% 1.06/1.28          | ~ (m1_subset_1 @ 
% 1.06/1.28               (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 1.06/1.28               (u1_struct_0 @ X0))
% 1.06/1.28          | ((k1_funct_1 @ (k4_tmap_1 @ X0 @ sk_B) @ 
% 1.06/1.28              (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))
% 1.06/1.28              = (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))
% 1.06/1.28          | ~ (m1_pre_topc @ sk_B @ X0)
% 1.06/1.28          | (v2_struct_0 @ sk_B))),
% 1.06/1.28      inference('sup-', [status(thm)], ['184', '185'])).
% 1.06/1.28  thf('187', plain,
% 1.06/1.28      (![X0 : $i]:
% 1.06/1.28         (~ (m1_pre_topc @ sk_B @ X0)
% 1.06/1.28          | ((k1_funct_1 @ (k4_tmap_1 @ X0 @ sk_B) @ 
% 1.06/1.28              (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))
% 1.06/1.28              = (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))
% 1.06/1.28          | ~ (m1_subset_1 @ 
% 1.06/1.28               (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 1.06/1.28               (u1_struct_0 @ X0))
% 1.06/1.28          | ~ (l1_pre_topc @ X0)
% 1.06/1.28          | ~ (v2_pre_topc @ X0)
% 1.06/1.28          | (v2_struct_0 @ X0)
% 1.06/1.28          | (v2_struct_0 @ sk_A)
% 1.06/1.28          | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.28             (k4_tmap_1 @ sk_A @ sk_B))
% 1.06/1.28          | (v2_struct_0 @ sk_B))),
% 1.06/1.28      inference('simplify', [status(thm)], ['186'])).
% 1.06/1.28  thf('188', plain,
% 1.06/1.28      (((v2_struct_0 @ sk_A)
% 1.06/1.28        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.28           (k4_tmap_1 @ sk_A @ sk_B))
% 1.06/1.28        | (v2_struct_0 @ sk_B)
% 1.06/1.28        | (v2_struct_0 @ sk_B)
% 1.06/1.28        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.28           (k4_tmap_1 @ sk_A @ sk_B))
% 1.06/1.28        | (v2_struct_0 @ sk_A)
% 1.06/1.28        | (v2_struct_0 @ sk_A)
% 1.06/1.28        | ~ (v2_pre_topc @ sk_A)
% 1.06/1.28        | ~ (l1_pre_topc @ sk_A)
% 1.06/1.28        | ((k1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 1.06/1.28            (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))
% 1.06/1.28            = (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))
% 1.06/1.28        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 1.06/1.28      inference('sup-', [status(thm)], ['183', '187'])).
% 1.06/1.28  thf('189', plain, ((v2_pre_topc @ sk_A)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('190', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('191', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('192', plain,
% 1.06/1.28      (((v2_struct_0 @ sk_A)
% 1.06/1.28        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.28           (k4_tmap_1 @ sk_A @ sk_B))
% 1.06/1.28        | (v2_struct_0 @ sk_B)
% 1.06/1.28        | (v2_struct_0 @ sk_B)
% 1.06/1.28        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.28           (k4_tmap_1 @ sk_A @ sk_B))
% 1.06/1.28        | (v2_struct_0 @ sk_A)
% 1.06/1.28        | (v2_struct_0 @ sk_A)
% 1.06/1.28        | ((k1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 1.06/1.28            (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))
% 1.06/1.28            = (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A)))),
% 1.06/1.28      inference('demod', [status(thm)], ['188', '189', '190', '191'])).
% 1.06/1.28  thf('193', plain,
% 1.06/1.28      ((((k1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 1.06/1.28          (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))
% 1.06/1.28          = (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))
% 1.06/1.28        | (v2_struct_0 @ sk_B)
% 1.06/1.28        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.28           (k4_tmap_1 @ sk_A @ sk_B))
% 1.06/1.28        | (v2_struct_0 @ sk_A))),
% 1.06/1.28      inference('simplify', [status(thm)], ['192'])).
% 1.06/1.28  thf('194', plain,
% 1.06/1.28      ((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 1.06/1.28        (k1_zfmisc_1 @ 
% 1.06/1.28         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.06/1.28      inference('clc', [status(thm)], ['6', '7'])).
% 1.06/1.28  thf('195', plain,
% 1.06/1.28      ((m1_subset_1 @ sk_C @ 
% 1.06/1.28        (k1_zfmisc_1 @ 
% 1.06/1.28         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('196', plain,
% 1.06/1.28      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 1.06/1.28         ((v2_struct_0 @ X38)
% 1.06/1.28          | ~ (v2_pre_topc @ X38)
% 1.06/1.28          | ~ (l1_pre_topc @ X38)
% 1.06/1.28          | ~ (v1_funct_1 @ X39)
% 1.06/1.28          | ~ (v1_funct_2 @ X39 @ (u1_struct_0 @ X38) @ (u1_struct_0 @ X40))
% 1.06/1.28          | ~ (m1_subset_1 @ X39 @ 
% 1.06/1.28               (k1_zfmisc_1 @ 
% 1.06/1.28                (k2_zfmisc_1 @ (u1_struct_0 @ X38) @ (u1_struct_0 @ X40))))
% 1.06/1.28          | (m1_subset_1 @ (sk_F @ X41 @ X39 @ X42 @ X38 @ X40) @ 
% 1.06/1.28             (u1_struct_0 @ X38))
% 1.06/1.28          | (r2_funct_2 @ (u1_struct_0 @ X42) @ (u1_struct_0 @ X40) @ 
% 1.06/1.28             (k2_tmap_1 @ X38 @ X40 @ X39 @ X42) @ X41)
% 1.06/1.28          | ~ (m1_subset_1 @ X41 @ 
% 1.06/1.28               (k1_zfmisc_1 @ 
% 1.06/1.28                (k2_zfmisc_1 @ (u1_struct_0 @ X42) @ (u1_struct_0 @ X40))))
% 1.06/1.28          | ~ (v1_funct_2 @ X41 @ (u1_struct_0 @ X42) @ (u1_struct_0 @ X40))
% 1.06/1.28          | ~ (v1_funct_1 @ X41)
% 1.06/1.28          | ~ (m1_pre_topc @ X42 @ X38)
% 1.06/1.28          | (v2_struct_0 @ X42)
% 1.06/1.28          | ~ (l1_pre_topc @ X40)
% 1.06/1.28          | ~ (v2_pre_topc @ X40)
% 1.06/1.28          | (v2_struct_0 @ X40))),
% 1.06/1.28      inference('cnf', [status(esa)], [t59_tmap_1])).
% 1.06/1.28  thf('197', plain,
% 1.06/1.28      (![X0 : $i, X1 : $i]:
% 1.06/1.28         ((v2_struct_0 @ sk_A)
% 1.06/1.28          | ~ (v2_pre_topc @ sk_A)
% 1.06/1.28          | ~ (l1_pre_topc @ sk_A)
% 1.06/1.28          | (v2_struct_0 @ X0)
% 1.06/1.28          | ~ (m1_pre_topc @ X0 @ sk_B)
% 1.06/1.28          | ~ (v1_funct_1 @ X1)
% 1.06/1.28          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 1.06/1.28          | ~ (m1_subset_1 @ X1 @ 
% 1.06/1.28               (k1_zfmisc_1 @ 
% 1.06/1.28                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 1.06/1.28          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.28             (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ X1)
% 1.06/1.28          | (m1_subset_1 @ (sk_F @ X1 @ sk_C @ X0 @ sk_B @ sk_A) @ 
% 1.06/1.28             (u1_struct_0 @ sk_B))
% 1.06/1.28          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.06/1.28          | ~ (v1_funct_1 @ sk_C)
% 1.06/1.28          | ~ (l1_pre_topc @ sk_B)
% 1.06/1.28          | ~ (v2_pre_topc @ sk_B)
% 1.06/1.28          | (v2_struct_0 @ sk_B))),
% 1.06/1.28      inference('sup-', [status(thm)], ['195', '196'])).
% 1.06/1.28  thf('198', plain, ((v2_pre_topc @ sk_A)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('199', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('200', plain,
% 1.06/1.28      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('201', plain, ((v1_funct_1 @ sk_C)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('202', plain, ((l1_pre_topc @ sk_B)),
% 1.06/1.28      inference('demod', [status(thm)], ['18', '19'])).
% 1.06/1.28  thf('203', plain, ((v2_pre_topc @ sk_B)),
% 1.06/1.28      inference('demod', [status(thm)], ['23', '24', '25'])).
% 1.06/1.28  thf('204', plain,
% 1.06/1.28      (![X0 : $i, X1 : $i]:
% 1.06/1.28         ((v2_struct_0 @ sk_A)
% 1.06/1.28          | (v2_struct_0 @ X0)
% 1.06/1.28          | ~ (m1_pre_topc @ X0 @ sk_B)
% 1.06/1.28          | ~ (v1_funct_1 @ X1)
% 1.06/1.28          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 1.06/1.28          | ~ (m1_subset_1 @ X1 @ 
% 1.06/1.28               (k1_zfmisc_1 @ 
% 1.06/1.28                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 1.06/1.28          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.28             (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ X1)
% 1.06/1.28          | (m1_subset_1 @ (sk_F @ X1 @ sk_C @ X0 @ sk_B @ sk_A) @ 
% 1.06/1.28             (u1_struct_0 @ sk_B))
% 1.06/1.28          | (v2_struct_0 @ sk_B))),
% 1.06/1.28      inference('demod', [status(thm)],
% 1.06/1.28                ['197', '198', '199', '200', '201', '202', '203'])).
% 1.06/1.28  thf('205', plain,
% 1.06/1.28      (((v2_struct_0 @ sk_B)
% 1.06/1.28        | (m1_subset_1 @ 
% 1.06/1.28           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 1.06/1.28           (u1_struct_0 @ sk_B))
% 1.06/1.28        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.28           (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) @ (k4_tmap_1 @ sk_A @ sk_B))
% 1.06/1.28        | ~ (v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.28             (u1_struct_0 @ sk_A))
% 1.06/1.28        | ~ (v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))
% 1.06/1.28        | ~ (m1_pre_topc @ sk_B @ sk_B)
% 1.06/1.28        | (v2_struct_0 @ sk_B)
% 1.06/1.28        | (v2_struct_0 @ sk_A))),
% 1.06/1.28      inference('sup-', [status(thm)], ['194', '204'])).
% 1.06/1.28  thf('206', plain, (((sk_C) = (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B))),
% 1.06/1.28      inference('demod', [status(thm)], ['148', '149'])).
% 1.06/1.28  thf('207', plain,
% 1.06/1.28      ((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.28        (u1_struct_0 @ sk_A))),
% 1.06/1.28      inference('clc', [status(thm)], ['156', '157'])).
% 1.06/1.28  thf('208', plain, ((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))),
% 1.06/1.28      inference('clc', [status(thm)], ['164', '165'])).
% 1.06/1.28  thf('209', plain, ((m1_pre_topc @ sk_B @ sk_B)),
% 1.06/1.28      inference('demod', [status(thm)], ['111', '112', '113', '114'])).
% 1.06/1.28  thf('210', plain,
% 1.06/1.28      (((v2_struct_0 @ sk_B)
% 1.06/1.28        | (m1_subset_1 @ 
% 1.06/1.28           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 1.06/1.28           (u1_struct_0 @ sk_B))
% 1.06/1.28        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.28           (k4_tmap_1 @ sk_A @ sk_B))
% 1.06/1.28        | (v2_struct_0 @ sk_B)
% 1.06/1.28        | (v2_struct_0 @ sk_A))),
% 1.06/1.28      inference('demod', [status(thm)], ['205', '206', '207', '208', '209'])).
% 1.06/1.28  thf('211', plain,
% 1.06/1.28      (((v2_struct_0 @ sk_A)
% 1.06/1.28        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.28           (k4_tmap_1 @ sk_A @ sk_B))
% 1.06/1.28        | (m1_subset_1 @ 
% 1.06/1.28           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 1.06/1.28           (u1_struct_0 @ sk_B))
% 1.06/1.28        | (v2_struct_0 @ sk_B))),
% 1.06/1.28      inference('simplify', [status(thm)], ['210'])).
% 1.06/1.28  thf('212', plain,
% 1.06/1.28      ((m1_subset_1 @ sk_C @ 
% 1.06/1.28        (k1_zfmisc_1 @ 
% 1.06/1.28         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf(redefinition_k3_funct_2, axiom,
% 1.06/1.28    (![A:$i,B:$i,C:$i,D:$i]:
% 1.06/1.28     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 1.06/1.28         ( v1_funct_2 @ C @ A @ B ) & 
% 1.06/1.28         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.06/1.28         ( m1_subset_1 @ D @ A ) ) =>
% 1.06/1.28       ( ( k3_funct_2 @ A @ B @ C @ D ) = ( k1_funct_1 @ C @ D ) ) ))).
% 1.06/1.28  thf('213', plain,
% 1.06/1.28      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.06/1.28         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5)))
% 1.06/1.28          | ~ (v1_funct_2 @ X3 @ X4 @ X5)
% 1.06/1.28          | ~ (v1_funct_1 @ X3)
% 1.06/1.28          | (v1_xboole_0 @ X4)
% 1.06/1.28          | ~ (m1_subset_1 @ X6 @ X4)
% 1.06/1.28          | ((k3_funct_2 @ X4 @ X5 @ X3 @ X6) = (k1_funct_1 @ X3 @ X6)))),
% 1.06/1.28      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 1.06/1.28  thf('214', plain,
% 1.06/1.28      (![X0 : $i]:
% 1.06/1.28         (((k3_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.28            X0) = (k1_funct_1 @ sk_C @ X0))
% 1.06/1.28          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 1.06/1.28          | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.06/1.28          | ~ (v1_funct_1 @ sk_C)
% 1.06/1.28          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 1.06/1.28      inference('sup-', [status(thm)], ['212', '213'])).
% 1.06/1.28  thf('215', plain, ((v1_funct_1 @ sk_C)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('216', plain,
% 1.06/1.28      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('217', plain,
% 1.06/1.28      (![X0 : $i]:
% 1.06/1.28         (((k3_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.28            X0) = (k1_funct_1 @ sk_C @ X0))
% 1.06/1.28          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 1.06/1.28          | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 1.06/1.28      inference('demod', [status(thm)], ['214', '215', '216'])).
% 1.06/1.28  thf('218', plain,
% 1.06/1.28      (((v2_struct_0 @ sk_B)
% 1.06/1.28        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.28           (k4_tmap_1 @ sk_A @ sk_B))
% 1.06/1.28        | (v2_struct_0 @ sk_A)
% 1.06/1.28        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.06/1.28        | ((k3_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.28            (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))
% 1.06/1.28            = (k1_funct_1 @ sk_C @ 
% 1.06/1.28               (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))))),
% 1.06/1.28      inference('sup-', [status(thm)], ['211', '217'])).
% 1.06/1.28  thf('219', plain,
% 1.06/1.28      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 1.06/1.28         ((v2_struct_0 @ X38)
% 1.06/1.28          | ~ (v2_pre_topc @ X38)
% 1.06/1.28          | ~ (l1_pre_topc @ X38)
% 1.06/1.28          | ~ (v1_funct_1 @ X39)
% 1.06/1.28          | ~ (v1_funct_2 @ X39 @ (u1_struct_0 @ X38) @ (u1_struct_0 @ X40))
% 1.06/1.28          | ~ (m1_subset_1 @ X39 @ 
% 1.06/1.28               (k1_zfmisc_1 @ 
% 1.06/1.28                (k2_zfmisc_1 @ (u1_struct_0 @ X38) @ (u1_struct_0 @ X40))))
% 1.06/1.28          | ((k3_funct_2 @ (u1_struct_0 @ X38) @ (u1_struct_0 @ X40) @ X39 @ 
% 1.06/1.28              (sk_F @ X41 @ X39 @ X42 @ X38 @ X40))
% 1.06/1.28              != (k1_funct_1 @ X41 @ (sk_F @ X41 @ X39 @ X42 @ X38 @ X40)))
% 1.06/1.28          | (r2_funct_2 @ (u1_struct_0 @ X42) @ (u1_struct_0 @ X40) @ 
% 1.06/1.28             (k2_tmap_1 @ X38 @ X40 @ X39 @ X42) @ X41)
% 1.06/1.28          | ~ (m1_subset_1 @ X41 @ 
% 1.06/1.28               (k1_zfmisc_1 @ 
% 1.06/1.28                (k2_zfmisc_1 @ (u1_struct_0 @ X42) @ (u1_struct_0 @ X40))))
% 1.06/1.28          | ~ (v1_funct_2 @ X41 @ (u1_struct_0 @ X42) @ (u1_struct_0 @ X40))
% 1.06/1.28          | ~ (v1_funct_1 @ X41)
% 1.06/1.28          | ~ (m1_pre_topc @ X42 @ X38)
% 1.06/1.28          | (v2_struct_0 @ X42)
% 1.06/1.28          | ~ (l1_pre_topc @ X40)
% 1.06/1.28          | ~ (v2_pre_topc @ X40)
% 1.06/1.28          | (v2_struct_0 @ X40))),
% 1.06/1.28      inference('cnf', [status(esa)], [t59_tmap_1])).
% 1.06/1.28  thf('220', plain,
% 1.06/1.28      ((((k1_funct_1 @ sk_C @ 
% 1.06/1.28          (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))
% 1.06/1.28          != (k1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 1.06/1.28              (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A)))
% 1.06/1.28        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.06/1.28        | (v2_struct_0 @ sk_A)
% 1.06/1.28        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.28           (k4_tmap_1 @ sk_A @ sk_B))
% 1.06/1.28        | (v2_struct_0 @ sk_B)
% 1.06/1.28        | (v2_struct_0 @ sk_A)
% 1.06/1.28        | ~ (v2_pre_topc @ sk_A)
% 1.06/1.28        | ~ (l1_pre_topc @ sk_A)
% 1.06/1.28        | (v2_struct_0 @ sk_B)
% 1.06/1.28        | ~ (m1_pre_topc @ sk_B @ sk_B)
% 1.06/1.28        | ~ (v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))
% 1.06/1.28        | ~ (v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.28             (u1_struct_0 @ sk_A))
% 1.06/1.28        | ~ (m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 1.06/1.28             (k1_zfmisc_1 @ 
% 1.06/1.28              (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 1.06/1.28        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.28           (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) @ (k4_tmap_1 @ sk_A @ sk_B))
% 1.06/1.28        | ~ (m1_subset_1 @ sk_C @ 
% 1.06/1.28             (k1_zfmisc_1 @ 
% 1.06/1.28              (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 1.06/1.28        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.06/1.28        | ~ (v1_funct_1 @ sk_C)
% 1.06/1.28        | ~ (l1_pre_topc @ sk_B)
% 1.06/1.28        | ~ (v2_pre_topc @ sk_B)
% 1.06/1.28        | (v2_struct_0 @ sk_B))),
% 1.06/1.28      inference('sup-', [status(thm)], ['218', '219'])).
% 1.06/1.28  thf('221', plain, ((v2_pre_topc @ sk_A)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('222', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('223', plain, ((m1_pre_topc @ sk_B @ sk_B)),
% 1.06/1.28      inference('demod', [status(thm)], ['111', '112', '113', '114'])).
% 1.06/1.28  thf('224', plain, ((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))),
% 1.06/1.28      inference('clc', [status(thm)], ['164', '165'])).
% 1.06/1.28  thf('225', plain,
% 1.06/1.28      ((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.28        (u1_struct_0 @ sk_A))),
% 1.06/1.28      inference('clc', [status(thm)], ['156', '157'])).
% 1.06/1.28  thf('226', plain,
% 1.06/1.28      ((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 1.06/1.28        (k1_zfmisc_1 @ 
% 1.06/1.28         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.06/1.28      inference('clc', [status(thm)], ['6', '7'])).
% 1.06/1.28  thf('227', plain, (((sk_C) = (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B))),
% 1.06/1.28      inference('demod', [status(thm)], ['148', '149'])).
% 1.06/1.28  thf('228', plain,
% 1.06/1.28      ((m1_subset_1 @ sk_C @ 
% 1.06/1.28        (k1_zfmisc_1 @ 
% 1.06/1.28         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('229', plain,
% 1.06/1.28      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('230', plain, ((v1_funct_1 @ sk_C)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('231', plain, ((l1_pre_topc @ sk_B)),
% 1.06/1.28      inference('demod', [status(thm)], ['18', '19'])).
% 1.06/1.28  thf('232', plain, ((v2_pre_topc @ sk_B)),
% 1.06/1.28      inference('demod', [status(thm)], ['23', '24', '25'])).
% 1.06/1.28  thf('233', plain,
% 1.06/1.28      ((((k1_funct_1 @ sk_C @ 
% 1.06/1.28          (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))
% 1.06/1.28          != (k1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 1.06/1.28              (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A)))
% 1.06/1.28        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.06/1.28        | (v2_struct_0 @ sk_A)
% 1.06/1.28        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.28           (k4_tmap_1 @ sk_A @ sk_B))
% 1.06/1.28        | (v2_struct_0 @ sk_B)
% 1.06/1.28        | (v2_struct_0 @ sk_A)
% 1.06/1.28        | (v2_struct_0 @ sk_B)
% 1.06/1.28        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.28           (k4_tmap_1 @ sk_A @ sk_B))
% 1.06/1.28        | (v2_struct_0 @ sk_B))),
% 1.06/1.28      inference('demod', [status(thm)],
% 1.06/1.28                ['220', '221', '222', '223', '224', '225', '226', '227', 
% 1.06/1.28                 '228', '229', '230', '231', '232'])).
% 1.06/1.28  thf('234', plain,
% 1.06/1.28      (((v2_struct_0 @ sk_B)
% 1.06/1.28        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.28           (k4_tmap_1 @ sk_A @ sk_B))
% 1.06/1.28        | (v2_struct_0 @ sk_A)
% 1.06/1.28        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.06/1.28        | ((k1_funct_1 @ sk_C @ 
% 1.06/1.28            (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))
% 1.06/1.28            != (k1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 1.06/1.28                (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))))),
% 1.06/1.28      inference('simplify', [status(thm)], ['233'])).
% 1.06/1.28  thf('235', plain,
% 1.06/1.28      ((((k1_funct_1 @ sk_C @ 
% 1.06/1.28          (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))
% 1.06/1.28          != (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))
% 1.06/1.28        | (v2_struct_0 @ sk_A)
% 1.06/1.28        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.28           (k4_tmap_1 @ sk_A @ sk_B))
% 1.06/1.28        | (v2_struct_0 @ sk_B)
% 1.06/1.28        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.06/1.28        | (v2_struct_0 @ sk_A)
% 1.06/1.28        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.28           (k4_tmap_1 @ sk_A @ sk_B))
% 1.06/1.28        | (v2_struct_0 @ sk_B))),
% 1.06/1.28      inference('sup-', [status(thm)], ['193', '234'])).
% 1.06/1.28  thf('236', plain,
% 1.06/1.28      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.06/1.28        | (v2_struct_0 @ sk_B)
% 1.06/1.28        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.28           (k4_tmap_1 @ sk_A @ sk_B))
% 1.06/1.28        | (v2_struct_0 @ sk_A)
% 1.06/1.28        | ((k1_funct_1 @ sk_C @ 
% 1.06/1.28            (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))
% 1.06/1.28            != (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A)))),
% 1.06/1.28      inference('simplify', [status(thm)], ['235'])).
% 1.06/1.28  thf('237', plain,
% 1.06/1.28      ((((sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A)
% 1.06/1.28          != (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))
% 1.06/1.28        | (v2_struct_0 @ sk_A)
% 1.06/1.28        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.28           (k4_tmap_1 @ sk_A @ sk_B))
% 1.06/1.28        | (v2_struct_0 @ sk_B)
% 1.06/1.28        | (v2_struct_0 @ sk_A)
% 1.06/1.28        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.28           (k4_tmap_1 @ sk_A @ sk_B))
% 1.06/1.28        | (v2_struct_0 @ sk_B)
% 1.06/1.28        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 1.06/1.28      inference('sup-', [status(thm)], ['182', '236'])).
% 1.06/1.28  thf('238', plain,
% 1.06/1.28      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.06/1.28        | (v2_struct_0 @ sk_B)
% 1.06/1.28        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.28           (k4_tmap_1 @ sk_A @ sk_B))
% 1.06/1.28        | (v2_struct_0 @ sk_A))),
% 1.06/1.28      inference('simplify', [status(thm)], ['237'])).
% 1.06/1.28  thf('239', plain,
% 1.06/1.28      ((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 1.06/1.28        (k1_zfmisc_1 @ 
% 1.06/1.28         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.06/1.28      inference('clc', [status(thm)], ['6', '7'])).
% 1.06/1.28  thf('240', plain,
% 1.06/1.28      (![X0 : $i]:
% 1.06/1.28         (~ (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.28             X0)
% 1.06/1.28          | ((sk_C) = (X0))
% 1.06/1.28          | ~ (m1_subset_1 @ X0 @ 
% 1.06/1.28               (k1_zfmisc_1 @ 
% 1.06/1.28                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 1.06/1.28          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.06/1.28          | ~ (v1_funct_1 @ X0))),
% 1.06/1.28      inference('demod', [status(thm)], ['59', '60', '61'])).
% 1.06/1.28  thf('241', plain,
% 1.06/1.28      ((~ (v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))
% 1.06/1.28        | ~ (v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.28             (u1_struct_0 @ sk_A))
% 1.06/1.28        | ((sk_C) = (k4_tmap_1 @ sk_A @ sk_B))
% 1.06/1.28        | ~ (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.28             (k4_tmap_1 @ sk_A @ sk_B)))),
% 1.06/1.28      inference('sup-', [status(thm)], ['239', '240'])).
% 1.06/1.28  thf('242', plain, ((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))),
% 1.06/1.28      inference('clc', [status(thm)], ['164', '165'])).
% 1.06/1.28  thf('243', plain,
% 1.06/1.28      ((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.28        (u1_struct_0 @ sk_A))),
% 1.06/1.28      inference('clc', [status(thm)], ['156', '157'])).
% 1.06/1.28  thf('244', plain,
% 1.06/1.28      ((((sk_C) = (k4_tmap_1 @ sk_A @ sk_B))
% 1.06/1.28        | ~ (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.28             (k4_tmap_1 @ sk_A @ sk_B)))),
% 1.06/1.28      inference('demod', [status(thm)], ['241', '242', '243'])).
% 1.06/1.28  thf('245', plain,
% 1.06/1.28      (((v2_struct_0 @ sk_A)
% 1.06/1.28        | (v2_struct_0 @ sk_B)
% 1.06/1.28        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.06/1.28        | ((sk_C) = (k4_tmap_1 @ sk_A @ sk_B)))),
% 1.06/1.28      inference('sup-', [status(thm)], ['238', '244'])).
% 1.06/1.28  thf('246', plain,
% 1.06/1.28      (~ (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.28          (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('247', plain,
% 1.06/1.28      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.28           sk_C)
% 1.06/1.28        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.06/1.28        | (v2_struct_0 @ sk_B)
% 1.06/1.28        | (v2_struct_0 @ sk_A))),
% 1.06/1.28      inference('sup-', [status(thm)], ['245', '246'])).
% 1.06/1.28  thf('248', plain,
% 1.06/1.28      ((m1_subset_1 @ sk_C @ 
% 1.06/1.28        (k1_zfmisc_1 @ 
% 1.06/1.28         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('249', plain,
% 1.06/1.28      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 1.06/1.28         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9)))
% 1.06/1.28          | ~ (v1_funct_2 @ X7 @ X8 @ X9)
% 1.06/1.28          | ~ (v1_funct_1 @ X7)
% 1.06/1.28          | ~ (v1_funct_1 @ X10)
% 1.06/1.28          | ~ (v1_funct_2 @ X10 @ X8 @ X9)
% 1.06/1.28          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9)))
% 1.06/1.28          | (r2_funct_2 @ X8 @ X9 @ X7 @ X10)
% 1.06/1.28          | ((X7) != (X10)))),
% 1.06/1.28      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 1.06/1.28  thf('250', plain,
% 1.06/1.28      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.06/1.28         ((r2_funct_2 @ X8 @ X9 @ X10 @ X10)
% 1.06/1.28          | ~ (v1_funct_1 @ X10)
% 1.06/1.28          | ~ (v1_funct_2 @ X10 @ X8 @ X9)
% 1.06/1.28          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 1.06/1.28      inference('simplify', [status(thm)], ['249'])).
% 1.06/1.28  thf('251', plain,
% 1.06/1.28      ((~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.06/1.28        | ~ (v1_funct_1 @ sk_C)
% 1.06/1.28        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.28           sk_C))),
% 1.06/1.28      inference('sup-', [status(thm)], ['248', '250'])).
% 1.06/1.28  thf('252', plain,
% 1.06/1.28      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('253', plain, ((v1_funct_1 @ sk_C)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('254', plain,
% 1.06/1.28      ((r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ sk_C)),
% 1.06/1.28      inference('demod', [status(thm)], ['251', '252', '253'])).
% 1.06/1.28  thf('255', plain,
% 1.06/1.28      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.06/1.28        | (v2_struct_0 @ sk_B)
% 1.06/1.28        | (v2_struct_0 @ sk_A))),
% 1.06/1.28      inference('demod', [status(thm)], ['247', '254'])).
% 1.06/1.28  thf('256', plain, (~ (v2_struct_0 @ sk_B)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('257', plain,
% 1.06/1.28      (((v2_struct_0 @ sk_A) | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 1.06/1.28      inference('clc', [status(thm)], ['255', '256'])).
% 1.06/1.28  thf('258', plain, (~ (v2_struct_0 @ sk_A)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('259', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_B))),
% 1.06/1.28      inference('clc', [status(thm)], ['257', '258'])).
% 1.06/1.28  thf(fc2_struct_0, axiom,
% 1.06/1.28    (![A:$i]:
% 1.06/1.28     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 1.06/1.28       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.06/1.28  thf('260', plain,
% 1.06/1.28      (![X16 : $i]:
% 1.06/1.28         (~ (v1_xboole_0 @ (u1_struct_0 @ X16))
% 1.06/1.28          | ~ (l1_struct_0 @ X16)
% 1.06/1.28          | (v2_struct_0 @ X16))),
% 1.06/1.28      inference('cnf', [status(esa)], [fc2_struct_0])).
% 1.06/1.28  thf('261', plain, (((v2_struct_0 @ sk_B) | ~ (l1_struct_0 @ sk_B))),
% 1.06/1.28      inference('sup-', [status(thm)], ['259', '260'])).
% 1.06/1.28  thf('262', plain, ((l1_struct_0 @ sk_B)),
% 1.06/1.28      inference('sup-', [status(thm)], ['32', '33'])).
% 1.06/1.28  thf('263', plain, ((v2_struct_0 @ sk_B)),
% 1.06/1.28      inference('demod', [status(thm)], ['261', '262'])).
% 1.06/1.28  thf('264', plain, ($false), inference('demod', [status(thm)], ['0', '263'])).
% 1.06/1.28  
% 1.06/1.28  % SZS output end Refutation
% 1.06/1.28  
% 1.06/1.29  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
