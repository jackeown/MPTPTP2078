%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wNm5A7U8zL

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:01 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 366 expanded)
%              Number of leaves         :   33 ( 122 expanded)
%              Depth                    :   28
%              Number of atoms          : 1917 (16055 expanded)
%              Number of equality atoms :   45 ( 217 expanded)
%              Maximal formula depth    :   25 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i > $i > $i )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_F_1_type,type,(
    sk_F_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(t73_tmap_1,conjecture,(
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
                            ( ( ( v1_funct_1 @ F )
                              & ( v1_funct_2 @ F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
                              & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) )
                           => ( ! [G: $i] :
                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) )
                                 => ( ( r2_hidden @ G @ ( u1_struct_0 @ C ) )
                                   => ( ( k3_funct_2 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) @ E @ G )
                                      = ( k1_funct_1 @ F @ G ) ) ) )
                             => ( r2_funct_2 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ F ) ) ) ) ) ) ) ) ) )).

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
                              ( ( ( v1_funct_1 @ F )
                                & ( v1_funct_2 @ F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
                                & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) )
                             => ( ! [G: $i] :
                                    ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) )
                                   => ( ( r2_hidden @ G @ ( u1_struct_0 @ C ) )
                                     => ( ( k3_funct_2 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) @ E @ G )
                                        = ( k1_funct_1 @ F @ G ) ) ) )
                               => ( r2_funct_2 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ F ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t73_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_F_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t173_funct_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ A @ B )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
             => ! [D: $i] :
                  ( ( ~ ( v1_xboole_0 @ D )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) )
                 => ! [E: $i] :
                      ( ( ( v1_funct_1 @ E )
                        & ( v1_funct_2 @ E @ D @ B )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) )
                     => ( ! [F: $i] :
                            ( ( m1_subset_1 @ F @ A )
                           => ( ( r2_hidden @ F @ D )
                             => ( ( k3_funct_2 @ A @ B @ C @ F )
                                = ( k1_funct_1 @ E @ F ) ) ) )
                       => ( ( k2_partfun1 @ A @ B @ C @ D )
                          = E ) ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( v1_xboole_0 @ X4 )
      | ( v1_xboole_0 @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( m1_subset_1 @ ( sk_F @ X7 @ X5 @ X8 @ X4 @ X6 ) @ X6 )
      | ( ( k2_partfun1 @ X6 @ X4 @ X8 @ X5 )
        = X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X4 ) ) )
      | ~ ( v1_funct_2 @ X7 @ X5 @ X4 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X4 ) ) )
      | ~ ( v1_funct_2 @ X8 @ X6 @ X4 )
      | ~ ( v1_funct_1 @ X8 )
      | ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t173_funct_2])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_1 @ sk_F_1 )
      | ~ ( v1_funct_2 @ sk_F_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k2_partfun1 @ X0 @ ( u1_struct_0 @ sk_B ) @ X1 @ ( u1_struct_0 @ sk_C ) )
        = sk_F_1 )
      | ( m1_subset_1 @ ( sk_F @ sk_F_1 @ ( u1_struct_0 @ sk_C ) @ X1 @ ( u1_struct_0 @ sk_B ) @ X0 ) @ X0 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_1 @ sk_F_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_funct_2 @ sk_F_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( ( k2_partfun1 @ X0 @ ( u1_struct_0 @ sk_B ) @ X1 @ ( u1_struct_0 @ sk_C ) )
        = sk_F_1 )
      | ( m1_subset_1 @ ( sk_F @ sk_F_1 @ ( u1_struct_0 @ sk_C ) @ X1 @ ( u1_struct_0 @ sk_B ) @ X0 ) @ X0 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
    | ( m1_subset_1 @ ( sk_F @ sk_F_1 @ ( u1_struct_0 @ sk_C ) @ sk_E @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) @ ( u1_struct_0 @ sk_D ) )
    | ( ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) )
      = sk_F_1 )
    | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_E )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf('9',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('10',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X18 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('11',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('13',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X10 @ X11 )
      | ( l1_pre_topc @ X10 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('14',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['11','16'])).

thf('18',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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

thf('21',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( v2_struct_0 @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( m1_pre_topc @ X14 @ X15 )
      | ~ ( m1_pre_topc @ X14 @ X16 )
      | ( ( k3_tmap_1 @ X15 @ X13 @ X16 @ X14 @ X17 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X13 ) @ X17 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X13 ) ) ) )
      | ~ ( v1_funct_2 @ X17 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X13 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( m1_pre_topc @ X16 @ X15 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d5_tmap_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['22','23','24','25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['18','31'])).

thf('33',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( m1_subset_1 @ ( sk_F @ sk_F_1 @ ( u1_struct_0 @ sk_C ) @ sk_E @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) @ ( u1_struct_0 @ sk_D ) )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
      = sk_F_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['8','17','38','39','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    m1_subset_1 @ sk_F_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( v1_xboole_0 @ X4 )
      | ( v1_xboole_0 @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( r2_hidden @ ( sk_F @ X7 @ X5 @ X8 @ X4 @ X6 ) @ X5 )
      | ( ( k2_partfun1 @ X6 @ X4 @ X8 @ X5 )
        = X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X4 ) ) )
      | ~ ( v1_funct_2 @ X7 @ X5 @ X4 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X4 ) ) )
      | ~ ( v1_funct_2 @ X8 @ X6 @ X4 )
      | ~ ( v1_funct_1 @ X8 )
      | ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t173_funct_2])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_1 @ sk_F_1 )
      | ~ ( v1_funct_2 @ sk_F_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k2_partfun1 @ X0 @ ( u1_struct_0 @ sk_B ) @ X1 @ ( u1_struct_0 @ sk_C ) )
        = sk_F_1 )
      | ( r2_hidden @ ( sk_F @ sk_F_1 @ ( u1_struct_0 @ sk_C ) @ X1 @ ( u1_struct_0 @ sk_B ) @ X0 ) @ ( u1_struct_0 @ sk_C ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_funct_1 @ sk_F_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_funct_2 @ sk_F_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( ( k2_partfun1 @ X0 @ ( u1_struct_0 @ sk_B ) @ X1 @ ( u1_struct_0 @ sk_C ) )
        = sk_F_1 )
      | ( r2_hidden @ ( sk_F @ sk_F_1 @ ( u1_struct_0 @ sk_C ) @ X1 @ ( u1_struct_0 @ sk_B ) @ X0 ) @ ( u1_struct_0 @ sk_C ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
    | ( r2_hidden @ ( sk_F @ sk_F_1 @ ( u1_struct_0 @ sk_C ) @ sk_E @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) @ ( u1_struct_0 @ sk_C ) )
    | ( ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) )
      = sk_F_1 )
    | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_E )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['42','48'])).

thf('50',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['11','16'])).

thf('51',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('52',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( r2_hidden @ ( sk_F @ sk_F_1 @ ( u1_struct_0 @ sk_C ) @ sk_E @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) @ ( u1_struct_0 @ sk_C ) )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
      = sk_F_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['49','50','51','52','53'])).

thf('55',plain,(
    ! [X20: $i] :
      ( ~ ( r2_hidden @ X20 @ ( u1_struct_0 @ sk_C ) )
      | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ X20 )
        = ( k1_funct_1 @ sk_F_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
      = sk_F_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( m1_subset_1 @ ( sk_F @ sk_F_1 @ ( u1_struct_0 @ sk_C ) @ sk_E @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) @ ( u1_struct_0 @ sk_D ) )
    | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( sk_F @ sk_F_1 @ ( u1_struct_0 @ sk_C ) @ sk_E @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) )
      = ( k1_funct_1 @ sk_F_1 @ ( sk_F @ sk_F_1 @ ( u1_struct_0 @ sk_C ) @ sk_E @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
      = sk_F_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( sk_F @ sk_F_1 @ ( u1_struct_0 @ sk_C ) @ sk_E @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) )
      = ( k1_funct_1 @ sk_F_1 @ ( sk_F @ sk_F_1 @ ( u1_struct_0 @ sk_C ) @ sk_E @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
      = sk_F_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['41','56'])).

thf('58',plain,
    ( ( ( k3_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( sk_F @ sk_F_1 @ ( u1_struct_0 @ sk_C ) @ sk_E @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) )
      = ( k1_funct_1 @ sk_F_1 @ ( sk_F @ sk_F_1 @ ( u1_struct_0 @ sk_C ) @ sk_E @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
      = sk_F_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( v1_xboole_0 @ X4 )
      | ( v1_xboole_0 @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( ( k3_funct_2 @ X6 @ X4 @ X8 @ ( sk_F @ X7 @ X5 @ X8 @ X4 @ X6 ) )
       != ( k1_funct_1 @ X7 @ ( sk_F @ X7 @ X5 @ X8 @ X4 @ X6 ) ) )
      | ( ( k2_partfun1 @ X6 @ X4 @ X8 @ X5 )
        = X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X4 ) ) )
      | ~ ( v1_funct_2 @ X7 @ X5 @ X4 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X4 ) ) )
      | ~ ( v1_funct_2 @ X8 @ X6 @ X4 )
      | ~ ( v1_funct_1 @ X8 )
      | ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t173_funct_2])).

thf('60',plain,
    ( ( ( k1_funct_1 @ sk_F_1 @ ( sk_F @ sk_F_1 @ ( u1_struct_0 @ sk_C ) @ sk_E @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) )
     != ( k1_funct_1 @ sk_F_1 @ ( sk_F @ sk_F_1 @ ( u1_struct_0 @ sk_C ) @ sk_E @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
      = sk_F_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v1_funct_1 @ sk_F_1 )
    | ~ ( v1_funct_2 @ sk_F_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( m1_subset_1 @ sk_F_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) )
      = sk_F_1 )
    | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v1_funct_1 @ sk_F_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_funct_2 @ sk_F_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    m1_subset_1 @ sk_F_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('68',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['11','16'])).

thf('69',plain,
    ( ( ( k1_funct_1 @ sk_F_1 @ ( sk_F @ sk_F_1 @ ( u1_struct_0 @ sk_C ) @ sk_E @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) )
     != ( k1_funct_1 @ sk_F_1 @ ( sk_F @ sk_F_1 @ ( u1_struct_0 @ sk_C ) @ sk_E @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
      = sk_F_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
      = sk_F_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['60','61','62','63','64','65','66','67','68'])).

thf('70',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
      = sk_F_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_F_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F_1 @ sk_F_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    m1_subset_1 @ sk_F_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) )
      | ~ ( v1_funct_2 @ X0 @ X1 @ X2 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_funct_2 @ X3 @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) )
      | ( r2_funct_2 @ X1 @ X2 @ X0 @ X3 )
      | ( X0 != X3 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('75',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( r2_funct_2 @ X1 @ X2 @ X3 @ X3 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_funct_2 @ X3 @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,
    ( ~ ( v1_funct_2 @ sk_F_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_F_1 )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F_1 @ sk_F_1 ) ),
    inference('sup-',[status(thm)],['73','75'])).

thf('77',plain,(
    v1_funct_2 @ sk_F_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v1_funct_1 @ sk_F_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F_1 @ sk_F_1 ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('80',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['72','79'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('81',plain,(
    ! [X12: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('82',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('84',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('85',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['82','85'])).

thf('87',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X12: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('90',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_D )
    | ~ ( l1_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['14','15'])).

thf('92',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('93',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['90','93'])).

thf('95',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X12: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('98',plain,
    ( ( v2_struct_0 @ sk_C )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X10 @ X11 )
      | ( l1_pre_topc @ X10 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('101',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('105',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    v2_struct_0 @ sk_C ),
    inference(demod,[status(thm)],['98','105'])).

thf('107',plain,(
    $false ),
    inference(demod,[status(thm)],['0','106'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wNm5A7U8zL
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:23:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.52  % Solved by: fo/fo7.sh
% 0.21/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.52  % done 70 iterations in 0.049s
% 0.21/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.52  % SZS output start Refutation
% 0.21/0.52  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.52  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 0.21/0.52  thf(sk_F_type, type, sk_F: $i > $i > $i > $i > $i > $i).
% 0.21/0.52  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.21/0.52  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.21/0.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.52  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.52  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.52  thf(sk_E_type, type, sk_E: $i).
% 0.21/0.52  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.21/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.52  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.21/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.52  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.52  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.52  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.52  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.52  thf(sk_F_1_type, type, sk_F_1: $i).
% 0.21/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.52  thf(t73_tmap_1, conjecture,
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
% 0.21/0.52                           ( ( ( v1_funct_1 @ F ) & 
% 0.21/0.52                               ( v1_funct_2 @
% 0.21/0.52                                 F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.52                               ( m1_subset_1 @
% 0.21/0.52                                 F @ 
% 0.21/0.52                                 ( k1_zfmisc_1 @
% 0.21/0.52                                   ( k2_zfmisc_1 @
% 0.21/0.52                                     ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.52                             ( ( ![G:$i]:
% 0.21/0.52                                 ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.21/0.52                                   ( ( r2_hidden @ G @ ( u1_struct_0 @ C ) ) =>
% 0.21/0.52                                     ( ( k3_funct_2 @
% 0.21/0.52                                         ( u1_struct_0 @ D ) @ 
% 0.21/0.52                                         ( u1_struct_0 @ B ) @ E @ G ) =
% 0.21/0.52                                       ( k1_funct_1 @ F @ G ) ) ) ) ) =>
% 0.21/0.52                               ( r2_funct_2 @
% 0.21/0.52                                 ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ 
% 0.21/0.52                                 ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.52    (~( ![A:$i]:
% 0.21/0.52        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.52            ( l1_pre_topc @ A ) ) =>
% 0.21/0.52          ( ![B:$i]:
% 0.21/0.52            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.52                ( l1_pre_topc @ B ) ) =>
% 0.21/0.52              ( ![C:$i]:
% 0.21/0.52                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.21/0.52                  ( ![D:$i]:
% 0.21/0.52                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.21/0.52                      ( ![E:$i]:
% 0.21/0.52                        ( ( ( v1_funct_1 @ E ) & 
% 0.21/0.52                            ( v1_funct_2 @
% 0.21/0.52                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.52                            ( m1_subset_1 @
% 0.21/0.52                              E @ 
% 0.21/0.52                              ( k1_zfmisc_1 @
% 0.21/0.52                                ( k2_zfmisc_1 @
% 0.21/0.52                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.52                          ( ( m1_pre_topc @ C @ D ) =>
% 0.21/0.52                            ( ![F:$i]:
% 0.21/0.52                              ( ( ( v1_funct_1 @ F ) & 
% 0.21/0.52                                  ( v1_funct_2 @
% 0.21/0.52                                    F @ ( u1_struct_0 @ C ) @ 
% 0.21/0.52                                    ( u1_struct_0 @ B ) ) & 
% 0.21/0.52                                  ( m1_subset_1 @
% 0.21/0.52                                    F @ 
% 0.21/0.52                                    ( k1_zfmisc_1 @
% 0.21/0.52                                      ( k2_zfmisc_1 @
% 0.21/0.52                                        ( u1_struct_0 @ C ) @ 
% 0.21/0.52                                        ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.52                                ( ( ![G:$i]:
% 0.21/0.52                                    ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.21/0.52                                      ( ( r2_hidden @ G @ ( u1_struct_0 @ C ) ) =>
% 0.21/0.52                                        ( ( k3_funct_2 @
% 0.21/0.52                                            ( u1_struct_0 @ D ) @ 
% 0.21/0.52                                            ( u1_struct_0 @ B ) @ E @ G ) =
% 0.21/0.52                                          ( k1_funct_1 @ F @ G ) ) ) ) ) =>
% 0.21/0.52                                  ( r2_funct_2 @
% 0.21/0.52                                    ( u1_struct_0 @ C ) @ 
% 0.21/0.52                                    ( u1_struct_0 @ B ) @ 
% 0.21/0.52                                    ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.52    inference('cnf.neg', [status(esa)], [t73_tmap_1])).
% 0.21/0.52  thf('0', plain, (~ (v2_struct_0 @ sk_C)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('1', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_E @ 
% 0.21/0.52        (k1_zfmisc_1 @ 
% 0.21/0.52         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('2', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_F_1 @ 
% 0.21/0.52        (k1_zfmisc_1 @ 
% 0.21/0.52         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(t173_funct_2, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.21/0.52           ( ![C:$i]:
% 0.21/0.52             ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.52                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.52               ( ![D:$i]:
% 0.21/0.52                 ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.21/0.52                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.52                   ( ![E:$i]:
% 0.21/0.52                     ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ D @ B ) & 
% 0.21/0.52                         ( m1_subset_1 @
% 0.21/0.52                           E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.21/0.52                       ( ( ![F:$i]:
% 0.21/0.52                           ( ( m1_subset_1 @ F @ A ) =>
% 0.21/0.52                             ( ( r2_hidden @ F @ D ) =>
% 0.21/0.52                               ( ( k3_funct_2 @ A @ B @ C @ F ) =
% 0.21/0.52                                 ( k1_funct_1 @ E @ F ) ) ) ) ) =>
% 0.21/0.52                         ( ( k2_partfun1 @ A @ B @ C @ D ) = ( E ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.52  thf('3', plain,
% 0.21/0.52      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.52         ((v1_xboole_0 @ X4)
% 0.21/0.52          | (v1_xboole_0 @ X5)
% 0.21/0.52          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 0.21/0.52          | (m1_subset_1 @ (sk_F @ X7 @ X5 @ X8 @ X4 @ X6) @ X6)
% 0.21/0.52          | ((k2_partfun1 @ X6 @ X4 @ X8 @ X5) = (X7))
% 0.21/0.52          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X4)))
% 0.21/0.52          | ~ (v1_funct_2 @ X7 @ X5 @ X4)
% 0.21/0.52          | ~ (v1_funct_1 @ X7)
% 0.21/0.52          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X4)))
% 0.21/0.52          | ~ (v1_funct_2 @ X8 @ X6 @ X4)
% 0.21/0.52          | ~ (v1_funct_1 @ X8)
% 0.21/0.52          | (v1_xboole_0 @ X6))),
% 0.21/0.52      inference('cnf', [status(esa)], [t173_funct_2])).
% 0.21/0.52  thf('4', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((v1_xboole_0 @ X0)
% 0.21/0.52          | ~ (v1_funct_1 @ X1)
% 0.21/0.52          | ~ (v1_funct_2 @ X1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.21/0.52          | ~ (m1_subset_1 @ X1 @ 
% 0.21/0.52               (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ (u1_struct_0 @ sk_B))))
% 0.21/0.52          | ~ (v1_funct_1 @ sk_F_1)
% 0.21/0.52          | ~ (v1_funct_2 @ sk_F_1 @ (u1_struct_0 @ sk_C) @ 
% 0.21/0.52               (u1_struct_0 @ sk_B))
% 0.21/0.52          | ((k2_partfun1 @ X0 @ (u1_struct_0 @ sk_B) @ X1 @ 
% 0.21/0.52              (u1_struct_0 @ sk_C)) = (sk_F_1))
% 0.21/0.52          | (m1_subset_1 @ 
% 0.21/0.52             (sk_F @ sk_F_1 @ (u1_struct_0 @ sk_C) @ X1 @ 
% 0.21/0.52              (u1_struct_0 @ sk_B) @ X0) @ 
% 0.21/0.52             X0)
% 0.21/0.52          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_C) @ (k1_zfmisc_1 @ X0))
% 0.21/0.52          | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.21/0.52          | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.52  thf('5', plain, ((v1_funct_1 @ sk_F_1)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('6', plain,
% 0.21/0.52      ((v1_funct_2 @ sk_F_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('7', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((v1_xboole_0 @ X0)
% 0.21/0.52          | ~ (v1_funct_1 @ X1)
% 0.21/0.52          | ~ (v1_funct_2 @ X1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.21/0.52          | ~ (m1_subset_1 @ X1 @ 
% 0.21/0.52               (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ (u1_struct_0 @ sk_B))))
% 0.21/0.52          | ((k2_partfun1 @ X0 @ (u1_struct_0 @ sk_B) @ X1 @ 
% 0.21/0.52              (u1_struct_0 @ sk_C)) = (sk_F_1))
% 0.21/0.52          | (m1_subset_1 @ 
% 0.21/0.52             (sk_F @ sk_F_1 @ (u1_struct_0 @ sk_C) @ X1 @ 
% 0.21/0.52              (u1_struct_0 @ sk_B) @ X0) @ 
% 0.21/0.52             X0)
% 0.21/0.52          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_C) @ (k1_zfmisc_1 @ X0))
% 0.21/0.52          | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.21/0.52          | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.52      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.21/0.52  thf('8', plain,
% 0.21/0.52      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.21/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.21/0.52        | ~ (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.21/0.52             (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.21/0.52        | (m1_subset_1 @ 
% 0.21/0.52           (sk_F @ sk_F_1 @ (u1_struct_0 @ sk_C) @ sk_E @ 
% 0.21/0.52            (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)) @ 
% 0.21/0.52           (u1_struct_0 @ sk_D))
% 0.21/0.52        | ((k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.21/0.52            (u1_struct_0 @ sk_C)) = (sk_F_1))
% 0.21/0.52        | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.21/0.52        | ~ (v1_funct_1 @ sk_E)
% 0.21/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_D)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['1', '7'])).
% 0.21/0.52  thf('9', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(t1_tsep_1, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( l1_pre_topc @ A ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.52           ( m1_subset_1 @
% 0.21/0.52             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.21/0.52  thf('10', plain,
% 0.21/0.52      (![X18 : $i, X19 : $i]:
% 0.21/0.52         (~ (m1_pre_topc @ X18 @ X19)
% 0.21/0.52          | (m1_subset_1 @ (u1_struct_0 @ X18) @ 
% 0.21/0.52             (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.21/0.52          | ~ (l1_pre_topc @ X19))),
% 0.21/0.52      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.21/0.52  thf('11', plain,
% 0.21/0.52      ((~ (l1_pre_topc @ sk_D)
% 0.21/0.52        | (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.21/0.52           (k1_zfmisc_1 @ (u1_struct_0 @ sk_D))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.52  thf('12', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(dt_m1_pre_topc, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( l1_pre_topc @ A ) =>
% 0.21/0.52       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.21/0.52  thf('13', plain,
% 0.21/0.52      (![X10 : $i, X11 : $i]:
% 0.21/0.52         (~ (m1_pre_topc @ X10 @ X11)
% 0.21/0.52          | (l1_pre_topc @ X10)
% 0.21/0.52          | ~ (l1_pre_topc @ X11))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.21/0.52  thf('14', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 0.21/0.52      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.52  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('16', plain, ((l1_pre_topc @ sk_D)),
% 0.21/0.52      inference('demod', [status(thm)], ['14', '15'])).
% 0.21/0.52  thf('17', plain,
% 0.21/0.52      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.21/0.52        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.21/0.52      inference('demod', [status(thm)], ['11', '16'])).
% 0.21/0.52  thf('18', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('19', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('20', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_E @ 
% 0.21/0.52        (k1_zfmisc_1 @ 
% 0.21/0.52         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(d5_tmap_1, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.52             ( l1_pre_topc @ B ) ) =>
% 0.21/0.52           ( ![C:$i]:
% 0.21/0.52             ( ( m1_pre_topc @ C @ A ) =>
% 0.21/0.52               ( ![D:$i]:
% 0.21/0.52                 ( ( m1_pre_topc @ D @ A ) =>
% 0.21/0.52                   ( ![E:$i]:
% 0.21/0.52                     ( ( ( v1_funct_1 @ E ) & 
% 0.21/0.52                         ( v1_funct_2 @
% 0.21/0.52                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.52                         ( m1_subset_1 @
% 0.21/0.52                           E @ 
% 0.21/0.52                           ( k1_zfmisc_1 @
% 0.21/0.52                             ( k2_zfmisc_1 @
% 0.21/0.52                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.52                       ( ( m1_pre_topc @ D @ C ) =>
% 0.21/0.52                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 0.21/0.52                           ( k2_partfun1 @
% 0.21/0.52                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 0.21/0.52                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.52  thf('21', plain,
% 0.21/0.52      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.52         ((v2_struct_0 @ X13)
% 0.21/0.52          | ~ (v2_pre_topc @ X13)
% 0.21/0.52          | ~ (l1_pre_topc @ X13)
% 0.21/0.52          | ~ (m1_pre_topc @ X14 @ X15)
% 0.21/0.52          | ~ (m1_pre_topc @ X14 @ X16)
% 0.21/0.52          | ((k3_tmap_1 @ X15 @ X13 @ X16 @ X14 @ X17)
% 0.21/0.52              = (k2_partfun1 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X13) @ 
% 0.21/0.52                 X17 @ (u1_struct_0 @ X14)))
% 0.21/0.52          | ~ (m1_subset_1 @ X17 @ 
% 0.21/0.52               (k1_zfmisc_1 @ 
% 0.21/0.52                (k2_zfmisc_1 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X13))))
% 0.21/0.52          | ~ (v1_funct_2 @ X17 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X13))
% 0.21/0.52          | ~ (v1_funct_1 @ X17)
% 0.21/0.52          | ~ (m1_pre_topc @ X16 @ X15)
% 0.21/0.52          | ~ (l1_pre_topc @ X15)
% 0.21/0.52          | ~ (v2_pre_topc @ X15)
% 0.21/0.52          | (v2_struct_0 @ X15))),
% 0.21/0.52      inference('cnf', [status(esa)], [d5_tmap_1])).
% 0.21/0.52  thf('22', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((v2_struct_0 @ X0)
% 0.21/0.52          | ~ (v2_pre_topc @ X0)
% 0.21/0.52          | ~ (l1_pre_topc @ X0)
% 0.21/0.52          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.21/0.52          | ~ (v1_funct_1 @ sk_E)
% 0.21/0.52          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.21/0.52          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E)
% 0.21/0.52              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.52                 sk_E @ (u1_struct_0 @ X1)))
% 0.21/0.52          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.21/0.52          | ~ (m1_pre_topc @ X1 @ X0)
% 0.21/0.52          | ~ (l1_pre_topc @ sk_B)
% 0.21/0.52          | ~ (v2_pre_topc @ sk_B)
% 0.21/0.52          | (v2_struct_0 @ sk_B))),
% 0.21/0.52      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.52  thf('23', plain, ((v1_funct_1 @ sk_E)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('24', plain,
% 0.21/0.52      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('25', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('26', plain, ((v2_pre_topc @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('27', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((v2_struct_0 @ X0)
% 0.21/0.52          | ~ (v2_pre_topc @ X0)
% 0.21/0.52          | ~ (l1_pre_topc @ X0)
% 0.21/0.52          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.21/0.52          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E)
% 0.21/0.52              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.52                 sk_E @ (u1_struct_0 @ X1)))
% 0.21/0.52          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.21/0.52          | ~ (m1_pre_topc @ X1 @ X0)
% 0.21/0.52          | (v2_struct_0 @ sk_B))),
% 0.21/0.52      inference('demod', [status(thm)], ['22', '23', '24', '25', '26'])).
% 0.21/0.52  thf('28', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((v2_struct_0 @ sk_B)
% 0.21/0.52          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.21/0.52          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.21/0.52          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_E)
% 0.21/0.52              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.52                 sk_E @ (u1_struct_0 @ X0)))
% 0.21/0.52          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.52          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.52          | (v2_struct_0 @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['19', '27'])).
% 0.21/0.52  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('30', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('31', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((v2_struct_0 @ sk_B)
% 0.21/0.52          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.21/0.52          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.21/0.52          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_E)
% 0.21/0.52              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.52                 sk_E @ (u1_struct_0 @ X0)))
% 0.21/0.52          | (v2_struct_0 @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.21/0.52  thf('32', plain,
% 0.21/0.52      (((v2_struct_0 @ sk_A)
% 0.21/0.52        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.21/0.52            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.52               sk_E @ (u1_struct_0 @ sk_C)))
% 0.21/0.52        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.21/0.52        | (v2_struct_0 @ sk_B))),
% 0.21/0.52      inference('sup-', [status(thm)], ['18', '31'])).
% 0.21/0.52  thf('33', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('34', plain,
% 0.21/0.52      (((v2_struct_0 @ sk_A)
% 0.21/0.52        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.21/0.52            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.52               sk_E @ (u1_struct_0 @ sk_C)))
% 0.21/0.52        | (v2_struct_0 @ sk_B))),
% 0.21/0.52      inference('demod', [status(thm)], ['32', '33'])).
% 0.21/0.52  thf('35', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('36', plain,
% 0.21/0.52      (((v2_struct_0 @ sk_B)
% 0.21/0.52        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.21/0.52            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.52               sk_E @ (u1_struct_0 @ sk_C))))),
% 0.21/0.52      inference('clc', [status(thm)], ['34', '35'])).
% 0.21/0.52  thf('37', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('38', plain,
% 0.21/0.52      (((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.21/0.52         = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.21/0.52            (u1_struct_0 @ sk_C)))),
% 0.21/0.52      inference('clc', [status(thm)], ['36', '37'])).
% 0.21/0.52  thf('39', plain,
% 0.21/0.52      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('40', plain, ((v1_funct_1 @ sk_E)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('41', plain,
% 0.21/0.52      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.21/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.21/0.52        | (m1_subset_1 @ 
% 0.21/0.52           (sk_F @ sk_F_1 @ (u1_struct_0 @ sk_C) @ sk_E @ 
% 0.21/0.52            (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)) @ 
% 0.21/0.52           (u1_struct_0 @ sk_D))
% 0.21/0.52        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) = (sk_F_1))
% 0.21/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_D)))),
% 0.21/0.52      inference('demod', [status(thm)], ['8', '17', '38', '39', '40'])).
% 0.21/0.52  thf('42', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_E @ 
% 0.21/0.52        (k1_zfmisc_1 @ 
% 0.21/0.52         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('43', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_F_1 @ 
% 0.21/0.52        (k1_zfmisc_1 @ 
% 0.21/0.52         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('44', plain,
% 0.21/0.52      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.52         ((v1_xboole_0 @ X4)
% 0.21/0.52          | (v1_xboole_0 @ X5)
% 0.21/0.52          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 0.21/0.52          | (r2_hidden @ (sk_F @ X7 @ X5 @ X8 @ X4 @ X6) @ X5)
% 0.21/0.52          | ((k2_partfun1 @ X6 @ X4 @ X8 @ X5) = (X7))
% 0.21/0.52          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X4)))
% 0.21/0.52          | ~ (v1_funct_2 @ X7 @ X5 @ X4)
% 0.21/0.52          | ~ (v1_funct_1 @ X7)
% 0.21/0.52          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X4)))
% 0.21/0.52          | ~ (v1_funct_2 @ X8 @ X6 @ X4)
% 0.21/0.52          | ~ (v1_funct_1 @ X8)
% 0.21/0.52          | (v1_xboole_0 @ X6))),
% 0.21/0.52      inference('cnf', [status(esa)], [t173_funct_2])).
% 0.21/0.52  thf('45', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((v1_xboole_0 @ X0)
% 0.21/0.52          | ~ (v1_funct_1 @ X1)
% 0.21/0.52          | ~ (v1_funct_2 @ X1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.21/0.52          | ~ (m1_subset_1 @ X1 @ 
% 0.21/0.52               (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ (u1_struct_0 @ sk_B))))
% 0.21/0.52          | ~ (v1_funct_1 @ sk_F_1)
% 0.21/0.52          | ~ (v1_funct_2 @ sk_F_1 @ (u1_struct_0 @ sk_C) @ 
% 0.21/0.52               (u1_struct_0 @ sk_B))
% 0.21/0.52          | ((k2_partfun1 @ X0 @ (u1_struct_0 @ sk_B) @ X1 @ 
% 0.21/0.52              (u1_struct_0 @ sk_C)) = (sk_F_1))
% 0.21/0.52          | (r2_hidden @ 
% 0.21/0.52             (sk_F @ sk_F_1 @ (u1_struct_0 @ sk_C) @ X1 @ 
% 0.21/0.52              (u1_struct_0 @ sk_B) @ X0) @ 
% 0.21/0.52             (u1_struct_0 @ sk_C))
% 0.21/0.52          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_C) @ (k1_zfmisc_1 @ X0))
% 0.21/0.52          | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.21/0.52          | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['43', '44'])).
% 0.21/0.52  thf('46', plain, ((v1_funct_1 @ sk_F_1)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('47', plain,
% 0.21/0.52      ((v1_funct_2 @ sk_F_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('48', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((v1_xboole_0 @ X0)
% 0.21/0.52          | ~ (v1_funct_1 @ X1)
% 0.21/0.52          | ~ (v1_funct_2 @ X1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.21/0.52          | ~ (m1_subset_1 @ X1 @ 
% 0.21/0.52               (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ (u1_struct_0 @ sk_B))))
% 0.21/0.52          | ((k2_partfun1 @ X0 @ (u1_struct_0 @ sk_B) @ X1 @ 
% 0.21/0.52              (u1_struct_0 @ sk_C)) = (sk_F_1))
% 0.21/0.52          | (r2_hidden @ 
% 0.21/0.52             (sk_F @ sk_F_1 @ (u1_struct_0 @ sk_C) @ X1 @ 
% 0.21/0.52              (u1_struct_0 @ sk_B) @ X0) @ 
% 0.21/0.52             (u1_struct_0 @ sk_C))
% 0.21/0.52          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_C) @ (k1_zfmisc_1 @ X0))
% 0.21/0.52          | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.21/0.52          | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.52      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.21/0.52  thf('49', plain,
% 0.21/0.52      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.21/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.21/0.52        | ~ (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.21/0.52             (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.21/0.52        | (r2_hidden @ 
% 0.21/0.52           (sk_F @ sk_F_1 @ (u1_struct_0 @ sk_C) @ sk_E @ 
% 0.21/0.52            (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)) @ 
% 0.21/0.52           (u1_struct_0 @ sk_C))
% 0.21/0.52        | ((k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.21/0.52            (u1_struct_0 @ sk_C)) = (sk_F_1))
% 0.21/0.52        | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.21/0.52        | ~ (v1_funct_1 @ sk_E)
% 0.21/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_D)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['42', '48'])).
% 0.21/0.52  thf('50', plain,
% 0.21/0.52      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.21/0.52        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.21/0.52      inference('demod', [status(thm)], ['11', '16'])).
% 0.21/0.52  thf('51', plain,
% 0.21/0.52      (((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.21/0.52         = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.21/0.52            (u1_struct_0 @ sk_C)))),
% 0.21/0.52      inference('clc', [status(thm)], ['36', '37'])).
% 0.21/0.52  thf('52', plain,
% 0.21/0.52      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('53', plain, ((v1_funct_1 @ sk_E)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('54', plain,
% 0.21/0.52      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.21/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.21/0.52        | (r2_hidden @ 
% 0.21/0.52           (sk_F @ sk_F_1 @ (u1_struct_0 @ sk_C) @ sk_E @ 
% 0.21/0.52            (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)) @ 
% 0.21/0.52           (u1_struct_0 @ sk_C))
% 0.21/0.52        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) = (sk_F_1))
% 0.21/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_D)))),
% 0.21/0.52      inference('demod', [status(thm)], ['49', '50', '51', '52', '53'])).
% 0.21/0.52  thf('55', plain,
% 0.21/0.52      (![X20 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X20 @ (u1_struct_0 @ sk_C))
% 0.21/0.52          | ((k3_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.52              sk_E @ X20) = (k1_funct_1 @ sk_F_1 @ X20))
% 0.21/0.52          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ sk_D)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('56', plain,
% 0.21/0.52      (((v1_xboole_0 @ (u1_struct_0 @ sk_D))
% 0.21/0.52        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) = (sk_F_1))
% 0.21/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.21/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.21/0.52        | ~ (m1_subset_1 @ 
% 0.21/0.52             (sk_F @ sk_F_1 @ (u1_struct_0 @ sk_C) @ sk_E @ 
% 0.21/0.52              (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)) @ 
% 0.21/0.52             (u1_struct_0 @ sk_D))
% 0.21/0.52        | ((k3_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.21/0.52            (sk_F @ sk_F_1 @ (u1_struct_0 @ sk_C) @ sk_E @ 
% 0.21/0.52             (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 0.21/0.52            = (k1_funct_1 @ sk_F_1 @ 
% 0.21/0.52               (sk_F @ sk_F_1 @ (u1_struct_0 @ sk_C) @ sk_E @ 
% 0.21/0.52                (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['54', '55'])).
% 0.21/0.52  thf('57', plain,
% 0.21/0.52      (((v1_xboole_0 @ (u1_struct_0 @ sk_D))
% 0.21/0.52        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) = (sk_F_1))
% 0.21/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.21/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.21/0.52        | ((k3_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.21/0.52            (sk_F @ sk_F_1 @ (u1_struct_0 @ sk_C) @ sk_E @ 
% 0.21/0.52             (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 0.21/0.52            = (k1_funct_1 @ sk_F_1 @ 
% 0.21/0.52               (sk_F @ sk_F_1 @ (u1_struct_0 @ sk_C) @ sk_E @ 
% 0.21/0.52                (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D))))
% 0.21/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.21/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.21/0.52        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) = (sk_F_1))
% 0.21/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_D)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['41', '56'])).
% 0.21/0.52  thf('58', plain,
% 0.21/0.52      ((((k3_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.21/0.52          (sk_F @ sk_F_1 @ (u1_struct_0 @ sk_C) @ sk_E @ 
% 0.21/0.52           (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 0.21/0.52          = (k1_funct_1 @ sk_F_1 @ 
% 0.21/0.52             (sk_F @ sk_F_1 @ (u1_struct_0 @ sk_C) @ sk_E @ 
% 0.21/0.52              (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D))))
% 0.21/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.21/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.21/0.52        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) = (sk_F_1))
% 0.21/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_D)))),
% 0.21/0.52      inference('simplify', [status(thm)], ['57'])).
% 0.21/0.52  thf('59', plain,
% 0.21/0.52      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.52         ((v1_xboole_0 @ X4)
% 0.21/0.52          | (v1_xboole_0 @ X5)
% 0.21/0.52          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 0.21/0.52          | ((k3_funct_2 @ X6 @ X4 @ X8 @ (sk_F @ X7 @ X5 @ X8 @ X4 @ X6))
% 0.21/0.52              != (k1_funct_1 @ X7 @ (sk_F @ X7 @ X5 @ X8 @ X4 @ X6)))
% 0.21/0.52          | ((k2_partfun1 @ X6 @ X4 @ X8 @ X5) = (X7))
% 0.21/0.52          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X4)))
% 0.21/0.52          | ~ (v1_funct_2 @ X7 @ X5 @ X4)
% 0.21/0.52          | ~ (v1_funct_1 @ X7)
% 0.21/0.52          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X4)))
% 0.21/0.52          | ~ (v1_funct_2 @ X8 @ X6 @ X4)
% 0.21/0.52          | ~ (v1_funct_1 @ X8)
% 0.21/0.52          | (v1_xboole_0 @ X6))),
% 0.21/0.52      inference('cnf', [status(esa)], [t173_funct_2])).
% 0.21/0.52  thf('60', plain,
% 0.21/0.52      ((((k1_funct_1 @ sk_F_1 @ 
% 0.21/0.52          (sk_F @ sk_F_1 @ (u1_struct_0 @ sk_C) @ sk_E @ 
% 0.21/0.52           (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 0.21/0.52          != (k1_funct_1 @ sk_F_1 @ 
% 0.21/0.52              (sk_F @ sk_F_1 @ (u1_struct_0 @ sk_C) @ sk_E @ 
% 0.21/0.52               (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D))))
% 0.21/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_D))
% 0.21/0.52        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) = (sk_F_1))
% 0.21/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.21/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.21/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_D))
% 0.21/0.52        | ~ (v1_funct_1 @ sk_E)
% 0.21/0.52        | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.21/0.52        | ~ (m1_subset_1 @ sk_E @ 
% 0.21/0.52             (k1_zfmisc_1 @ 
% 0.21/0.52              (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 0.21/0.52        | ~ (v1_funct_1 @ sk_F_1)
% 0.21/0.52        | ~ (v1_funct_2 @ sk_F_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.21/0.52        | ~ (m1_subset_1 @ sk_F_1 @ 
% 0.21/0.52             (k1_zfmisc_1 @ 
% 0.21/0.52              (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 0.21/0.52        | ((k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.21/0.52            (u1_struct_0 @ sk_C)) = (sk_F_1))
% 0.21/0.52        | ~ (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.21/0.52             (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.21/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.21/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['58', '59'])).
% 0.21/0.52  thf('61', plain, ((v1_funct_1 @ sk_E)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('62', plain,
% 0.21/0.52      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('63', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_E @ 
% 0.21/0.52        (k1_zfmisc_1 @ 
% 0.21/0.52         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('64', plain, ((v1_funct_1 @ sk_F_1)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('65', plain,
% 0.21/0.52      ((v1_funct_2 @ sk_F_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('66', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_F_1 @ 
% 0.21/0.52        (k1_zfmisc_1 @ 
% 0.21/0.52         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('67', plain,
% 0.21/0.52      (((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.21/0.52         = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.21/0.52            (u1_struct_0 @ sk_C)))),
% 0.21/0.52      inference('clc', [status(thm)], ['36', '37'])).
% 0.21/0.52  thf('68', plain,
% 0.21/0.52      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.21/0.52        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.21/0.52      inference('demod', [status(thm)], ['11', '16'])).
% 0.21/0.52  thf('69', plain,
% 0.21/0.52      ((((k1_funct_1 @ sk_F_1 @ 
% 0.21/0.52          (sk_F @ sk_F_1 @ (u1_struct_0 @ sk_C) @ sk_E @ 
% 0.21/0.52           (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 0.21/0.52          != (k1_funct_1 @ sk_F_1 @ 
% 0.21/0.52              (sk_F @ sk_F_1 @ (u1_struct_0 @ sk_C) @ sk_E @ 
% 0.21/0.52               (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D))))
% 0.21/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_D))
% 0.21/0.52        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) = (sk_F_1))
% 0.21/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.21/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.21/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_D))
% 0.21/0.52        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) = (sk_F_1))
% 0.21/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.21/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.52      inference('demod', [status(thm)],
% 0.21/0.52                ['60', '61', '62', '63', '64', '65', '66', '67', '68'])).
% 0.21/0.52  thf('70', plain,
% 0.21/0.52      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.21/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.21/0.52        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) = (sk_F_1))
% 0.21/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_D)))),
% 0.21/0.52      inference('simplify', [status(thm)], ['69'])).
% 0.21/0.52  thf('71', plain,
% 0.21/0.52      (~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.52          (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F_1)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('72', plain,
% 0.21/0.52      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_F_1 @ 
% 0.21/0.52           sk_F_1)
% 0.21/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_D))
% 0.21/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.21/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['70', '71'])).
% 0.21/0.52  thf('73', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_F_1 @ 
% 0.21/0.52        (k1_zfmisc_1 @ 
% 0.21/0.52         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(redefinition_r2_funct_2, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.52     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.52         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.21/0.52         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.21/0.52         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.52       ( ( r2_funct_2 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.21/0.52  thf('74', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 0.21/0.52          | ~ (v1_funct_2 @ X0 @ X1 @ X2)
% 0.21/0.52          | ~ (v1_funct_1 @ X0)
% 0.21/0.52          | ~ (v1_funct_1 @ X3)
% 0.21/0.52          | ~ (v1_funct_2 @ X3 @ X1 @ X2)
% 0.21/0.52          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 0.21/0.52          | (r2_funct_2 @ X1 @ X2 @ X0 @ X3)
% 0.21/0.52          | ((X0) != (X3)))),
% 0.21/0.52      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 0.21/0.52  thf('75', plain,
% 0.21/0.52      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.52         ((r2_funct_2 @ X1 @ X2 @ X3 @ X3)
% 0.21/0.52          | ~ (v1_funct_1 @ X3)
% 0.21/0.52          | ~ (v1_funct_2 @ X3 @ X1 @ X2)
% 0.21/0.52          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2))))),
% 0.21/0.52      inference('simplify', [status(thm)], ['74'])).
% 0.21/0.52  thf('76', plain,
% 0.21/0.52      ((~ (v1_funct_2 @ sk_F_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.21/0.52        | ~ (v1_funct_1 @ sk_F_1)
% 0.21/0.52        | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_F_1 @ 
% 0.21/0.52           sk_F_1))),
% 0.21/0.52      inference('sup-', [status(thm)], ['73', '75'])).
% 0.21/0.52  thf('77', plain,
% 0.21/0.52      ((v1_funct_2 @ sk_F_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('78', plain, ((v1_funct_1 @ sk_F_1)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('79', plain,
% 0.21/0.52      ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_F_1 @ 
% 0.21/0.52        sk_F_1)),
% 0.21/0.52      inference('demod', [status(thm)], ['76', '77', '78'])).
% 0.21/0.52  thf('80', plain,
% 0.21/0.52      (((v1_xboole_0 @ (u1_struct_0 @ sk_D))
% 0.21/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.21/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.52      inference('demod', [status(thm)], ['72', '79'])).
% 0.21/0.52  thf(fc2_struct_0, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.52       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.52  thf('81', plain,
% 0.21/0.52      (![X12 : $i]:
% 0.21/0.52         (~ (v1_xboole_0 @ (u1_struct_0 @ X12))
% 0.21/0.52          | ~ (l1_struct_0 @ X12)
% 0.21/0.52          | (v2_struct_0 @ X12))),
% 0.21/0.52      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.21/0.52  thf('82', plain,
% 0.21/0.52      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.21/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_D))
% 0.21/0.52        | (v2_struct_0 @ sk_B)
% 0.21/0.52        | ~ (l1_struct_0 @ sk_B))),
% 0.21/0.52      inference('sup-', [status(thm)], ['80', '81'])).
% 0.21/0.52  thf('83', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(dt_l1_pre_topc, axiom,
% 0.21/0.52    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.52  thf('84', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.52  thf('85', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.52      inference('sup-', [status(thm)], ['83', '84'])).
% 0.21/0.52  thf('86', plain,
% 0.21/0.52      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.21/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_D))
% 0.21/0.52        | (v2_struct_0 @ sk_B))),
% 0.21/0.52      inference('demod', [status(thm)], ['82', '85'])).
% 0.21/0.52  thf('87', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('88', plain,
% 0.21/0.52      (((v1_xboole_0 @ (u1_struct_0 @ sk_D))
% 0.21/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_C)))),
% 0.21/0.52      inference('clc', [status(thm)], ['86', '87'])).
% 0.21/0.52  thf('89', plain,
% 0.21/0.52      (![X12 : $i]:
% 0.21/0.52         (~ (v1_xboole_0 @ (u1_struct_0 @ X12))
% 0.21/0.52          | ~ (l1_struct_0 @ X12)
% 0.21/0.52          | (v2_struct_0 @ X12))),
% 0.21/0.52      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.21/0.52  thf('90', plain,
% 0.21/0.52      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.21/0.52        | (v2_struct_0 @ sk_D)
% 0.21/0.52        | ~ (l1_struct_0 @ sk_D))),
% 0.21/0.52      inference('sup-', [status(thm)], ['88', '89'])).
% 0.21/0.52  thf('91', plain, ((l1_pre_topc @ sk_D)),
% 0.21/0.52      inference('demod', [status(thm)], ['14', '15'])).
% 0.21/0.52  thf('92', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.52  thf('93', plain, ((l1_struct_0 @ sk_D)),
% 0.21/0.52      inference('sup-', [status(thm)], ['91', '92'])).
% 0.21/0.52  thf('94', plain,
% 0.21/0.52      (((v1_xboole_0 @ (u1_struct_0 @ sk_C)) | (v2_struct_0 @ sk_D))),
% 0.21/0.52      inference('demod', [status(thm)], ['90', '93'])).
% 0.21/0.52  thf('95', plain, (~ (v2_struct_0 @ sk_D)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('96', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_C))),
% 0.21/0.52      inference('clc', [status(thm)], ['94', '95'])).
% 0.21/0.52  thf('97', plain,
% 0.21/0.52      (![X12 : $i]:
% 0.21/0.52         (~ (v1_xboole_0 @ (u1_struct_0 @ X12))
% 0.21/0.52          | ~ (l1_struct_0 @ X12)
% 0.21/0.52          | (v2_struct_0 @ X12))),
% 0.21/0.52      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.21/0.52  thf('98', plain, (((v2_struct_0 @ sk_C) | ~ (l1_struct_0 @ sk_C))),
% 0.21/0.52      inference('sup-', [status(thm)], ['96', '97'])).
% 0.21/0.52  thf('99', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('100', plain,
% 0.21/0.52      (![X10 : $i, X11 : $i]:
% 0.21/0.52         (~ (m1_pre_topc @ X10 @ X11)
% 0.21/0.52          | (l1_pre_topc @ X10)
% 0.21/0.52          | ~ (l1_pre_topc @ X11))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.21/0.52  thf('101', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 0.21/0.52      inference('sup-', [status(thm)], ['99', '100'])).
% 0.21/0.52  thf('102', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('103', plain, ((l1_pre_topc @ sk_C)),
% 0.21/0.52      inference('demod', [status(thm)], ['101', '102'])).
% 0.21/0.52  thf('104', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.52  thf('105', plain, ((l1_struct_0 @ sk_C)),
% 0.21/0.52      inference('sup-', [status(thm)], ['103', '104'])).
% 0.21/0.52  thf('106', plain, ((v2_struct_0 @ sk_C)),
% 0.21/0.52      inference('demod', [status(thm)], ['98', '105'])).
% 0.21/0.52  thf('107', plain, ($false), inference('demod', [status(thm)], ['0', '106'])).
% 0.21/0.52  
% 0.21/0.52  % SZS output end Refutation
% 0.21/0.52  
% 0.21/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
