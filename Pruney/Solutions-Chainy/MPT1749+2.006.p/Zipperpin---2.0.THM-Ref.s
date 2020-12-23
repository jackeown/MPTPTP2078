%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.nUjny8JM0j

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:38 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 310 expanded)
%              Number of leaves         :   32 ( 107 expanded)
%              Depth                    :   25
%              Number of atoms          : 1753 (12653 expanded)
%              Number of equality atoms :   42 ( 188 expanded)
%              Maximal formula depth    :   22 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(t59_tmap_1,conjecture,(
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
                         => ( r2_funct_2 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ ( k2_tmap_1 @ B @ A @ D @ C ) @ E ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t59_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
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
      | ~ ( v1_funct_2 @ X1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_partfun1 @ X0 @ ( u1_struct_0 @ sk_A ) @ X1 @ ( u1_struct_0 @ sk_C ) )
        = sk_E )
      | ( m1_subset_1 @ ( sk_F @ sk_E @ ( u1_struct_0 @ sk_C ) @ X1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ X0 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( ( k2_partfun1 @ X0 @ ( u1_struct_0 @ sk_A ) @ X1 @ ( u1_struct_0 @ sk_C ) )
        = sk_E )
      | ( m1_subset_1 @ ( sk_F @ sk_E @ ( u1_struct_0 @ sk_C ) @ X1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ X0 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( m1_subset_1 @ ( sk_F @ sk_E @ ( u1_struct_0 @ sk_C ) @ sk_D @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( u1_struct_0 @ sk_C ) )
      = sk_E )
    | ~ ( v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf('9',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('10',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_pre_topc @ X17 @ X18 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X17 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('11',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
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

thf('16',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( v2_struct_0 @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( m1_pre_topc @ X14 @ X15 )
      | ( ( k2_tmap_1 @ X15 @ X13 @ X16 @ X14 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X13 ) @ X16 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X13 ) ) ) )
      | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X13 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','18','19','20','21','22','23'])).

thf('25',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['14','24'])).

thf('26',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('28',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('30',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( m1_subset_1 @ ( sk_F @ sk_E @ ( u1_struct_0 @ sk_C ) @ sk_D @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
      = sk_E )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['8','13','29','30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
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

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_partfun1 @ X0 @ ( u1_struct_0 @ sk_A ) @ X1 @ ( u1_struct_0 @ sk_C ) )
        = sk_E )
      | ( r2_hidden @ ( sk_F @ sk_E @ ( u1_struct_0 @ sk_C ) @ X1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( u1_struct_0 @ sk_C ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( ( k2_partfun1 @ X0 @ ( u1_struct_0 @ sk_A ) @ X1 @ ( u1_struct_0 @ sk_C ) )
        = sk_E )
      | ( r2_hidden @ ( sk_F @ sk_E @ ( u1_struct_0 @ sk_C ) @ X1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( u1_struct_0 @ sk_C ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( r2_hidden @ ( sk_F @ sk_E @ ( u1_struct_0 @ sk_C ) @ sk_D @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_C ) )
    | ( ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( u1_struct_0 @ sk_C ) )
      = sk_E )
    | ~ ( v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['33','39'])).

thf('41',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('42',plain,
    ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('43',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( r2_hidden @ ( sk_F @ sk_E @ ( u1_struct_0 @ sk_C ) @ sk_D @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_C ) )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
      = sk_E )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['40','41','42','43','44'])).

thf('46',plain,(
    ! [X19: $i] :
      ( ~ ( r2_hidden @ X19 @ ( u1_struct_0 @ sk_C ) )
      | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X19 )
        = ( k1_funct_1 @ sk_E @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
      = sk_E )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( sk_F @ sk_E @ ( u1_struct_0 @ sk_C ) @ sk_D @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( sk_F @ sk_E @ ( u1_struct_0 @ sk_C ) @ sk_D @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
      = ( k1_funct_1 @ sk_E @ ( sk_F @ sk_E @ ( u1_struct_0 @ sk_C ) @ sk_D @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
      = sk_E )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( sk_F @ sk_E @ ( u1_struct_0 @ sk_C ) @ sk_D @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
      = ( k1_funct_1 @ sk_E @ ( sk_F @ sk_E @ ( u1_struct_0 @ sk_C ) @ sk_D @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
      = sk_E )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['32','47'])).

thf('49',plain,
    ( ( ( k3_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( sk_F @ sk_E @ ( u1_struct_0 @ sk_C ) @ sk_D @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
      = ( k1_funct_1 @ sk_E @ ( sk_F @ sk_E @ ( u1_struct_0 @ sk_C ) @ sk_D @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
      = sk_E )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
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

thf('51',plain,
    ( ( ( k1_funct_1 @ sk_E @ ( sk_F @ sk_E @ ( u1_struct_0 @ sk_C ) @ sk_D @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
     != ( k1_funct_1 @ sk_E @ ( sk_F @ sk_E @ ( u1_struct_0 @ sk_C ) @ sk_D @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
      = sk_E )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( u1_struct_0 @ sk_C ) )
      = sk_E )
    | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('59',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('60',plain,
    ( ( ( k1_funct_1 @ sk_E @ ( sk_F @ sk_E @ ( u1_struct_0 @ sk_C ) @ sk_D @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
     != ( k1_funct_1 @ sk_E @ ( sk_F @ sk_E @ ( u1_struct_0 @ sk_C ) @ sk_D @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
      = sk_E )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
      = sk_E )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['51','52','53','54','55','56','57','58','59'])).

thf('61',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
      = sk_E )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C ) @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ sk_E )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
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

thf('65',plain,(
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

thf('66',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( r2_funct_2 @ X1 @ X2 @ X3 @ X3 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_funct_2 @ X3 @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,
    ( ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_E )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ sk_E ) ),
    inference('sup-',[status(thm)],['64','66'])).

thf('68',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ sk_E ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['63','70'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('72',plain,(
    ! [X12: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('73',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('75',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('76',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['73','76'])).

thf('78',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X12: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('81',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_C )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('83',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X10 @ X11 )
      | ( l1_pre_topc @ X10 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('84',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('88',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['81','88'])).

thf('90',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X12: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('93',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('96',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    v2_struct_0 @ sk_B ),
    inference(demod,[status(thm)],['93','96'])).

thf('98',plain,(
    $false ),
    inference(demod,[status(thm)],['0','97'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.nUjny8JM0j
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:34:11 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.50  % Solved by: fo/fo7.sh
% 0.19/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.50  % done 56 iterations in 0.046s
% 0.19/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.50  % SZS output start Refutation
% 0.19/0.50  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.19/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.50  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 0.19/0.50  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.19/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.50  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.19/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.50  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.19/0.50  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.19/0.50  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.19/0.50  thf(sk_D_type, type, sk_D: $i).
% 0.19/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.50  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.19/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.19/0.50  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.19/0.50  thf(sk_F_type, type, sk_F: $i > $i > $i > $i > $i > $i).
% 0.19/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.50  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.19/0.50  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.19/0.50  thf(sk_E_type, type, sk_E: $i).
% 0.19/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.50  thf(t59_tmap_1, conjecture,
% 0.19/0.50    (![A:$i]:
% 0.19/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.50       ( ![B:$i]:
% 0.19/0.50         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.19/0.50             ( l1_pre_topc @ B ) ) =>
% 0.19/0.50           ( ![C:$i]:
% 0.19/0.50             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.19/0.50               ( ![D:$i]:
% 0.19/0.50                 ( ( ( v1_funct_1 @ D ) & 
% 0.19/0.50                     ( v1_funct_2 @
% 0.19/0.50                       D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.19/0.50                     ( m1_subset_1 @
% 0.19/0.50                       D @ 
% 0.19/0.50                       ( k1_zfmisc_1 @
% 0.19/0.50                         ( k2_zfmisc_1 @
% 0.19/0.50                           ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.19/0.50                   ( ![E:$i]:
% 0.19/0.50                     ( ( ( v1_funct_1 @ E ) & 
% 0.19/0.50                         ( v1_funct_2 @
% 0.19/0.50                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) ) & 
% 0.19/0.50                         ( m1_subset_1 @
% 0.19/0.50                           E @ 
% 0.19/0.50                           ( k1_zfmisc_1 @
% 0.19/0.50                             ( k2_zfmisc_1 @
% 0.19/0.50                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.19/0.50                       ( ( ![F:$i]:
% 0.19/0.50                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 0.19/0.50                             ( ( r2_hidden @ F @ ( u1_struct_0 @ C ) ) =>
% 0.19/0.50                               ( ( k3_funct_2 @
% 0.19/0.50                                   ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.19/0.50                                   D @ F ) =
% 0.19/0.50                                 ( k1_funct_1 @ E @ F ) ) ) ) ) =>
% 0.19/0.50                         ( r2_funct_2 @
% 0.19/0.50                           ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ 
% 0.19/0.50                           ( k2_tmap_1 @ B @ A @ D @ C ) @ E ) ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.50    (~( ![A:$i]:
% 0.19/0.50        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.19/0.50            ( l1_pre_topc @ A ) ) =>
% 0.19/0.50          ( ![B:$i]:
% 0.19/0.50            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.19/0.50                ( l1_pre_topc @ B ) ) =>
% 0.19/0.50              ( ![C:$i]:
% 0.19/0.50                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.19/0.50                  ( ![D:$i]:
% 0.19/0.50                    ( ( ( v1_funct_1 @ D ) & 
% 0.19/0.50                        ( v1_funct_2 @
% 0.19/0.50                          D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.19/0.50                        ( m1_subset_1 @
% 0.19/0.50                          D @ 
% 0.19/0.50                          ( k1_zfmisc_1 @
% 0.19/0.50                            ( k2_zfmisc_1 @
% 0.19/0.50                              ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.19/0.50                      ( ![E:$i]:
% 0.19/0.50                        ( ( ( v1_funct_1 @ E ) & 
% 0.19/0.50                            ( v1_funct_2 @
% 0.19/0.50                              E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) ) & 
% 0.19/0.50                            ( m1_subset_1 @
% 0.19/0.50                              E @ 
% 0.19/0.50                              ( k1_zfmisc_1 @
% 0.19/0.50                                ( k2_zfmisc_1 @
% 0.19/0.50                                  ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.19/0.50                          ( ( ![F:$i]:
% 0.19/0.50                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 0.19/0.50                                ( ( r2_hidden @ F @ ( u1_struct_0 @ C ) ) =>
% 0.19/0.50                                  ( ( k3_funct_2 @
% 0.19/0.50                                      ( u1_struct_0 @ B ) @ 
% 0.19/0.50                                      ( u1_struct_0 @ A ) @ D @ F ) =
% 0.19/0.50                                    ( k1_funct_1 @ E @ F ) ) ) ) ) =>
% 0.19/0.50                            ( r2_funct_2 @
% 0.19/0.50                              ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ 
% 0.19/0.50                              ( k2_tmap_1 @ B @ A @ D @ C ) @ E ) ) ) ) ) ) ) ) ) ) ) )),
% 0.19/0.50    inference('cnf.neg', [status(esa)], [t59_tmap_1])).
% 0.19/0.50  thf('0', plain, (~ (v2_struct_0 @ sk_B)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('1', plain,
% 0.19/0.50      ((m1_subset_1 @ sk_D @ 
% 0.19/0.50        (k1_zfmisc_1 @ 
% 0.19/0.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('2', plain,
% 0.19/0.50      ((m1_subset_1 @ sk_E @ 
% 0.19/0.50        (k1_zfmisc_1 @ 
% 0.19/0.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf(t173_funct_2, axiom,
% 0.19/0.50    (![A:$i]:
% 0.19/0.50     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.19/0.50       ( ![B:$i]:
% 0.19/0.50         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.19/0.50           ( ![C:$i]:
% 0.19/0.50             ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.19/0.50                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.19/0.50               ( ![D:$i]:
% 0.19/0.50                 ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.19/0.50                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.19/0.50                   ( ![E:$i]:
% 0.19/0.50                     ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ D @ B ) & 
% 0.19/0.50                         ( m1_subset_1 @
% 0.19/0.50                           E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.19/0.50                       ( ( ![F:$i]:
% 0.19/0.50                           ( ( m1_subset_1 @ F @ A ) =>
% 0.19/0.50                             ( ( r2_hidden @ F @ D ) =>
% 0.19/0.50                               ( ( k3_funct_2 @ A @ B @ C @ F ) =
% 0.19/0.50                                 ( k1_funct_1 @ E @ F ) ) ) ) ) =>
% 0.19/0.50                         ( ( k2_partfun1 @ A @ B @ C @ D ) = ( E ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.50  thf('3', plain,
% 0.19/0.50      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.19/0.50         ((v1_xboole_0 @ X4)
% 0.19/0.50          | (v1_xboole_0 @ X5)
% 0.19/0.50          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 0.19/0.50          | (m1_subset_1 @ (sk_F @ X7 @ X5 @ X8 @ X4 @ X6) @ X6)
% 0.19/0.50          | ((k2_partfun1 @ X6 @ X4 @ X8 @ X5) = (X7))
% 0.19/0.50          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X4)))
% 0.19/0.50          | ~ (v1_funct_2 @ X7 @ X5 @ X4)
% 0.19/0.50          | ~ (v1_funct_1 @ X7)
% 0.19/0.50          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X4)))
% 0.19/0.50          | ~ (v1_funct_2 @ X8 @ X6 @ X4)
% 0.19/0.50          | ~ (v1_funct_1 @ X8)
% 0.19/0.50          | (v1_xboole_0 @ X6))),
% 0.19/0.50      inference('cnf', [status(esa)], [t173_funct_2])).
% 0.19/0.50  thf('4', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]:
% 0.19/0.50         ((v1_xboole_0 @ X0)
% 0.19/0.50          | ~ (v1_funct_1 @ X1)
% 0.19/0.50          | ~ (v1_funct_2 @ X1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.19/0.50          | ~ (m1_subset_1 @ X1 @ 
% 0.19/0.50               (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ (u1_struct_0 @ sk_A))))
% 0.19/0.50          | ~ (v1_funct_1 @ sk_E)
% 0.19/0.50          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))
% 0.19/0.50          | ((k2_partfun1 @ X0 @ (u1_struct_0 @ sk_A) @ X1 @ 
% 0.19/0.50              (u1_struct_0 @ sk_C)) = (sk_E))
% 0.19/0.50          | (m1_subset_1 @ 
% 0.19/0.50             (sk_F @ sk_E @ (u1_struct_0 @ sk_C) @ X1 @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.50              X0) @ 
% 0.19/0.50             X0)
% 0.19/0.50          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_C) @ (k1_zfmisc_1 @ X0))
% 0.19/0.50          | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.19/0.50          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['2', '3'])).
% 0.19/0.50  thf('5', plain, ((v1_funct_1 @ sk_E)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('6', plain,
% 0.19/0.50      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('7', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]:
% 0.19/0.50         ((v1_xboole_0 @ X0)
% 0.19/0.50          | ~ (v1_funct_1 @ X1)
% 0.19/0.50          | ~ (v1_funct_2 @ X1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.19/0.50          | ~ (m1_subset_1 @ X1 @ 
% 0.19/0.50               (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ (u1_struct_0 @ sk_A))))
% 0.19/0.50          | ((k2_partfun1 @ X0 @ (u1_struct_0 @ sk_A) @ X1 @ 
% 0.19/0.50              (u1_struct_0 @ sk_C)) = (sk_E))
% 0.19/0.50          | (m1_subset_1 @ 
% 0.19/0.50             (sk_F @ sk_E @ (u1_struct_0 @ sk_C) @ X1 @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.50              X0) @ 
% 0.19/0.50             X0)
% 0.19/0.50          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_C) @ (k1_zfmisc_1 @ X0))
% 0.19/0.50          | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.19/0.50          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.50      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.19/0.50  thf('8', plain,
% 0.19/0.50      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.19/0.50        | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.19/0.50        | ~ (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.19/0.50             (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.19/0.50        | (m1_subset_1 @ 
% 0.19/0.50           (sk_F @ sk_E @ (u1_struct_0 @ sk_C) @ sk_D @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.50            (u1_struct_0 @ sk_B)) @ 
% 0.19/0.50           (u1_struct_0 @ sk_B))
% 0.19/0.50        | ((k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.19/0.50            (u1_struct_0 @ sk_C)) = (sk_E))
% 0.19/0.50        | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.19/0.50        | ~ (v1_funct_1 @ sk_D)
% 0.19/0.50        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['1', '7'])).
% 0.19/0.50  thf('9', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf(t1_tsep_1, axiom,
% 0.19/0.50    (![A:$i]:
% 0.19/0.50     ( ( l1_pre_topc @ A ) =>
% 0.19/0.50       ( ![B:$i]:
% 0.19/0.50         ( ( m1_pre_topc @ B @ A ) =>
% 0.19/0.50           ( m1_subset_1 @
% 0.19/0.50             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.19/0.50  thf('10', plain,
% 0.19/0.50      (![X17 : $i, X18 : $i]:
% 0.19/0.50         (~ (m1_pre_topc @ X17 @ X18)
% 0.19/0.50          | (m1_subset_1 @ (u1_struct_0 @ X17) @ 
% 0.19/0.50             (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.19/0.50          | ~ (l1_pre_topc @ X18))),
% 0.19/0.50      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.19/0.50  thf('11', plain,
% 0.19/0.50      ((~ (l1_pre_topc @ sk_B)
% 0.19/0.50        | (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.19/0.50           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.19/0.50      inference('sup-', [status(thm)], ['9', '10'])).
% 0.19/0.50  thf('12', plain, ((l1_pre_topc @ sk_B)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('13', plain,
% 0.19/0.50      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.19/0.50        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.19/0.50      inference('demod', [status(thm)], ['11', '12'])).
% 0.19/0.50  thf('14', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('15', plain,
% 0.19/0.50      ((m1_subset_1 @ sk_D @ 
% 0.19/0.50        (k1_zfmisc_1 @ 
% 0.19/0.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf(d4_tmap_1, axiom,
% 0.19/0.50    (![A:$i]:
% 0.19/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.50       ( ![B:$i]:
% 0.19/0.50         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.19/0.50             ( l1_pre_topc @ B ) ) =>
% 0.19/0.50           ( ![C:$i]:
% 0.19/0.50             ( ( ( v1_funct_1 @ C ) & 
% 0.19/0.50                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.19/0.50                 ( m1_subset_1 @
% 0.19/0.50                   C @ 
% 0.19/0.50                   ( k1_zfmisc_1 @
% 0.19/0.50                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.19/0.50               ( ![D:$i]:
% 0.19/0.50                 ( ( m1_pre_topc @ D @ A ) =>
% 0.19/0.50                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 0.19/0.50                     ( k2_partfun1 @
% 0.19/0.50                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.19/0.50                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.50  thf('16', plain,
% 0.19/0.50      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.19/0.50         ((v2_struct_0 @ X13)
% 0.19/0.50          | ~ (v2_pre_topc @ X13)
% 0.19/0.50          | ~ (l1_pre_topc @ X13)
% 0.19/0.50          | ~ (m1_pre_topc @ X14 @ X15)
% 0.19/0.50          | ((k2_tmap_1 @ X15 @ X13 @ X16 @ X14)
% 0.19/0.50              = (k2_partfun1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X13) @ 
% 0.19/0.50                 X16 @ (u1_struct_0 @ X14)))
% 0.19/0.50          | ~ (m1_subset_1 @ X16 @ 
% 0.19/0.50               (k1_zfmisc_1 @ 
% 0.19/0.50                (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X13))))
% 0.19/0.50          | ~ (v1_funct_2 @ X16 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X13))
% 0.19/0.50          | ~ (v1_funct_1 @ X16)
% 0.19/0.50          | ~ (l1_pre_topc @ X15)
% 0.19/0.50          | ~ (v2_pre_topc @ X15)
% 0.19/0.50          | (v2_struct_0 @ X15))),
% 0.19/0.50      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.19/0.50  thf('17', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         ((v2_struct_0 @ sk_B)
% 0.19/0.50          | ~ (v2_pre_topc @ sk_B)
% 0.19/0.50          | ~ (l1_pre_topc @ sk_B)
% 0.19/0.50          | ~ (v1_funct_1 @ sk_D)
% 0.19/0.50          | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.19/0.50          | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0)
% 0.19/0.50              = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.50                 sk_D @ (u1_struct_0 @ X0)))
% 0.19/0.50          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.19/0.50          | ~ (l1_pre_topc @ sk_A)
% 0.19/0.50          | ~ (v2_pre_topc @ sk_A)
% 0.19/0.50          | (v2_struct_0 @ sk_A))),
% 0.19/0.50      inference('sup-', [status(thm)], ['15', '16'])).
% 0.19/0.50  thf('18', plain, ((v2_pre_topc @ sk_B)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('19', plain, ((l1_pre_topc @ sk_B)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('20', plain, ((v1_funct_1 @ sk_D)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('21', plain,
% 0.19/0.50      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('23', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('24', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         ((v2_struct_0 @ sk_B)
% 0.19/0.50          | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0)
% 0.19/0.50              = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.50                 sk_D @ (u1_struct_0 @ X0)))
% 0.19/0.50          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.19/0.50          | (v2_struct_0 @ sk_A))),
% 0.19/0.50      inference('demod', [status(thm)],
% 0.19/0.50                ['17', '18', '19', '20', '21', '22', '23'])).
% 0.19/0.50  thf('25', plain,
% 0.19/0.50      (((v2_struct_0 @ sk_A)
% 0.19/0.50        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.19/0.50            = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.50               sk_D @ (u1_struct_0 @ sk_C)))
% 0.19/0.50        | (v2_struct_0 @ sk_B))),
% 0.19/0.50      inference('sup-', [status(thm)], ['14', '24'])).
% 0.19/0.50  thf('26', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('27', plain,
% 0.19/0.50      (((v2_struct_0 @ sk_B)
% 0.19/0.50        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.19/0.50            = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.50               sk_D @ (u1_struct_0 @ sk_C))))),
% 0.19/0.50      inference('clc', [status(thm)], ['25', '26'])).
% 0.19/0.50  thf('28', plain, (~ (v2_struct_0 @ sk_B)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('29', plain,
% 0.19/0.50      (((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.19/0.50         = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.19/0.50            (u1_struct_0 @ sk_C)))),
% 0.19/0.50      inference('clc', [status(thm)], ['27', '28'])).
% 0.19/0.50  thf('30', plain,
% 0.19/0.50      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('31', plain, ((v1_funct_1 @ sk_D)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('32', plain,
% 0.19/0.50      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.19/0.50        | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.19/0.50        | (m1_subset_1 @ 
% 0.19/0.50           (sk_F @ sk_E @ (u1_struct_0 @ sk_C) @ sk_D @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.50            (u1_struct_0 @ sk_B)) @ 
% 0.19/0.50           (u1_struct_0 @ sk_B))
% 0.19/0.50        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C) = (sk_E))
% 0.19/0.50        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.19/0.50      inference('demod', [status(thm)], ['8', '13', '29', '30', '31'])).
% 0.19/0.50  thf('33', plain,
% 0.19/0.50      ((m1_subset_1 @ sk_D @ 
% 0.19/0.50        (k1_zfmisc_1 @ 
% 0.19/0.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('34', plain,
% 0.19/0.50      ((m1_subset_1 @ sk_E @ 
% 0.19/0.50        (k1_zfmisc_1 @ 
% 0.19/0.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('35', plain,
% 0.19/0.50      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.19/0.50         ((v1_xboole_0 @ X4)
% 0.19/0.50          | (v1_xboole_0 @ X5)
% 0.19/0.50          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 0.19/0.50          | (r2_hidden @ (sk_F @ X7 @ X5 @ X8 @ X4 @ X6) @ X5)
% 0.19/0.50          | ((k2_partfun1 @ X6 @ X4 @ X8 @ X5) = (X7))
% 0.19/0.50          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X4)))
% 0.19/0.50          | ~ (v1_funct_2 @ X7 @ X5 @ X4)
% 0.19/0.50          | ~ (v1_funct_1 @ X7)
% 0.19/0.50          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X4)))
% 0.19/0.50          | ~ (v1_funct_2 @ X8 @ X6 @ X4)
% 0.19/0.50          | ~ (v1_funct_1 @ X8)
% 0.19/0.50          | (v1_xboole_0 @ X6))),
% 0.19/0.50      inference('cnf', [status(esa)], [t173_funct_2])).
% 0.19/0.50  thf('36', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]:
% 0.19/0.50         ((v1_xboole_0 @ X0)
% 0.19/0.50          | ~ (v1_funct_1 @ X1)
% 0.19/0.50          | ~ (v1_funct_2 @ X1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.19/0.50          | ~ (m1_subset_1 @ X1 @ 
% 0.19/0.50               (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ (u1_struct_0 @ sk_A))))
% 0.19/0.50          | ~ (v1_funct_1 @ sk_E)
% 0.19/0.50          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))
% 0.19/0.50          | ((k2_partfun1 @ X0 @ (u1_struct_0 @ sk_A) @ X1 @ 
% 0.19/0.50              (u1_struct_0 @ sk_C)) = (sk_E))
% 0.19/0.50          | (r2_hidden @ 
% 0.19/0.50             (sk_F @ sk_E @ (u1_struct_0 @ sk_C) @ X1 @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.50              X0) @ 
% 0.19/0.50             (u1_struct_0 @ sk_C))
% 0.19/0.50          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_C) @ (k1_zfmisc_1 @ X0))
% 0.19/0.50          | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.19/0.50          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['34', '35'])).
% 0.19/0.50  thf('37', plain, ((v1_funct_1 @ sk_E)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('38', plain,
% 0.19/0.50      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('39', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]:
% 0.19/0.50         ((v1_xboole_0 @ X0)
% 0.19/0.50          | ~ (v1_funct_1 @ X1)
% 0.19/0.50          | ~ (v1_funct_2 @ X1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.19/0.50          | ~ (m1_subset_1 @ X1 @ 
% 0.19/0.50               (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ (u1_struct_0 @ sk_A))))
% 0.19/0.50          | ((k2_partfun1 @ X0 @ (u1_struct_0 @ sk_A) @ X1 @ 
% 0.19/0.50              (u1_struct_0 @ sk_C)) = (sk_E))
% 0.19/0.50          | (r2_hidden @ 
% 0.19/0.50             (sk_F @ sk_E @ (u1_struct_0 @ sk_C) @ X1 @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.50              X0) @ 
% 0.19/0.50             (u1_struct_0 @ sk_C))
% 0.19/0.50          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_C) @ (k1_zfmisc_1 @ X0))
% 0.19/0.50          | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.19/0.50          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.50      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.19/0.50  thf('40', plain,
% 0.19/0.50      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.19/0.50        | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.19/0.50        | ~ (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.19/0.50             (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.19/0.50        | (r2_hidden @ 
% 0.19/0.50           (sk_F @ sk_E @ (u1_struct_0 @ sk_C) @ sk_D @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.50            (u1_struct_0 @ sk_B)) @ 
% 0.19/0.50           (u1_struct_0 @ sk_C))
% 0.19/0.50        | ((k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.19/0.50            (u1_struct_0 @ sk_C)) = (sk_E))
% 0.19/0.50        | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.19/0.50        | ~ (v1_funct_1 @ sk_D)
% 0.19/0.50        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['33', '39'])).
% 0.19/0.50  thf('41', plain,
% 0.19/0.50      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.19/0.50        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.19/0.50      inference('demod', [status(thm)], ['11', '12'])).
% 0.19/0.50  thf('42', plain,
% 0.19/0.50      (((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.19/0.50         = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.19/0.50            (u1_struct_0 @ sk_C)))),
% 0.19/0.50      inference('clc', [status(thm)], ['27', '28'])).
% 0.19/0.50  thf('43', plain,
% 0.19/0.50      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('44', plain, ((v1_funct_1 @ sk_D)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('45', plain,
% 0.19/0.50      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.19/0.50        | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.19/0.50        | (r2_hidden @ 
% 0.19/0.50           (sk_F @ sk_E @ (u1_struct_0 @ sk_C) @ sk_D @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.50            (u1_struct_0 @ sk_B)) @ 
% 0.19/0.50           (u1_struct_0 @ sk_C))
% 0.19/0.50        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C) = (sk_E))
% 0.19/0.50        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.19/0.50      inference('demod', [status(thm)], ['40', '41', '42', '43', '44'])).
% 0.19/0.50  thf('46', plain,
% 0.19/0.50      (![X19 : $i]:
% 0.19/0.50         (~ (r2_hidden @ X19 @ (u1_struct_0 @ sk_C))
% 0.19/0.50          | ((k3_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.50              sk_D @ X19) = (k1_funct_1 @ sk_E @ X19))
% 0.19/0.50          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ sk_B)))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('47', plain,
% 0.19/0.50      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.19/0.50        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C) = (sk_E))
% 0.19/0.50        | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.19/0.50        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.19/0.50        | ~ (m1_subset_1 @ 
% 0.19/0.50             (sk_F @ sk_E @ (u1_struct_0 @ sk_C) @ sk_D @ 
% 0.19/0.50              (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)) @ 
% 0.19/0.50             (u1_struct_0 @ sk_B))
% 0.19/0.50        | ((k3_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.19/0.50            (sk_F @ sk_E @ (u1_struct_0 @ sk_C) @ sk_D @ 
% 0.19/0.50             (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 0.19/0.50            = (k1_funct_1 @ sk_E @ 
% 0.19/0.50               (sk_F @ sk_E @ (u1_struct_0 @ sk_C) @ sk_D @ 
% 0.19/0.50                (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))))),
% 0.19/0.50      inference('sup-', [status(thm)], ['45', '46'])).
% 0.19/0.50  thf('48', plain,
% 0.19/0.50      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.19/0.50        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C) = (sk_E))
% 0.19/0.50        | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.19/0.50        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.19/0.50        | ((k3_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.19/0.50            (sk_F @ sk_E @ (u1_struct_0 @ sk_C) @ sk_D @ 
% 0.19/0.50             (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 0.19/0.50            = (k1_funct_1 @ sk_E @ 
% 0.19/0.50               (sk_F @ sk_E @ (u1_struct_0 @ sk_C) @ sk_D @ 
% 0.19/0.50                (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.19/0.50        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.19/0.50        | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.19/0.50        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C) = (sk_E))
% 0.19/0.50        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['32', '47'])).
% 0.19/0.50  thf('49', plain,
% 0.19/0.50      ((((k3_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.19/0.50          (sk_F @ sk_E @ (u1_struct_0 @ sk_C) @ sk_D @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.50           (u1_struct_0 @ sk_B)))
% 0.19/0.50          = (k1_funct_1 @ sk_E @ 
% 0.19/0.50             (sk_F @ sk_E @ (u1_struct_0 @ sk_C) @ sk_D @ 
% 0.19/0.50              (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.19/0.50        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.19/0.50        | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.19/0.50        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C) = (sk_E))
% 0.19/0.50        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.19/0.50      inference('simplify', [status(thm)], ['48'])).
% 0.19/0.50  thf('50', plain,
% 0.19/0.50      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.19/0.50         ((v1_xboole_0 @ X4)
% 0.19/0.50          | (v1_xboole_0 @ X5)
% 0.19/0.50          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 0.19/0.50          | ((k3_funct_2 @ X6 @ X4 @ X8 @ (sk_F @ X7 @ X5 @ X8 @ X4 @ X6))
% 0.19/0.50              != (k1_funct_1 @ X7 @ (sk_F @ X7 @ X5 @ X8 @ X4 @ X6)))
% 0.19/0.50          | ((k2_partfun1 @ X6 @ X4 @ X8 @ X5) = (X7))
% 0.19/0.50          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X4)))
% 0.19/0.50          | ~ (v1_funct_2 @ X7 @ X5 @ X4)
% 0.19/0.50          | ~ (v1_funct_1 @ X7)
% 0.19/0.50          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X4)))
% 0.19/0.50          | ~ (v1_funct_2 @ X8 @ X6 @ X4)
% 0.19/0.50          | ~ (v1_funct_1 @ X8)
% 0.19/0.50          | (v1_xboole_0 @ X6))),
% 0.19/0.50      inference('cnf', [status(esa)], [t173_funct_2])).
% 0.19/0.50  thf('51', plain,
% 0.19/0.50      ((((k1_funct_1 @ sk_E @ 
% 0.19/0.50          (sk_F @ sk_E @ (u1_struct_0 @ sk_C) @ sk_D @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.50           (u1_struct_0 @ sk_B)))
% 0.19/0.50          != (k1_funct_1 @ sk_E @ 
% 0.19/0.50              (sk_F @ sk_E @ (u1_struct_0 @ sk_C) @ sk_D @ 
% 0.19/0.50               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.19/0.50        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.19/0.50        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C) = (sk_E))
% 0.19/0.50        | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.19/0.50        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.19/0.50        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.19/0.50        | ~ (v1_funct_1 @ sk_D)
% 0.19/0.50        | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.19/0.50        | ~ (m1_subset_1 @ sk_D @ 
% 0.19/0.50             (k1_zfmisc_1 @ 
% 0.19/0.50              (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 0.19/0.50        | ~ (v1_funct_1 @ sk_E)
% 0.19/0.50        | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))
% 0.19/0.50        | ~ (m1_subset_1 @ sk_E @ 
% 0.19/0.50             (k1_zfmisc_1 @ 
% 0.19/0.50              (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))
% 0.19/0.50        | ((k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.19/0.50            (u1_struct_0 @ sk_C)) = (sk_E))
% 0.19/0.50        | ~ (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.19/0.50             (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.19/0.50        | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.19/0.50        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['49', '50'])).
% 0.19/0.50  thf('52', plain, ((v1_funct_1 @ sk_D)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('53', plain,
% 0.19/0.50      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('54', plain,
% 0.19/0.50      ((m1_subset_1 @ sk_D @ 
% 0.19/0.50        (k1_zfmisc_1 @ 
% 0.19/0.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('55', plain, ((v1_funct_1 @ sk_E)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('56', plain,
% 0.19/0.50      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('57', plain,
% 0.19/0.50      ((m1_subset_1 @ sk_E @ 
% 0.19/0.50        (k1_zfmisc_1 @ 
% 0.19/0.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('58', plain,
% 0.19/0.50      (((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.19/0.50         = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.19/0.50            (u1_struct_0 @ sk_C)))),
% 0.19/0.50      inference('clc', [status(thm)], ['27', '28'])).
% 0.19/0.50  thf('59', plain,
% 0.19/0.50      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.19/0.50        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.19/0.50      inference('demod', [status(thm)], ['11', '12'])).
% 0.19/0.50  thf('60', plain,
% 0.19/0.50      ((((k1_funct_1 @ sk_E @ 
% 0.19/0.50          (sk_F @ sk_E @ (u1_struct_0 @ sk_C) @ sk_D @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.50           (u1_struct_0 @ sk_B)))
% 0.19/0.50          != (k1_funct_1 @ sk_E @ 
% 0.19/0.50              (sk_F @ sk_E @ (u1_struct_0 @ sk_C) @ sk_D @ 
% 0.19/0.50               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.19/0.50        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.19/0.50        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C) = (sk_E))
% 0.19/0.50        | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.19/0.50        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.19/0.50        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.19/0.50        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C) = (sk_E))
% 0.19/0.50        | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.19/0.50        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.50      inference('demod', [status(thm)],
% 0.19/0.50                ['51', '52', '53', '54', '55', '56', '57', '58', '59'])).
% 0.19/0.50  thf('61', plain,
% 0.19/0.50      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.19/0.50        | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.19/0.50        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C) = (sk_E))
% 0.19/0.50        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.19/0.50      inference('simplify', [status(thm)], ['60'])).
% 0.19/0.50  thf('62', plain,
% 0.19/0.50      (~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.50          (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C) @ sk_E)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('63', plain,
% 0.19/0.50      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_E @ 
% 0.19/0.50           sk_E)
% 0.19/0.50        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.19/0.50        | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.19/0.50        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['61', '62'])).
% 0.19/0.50  thf('64', plain,
% 0.19/0.50      ((m1_subset_1 @ sk_E @ 
% 0.19/0.50        (k1_zfmisc_1 @ 
% 0.19/0.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf(redefinition_r2_funct_2, axiom,
% 0.19/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.50     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.19/0.50         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.19/0.50         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.19/0.50         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.19/0.50       ( ( r2_funct_2 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.19/0.50  thf('65', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.50         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 0.19/0.50          | ~ (v1_funct_2 @ X0 @ X1 @ X2)
% 0.19/0.50          | ~ (v1_funct_1 @ X0)
% 0.19/0.50          | ~ (v1_funct_1 @ X3)
% 0.19/0.50          | ~ (v1_funct_2 @ X3 @ X1 @ X2)
% 0.19/0.50          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 0.19/0.50          | (r2_funct_2 @ X1 @ X2 @ X0 @ X3)
% 0.19/0.50          | ((X0) != (X3)))),
% 0.19/0.50      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 0.19/0.50  thf('66', plain,
% 0.19/0.50      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.50         ((r2_funct_2 @ X1 @ X2 @ X3 @ X3)
% 0.19/0.50          | ~ (v1_funct_1 @ X3)
% 0.19/0.50          | ~ (v1_funct_2 @ X3 @ X1 @ X2)
% 0.19/0.50          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2))))),
% 0.19/0.50      inference('simplify', [status(thm)], ['65'])).
% 0.19/0.50  thf('67', plain,
% 0.19/0.50      ((~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))
% 0.19/0.50        | ~ (v1_funct_1 @ sk_E)
% 0.19/0.50        | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_E @ 
% 0.19/0.50           sk_E))),
% 0.19/0.50      inference('sup-', [status(thm)], ['64', '66'])).
% 0.19/0.50  thf('68', plain,
% 0.19/0.50      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('69', plain, ((v1_funct_1 @ sk_E)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('70', plain,
% 0.19/0.50      ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_E @ sk_E)),
% 0.19/0.50      inference('demod', [status(thm)], ['67', '68', '69'])).
% 0.19/0.50  thf('71', plain,
% 0.19/0.50      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.19/0.50        | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.19/0.50        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.50      inference('demod', [status(thm)], ['63', '70'])).
% 0.19/0.50  thf(fc2_struct_0, axiom,
% 0.19/0.50    (![A:$i]:
% 0.19/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.19/0.50       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.19/0.50  thf('72', plain,
% 0.19/0.50      (![X12 : $i]:
% 0.19/0.50         (~ (v1_xboole_0 @ (u1_struct_0 @ X12))
% 0.19/0.50          | ~ (l1_struct_0 @ X12)
% 0.19/0.50          | (v2_struct_0 @ X12))),
% 0.19/0.50      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.19/0.50  thf('73', plain,
% 0.19/0.50      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.19/0.50        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.19/0.50        | (v2_struct_0 @ sk_A)
% 0.19/0.50        | ~ (l1_struct_0 @ sk_A))),
% 0.19/0.50      inference('sup-', [status(thm)], ['71', '72'])).
% 0.19/0.50  thf('74', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf(dt_l1_pre_topc, axiom,
% 0.19/0.50    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.19/0.50  thf('75', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.19/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.19/0.50  thf('76', plain, ((l1_struct_0 @ sk_A)),
% 0.19/0.50      inference('sup-', [status(thm)], ['74', '75'])).
% 0.19/0.50  thf('77', plain,
% 0.19/0.50      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.19/0.50        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.19/0.50        | (v2_struct_0 @ sk_A))),
% 0.19/0.50      inference('demod', [status(thm)], ['73', '76'])).
% 0.19/0.50  thf('78', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('79', plain,
% 0.19/0.50      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.19/0.50        | (v1_xboole_0 @ (u1_struct_0 @ sk_C)))),
% 0.19/0.50      inference('clc', [status(thm)], ['77', '78'])).
% 0.19/0.50  thf('80', plain,
% 0.19/0.50      (![X12 : $i]:
% 0.19/0.50         (~ (v1_xboole_0 @ (u1_struct_0 @ X12))
% 0.19/0.50          | ~ (l1_struct_0 @ X12)
% 0.19/0.50          | (v2_struct_0 @ X12))),
% 0.19/0.50      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.19/0.50  thf('81', plain,
% 0.19/0.50      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.19/0.50        | (v2_struct_0 @ sk_C)
% 0.19/0.50        | ~ (l1_struct_0 @ sk_C))),
% 0.19/0.50      inference('sup-', [status(thm)], ['79', '80'])).
% 0.19/0.50  thf('82', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf(dt_m1_pre_topc, axiom,
% 0.19/0.50    (![A:$i]:
% 0.19/0.50     ( ( l1_pre_topc @ A ) =>
% 0.19/0.50       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.19/0.50  thf('83', plain,
% 0.19/0.50      (![X10 : $i, X11 : $i]:
% 0.19/0.50         (~ (m1_pre_topc @ X10 @ X11)
% 0.19/0.50          | (l1_pre_topc @ X10)
% 0.19/0.50          | ~ (l1_pre_topc @ X11))),
% 0.19/0.50      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.19/0.50  thf('84', plain, ((~ (l1_pre_topc @ sk_B) | (l1_pre_topc @ sk_C))),
% 0.19/0.50      inference('sup-', [status(thm)], ['82', '83'])).
% 0.19/0.50  thf('85', plain, ((l1_pre_topc @ sk_B)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('86', plain, ((l1_pre_topc @ sk_C)),
% 0.19/0.50      inference('demod', [status(thm)], ['84', '85'])).
% 0.19/0.50  thf('87', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.19/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.19/0.50  thf('88', plain, ((l1_struct_0 @ sk_C)),
% 0.19/0.50      inference('sup-', [status(thm)], ['86', '87'])).
% 0.19/0.50  thf('89', plain,
% 0.19/0.50      (((v1_xboole_0 @ (u1_struct_0 @ sk_B)) | (v2_struct_0 @ sk_C))),
% 0.19/0.50      inference('demod', [status(thm)], ['81', '88'])).
% 0.19/0.50  thf('90', plain, (~ (v2_struct_0 @ sk_C)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('91', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_B))),
% 0.19/0.50      inference('clc', [status(thm)], ['89', '90'])).
% 0.19/0.50  thf('92', plain,
% 0.19/0.50      (![X12 : $i]:
% 0.19/0.50         (~ (v1_xboole_0 @ (u1_struct_0 @ X12))
% 0.19/0.50          | ~ (l1_struct_0 @ X12)
% 0.19/0.50          | (v2_struct_0 @ X12))),
% 0.19/0.50      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.19/0.50  thf('93', plain, (((v2_struct_0 @ sk_B) | ~ (l1_struct_0 @ sk_B))),
% 0.19/0.50      inference('sup-', [status(thm)], ['91', '92'])).
% 0.19/0.50  thf('94', plain, ((l1_pre_topc @ sk_B)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('95', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.19/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.19/0.50  thf('96', plain, ((l1_struct_0 @ sk_B)),
% 0.19/0.50      inference('sup-', [status(thm)], ['94', '95'])).
% 0.19/0.50  thf('97', plain, ((v2_struct_0 @ sk_B)),
% 0.19/0.50      inference('demod', [status(thm)], ['93', '96'])).
% 0.19/0.50  thf('98', plain, ($false), inference('demod', [status(thm)], ['0', '97'])).
% 0.19/0.50  
% 0.19/0.50  % SZS output end Refutation
% 0.19/0.50  
% 0.19/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
