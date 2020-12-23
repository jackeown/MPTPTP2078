%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uEdyBweq8Q

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:12 EST 2020

% Result     : Theorem 11.35s
% Output     : Refutation 11.35s
% Verified   : 
% Statistics : Number of formulae       :  395 (4602 expanded)
%              Number of leaves         :   35 (1343 expanded)
%              Depth                    :   32
%              Number of atoms          : 5424 (188463 expanded)
%              Number of equality atoms :   69 (2846 expanded)
%              Maximal formula depth    :   26 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

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
    ! [X30: $i] :
      ( ( m1_pre_topc @ X30 @ X30 )
      | ~ ( l1_pre_topc @ X30 ) ) ),
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
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( v2_struct_0 @ X37 )
      | ~ ( v2_pre_topc @ X37 )
      | ~ ( l1_pre_topc @ X37 )
      | ( v2_struct_0 @ X38 )
      | ~ ( m1_pre_topc @ X38 @ X39 )
      | ~ ( m1_pre_topc @ X38 @ X40 )
      | ~ ( m1_pre_topc @ X41 @ X38 )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( v1_funct_2 @ X42 @ ( u1_struct_0 @ X40 ) @ ( u1_struct_0 @ X37 ) )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X40 ) @ ( u1_struct_0 @ X37 ) ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X41 ) @ ( u1_struct_0 @ X37 ) @ ( k3_tmap_1 @ X39 @ X37 @ X38 @ X41 @ ( k3_tmap_1 @ X39 @ X37 @ X40 @ X38 @ X42 ) ) @ ( k3_tmap_1 @ X39 @ X37 @ X40 @ X41 @ X42 ) )
      | ~ ( m1_pre_topc @ X41 @ X39 )
      | ( v2_struct_0 @ X41 )
      | ~ ( m1_pre_topc @ X40 @ X39 )
      | ( v2_struct_0 @ X40 )
      | ~ ( l1_pre_topc @ X39 )
      | ~ ( v2_pre_topc @ X39 )
      | ( v2_struct_0 @ X39 ) ) ),
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
    ! [X30: $i] :
      ( ( m1_pre_topc @ X30 @ X30 )
      | ~ ( l1_pre_topc @ X30 ) ) ),
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
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( v2_struct_0 @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( m1_pre_topc @ X17 @ X18 )
      | ~ ( m1_pre_topc @ X17 @ X19 )
      | ( ( k3_tmap_1 @ X18 @ X16 @ X19 @ X17 @ X20 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X16 ) @ X20 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X16 ) ) ) )
      | ~ ( v1_funct_2 @ X20 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X16 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( m1_pre_topc @ X19 @ X18 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
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
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( v2_struct_0 @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( m1_pre_topc @ X13 @ X14 )
      | ( ( k2_tmap_1 @ X14 @ X12 @ X15 @ X13 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X12 ) @ X15 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X12 ) ) ) )
      | ~ ( v1_funct_2 @ X15 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X12 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
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
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X30: $i] :
      ( ( m1_pre_topc @ X30 @ X30 )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('78',plain,(
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

thf('79',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_pre_topc @ X25 @ X26 )
      | ~ ( m1_pre_topc @ X27 @ X26 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_2 @ X29 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X28 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X28 ) ) ) )
      | ( m1_subset_1 @ ( k3_tmap_1 @ X26 @ X28 @ X27 @ X25 @ X29 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X28 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_tmap_1])).

thf('80',plain,(
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
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_A @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['80','81','82','83','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['77','85'])).

thf('87',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['86','87','88','89'])).

thf('91',plain,
    ( ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['76','90'])).

thf('92',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ),
    inference('sup+',[status(thm)],['65','72'])).

thf('93',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['93','94'])).

thf('96',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( v2_struct_0 @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( m1_pre_topc @ X17 @ X18 )
      | ~ ( m1_pre_topc @ X17 @ X19 )
      | ( ( k3_tmap_1 @ X18 @ X16 @ X19 @ X17 @ X20 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X16 ) @ X20 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X16 ) ) ) )
      | ~ ( v1_funct_2 @ X20 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X16 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( m1_pre_topc @ X19 @ X18 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d5_tmap_1])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    ! [X30: $i] :
      ( ( m1_pre_topc @ X30 @ X30 )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('102',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_pre_topc @ X25 @ X26 )
      | ~ ( m1_pre_topc @ X27 @ X26 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_2 @ X29 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X28 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X28 ) ) ) )
      | ( v1_funct_1 @ ( k3_tmap_1 @ X26 @ X28 @ X27 @ X25 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_tmap_1])).

thf('104',plain,(
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
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_A @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['104','105','106','107','108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['101','109'])).

thf('111',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['110','111','112','113'])).

thf('115',plain,
    ( ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['100','114'])).

thf('116',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ),
    inference('sup+',[status(thm)],['65','72'])).

thf('117',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) ),
    inference(clc,[status(thm)],['117','118'])).

thf('120',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ),
    inference(clc,[status(thm)],['119','120'])).

thf('122',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    ! [X30: $i] :
      ( ( m1_pre_topc @ X30 @ X30 )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('124',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_pre_topc @ X25 @ X26 )
      | ~ ( m1_pre_topc @ X27 @ X26 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_2 @ X29 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X28 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X28 ) ) ) )
      | ( v1_funct_2 @ ( k3_tmap_1 @ X26 @ X28 @ X27 @ X25 @ X29 ) @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_tmap_1])).

thf('126',plain,(
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
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_A @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['126','127','128','129','130'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['123','131'])).

thf('133',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['132','133','134','135'])).

thf('137',plain,
    ( ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['122','136'])).

thf('138',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ),
    inference('sup+',[status(thm)],['65','72'])).

thf('139',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['137','138'])).

thf('140',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['139','140'])).

thf('142',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['141','142'])).

thf('144',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['99','121','143','144','145'])).

thf('147',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['75','146'])).

thf('148',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['147','148','149'])).

thf('151',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['74','150'])).

thf('152',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['95','96'])).

thf('154',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( v2_struct_0 @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( m1_pre_topc @ X13 @ X14 )
      | ( ( k2_tmap_1 @ X14 @ X12 @ X15 @ X13 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X12 ) @ X15 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X12 ) ) ) )
      | ~ ( v1_funct_2 @ X15 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X12 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('155',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('157',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_pre_topc @ X4 @ X5 )
      | ( v2_pre_topc @ X4 )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('158',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['156','157'])).

thf('159',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['158','159','160'])).

thf('162',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('163',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_pre_topc @ X7 @ X8 )
      | ( l1_pre_topc @ X7 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('164',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['162','163'])).

thf('165',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['164','165'])).

thf('167',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ),
    inference(clc,[status(thm)],['119','120'])).

thf('168',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['141','142'])).

thf('169',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['155','161','166','167','168','169','170'])).

thf('172',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['152','171'])).

thf('173',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['172','173'])).

thf('175',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ sk_C )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['174','175'])).

thf('177',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) )
      = ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['151','176','177'])).

thf('179',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) )
      = ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ sk_C ) ) ),
    inference(clc,[status(thm)],['178','179'])).

thf('181',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) )
    = ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ sk_C ) ),
    inference(clc,[status(thm)],['180','181'])).

thf('183',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ sk_C ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['58','73','182','183'])).

thf('185',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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

thf('186',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X23 ) ) ) )
      | ~ ( v1_funct_2 @ X21 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X23 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( l1_struct_0 @ X23 )
      | ~ ( l1_struct_0 @ X22 )
      | ~ ( l1_struct_0 @ X24 )
      | ( v1_funct_1 @ ( k2_tmap_1 @ X22 @ X23 @ X21 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tmap_1])).

thf('187',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['185','186'])).

thf('188',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('189',plain,(
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('190',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['188','189'])).

thf('191',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,(
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('193',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['191','192'])).

thf('194',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['187','190','193','194','195'])).

thf('197',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X23 ) ) ) )
      | ~ ( v1_funct_2 @ X21 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X23 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( l1_struct_0 @ X23 )
      | ~ ( l1_struct_0 @ X22 )
      | ~ ( l1_struct_0 @ X24 )
      | ( v1_funct_2 @ ( k2_tmap_1 @ X22 @ X23 @ X21 @ X24 ) @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tmap_1])).

thf('199',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['197','198'])).

thf('200',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['188','189'])).

thf('201',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['191','192'])).

thf('202',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('203',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['199','200','201','202','203'])).

thf('205',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X23 ) ) ) )
      | ~ ( v1_funct_2 @ X21 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X23 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( l1_struct_0 @ X23 )
      | ~ ( l1_struct_0 @ X22 )
      | ~ ( l1_struct_0 @ X24 )
      | ( m1_subset_1 @ ( k2_tmap_1 @ X22 @ X23 @ X21 @ X24 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X23 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tmap_1])).

thf('207',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['205','206'])).

thf('208',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['188','189'])).

thf('209',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['191','192'])).

thf('210',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('211',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('212',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['207','208','209','210','211'])).

thf('213',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X23 ) ) ) )
      | ~ ( v1_funct_2 @ X21 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X23 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( l1_struct_0 @ X23 )
      | ~ ( l1_struct_0 @ X22 )
      | ~ ( l1_struct_0 @ X24 )
      | ( m1_subset_1 @ ( k2_tmap_1 @ X22 @ X23 @ X21 @ X24 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X23 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tmap_1])).

thf('214',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( k2_tmap_1 @ X0 @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['212','213'])).

thf('215',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['191','192'])).

thf('216',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( k2_tmap_1 @ X0 @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['214','215'])).

thf('217',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( l1_struct_0 @ X1 )
      | ( m1_subset_1 @ ( k2_tmap_1 @ X0 @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['216'])).

thf('218',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( k2_tmap_1 @ X0 @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X1 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['204','217'])).

thf('219',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( l1_struct_0 @ X1 )
      | ( m1_subset_1 @ ( k2_tmap_1 @ X0 @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['218'])).

thf('220',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( k2_tmap_1 @ X0 @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['196','219'])).

thf('221',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X1 )
      | ( m1_subset_1 @ ( k2_tmap_1 @ X0 @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['220'])).

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

thf('222',plain,(
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

thf('223',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ X1 @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1 ) @ X0 ) @ X2 )
      | ( ( k2_tmap_1 @ X1 @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1 ) @ X0 )
        = X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ X1 @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1 ) @ X0 ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ X1 @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1 ) @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['221','222'])).

thf('224',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ sk_C )
      = ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_C )
    | ~ ( l1_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['184','223'])).

thf('225',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('226',plain,(
    ! [X30: $i] :
      ( ( m1_pre_topc @ X30 @ X30 )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('227',plain,(
    m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['95','96'])).

thf('228',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_pre_topc @ X25 @ X26 )
      | ~ ( m1_pre_topc @ X27 @ X26 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_2 @ X29 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X28 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X28 ) ) ) )
      | ( v1_funct_2 @ ( k3_tmap_1 @ X26 @ X28 @ X27 @ X25 @ X29 ) @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_tmap_1])).

thf('229',plain,(
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
    inference('sup-',[status(thm)],['227','228'])).

thf('230',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['141','142'])).

thf('231',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ),
    inference(clc,[status(thm)],['119','120'])).

thf('232',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('233',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('234',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['229','230','231','232','233'])).

thf('235',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_D )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ( v2_struct_0 @ sk_D )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['226','234'])).

thf('236',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['164','165'])).

thf('237',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['164','165'])).

thf('238',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['158','159','160'])).

thf('239',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['235','236','237','238'])).

thf('240',plain,
    ( ( v1_funct_2 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['225','239'])).

thf('241',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('242',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v1_funct_2 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['240','241'])).

thf('243',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('244',plain,(
    v1_funct_2 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['242','243'])).

thf('245',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('246',plain,(
    ! [X30: $i] :
      ( ( m1_pre_topc @ X30 @ X30 )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('247',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['99','121','143','144','145'])).

thf('248',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['246','247'])).

thf('249',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['164','165'])).

thf('250',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['164','165'])).

thf('251',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['158','159','160'])).

thf('252',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['248','249','250','251'])).

thf('253',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['252'])).

thf('254',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['245','253'])).

thf('255',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('256',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['254','255'])).

thf('257',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('258',plain,
    ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['256','257'])).

thf('259',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ sk_C )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['174','175'])).

thf('260',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ sk_C )
    = ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) ),
    inference('sup+',[status(thm)],['258','259'])).

thf('261',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['244','260'])).

thf('262',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('263',plain,(
    ! [X30: $i] :
      ( ( m1_pre_topc @ X30 @ X30 )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('264',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['141','142'])).

thf('265',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['207','208','209','210','211'])).

thf('266',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_pre_topc @ X25 @ X26 )
      | ~ ( m1_pre_topc @ X27 @ X26 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_2 @ X29 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X28 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X28 ) ) ) )
      | ( v1_funct_1 @ ( k3_tmap_1 @ X26 @ X28 @ X27 @ X25 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_tmap_1])).

thf('267',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v1_funct_1 @ ( k3_tmap_1 @ X2 @ sk_B @ X0 @ X1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ( v2_struct_0 @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X2 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ X2 )
      | ~ ( m1_pre_topc @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['265','266'])).

thf('268',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('269',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('270',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v1_funct_1 @ ( k3_tmap_1 @ X2 @ sk_B @ X0 @ X1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ( v2_struct_0 @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X2 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ X2 )
      | ~ ( m1_pre_topc @ X1 @ X2 ) ) ),
    inference(demod,[status(thm)],['267','268','269'])).

thf('271',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) )
      | ( v1_funct_1 @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) )
      | ~ ( l1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['264','270'])).

thf('272',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ),
    inference(clc,[status(thm)],['119','120'])).

thf('273',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['164','165'])).

thf('274',plain,(
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('275',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['273','274'])).

thf('276',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_funct_1 @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) ) ) ),
    inference(demod,[status(thm)],['271','272','275'])).

thf('277',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_D )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) )
      | ( v2_struct_0 @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ~ ( l1_pre_topc @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['263','276'])).

thf('278',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['164','165'])).

thf('279',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['158','159','160'])).

thf('280',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['164','165'])).

thf('281',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['277','278','279','280'])).

thf('282',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v1_funct_1 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['262','281'])).

thf('283',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('284',plain,
    ( ( v1_funct_1 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference(clc,[status(thm)],['282','283'])).

thf('285',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('286',plain,(
    v1_funct_1 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) ),
    inference(clc,[status(thm)],['284','285'])).

thf('287',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ sk_C )
    = ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) ),
    inference('sup+',[status(thm)],['258','259'])).

thf('288',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ sk_C ) ),
    inference(demod,[status(thm)],['286','287'])).

thf('289',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('290',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['110','111','112','113'])).

thf('291',plain,
    ( ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['289','290'])).

thf('292',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference('sup+',[status(thm)],['39','55'])).

thf('293',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['291','292'])).

thf('294',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('295',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) ) ),
    inference(clc,[status(thm)],['293','294'])).

thf('296',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('297',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) ),
    inference(clc,[status(thm)],['295','296'])).

thf('298',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('299',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['132','133','134','135'])).

thf('300',plain,
    ( ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['298','299'])).

thf('301',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference('sup+',[status(thm)],['39','55'])).

thf('302',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['300','301'])).

thf('303',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('304',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['302','303'])).

thf('305',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('306',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['304','305'])).

thf('307',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('308',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['86','87','88','89'])).

thf('309',plain,
    ( ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['307','308'])).

thf('310',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference('sup+',[status(thm)],['39','55'])).

thf('311',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['309','310'])).

thf('312',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('313',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['311','312'])).

thf('314',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('315',plain,(
    m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['313','314'])).

thf('316',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('317',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_pre_topc @ X7 @ X8 )
      | ( l1_pre_topc @ X7 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('318',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['316','317'])).

thf('319',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('320',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['318','319'])).

thf('321',plain,(
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('322',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['320','321'])).

thf('323',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['273','274'])).

thf('324',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ sk_C )
      = ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) ) ),
    inference(demod,[status(thm)],['224','261','288','297','306','315','322','323'])).

thf('325',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('326',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('327',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['325','326'])).

thf('328',plain,(
    r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('329',plain,(
    m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['95','96'])).

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

thf('330',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( v2_struct_0 @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ~ ( l1_pre_topc @ X31 )
      | ( v2_struct_0 @ X32 )
      | ~ ( m1_pre_topc @ X32 @ X31 )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X32 ) )
      | ( r1_tmap_1 @ X32 @ X34 @ ( k2_tmap_1 @ X31 @ X34 @ X35 @ X32 ) @ X33 )
      | ( X36 != X33 )
      | ~ ( r1_tmap_1 @ X31 @ X34 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ X31 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X34 ) ) ) )
      | ~ ( v1_funct_2 @ X35 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X34 ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( l1_pre_topc @ X34 )
      | ~ ( v2_pre_topc @ X34 )
      | ( v2_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t64_tmap_1])).

thf('331',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( v2_struct_0 @ X34 )
      | ~ ( v2_pre_topc @ X34 )
      | ~ ( l1_pre_topc @ X34 )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_funct_2 @ X35 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X34 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X34 ) ) ) )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X31 ) )
      | ~ ( r1_tmap_1 @ X31 @ X34 @ X35 @ X33 )
      | ( r1_tmap_1 @ X32 @ X34 @ ( k2_tmap_1 @ X31 @ X34 @ X35 @ X32 ) @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X32 ) )
      | ~ ( m1_pre_topc @ X32 @ X31 )
      | ( v2_struct_0 @ X32 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(simplify,[status(thm)],['330'])).

thf('332',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ~ ( l1_pre_topc @ sk_D )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ sk_B @ ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ X0 ) @ X1 )
      | ~ ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['329','331'])).

thf('333',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['158','159','160'])).

thf('334',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['164','165'])).

thf('335',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['141','142'])).

thf('336',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ),
    inference(clc,[status(thm)],['119','120'])).

thf('337',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('338',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('339',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ sk_B @ ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ X0 ) @ X1 )
      | ~ ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_D ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['332','333','334','335','336','337','338'])).

thf('340',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) )
      | ( r1_tmap_1 @ X0 @ sk_B @ ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ X0 ) @ sk_F )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['328','339'])).

thf('341',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('342',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r1_tmap_1 @ X0 @ sk_B @ ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ X0 ) @ sk_F )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['340','341'])).

thf('343',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ~ ( m1_pre_topc @ sk_C @ sk_D )
    | ( r1_tmap_1 @ sk_C @ sk_B @ ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ sk_C ) @ sk_F )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['327','342'])).

thf('344',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('345',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_C @ sk_B @ ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ sk_C ) @ sk_F )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['343','344'])).

thf('346',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup+',[status(thm)],['324','345'])).

thf('347',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_C @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F ) ),
    inference(simplify,[status(thm)],['346'])).

thf('348',plain,(
    ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('349',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('350',plain,(
    ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F ) ),
    inference(demod,[status(thm)],['348','349'])).

thf('351',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['347','350'])).

thf('352',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('353',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['351','352'])).

thf('354',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('355',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['353','354'])).

thf('356',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('357',plain,(
    v2_struct_0 @ sk_C ),
    inference(clc,[status(thm)],['355','356'])).

thf('358',plain,(
    $false ),
    inference(demod,[status(thm)],['0','357'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uEdyBweq8Q
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:16:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.20/0.36  % Python version: Python 3.6.8
% 0.20/0.36  % Running in FO mode
% 11.35/11.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 11.35/11.60  % Solved by: fo/fo7.sh
% 11.35/11.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 11.35/11.60  % done 11120 iterations in 11.127s
% 11.35/11.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 11.35/11.60  % SZS output start Refutation
% 11.35/11.60  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 11.35/11.60  thf(sk_D_type, type, sk_D: $i).
% 11.35/11.60  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 11.35/11.60  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 11.35/11.60  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 11.35/11.60  thf(sk_B_type, type, sk_B: $i).
% 11.35/11.60  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 11.35/11.60  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 11.35/11.60  thf(sk_F_type, type, sk_F: $i).
% 11.35/11.60  thf(sk_C_type, type, sk_C: $i).
% 11.35/11.60  thf(sk_E_type, type, sk_E: $i).
% 11.35/11.60  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 11.35/11.60  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 11.35/11.60  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 11.35/11.60  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 11.35/11.60  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 11.35/11.60  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 11.35/11.60  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 11.35/11.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 11.35/11.60  thf(sk_A_type, type, sk_A: $i).
% 11.35/11.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 11.35/11.60  thf(sk_G_type, type, sk_G: $i).
% 11.35/11.60  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 11.35/11.60  thf(t82_tmap_1, conjecture,
% 11.35/11.60    (![A:$i]:
% 11.35/11.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 11.35/11.60       ( ![B:$i]:
% 11.35/11.60         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 11.35/11.60             ( l1_pre_topc @ B ) ) =>
% 11.35/11.60           ( ![C:$i]:
% 11.35/11.60             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 11.35/11.60               ( ![D:$i]:
% 11.35/11.60                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 11.35/11.60                   ( ![E:$i]:
% 11.35/11.60                     ( ( ( v1_funct_1 @ E ) & 
% 11.35/11.60                         ( v1_funct_2 @
% 11.35/11.60                           E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 11.35/11.60                         ( m1_subset_1 @
% 11.35/11.60                           E @ 
% 11.35/11.60                           ( k1_zfmisc_1 @
% 11.35/11.60                             ( k2_zfmisc_1 @
% 11.35/11.60                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 11.35/11.60                       ( ( m1_pre_topc @ C @ D ) =>
% 11.35/11.60                         ( ![F:$i]:
% 11.35/11.60                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 11.35/11.60                             ( ![G:$i]:
% 11.35/11.60                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 11.35/11.60                                 ( ( ( ( F ) = ( G ) ) & 
% 11.35/11.60                                     ( r1_tmap_1 @
% 11.35/11.60                                       D @ B @ ( k2_tmap_1 @ A @ B @ E @ D ) @ 
% 11.35/11.60                                       F ) ) =>
% 11.35/11.60                                   ( r1_tmap_1 @
% 11.35/11.60                                     C @ B @ ( k2_tmap_1 @ A @ B @ E @ C ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 11.35/11.60  thf(zf_stmt_0, negated_conjecture,
% 11.35/11.60    (~( ![A:$i]:
% 11.35/11.60        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 11.35/11.60            ( l1_pre_topc @ A ) ) =>
% 11.35/11.60          ( ![B:$i]:
% 11.35/11.60            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 11.35/11.60                ( l1_pre_topc @ B ) ) =>
% 11.35/11.60              ( ![C:$i]:
% 11.35/11.60                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 11.35/11.60                  ( ![D:$i]:
% 11.35/11.60                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 11.35/11.60                      ( ![E:$i]:
% 11.35/11.60                        ( ( ( v1_funct_1 @ E ) & 
% 11.35/11.60                            ( v1_funct_2 @
% 11.35/11.60                              E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 11.35/11.60                            ( m1_subset_1 @
% 11.35/11.60                              E @ 
% 11.35/11.60                              ( k1_zfmisc_1 @
% 11.35/11.60                                ( k2_zfmisc_1 @
% 11.35/11.60                                  ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 11.35/11.60                          ( ( m1_pre_topc @ C @ D ) =>
% 11.35/11.60                            ( ![F:$i]:
% 11.35/11.60                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 11.35/11.60                                ( ![G:$i]:
% 11.35/11.60                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 11.35/11.60                                    ( ( ( ( F ) = ( G ) ) & 
% 11.35/11.60                                        ( r1_tmap_1 @
% 11.35/11.60                                          D @ B @ 
% 11.35/11.60                                          ( k2_tmap_1 @ A @ B @ E @ D ) @ F ) ) =>
% 11.35/11.60                                      ( r1_tmap_1 @
% 11.35/11.60                                        C @ B @ 
% 11.35/11.60                                        ( k2_tmap_1 @ A @ B @ E @ C ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 11.35/11.60    inference('cnf.neg', [status(esa)], [t82_tmap_1])).
% 11.35/11.60  thf('0', plain, (~ (v2_struct_0 @ sk_C)),
% 11.35/11.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.60  thf('1', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 11.35/11.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.60  thf('2', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 11.35/11.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.60  thf(t2_tsep_1, axiom,
% 11.35/11.60    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 11.35/11.60  thf('3', plain,
% 11.35/11.60      (![X30 : $i]: ((m1_pre_topc @ X30 @ X30) | ~ (l1_pre_topc @ X30))),
% 11.35/11.60      inference('cnf', [status(esa)], [t2_tsep_1])).
% 11.35/11.60  thf('4', plain,
% 11.35/11.60      ((m1_subset_1 @ sk_E @ 
% 11.35/11.60        (k1_zfmisc_1 @ 
% 11.35/11.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 11.35/11.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.60  thf(t79_tmap_1, axiom,
% 11.35/11.60    (![A:$i]:
% 11.35/11.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 11.35/11.60       ( ![B:$i]:
% 11.35/11.60         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 11.35/11.60             ( l1_pre_topc @ B ) ) =>
% 11.35/11.60           ( ![C:$i]:
% 11.35/11.60             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 11.35/11.60               ( ![D:$i]:
% 11.35/11.60                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 11.35/11.60                   ( ![E:$i]:
% 11.35/11.60                     ( ( ( ~( v2_struct_0 @ E ) ) & ( m1_pre_topc @ E @ A ) ) =>
% 11.35/11.60                       ( ( ( m1_pre_topc @ D @ C ) & ( m1_pre_topc @ E @ D ) ) =>
% 11.35/11.60                         ( ![F:$i]:
% 11.35/11.60                           ( ( ( v1_funct_1 @ F ) & 
% 11.35/11.60                               ( v1_funct_2 @
% 11.35/11.60                                 F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 11.35/11.60                               ( m1_subset_1 @
% 11.35/11.60                                 F @ 
% 11.35/11.60                                 ( k1_zfmisc_1 @
% 11.35/11.60                                   ( k2_zfmisc_1 @
% 11.35/11.60                                     ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 11.35/11.60                             ( r2_funct_2 @
% 11.35/11.60                               ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) @ 
% 11.35/11.60                               ( k3_tmap_1 @
% 11.35/11.60                                 A @ B @ D @ E @ 
% 11.35/11.60                                 ( k3_tmap_1 @ A @ B @ C @ D @ F ) ) @ 
% 11.35/11.60                               ( k3_tmap_1 @ A @ B @ C @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 11.35/11.60  thf('5', plain,
% 11.35/11.60      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 11.35/11.60         ((v2_struct_0 @ X37)
% 11.35/11.60          | ~ (v2_pre_topc @ X37)
% 11.35/11.60          | ~ (l1_pre_topc @ X37)
% 11.35/11.60          | (v2_struct_0 @ X38)
% 11.35/11.60          | ~ (m1_pre_topc @ X38 @ X39)
% 11.35/11.60          | ~ (m1_pre_topc @ X38 @ X40)
% 11.35/11.60          | ~ (m1_pre_topc @ X41 @ X38)
% 11.35/11.60          | ~ (v1_funct_1 @ X42)
% 11.35/11.60          | ~ (v1_funct_2 @ X42 @ (u1_struct_0 @ X40) @ (u1_struct_0 @ X37))
% 11.35/11.60          | ~ (m1_subset_1 @ X42 @ 
% 11.35/11.60               (k1_zfmisc_1 @ 
% 11.35/11.60                (k2_zfmisc_1 @ (u1_struct_0 @ X40) @ (u1_struct_0 @ X37))))
% 11.35/11.60          | (r2_funct_2 @ (u1_struct_0 @ X41) @ (u1_struct_0 @ X37) @ 
% 11.35/11.60             (k3_tmap_1 @ X39 @ X37 @ X38 @ X41 @ 
% 11.35/11.60              (k3_tmap_1 @ X39 @ X37 @ X40 @ X38 @ X42)) @ 
% 11.35/11.60             (k3_tmap_1 @ X39 @ X37 @ X40 @ X41 @ X42))
% 11.35/11.60          | ~ (m1_pre_topc @ X41 @ X39)
% 11.35/11.60          | (v2_struct_0 @ X41)
% 11.35/11.60          | ~ (m1_pre_topc @ X40 @ X39)
% 11.35/11.60          | (v2_struct_0 @ X40)
% 11.35/11.60          | ~ (l1_pre_topc @ X39)
% 11.35/11.60          | ~ (v2_pre_topc @ X39)
% 11.35/11.60          | (v2_struct_0 @ X39))),
% 11.35/11.60      inference('cnf', [status(esa)], [t79_tmap_1])).
% 11.35/11.60  thf('6', plain,
% 11.35/11.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.35/11.60         ((v2_struct_0 @ X0)
% 11.35/11.60          | ~ (v2_pre_topc @ X0)
% 11.35/11.60          | ~ (l1_pre_topc @ X0)
% 11.35/11.60          | (v2_struct_0 @ sk_A)
% 11.35/11.60          | ~ (m1_pre_topc @ sk_A @ X0)
% 11.35/11.60          | (v2_struct_0 @ X1)
% 11.35/11.60          | ~ (m1_pre_topc @ X1 @ X0)
% 11.35/11.60          | (r2_funct_2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B) @ 
% 11.35/11.60             (k3_tmap_1 @ X0 @ sk_B @ X2 @ X1 @ 
% 11.35/11.60              (k3_tmap_1 @ X0 @ sk_B @ sk_A @ X2 @ sk_E)) @ 
% 11.35/11.60             (k3_tmap_1 @ X0 @ sk_B @ sk_A @ X1 @ sk_E))
% 11.35/11.60          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 11.35/11.60          | ~ (v1_funct_1 @ sk_E)
% 11.35/11.60          | ~ (m1_pre_topc @ X1 @ X2)
% 11.35/11.60          | ~ (m1_pre_topc @ X2 @ sk_A)
% 11.35/11.60          | ~ (m1_pre_topc @ X2 @ X0)
% 11.35/11.60          | (v2_struct_0 @ X2)
% 11.35/11.60          | ~ (l1_pre_topc @ sk_B)
% 11.35/11.60          | ~ (v2_pre_topc @ sk_B)
% 11.35/11.60          | (v2_struct_0 @ sk_B))),
% 11.35/11.60      inference('sup-', [status(thm)], ['4', '5'])).
% 11.35/11.60  thf('7', plain,
% 11.35/11.60      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 11.35/11.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.60  thf('8', plain, ((v1_funct_1 @ sk_E)),
% 11.35/11.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.60  thf('9', plain, ((l1_pre_topc @ sk_B)),
% 11.35/11.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.60  thf('10', plain, ((v2_pre_topc @ sk_B)),
% 11.35/11.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.60  thf('11', plain,
% 11.35/11.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.35/11.60         ((v2_struct_0 @ X0)
% 11.35/11.60          | ~ (v2_pre_topc @ X0)
% 11.35/11.60          | ~ (l1_pre_topc @ X0)
% 11.35/11.60          | (v2_struct_0 @ sk_A)
% 11.35/11.60          | ~ (m1_pre_topc @ sk_A @ X0)
% 11.35/11.60          | (v2_struct_0 @ X1)
% 11.35/11.60          | ~ (m1_pre_topc @ X1 @ X0)
% 11.35/11.60          | (r2_funct_2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B) @ 
% 11.35/11.60             (k3_tmap_1 @ X0 @ sk_B @ X2 @ X1 @ 
% 11.35/11.60              (k3_tmap_1 @ X0 @ sk_B @ sk_A @ X2 @ sk_E)) @ 
% 11.35/11.60             (k3_tmap_1 @ X0 @ sk_B @ sk_A @ X1 @ sk_E))
% 11.35/11.60          | ~ (m1_pre_topc @ X1 @ X2)
% 11.35/11.60          | ~ (m1_pre_topc @ X2 @ sk_A)
% 11.35/11.60          | ~ (m1_pre_topc @ X2 @ X0)
% 11.35/11.60          | (v2_struct_0 @ X2)
% 11.35/11.60          | (v2_struct_0 @ sk_B))),
% 11.35/11.60      inference('demod', [status(thm)], ['6', '7', '8', '9', '10'])).
% 11.35/11.60  thf('12', plain,
% 11.35/11.60      (![X0 : $i, X1 : $i]:
% 11.35/11.60         (~ (l1_pre_topc @ sk_A)
% 11.35/11.60          | (v2_struct_0 @ sk_B)
% 11.35/11.60          | (v2_struct_0 @ X0)
% 11.35/11.60          | ~ (m1_pre_topc @ X0 @ sk_A)
% 11.35/11.60          | ~ (m1_pre_topc @ X0 @ sk_A)
% 11.35/11.60          | ~ (m1_pre_topc @ X1 @ X0)
% 11.35/11.60          | (r2_funct_2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B) @ 
% 11.35/11.60             (k3_tmap_1 @ sk_A @ sk_B @ X0 @ X1 @ 
% 11.35/11.60              (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E)) @ 
% 11.35/11.60             (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X1 @ sk_E))
% 11.35/11.60          | ~ (m1_pre_topc @ X1 @ sk_A)
% 11.35/11.60          | (v2_struct_0 @ X1)
% 11.35/11.60          | (v2_struct_0 @ sk_A)
% 11.35/11.60          | ~ (l1_pre_topc @ sk_A)
% 11.35/11.60          | ~ (v2_pre_topc @ sk_A)
% 11.35/11.60          | (v2_struct_0 @ sk_A))),
% 11.35/11.60      inference('sup-', [status(thm)], ['3', '11'])).
% 11.35/11.60  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 11.35/11.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.60  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 11.35/11.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.60  thf('15', plain, ((v2_pre_topc @ sk_A)),
% 11.35/11.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.60  thf('16', plain,
% 11.35/11.60      (![X0 : $i, X1 : $i]:
% 11.35/11.60         ((v2_struct_0 @ sk_B)
% 11.35/11.60          | (v2_struct_0 @ X0)
% 11.35/11.60          | ~ (m1_pre_topc @ X0 @ sk_A)
% 11.35/11.60          | ~ (m1_pre_topc @ X0 @ sk_A)
% 11.35/11.60          | ~ (m1_pre_topc @ X1 @ X0)
% 11.35/11.60          | (r2_funct_2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B) @ 
% 11.35/11.60             (k3_tmap_1 @ sk_A @ sk_B @ X0 @ X1 @ 
% 11.35/11.60              (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E)) @ 
% 11.35/11.60             (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X1 @ sk_E))
% 11.35/11.60          | ~ (m1_pre_topc @ X1 @ sk_A)
% 11.35/11.60          | (v2_struct_0 @ X1)
% 11.35/11.60          | (v2_struct_0 @ sk_A)
% 11.35/11.60          | (v2_struct_0 @ sk_A))),
% 11.35/11.60      inference('demod', [status(thm)], ['12', '13', '14', '15'])).
% 11.35/11.60  thf('17', plain,
% 11.35/11.60      (![X0 : $i, X1 : $i]:
% 11.35/11.60         ((v2_struct_0 @ sk_A)
% 11.35/11.60          | (v2_struct_0 @ X1)
% 11.35/11.60          | ~ (m1_pre_topc @ X1 @ sk_A)
% 11.35/11.60          | (r2_funct_2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B) @ 
% 11.35/11.60             (k3_tmap_1 @ sk_A @ sk_B @ X0 @ X1 @ 
% 11.35/11.60              (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E)) @ 
% 11.35/11.60             (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X1 @ sk_E))
% 11.35/11.60          | ~ (m1_pre_topc @ X1 @ X0)
% 11.35/11.60          | ~ (m1_pre_topc @ X0 @ sk_A)
% 11.35/11.60          | (v2_struct_0 @ X0)
% 11.35/11.60          | (v2_struct_0 @ sk_B))),
% 11.35/11.60      inference('simplify', [status(thm)], ['16'])).
% 11.35/11.60  thf('18', plain,
% 11.35/11.60      (![X0 : $i]:
% 11.35/11.60         ((v2_struct_0 @ sk_B)
% 11.35/11.60          | (v2_struct_0 @ X0)
% 11.35/11.60          | ~ (m1_pre_topc @ X0 @ sk_A)
% 11.35/11.60          | ~ (m1_pre_topc @ sk_C @ X0)
% 11.35/11.60          | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 11.35/11.60             (k3_tmap_1 @ sk_A @ sk_B @ X0 @ sk_C @ 
% 11.35/11.60              (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E)) @ 
% 11.35/11.60             (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E))
% 11.35/11.60          | (v2_struct_0 @ sk_C)
% 11.35/11.60          | (v2_struct_0 @ sk_A))),
% 11.35/11.60      inference('sup-', [status(thm)], ['2', '17'])).
% 11.35/11.60  thf('19', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 11.35/11.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.60  thf('20', plain,
% 11.35/11.60      (![X30 : $i]: ((m1_pre_topc @ X30 @ X30) | ~ (l1_pre_topc @ X30))),
% 11.35/11.60      inference('cnf', [status(esa)], [t2_tsep_1])).
% 11.35/11.60  thf('21', plain,
% 11.35/11.60      ((m1_subset_1 @ sk_E @ 
% 11.35/11.60        (k1_zfmisc_1 @ 
% 11.35/11.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 11.35/11.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.60  thf(d5_tmap_1, axiom,
% 11.35/11.60    (![A:$i]:
% 11.35/11.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 11.35/11.60       ( ![B:$i]:
% 11.35/11.60         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 11.35/11.60             ( l1_pre_topc @ B ) ) =>
% 11.35/11.60           ( ![C:$i]:
% 11.35/11.60             ( ( m1_pre_topc @ C @ A ) =>
% 11.35/11.60               ( ![D:$i]:
% 11.35/11.60                 ( ( m1_pre_topc @ D @ A ) =>
% 11.35/11.60                   ( ![E:$i]:
% 11.35/11.60                     ( ( ( v1_funct_1 @ E ) & 
% 11.35/11.60                         ( v1_funct_2 @
% 11.35/11.60                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 11.35/11.60                         ( m1_subset_1 @
% 11.35/11.60                           E @ 
% 11.35/11.60                           ( k1_zfmisc_1 @
% 11.35/11.60                             ( k2_zfmisc_1 @
% 11.35/11.60                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 11.35/11.60                       ( ( m1_pre_topc @ D @ C ) =>
% 11.35/11.60                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 11.35/11.60                           ( k2_partfun1 @
% 11.35/11.60                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 11.35/11.60                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 11.35/11.60  thf('22', plain,
% 11.35/11.60      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 11.35/11.60         ((v2_struct_0 @ X16)
% 11.35/11.60          | ~ (v2_pre_topc @ X16)
% 11.35/11.60          | ~ (l1_pre_topc @ X16)
% 11.35/11.60          | ~ (m1_pre_topc @ X17 @ X18)
% 11.35/11.60          | ~ (m1_pre_topc @ X17 @ X19)
% 11.35/11.60          | ((k3_tmap_1 @ X18 @ X16 @ X19 @ X17 @ X20)
% 11.35/11.60              = (k2_partfun1 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X16) @ 
% 11.35/11.60                 X20 @ (u1_struct_0 @ X17)))
% 11.35/11.60          | ~ (m1_subset_1 @ X20 @ 
% 11.35/11.60               (k1_zfmisc_1 @ 
% 11.35/11.60                (k2_zfmisc_1 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X16))))
% 11.35/11.60          | ~ (v1_funct_2 @ X20 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X16))
% 11.35/11.60          | ~ (v1_funct_1 @ X20)
% 11.35/11.60          | ~ (m1_pre_topc @ X19 @ X18)
% 11.35/11.60          | ~ (l1_pre_topc @ X18)
% 11.35/11.60          | ~ (v2_pre_topc @ X18)
% 11.35/11.60          | (v2_struct_0 @ X18))),
% 11.35/11.60      inference('cnf', [status(esa)], [d5_tmap_1])).
% 11.35/11.60  thf('23', plain,
% 11.35/11.60      (![X0 : $i, X1 : $i]:
% 11.35/11.60         ((v2_struct_0 @ X0)
% 11.35/11.60          | ~ (v2_pre_topc @ X0)
% 11.35/11.60          | ~ (l1_pre_topc @ X0)
% 11.35/11.60          | ~ (m1_pre_topc @ sk_A @ X0)
% 11.35/11.60          | ~ (v1_funct_1 @ sk_E)
% 11.35/11.60          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 11.35/11.60          | ((k3_tmap_1 @ X0 @ sk_B @ sk_A @ X1 @ sk_E)
% 11.35/11.60              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 11.35/11.60                 sk_E @ (u1_struct_0 @ X1)))
% 11.35/11.60          | ~ (m1_pre_topc @ X1 @ sk_A)
% 11.35/11.60          | ~ (m1_pre_topc @ X1 @ X0)
% 11.35/11.60          | ~ (l1_pre_topc @ sk_B)
% 11.35/11.60          | ~ (v2_pre_topc @ sk_B)
% 11.35/11.60          | (v2_struct_0 @ sk_B))),
% 11.35/11.60      inference('sup-', [status(thm)], ['21', '22'])).
% 11.35/11.60  thf('24', plain, ((v1_funct_1 @ sk_E)),
% 11.35/11.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.60  thf('25', plain,
% 11.35/11.60      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 11.35/11.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.60  thf('26', plain, ((l1_pre_topc @ sk_B)),
% 11.35/11.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.60  thf('27', plain, ((v2_pre_topc @ sk_B)),
% 11.35/11.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.60  thf('28', plain,
% 11.35/11.60      (![X0 : $i, X1 : $i]:
% 11.35/11.60         ((v2_struct_0 @ X0)
% 11.35/11.60          | ~ (v2_pre_topc @ X0)
% 11.35/11.60          | ~ (l1_pre_topc @ X0)
% 11.35/11.60          | ~ (m1_pre_topc @ sk_A @ X0)
% 11.35/11.60          | ((k3_tmap_1 @ X0 @ sk_B @ sk_A @ X1 @ sk_E)
% 11.35/11.60              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 11.35/11.60                 sk_E @ (u1_struct_0 @ X1)))
% 11.35/11.60          | ~ (m1_pre_topc @ X1 @ sk_A)
% 11.35/11.60          | ~ (m1_pre_topc @ X1 @ X0)
% 11.35/11.60          | (v2_struct_0 @ sk_B))),
% 11.35/11.60      inference('demod', [status(thm)], ['23', '24', '25', '26', '27'])).
% 11.35/11.60  thf('29', plain,
% 11.35/11.60      (![X0 : $i]:
% 11.35/11.60         (~ (l1_pre_topc @ sk_A)
% 11.35/11.60          | (v2_struct_0 @ sk_B)
% 11.35/11.60          | ~ (m1_pre_topc @ X0 @ sk_A)
% 11.35/11.60          | ~ (m1_pre_topc @ X0 @ sk_A)
% 11.35/11.60          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E)
% 11.35/11.60              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 11.35/11.60                 sk_E @ (u1_struct_0 @ X0)))
% 11.35/11.60          | ~ (l1_pre_topc @ sk_A)
% 11.35/11.60          | ~ (v2_pre_topc @ sk_A)
% 11.35/11.60          | (v2_struct_0 @ sk_A))),
% 11.35/11.60      inference('sup-', [status(thm)], ['20', '28'])).
% 11.35/11.60  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 11.35/11.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.60  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 11.35/11.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.60  thf('32', plain, ((v2_pre_topc @ sk_A)),
% 11.35/11.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.60  thf('33', plain,
% 11.35/11.60      (![X0 : $i]:
% 11.35/11.60         ((v2_struct_0 @ sk_B)
% 11.35/11.60          | ~ (m1_pre_topc @ X0 @ sk_A)
% 11.35/11.60          | ~ (m1_pre_topc @ X0 @ sk_A)
% 11.35/11.60          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E)
% 11.35/11.60              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 11.35/11.60                 sk_E @ (u1_struct_0 @ X0)))
% 11.35/11.60          | (v2_struct_0 @ sk_A))),
% 11.35/11.60      inference('demod', [status(thm)], ['29', '30', '31', '32'])).
% 11.35/11.60  thf('34', plain,
% 11.35/11.60      (![X0 : $i]:
% 11.35/11.60         ((v2_struct_0 @ sk_A)
% 11.35/11.60          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E)
% 11.35/11.60              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 11.35/11.60                 sk_E @ (u1_struct_0 @ X0)))
% 11.35/11.60          | ~ (m1_pre_topc @ X0 @ sk_A)
% 11.35/11.60          | (v2_struct_0 @ sk_B))),
% 11.35/11.60      inference('simplify', [status(thm)], ['33'])).
% 11.35/11.60  thf('35', plain,
% 11.35/11.60      (((v2_struct_0 @ sk_B)
% 11.35/11.60        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E)
% 11.35/11.60            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 11.35/11.60               sk_E @ (u1_struct_0 @ sk_C)))
% 11.35/11.60        | (v2_struct_0 @ sk_A))),
% 11.35/11.60      inference('sup-', [status(thm)], ['19', '34'])).
% 11.35/11.60  thf('36', plain, (~ (v2_struct_0 @ sk_B)),
% 11.35/11.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.60  thf('37', plain,
% 11.35/11.60      (((v2_struct_0 @ sk_A)
% 11.35/11.60        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E)
% 11.35/11.60            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 11.35/11.60               sk_E @ (u1_struct_0 @ sk_C))))),
% 11.35/11.60      inference('clc', [status(thm)], ['35', '36'])).
% 11.35/11.60  thf('38', plain, (~ (v2_struct_0 @ sk_A)),
% 11.35/11.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.60  thf('39', plain,
% 11.35/11.60      (((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E)
% 11.35/11.60         = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 11.35/11.60            (u1_struct_0 @ sk_C)))),
% 11.35/11.60      inference('clc', [status(thm)], ['37', '38'])).
% 11.35/11.60  thf('40', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 11.35/11.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.60  thf('41', plain,
% 11.35/11.60      ((m1_subset_1 @ sk_E @ 
% 11.35/11.60        (k1_zfmisc_1 @ 
% 11.35/11.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 11.35/11.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.60  thf(d4_tmap_1, axiom,
% 11.35/11.60    (![A:$i]:
% 11.35/11.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 11.35/11.60       ( ![B:$i]:
% 11.35/11.60         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 11.35/11.60             ( l1_pre_topc @ B ) ) =>
% 11.35/11.60           ( ![C:$i]:
% 11.35/11.60             ( ( ( v1_funct_1 @ C ) & 
% 11.35/11.60                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 11.35/11.60                 ( m1_subset_1 @
% 11.35/11.60                   C @ 
% 11.35/11.60                   ( k1_zfmisc_1 @
% 11.35/11.60                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 11.35/11.60               ( ![D:$i]:
% 11.35/11.60                 ( ( m1_pre_topc @ D @ A ) =>
% 11.35/11.60                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 11.35/11.60                     ( k2_partfun1 @
% 11.35/11.60                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 11.35/11.60                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 11.35/11.60  thf('42', plain,
% 11.35/11.60      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 11.35/11.60         ((v2_struct_0 @ X12)
% 11.35/11.60          | ~ (v2_pre_topc @ X12)
% 11.35/11.60          | ~ (l1_pre_topc @ X12)
% 11.35/11.60          | ~ (m1_pre_topc @ X13 @ X14)
% 11.35/11.60          | ((k2_tmap_1 @ X14 @ X12 @ X15 @ X13)
% 11.35/11.60              = (k2_partfun1 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X12) @ 
% 11.35/11.60                 X15 @ (u1_struct_0 @ X13)))
% 11.35/11.60          | ~ (m1_subset_1 @ X15 @ 
% 11.35/11.60               (k1_zfmisc_1 @ 
% 11.35/11.60                (k2_zfmisc_1 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X12))))
% 11.35/11.60          | ~ (v1_funct_2 @ X15 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X12))
% 11.35/11.60          | ~ (v1_funct_1 @ X15)
% 11.35/11.60          | ~ (l1_pre_topc @ X14)
% 11.35/11.60          | ~ (v2_pre_topc @ X14)
% 11.35/11.60          | (v2_struct_0 @ X14))),
% 11.35/11.60      inference('cnf', [status(esa)], [d4_tmap_1])).
% 11.35/11.60  thf('43', plain,
% 11.35/11.60      (![X0 : $i]:
% 11.35/11.60         ((v2_struct_0 @ sk_A)
% 11.35/11.60          | ~ (v2_pre_topc @ sk_A)
% 11.35/11.60          | ~ (l1_pre_topc @ sk_A)
% 11.35/11.60          | ~ (v1_funct_1 @ sk_E)
% 11.35/11.60          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 11.35/11.60          | ((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0)
% 11.35/11.60              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 11.35/11.60                 sk_E @ (u1_struct_0 @ X0)))
% 11.35/11.60          | ~ (m1_pre_topc @ X0 @ sk_A)
% 11.35/11.60          | ~ (l1_pre_topc @ sk_B)
% 11.35/11.60          | ~ (v2_pre_topc @ sk_B)
% 11.35/11.60          | (v2_struct_0 @ sk_B))),
% 11.35/11.60      inference('sup-', [status(thm)], ['41', '42'])).
% 11.35/11.60  thf('44', plain, ((v2_pre_topc @ sk_A)),
% 11.35/11.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.60  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 11.35/11.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.60  thf('46', plain, ((v1_funct_1 @ sk_E)),
% 11.35/11.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.60  thf('47', plain,
% 11.35/11.60      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 11.35/11.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.60  thf('48', plain, ((l1_pre_topc @ sk_B)),
% 11.35/11.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.60  thf('49', plain, ((v2_pre_topc @ sk_B)),
% 11.35/11.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.60  thf('50', plain,
% 11.35/11.60      (![X0 : $i]:
% 11.35/11.60         ((v2_struct_0 @ sk_A)
% 11.35/11.60          | ((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0)
% 11.35/11.60              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 11.35/11.60                 sk_E @ (u1_struct_0 @ X0)))
% 11.35/11.60          | ~ (m1_pre_topc @ X0 @ sk_A)
% 11.35/11.60          | (v2_struct_0 @ sk_B))),
% 11.35/11.60      inference('demod', [status(thm)],
% 11.35/11.60                ['43', '44', '45', '46', '47', '48', '49'])).
% 11.35/11.60  thf('51', plain,
% 11.35/11.60      (((v2_struct_0 @ sk_B)
% 11.35/11.60        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C)
% 11.35/11.60            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 11.35/11.60               sk_E @ (u1_struct_0 @ sk_C)))
% 11.35/11.60        | (v2_struct_0 @ sk_A))),
% 11.35/11.60      inference('sup-', [status(thm)], ['40', '50'])).
% 11.35/11.60  thf('52', plain, (~ (v2_struct_0 @ sk_B)),
% 11.35/11.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.60  thf('53', plain,
% 11.35/11.60      (((v2_struct_0 @ sk_A)
% 11.35/11.60        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C)
% 11.35/11.60            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 11.35/11.60               sk_E @ (u1_struct_0 @ sk_C))))),
% 11.35/11.60      inference('clc', [status(thm)], ['51', '52'])).
% 11.35/11.60  thf('54', plain, (~ (v2_struct_0 @ sk_A)),
% 11.35/11.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.60  thf('55', plain,
% 11.35/11.60      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C)
% 11.35/11.60         = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 11.35/11.60            (u1_struct_0 @ sk_C)))),
% 11.35/11.60      inference('clc', [status(thm)], ['53', '54'])).
% 11.35/11.60  thf('56', plain,
% 11.35/11.60      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C)
% 11.35/11.60         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E))),
% 11.35/11.60      inference('sup+', [status(thm)], ['39', '55'])).
% 11.35/11.60  thf('57', plain,
% 11.35/11.60      (![X0 : $i]:
% 11.35/11.60         ((v2_struct_0 @ sk_B)
% 11.35/11.60          | (v2_struct_0 @ X0)
% 11.35/11.60          | ~ (m1_pre_topc @ X0 @ sk_A)
% 11.35/11.60          | ~ (m1_pre_topc @ sk_C @ X0)
% 11.35/11.60          | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 11.35/11.60             (k3_tmap_1 @ sk_A @ sk_B @ X0 @ sk_C @ 
% 11.35/11.60              (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E)) @ 
% 11.35/11.60             (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C))
% 11.35/11.60          | (v2_struct_0 @ sk_C)
% 11.35/11.60          | (v2_struct_0 @ sk_A))),
% 11.35/11.60      inference('demod', [status(thm)], ['18', '56'])).
% 11.35/11.60  thf('58', plain,
% 11.35/11.60      (((v2_struct_0 @ sk_A)
% 11.35/11.60        | (v2_struct_0 @ sk_C)
% 11.35/11.60        | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 11.35/11.60           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ 
% 11.35/11.60            (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E)) @ 
% 11.35/11.60           (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C))
% 11.35/11.60        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 11.35/11.60        | (v2_struct_0 @ sk_D)
% 11.35/11.60        | (v2_struct_0 @ sk_B))),
% 11.35/11.60      inference('sup-', [status(thm)], ['1', '57'])).
% 11.35/11.60  thf('59', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 11.35/11.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.60  thf('60', plain,
% 11.35/11.60      (![X0 : $i]:
% 11.35/11.60         ((v2_struct_0 @ sk_A)
% 11.35/11.60          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E)
% 11.35/11.60              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 11.35/11.60                 sk_E @ (u1_struct_0 @ X0)))
% 11.35/11.60          | ~ (m1_pre_topc @ X0 @ sk_A)
% 11.35/11.60          | (v2_struct_0 @ sk_B))),
% 11.35/11.60      inference('simplify', [status(thm)], ['33'])).
% 11.35/11.60  thf('61', plain,
% 11.35/11.60      (((v2_struct_0 @ sk_B)
% 11.35/11.60        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E)
% 11.35/11.60            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 11.35/11.60               sk_E @ (u1_struct_0 @ sk_D)))
% 11.35/11.60        | (v2_struct_0 @ sk_A))),
% 11.35/11.60      inference('sup-', [status(thm)], ['59', '60'])).
% 11.35/11.60  thf('62', plain, (~ (v2_struct_0 @ sk_B)),
% 11.35/11.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.60  thf('63', plain,
% 11.35/11.60      (((v2_struct_0 @ sk_A)
% 11.35/11.60        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E)
% 11.35/11.60            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 11.35/11.60               sk_E @ (u1_struct_0 @ sk_D))))),
% 11.35/11.60      inference('clc', [status(thm)], ['61', '62'])).
% 11.35/11.60  thf('64', plain, (~ (v2_struct_0 @ sk_A)),
% 11.35/11.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.60  thf('65', plain,
% 11.35/11.60      (((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E)
% 11.35/11.60         = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 11.35/11.60            (u1_struct_0 @ sk_D)))),
% 11.35/11.60      inference('clc', [status(thm)], ['63', '64'])).
% 11.35/11.60  thf('66', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 11.35/11.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.60  thf('67', plain,
% 11.35/11.60      (![X0 : $i]:
% 11.35/11.60         ((v2_struct_0 @ sk_A)
% 11.35/11.60          | ((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0)
% 11.35/11.60              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 11.35/11.60                 sk_E @ (u1_struct_0 @ X0)))
% 11.35/11.60          | ~ (m1_pre_topc @ X0 @ sk_A)
% 11.35/11.60          | (v2_struct_0 @ sk_B))),
% 11.35/11.60      inference('demod', [status(thm)],
% 11.35/11.60                ['43', '44', '45', '46', '47', '48', '49'])).
% 11.35/11.60  thf('68', plain,
% 11.35/11.60      (((v2_struct_0 @ sk_B)
% 11.35/11.60        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 11.35/11.60            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 11.35/11.60               sk_E @ (u1_struct_0 @ sk_D)))
% 11.35/11.60        | (v2_struct_0 @ sk_A))),
% 11.35/11.60      inference('sup-', [status(thm)], ['66', '67'])).
% 11.35/11.60  thf('69', plain, (~ (v2_struct_0 @ sk_B)),
% 11.35/11.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.60  thf('70', plain,
% 11.35/11.60      (((v2_struct_0 @ sk_A)
% 11.35/11.60        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 11.35/11.60            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 11.35/11.60               sk_E @ (u1_struct_0 @ sk_D))))),
% 11.35/11.60      inference('clc', [status(thm)], ['68', '69'])).
% 11.35/11.60  thf('71', plain, (~ (v2_struct_0 @ sk_A)),
% 11.35/11.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.60  thf('72', plain,
% 11.35/11.60      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 11.35/11.60         = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 11.35/11.60            (u1_struct_0 @ sk_D)))),
% 11.35/11.60      inference('clc', [status(thm)], ['70', '71'])).
% 11.35/11.60  thf('73', plain,
% 11.35/11.60      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 11.35/11.60         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))),
% 11.35/11.60      inference('sup+', [status(thm)], ['65', '72'])).
% 11.35/11.60  thf('74', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 11.35/11.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.60  thf('75', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 11.35/11.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.60  thf('76', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 11.35/11.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.60  thf('77', plain,
% 11.35/11.60      (![X30 : $i]: ((m1_pre_topc @ X30 @ X30) | ~ (l1_pre_topc @ X30))),
% 11.35/11.60      inference('cnf', [status(esa)], [t2_tsep_1])).
% 11.35/11.60  thf('78', plain,
% 11.35/11.60      ((m1_subset_1 @ sk_E @ 
% 11.35/11.60        (k1_zfmisc_1 @ 
% 11.35/11.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 11.35/11.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.60  thf(dt_k3_tmap_1, axiom,
% 11.35/11.60    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 11.35/11.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 11.35/11.60         ( l1_pre_topc @ A ) & ( ~( v2_struct_0 @ B ) ) & 
% 11.35/11.60         ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) & ( m1_pre_topc @ C @ A ) & 
% 11.35/11.60         ( m1_pre_topc @ D @ A ) & ( v1_funct_1 @ E ) & 
% 11.35/11.60         ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 11.35/11.60         ( m1_subset_1 @
% 11.35/11.60           E @ 
% 11.35/11.60           ( k1_zfmisc_1 @
% 11.35/11.60             ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 11.35/11.60       ( ( v1_funct_1 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) ) & 
% 11.35/11.60         ( v1_funct_2 @
% 11.35/11.60           ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ ( u1_struct_0 @ D ) @ 
% 11.35/11.60           ( u1_struct_0 @ B ) ) & 
% 11.35/11.60         ( m1_subset_1 @
% 11.35/11.60           ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ 
% 11.35/11.60           ( k1_zfmisc_1 @
% 11.35/11.60             ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 11.35/11.60  thf('79', plain,
% 11.35/11.60      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 11.35/11.60         (~ (m1_pre_topc @ X25 @ X26)
% 11.35/11.60          | ~ (m1_pre_topc @ X27 @ X26)
% 11.35/11.60          | ~ (l1_pre_topc @ X28)
% 11.35/11.60          | ~ (v2_pre_topc @ X28)
% 11.35/11.60          | (v2_struct_0 @ X28)
% 11.35/11.60          | ~ (l1_pre_topc @ X26)
% 11.35/11.60          | ~ (v2_pre_topc @ X26)
% 11.35/11.60          | (v2_struct_0 @ X26)
% 11.35/11.60          | ~ (v1_funct_1 @ X29)
% 11.35/11.60          | ~ (v1_funct_2 @ X29 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X28))
% 11.35/11.60          | ~ (m1_subset_1 @ X29 @ 
% 11.35/11.60               (k1_zfmisc_1 @ 
% 11.35/11.60                (k2_zfmisc_1 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X28))))
% 11.35/11.60          | (m1_subset_1 @ (k3_tmap_1 @ X26 @ X28 @ X27 @ X25 @ X29) @ 
% 11.35/11.60             (k1_zfmisc_1 @ 
% 11.35/11.60              (k2_zfmisc_1 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X28)))))),
% 11.35/11.60      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 11.35/11.60  thf('80', plain,
% 11.35/11.60      (![X0 : $i, X1 : $i]:
% 11.35/11.60         ((m1_subset_1 @ (k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 11.35/11.60           (k1_zfmisc_1 @ 
% 11.35/11.60            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 11.35/11.60          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 11.35/11.60          | ~ (v1_funct_1 @ sk_E)
% 11.35/11.60          | (v2_struct_0 @ X1)
% 11.35/11.60          | ~ (v2_pre_topc @ X1)
% 11.35/11.60          | ~ (l1_pre_topc @ X1)
% 11.35/11.60          | (v2_struct_0 @ sk_B)
% 11.35/11.60          | ~ (v2_pre_topc @ sk_B)
% 11.35/11.60          | ~ (l1_pre_topc @ sk_B)
% 11.35/11.60          | ~ (m1_pre_topc @ sk_A @ X1)
% 11.35/11.60          | ~ (m1_pre_topc @ X0 @ X1))),
% 11.35/11.60      inference('sup-', [status(thm)], ['78', '79'])).
% 11.35/11.60  thf('81', plain,
% 11.35/11.60      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 11.35/11.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.60  thf('82', plain, ((v1_funct_1 @ sk_E)),
% 11.35/11.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.60  thf('83', plain, ((v2_pre_topc @ sk_B)),
% 11.35/11.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.60  thf('84', plain, ((l1_pre_topc @ sk_B)),
% 11.35/11.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.60  thf('85', plain,
% 11.35/11.60      (![X0 : $i, X1 : $i]:
% 11.35/11.60         ((m1_subset_1 @ (k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 11.35/11.60           (k1_zfmisc_1 @ 
% 11.35/11.60            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 11.35/11.60          | (v2_struct_0 @ X1)
% 11.35/11.60          | ~ (v2_pre_topc @ X1)
% 11.35/11.60          | ~ (l1_pre_topc @ X1)
% 11.35/11.60          | (v2_struct_0 @ sk_B)
% 11.35/11.60          | ~ (m1_pre_topc @ sk_A @ X1)
% 11.35/11.60          | ~ (m1_pre_topc @ X0 @ X1))),
% 11.35/11.60      inference('demod', [status(thm)], ['80', '81', '82', '83', '84'])).
% 11.35/11.60  thf('86', plain,
% 11.35/11.60      (![X0 : $i]:
% 11.35/11.60         (~ (l1_pre_topc @ sk_A)
% 11.35/11.60          | ~ (m1_pre_topc @ X0 @ sk_A)
% 11.35/11.60          | (v2_struct_0 @ sk_B)
% 11.35/11.60          | ~ (l1_pre_topc @ sk_A)
% 11.35/11.60          | ~ (v2_pre_topc @ sk_A)
% 11.35/11.60          | (v2_struct_0 @ sk_A)
% 11.35/11.60          | (m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 11.35/11.60             (k1_zfmisc_1 @ 
% 11.35/11.60              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))))),
% 11.35/11.60      inference('sup-', [status(thm)], ['77', '85'])).
% 11.35/11.60  thf('87', plain, ((l1_pre_topc @ sk_A)),
% 11.35/11.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.60  thf('88', plain, ((l1_pre_topc @ sk_A)),
% 11.35/11.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.60  thf('89', plain, ((v2_pre_topc @ sk_A)),
% 11.35/11.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.60  thf('90', plain,
% 11.35/11.60      (![X0 : $i]:
% 11.35/11.60         (~ (m1_pre_topc @ X0 @ sk_A)
% 11.35/11.60          | (v2_struct_0 @ sk_B)
% 11.35/11.60          | (v2_struct_0 @ sk_A)
% 11.35/11.60          | (m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 11.35/11.60             (k1_zfmisc_1 @ 
% 11.35/11.60              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))))),
% 11.35/11.60      inference('demod', [status(thm)], ['86', '87', '88', '89'])).
% 11.35/11.60  thf('91', plain,
% 11.35/11.60      (((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E) @ 
% 11.35/11.60         (k1_zfmisc_1 @ 
% 11.35/11.60          (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 11.35/11.60        | (v2_struct_0 @ sk_A)
% 11.35/11.60        | (v2_struct_0 @ sk_B))),
% 11.35/11.60      inference('sup-', [status(thm)], ['76', '90'])).
% 11.35/11.60  thf('92', plain,
% 11.35/11.60      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 11.35/11.60         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))),
% 11.35/11.60      inference('sup+', [status(thm)], ['65', '72'])).
% 11.35/11.60  thf('93', plain,
% 11.35/11.60      (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 11.35/11.60         (k1_zfmisc_1 @ 
% 11.35/11.60          (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 11.35/11.60        | (v2_struct_0 @ sk_A)
% 11.35/11.60        | (v2_struct_0 @ sk_B))),
% 11.35/11.60      inference('demod', [status(thm)], ['91', '92'])).
% 11.35/11.60  thf('94', plain, (~ (v2_struct_0 @ sk_A)),
% 11.35/11.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.60  thf('95', plain,
% 11.35/11.60      (((v2_struct_0 @ sk_B)
% 11.35/11.60        | (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 11.35/11.60           (k1_zfmisc_1 @ 
% 11.35/11.60            (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))))),
% 11.35/11.60      inference('clc', [status(thm)], ['93', '94'])).
% 11.35/11.60  thf('96', plain, (~ (v2_struct_0 @ sk_B)),
% 11.35/11.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.60  thf('97', plain,
% 11.35/11.60      ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 11.35/11.60        (k1_zfmisc_1 @ 
% 11.35/11.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 11.35/11.60      inference('clc', [status(thm)], ['95', '96'])).
% 11.35/11.60  thf('98', plain,
% 11.35/11.60      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 11.35/11.60         ((v2_struct_0 @ X16)
% 11.35/11.60          | ~ (v2_pre_topc @ X16)
% 11.35/11.60          | ~ (l1_pre_topc @ X16)
% 11.35/11.60          | ~ (m1_pre_topc @ X17 @ X18)
% 11.35/11.60          | ~ (m1_pre_topc @ X17 @ X19)
% 11.35/11.60          | ((k3_tmap_1 @ X18 @ X16 @ X19 @ X17 @ X20)
% 11.35/11.60              = (k2_partfun1 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X16) @ 
% 11.35/11.60                 X20 @ (u1_struct_0 @ X17)))
% 11.35/11.60          | ~ (m1_subset_1 @ X20 @ 
% 11.35/11.60               (k1_zfmisc_1 @ 
% 11.35/11.60                (k2_zfmisc_1 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X16))))
% 11.35/11.60          | ~ (v1_funct_2 @ X20 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X16))
% 11.35/11.60          | ~ (v1_funct_1 @ X20)
% 11.35/11.60          | ~ (m1_pre_topc @ X19 @ X18)
% 11.35/11.60          | ~ (l1_pre_topc @ X18)
% 11.35/11.60          | ~ (v2_pre_topc @ X18)
% 11.35/11.60          | (v2_struct_0 @ X18))),
% 11.35/11.60      inference('cnf', [status(esa)], [d5_tmap_1])).
% 11.35/11.60  thf('99', plain,
% 11.35/11.60      (![X0 : $i, X1 : $i]:
% 11.35/11.60         ((v2_struct_0 @ X0)
% 11.35/11.60          | ~ (v2_pre_topc @ X0)
% 11.35/11.60          | ~ (l1_pre_topc @ X0)
% 11.35/11.60          | ~ (m1_pre_topc @ sk_D @ X0)
% 11.35/11.60          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))
% 11.35/11.60          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 11.35/11.60               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 11.35/11.60          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ 
% 11.35/11.60              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))
% 11.35/11.60              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 11.35/11.60                 (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ (u1_struct_0 @ X1)))
% 11.35/11.60          | ~ (m1_pre_topc @ X1 @ sk_D)
% 11.35/11.60          | ~ (m1_pre_topc @ X1 @ X0)
% 11.35/11.60          | ~ (l1_pre_topc @ sk_B)
% 11.35/11.60          | ~ (v2_pre_topc @ sk_B)
% 11.35/11.60          | (v2_struct_0 @ sk_B))),
% 11.35/11.60      inference('sup-', [status(thm)], ['97', '98'])).
% 11.35/11.60  thf('100', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 11.35/11.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.60  thf('101', plain,
% 11.35/11.60      (![X30 : $i]: ((m1_pre_topc @ X30 @ X30) | ~ (l1_pre_topc @ X30))),
% 11.35/11.60      inference('cnf', [status(esa)], [t2_tsep_1])).
% 11.35/11.60  thf('102', plain,
% 11.35/11.60      ((m1_subset_1 @ sk_E @ 
% 11.35/11.60        (k1_zfmisc_1 @ 
% 11.35/11.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 11.35/11.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.60  thf('103', plain,
% 11.35/11.60      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 11.35/11.60         (~ (m1_pre_topc @ X25 @ X26)
% 11.35/11.60          | ~ (m1_pre_topc @ X27 @ X26)
% 11.35/11.60          | ~ (l1_pre_topc @ X28)
% 11.35/11.60          | ~ (v2_pre_topc @ X28)
% 11.35/11.60          | (v2_struct_0 @ X28)
% 11.35/11.60          | ~ (l1_pre_topc @ X26)
% 11.35/11.60          | ~ (v2_pre_topc @ X26)
% 11.35/11.60          | (v2_struct_0 @ X26)
% 11.35/11.60          | ~ (v1_funct_1 @ X29)
% 11.35/11.60          | ~ (v1_funct_2 @ X29 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X28))
% 11.35/11.60          | ~ (m1_subset_1 @ X29 @ 
% 11.35/11.60               (k1_zfmisc_1 @ 
% 11.35/11.60                (k2_zfmisc_1 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X28))))
% 11.35/11.60          | (v1_funct_1 @ (k3_tmap_1 @ X26 @ X28 @ X27 @ X25 @ X29)))),
% 11.35/11.60      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 11.35/11.60  thf('104', plain,
% 11.35/11.60      (![X0 : $i, X1 : $i]:
% 11.35/11.60         ((v1_funct_1 @ (k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E))
% 11.35/11.60          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 11.35/11.60          | ~ (v1_funct_1 @ sk_E)
% 11.35/11.60          | (v2_struct_0 @ X1)
% 11.35/11.60          | ~ (v2_pre_topc @ X1)
% 11.35/11.60          | ~ (l1_pre_topc @ X1)
% 11.35/11.60          | (v2_struct_0 @ sk_B)
% 11.35/11.60          | ~ (v2_pre_topc @ sk_B)
% 11.35/11.60          | ~ (l1_pre_topc @ sk_B)
% 11.35/11.60          | ~ (m1_pre_topc @ sk_A @ X1)
% 11.35/11.60          | ~ (m1_pre_topc @ X0 @ X1))),
% 11.35/11.60      inference('sup-', [status(thm)], ['102', '103'])).
% 11.35/11.60  thf('105', plain,
% 11.35/11.60      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 11.35/11.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.60  thf('106', plain, ((v1_funct_1 @ sk_E)),
% 11.35/11.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.60  thf('107', plain, ((v2_pre_topc @ sk_B)),
% 11.35/11.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.60  thf('108', plain, ((l1_pre_topc @ sk_B)),
% 11.35/11.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.60  thf('109', plain,
% 11.35/11.60      (![X0 : $i, X1 : $i]:
% 11.35/11.60         ((v1_funct_1 @ (k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E))
% 11.35/11.60          | (v2_struct_0 @ X1)
% 11.35/11.60          | ~ (v2_pre_topc @ X1)
% 11.35/11.60          | ~ (l1_pre_topc @ X1)
% 11.35/11.60          | (v2_struct_0 @ sk_B)
% 11.35/11.60          | ~ (m1_pre_topc @ sk_A @ X1)
% 11.35/11.60          | ~ (m1_pre_topc @ X0 @ X1))),
% 11.35/11.60      inference('demod', [status(thm)], ['104', '105', '106', '107', '108'])).
% 11.35/11.60  thf('110', plain,
% 11.35/11.60      (![X0 : $i]:
% 11.35/11.60         (~ (l1_pre_topc @ sk_A)
% 11.35/11.60          | ~ (m1_pre_topc @ X0 @ sk_A)
% 11.35/11.60          | (v2_struct_0 @ sk_B)
% 11.35/11.60          | ~ (l1_pre_topc @ sk_A)
% 11.35/11.60          | ~ (v2_pre_topc @ sk_A)
% 11.35/11.60          | (v2_struct_0 @ sk_A)
% 11.35/11.60          | (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E)))),
% 11.35/11.60      inference('sup-', [status(thm)], ['101', '109'])).
% 11.35/11.60  thf('111', plain, ((l1_pre_topc @ sk_A)),
% 11.35/11.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.60  thf('112', plain, ((l1_pre_topc @ sk_A)),
% 11.35/11.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.60  thf('113', plain, ((v2_pre_topc @ sk_A)),
% 11.35/11.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.60  thf('114', plain,
% 11.35/11.60      (![X0 : $i]:
% 11.35/11.60         (~ (m1_pre_topc @ X0 @ sk_A)
% 11.35/11.60          | (v2_struct_0 @ sk_B)
% 11.35/11.60          | (v2_struct_0 @ sk_A)
% 11.35/11.60          | (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E)))),
% 11.35/11.60      inference('demod', [status(thm)], ['110', '111', '112', '113'])).
% 11.35/11.60  thf('115', plain,
% 11.35/11.60      (((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))
% 11.35/11.60        | (v2_struct_0 @ sk_A)
% 11.35/11.60        | (v2_struct_0 @ sk_B))),
% 11.35/11.60      inference('sup-', [status(thm)], ['100', '114'])).
% 11.35/11.60  thf('116', plain,
% 11.35/11.60      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 11.35/11.60         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))),
% 11.35/11.60      inference('sup+', [status(thm)], ['65', '72'])).
% 11.35/11.60  thf('117', plain,
% 11.35/11.60      (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))
% 11.35/11.60        | (v2_struct_0 @ sk_A)
% 11.35/11.60        | (v2_struct_0 @ sk_B))),
% 11.35/11.60      inference('demod', [status(thm)], ['115', '116'])).
% 11.35/11.60  thf('118', plain, (~ (v2_struct_0 @ sk_A)),
% 11.35/11.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.60  thf('119', plain,
% 11.35/11.60      (((v2_struct_0 @ sk_B)
% 11.35/11.60        | (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)))),
% 11.35/11.60      inference('clc', [status(thm)], ['117', '118'])).
% 11.35/11.60  thf('120', plain, (~ (v2_struct_0 @ sk_B)),
% 11.35/11.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.60  thf('121', plain, ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))),
% 11.35/11.60      inference('clc', [status(thm)], ['119', '120'])).
% 11.35/11.60  thf('122', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 11.35/11.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.60  thf('123', plain,
% 11.35/11.60      (![X30 : $i]: ((m1_pre_topc @ X30 @ X30) | ~ (l1_pre_topc @ X30))),
% 11.35/11.60      inference('cnf', [status(esa)], [t2_tsep_1])).
% 11.35/11.60  thf('124', plain,
% 11.35/11.60      ((m1_subset_1 @ sk_E @ 
% 11.35/11.60        (k1_zfmisc_1 @ 
% 11.35/11.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 11.35/11.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.60  thf('125', plain,
% 11.35/11.60      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 11.35/11.60         (~ (m1_pre_topc @ X25 @ X26)
% 11.35/11.60          | ~ (m1_pre_topc @ X27 @ X26)
% 11.35/11.60          | ~ (l1_pre_topc @ X28)
% 11.35/11.60          | ~ (v2_pre_topc @ X28)
% 11.35/11.60          | (v2_struct_0 @ X28)
% 11.35/11.60          | ~ (l1_pre_topc @ X26)
% 11.35/11.60          | ~ (v2_pre_topc @ X26)
% 11.35/11.60          | (v2_struct_0 @ X26)
% 11.35/11.60          | ~ (v1_funct_1 @ X29)
% 11.35/11.60          | ~ (v1_funct_2 @ X29 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X28))
% 11.35/11.60          | ~ (m1_subset_1 @ X29 @ 
% 11.35/11.60               (k1_zfmisc_1 @ 
% 11.35/11.60                (k2_zfmisc_1 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X28))))
% 11.35/11.60          | (v1_funct_2 @ (k3_tmap_1 @ X26 @ X28 @ X27 @ X25 @ X29) @ 
% 11.35/11.60             (u1_struct_0 @ X25) @ (u1_struct_0 @ X28)))),
% 11.35/11.60      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 11.35/11.60  thf('126', plain,
% 11.35/11.60      (![X0 : $i, X1 : $i]:
% 11.35/11.60         ((v1_funct_2 @ (k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 11.35/11.60           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 11.35/11.60          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 11.35/11.60          | ~ (v1_funct_1 @ sk_E)
% 11.35/11.60          | (v2_struct_0 @ X1)
% 11.35/11.60          | ~ (v2_pre_topc @ X1)
% 11.35/11.60          | ~ (l1_pre_topc @ X1)
% 11.35/11.60          | (v2_struct_0 @ sk_B)
% 11.35/11.60          | ~ (v2_pre_topc @ sk_B)
% 11.35/11.60          | ~ (l1_pre_topc @ sk_B)
% 11.35/11.60          | ~ (m1_pre_topc @ sk_A @ X1)
% 11.35/11.60          | ~ (m1_pre_topc @ X0 @ X1))),
% 11.35/11.60      inference('sup-', [status(thm)], ['124', '125'])).
% 11.35/11.60  thf('127', plain,
% 11.35/11.60      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 11.35/11.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.60  thf('128', plain, ((v1_funct_1 @ sk_E)),
% 11.35/11.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.60  thf('129', plain, ((v2_pre_topc @ sk_B)),
% 11.35/11.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.60  thf('130', plain, ((l1_pre_topc @ sk_B)),
% 11.35/11.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.60  thf('131', plain,
% 11.35/11.60      (![X0 : $i, X1 : $i]:
% 11.35/11.60         ((v1_funct_2 @ (k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 11.35/11.60           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 11.35/11.60          | (v2_struct_0 @ X1)
% 11.35/11.60          | ~ (v2_pre_topc @ X1)
% 11.35/11.60          | ~ (l1_pre_topc @ X1)
% 11.35/11.60          | (v2_struct_0 @ sk_B)
% 11.35/11.60          | ~ (m1_pre_topc @ sk_A @ X1)
% 11.35/11.60          | ~ (m1_pre_topc @ X0 @ X1))),
% 11.35/11.60      inference('demod', [status(thm)], ['126', '127', '128', '129', '130'])).
% 11.35/11.60  thf('132', plain,
% 11.35/11.60      (![X0 : $i]:
% 11.35/11.60         (~ (l1_pre_topc @ sk_A)
% 11.35/11.60          | ~ (m1_pre_topc @ X0 @ sk_A)
% 11.35/11.60          | (v2_struct_0 @ sk_B)
% 11.35/11.60          | ~ (l1_pre_topc @ sk_A)
% 11.35/11.60          | ~ (v2_pre_topc @ sk_A)
% 11.35/11.60          | (v2_struct_0 @ sk_A)
% 11.35/11.60          | (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 11.35/11.60             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 11.35/11.60      inference('sup-', [status(thm)], ['123', '131'])).
% 11.35/11.60  thf('133', plain, ((l1_pre_topc @ sk_A)),
% 11.35/11.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.60  thf('134', plain, ((l1_pre_topc @ sk_A)),
% 11.35/11.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.60  thf('135', plain, ((v2_pre_topc @ sk_A)),
% 11.35/11.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.60  thf('136', plain,
% 11.35/11.60      (![X0 : $i]:
% 11.35/11.60         (~ (m1_pre_topc @ X0 @ sk_A)
% 11.35/11.60          | (v2_struct_0 @ sk_B)
% 11.35/11.60          | (v2_struct_0 @ sk_A)
% 11.35/11.60          | (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 11.35/11.60             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 11.35/11.60      inference('demod', [status(thm)], ['132', '133', '134', '135'])).
% 11.35/11.60  thf('137', plain,
% 11.35/11.60      (((v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E) @ 
% 11.35/11.60         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 11.35/11.60        | (v2_struct_0 @ sk_A)
% 11.35/11.60        | (v2_struct_0 @ sk_B))),
% 11.35/11.60      inference('sup-', [status(thm)], ['122', '136'])).
% 11.35/11.60  thf('138', plain,
% 11.35/11.60      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 11.35/11.60         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))),
% 11.35/11.60      inference('sup+', [status(thm)], ['65', '72'])).
% 11.35/11.60  thf('139', plain,
% 11.35/11.60      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 11.35/11.60         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 11.35/11.60        | (v2_struct_0 @ sk_A)
% 11.35/11.60        | (v2_struct_0 @ sk_B))),
% 11.35/11.60      inference('demod', [status(thm)], ['137', '138'])).
% 11.35/11.60  thf('140', plain, (~ (v2_struct_0 @ sk_A)),
% 11.35/11.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.60  thf('141', plain,
% 11.35/11.60      (((v2_struct_0 @ sk_B)
% 11.35/11.60        | (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 11.35/11.60           (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))),
% 11.35/11.60      inference('clc', [status(thm)], ['139', '140'])).
% 11.35/11.60  thf('142', plain, (~ (v2_struct_0 @ sk_B)),
% 11.35/11.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.60  thf('143', plain,
% 11.35/11.60      ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 11.35/11.60        (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 11.35/11.60      inference('clc', [status(thm)], ['141', '142'])).
% 11.35/11.60  thf('144', plain, ((l1_pre_topc @ sk_B)),
% 11.35/11.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.60  thf('145', plain, ((v2_pre_topc @ sk_B)),
% 11.35/11.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.60  thf('146', plain,
% 11.35/11.60      (![X0 : $i, X1 : $i]:
% 11.35/11.60         ((v2_struct_0 @ X0)
% 11.35/11.60          | ~ (v2_pre_topc @ X0)
% 11.35/11.60          | ~ (l1_pre_topc @ X0)
% 11.35/11.60          | ~ (m1_pre_topc @ sk_D @ X0)
% 11.35/11.60          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ 
% 11.35/11.60              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))
% 11.35/11.60              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 11.35/11.60                 (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ (u1_struct_0 @ X1)))
% 11.35/11.60          | ~ (m1_pre_topc @ X1 @ sk_D)
% 11.35/11.60          | ~ (m1_pre_topc @ X1 @ X0)
% 11.35/11.60          | (v2_struct_0 @ sk_B))),
% 11.35/11.60      inference('demod', [status(thm)], ['99', '121', '143', '144', '145'])).
% 11.35/11.60  thf('147', plain,
% 11.35/11.60      (![X0 : $i]:
% 11.35/11.60         ((v2_struct_0 @ sk_B)
% 11.35/11.60          | ~ (m1_pre_topc @ X0 @ sk_A)
% 11.35/11.60          | ~ (m1_pre_topc @ X0 @ sk_D)
% 11.35/11.60          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ 
% 11.35/11.60              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))
% 11.35/11.60              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 11.35/11.60                 (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ (u1_struct_0 @ X0)))
% 11.35/11.60          | ~ (l1_pre_topc @ sk_A)
% 11.35/11.60          | ~ (v2_pre_topc @ sk_A)
% 11.35/11.60          | (v2_struct_0 @ sk_A))),
% 11.35/11.60      inference('sup-', [status(thm)], ['75', '146'])).
% 11.35/11.60  thf('148', plain, ((l1_pre_topc @ sk_A)),
% 11.35/11.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.60  thf('149', plain, ((v2_pre_topc @ sk_A)),
% 11.35/11.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.60  thf('150', plain,
% 11.35/11.60      (![X0 : $i]:
% 11.35/11.60         ((v2_struct_0 @ sk_B)
% 11.35/11.60          | ~ (m1_pre_topc @ X0 @ sk_A)
% 11.35/11.60          | ~ (m1_pre_topc @ X0 @ sk_D)
% 11.35/11.60          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ 
% 11.35/11.60              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))
% 11.35/11.60              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 11.35/11.60                 (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ (u1_struct_0 @ X0)))
% 11.35/11.60          | (v2_struct_0 @ sk_A))),
% 11.35/11.60      inference('demod', [status(thm)], ['147', '148', '149'])).
% 11.35/11.60  thf('151', plain,
% 11.35/11.60      (((v2_struct_0 @ sk_A)
% 11.35/11.60        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ 
% 11.35/11.60            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))
% 11.35/11.60            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 11.35/11.60               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ (u1_struct_0 @ sk_C)))
% 11.35/11.60        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 11.35/11.60        | (v2_struct_0 @ sk_B))),
% 11.35/11.60      inference('sup-', [status(thm)], ['74', '150'])).
% 11.35/11.60  thf('152', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 11.35/11.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.60  thf('153', plain,
% 11.35/11.60      ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 11.35/11.60        (k1_zfmisc_1 @ 
% 11.35/11.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 11.35/11.60      inference('clc', [status(thm)], ['95', '96'])).
% 11.35/11.60  thf('154', plain,
% 11.35/11.60      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 11.35/11.60         ((v2_struct_0 @ X12)
% 11.35/11.60          | ~ (v2_pre_topc @ X12)
% 11.35/11.60          | ~ (l1_pre_topc @ X12)
% 11.35/11.60          | ~ (m1_pre_topc @ X13 @ X14)
% 11.35/11.60          | ((k2_tmap_1 @ X14 @ X12 @ X15 @ X13)
% 11.35/11.60              = (k2_partfun1 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X12) @ 
% 11.35/11.60                 X15 @ (u1_struct_0 @ X13)))
% 11.35/11.60          | ~ (m1_subset_1 @ X15 @ 
% 11.35/11.60               (k1_zfmisc_1 @ 
% 11.35/11.60                (k2_zfmisc_1 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X12))))
% 11.35/11.60          | ~ (v1_funct_2 @ X15 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X12))
% 11.35/11.60          | ~ (v1_funct_1 @ X15)
% 11.35/11.60          | ~ (l1_pre_topc @ X14)
% 11.35/11.60          | ~ (v2_pre_topc @ X14)
% 11.35/11.60          | (v2_struct_0 @ X14))),
% 11.35/11.60      inference('cnf', [status(esa)], [d4_tmap_1])).
% 11.35/11.60  thf('155', plain,
% 11.35/11.60      (![X0 : $i]:
% 11.35/11.60         ((v2_struct_0 @ sk_D)
% 11.35/11.60          | ~ (v2_pre_topc @ sk_D)
% 11.35/11.60          | ~ (l1_pre_topc @ sk_D)
% 11.35/11.60          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))
% 11.35/11.60          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 11.35/11.60               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 11.35/11.60          | ((k2_tmap_1 @ sk_D @ sk_B @ 
% 11.35/11.60              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ X0)
% 11.35/11.60              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 11.35/11.60                 (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ (u1_struct_0 @ X0)))
% 11.35/11.60          | ~ (m1_pre_topc @ X0 @ sk_D)
% 11.35/11.60          | ~ (l1_pre_topc @ sk_B)
% 11.35/11.60          | ~ (v2_pre_topc @ sk_B)
% 11.35/11.60          | (v2_struct_0 @ sk_B))),
% 11.35/11.60      inference('sup-', [status(thm)], ['153', '154'])).
% 11.35/11.60  thf('156', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 11.35/11.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.60  thf(cc1_pre_topc, axiom,
% 11.35/11.60    (![A:$i]:
% 11.35/11.60     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 11.35/11.60       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 11.35/11.60  thf('157', plain,
% 11.35/11.60      (![X4 : $i, X5 : $i]:
% 11.35/11.60         (~ (m1_pre_topc @ X4 @ X5)
% 11.35/11.60          | (v2_pre_topc @ X4)
% 11.35/11.60          | ~ (l1_pre_topc @ X5)
% 11.35/11.60          | ~ (v2_pre_topc @ X5))),
% 11.35/11.60      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 11.35/11.60  thf('158', plain,
% 11.35/11.60      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_D))),
% 11.35/11.60      inference('sup-', [status(thm)], ['156', '157'])).
% 11.35/11.60  thf('159', plain, ((v2_pre_topc @ sk_A)),
% 11.35/11.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.60  thf('160', plain, ((l1_pre_topc @ sk_A)),
% 11.35/11.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.60  thf('161', plain, ((v2_pre_topc @ sk_D)),
% 11.35/11.60      inference('demod', [status(thm)], ['158', '159', '160'])).
% 11.35/11.60  thf('162', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 11.35/11.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.60  thf(dt_m1_pre_topc, axiom,
% 11.35/11.60    (![A:$i]:
% 11.35/11.60     ( ( l1_pre_topc @ A ) =>
% 11.35/11.60       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 11.35/11.60  thf('163', plain,
% 11.35/11.60      (![X7 : $i, X8 : $i]:
% 11.35/11.60         (~ (m1_pre_topc @ X7 @ X8) | (l1_pre_topc @ X7) | ~ (l1_pre_topc @ X8))),
% 11.35/11.60      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 11.35/11.60  thf('164', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 11.35/11.60      inference('sup-', [status(thm)], ['162', '163'])).
% 11.35/11.60  thf('165', plain, ((l1_pre_topc @ sk_A)),
% 11.35/11.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.60  thf('166', plain, ((l1_pre_topc @ sk_D)),
% 11.35/11.60      inference('demod', [status(thm)], ['164', '165'])).
% 11.35/11.60  thf('167', plain, ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))),
% 11.35/11.60      inference('clc', [status(thm)], ['119', '120'])).
% 11.35/11.60  thf('168', plain,
% 11.35/11.60      ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 11.35/11.60        (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 11.35/11.60      inference('clc', [status(thm)], ['141', '142'])).
% 11.35/11.60  thf('169', plain, ((l1_pre_topc @ sk_B)),
% 11.35/11.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.60  thf('170', plain, ((v2_pre_topc @ sk_B)),
% 11.35/11.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.60  thf('171', plain,
% 11.35/11.60      (![X0 : $i]:
% 11.35/11.60         ((v2_struct_0 @ sk_D)
% 11.35/11.60          | ((k2_tmap_1 @ sk_D @ sk_B @ 
% 11.35/11.60              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ X0)
% 11.35/11.60              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 11.35/11.60                 (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ (u1_struct_0 @ X0)))
% 11.35/11.60          | ~ (m1_pre_topc @ X0 @ sk_D)
% 11.35/11.60          | (v2_struct_0 @ sk_B))),
% 11.35/11.60      inference('demod', [status(thm)],
% 11.35/11.60                ['155', '161', '166', '167', '168', '169', '170'])).
% 11.35/11.60  thf('172', plain,
% 11.35/11.60      (((v2_struct_0 @ sk_B)
% 11.35/11.60        | ((k2_tmap_1 @ sk_D @ sk_B @ 
% 11.35/11.60            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ sk_C)
% 11.35/11.60            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 11.35/11.60               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ (u1_struct_0 @ sk_C)))
% 11.35/11.60        | (v2_struct_0 @ sk_D))),
% 11.35/11.60      inference('sup-', [status(thm)], ['152', '171'])).
% 11.35/11.60  thf('173', plain, (~ (v2_struct_0 @ sk_B)),
% 11.35/11.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.60  thf('174', plain,
% 11.35/11.60      (((v2_struct_0 @ sk_D)
% 11.35/11.60        | ((k2_tmap_1 @ sk_D @ sk_B @ 
% 11.35/11.60            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ sk_C)
% 11.35/11.60            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 11.35/11.60               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ (u1_struct_0 @ sk_C))))),
% 11.35/11.60      inference('clc', [status(thm)], ['172', '173'])).
% 11.35/11.60  thf('175', plain, (~ (v2_struct_0 @ sk_D)),
% 11.35/11.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.60  thf('176', plain,
% 11.35/11.60      (((k2_tmap_1 @ sk_D @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 11.35/11.60         sk_C)
% 11.35/11.60         = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 11.35/11.60            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ (u1_struct_0 @ sk_C)))),
% 11.35/11.60      inference('clc', [status(thm)], ['174', '175'])).
% 11.35/11.60  thf('177', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 11.35/11.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.60  thf('178', plain,
% 11.35/11.60      (((v2_struct_0 @ sk_A)
% 11.35/11.60        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ 
% 11.35/11.60            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))
% 11.35/11.60            = (k2_tmap_1 @ sk_D @ sk_B @ 
% 11.35/11.60               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ sk_C))
% 11.35/11.60        | (v2_struct_0 @ sk_B))),
% 11.35/11.60      inference('demod', [status(thm)], ['151', '176', '177'])).
% 11.35/11.60  thf('179', plain, (~ (v2_struct_0 @ sk_A)),
% 11.35/11.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.60  thf('180', plain,
% 11.35/11.60      (((v2_struct_0 @ sk_B)
% 11.35/11.60        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ 
% 11.35/11.60            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))
% 11.35/11.60            = (k2_tmap_1 @ sk_D @ sk_B @ 
% 11.35/11.60               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ sk_C)))),
% 11.35/11.60      inference('clc', [status(thm)], ['178', '179'])).
% 11.35/11.60  thf('181', plain, (~ (v2_struct_0 @ sk_B)),
% 11.35/11.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.60  thf('182', plain,
% 11.35/11.60      (((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ 
% 11.35/11.60         (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))
% 11.35/11.60         = (k2_tmap_1 @ sk_D @ sk_B @ 
% 11.35/11.60            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ sk_C))),
% 11.35/11.60      inference('clc', [status(thm)], ['180', '181'])).
% 11.35/11.60  thf('183', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 11.35/11.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.60  thf('184', plain,
% 11.35/11.60      (((v2_struct_0 @ sk_A)
% 11.35/11.60        | (v2_struct_0 @ sk_C)
% 11.35/11.60        | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 11.35/11.60           (k2_tmap_1 @ sk_D @ sk_B @ 
% 11.35/11.60            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ sk_C) @ 
% 11.35/11.60           (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C))
% 11.35/11.60        | (v2_struct_0 @ sk_D)
% 11.35/11.60        | (v2_struct_0 @ sk_B))),
% 11.35/11.60      inference('demod', [status(thm)], ['58', '73', '182', '183'])).
% 11.35/11.60  thf('185', plain,
% 11.35/11.60      ((m1_subset_1 @ sk_E @ 
% 11.35/11.60        (k1_zfmisc_1 @ 
% 11.35/11.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 11.35/11.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.60  thf(dt_k2_tmap_1, axiom,
% 11.35/11.60    (![A:$i,B:$i,C:$i,D:$i]:
% 11.35/11.60     ( ( ( l1_struct_0 @ A ) & ( l1_struct_0 @ B ) & ( v1_funct_1 @ C ) & 
% 11.35/11.60         ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 11.35/11.60         ( m1_subset_1 @
% 11.35/11.60           C @ 
% 11.35/11.60           ( k1_zfmisc_1 @
% 11.35/11.60             ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 11.35/11.60         ( l1_struct_0 @ D ) ) =>
% 11.35/11.60       ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) ) & 
% 11.35/11.60         ( v1_funct_2 @
% 11.35/11.60           ( k2_tmap_1 @ A @ B @ C @ D ) @ ( u1_struct_0 @ D ) @ 
% 11.35/11.60           ( u1_struct_0 @ B ) ) & 
% 11.35/11.60         ( m1_subset_1 @
% 11.35/11.60           ( k2_tmap_1 @ A @ B @ C @ D ) @ 
% 11.35/11.60           ( k1_zfmisc_1 @
% 11.35/11.60             ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 11.35/11.60  thf('186', plain,
% 11.35/11.60      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 11.35/11.60         (~ (m1_subset_1 @ X21 @ 
% 11.35/11.60             (k1_zfmisc_1 @ 
% 11.35/11.61              (k2_zfmisc_1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X23))))
% 11.35/11.61          | ~ (v1_funct_2 @ X21 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X23))
% 11.35/11.61          | ~ (v1_funct_1 @ X21)
% 11.35/11.61          | ~ (l1_struct_0 @ X23)
% 11.35/11.61          | ~ (l1_struct_0 @ X22)
% 11.35/11.61          | ~ (l1_struct_0 @ X24)
% 11.35/11.61          | (v1_funct_1 @ (k2_tmap_1 @ X22 @ X23 @ X21 @ X24)))),
% 11.35/11.61      inference('cnf', [status(esa)], [dt_k2_tmap_1])).
% 11.35/11.61  thf('187', plain,
% 11.35/11.61      (![X0 : $i]:
% 11.35/11.61         ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 11.35/11.61          | ~ (l1_struct_0 @ X0)
% 11.35/11.61          | ~ (l1_struct_0 @ sk_A)
% 11.35/11.61          | ~ (l1_struct_0 @ sk_B)
% 11.35/11.61          | ~ (v1_funct_1 @ sk_E)
% 11.35/11.61          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 11.35/11.61      inference('sup-', [status(thm)], ['185', '186'])).
% 11.35/11.61  thf('188', plain, ((l1_pre_topc @ sk_A)),
% 11.35/11.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.61  thf(dt_l1_pre_topc, axiom,
% 11.35/11.61    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 11.35/11.61  thf('189', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 11.35/11.61      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 11.35/11.61  thf('190', plain, ((l1_struct_0 @ sk_A)),
% 11.35/11.61      inference('sup-', [status(thm)], ['188', '189'])).
% 11.35/11.61  thf('191', plain, ((l1_pre_topc @ sk_B)),
% 11.35/11.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.61  thf('192', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 11.35/11.61      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 11.35/11.61  thf('193', plain, ((l1_struct_0 @ sk_B)),
% 11.35/11.61      inference('sup-', [status(thm)], ['191', '192'])).
% 11.35/11.61  thf('194', plain, ((v1_funct_1 @ sk_E)),
% 11.35/11.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.61  thf('195', plain,
% 11.35/11.61      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 11.35/11.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.61  thf('196', plain,
% 11.35/11.61      (![X0 : $i]:
% 11.35/11.61         ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 11.35/11.61          | ~ (l1_struct_0 @ X0))),
% 11.35/11.61      inference('demod', [status(thm)], ['187', '190', '193', '194', '195'])).
% 11.35/11.61  thf('197', plain,
% 11.35/11.61      ((m1_subset_1 @ sk_E @ 
% 11.35/11.61        (k1_zfmisc_1 @ 
% 11.35/11.61         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 11.35/11.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.61  thf('198', plain,
% 11.35/11.61      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 11.35/11.61         (~ (m1_subset_1 @ X21 @ 
% 11.35/11.61             (k1_zfmisc_1 @ 
% 11.35/11.61              (k2_zfmisc_1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X23))))
% 11.35/11.61          | ~ (v1_funct_2 @ X21 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X23))
% 11.35/11.61          | ~ (v1_funct_1 @ X21)
% 11.35/11.61          | ~ (l1_struct_0 @ X23)
% 11.35/11.61          | ~ (l1_struct_0 @ X22)
% 11.35/11.61          | ~ (l1_struct_0 @ X24)
% 11.35/11.61          | (v1_funct_2 @ (k2_tmap_1 @ X22 @ X23 @ X21 @ X24) @ 
% 11.35/11.61             (u1_struct_0 @ X24) @ (u1_struct_0 @ X23)))),
% 11.35/11.61      inference('cnf', [status(esa)], [dt_k2_tmap_1])).
% 11.35/11.61  thf('199', plain,
% 11.35/11.61      (![X0 : $i]:
% 11.35/11.61         ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 11.35/11.61           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 11.35/11.61          | ~ (l1_struct_0 @ X0)
% 11.35/11.61          | ~ (l1_struct_0 @ sk_A)
% 11.35/11.61          | ~ (l1_struct_0 @ sk_B)
% 11.35/11.61          | ~ (v1_funct_1 @ sk_E)
% 11.35/11.61          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 11.35/11.61      inference('sup-', [status(thm)], ['197', '198'])).
% 11.35/11.61  thf('200', plain, ((l1_struct_0 @ sk_A)),
% 11.35/11.61      inference('sup-', [status(thm)], ['188', '189'])).
% 11.35/11.61  thf('201', plain, ((l1_struct_0 @ sk_B)),
% 11.35/11.61      inference('sup-', [status(thm)], ['191', '192'])).
% 11.35/11.61  thf('202', plain, ((v1_funct_1 @ sk_E)),
% 11.35/11.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.61  thf('203', plain,
% 11.35/11.61      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 11.35/11.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.61  thf('204', plain,
% 11.35/11.61      (![X0 : $i]:
% 11.35/11.61         ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 11.35/11.61           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 11.35/11.61          | ~ (l1_struct_0 @ X0))),
% 11.35/11.61      inference('demod', [status(thm)], ['199', '200', '201', '202', '203'])).
% 11.35/11.61  thf('205', plain,
% 11.35/11.61      ((m1_subset_1 @ sk_E @ 
% 11.35/11.61        (k1_zfmisc_1 @ 
% 11.35/11.61         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 11.35/11.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.61  thf('206', plain,
% 11.35/11.61      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 11.35/11.61         (~ (m1_subset_1 @ X21 @ 
% 11.35/11.61             (k1_zfmisc_1 @ 
% 11.35/11.61              (k2_zfmisc_1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X23))))
% 11.35/11.61          | ~ (v1_funct_2 @ X21 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X23))
% 11.35/11.61          | ~ (v1_funct_1 @ X21)
% 11.35/11.61          | ~ (l1_struct_0 @ X23)
% 11.35/11.61          | ~ (l1_struct_0 @ X22)
% 11.35/11.61          | ~ (l1_struct_0 @ X24)
% 11.35/11.61          | (m1_subset_1 @ (k2_tmap_1 @ X22 @ X23 @ X21 @ X24) @ 
% 11.35/11.61             (k1_zfmisc_1 @ 
% 11.35/11.61              (k2_zfmisc_1 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X23)))))),
% 11.35/11.61      inference('cnf', [status(esa)], [dt_k2_tmap_1])).
% 11.35/11.61  thf('207', plain,
% 11.35/11.61      (![X0 : $i]:
% 11.35/11.61         ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 11.35/11.61           (k1_zfmisc_1 @ 
% 11.35/11.61            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 11.35/11.61          | ~ (l1_struct_0 @ X0)
% 11.35/11.61          | ~ (l1_struct_0 @ sk_A)
% 11.35/11.61          | ~ (l1_struct_0 @ sk_B)
% 11.35/11.61          | ~ (v1_funct_1 @ sk_E)
% 11.35/11.61          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 11.35/11.61      inference('sup-', [status(thm)], ['205', '206'])).
% 11.35/11.61  thf('208', plain, ((l1_struct_0 @ sk_A)),
% 11.35/11.61      inference('sup-', [status(thm)], ['188', '189'])).
% 11.35/11.61  thf('209', plain, ((l1_struct_0 @ sk_B)),
% 11.35/11.61      inference('sup-', [status(thm)], ['191', '192'])).
% 11.35/11.61  thf('210', plain, ((v1_funct_1 @ sk_E)),
% 11.35/11.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.61  thf('211', plain,
% 11.35/11.61      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 11.35/11.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.61  thf('212', plain,
% 11.35/11.61      (![X0 : $i]:
% 11.35/11.61         ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 11.35/11.61           (k1_zfmisc_1 @ 
% 11.35/11.61            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 11.35/11.61          | ~ (l1_struct_0 @ X0))),
% 11.35/11.61      inference('demod', [status(thm)], ['207', '208', '209', '210', '211'])).
% 11.35/11.61  thf('213', plain,
% 11.35/11.61      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 11.35/11.61         (~ (m1_subset_1 @ X21 @ 
% 11.35/11.61             (k1_zfmisc_1 @ 
% 11.35/11.61              (k2_zfmisc_1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X23))))
% 11.35/11.61          | ~ (v1_funct_2 @ X21 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X23))
% 11.35/11.61          | ~ (v1_funct_1 @ X21)
% 11.35/11.61          | ~ (l1_struct_0 @ X23)
% 11.35/11.61          | ~ (l1_struct_0 @ X22)
% 11.35/11.61          | ~ (l1_struct_0 @ X24)
% 11.35/11.61          | (m1_subset_1 @ (k2_tmap_1 @ X22 @ X23 @ X21 @ X24) @ 
% 11.35/11.61             (k1_zfmisc_1 @ 
% 11.35/11.61              (k2_zfmisc_1 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X23)))))),
% 11.35/11.61      inference('cnf', [status(esa)], [dt_k2_tmap_1])).
% 11.35/11.61  thf('214', plain,
% 11.35/11.61      (![X0 : $i, X1 : $i]:
% 11.35/11.61         (~ (l1_struct_0 @ X0)
% 11.35/11.61          | (m1_subset_1 @ 
% 11.35/11.61             (k2_tmap_1 @ X0 @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 11.35/11.61              X1) @ 
% 11.35/11.61             (k1_zfmisc_1 @ 
% 11.35/11.61              (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B))))
% 11.35/11.61          | ~ (l1_struct_0 @ X1)
% 11.35/11.61          | ~ (l1_struct_0 @ X0)
% 11.35/11.61          | ~ (l1_struct_0 @ sk_B)
% 11.35/11.61          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 11.35/11.61          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 11.35/11.61               (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 11.35/11.61      inference('sup-', [status(thm)], ['212', '213'])).
% 11.35/11.61  thf('215', plain, ((l1_struct_0 @ sk_B)),
% 11.35/11.61      inference('sup-', [status(thm)], ['191', '192'])).
% 11.35/11.61  thf('216', plain,
% 11.35/11.61      (![X0 : $i, X1 : $i]:
% 11.35/11.61         (~ (l1_struct_0 @ X0)
% 11.35/11.61          | (m1_subset_1 @ 
% 11.35/11.61             (k2_tmap_1 @ X0 @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 11.35/11.61              X1) @ 
% 11.35/11.61             (k1_zfmisc_1 @ 
% 11.35/11.61              (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B))))
% 11.35/11.61          | ~ (l1_struct_0 @ X1)
% 11.35/11.61          | ~ (l1_struct_0 @ X0)
% 11.35/11.61          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 11.35/11.61          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 11.35/11.61               (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 11.35/11.61      inference('demod', [status(thm)], ['214', '215'])).
% 11.35/11.61  thf('217', plain,
% 11.35/11.61      (![X0 : $i, X1 : $i]:
% 11.35/11.61         (~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 11.35/11.61             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 11.35/11.61          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 11.35/11.61          | ~ (l1_struct_0 @ X1)
% 11.35/11.61          | (m1_subset_1 @ 
% 11.35/11.61             (k2_tmap_1 @ X0 @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 11.35/11.61              X1) @ 
% 11.35/11.61             (k1_zfmisc_1 @ 
% 11.35/11.61              (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B))))
% 11.35/11.61          | ~ (l1_struct_0 @ X0))),
% 11.35/11.61      inference('simplify', [status(thm)], ['216'])).
% 11.35/11.61  thf('218', plain,
% 11.35/11.61      (![X0 : $i, X1 : $i]:
% 11.35/11.61         (~ (l1_struct_0 @ X0)
% 11.35/11.61          | ~ (l1_struct_0 @ X0)
% 11.35/11.61          | (m1_subset_1 @ 
% 11.35/11.61             (k2_tmap_1 @ X0 @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 11.35/11.61              X1) @ 
% 11.35/11.61             (k1_zfmisc_1 @ 
% 11.35/11.61              (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B))))
% 11.35/11.61          | ~ (l1_struct_0 @ X1)
% 11.35/11.61          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0)))),
% 11.35/11.61      inference('sup-', [status(thm)], ['204', '217'])).
% 11.35/11.61  thf('219', plain,
% 11.35/11.61      (![X0 : $i, X1 : $i]:
% 11.35/11.61         (~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 11.35/11.61          | ~ (l1_struct_0 @ X1)
% 11.35/11.61          | (m1_subset_1 @ 
% 11.35/11.61             (k2_tmap_1 @ X0 @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 11.35/11.61              X1) @ 
% 11.35/11.61             (k1_zfmisc_1 @ 
% 11.35/11.61              (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B))))
% 11.35/11.61          | ~ (l1_struct_0 @ X0))),
% 11.35/11.61      inference('simplify', [status(thm)], ['218'])).
% 11.35/11.61  thf('220', plain,
% 11.35/11.61      (![X0 : $i, X1 : $i]:
% 11.35/11.61         (~ (l1_struct_0 @ X0)
% 11.35/11.61          | ~ (l1_struct_0 @ X0)
% 11.35/11.61          | (m1_subset_1 @ 
% 11.35/11.61             (k2_tmap_1 @ X0 @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 11.35/11.61              X1) @ 
% 11.35/11.61             (k1_zfmisc_1 @ 
% 11.35/11.61              (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B))))
% 11.35/11.61          | ~ (l1_struct_0 @ X1))),
% 11.35/11.61      inference('sup-', [status(thm)], ['196', '219'])).
% 11.35/11.61  thf('221', plain,
% 11.35/11.61      (![X0 : $i, X1 : $i]:
% 11.35/11.61         (~ (l1_struct_0 @ X1)
% 11.35/11.61          | (m1_subset_1 @ 
% 11.35/11.61             (k2_tmap_1 @ X0 @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 11.35/11.61              X1) @ 
% 11.35/11.61             (k1_zfmisc_1 @ 
% 11.35/11.61              (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B))))
% 11.35/11.61          | ~ (l1_struct_0 @ X0))),
% 11.35/11.61      inference('simplify', [status(thm)], ['220'])).
% 11.35/11.61  thf(redefinition_r2_funct_2, axiom,
% 11.35/11.61    (![A:$i,B:$i,C:$i,D:$i]:
% 11.35/11.61     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 11.35/11.61         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 11.35/11.61         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 11.35/11.61         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 11.35/11.61       ( ( r2_funct_2 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 11.35/11.61  thf('222', plain,
% 11.35/11.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 11.35/11.61         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 11.35/11.61          | ~ (v1_funct_2 @ X0 @ X1 @ X2)
% 11.35/11.61          | ~ (v1_funct_1 @ X0)
% 11.35/11.61          | ~ (v1_funct_1 @ X3)
% 11.35/11.61          | ~ (v1_funct_2 @ X3 @ X1 @ X2)
% 11.35/11.61          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 11.35/11.61          | ((X0) = (X3))
% 11.35/11.61          | ~ (r2_funct_2 @ X1 @ X2 @ X0 @ X3))),
% 11.35/11.61      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 11.35/11.61  thf('223', plain,
% 11.35/11.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.35/11.61         (~ (l1_struct_0 @ X1)
% 11.35/11.61          | ~ (l1_struct_0 @ X0)
% 11.35/11.61          | ~ (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 11.35/11.61               (k2_tmap_1 @ X1 @ sk_B @ 
% 11.35/11.61                (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1) @ X0) @ 
% 11.35/11.61               X2)
% 11.35/11.61          | ((k2_tmap_1 @ X1 @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1) @ 
% 11.35/11.61              X0) = (X2))
% 11.35/11.61          | ~ (m1_subset_1 @ X2 @ 
% 11.35/11.61               (k1_zfmisc_1 @ 
% 11.35/11.61                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 11.35/11.61          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 11.35/11.61          | ~ (v1_funct_1 @ X2)
% 11.35/11.61          | ~ (v1_funct_1 @ 
% 11.35/11.61               (k2_tmap_1 @ X1 @ sk_B @ 
% 11.35/11.61                (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1) @ X0))
% 11.35/11.61          | ~ (v1_funct_2 @ 
% 11.35/11.61               (k2_tmap_1 @ X1 @ sk_B @ 
% 11.35/11.61                (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1) @ X0) @ 
% 11.35/11.61               (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 11.35/11.61      inference('sup-', [status(thm)], ['221', '222'])).
% 11.35/11.61  thf('224', plain,
% 11.35/11.61      (((v2_struct_0 @ sk_B)
% 11.35/11.61        | (v2_struct_0 @ sk_D)
% 11.35/11.61        | (v2_struct_0 @ sk_C)
% 11.35/11.61        | (v2_struct_0 @ sk_A)
% 11.35/11.61        | ~ (v1_funct_2 @ 
% 11.35/11.61             (k2_tmap_1 @ sk_D @ sk_B @ 
% 11.35/11.61              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ sk_C) @ 
% 11.35/11.61             (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 11.35/11.61        | ~ (v1_funct_1 @ 
% 11.35/11.61             (k2_tmap_1 @ sk_D @ sk_B @ 
% 11.35/11.61              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ sk_C))
% 11.35/11.61        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C))
% 11.35/11.61        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 11.35/11.61             (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 11.35/11.61        | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 11.35/11.61             (k1_zfmisc_1 @ 
% 11.35/11.61              (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 11.35/11.61        | ((k2_tmap_1 @ sk_D @ sk_B @ 
% 11.35/11.61            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ sk_C)
% 11.35/11.61            = (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C))
% 11.35/11.61        | ~ (l1_struct_0 @ sk_C)
% 11.35/11.61        | ~ (l1_struct_0 @ sk_D))),
% 11.35/11.61      inference('sup-', [status(thm)], ['184', '223'])).
% 11.35/11.61  thf('225', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 11.35/11.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.61  thf('226', plain,
% 11.35/11.61      (![X30 : $i]: ((m1_pre_topc @ X30 @ X30) | ~ (l1_pre_topc @ X30))),
% 11.35/11.61      inference('cnf', [status(esa)], [t2_tsep_1])).
% 11.35/11.61  thf('227', plain,
% 11.35/11.61      ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 11.35/11.61        (k1_zfmisc_1 @ 
% 11.35/11.61         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 11.35/11.61      inference('clc', [status(thm)], ['95', '96'])).
% 11.35/11.61  thf('228', plain,
% 11.35/11.61      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 11.35/11.61         (~ (m1_pre_topc @ X25 @ X26)
% 11.35/11.61          | ~ (m1_pre_topc @ X27 @ X26)
% 11.35/11.61          | ~ (l1_pre_topc @ X28)
% 11.35/11.61          | ~ (v2_pre_topc @ X28)
% 11.35/11.61          | (v2_struct_0 @ X28)
% 11.35/11.61          | ~ (l1_pre_topc @ X26)
% 11.35/11.61          | ~ (v2_pre_topc @ X26)
% 11.35/11.61          | (v2_struct_0 @ X26)
% 11.35/11.61          | ~ (v1_funct_1 @ X29)
% 11.35/11.61          | ~ (v1_funct_2 @ X29 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X28))
% 11.35/11.61          | ~ (m1_subset_1 @ X29 @ 
% 11.35/11.61               (k1_zfmisc_1 @ 
% 11.35/11.61                (k2_zfmisc_1 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X28))))
% 11.35/11.61          | (v1_funct_2 @ (k3_tmap_1 @ X26 @ X28 @ X27 @ X25 @ X29) @ 
% 11.35/11.61             (u1_struct_0 @ X25) @ (u1_struct_0 @ X28)))),
% 11.35/11.61      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 11.35/11.61  thf('229', plain,
% 11.35/11.61      (![X0 : $i, X1 : $i]:
% 11.35/11.61         ((v1_funct_2 @ 
% 11.35/11.61           (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ 
% 11.35/11.61            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 11.35/11.61           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 11.35/11.61          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 11.35/11.61               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 11.35/11.61          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))
% 11.35/11.61          | (v2_struct_0 @ X1)
% 11.35/11.61          | ~ (v2_pre_topc @ X1)
% 11.35/11.61          | ~ (l1_pre_topc @ X1)
% 11.35/11.61          | (v2_struct_0 @ sk_B)
% 11.35/11.61          | ~ (v2_pre_topc @ sk_B)
% 11.35/11.61          | ~ (l1_pre_topc @ sk_B)
% 11.35/11.61          | ~ (m1_pre_topc @ sk_D @ X1)
% 11.35/11.61          | ~ (m1_pre_topc @ X0 @ X1))),
% 11.35/11.61      inference('sup-', [status(thm)], ['227', '228'])).
% 11.35/11.61  thf('230', plain,
% 11.35/11.61      ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 11.35/11.61        (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 11.35/11.61      inference('clc', [status(thm)], ['141', '142'])).
% 11.35/11.61  thf('231', plain, ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))),
% 11.35/11.61      inference('clc', [status(thm)], ['119', '120'])).
% 11.35/11.61  thf('232', plain, ((v2_pre_topc @ sk_B)),
% 11.35/11.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.61  thf('233', plain, ((l1_pre_topc @ sk_B)),
% 11.35/11.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.61  thf('234', plain,
% 11.35/11.61      (![X0 : $i, X1 : $i]:
% 11.35/11.61         ((v1_funct_2 @ 
% 11.35/11.61           (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ 
% 11.35/11.61            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 11.35/11.61           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 11.35/11.61          | (v2_struct_0 @ X1)
% 11.35/11.61          | ~ (v2_pre_topc @ X1)
% 11.35/11.61          | ~ (l1_pre_topc @ X1)
% 11.35/11.61          | (v2_struct_0 @ sk_B)
% 11.35/11.61          | ~ (m1_pre_topc @ sk_D @ X1)
% 11.35/11.61          | ~ (m1_pre_topc @ X0 @ X1))),
% 11.35/11.61      inference('demod', [status(thm)], ['229', '230', '231', '232', '233'])).
% 11.35/11.61  thf('235', plain,
% 11.35/11.61      (![X0 : $i]:
% 11.35/11.61         (~ (l1_pre_topc @ sk_D)
% 11.35/11.61          | ~ (m1_pre_topc @ X0 @ sk_D)
% 11.35/11.61          | (v2_struct_0 @ sk_B)
% 11.35/11.61          | ~ (l1_pre_topc @ sk_D)
% 11.35/11.61          | ~ (v2_pre_topc @ sk_D)
% 11.35/11.61          | (v2_struct_0 @ sk_D)
% 11.35/11.61          | (v1_funct_2 @ 
% 11.35/11.61             (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ 
% 11.35/11.61              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 11.35/11.61             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 11.35/11.61      inference('sup-', [status(thm)], ['226', '234'])).
% 11.35/11.61  thf('236', plain, ((l1_pre_topc @ sk_D)),
% 11.35/11.61      inference('demod', [status(thm)], ['164', '165'])).
% 11.35/11.61  thf('237', plain, ((l1_pre_topc @ sk_D)),
% 11.35/11.61      inference('demod', [status(thm)], ['164', '165'])).
% 11.35/11.61  thf('238', plain, ((v2_pre_topc @ sk_D)),
% 11.35/11.61      inference('demod', [status(thm)], ['158', '159', '160'])).
% 11.35/11.61  thf('239', plain,
% 11.35/11.61      (![X0 : $i]:
% 11.35/11.61         (~ (m1_pre_topc @ X0 @ sk_D)
% 11.35/11.61          | (v2_struct_0 @ sk_B)
% 11.35/11.61          | (v2_struct_0 @ sk_D)
% 11.35/11.61          | (v1_funct_2 @ 
% 11.35/11.61             (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ 
% 11.35/11.61              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 11.35/11.61             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 11.35/11.61      inference('demod', [status(thm)], ['235', '236', '237', '238'])).
% 11.35/11.61  thf('240', plain,
% 11.35/11.61      (((v1_funct_2 @ 
% 11.35/11.61         (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ 
% 11.35/11.61          (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 11.35/11.61         (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 11.35/11.61        | (v2_struct_0 @ sk_D)
% 11.35/11.61        | (v2_struct_0 @ sk_B))),
% 11.35/11.61      inference('sup-', [status(thm)], ['225', '239'])).
% 11.35/11.61  thf('241', plain, (~ (v2_struct_0 @ sk_D)),
% 11.35/11.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.61  thf('242', plain,
% 11.35/11.61      (((v2_struct_0 @ sk_B)
% 11.35/11.61        | (v1_funct_2 @ 
% 11.35/11.61           (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ 
% 11.35/11.61            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 11.35/11.61           (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 11.35/11.61      inference('clc', [status(thm)], ['240', '241'])).
% 11.35/11.61  thf('243', plain, (~ (v2_struct_0 @ sk_B)),
% 11.35/11.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.61  thf('244', plain,
% 11.35/11.61      ((v1_funct_2 @ 
% 11.35/11.61        (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ 
% 11.35/11.61         (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 11.35/11.61        (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 11.35/11.61      inference('clc', [status(thm)], ['242', '243'])).
% 11.35/11.61  thf('245', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 11.35/11.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.61  thf('246', plain,
% 11.35/11.61      (![X30 : $i]: ((m1_pre_topc @ X30 @ X30) | ~ (l1_pre_topc @ X30))),
% 11.35/11.61      inference('cnf', [status(esa)], [t2_tsep_1])).
% 11.35/11.61  thf('247', plain,
% 11.35/11.61      (![X0 : $i, X1 : $i]:
% 11.35/11.61         ((v2_struct_0 @ X0)
% 11.35/11.61          | ~ (v2_pre_topc @ X0)
% 11.35/11.61          | ~ (l1_pre_topc @ X0)
% 11.35/11.61          | ~ (m1_pre_topc @ sk_D @ X0)
% 11.35/11.61          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ 
% 11.35/11.61              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))
% 11.35/11.61              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 11.35/11.61                 (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ (u1_struct_0 @ X1)))
% 11.35/11.61          | ~ (m1_pre_topc @ X1 @ sk_D)
% 11.35/11.61          | ~ (m1_pre_topc @ X1 @ X0)
% 11.35/11.61          | (v2_struct_0 @ sk_B))),
% 11.35/11.61      inference('demod', [status(thm)], ['99', '121', '143', '144', '145'])).
% 11.35/11.61  thf('248', plain,
% 11.35/11.61      (![X0 : $i]:
% 11.35/11.61         (~ (l1_pre_topc @ sk_D)
% 11.35/11.61          | (v2_struct_0 @ sk_B)
% 11.35/11.61          | ~ (m1_pre_topc @ X0 @ sk_D)
% 11.35/11.61          | ~ (m1_pre_topc @ X0 @ sk_D)
% 11.35/11.61          | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ 
% 11.35/11.61              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))
% 11.35/11.61              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 11.35/11.61                 (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ (u1_struct_0 @ X0)))
% 11.35/11.61          | ~ (l1_pre_topc @ sk_D)
% 11.35/11.61          | ~ (v2_pre_topc @ sk_D)
% 11.35/11.61          | (v2_struct_0 @ sk_D))),
% 11.35/11.61      inference('sup-', [status(thm)], ['246', '247'])).
% 11.35/11.61  thf('249', plain, ((l1_pre_topc @ sk_D)),
% 11.35/11.61      inference('demod', [status(thm)], ['164', '165'])).
% 11.35/11.61  thf('250', plain, ((l1_pre_topc @ sk_D)),
% 11.35/11.61      inference('demod', [status(thm)], ['164', '165'])).
% 11.35/11.61  thf('251', plain, ((v2_pre_topc @ sk_D)),
% 11.35/11.61      inference('demod', [status(thm)], ['158', '159', '160'])).
% 11.35/11.61  thf('252', plain,
% 11.35/11.61      (![X0 : $i]:
% 11.35/11.61         ((v2_struct_0 @ sk_B)
% 11.35/11.61          | ~ (m1_pre_topc @ X0 @ sk_D)
% 11.35/11.61          | ~ (m1_pre_topc @ X0 @ sk_D)
% 11.35/11.61          | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ 
% 11.35/11.61              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))
% 11.35/11.61              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 11.35/11.61                 (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ (u1_struct_0 @ X0)))
% 11.35/11.61          | (v2_struct_0 @ sk_D))),
% 11.35/11.61      inference('demod', [status(thm)], ['248', '249', '250', '251'])).
% 11.35/11.61  thf('253', plain,
% 11.35/11.61      (![X0 : $i]:
% 11.35/11.61         ((v2_struct_0 @ sk_D)
% 11.35/11.61          | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ 
% 11.35/11.61              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))
% 11.35/11.61              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 11.35/11.61                 (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ (u1_struct_0 @ X0)))
% 11.35/11.61          | ~ (m1_pre_topc @ X0 @ sk_D)
% 11.35/11.61          | (v2_struct_0 @ sk_B))),
% 11.35/11.61      inference('simplify', [status(thm)], ['252'])).
% 11.35/11.61  thf('254', plain,
% 11.35/11.61      (((v2_struct_0 @ sk_B)
% 11.35/11.61        | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ 
% 11.35/11.61            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))
% 11.35/11.61            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 11.35/11.61               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ (u1_struct_0 @ sk_C)))
% 11.35/11.61        | (v2_struct_0 @ sk_D))),
% 11.35/11.61      inference('sup-', [status(thm)], ['245', '253'])).
% 11.35/11.61  thf('255', plain, (~ (v2_struct_0 @ sk_B)),
% 11.35/11.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.61  thf('256', plain,
% 11.35/11.61      (((v2_struct_0 @ sk_D)
% 11.35/11.61        | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ 
% 11.35/11.61            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))
% 11.35/11.61            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 11.35/11.61               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ (u1_struct_0 @ sk_C))))),
% 11.35/11.61      inference('clc', [status(thm)], ['254', '255'])).
% 11.35/11.61  thf('257', plain, (~ (v2_struct_0 @ sk_D)),
% 11.35/11.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.61  thf('258', plain,
% 11.35/11.61      (((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ 
% 11.35/11.61         (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))
% 11.35/11.61         = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 11.35/11.61            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ (u1_struct_0 @ sk_C)))),
% 11.35/11.61      inference('clc', [status(thm)], ['256', '257'])).
% 11.35/11.61  thf('259', plain,
% 11.35/11.61      (((k2_tmap_1 @ sk_D @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 11.35/11.61         sk_C)
% 11.35/11.61         = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 11.35/11.61            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ (u1_struct_0 @ sk_C)))),
% 11.35/11.61      inference('clc', [status(thm)], ['174', '175'])).
% 11.35/11.61  thf('260', plain,
% 11.35/11.61      (((k2_tmap_1 @ sk_D @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 11.35/11.61         sk_C)
% 11.35/11.61         = (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ 
% 11.35/11.61            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)))),
% 11.35/11.61      inference('sup+', [status(thm)], ['258', '259'])).
% 11.35/11.61  thf('261', plain,
% 11.35/11.61      ((v1_funct_2 @ 
% 11.35/11.61        (k2_tmap_1 @ sk_D @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 11.35/11.61         sk_C) @ 
% 11.35/11.61        (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 11.35/11.61      inference('demod', [status(thm)], ['244', '260'])).
% 11.35/11.61  thf('262', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 11.35/11.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.61  thf('263', plain,
% 11.35/11.61      (![X30 : $i]: ((m1_pre_topc @ X30 @ X30) | ~ (l1_pre_topc @ X30))),
% 11.35/11.61      inference('cnf', [status(esa)], [t2_tsep_1])).
% 11.35/11.61  thf('264', plain,
% 11.35/11.61      ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 11.35/11.61        (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 11.35/11.61      inference('clc', [status(thm)], ['141', '142'])).
% 11.35/11.61  thf('265', plain,
% 11.35/11.61      (![X0 : $i]:
% 11.35/11.61         ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 11.35/11.61           (k1_zfmisc_1 @ 
% 11.35/11.61            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 11.35/11.61          | ~ (l1_struct_0 @ X0))),
% 11.35/11.61      inference('demod', [status(thm)], ['207', '208', '209', '210', '211'])).
% 11.35/11.61  thf('266', plain,
% 11.35/11.61      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 11.35/11.61         (~ (m1_pre_topc @ X25 @ X26)
% 11.35/11.61          | ~ (m1_pre_topc @ X27 @ X26)
% 11.35/11.61          | ~ (l1_pre_topc @ X28)
% 11.35/11.61          | ~ (v2_pre_topc @ X28)
% 11.35/11.61          | (v2_struct_0 @ X28)
% 11.35/11.61          | ~ (l1_pre_topc @ X26)
% 11.35/11.61          | ~ (v2_pre_topc @ X26)
% 11.35/11.61          | (v2_struct_0 @ X26)
% 11.35/11.61          | ~ (v1_funct_1 @ X29)
% 11.35/11.61          | ~ (v1_funct_2 @ X29 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X28))
% 11.35/11.61          | ~ (m1_subset_1 @ X29 @ 
% 11.35/11.61               (k1_zfmisc_1 @ 
% 11.35/11.61                (k2_zfmisc_1 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X28))))
% 11.35/11.61          | (v1_funct_1 @ (k3_tmap_1 @ X26 @ X28 @ X27 @ X25 @ X29)))),
% 11.35/11.61      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 11.35/11.61  thf('267', plain,
% 11.35/11.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.35/11.61         (~ (l1_struct_0 @ X0)
% 11.35/11.61          | (v1_funct_1 @ 
% 11.35/11.61             (k3_tmap_1 @ X2 @ sk_B @ X0 @ X1 @ 
% 11.35/11.61              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0)))
% 11.35/11.61          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 11.35/11.61               (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 11.35/11.61          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 11.35/11.61          | (v2_struct_0 @ X2)
% 11.35/11.61          | ~ (v2_pre_topc @ X2)
% 11.35/11.61          | ~ (l1_pre_topc @ X2)
% 11.35/11.61          | (v2_struct_0 @ sk_B)
% 11.35/11.61          | ~ (v2_pre_topc @ sk_B)
% 11.35/11.61          | ~ (l1_pre_topc @ sk_B)
% 11.35/11.61          | ~ (m1_pre_topc @ X0 @ X2)
% 11.35/11.61          | ~ (m1_pre_topc @ X1 @ X2))),
% 11.35/11.61      inference('sup-', [status(thm)], ['265', '266'])).
% 11.35/11.61  thf('268', plain, ((v2_pre_topc @ sk_B)),
% 11.35/11.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.61  thf('269', plain, ((l1_pre_topc @ sk_B)),
% 11.35/11.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.61  thf('270', plain,
% 11.35/11.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.35/11.61         (~ (l1_struct_0 @ X0)
% 11.35/11.61          | (v1_funct_1 @ 
% 11.35/11.61             (k3_tmap_1 @ X2 @ sk_B @ X0 @ X1 @ 
% 11.35/11.61              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0)))
% 11.35/11.61          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 11.35/11.61               (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 11.35/11.61          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 11.35/11.61          | (v2_struct_0 @ X2)
% 11.35/11.61          | ~ (v2_pre_topc @ X2)
% 11.35/11.61          | ~ (l1_pre_topc @ X2)
% 11.35/11.61          | (v2_struct_0 @ sk_B)
% 11.35/11.61          | ~ (m1_pre_topc @ X0 @ X2)
% 11.35/11.61          | ~ (m1_pre_topc @ X1 @ X2))),
% 11.35/11.61      inference('demod', [status(thm)], ['267', '268', '269'])).
% 11.35/11.61  thf('271', plain,
% 11.35/11.61      (![X0 : $i, X1 : $i]:
% 11.35/11.61         (~ (m1_pre_topc @ X1 @ X0)
% 11.35/11.61          | ~ (m1_pre_topc @ sk_D @ X0)
% 11.35/11.61          | (v2_struct_0 @ sk_B)
% 11.35/11.61          | ~ (l1_pre_topc @ X0)
% 11.35/11.61          | ~ (v2_pre_topc @ X0)
% 11.35/11.61          | (v2_struct_0 @ X0)
% 11.35/11.61          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))
% 11.35/11.61          | (v1_funct_1 @ 
% 11.35/11.61             (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ 
% 11.35/11.61              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)))
% 11.35/11.61          | ~ (l1_struct_0 @ sk_D))),
% 11.35/11.61      inference('sup-', [status(thm)], ['264', '270'])).
% 11.35/11.61  thf('272', plain, ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))),
% 11.35/11.61      inference('clc', [status(thm)], ['119', '120'])).
% 11.35/11.61  thf('273', plain, ((l1_pre_topc @ sk_D)),
% 11.35/11.61      inference('demod', [status(thm)], ['164', '165'])).
% 11.35/11.61  thf('274', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 11.35/11.61      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 11.35/11.61  thf('275', plain, ((l1_struct_0 @ sk_D)),
% 11.35/11.61      inference('sup-', [status(thm)], ['273', '274'])).
% 11.35/11.61  thf('276', plain,
% 11.35/11.61      (![X0 : $i, X1 : $i]:
% 11.35/11.61         (~ (m1_pre_topc @ X1 @ X0)
% 11.35/11.61          | ~ (m1_pre_topc @ sk_D @ X0)
% 11.35/11.61          | (v2_struct_0 @ sk_B)
% 11.35/11.61          | ~ (l1_pre_topc @ X0)
% 11.35/11.61          | ~ (v2_pre_topc @ X0)
% 11.35/11.61          | (v2_struct_0 @ X0)
% 11.35/11.61          | (v1_funct_1 @ 
% 11.35/11.61             (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ 
% 11.35/11.61              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))))),
% 11.35/11.61      inference('demod', [status(thm)], ['271', '272', '275'])).
% 11.35/11.61  thf('277', plain,
% 11.35/11.61      (![X0 : $i]:
% 11.35/11.61         (~ (l1_pre_topc @ sk_D)
% 11.35/11.61          | (v1_funct_1 @ 
% 11.35/11.61             (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ 
% 11.35/11.61              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)))
% 11.35/11.61          | (v2_struct_0 @ sk_D)
% 11.35/11.61          | ~ (v2_pre_topc @ sk_D)
% 11.35/11.61          | ~ (l1_pre_topc @ sk_D)
% 11.35/11.61          | (v2_struct_0 @ sk_B)
% 11.35/11.61          | ~ (m1_pre_topc @ X0 @ sk_D))),
% 11.35/11.61      inference('sup-', [status(thm)], ['263', '276'])).
% 11.35/11.61  thf('278', plain, ((l1_pre_topc @ sk_D)),
% 11.35/11.61      inference('demod', [status(thm)], ['164', '165'])).
% 11.35/11.61  thf('279', plain, ((v2_pre_topc @ sk_D)),
% 11.35/11.61      inference('demod', [status(thm)], ['158', '159', '160'])).
% 11.35/11.61  thf('280', plain, ((l1_pre_topc @ sk_D)),
% 11.35/11.61      inference('demod', [status(thm)], ['164', '165'])).
% 11.35/11.61  thf('281', plain,
% 11.35/11.61      (![X0 : $i]:
% 11.35/11.61         ((v1_funct_1 @ 
% 11.35/11.61           (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ 
% 11.35/11.61            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)))
% 11.35/11.61          | (v2_struct_0 @ sk_D)
% 11.35/11.61          | (v2_struct_0 @ sk_B)
% 11.35/11.61          | ~ (m1_pre_topc @ X0 @ sk_D))),
% 11.35/11.61      inference('demod', [status(thm)], ['277', '278', '279', '280'])).
% 11.35/11.61  thf('282', plain,
% 11.35/11.61      (((v2_struct_0 @ sk_B)
% 11.35/11.61        | (v2_struct_0 @ sk_D)
% 11.35/11.61        | (v1_funct_1 @ 
% 11.35/11.61           (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ 
% 11.35/11.61            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))))),
% 11.35/11.61      inference('sup-', [status(thm)], ['262', '281'])).
% 11.35/11.61  thf('283', plain, (~ (v2_struct_0 @ sk_B)),
% 11.35/11.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.61  thf('284', plain,
% 11.35/11.61      (((v1_funct_1 @ 
% 11.35/11.61         (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ 
% 11.35/11.61          (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)))
% 11.35/11.61        | (v2_struct_0 @ sk_D))),
% 11.35/11.61      inference('clc', [status(thm)], ['282', '283'])).
% 11.35/11.61  thf('285', plain, (~ (v2_struct_0 @ sk_D)),
% 11.35/11.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.61  thf('286', plain,
% 11.35/11.61      ((v1_funct_1 @ 
% 11.35/11.61        (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ 
% 11.35/11.61         (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)))),
% 11.35/11.61      inference('clc', [status(thm)], ['284', '285'])).
% 11.35/11.61  thf('287', plain,
% 11.35/11.61      (((k2_tmap_1 @ sk_D @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 11.35/11.61         sk_C)
% 11.35/11.61         = (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ 
% 11.35/11.61            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)))),
% 11.35/11.61      inference('sup+', [status(thm)], ['258', '259'])).
% 11.35/11.61  thf('288', plain,
% 11.35/11.61      ((v1_funct_1 @ 
% 11.35/11.61        (k2_tmap_1 @ sk_D @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 11.35/11.61         sk_C))),
% 11.35/11.61      inference('demod', [status(thm)], ['286', '287'])).
% 11.35/11.61  thf('289', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 11.35/11.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.61  thf('290', plain,
% 11.35/11.61      (![X0 : $i]:
% 11.35/11.61         (~ (m1_pre_topc @ X0 @ sk_A)
% 11.35/11.61          | (v2_struct_0 @ sk_B)
% 11.35/11.61          | (v2_struct_0 @ sk_A)
% 11.35/11.61          | (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E)))),
% 11.35/11.61      inference('demod', [status(thm)], ['110', '111', '112', '113'])).
% 11.35/11.61  thf('291', plain,
% 11.35/11.61      (((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E))
% 11.35/11.61        | (v2_struct_0 @ sk_A)
% 11.35/11.61        | (v2_struct_0 @ sk_B))),
% 11.35/11.61      inference('sup-', [status(thm)], ['289', '290'])).
% 11.35/11.61  thf('292', plain,
% 11.35/11.61      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C)
% 11.35/11.61         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E))),
% 11.35/11.61      inference('sup+', [status(thm)], ['39', '55'])).
% 11.35/11.61  thf('293', plain,
% 11.35/11.61      (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C))
% 11.35/11.61        | (v2_struct_0 @ sk_A)
% 11.35/11.61        | (v2_struct_0 @ sk_B))),
% 11.35/11.61      inference('demod', [status(thm)], ['291', '292'])).
% 11.35/11.61  thf('294', plain, (~ (v2_struct_0 @ sk_A)),
% 11.35/11.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.61  thf('295', plain,
% 11.35/11.61      (((v2_struct_0 @ sk_B)
% 11.35/11.61        | (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C)))),
% 11.35/11.61      inference('clc', [status(thm)], ['293', '294'])).
% 11.35/11.61  thf('296', plain, (~ (v2_struct_0 @ sk_B)),
% 11.35/11.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.61  thf('297', plain, ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C))),
% 11.35/11.61      inference('clc', [status(thm)], ['295', '296'])).
% 11.35/11.61  thf('298', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 11.35/11.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.61  thf('299', plain,
% 11.35/11.61      (![X0 : $i]:
% 11.35/11.61         (~ (m1_pre_topc @ X0 @ sk_A)
% 11.35/11.61          | (v2_struct_0 @ sk_B)
% 11.35/11.61          | (v2_struct_0 @ sk_A)
% 11.35/11.61          | (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 11.35/11.61             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 11.35/11.61      inference('demod', [status(thm)], ['132', '133', '134', '135'])).
% 11.35/11.61  thf('300', plain,
% 11.35/11.61      (((v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E) @ 
% 11.35/11.61         (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 11.35/11.61        | (v2_struct_0 @ sk_A)
% 11.35/11.61        | (v2_struct_0 @ sk_B))),
% 11.35/11.61      inference('sup-', [status(thm)], ['298', '299'])).
% 11.35/11.61  thf('301', plain,
% 11.35/11.61      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C)
% 11.35/11.61         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E))),
% 11.35/11.61      inference('sup+', [status(thm)], ['39', '55'])).
% 11.35/11.61  thf('302', plain,
% 11.35/11.61      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 11.35/11.61         (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 11.35/11.61        | (v2_struct_0 @ sk_A)
% 11.35/11.61        | (v2_struct_0 @ sk_B))),
% 11.35/11.61      inference('demod', [status(thm)], ['300', '301'])).
% 11.35/11.61  thf('303', plain, (~ (v2_struct_0 @ sk_A)),
% 11.35/11.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.61  thf('304', plain,
% 11.35/11.61      (((v2_struct_0 @ sk_B)
% 11.35/11.61        | (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 11.35/11.61           (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 11.35/11.61      inference('clc', [status(thm)], ['302', '303'])).
% 11.35/11.61  thf('305', plain, (~ (v2_struct_0 @ sk_B)),
% 11.35/11.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.61  thf('306', plain,
% 11.35/11.61      ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 11.35/11.61        (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 11.35/11.61      inference('clc', [status(thm)], ['304', '305'])).
% 11.35/11.61  thf('307', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 11.35/11.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.61  thf('308', plain,
% 11.35/11.61      (![X0 : $i]:
% 11.35/11.61         (~ (m1_pre_topc @ X0 @ sk_A)
% 11.35/11.61          | (v2_struct_0 @ sk_B)
% 11.35/11.61          | (v2_struct_0 @ sk_A)
% 11.35/11.61          | (m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 11.35/11.61             (k1_zfmisc_1 @ 
% 11.35/11.61              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))))),
% 11.35/11.61      inference('demod', [status(thm)], ['86', '87', '88', '89'])).
% 11.35/11.61  thf('309', plain,
% 11.35/11.61      (((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E) @ 
% 11.35/11.61         (k1_zfmisc_1 @ 
% 11.35/11.61          (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 11.35/11.61        | (v2_struct_0 @ sk_A)
% 11.35/11.61        | (v2_struct_0 @ sk_B))),
% 11.35/11.61      inference('sup-', [status(thm)], ['307', '308'])).
% 11.35/11.61  thf('310', plain,
% 11.35/11.61      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C)
% 11.35/11.61         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E))),
% 11.35/11.61      inference('sup+', [status(thm)], ['39', '55'])).
% 11.35/11.61  thf('311', plain,
% 11.35/11.61      (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 11.35/11.61         (k1_zfmisc_1 @ 
% 11.35/11.61          (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 11.35/11.61        | (v2_struct_0 @ sk_A)
% 11.35/11.61        | (v2_struct_0 @ sk_B))),
% 11.35/11.61      inference('demod', [status(thm)], ['309', '310'])).
% 11.35/11.61  thf('312', plain, (~ (v2_struct_0 @ sk_A)),
% 11.35/11.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.61  thf('313', plain,
% 11.35/11.61      (((v2_struct_0 @ sk_B)
% 11.35/11.61        | (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 11.35/11.61           (k1_zfmisc_1 @ 
% 11.35/11.61            (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))))),
% 11.35/11.61      inference('clc', [status(thm)], ['311', '312'])).
% 11.35/11.61  thf('314', plain, (~ (v2_struct_0 @ sk_B)),
% 11.35/11.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.61  thf('315', plain,
% 11.35/11.61      ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 11.35/11.61        (k1_zfmisc_1 @ 
% 11.35/11.61         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 11.35/11.61      inference('clc', [status(thm)], ['313', '314'])).
% 11.35/11.61  thf('316', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 11.35/11.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.61  thf('317', plain,
% 11.35/11.61      (![X7 : $i, X8 : $i]:
% 11.35/11.61         (~ (m1_pre_topc @ X7 @ X8) | (l1_pre_topc @ X7) | ~ (l1_pre_topc @ X8))),
% 11.35/11.61      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 11.35/11.61  thf('318', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 11.35/11.61      inference('sup-', [status(thm)], ['316', '317'])).
% 11.35/11.61  thf('319', plain, ((l1_pre_topc @ sk_A)),
% 11.35/11.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.61  thf('320', plain, ((l1_pre_topc @ sk_C)),
% 11.35/11.61      inference('demod', [status(thm)], ['318', '319'])).
% 11.35/11.61  thf('321', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 11.35/11.61      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 11.35/11.61  thf('322', plain, ((l1_struct_0 @ sk_C)),
% 11.35/11.61      inference('sup-', [status(thm)], ['320', '321'])).
% 11.35/11.61  thf('323', plain, ((l1_struct_0 @ sk_D)),
% 11.35/11.61      inference('sup-', [status(thm)], ['273', '274'])).
% 11.35/11.61  thf('324', plain,
% 11.35/11.61      (((v2_struct_0 @ sk_B)
% 11.35/11.61        | (v2_struct_0 @ sk_D)
% 11.35/11.61        | (v2_struct_0 @ sk_C)
% 11.35/11.61        | (v2_struct_0 @ sk_A)
% 11.35/11.61        | ((k2_tmap_1 @ sk_D @ sk_B @ 
% 11.35/11.61            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ sk_C)
% 11.35/11.61            = (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C)))),
% 11.35/11.61      inference('demod', [status(thm)],
% 11.35/11.61                ['224', '261', '288', '297', '306', '315', '322', '323'])).
% 11.35/11.61  thf('325', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C))),
% 11.35/11.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.61  thf('326', plain, (((sk_F) = (sk_G))),
% 11.35/11.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.61  thf('327', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 11.35/11.61      inference('demod', [status(thm)], ['325', '326'])).
% 11.35/11.61  thf('328', plain,
% 11.35/11.61      ((r1_tmap_1 @ sk_D @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 11.35/11.61        sk_F)),
% 11.35/11.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.61  thf('329', plain,
% 11.35/11.61      ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 11.35/11.61        (k1_zfmisc_1 @ 
% 11.35/11.61         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 11.35/11.61      inference('clc', [status(thm)], ['95', '96'])).
% 11.35/11.61  thf(t64_tmap_1, axiom,
% 11.35/11.61    (![A:$i]:
% 11.35/11.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 11.35/11.61       ( ![B:$i]:
% 11.35/11.61         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 11.35/11.61             ( l1_pre_topc @ B ) ) =>
% 11.35/11.61           ( ![C:$i]:
% 11.35/11.61             ( ( ( v1_funct_1 @ C ) & 
% 11.35/11.61                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 11.35/11.61                 ( m1_subset_1 @
% 11.35/11.61                   C @ 
% 11.35/11.61                   ( k1_zfmisc_1 @
% 11.35/11.61                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 11.35/11.61               ( ![D:$i]:
% 11.35/11.61                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 11.35/11.61                   ( ![E:$i]:
% 11.35/11.61                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 11.35/11.61                       ( ![F:$i]:
% 11.35/11.61                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 11.35/11.61                           ( ( ( ( E ) = ( F ) ) & 
% 11.35/11.61                               ( r1_tmap_1 @ B @ A @ C @ E ) ) =>
% 11.35/11.61                             ( r1_tmap_1 @
% 11.35/11.61                               D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 11.35/11.61  thf('330', plain,
% 11.35/11.61      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 11.35/11.61         ((v2_struct_0 @ X31)
% 11.35/11.61          | ~ (v2_pre_topc @ X31)
% 11.35/11.61          | ~ (l1_pre_topc @ X31)
% 11.35/11.61          | (v2_struct_0 @ X32)
% 11.35/11.61          | ~ (m1_pre_topc @ X32 @ X31)
% 11.35/11.61          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X32))
% 11.35/11.61          | (r1_tmap_1 @ X32 @ X34 @ (k2_tmap_1 @ X31 @ X34 @ X35 @ X32) @ X33)
% 11.35/11.61          | ((X36) != (X33))
% 11.35/11.61          | ~ (r1_tmap_1 @ X31 @ X34 @ X35 @ X36)
% 11.35/11.61          | ~ (m1_subset_1 @ X36 @ (u1_struct_0 @ X31))
% 11.35/11.61          | ~ (m1_subset_1 @ X35 @ 
% 11.35/11.61               (k1_zfmisc_1 @ 
% 11.35/11.61                (k2_zfmisc_1 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X34))))
% 11.35/11.61          | ~ (v1_funct_2 @ X35 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X34))
% 11.35/11.61          | ~ (v1_funct_1 @ X35)
% 11.35/11.61          | ~ (l1_pre_topc @ X34)
% 11.35/11.61          | ~ (v2_pre_topc @ X34)
% 11.35/11.61          | (v2_struct_0 @ X34))),
% 11.35/11.61      inference('cnf', [status(esa)], [t64_tmap_1])).
% 11.35/11.61  thf('331', plain,
% 11.35/11.61      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 11.35/11.61         ((v2_struct_0 @ X34)
% 11.35/11.61          | ~ (v2_pre_topc @ X34)
% 11.35/11.61          | ~ (l1_pre_topc @ X34)
% 11.35/11.61          | ~ (v1_funct_1 @ X35)
% 11.35/11.61          | ~ (v1_funct_2 @ X35 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X34))
% 11.35/11.61          | ~ (m1_subset_1 @ X35 @ 
% 11.35/11.61               (k1_zfmisc_1 @ 
% 11.35/11.61                (k2_zfmisc_1 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X34))))
% 11.35/11.61          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X31))
% 11.35/11.61          | ~ (r1_tmap_1 @ X31 @ X34 @ X35 @ X33)
% 11.35/11.61          | (r1_tmap_1 @ X32 @ X34 @ (k2_tmap_1 @ X31 @ X34 @ X35 @ X32) @ X33)
% 11.35/11.61          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X32))
% 11.35/11.61          | ~ (m1_pre_topc @ X32 @ X31)
% 11.35/11.61          | (v2_struct_0 @ X32)
% 11.35/11.61          | ~ (l1_pre_topc @ X31)
% 11.35/11.61          | ~ (v2_pre_topc @ X31)
% 11.35/11.61          | (v2_struct_0 @ X31))),
% 11.35/11.61      inference('simplify', [status(thm)], ['330'])).
% 11.35/11.61  thf('332', plain,
% 11.35/11.61      (![X0 : $i, X1 : $i]:
% 11.35/11.61         ((v2_struct_0 @ sk_D)
% 11.35/11.61          | ~ (v2_pre_topc @ sk_D)
% 11.35/11.61          | ~ (l1_pre_topc @ sk_D)
% 11.35/11.61          | (v2_struct_0 @ X0)
% 11.35/11.61          | ~ (m1_pre_topc @ X0 @ sk_D)
% 11.35/11.61          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 11.35/11.61          | (r1_tmap_1 @ X0 @ sk_B @ 
% 11.35/11.61             (k2_tmap_1 @ sk_D @ sk_B @ 
% 11.35/11.61              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ X0) @ 
% 11.35/11.61             X1)
% 11.35/11.61          | ~ (r1_tmap_1 @ sk_D @ sk_B @ 
% 11.35/11.61               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ X1)
% 11.35/11.61          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D))
% 11.35/11.61          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 11.35/11.61               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 11.35/11.61          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))
% 11.35/11.61          | ~ (l1_pre_topc @ sk_B)
% 11.35/11.61          | ~ (v2_pre_topc @ sk_B)
% 11.35/11.61          | (v2_struct_0 @ sk_B))),
% 11.35/11.61      inference('sup-', [status(thm)], ['329', '331'])).
% 11.35/11.61  thf('333', plain, ((v2_pre_topc @ sk_D)),
% 11.35/11.61      inference('demod', [status(thm)], ['158', '159', '160'])).
% 11.35/11.61  thf('334', plain, ((l1_pre_topc @ sk_D)),
% 11.35/11.61      inference('demod', [status(thm)], ['164', '165'])).
% 11.35/11.61  thf('335', plain,
% 11.35/11.61      ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 11.35/11.61        (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 11.35/11.61      inference('clc', [status(thm)], ['141', '142'])).
% 11.35/11.61  thf('336', plain, ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))),
% 11.35/11.61      inference('clc', [status(thm)], ['119', '120'])).
% 11.35/11.61  thf('337', plain, ((l1_pre_topc @ sk_B)),
% 11.35/11.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.61  thf('338', plain, ((v2_pre_topc @ sk_B)),
% 11.35/11.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.61  thf('339', plain,
% 11.35/11.61      (![X0 : $i, X1 : $i]:
% 11.35/11.61         ((v2_struct_0 @ sk_D)
% 11.35/11.61          | (v2_struct_0 @ X0)
% 11.35/11.61          | ~ (m1_pre_topc @ X0 @ sk_D)
% 11.35/11.61          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 11.35/11.61          | (r1_tmap_1 @ X0 @ sk_B @ 
% 11.35/11.61             (k2_tmap_1 @ sk_D @ sk_B @ 
% 11.35/11.61              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ X0) @ 
% 11.35/11.61             X1)
% 11.35/11.61          | ~ (r1_tmap_1 @ sk_D @ sk_B @ 
% 11.35/11.61               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ X1)
% 11.35/11.61          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D))
% 11.35/11.61          | (v2_struct_0 @ sk_B))),
% 11.35/11.61      inference('demod', [status(thm)],
% 11.35/11.61                ['332', '333', '334', '335', '336', '337', '338'])).
% 11.35/11.61  thf('340', plain,
% 11.35/11.61      (![X0 : $i]:
% 11.35/11.61         ((v2_struct_0 @ sk_B)
% 11.35/11.61          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))
% 11.35/11.61          | (r1_tmap_1 @ X0 @ sk_B @ 
% 11.35/11.61             (k2_tmap_1 @ sk_D @ sk_B @ 
% 11.35/11.61              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ X0) @ 
% 11.35/11.61             sk_F)
% 11.35/11.61          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ X0))
% 11.35/11.61          | ~ (m1_pre_topc @ X0 @ sk_D)
% 11.35/11.61          | (v2_struct_0 @ X0)
% 11.35/11.61          | (v2_struct_0 @ sk_D))),
% 11.35/11.61      inference('sup-', [status(thm)], ['328', '339'])).
% 11.35/11.61  thf('341', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 11.35/11.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.61  thf('342', plain,
% 11.35/11.61      (![X0 : $i]:
% 11.35/11.61         ((v2_struct_0 @ sk_B)
% 11.35/11.61          | (r1_tmap_1 @ X0 @ sk_B @ 
% 11.35/11.61             (k2_tmap_1 @ sk_D @ sk_B @ 
% 11.35/11.61              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ X0) @ 
% 11.35/11.61             sk_F)
% 11.35/11.61          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ X0))
% 11.35/11.61          | ~ (m1_pre_topc @ X0 @ sk_D)
% 11.35/11.61          | (v2_struct_0 @ X0)
% 11.35/11.61          | (v2_struct_0 @ sk_D))),
% 11.35/11.61      inference('demod', [status(thm)], ['340', '341'])).
% 11.35/11.61  thf('343', plain,
% 11.35/11.61      (((v2_struct_0 @ sk_D)
% 11.35/11.61        | (v2_struct_0 @ sk_C)
% 11.35/11.61        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 11.35/11.61        | (r1_tmap_1 @ sk_C @ sk_B @ 
% 11.35/11.61           (k2_tmap_1 @ sk_D @ sk_B @ 
% 11.35/11.61            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ sk_C) @ 
% 11.35/11.61           sk_F)
% 11.35/11.61        | (v2_struct_0 @ sk_B))),
% 11.35/11.61      inference('sup-', [status(thm)], ['327', '342'])).
% 11.35/11.61  thf('344', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 11.35/11.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.61  thf('345', plain,
% 11.35/11.61      (((v2_struct_0 @ sk_D)
% 11.35/11.61        | (v2_struct_0 @ sk_C)
% 11.35/11.61        | (r1_tmap_1 @ sk_C @ sk_B @ 
% 11.35/11.61           (k2_tmap_1 @ sk_D @ sk_B @ 
% 11.35/11.61            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ sk_C) @ 
% 11.35/11.61           sk_F)
% 11.35/11.61        | (v2_struct_0 @ sk_B))),
% 11.35/11.61      inference('demod', [status(thm)], ['343', '344'])).
% 11.35/11.61  thf('346', plain,
% 11.35/11.61      (((r1_tmap_1 @ sk_C @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 11.35/11.61         sk_F)
% 11.35/11.61        | (v2_struct_0 @ sk_A)
% 11.35/11.61        | (v2_struct_0 @ sk_C)
% 11.35/11.61        | (v2_struct_0 @ sk_D)
% 11.35/11.61        | (v2_struct_0 @ sk_B)
% 11.35/11.61        | (v2_struct_0 @ sk_B)
% 11.35/11.61        | (v2_struct_0 @ sk_C)
% 11.35/11.61        | (v2_struct_0 @ sk_D))),
% 11.35/11.61      inference('sup+', [status(thm)], ['324', '345'])).
% 11.35/11.61  thf('347', plain,
% 11.35/11.61      (((v2_struct_0 @ sk_B)
% 11.35/11.61        | (v2_struct_0 @ sk_D)
% 11.35/11.61        | (v2_struct_0 @ sk_C)
% 11.35/11.61        | (v2_struct_0 @ sk_A)
% 11.35/11.61        | (r1_tmap_1 @ sk_C @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 11.35/11.61           sk_F))),
% 11.35/11.61      inference('simplify', [status(thm)], ['346'])).
% 11.35/11.61  thf('348', plain,
% 11.35/11.61      (~ (r1_tmap_1 @ sk_C @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 11.35/11.61          sk_G)),
% 11.35/11.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.61  thf('349', plain, (((sk_F) = (sk_G))),
% 11.35/11.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.61  thf('350', plain,
% 11.35/11.61      (~ (r1_tmap_1 @ sk_C @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 11.35/11.61          sk_F)),
% 11.35/11.61      inference('demod', [status(thm)], ['348', '349'])).
% 11.35/11.61  thf('351', plain,
% 11.35/11.61      (((v2_struct_0 @ sk_A)
% 11.35/11.61        | (v2_struct_0 @ sk_C)
% 11.35/11.61        | (v2_struct_0 @ sk_D)
% 11.35/11.61        | (v2_struct_0 @ sk_B))),
% 11.35/11.61      inference('sup-', [status(thm)], ['347', '350'])).
% 11.35/11.61  thf('352', plain, (~ (v2_struct_0 @ sk_B)),
% 11.35/11.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.61  thf('353', plain,
% 11.35/11.61      (((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A))),
% 11.35/11.61      inference('sup-', [status(thm)], ['351', '352'])).
% 11.35/11.61  thf('354', plain, (~ (v2_struct_0 @ sk_D)),
% 11.35/11.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.61  thf('355', plain, (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C))),
% 11.35/11.61      inference('clc', [status(thm)], ['353', '354'])).
% 11.35/11.61  thf('356', plain, (~ (v2_struct_0 @ sk_A)),
% 11.35/11.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.35/11.61  thf('357', plain, ((v2_struct_0 @ sk_C)),
% 11.35/11.61      inference('clc', [status(thm)], ['355', '356'])).
% 11.35/11.61  thf('358', plain, ($false), inference('demod', [status(thm)], ['0', '357'])).
% 11.35/11.61  
% 11.35/11.61  % SZS output end Refutation
% 11.35/11.61  
% 11.35/11.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
