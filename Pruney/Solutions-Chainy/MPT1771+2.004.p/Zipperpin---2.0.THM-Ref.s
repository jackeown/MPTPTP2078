%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.S9VknXAk9P

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:13 EST 2020

% Result     : Theorem 0.66s
% Output     : Refutation 0.66s
% Verified   : 
% Statistics : Number of formulae       :  300 (2158 expanded)
%              Number of leaves         :   30 ( 634 expanded)
%              Depth                    :   31
%              Number of atoms          : 4300 (90120 expanded)
%              Number of equality atoms :   47 (1342 expanded)
%              Maximal formula depth    :   28 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

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

thf('3',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t78_tmap_1,axiom,(
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
                       => ( r2_funct_2 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ ( k3_tmap_1 @ A @ B @ D @ C @ ( k2_tmap_1 @ A @ B @ E @ D ) ) @ ( k2_tmap_1 @ A @ B @ E @ C ) ) ) ) ) ) ) ) )).

thf('4',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( v2_struct_0 @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ~ ( l1_pre_topc @ X19 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_pre_topc @ X20 @ X21 )
      | ~ ( m1_pre_topc @ X22 @ X20 )
      | ( r2_funct_2 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X19 ) @ ( k3_tmap_1 @ X21 @ X19 @ X20 @ X22 @ ( k2_tmap_1 @ X21 @ X19 @ X23 @ X20 ) ) @ ( k2_tmap_1 @ X21 @ X19 @ X23 @ X22 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X19 ) ) ) )
      | ~ ( v1_funct_2 @ X23 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X19 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( m1_pre_topc @ X22 @ X21 )
      | ( v2_struct_0 @ X22 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t78_tmap_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ X1 @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1 ) ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ X1 @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1 ) ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['5','6','7','8','9','10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ X0 @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','12'])).

thf('14',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','13'])).

thf('15',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('20',plain,(
    ! [X18: $i] :
      ( ( m1_pre_topc @ X18 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('21',plain,(
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

thf('22',plain,(
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

thf('23',plain,(
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
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_A @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['23','24','25','26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
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
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['29','30','31','32'])).

thf('34',plain,
    ( ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['19','33'])).

thf('35',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,(
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

thf('40',plain,(
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
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
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
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X18: $i] :
      ( ( m1_pre_topc @ X18 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('46',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
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

thf('48',plain,(
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
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_A @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['48','49','50','51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['45','53'])).

thf('55',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['54','55','56','57'])).

thf('59',plain,
    ( ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['44','58'])).

thf('60',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ) ),
    inference(clc,[status(thm)],['59','60'])).

thf('62',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ),
    inference(clc,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['43','63'])).

thf('65',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X18: $i] :
      ( ( m1_pre_topc @ X18 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('67',plain,(
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

thf('68',plain,(
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

thf('69',plain,(
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
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
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
    inference(demod,[status(thm)],['69','70','71','72','73'])).

thf('75',plain,(
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
    inference('sup-',[status(thm)],['66','74'])).

thf('76',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['75','76','77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['65','80'])).

thf('82',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference(clc,[status(thm)],['81','82'])).

thf('84',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['83','84'])).

thf('86',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
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

thf('88',plain,(
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

thf('89',plain,(
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
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['89','90','91','92','93','94','95'])).

thf('97',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['86','96'])).

thf('98',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference(clc,[status(thm)],['97','98'])).

thf('100',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['99','100'])).

thf('102',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ),
    inference('sup+',[status(thm)],['85','101'])).

thf('103',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ),
    inference('sup+',[status(thm)],['85','101'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['64','102','103'])).

thf('105',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    ! [X18: $i] :
      ( ( m1_pre_topc @ X18 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('107',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
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

thf('109',plain,(
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
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_A @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['109','110','111','112','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['106','114'])).

thf('116',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['115','116','117','118'])).

thf('120',plain,
    ( ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['105','119'])).

thf('121',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ),
    inference('sup+',[status(thm)],['85','101'])).

thf('122',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['122','123'])).

thf('125',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['104','126'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['18','127'])).

thf('129',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['128','129','130'])).

thf('132',plain,
    ( ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['17','131'])).

thf('133',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['132','133'])).

thf('135',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['134','135'])).

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

thf('137',plain,(
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

thf('138',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ X0 )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('142',plain,(
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

thf('143',plain,(
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
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
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
    inference(demod,[status(thm)],['143','144','145'])).

thf('147',plain,(
    v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ),
    inference(clc,[status(thm)],['61','62'])).

thf('148',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ) )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['146','147'])).

thf('149',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ),
    inference('sup+',[status(thm)],['85','101'])).

thf('150',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ),
    inference('sup+',[status(thm)],['85','101'])).

thf('151',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['148','149','150'])).

thf('152',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['124','125'])).

thf('153',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['151','152'])).

thf('154',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) ) ) ),
    inference('sup-',[status(thm)],['140','153'])).

thf('155',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) ) ) ),
    inference(demod,[status(thm)],['154','155','156'])).

thf('158',plain,
    ( ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['139','157'])).

thf('159',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) ) ),
    inference(clc,[status(thm)],['158','159'])).

thf('161',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,(
    v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) ),
    inference(clc,[status(thm)],['160','161'])).

thf('163',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('166',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ),
    inference('sup+',[status(thm)],['85','101'])).

thf('167',plain,(
    m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['165','166'])).

thf('168',plain,(
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

thf('169',plain,(
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
    inference('sup-',[status(thm)],['167','168'])).

thf('170',plain,(
    v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ),
    inference(clc,[status(thm)],['61','62'])).

thf('171',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ),
    inference('sup+',[status(thm)],['85','101'])).

thf('172',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ),
    inference(demod,[status(thm)],['170','171'])).

thf('173',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['169','172','173','174'])).

thf('176',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['124','125'])).

thf('177',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['175','176'])).

thf('178',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['164','177'])).

thf('179',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['178','179','180'])).

thf('182',plain,
    ( ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['163','181'])).

thf('183',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['182','183'])).

thf('185',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,(
    v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['184','185'])).

thf('187',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ X0 )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['138','162','186'])).

thf('188',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) )
      = ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) ) ),
    inference('sup-',[status(thm)],['16','187'])).

thf('189',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['54','55','56','57'])).

thf('191',plain,
    ( ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['189','190'])).

thf('192',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E ) ) ),
    inference(clc,[status(thm)],['191','192'])).

thf('194',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,(
    v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference(clc,[status(thm)],['193','194'])).

thf('196',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf('198',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['196','197'])).

thf('199',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['198','199'])).

thf('201',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('202',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['200','201'])).

thf('203',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['89','90','91','92','93','94','95'])).

thf('205',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['203','204'])).

thf('206',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['205','206'])).

thf('208',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('209',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['207','208'])).

thf('210',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference('sup+',[status(thm)],['202','209'])).

thf('211',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) ),
    inference(demod,[status(thm)],['195','210'])).

thf('212',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('213',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['115','116','117','118'])).

thf('214',plain,
    ( ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['212','213'])).

thf('215',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference('sup+',[status(thm)],['202','209'])).

thf('216',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['214','215'])).

thf('217',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('218',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['216','217'])).

thf('219',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('220',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['218','219'])).

thf('221',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('222',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['29','30','31','32'])).

thf('223',plain,
    ( ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['221','222'])).

thf('224',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('225',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['223','224'])).

thf('226',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('227',plain,(
    m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['225','226'])).

thf('228',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference('sup+',[status(thm)],['202','209'])).

thf('229',plain,(
    m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['227','228'])).

thf('230',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) )
      = ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) ) ),
    inference(demod,[status(thm)],['188','211','220','229'])).

thf('231',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('232',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('233',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('234',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['232','233'])).

thf('235',plain,(
    r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('236',plain,(
    m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['165','166'])).

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

thf('237',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( v2_struct_0 @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ~ ( l1_pre_topc @ X27 )
      | ( v2_struct_0 @ X28 )
      | ~ ( m1_pre_topc @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X31 ) )
      | ~ ( m1_pre_topc @ X28 @ X31 )
      | ~ ( r1_tmap_1 @ X31 @ X27 @ X32 @ X30 )
      | ( X30 != X33 )
      | ( r1_tmap_1 @ X28 @ X27 @ ( k3_tmap_1 @ X29 @ X27 @ X31 @ X28 @ X32 ) @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X28 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X27 ) ) ) )
      | ~ ( v1_funct_2 @ X32 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X27 ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( m1_pre_topc @ X31 @ X29 )
      | ( v2_struct_0 @ X31 )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t81_tmap_1])).

thf('238',plain,(
    ! [X27: $i,X28: $i,X29: $i,X31: $i,X32: $i,X33: $i] :
      ( ( v2_struct_0 @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ~ ( l1_pre_topc @ X29 )
      | ( v2_struct_0 @ X31 )
      | ~ ( m1_pre_topc @ X31 @ X29 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_funct_2 @ X32 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X27 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X27 ) ) ) )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X28 ) )
      | ( r1_tmap_1 @ X28 @ X27 @ ( k3_tmap_1 @ X29 @ X27 @ X31 @ X28 @ X32 ) @ X33 )
      | ~ ( r1_tmap_1 @ X31 @ X27 @ X32 @ X33 )
      | ~ ( m1_pre_topc @ X28 @ X31 )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X31 ) )
      | ~ ( m1_pre_topc @ X28 @ X29 )
      | ( v2_struct_0 @ X28 )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(simplify,[status(thm)],['237'])).

thf('239',plain,(
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
    inference('sup-',[status(thm)],['236','238'])).

thf('240',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('241',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('242',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['124','125'])).

thf('243',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ),
    inference(demod,[status(thm)],['170','171'])).

thf('244',plain,(
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
    inference(demod,[status(thm)],['239','240','241','242','243'])).

thf('245',plain,(
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
    inference('sup-',[status(thm)],['235','244'])).

thf('246',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('247',plain,(
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
    inference(demod,[status(thm)],['245','246'])).

thf('248',plain,(
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
    inference('sup-',[status(thm)],['234','247'])).

thf('249',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('250',plain,(
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
    inference(demod,[status(thm)],['248','249'])).

thf('251',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ~ ( m1_pre_topc @ sk_D @ sk_A )
    | ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ sk_F )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['231','250'])).

thf('252',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('253',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('254',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('255',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ sk_F )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['251','252','253','254'])).

thf('256',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['230','255'])).

thf('257',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_C @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F ) ),
    inference(simplify,[status(thm)],['256'])).

thf('258',plain,(
    ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('259',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('260',plain,(
    ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F ) ),
    inference(demod,[status(thm)],['258','259'])).

thf('261',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['257','260'])).

thf('262',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('263',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['261','262'])).

thf('264',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('265',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['263','264'])).

thf('266',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('267',plain,(
    v2_struct_0 @ sk_C ),
    inference(clc,[status(thm)],['265','266'])).

thf('268',plain,(
    $false ),
    inference(demod,[status(thm)],['0','267'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.S9VknXAk9P
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:41:31 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.66/0.86  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.66/0.86  % Solved by: fo/fo7.sh
% 0.66/0.86  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.66/0.86  % done 688 iterations in 0.399s
% 0.66/0.86  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.66/0.86  % SZS output start Refutation
% 0.66/0.86  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.66/0.86  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.66/0.86  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.66/0.86  thf(sk_F_type, type, sk_F: $i).
% 0.66/0.86  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.66/0.86  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.66/0.86  thf(sk_E_type, type, sk_E: $i).
% 0.66/0.86  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.66/0.86  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.66/0.86  thf(sk_B_type, type, sk_B: $i).
% 0.66/0.86  thf(sk_D_type, type, sk_D: $i).
% 0.66/0.86  thf(sk_C_type, type, sk_C: $i).
% 0.66/0.86  thf(sk_A_type, type, sk_A: $i).
% 0.66/0.86  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.66/0.86  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.66/0.86  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.66/0.86  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.66/0.86  thf(sk_G_type, type, sk_G: $i).
% 0.66/0.86  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.66/0.86  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.66/0.86  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.66/0.86  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.66/0.86  thf(t82_tmap_1, conjecture,
% 0.66/0.86    (![A:$i]:
% 0.66/0.86     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.66/0.86       ( ![B:$i]:
% 0.66/0.86         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.66/0.86             ( l1_pre_topc @ B ) ) =>
% 0.66/0.86           ( ![C:$i]:
% 0.66/0.86             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.66/0.86               ( ![D:$i]:
% 0.66/0.86                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.66/0.86                   ( ![E:$i]:
% 0.66/0.86                     ( ( ( v1_funct_1 @ E ) & 
% 0.66/0.86                         ( v1_funct_2 @
% 0.66/0.86                           E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.66/0.86                         ( m1_subset_1 @
% 0.66/0.86                           E @ 
% 0.66/0.86                           ( k1_zfmisc_1 @
% 0.66/0.86                             ( k2_zfmisc_1 @
% 0.66/0.86                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.66/0.86                       ( ( m1_pre_topc @ C @ D ) =>
% 0.66/0.86                         ( ![F:$i]:
% 0.66/0.86                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.66/0.86                             ( ![G:$i]:
% 0.66/0.86                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.66/0.86                                 ( ( ( ( F ) = ( G ) ) & 
% 0.66/0.86                                     ( r1_tmap_1 @
% 0.66/0.86                                       D @ B @ ( k2_tmap_1 @ A @ B @ E @ D ) @ 
% 0.66/0.86                                       F ) ) =>
% 0.66/0.86                                   ( r1_tmap_1 @
% 0.66/0.86                                     C @ B @ ( k2_tmap_1 @ A @ B @ E @ C ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.66/0.86  thf(zf_stmt_0, negated_conjecture,
% 0.66/0.86    (~( ![A:$i]:
% 0.66/0.86        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.66/0.86            ( l1_pre_topc @ A ) ) =>
% 0.66/0.86          ( ![B:$i]:
% 0.66/0.86            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.66/0.86                ( l1_pre_topc @ B ) ) =>
% 0.66/0.86              ( ![C:$i]:
% 0.66/0.86                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.66/0.86                  ( ![D:$i]:
% 0.66/0.86                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.66/0.86                      ( ![E:$i]:
% 0.66/0.86                        ( ( ( v1_funct_1 @ E ) & 
% 0.66/0.86                            ( v1_funct_2 @
% 0.66/0.86                              E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.66/0.86                            ( m1_subset_1 @
% 0.66/0.86                              E @ 
% 0.66/0.86                              ( k1_zfmisc_1 @
% 0.66/0.86                                ( k2_zfmisc_1 @
% 0.66/0.86                                  ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.66/0.86                          ( ( m1_pre_topc @ C @ D ) =>
% 0.66/0.86                            ( ![F:$i]:
% 0.66/0.86                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.66/0.86                                ( ![G:$i]:
% 0.66/0.86                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.66/0.86                                    ( ( ( ( F ) = ( G ) ) & 
% 0.66/0.86                                        ( r1_tmap_1 @
% 0.66/0.86                                          D @ B @ 
% 0.66/0.86                                          ( k2_tmap_1 @ A @ B @ E @ D ) @ F ) ) =>
% 0.66/0.86                                      ( r1_tmap_1 @
% 0.66/0.86                                        C @ B @ 
% 0.66/0.86                                        ( k2_tmap_1 @ A @ B @ E @ C ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.66/0.86    inference('cnf.neg', [status(esa)], [t82_tmap_1])).
% 0.66/0.86  thf('0', plain, (~ (v2_struct_0 @ sk_C)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('1', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('2', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('3', plain,
% 0.66/0.86      ((m1_subset_1 @ sk_E @ 
% 0.66/0.86        (k1_zfmisc_1 @ 
% 0.66/0.86         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf(t78_tmap_1, axiom,
% 0.66/0.86    (![A:$i]:
% 0.66/0.86     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.66/0.86       ( ![B:$i]:
% 0.66/0.86         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.66/0.86             ( l1_pre_topc @ B ) ) =>
% 0.66/0.86           ( ![C:$i]:
% 0.66/0.86             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.66/0.86               ( ![D:$i]:
% 0.66/0.86                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.66/0.86                   ( ![E:$i]:
% 0.66/0.86                     ( ( ( v1_funct_1 @ E ) & 
% 0.66/0.86                         ( v1_funct_2 @
% 0.66/0.86                           E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.66/0.86                         ( m1_subset_1 @
% 0.66/0.86                           E @ 
% 0.66/0.86                           ( k1_zfmisc_1 @
% 0.66/0.86                             ( k2_zfmisc_1 @
% 0.66/0.86                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.66/0.86                       ( ( m1_pre_topc @ C @ D ) =>
% 0.66/0.86                         ( r2_funct_2 @
% 0.66/0.86                           ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ 
% 0.66/0.86                           ( k3_tmap_1 @
% 0.66/0.86                             A @ B @ D @ C @ ( k2_tmap_1 @ A @ B @ E @ D ) ) @ 
% 0.66/0.86                           ( k2_tmap_1 @ A @ B @ E @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.66/0.86  thf('4', plain,
% 0.66/0.86      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.66/0.86         ((v2_struct_0 @ X19)
% 0.66/0.86          | ~ (v2_pre_topc @ X19)
% 0.66/0.86          | ~ (l1_pre_topc @ X19)
% 0.66/0.86          | (v2_struct_0 @ X20)
% 0.66/0.86          | ~ (m1_pre_topc @ X20 @ X21)
% 0.66/0.86          | ~ (m1_pre_topc @ X22 @ X20)
% 0.66/0.86          | (r2_funct_2 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X19) @ 
% 0.66/0.86             (k3_tmap_1 @ X21 @ X19 @ X20 @ X22 @ 
% 0.66/0.86              (k2_tmap_1 @ X21 @ X19 @ X23 @ X20)) @ 
% 0.66/0.86             (k2_tmap_1 @ X21 @ X19 @ X23 @ X22))
% 0.66/0.86          | ~ (m1_subset_1 @ X23 @ 
% 0.66/0.86               (k1_zfmisc_1 @ 
% 0.66/0.86                (k2_zfmisc_1 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X19))))
% 0.66/0.86          | ~ (v1_funct_2 @ X23 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X19))
% 0.66/0.86          | ~ (v1_funct_1 @ X23)
% 0.66/0.86          | ~ (m1_pre_topc @ X22 @ X21)
% 0.66/0.86          | (v2_struct_0 @ X22)
% 0.66/0.86          | ~ (l1_pre_topc @ X21)
% 0.66/0.86          | ~ (v2_pre_topc @ X21)
% 0.66/0.86          | (v2_struct_0 @ X21))),
% 0.66/0.86      inference('cnf', [status(esa)], [t78_tmap_1])).
% 0.66/0.86  thf('5', plain,
% 0.66/0.86      (![X0 : $i, X1 : $i]:
% 0.66/0.86         ((v2_struct_0 @ sk_A)
% 0.66/0.86          | ~ (v2_pre_topc @ sk_A)
% 0.66/0.86          | ~ (l1_pre_topc @ sk_A)
% 0.66/0.86          | (v2_struct_0 @ X0)
% 0.66/0.86          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.66/0.86          | ~ (v1_funct_1 @ sk_E)
% 0.66/0.86          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.66/0.86          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.86             (k3_tmap_1 @ sk_A @ sk_B @ X1 @ X0 @ 
% 0.66/0.86              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1)) @ 
% 0.66/0.86             (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 0.66/0.86          | ~ (m1_pre_topc @ X0 @ X1)
% 0.66/0.86          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.66/0.86          | (v2_struct_0 @ X1)
% 0.66/0.86          | ~ (l1_pre_topc @ sk_B)
% 0.66/0.86          | ~ (v2_pre_topc @ sk_B)
% 0.66/0.86          | (v2_struct_0 @ sk_B))),
% 0.66/0.86      inference('sup-', [status(thm)], ['3', '4'])).
% 0.66/0.86  thf('6', plain, ((v2_pre_topc @ sk_A)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('8', plain, ((v1_funct_1 @ sk_E)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('9', plain,
% 0.66/0.86      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('10', plain, ((l1_pre_topc @ sk_B)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('11', plain, ((v2_pre_topc @ sk_B)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('12', plain,
% 0.66/0.86      (![X0 : $i, X1 : $i]:
% 0.66/0.86         ((v2_struct_0 @ sk_A)
% 0.66/0.86          | (v2_struct_0 @ X0)
% 0.66/0.86          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.66/0.86          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.86             (k3_tmap_1 @ sk_A @ sk_B @ X1 @ X0 @ 
% 0.66/0.86              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1)) @ 
% 0.66/0.86             (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 0.66/0.86          | ~ (m1_pre_topc @ X0 @ X1)
% 0.66/0.86          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.66/0.86          | (v2_struct_0 @ X1)
% 0.66/0.86          | (v2_struct_0 @ sk_B))),
% 0.66/0.86      inference('demod', [status(thm)], ['5', '6', '7', '8', '9', '10', '11'])).
% 0.66/0.86  thf('13', plain,
% 0.66/0.86      (![X0 : $i]:
% 0.66/0.86         ((v2_struct_0 @ sk_B)
% 0.66/0.86          | (v2_struct_0 @ X0)
% 0.66/0.86          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.66/0.86          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.66/0.86          | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.86             (k3_tmap_1 @ sk_A @ sk_B @ X0 @ sk_C @ 
% 0.66/0.86              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0)) @ 
% 0.66/0.86             (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C))
% 0.66/0.86          | (v2_struct_0 @ sk_C)
% 0.66/0.86          | (v2_struct_0 @ sk_A))),
% 0.66/0.86      inference('sup-', [status(thm)], ['2', '12'])).
% 0.66/0.86  thf('14', plain,
% 0.66/0.86      (((v2_struct_0 @ sk_A)
% 0.66/0.86        | (v2_struct_0 @ sk_C)
% 0.66/0.86        | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.86           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ 
% 0.66/0.86            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.66/0.86           (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C))
% 0.66/0.86        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.66/0.86        | (v2_struct_0 @ sk_D)
% 0.66/0.86        | (v2_struct_0 @ sk_B))),
% 0.66/0.86      inference('sup-', [status(thm)], ['1', '13'])).
% 0.66/0.86  thf('15', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('16', plain,
% 0.66/0.86      (((v2_struct_0 @ sk_A)
% 0.66/0.86        | (v2_struct_0 @ sk_C)
% 0.66/0.86        | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.86           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ 
% 0.66/0.86            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.66/0.86           (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C))
% 0.66/0.86        | (v2_struct_0 @ sk_D)
% 0.66/0.86        | (v2_struct_0 @ sk_B))),
% 0.66/0.86      inference('demod', [status(thm)], ['14', '15'])).
% 0.66/0.86  thf('17', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('18', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('19', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf(t2_tsep_1, axiom,
% 0.66/0.86    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.66/0.86  thf('20', plain,
% 0.66/0.86      (![X18 : $i]: ((m1_pre_topc @ X18 @ X18) | ~ (l1_pre_topc @ X18))),
% 0.66/0.86      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.66/0.86  thf('21', plain,
% 0.66/0.86      ((m1_subset_1 @ sk_E @ 
% 0.66/0.86        (k1_zfmisc_1 @ 
% 0.66/0.86         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf(dt_k3_tmap_1, axiom,
% 0.66/0.86    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.66/0.86     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.66/0.86         ( l1_pre_topc @ A ) & ( ~( v2_struct_0 @ B ) ) & 
% 0.66/0.86         ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) & ( m1_pre_topc @ C @ A ) & 
% 0.66/0.86         ( m1_pre_topc @ D @ A ) & ( v1_funct_1 @ E ) & 
% 0.66/0.86         ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.66/0.86         ( m1_subset_1 @
% 0.66/0.86           E @ 
% 0.66/0.86           ( k1_zfmisc_1 @
% 0.66/0.86             ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.66/0.86       ( ( v1_funct_1 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) ) & 
% 0.66/0.86         ( v1_funct_2 @
% 0.66/0.86           ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ ( u1_struct_0 @ D ) @ 
% 0.66/0.86           ( u1_struct_0 @ B ) ) & 
% 0.66/0.86         ( m1_subset_1 @
% 0.66/0.86           ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ 
% 0.66/0.86           ( k1_zfmisc_1 @
% 0.66/0.86             ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.66/0.86  thf('22', plain,
% 0.66/0.86      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.66/0.86         (~ (m1_pre_topc @ X13 @ X14)
% 0.66/0.86          | ~ (m1_pre_topc @ X15 @ X14)
% 0.66/0.86          | ~ (l1_pre_topc @ X16)
% 0.66/0.86          | ~ (v2_pre_topc @ X16)
% 0.66/0.86          | (v2_struct_0 @ X16)
% 0.66/0.86          | ~ (l1_pre_topc @ X14)
% 0.66/0.86          | ~ (v2_pre_topc @ X14)
% 0.66/0.86          | (v2_struct_0 @ X14)
% 0.66/0.86          | ~ (v1_funct_1 @ X17)
% 0.66/0.86          | ~ (v1_funct_2 @ X17 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X16))
% 0.66/0.86          | ~ (m1_subset_1 @ X17 @ 
% 0.66/0.86               (k1_zfmisc_1 @ 
% 0.66/0.86                (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X16))))
% 0.66/0.86          | (m1_subset_1 @ (k3_tmap_1 @ X14 @ X16 @ X15 @ X13 @ X17) @ 
% 0.66/0.86             (k1_zfmisc_1 @ 
% 0.66/0.86              (k2_zfmisc_1 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X16)))))),
% 0.66/0.86      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 0.66/0.86  thf('23', plain,
% 0.66/0.86      (![X0 : $i, X1 : $i]:
% 0.66/0.86         ((m1_subset_1 @ (k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 0.66/0.86           (k1_zfmisc_1 @ 
% 0.66/0.86            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.66/0.86          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.66/0.86          | ~ (v1_funct_1 @ sk_E)
% 0.66/0.86          | (v2_struct_0 @ X1)
% 0.66/0.86          | ~ (v2_pre_topc @ X1)
% 0.66/0.86          | ~ (l1_pre_topc @ X1)
% 0.66/0.86          | (v2_struct_0 @ sk_B)
% 0.66/0.86          | ~ (v2_pre_topc @ sk_B)
% 0.66/0.86          | ~ (l1_pre_topc @ sk_B)
% 0.66/0.86          | ~ (m1_pre_topc @ sk_A @ X1)
% 0.66/0.86          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.66/0.86      inference('sup-', [status(thm)], ['21', '22'])).
% 0.66/0.86  thf('24', plain,
% 0.66/0.86      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('25', plain, ((v1_funct_1 @ sk_E)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('26', plain, ((v2_pre_topc @ sk_B)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('27', plain, ((l1_pre_topc @ sk_B)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('28', plain,
% 0.66/0.86      (![X0 : $i, X1 : $i]:
% 0.66/0.86         ((m1_subset_1 @ (k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 0.66/0.86           (k1_zfmisc_1 @ 
% 0.66/0.86            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.66/0.86          | (v2_struct_0 @ X1)
% 0.66/0.86          | ~ (v2_pre_topc @ X1)
% 0.66/0.86          | ~ (l1_pre_topc @ X1)
% 0.66/0.86          | (v2_struct_0 @ sk_B)
% 0.66/0.86          | ~ (m1_pre_topc @ sk_A @ X1)
% 0.66/0.86          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.66/0.86      inference('demod', [status(thm)], ['23', '24', '25', '26', '27'])).
% 0.66/0.86  thf('29', plain,
% 0.66/0.86      (![X0 : $i]:
% 0.66/0.86         (~ (l1_pre_topc @ sk_A)
% 0.66/0.86          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.66/0.86          | (v2_struct_0 @ sk_B)
% 0.66/0.86          | ~ (l1_pre_topc @ sk_A)
% 0.66/0.86          | ~ (v2_pre_topc @ sk_A)
% 0.66/0.86          | (v2_struct_0 @ sk_A)
% 0.66/0.86          | (m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 0.66/0.86             (k1_zfmisc_1 @ 
% 0.66/0.86              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))))),
% 0.66/0.86      inference('sup-', [status(thm)], ['20', '28'])).
% 0.66/0.86  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('32', plain, ((v2_pre_topc @ sk_A)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('33', plain,
% 0.66/0.86      (![X0 : $i]:
% 0.66/0.86         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.66/0.86          | (v2_struct_0 @ sk_B)
% 0.66/0.86          | (v2_struct_0 @ sk_A)
% 0.66/0.86          | (m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 0.66/0.86             (k1_zfmisc_1 @ 
% 0.66/0.86              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))))),
% 0.66/0.86      inference('demod', [status(thm)], ['29', '30', '31', '32'])).
% 0.66/0.86  thf('34', plain,
% 0.66/0.86      (((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E) @ 
% 0.66/0.86         (k1_zfmisc_1 @ 
% 0.66/0.86          (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 0.66/0.86        | (v2_struct_0 @ sk_A)
% 0.66/0.86        | (v2_struct_0 @ sk_B))),
% 0.66/0.86      inference('sup-', [status(thm)], ['19', '33'])).
% 0.66/0.86  thf('35', plain, (~ (v2_struct_0 @ sk_A)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('36', plain,
% 0.66/0.86      (((v2_struct_0 @ sk_B)
% 0.66/0.86        | (m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E) @ 
% 0.66/0.86           (k1_zfmisc_1 @ 
% 0.66/0.86            (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))))),
% 0.66/0.86      inference('clc', [status(thm)], ['34', '35'])).
% 0.66/0.86  thf('37', plain, (~ (v2_struct_0 @ sk_B)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('38', plain,
% 0.66/0.86      ((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E) @ 
% 0.66/0.86        (k1_zfmisc_1 @ 
% 0.66/0.86         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.66/0.86      inference('clc', [status(thm)], ['36', '37'])).
% 0.66/0.86  thf('39', plain,
% 0.66/0.86      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.66/0.86         (~ (m1_pre_topc @ X13 @ X14)
% 0.66/0.86          | ~ (m1_pre_topc @ X15 @ X14)
% 0.66/0.86          | ~ (l1_pre_topc @ X16)
% 0.66/0.86          | ~ (v2_pre_topc @ X16)
% 0.66/0.86          | (v2_struct_0 @ X16)
% 0.66/0.86          | ~ (l1_pre_topc @ X14)
% 0.66/0.86          | ~ (v2_pre_topc @ X14)
% 0.66/0.86          | (v2_struct_0 @ X14)
% 0.66/0.86          | ~ (v1_funct_1 @ X17)
% 0.66/0.86          | ~ (v1_funct_2 @ X17 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X16))
% 0.66/0.86          | ~ (m1_subset_1 @ X17 @ 
% 0.66/0.86               (k1_zfmisc_1 @ 
% 0.66/0.86                (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X16))))
% 0.66/0.86          | (m1_subset_1 @ (k3_tmap_1 @ X14 @ X16 @ X15 @ X13 @ X17) @ 
% 0.66/0.86             (k1_zfmisc_1 @ 
% 0.66/0.86              (k2_zfmisc_1 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X16)))))),
% 0.66/0.86      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 0.66/0.86  thf('40', plain,
% 0.66/0.86      (![X0 : $i, X1 : $i]:
% 0.66/0.86         ((m1_subset_1 @ 
% 0.66/0.86           (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ 
% 0.66/0.86            (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E)) @ 
% 0.66/0.86           (k1_zfmisc_1 @ 
% 0.66/0.86            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.66/0.86          | ~ (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E) @ 
% 0.66/0.86               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.66/0.86          | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))
% 0.66/0.86          | (v2_struct_0 @ X1)
% 0.66/0.86          | ~ (v2_pre_topc @ X1)
% 0.66/0.86          | ~ (l1_pre_topc @ X1)
% 0.66/0.86          | (v2_struct_0 @ sk_B)
% 0.66/0.86          | ~ (v2_pre_topc @ sk_B)
% 0.66/0.86          | ~ (l1_pre_topc @ sk_B)
% 0.66/0.86          | ~ (m1_pre_topc @ sk_D @ X1)
% 0.66/0.86          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.66/0.86      inference('sup-', [status(thm)], ['38', '39'])).
% 0.66/0.86  thf('41', plain, ((v2_pre_topc @ sk_B)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('42', plain, ((l1_pre_topc @ sk_B)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('43', plain,
% 0.66/0.86      (![X0 : $i, X1 : $i]:
% 0.66/0.86         ((m1_subset_1 @ 
% 0.66/0.86           (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ 
% 0.66/0.86            (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E)) @ 
% 0.66/0.86           (k1_zfmisc_1 @ 
% 0.66/0.86            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.66/0.86          | ~ (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E) @ 
% 0.66/0.86               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.66/0.86          | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))
% 0.66/0.86          | (v2_struct_0 @ X1)
% 0.66/0.86          | ~ (v2_pre_topc @ X1)
% 0.66/0.86          | ~ (l1_pre_topc @ X1)
% 0.66/0.86          | (v2_struct_0 @ sk_B)
% 0.66/0.86          | ~ (m1_pre_topc @ sk_D @ X1)
% 0.66/0.86          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.66/0.86      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.66/0.86  thf('44', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('45', plain,
% 0.66/0.86      (![X18 : $i]: ((m1_pre_topc @ X18 @ X18) | ~ (l1_pre_topc @ X18))),
% 0.66/0.86      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.66/0.86  thf('46', plain,
% 0.66/0.86      ((m1_subset_1 @ sk_E @ 
% 0.66/0.86        (k1_zfmisc_1 @ 
% 0.66/0.86         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('47', plain,
% 0.66/0.86      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.66/0.86         (~ (m1_pre_topc @ X13 @ X14)
% 0.66/0.86          | ~ (m1_pre_topc @ X15 @ X14)
% 0.66/0.86          | ~ (l1_pre_topc @ X16)
% 0.66/0.86          | ~ (v2_pre_topc @ X16)
% 0.66/0.86          | (v2_struct_0 @ X16)
% 0.66/0.86          | ~ (l1_pre_topc @ X14)
% 0.66/0.86          | ~ (v2_pre_topc @ X14)
% 0.66/0.86          | (v2_struct_0 @ X14)
% 0.66/0.86          | ~ (v1_funct_1 @ X17)
% 0.66/0.86          | ~ (v1_funct_2 @ X17 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X16))
% 0.66/0.86          | ~ (m1_subset_1 @ X17 @ 
% 0.66/0.86               (k1_zfmisc_1 @ 
% 0.66/0.86                (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X16))))
% 0.66/0.86          | (v1_funct_1 @ (k3_tmap_1 @ X14 @ X16 @ X15 @ X13 @ X17)))),
% 0.66/0.86      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 0.66/0.86  thf('48', plain,
% 0.66/0.86      (![X0 : $i, X1 : $i]:
% 0.66/0.86         ((v1_funct_1 @ (k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E))
% 0.66/0.86          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.66/0.86          | ~ (v1_funct_1 @ sk_E)
% 0.66/0.86          | (v2_struct_0 @ X1)
% 0.66/0.86          | ~ (v2_pre_topc @ X1)
% 0.66/0.86          | ~ (l1_pre_topc @ X1)
% 0.66/0.86          | (v2_struct_0 @ sk_B)
% 0.66/0.86          | ~ (v2_pre_topc @ sk_B)
% 0.66/0.86          | ~ (l1_pre_topc @ sk_B)
% 0.66/0.86          | ~ (m1_pre_topc @ sk_A @ X1)
% 0.66/0.86          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.66/0.86      inference('sup-', [status(thm)], ['46', '47'])).
% 0.66/0.86  thf('49', plain,
% 0.66/0.86      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('50', plain, ((v1_funct_1 @ sk_E)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('51', plain, ((v2_pre_topc @ sk_B)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('52', plain, ((l1_pre_topc @ sk_B)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('53', plain,
% 0.66/0.86      (![X0 : $i, X1 : $i]:
% 0.66/0.86         ((v1_funct_1 @ (k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E))
% 0.66/0.86          | (v2_struct_0 @ X1)
% 0.66/0.86          | ~ (v2_pre_topc @ X1)
% 0.66/0.86          | ~ (l1_pre_topc @ X1)
% 0.66/0.86          | (v2_struct_0 @ sk_B)
% 0.66/0.86          | ~ (m1_pre_topc @ sk_A @ X1)
% 0.66/0.86          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.66/0.86      inference('demod', [status(thm)], ['48', '49', '50', '51', '52'])).
% 0.66/0.86  thf('54', plain,
% 0.66/0.86      (![X0 : $i]:
% 0.66/0.86         (~ (l1_pre_topc @ sk_A)
% 0.66/0.86          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.66/0.86          | (v2_struct_0 @ sk_B)
% 0.66/0.86          | ~ (l1_pre_topc @ sk_A)
% 0.66/0.86          | ~ (v2_pre_topc @ sk_A)
% 0.66/0.86          | (v2_struct_0 @ sk_A)
% 0.66/0.86          | (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E)))),
% 0.66/0.86      inference('sup-', [status(thm)], ['45', '53'])).
% 0.66/0.86  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('56', plain, ((l1_pre_topc @ sk_A)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('57', plain, ((v2_pre_topc @ sk_A)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('58', plain,
% 0.66/0.86      (![X0 : $i]:
% 0.66/0.86         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.66/0.86          | (v2_struct_0 @ sk_B)
% 0.66/0.86          | (v2_struct_0 @ sk_A)
% 0.66/0.86          | (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E)))),
% 0.66/0.86      inference('demod', [status(thm)], ['54', '55', '56', '57'])).
% 0.66/0.86  thf('59', plain,
% 0.66/0.86      (((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))
% 0.66/0.86        | (v2_struct_0 @ sk_A)
% 0.66/0.86        | (v2_struct_0 @ sk_B))),
% 0.66/0.86      inference('sup-', [status(thm)], ['44', '58'])).
% 0.66/0.86  thf('60', plain, (~ (v2_struct_0 @ sk_A)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('61', plain,
% 0.66/0.86      (((v2_struct_0 @ sk_B)
% 0.66/0.86        | (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E)))),
% 0.66/0.86      inference('clc', [status(thm)], ['59', '60'])).
% 0.66/0.86  thf('62', plain, (~ (v2_struct_0 @ sk_B)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('63', plain,
% 0.66/0.86      ((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))),
% 0.66/0.86      inference('clc', [status(thm)], ['61', '62'])).
% 0.66/0.86  thf('64', plain,
% 0.66/0.86      (![X0 : $i, X1 : $i]:
% 0.66/0.86         ((m1_subset_1 @ 
% 0.66/0.86           (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ 
% 0.66/0.86            (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E)) @ 
% 0.66/0.86           (k1_zfmisc_1 @ 
% 0.66/0.86            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.66/0.86          | ~ (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E) @ 
% 0.66/0.86               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.66/0.86          | (v2_struct_0 @ X1)
% 0.66/0.86          | ~ (v2_pre_topc @ X1)
% 0.66/0.86          | ~ (l1_pre_topc @ X1)
% 0.66/0.86          | (v2_struct_0 @ sk_B)
% 0.66/0.86          | ~ (m1_pre_topc @ sk_D @ X1)
% 0.66/0.86          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.66/0.86      inference('demod', [status(thm)], ['43', '63'])).
% 0.66/0.86  thf('65', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('66', plain,
% 0.66/0.86      (![X18 : $i]: ((m1_pre_topc @ X18 @ X18) | ~ (l1_pre_topc @ X18))),
% 0.66/0.86      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.66/0.86  thf('67', plain,
% 0.66/0.86      ((m1_subset_1 @ sk_E @ 
% 0.66/0.86        (k1_zfmisc_1 @ 
% 0.66/0.86         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf(d5_tmap_1, axiom,
% 0.66/0.86    (![A:$i]:
% 0.66/0.86     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.66/0.86       ( ![B:$i]:
% 0.66/0.86         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.66/0.86             ( l1_pre_topc @ B ) ) =>
% 0.66/0.86           ( ![C:$i]:
% 0.66/0.86             ( ( m1_pre_topc @ C @ A ) =>
% 0.66/0.86               ( ![D:$i]:
% 0.66/0.86                 ( ( m1_pre_topc @ D @ A ) =>
% 0.66/0.86                   ( ![E:$i]:
% 0.66/0.86                     ( ( ( v1_funct_1 @ E ) & 
% 0.66/0.86                         ( v1_funct_2 @
% 0.66/0.86                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.66/0.86                         ( m1_subset_1 @
% 0.66/0.86                           E @ 
% 0.66/0.86                           ( k1_zfmisc_1 @
% 0.66/0.86                             ( k2_zfmisc_1 @
% 0.66/0.86                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.66/0.86                       ( ( m1_pre_topc @ D @ C ) =>
% 0.66/0.86                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 0.66/0.86                           ( k2_partfun1 @
% 0.66/0.86                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 0.66/0.86                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.66/0.86  thf('68', plain,
% 0.66/0.86      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.66/0.86         ((v2_struct_0 @ X8)
% 0.66/0.86          | ~ (v2_pre_topc @ X8)
% 0.66/0.86          | ~ (l1_pre_topc @ X8)
% 0.66/0.86          | ~ (m1_pre_topc @ X9 @ X10)
% 0.66/0.86          | ~ (m1_pre_topc @ X9 @ X11)
% 0.66/0.86          | ((k3_tmap_1 @ X10 @ X8 @ X11 @ X9 @ X12)
% 0.66/0.86              = (k2_partfun1 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X8) @ 
% 0.66/0.86                 X12 @ (u1_struct_0 @ X9)))
% 0.66/0.86          | ~ (m1_subset_1 @ X12 @ 
% 0.66/0.86               (k1_zfmisc_1 @ 
% 0.66/0.86                (k2_zfmisc_1 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X8))))
% 0.66/0.86          | ~ (v1_funct_2 @ X12 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X8))
% 0.66/0.86          | ~ (v1_funct_1 @ X12)
% 0.66/0.86          | ~ (m1_pre_topc @ X11 @ X10)
% 0.66/0.86          | ~ (l1_pre_topc @ X10)
% 0.66/0.86          | ~ (v2_pre_topc @ X10)
% 0.66/0.86          | (v2_struct_0 @ X10))),
% 0.66/0.86      inference('cnf', [status(esa)], [d5_tmap_1])).
% 0.66/0.86  thf('69', plain,
% 0.66/0.86      (![X0 : $i, X1 : $i]:
% 0.66/0.86         ((v2_struct_0 @ X0)
% 0.66/0.86          | ~ (v2_pre_topc @ X0)
% 0.66/0.86          | ~ (l1_pre_topc @ X0)
% 0.66/0.86          | ~ (m1_pre_topc @ sk_A @ X0)
% 0.66/0.86          | ~ (v1_funct_1 @ sk_E)
% 0.66/0.86          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.66/0.86          | ((k3_tmap_1 @ X0 @ sk_B @ sk_A @ X1 @ sk_E)
% 0.66/0.86              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.86                 sk_E @ (u1_struct_0 @ X1)))
% 0.66/0.86          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.66/0.86          | ~ (m1_pre_topc @ X1 @ X0)
% 0.66/0.86          | ~ (l1_pre_topc @ sk_B)
% 0.66/0.86          | ~ (v2_pre_topc @ sk_B)
% 0.66/0.86          | (v2_struct_0 @ sk_B))),
% 0.66/0.86      inference('sup-', [status(thm)], ['67', '68'])).
% 0.66/0.86  thf('70', plain, ((v1_funct_1 @ sk_E)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('71', plain,
% 0.66/0.86      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('72', plain, ((l1_pre_topc @ sk_B)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('73', plain, ((v2_pre_topc @ sk_B)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('74', plain,
% 0.66/0.86      (![X0 : $i, X1 : $i]:
% 0.66/0.86         ((v2_struct_0 @ X0)
% 0.66/0.86          | ~ (v2_pre_topc @ X0)
% 0.66/0.86          | ~ (l1_pre_topc @ X0)
% 0.66/0.86          | ~ (m1_pre_topc @ sk_A @ X0)
% 0.66/0.86          | ((k3_tmap_1 @ X0 @ sk_B @ sk_A @ X1 @ sk_E)
% 0.66/0.86              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.86                 sk_E @ (u1_struct_0 @ X1)))
% 0.66/0.86          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.66/0.86          | ~ (m1_pre_topc @ X1 @ X0)
% 0.66/0.86          | (v2_struct_0 @ sk_B))),
% 0.66/0.86      inference('demod', [status(thm)], ['69', '70', '71', '72', '73'])).
% 0.66/0.86  thf('75', plain,
% 0.66/0.86      (![X0 : $i]:
% 0.66/0.86         (~ (l1_pre_topc @ sk_A)
% 0.66/0.86          | (v2_struct_0 @ sk_B)
% 0.66/0.86          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.66/0.86          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.66/0.86          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E)
% 0.66/0.86              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.86                 sk_E @ (u1_struct_0 @ X0)))
% 0.66/0.86          | ~ (l1_pre_topc @ sk_A)
% 0.66/0.86          | ~ (v2_pre_topc @ sk_A)
% 0.66/0.86          | (v2_struct_0 @ sk_A))),
% 0.66/0.86      inference('sup-', [status(thm)], ['66', '74'])).
% 0.66/0.86  thf('76', plain, ((l1_pre_topc @ sk_A)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('77', plain, ((l1_pre_topc @ sk_A)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('78', plain, ((v2_pre_topc @ sk_A)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('79', plain,
% 0.66/0.86      (![X0 : $i]:
% 0.66/0.86         ((v2_struct_0 @ sk_B)
% 0.66/0.86          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.66/0.86          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.66/0.86          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E)
% 0.66/0.86              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.86                 sk_E @ (u1_struct_0 @ X0)))
% 0.66/0.86          | (v2_struct_0 @ sk_A))),
% 0.66/0.86      inference('demod', [status(thm)], ['75', '76', '77', '78'])).
% 0.66/0.86  thf('80', plain,
% 0.66/0.86      (![X0 : $i]:
% 0.66/0.86         ((v2_struct_0 @ sk_A)
% 0.66/0.86          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E)
% 0.66/0.86              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.86                 sk_E @ (u1_struct_0 @ X0)))
% 0.66/0.86          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.66/0.86          | (v2_struct_0 @ sk_B))),
% 0.66/0.86      inference('simplify', [status(thm)], ['79'])).
% 0.66/0.86  thf('81', plain,
% 0.66/0.86      (((v2_struct_0 @ sk_B)
% 0.66/0.86        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E)
% 0.66/0.86            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.86               sk_E @ (u1_struct_0 @ sk_D)))
% 0.66/0.86        | (v2_struct_0 @ sk_A))),
% 0.66/0.86      inference('sup-', [status(thm)], ['65', '80'])).
% 0.66/0.86  thf('82', plain, (~ (v2_struct_0 @ sk_B)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('83', plain,
% 0.66/0.86      (((v2_struct_0 @ sk_A)
% 0.66/0.86        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E)
% 0.66/0.86            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.86               sk_E @ (u1_struct_0 @ sk_D))))),
% 0.66/0.86      inference('clc', [status(thm)], ['81', '82'])).
% 0.66/0.86  thf('84', plain, (~ (v2_struct_0 @ sk_A)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('85', plain,
% 0.66/0.86      (((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E)
% 0.66/0.86         = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.66/0.86            (u1_struct_0 @ sk_D)))),
% 0.66/0.86      inference('clc', [status(thm)], ['83', '84'])).
% 0.66/0.86  thf('86', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('87', plain,
% 0.66/0.86      ((m1_subset_1 @ sk_E @ 
% 0.66/0.86        (k1_zfmisc_1 @ 
% 0.66/0.86         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf(d4_tmap_1, axiom,
% 0.66/0.86    (![A:$i]:
% 0.66/0.86     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.66/0.86       ( ![B:$i]:
% 0.66/0.86         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.66/0.86             ( l1_pre_topc @ B ) ) =>
% 0.66/0.86           ( ![C:$i]:
% 0.66/0.86             ( ( ( v1_funct_1 @ C ) & 
% 0.66/0.86                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.66/0.86                 ( m1_subset_1 @
% 0.66/0.86                   C @ 
% 0.66/0.86                   ( k1_zfmisc_1 @
% 0.66/0.86                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.66/0.86               ( ![D:$i]:
% 0.66/0.86                 ( ( m1_pre_topc @ D @ A ) =>
% 0.66/0.86                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 0.66/0.86                     ( k2_partfun1 @
% 0.66/0.86                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.66/0.86                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 0.66/0.86  thf('88', plain,
% 0.66/0.86      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.66/0.86         ((v2_struct_0 @ X4)
% 0.66/0.86          | ~ (v2_pre_topc @ X4)
% 0.66/0.86          | ~ (l1_pre_topc @ X4)
% 0.66/0.86          | ~ (m1_pre_topc @ X5 @ X6)
% 0.66/0.86          | ((k2_tmap_1 @ X6 @ X4 @ X7 @ X5)
% 0.66/0.86              = (k2_partfun1 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X4) @ X7 @ 
% 0.66/0.86                 (u1_struct_0 @ X5)))
% 0.66/0.86          | ~ (m1_subset_1 @ X7 @ 
% 0.66/0.86               (k1_zfmisc_1 @ 
% 0.66/0.86                (k2_zfmisc_1 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X4))))
% 0.66/0.86          | ~ (v1_funct_2 @ X7 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X4))
% 0.66/0.86          | ~ (v1_funct_1 @ X7)
% 0.66/0.86          | ~ (l1_pre_topc @ X6)
% 0.66/0.86          | ~ (v2_pre_topc @ X6)
% 0.66/0.86          | (v2_struct_0 @ X6))),
% 0.66/0.86      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.66/0.86  thf('89', plain,
% 0.66/0.86      (![X0 : $i]:
% 0.66/0.86         ((v2_struct_0 @ sk_A)
% 0.66/0.86          | ~ (v2_pre_topc @ sk_A)
% 0.66/0.86          | ~ (l1_pre_topc @ sk_A)
% 0.66/0.86          | ~ (v1_funct_1 @ sk_E)
% 0.66/0.86          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.66/0.86          | ((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0)
% 0.66/0.86              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.86                 sk_E @ (u1_struct_0 @ X0)))
% 0.66/0.86          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.66/0.86          | ~ (l1_pre_topc @ sk_B)
% 0.66/0.86          | ~ (v2_pre_topc @ sk_B)
% 0.66/0.86          | (v2_struct_0 @ sk_B))),
% 0.66/0.86      inference('sup-', [status(thm)], ['87', '88'])).
% 0.66/0.86  thf('90', plain, ((v2_pre_topc @ sk_A)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('91', plain, ((l1_pre_topc @ sk_A)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('92', plain, ((v1_funct_1 @ sk_E)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('93', plain,
% 0.66/0.86      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('94', plain, ((l1_pre_topc @ sk_B)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('95', plain, ((v2_pre_topc @ sk_B)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('96', plain,
% 0.66/0.86      (![X0 : $i]:
% 0.66/0.86         ((v2_struct_0 @ sk_A)
% 0.66/0.86          | ((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0)
% 0.66/0.86              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.86                 sk_E @ (u1_struct_0 @ X0)))
% 0.66/0.86          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.66/0.86          | (v2_struct_0 @ sk_B))),
% 0.66/0.86      inference('demod', [status(thm)],
% 0.66/0.86                ['89', '90', '91', '92', '93', '94', '95'])).
% 0.66/0.86  thf('97', plain,
% 0.66/0.86      (((v2_struct_0 @ sk_B)
% 0.66/0.86        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 0.66/0.86            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.86               sk_E @ (u1_struct_0 @ sk_D)))
% 0.66/0.86        | (v2_struct_0 @ sk_A))),
% 0.66/0.86      inference('sup-', [status(thm)], ['86', '96'])).
% 0.66/0.86  thf('98', plain, (~ (v2_struct_0 @ sk_B)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('99', plain,
% 0.66/0.86      (((v2_struct_0 @ sk_A)
% 0.66/0.86        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 0.66/0.86            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.86               sk_E @ (u1_struct_0 @ sk_D))))),
% 0.66/0.86      inference('clc', [status(thm)], ['97', '98'])).
% 0.66/0.86  thf('100', plain, (~ (v2_struct_0 @ sk_A)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('101', plain,
% 0.66/0.86      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 0.66/0.86         = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.66/0.86            (u1_struct_0 @ sk_D)))),
% 0.66/0.86      inference('clc', [status(thm)], ['99', '100'])).
% 0.66/0.86  thf('102', plain,
% 0.66/0.86      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 0.66/0.86         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))),
% 0.66/0.86      inference('sup+', [status(thm)], ['85', '101'])).
% 0.66/0.86  thf('103', plain,
% 0.66/0.86      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 0.66/0.86         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))),
% 0.66/0.86      inference('sup+', [status(thm)], ['85', '101'])).
% 0.66/0.86  thf('104', plain,
% 0.66/0.86      (![X0 : $i, X1 : $i]:
% 0.66/0.86         ((m1_subset_1 @ 
% 0.66/0.86           (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ 
% 0.66/0.86            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.66/0.86           (k1_zfmisc_1 @ 
% 0.66/0.86            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.66/0.86          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.66/0.86               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.66/0.86          | (v2_struct_0 @ X1)
% 0.66/0.86          | ~ (v2_pre_topc @ X1)
% 0.66/0.86          | ~ (l1_pre_topc @ X1)
% 0.66/0.86          | (v2_struct_0 @ sk_B)
% 0.66/0.86          | ~ (m1_pre_topc @ sk_D @ X1)
% 0.66/0.86          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.66/0.86      inference('demod', [status(thm)], ['64', '102', '103'])).
% 0.66/0.86  thf('105', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('106', plain,
% 0.66/0.86      (![X18 : $i]: ((m1_pre_topc @ X18 @ X18) | ~ (l1_pre_topc @ X18))),
% 0.66/0.86      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.66/0.86  thf('107', plain,
% 0.66/0.86      ((m1_subset_1 @ sk_E @ 
% 0.66/0.86        (k1_zfmisc_1 @ 
% 0.66/0.86         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('108', plain,
% 0.66/0.86      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.66/0.86         (~ (m1_pre_topc @ X13 @ X14)
% 0.66/0.86          | ~ (m1_pre_topc @ X15 @ X14)
% 0.66/0.86          | ~ (l1_pre_topc @ X16)
% 0.66/0.86          | ~ (v2_pre_topc @ X16)
% 0.66/0.86          | (v2_struct_0 @ X16)
% 0.66/0.86          | ~ (l1_pre_topc @ X14)
% 0.66/0.86          | ~ (v2_pre_topc @ X14)
% 0.66/0.86          | (v2_struct_0 @ X14)
% 0.66/0.86          | ~ (v1_funct_1 @ X17)
% 0.66/0.86          | ~ (v1_funct_2 @ X17 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X16))
% 0.66/0.86          | ~ (m1_subset_1 @ X17 @ 
% 0.66/0.86               (k1_zfmisc_1 @ 
% 0.66/0.86                (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X16))))
% 0.66/0.86          | (v1_funct_2 @ (k3_tmap_1 @ X14 @ X16 @ X15 @ X13 @ X17) @ 
% 0.66/0.86             (u1_struct_0 @ X13) @ (u1_struct_0 @ X16)))),
% 0.66/0.86      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 0.66/0.86  thf('109', plain,
% 0.66/0.86      (![X0 : $i, X1 : $i]:
% 0.66/0.86         ((v1_funct_2 @ (k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 0.66/0.86           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.66/0.86          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.66/0.86          | ~ (v1_funct_1 @ sk_E)
% 0.66/0.86          | (v2_struct_0 @ X1)
% 0.66/0.86          | ~ (v2_pre_topc @ X1)
% 0.66/0.86          | ~ (l1_pre_topc @ X1)
% 0.66/0.86          | (v2_struct_0 @ sk_B)
% 0.66/0.86          | ~ (v2_pre_topc @ sk_B)
% 0.66/0.86          | ~ (l1_pre_topc @ sk_B)
% 0.66/0.86          | ~ (m1_pre_topc @ sk_A @ X1)
% 0.66/0.86          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.66/0.86      inference('sup-', [status(thm)], ['107', '108'])).
% 0.66/0.86  thf('110', plain,
% 0.66/0.86      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('111', plain, ((v1_funct_1 @ sk_E)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('112', plain, ((v2_pre_topc @ sk_B)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('113', plain, ((l1_pre_topc @ sk_B)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('114', plain,
% 0.66/0.86      (![X0 : $i, X1 : $i]:
% 0.66/0.86         ((v1_funct_2 @ (k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 0.66/0.86           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.66/0.86          | (v2_struct_0 @ X1)
% 0.66/0.86          | ~ (v2_pre_topc @ X1)
% 0.66/0.86          | ~ (l1_pre_topc @ X1)
% 0.66/0.86          | (v2_struct_0 @ sk_B)
% 0.66/0.86          | ~ (m1_pre_topc @ sk_A @ X1)
% 0.66/0.86          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.66/0.86      inference('demod', [status(thm)], ['109', '110', '111', '112', '113'])).
% 0.66/0.86  thf('115', plain,
% 0.66/0.86      (![X0 : $i]:
% 0.66/0.86         (~ (l1_pre_topc @ sk_A)
% 0.66/0.86          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.66/0.86          | (v2_struct_0 @ sk_B)
% 0.66/0.86          | ~ (l1_pre_topc @ sk_A)
% 0.66/0.86          | ~ (v2_pre_topc @ sk_A)
% 0.66/0.86          | (v2_struct_0 @ sk_A)
% 0.66/0.86          | (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 0.66/0.86             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 0.66/0.86      inference('sup-', [status(thm)], ['106', '114'])).
% 0.66/0.86  thf('116', plain, ((l1_pre_topc @ sk_A)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('117', plain, ((l1_pre_topc @ sk_A)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('118', plain, ((v2_pre_topc @ sk_A)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('119', plain,
% 0.66/0.86      (![X0 : $i]:
% 0.66/0.86         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.66/0.86          | (v2_struct_0 @ sk_B)
% 0.66/0.86          | (v2_struct_0 @ sk_A)
% 0.66/0.86          | (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 0.66/0.86             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 0.66/0.86      inference('demod', [status(thm)], ['115', '116', '117', '118'])).
% 0.66/0.86  thf('120', plain,
% 0.66/0.86      (((v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E) @ 
% 0.66/0.86         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.66/0.86        | (v2_struct_0 @ sk_A)
% 0.66/0.86        | (v2_struct_0 @ sk_B))),
% 0.66/0.86      inference('sup-', [status(thm)], ['105', '119'])).
% 0.66/0.86  thf('121', plain,
% 0.66/0.86      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 0.66/0.86         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))),
% 0.66/0.86      inference('sup+', [status(thm)], ['85', '101'])).
% 0.66/0.86  thf('122', plain,
% 0.66/0.86      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.66/0.86         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.66/0.86        | (v2_struct_0 @ sk_A)
% 0.66/0.86        | (v2_struct_0 @ sk_B))),
% 0.66/0.86      inference('demod', [status(thm)], ['120', '121'])).
% 0.66/0.86  thf('123', plain, (~ (v2_struct_0 @ sk_A)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('124', plain,
% 0.66/0.86      (((v2_struct_0 @ sk_B)
% 0.66/0.86        | (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.66/0.86           (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))),
% 0.66/0.86      inference('clc', [status(thm)], ['122', '123'])).
% 0.66/0.86  thf('125', plain, (~ (v2_struct_0 @ sk_B)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('126', plain,
% 0.66/0.86      ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.66/0.86        (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.66/0.86      inference('clc', [status(thm)], ['124', '125'])).
% 0.66/0.86  thf('127', plain,
% 0.66/0.86      (![X0 : $i, X1 : $i]:
% 0.66/0.86         ((m1_subset_1 @ 
% 0.66/0.86           (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ 
% 0.66/0.86            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.66/0.86           (k1_zfmisc_1 @ 
% 0.66/0.86            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.66/0.86          | (v2_struct_0 @ X1)
% 0.66/0.86          | ~ (v2_pre_topc @ X1)
% 0.66/0.86          | ~ (l1_pre_topc @ X1)
% 0.66/0.86          | (v2_struct_0 @ sk_B)
% 0.66/0.86          | ~ (m1_pre_topc @ sk_D @ X1)
% 0.66/0.86          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.66/0.86      inference('demod', [status(thm)], ['104', '126'])).
% 0.66/0.86  thf('128', plain,
% 0.66/0.86      (![X0 : $i]:
% 0.66/0.86         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.66/0.86          | (v2_struct_0 @ sk_B)
% 0.66/0.86          | ~ (l1_pre_topc @ sk_A)
% 0.66/0.86          | ~ (v2_pre_topc @ sk_A)
% 0.66/0.86          | (v2_struct_0 @ sk_A)
% 0.66/0.86          | (m1_subset_1 @ 
% 0.66/0.86             (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ 
% 0.66/0.86              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.66/0.86             (k1_zfmisc_1 @ 
% 0.66/0.86              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))))),
% 0.66/0.86      inference('sup-', [status(thm)], ['18', '127'])).
% 0.66/0.86  thf('129', plain, ((l1_pre_topc @ sk_A)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('130', plain, ((v2_pre_topc @ sk_A)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('131', plain,
% 0.66/0.86      (![X0 : $i]:
% 0.66/0.86         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.66/0.86          | (v2_struct_0 @ sk_B)
% 0.66/0.86          | (v2_struct_0 @ sk_A)
% 0.66/0.86          | (m1_subset_1 @ 
% 0.66/0.86             (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ 
% 0.66/0.86              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.66/0.86             (k1_zfmisc_1 @ 
% 0.66/0.86              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))))),
% 0.66/0.86      inference('demod', [status(thm)], ['128', '129', '130'])).
% 0.66/0.86  thf('132', plain,
% 0.66/0.86      (((m1_subset_1 @ 
% 0.66/0.86         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ 
% 0.66/0.86          (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.66/0.86         (k1_zfmisc_1 @ 
% 0.66/0.86          (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 0.66/0.86        | (v2_struct_0 @ sk_A)
% 0.66/0.86        | (v2_struct_0 @ sk_B))),
% 0.66/0.86      inference('sup-', [status(thm)], ['17', '131'])).
% 0.66/0.86  thf('133', plain, (~ (v2_struct_0 @ sk_A)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('134', plain,
% 0.66/0.86      (((v2_struct_0 @ sk_B)
% 0.66/0.86        | (m1_subset_1 @ 
% 0.66/0.86           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ 
% 0.66/0.86            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.66/0.86           (k1_zfmisc_1 @ 
% 0.66/0.86            (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))))),
% 0.66/0.86      inference('clc', [status(thm)], ['132', '133'])).
% 0.66/0.86  thf('135', plain, (~ (v2_struct_0 @ sk_B)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('136', plain,
% 0.66/0.86      ((m1_subset_1 @ 
% 0.66/0.86        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ 
% 0.66/0.86         (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.66/0.86        (k1_zfmisc_1 @ 
% 0.66/0.86         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.66/0.86      inference('clc', [status(thm)], ['134', '135'])).
% 0.66/0.86  thf(redefinition_r2_funct_2, axiom,
% 0.66/0.86    (![A:$i,B:$i,C:$i,D:$i]:
% 0.66/0.86     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.66/0.86         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.66/0.86         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.66/0.86         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.66/0.86       ( ( r2_funct_2 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.66/0.86  thf('137', plain,
% 0.66/0.86      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.66/0.86         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 0.66/0.86          | ~ (v1_funct_2 @ X0 @ X1 @ X2)
% 0.66/0.86          | ~ (v1_funct_1 @ X0)
% 0.66/0.86          | ~ (v1_funct_1 @ X3)
% 0.66/0.86          | ~ (v1_funct_2 @ X3 @ X1 @ X2)
% 0.66/0.86          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 0.66/0.86          | ((X0) = (X3))
% 0.66/0.86          | ~ (r2_funct_2 @ X1 @ X2 @ X0 @ X3))),
% 0.66/0.86      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 0.66/0.86  thf('138', plain,
% 0.66/0.86      (![X0 : $i]:
% 0.66/0.86         (~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.86             (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ 
% 0.66/0.86              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.66/0.86             X0)
% 0.66/0.86          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ 
% 0.66/0.86              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) = (X0))
% 0.66/0.86          | ~ (m1_subset_1 @ X0 @ 
% 0.66/0.86               (k1_zfmisc_1 @ 
% 0.66/0.86                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 0.66/0.86          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.66/0.86          | ~ (v1_funct_1 @ X0)
% 0.66/0.86          | ~ (v1_funct_1 @ 
% 0.66/0.86               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ 
% 0.66/0.86                (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)))
% 0.66/0.86          | ~ (v1_funct_2 @ 
% 0.66/0.86               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ 
% 0.66/0.86                (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.66/0.86               (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 0.66/0.86      inference('sup-', [status(thm)], ['136', '137'])).
% 0.66/0.86  thf('139', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('140', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('141', plain,
% 0.66/0.86      ((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E) @ 
% 0.66/0.86        (k1_zfmisc_1 @ 
% 0.66/0.86         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.66/0.86      inference('clc', [status(thm)], ['36', '37'])).
% 0.66/0.86  thf('142', plain,
% 0.66/0.86      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.66/0.86         (~ (m1_pre_topc @ X13 @ X14)
% 0.66/0.86          | ~ (m1_pre_topc @ X15 @ X14)
% 0.66/0.86          | ~ (l1_pre_topc @ X16)
% 0.66/0.86          | ~ (v2_pre_topc @ X16)
% 0.66/0.86          | (v2_struct_0 @ X16)
% 0.66/0.86          | ~ (l1_pre_topc @ X14)
% 0.66/0.86          | ~ (v2_pre_topc @ X14)
% 0.66/0.86          | (v2_struct_0 @ X14)
% 0.66/0.86          | ~ (v1_funct_1 @ X17)
% 0.66/0.86          | ~ (v1_funct_2 @ X17 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X16))
% 0.66/0.86          | ~ (m1_subset_1 @ X17 @ 
% 0.66/0.86               (k1_zfmisc_1 @ 
% 0.66/0.86                (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X16))))
% 0.66/0.86          | (v1_funct_1 @ (k3_tmap_1 @ X14 @ X16 @ X15 @ X13 @ X17)))),
% 0.66/0.86      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 0.66/0.86  thf('143', plain,
% 0.66/0.86      (![X0 : $i, X1 : $i]:
% 0.66/0.86         ((v1_funct_1 @ 
% 0.66/0.86           (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ 
% 0.66/0.86            (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E)))
% 0.66/0.86          | ~ (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E) @ 
% 0.66/0.86               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.66/0.86          | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))
% 0.66/0.86          | (v2_struct_0 @ X1)
% 0.66/0.86          | ~ (v2_pre_topc @ X1)
% 0.66/0.86          | ~ (l1_pre_topc @ X1)
% 0.66/0.86          | (v2_struct_0 @ sk_B)
% 0.66/0.86          | ~ (v2_pre_topc @ sk_B)
% 0.66/0.86          | ~ (l1_pre_topc @ sk_B)
% 0.66/0.86          | ~ (m1_pre_topc @ sk_D @ X1)
% 0.66/0.86          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.66/0.86      inference('sup-', [status(thm)], ['141', '142'])).
% 0.66/0.86  thf('144', plain, ((v2_pre_topc @ sk_B)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('145', plain, ((l1_pre_topc @ sk_B)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('146', plain,
% 0.66/0.86      (![X0 : $i, X1 : $i]:
% 0.66/0.86         ((v1_funct_1 @ 
% 0.66/0.86           (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ 
% 0.66/0.86            (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E)))
% 0.66/0.86          | ~ (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E) @ 
% 0.66/0.86               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.66/0.86          | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))
% 0.66/0.86          | (v2_struct_0 @ X1)
% 0.66/0.86          | ~ (v2_pre_topc @ X1)
% 0.66/0.86          | ~ (l1_pre_topc @ X1)
% 0.66/0.86          | (v2_struct_0 @ sk_B)
% 0.66/0.86          | ~ (m1_pre_topc @ sk_D @ X1)
% 0.66/0.86          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.66/0.86      inference('demod', [status(thm)], ['143', '144', '145'])).
% 0.66/0.86  thf('147', plain,
% 0.66/0.86      ((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))),
% 0.66/0.86      inference('clc', [status(thm)], ['61', '62'])).
% 0.66/0.86  thf('148', plain,
% 0.66/0.86      (![X0 : $i, X1 : $i]:
% 0.66/0.86         ((v1_funct_1 @ 
% 0.66/0.86           (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ 
% 0.66/0.86            (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E)))
% 0.66/0.86          | ~ (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E) @ 
% 0.66/0.86               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.66/0.86          | (v2_struct_0 @ X1)
% 0.66/0.86          | ~ (v2_pre_topc @ X1)
% 0.66/0.86          | ~ (l1_pre_topc @ X1)
% 0.66/0.86          | (v2_struct_0 @ sk_B)
% 0.66/0.86          | ~ (m1_pre_topc @ sk_D @ X1)
% 0.66/0.86          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.66/0.86      inference('demod', [status(thm)], ['146', '147'])).
% 0.66/0.86  thf('149', plain,
% 0.66/0.86      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 0.66/0.86         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))),
% 0.66/0.86      inference('sup+', [status(thm)], ['85', '101'])).
% 0.66/0.86  thf('150', plain,
% 0.66/0.86      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 0.66/0.86         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))),
% 0.66/0.86      inference('sup+', [status(thm)], ['85', '101'])).
% 0.66/0.86  thf('151', plain,
% 0.66/0.86      (![X0 : $i, X1 : $i]:
% 0.66/0.86         ((v1_funct_1 @ 
% 0.66/0.86           (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ 
% 0.66/0.86            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)))
% 0.66/0.86          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.66/0.86               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.66/0.86          | (v2_struct_0 @ X1)
% 0.66/0.86          | ~ (v2_pre_topc @ X1)
% 0.66/0.86          | ~ (l1_pre_topc @ X1)
% 0.66/0.86          | (v2_struct_0 @ sk_B)
% 0.66/0.86          | ~ (m1_pre_topc @ sk_D @ X1)
% 0.66/0.86          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.66/0.86      inference('demod', [status(thm)], ['148', '149', '150'])).
% 0.66/0.86  thf('152', plain,
% 0.66/0.86      ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.66/0.86        (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.66/0.86      inference('clc', [status(thm)], ['124', '125'])).
% 0.66/0.86  thf('153', plain,
% 0.66/0.86      (![X0 : $i, X1 : $i]:
% 0.66/0.86         ((v1_funct_1 @ 
% 0.66/0.86           (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ 
% 0.66/0.86            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)))
% 0.66/0.86          | (v2_struct_0 @ X1)
% 0.66/0.86          | ~ (v2_pre_topc @ X1)
% 0.66/0.86          | ~ (l1_pre_topc @ X1)
% 0.66/0.86          | (v2_struct_0 @ sk_B)
% 0.66/0.86          | ~ (m1_pre_topc @ sk_D @ X1)
% 0.66/0.86          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.66/0.86      inference('demod', [status(thm)], ['151', '152'])).
% 0.66/0.86  thf('154', plain,
% 0.66/0.86      (![X0 : $i]:
% 0.66/0.86         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.66/0.86          | (v2_struct_0 @ sk_B)
% 0.66/0.86          | ~ (l1_pre_topc @ sk_A)
% 0.66/0.86          | ~ (v2_pre_topc @ sk_A)
% 0.66/0.86          | (v2_struct_0 @ sk_A)
% 0.66/0.86          | (v1_funct_1 @ 
% 0.66/0.86             (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ 
% 0.66/0.86              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))))),
% 0.66/0.86      inference('sup-', [status(thm)], ['140', '153'])).
% 0.66/0.86  thf('155', plain, ((l1_pre_topc @ sk_A)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('156', plain, ((v2_pre_topc @ sk_A)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('157', plain,
% 0.66/0.86      (![X0 : $i]:
% 0.66/0.86         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.66/0.86          | (v2_struct_0 @ sk_B)
% 0.66/0.86          | (v2_struct_0 @ sk_A)
% 0.66/0.86          | (v1_funct_1 @ 
% 0.66/0.86             (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ 
% 0.66/0.86              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))))),
% 0.66/0.86      inference('demod', [status(thm)], ['154', '155', '156'])).
% 0.66/0.86  thf('158', plain,
% 0.66/0.86      (((v1_funct_1 @ 
% 0.66/0.86         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ 
% 0.66/0.86          (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)))
% 0.66/0.86        | (v2_struct_0 @ sk_A)
% 0.66/0.86        | (v2_struct_0 @ sk_B))),
% 0.66/0.86      inference('sup-', [status(thm)], ['139', '157'])).
% 0.66/0.86  thf('159', plain, (~ (v2_struct_0 @ sk_A)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('160', plain,
% 0.66/0.86      (((v2_struct_0 @ sk_B)
% 0.66/0.86        | (v1_funct_1 @ 
% 0.66/0.86           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ 
% 0.66/0.86            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))))),
% 0.66/0.86      inference('clc', [status(thm)], ['158', '159'])).
% 0.66/0.86  thf('161', plain, (~ (v2_struct_0 @ sk_B)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('162', plain,
% 0.66/0.86      ((v1_funct_1 @ 
% 0.66/0.86        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ 
% 0.66/0.86         (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)))),
% 0.66/0.86      inference('clc', [status(thm)], ['160', '161'])).
% 0.66/0.86  thf('163', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('164', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('165', plain,
% 0.66/0.86      ((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E) @ 
% 0.66/0.86        (k1_zfmisc_1 @ 
% 0.66/0.86         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.66/0.86      inference('clc', [status(thm)], ['36', '37'])).
% 0.66/0.86  thf('166', plain,
% 0.66/0.86      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 0.66/0.86         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))),
% 0.66/0.86      inference('sup+', [status(thm)], ['85', '101'])).
% 0.66/0.86  thf('167', plain,
% 0.66/0.86      ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.66/0.86        (k1_zfmisc_1 @ 
% 0.66/0.86         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.66/0.86      inference('demod', [status(thm)], ['165', '166'])).
% 0.66/0.86  thf('168', plain,
% 0.66/0.86      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.66/0.86         (~ (m1_pre_topc @ X13 @ X14)
% 0.66/0.86          | ~ (m1_pre_topc @ X15 @ X14)
% 0.66/0.86          | ~ (l1_pre_topc @ X16)
% 0.66/0.86          | ~ (v2_pre_topc @ X16)
% 0.66/0.86          | (v2_struct_0 @ X16)
% 0.66/0.86          | ~ (l1_pre_topc @ X14)
% 0.66/0.86          | ~ (v2_pre_topc @ X14)
% 0.66/0.86          | (v2_struct_0 @ X14)
% 0.66/0.86          | ~ (v1_funct_1 @ X17)
% 0.66/0.86          | ~ (v1_funct_2 @ X17 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X16))
% 0.66/0.86          | ~ (m1_subset_1 @ X17 @ 
% 0.66/0.86               (k1_zfmisc_1 @ 
% 0.66/0.86                (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X16))))
% 0.66/0.86          | (v1_funct_2 @ (k3_tmap_1 @ X14 @ X16 @ X15 @ X13 @ X17) @ 
% 0.66/0.86             (u1_struct_0 @ X13) @ (u1_struct_0 @ X16)))),
% 0.66/0.86      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 0.66/0.86  thf('169', plain,
% 0.66/0.86      (![X0 : $i, X1 : $i]:
% 0.66/0.86         ((v1_funct_2 @ 
% 0.66/0.86           (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ 
% 0.66/0.86            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.66/0.86           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.66/0.86          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.66/0.86               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.66/0.86          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))
% 0.66/0.86          | (v2_struct_0 @ X1)
% 0.66/0.86          | ~ (v2_pre_topc @ X1)
% 0.66/0.86          | ~ (l1_pre_topc @ X1)
% 0.66/0.86          | (v2_struct_0 @ sk_B)
% 0.66/0.86          | ~ (v2_pre_topc @ sk_B)
% 0.66/0.86          | ~ (l1_pre_topc @ sk_B)
% 0.66/0.86          | ~ (m1_pre_topc @ sk_D @ X1)
% 0.66/0.86          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.66/0.86      inference('sup-', [status(thm)], ['167', '168'])).
% 0.66/0.86  thf('170', plain,
% 0.66/0.86      ((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))),
% 0.66/0.86      inference('clc', [status(thm)], ['61', '62'])).
% 0.66/0.86  thf('171', plain,
% 0.66/0.86      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 0.66/0.86         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))),
% 0.66/0.86      inference('sup+', [status(thm)], ['85', '101'])).
% 0.66/0.86  thf('172', plain, ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))),
% 0.66/0.86      inference('demod', [status(thm)], ['170', '171'])).
% 0.66/0.86  thf('173', plain, ((v2_pre_topc @ sk_B)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('174', plain, ((l1_pre_topc @ sk_B)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('175', plain,
% 0.66/0.86      (![X0 : $i, X1 : $i]:
% 0.66/0.86         ((v1_funct_2 @ 
% 0.66/0.86           (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ 
% 0.66/0.86            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.66/0.86           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.66/0.86          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.66/0.86               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.66/0.86          | (v2_struct_0 @ X1)
% 0.66/0.86          | ~ (v2_pre_topc @ X1)
% 0.66/0.86          | ~ (l1_pre_topc @ X1)
% 0.66/0.86          | (v2_struct_0 @ sk_B)
% 0.66/0.86          | ~ (m1_pre_topc @ sk_D @ X1)
% 0.66/0.86          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.66/0.86      inference('demod', [status(thm)], ['169', '172', '173', '174'])).
% 0.66/0.86  thf('176', plain,
% 0.66/0.86      ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.66/0.86        (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.66/0.86      inference('clc', [status(thm)], ['124', '125'])).
% 0.66/0.86  thf('177', plain,
% 0.66/0.86      (![X0 : $i, X1 : $i]:
% 0.66/0.86         ((v1_funct_2 @ 
% 0.66/0.86           (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ 
% 0.66/0.86            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.66/0.86           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.66/0.86          | (v2_struct_0 @ X1)
% 0.66/0.86          | ~ (v2_pre_topc @ X1)
% 0.66/0.86          | ~ (l1_pre_topc @ X1)
% 0.66/0.86          | (v2_struct_0 @ sk_B)
% 0.66/0.86          | ~ (m1_pre_topc @ sk_D @ X1)
% 0.66/0.86          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.66/0.86      inference('demod', [status(thm)], ['175', '176'])).
% 0.66/0.86  thf('178', plain,
% 0.66/0.86      (![X0 : $i]:
% 0.66/0.86         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.66/0.86          | (v2_struct_0 @ sk_B)
% 0.66/0.86          | ~ (l1_pre_topc @ sk_A)
% 0.66/0.86          | ~ (v2_pre_topc @ sk_A)
% 0.66/0.86          | (v2_struct_0 @ sk_A)
% 0.66/0.86          | (v1_funct_2 @ 
% 0.66/0.86             (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ 
% 0.66/0.86              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.66/0.86             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 0.66/0.86      inference('sup-', [status(thm)], ['164', '177'])).
% 0.66/0.86  thf('179', plain, ((l1_pre_topc @ sk_A)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('180', plain, ((v2_pre_topc @ sk_A)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('181', plain,
% 0.66/0.86      (![X0 : $i]:
% 0.66/0.86         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.66/0.86          | (v2_struct_0 @ sk_B)
% 0.66/0.86          | (v2_struct_0 @ sk_A)
% 0.66/0.86          | (v1_funct_2 @ 
% 0.66/0.86             (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ 
% 0.66/0.86              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.66/0.86             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 0.66/0.86      inference('demod', [status(thm)], ['178', '179', '180'])).
% 0.66/0.86  thf('182', plain,
% 0.66/0.86      (((v1_funct_2 @ 
% 0.66/0.86         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ 
% 0.66/0.86          (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.66/0.86         (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.66/0.86        | (v2_struct_0 @ sk_A)
% 0.66/0.86        | (v2_struct_0 @ sk_B))),
% 0.66/0.86      inference('sup-', [status(thm)], ['163', '181'])).
% 0.66/0.86  thf('183', plain, (~ (v2_struct_0 @ sk_A)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('184', plain,
% 0.66/0.86      (((v2_struct_0 @ sk_B)
% 0.66/0.86        | (v1_funct_2 @ 
% 0.66/0.86           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ 
% 0.66/0.86            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.66/0.86           (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 0.66/0.86      inference('clc', [status(thm)], ['182', '183'])).
% 0.66/0.86  thf('185', plain, (~ (v2_struct_0 @ sk_B)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('186', plain,
% 0.66/0.86      ((v1_funct_2 @ 
% 0.66/0.86        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ 
% 0.66/0.86         (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.66/0.86        (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.66/0.86      inference('clc', [status(thm)], ['184', '185'])).
% 0.66/0.86  thf('187', plain,
% 0.66/0.86      (![X0 : $i]:
% 0.66/0.86         (~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.86             (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ 
% 0.66/0.86              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.66/0.86             X0)
% 0.66/0.86          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ 
% 0.66/0.86              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) = (X0))
% 0.66/0.86          | ~ (m1_subset_1 @ X0 @ 
% 0.66/0.86               (k1_zfmisc_1 @ 
% 0.66/0.86                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 0.66/0.86          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.66/0.86          | ~ (v1_funct_1 @ X0))),
% 0.66/0.86      inference('demod', [status(thm)], ['138', '162', '186'])).
% 0.66/0.86  thf('188', plain,
% 0.66/0.86      (((v2_struct_0 @ sk_B)
% 0.66/0.86        | (v2_struct_0 @ sk_D)
% 0.66/0.86        | (v2_struct_0 @ sk_C)
% 0.66/0.86        | (v2_struct_0 @ sk_A)
% 0.66/0.86        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C))
% 0.66/0.86        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 0.66/0.86             (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.66/0.86        | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 0.66/0.86             (k1_zfmisc_1 @ 
% 0.66/0.86              (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 0.66/0.86        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ 
% 0.66/0.86            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))
% 0.66/0.86            = (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C)))),
% 0.66/0.86      inference('sup-', [status(thm)], ['16', '187'])).
% 0.66/0.86  thf('189', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('190', plain,
% 0.66/0.86      (![X0 : $i]:
% 0.66/0.86         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.66/0.86          | (v2_struct_0 @ sk_B)
% 0.66/0.86          | (v2_struct_0 @ sk_A)
% 0.66/0.86          | (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E)))),
% 0.66/0.86      inference('demod', [status(thm)], ['54', '55', '56', '57'])).
% 0.66/0.86  thf('191', plain,
% 0.66/0.86      (((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E))
% 0.66/0.86        | (v2_struct_0 @ sk_A)
% 0.66/0.86        | (v2_struct_0 @ sk_B))),
% 0.66/0.86      inference('sup-', [status(thm)], ['189', '190'])).
% 0.66/0.86  thf('192', plain, (~ (v2_struct_0 @ sk_A)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('193', plain,
% 0.66/0.86      (((v2_struct_0 @ sk_B)
% 0.66/0.86        | (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E)))),
% 0.66/0.86      inference('clc', [status(thm)], ['191', '192'])).
% 0.66/0.86  thf('194', plain, (~ (v2_struct_0 @ sk_B)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('195', plain,
% 0.66/0.86      ((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E))),
% 0.66/0.86      inference('clc', [status(thm)], ['193', '194'])).
% 0.66/0.86  thf('196', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('197', plain,
% 0.66/0.86      (![X0 : $i]:
% 0.66/0.86         ((v2_struct_0 @ sk_A)
% 0.66/0.86          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E)
% 0.66/0.86              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.86                 sk_E @ (u1_struct_0 @ X0)))
% 0.66/0.86          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.66/0.86          | (v2_struct_0 @ sk_B))),
% 0.66/0.86      inference('simplify', [status(thm)], ['79'])).
% 0.66/0.86  thf('198', plain,
% 0.66/0.86      (((v2_struct_0 @ sk_B)
% 0.66/0.86        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E)
% 0.66/0.86            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.86               sk_E @ (u1_struct_0 @ sk_C)))
% 0.66/0.86        | (v2_struct_0 @ sk_A))),
% 0.66/0.86      inference('sup-', [status(thm)], ['196', '197'])).
% 0.66/0.86  thf('199', plain, (~ (v2_struct_0 @ sk_B)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('200', plain,
% 0.66/0.86      (((v2_struct_0 @ sk_A)
% 0.66/0.86        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E)
% 0.66/0.86            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.86               sk_E @ (u1_struct_0 @ sk_C))))),
% 0.66/0.86      inference('clc', [status(thm)], ['198', '199'])).
% 0.66/0.86  thf('201', plain, (~ (v2_struct_0 @ sk_A)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('202', plain,
% 0.66/0.86      (((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E)
% 0.66/0.86         = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.66/0.86            (u1_struct_0 @ sk_C)))),
% 0.66/0.86      inference('clc', [status(thm)], ['200', '201'])).
% 0.66/0.86  thf('203', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('204', plain,
% 0.66/0.86      (![X0 : $i]:
% 0.66/0.86         ((v2_struct_0 @ sk_A)
% 0.66/0.86          | ((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0)
% 0.66/0.86              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.86                 sk_E @ (u1_struct_0 @ X0)))
% 0.66/0.86          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.66/0.86          | (v2_struct_0 @ sk_B))),
% 0.66/0.86      inference('demod', [status(thm)],
% 0.66/0.86                ['89', '90', '91', '92', '93', '94', '95'])).
% 0.66/0.86  thf('205', plain,
% 0.66/0.86      (((v2_struct_0 @ sk_B)
% 0.66/0.86        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C)
% 0.66/0.86            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.86               sk_E @ (u1_struct_0 @ sk_C)))
% 0.66/0.86        | (v2_struct_0 @ sk_A))),
% 0.66/0.86      inference('sup-', [status(thm)], ['203', '204'])).
% 0.66/0.86  thf('206', plain, (~ (v2_struct_0 @ sk_B)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('207', plain,
% 0.66/0.86      (((v2_struct_0 @ sk_A)
% 0.66/0.86        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C)
% 0.66/0.86            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.66/0.86               sk_E @ (u1_struct_0 @ sk_C))))),
% 0.66/0.86      inference('clc', [status(thm)], ['205', '206'])).
% 0.66/0.86  thf('208', plain, (~ (v2_struct_0 @ sk_A)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('209', plain,
% 0.66/0.86      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C)
% 0.66/0.86         = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.66/0.86            (u1_struct_0 @ sk_C)))),
% 0.66/0.86      inference('clc', [status(thm)], ['207', '208'])).
% 0.66/0.86  thf('210', plain,
% 0.66/0.86      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C)
% 0.66/0.86         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E))),
% 0.66/0.86      inference('sup+', [status(thm)], ['202', '209'])).
% 0.66/0.86  thf('211', plain, ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C))),
% 0.66/0.86      inference('demod', [status(thm)], ['195', '210'])).
% 0.66/0.86  thf('212', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('213', plain,
% 0.66/0.86      (![X0 : $i]:
% 0.66/0.86         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.66/0.86          | (v2_struct_0 @ sk_B)
% 0.66/0.86          | (v2_struct_0 @ sk_A)
% 0.66/0.86          | (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 0.66/0.86             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 0.66/0.86      inference('demod', [status(thm)], ['115', '116', '117', '118'])).
% 0.66/0.86  thf('214', plain,
% 0.66/0.86      (((v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E) @ 
% 0.66/0.86         (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.66/0.86        | (v2_struct_0 @ sk_A)
% 0.66/0.86        | (v2_struct_0 @ sk_B))),
% 0.66/0.86      inference('sup-', [status(thm)], ['212', '213'])).
% 0.66/0.86  thf('215', plain,
% 0.66/0.86      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C)
% 0.66/0.86         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E))),
% 0.66/0.86      inference('sup+', [status(thm)], ['202', '209'])).
% 0.66/0.86  thf('216', plain,
% 0.66/0.86      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 0.66/0.86         (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.66/0.86        | (v2_struct_0 @ sk_A)
% 0.66/0.86        | (v2_struct_0 @ sk_B))),
% 0.66/0.86      inference('demod', [status(thm)], ['214', '215'])).
% 0.66/0.86  thf('217', plain, (~ (v2_struct_0 @ sk_A)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('218', plain,
% 0.66/0.86      (((v2_struct_0 @ sk_B)
% 0.66/0.86        | (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 0.66/0.86           (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 0.66/0.86      inference('clc', [status(thm)], ['216', '217'])).
% 0.66/0.86  thf('219', plain, (~ (v2_struct_0 @ sk_B)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('220', plain,
% 0.66/0.86      ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 0.66/0.86        (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.66/0.86      inference('clc', [status(thm)], ['218', '219'])).
% 0.66/0.86  thf('221', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('222', plain,
% 0.66/0.86      (![X0 : $i]:
% 0.66/0.86         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.66/0.86          | (v2_struct_0 @ sk_B)
% 0.66/0.86          | (v2_struct_0 @ sk_A)
% 0.66/0.86          | (m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 0.66/0.86             (k1_zfmisc_1 @ 
% 0.66/0.86              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))))),
% 0.66/0.86      inference('demod', [status(thm)], ['29', '30', '31', '32'])).
% 0.66/0.86  thf('223', plain,
% 0.66/0.86      (((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E) @ 
% 0.66/0.86         (k1_zfmisc_1 @ 
% 0.66/0.86          (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 0.66/0.86        | (v2_struct_0 @ sk_A)
% 0.66/0.86        | (v2_struct_0 @ sk_B))),
% 0.66/0.86      inference('sup-', [status(thm)], ['221', '222'])).
% 0.66/0.86  thf('224', plain, (~ (v2_struct_0 @ sk_A)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('225', plain,
% 0.66/0.86      (((v2_struct_0 @ sk_B)
% 0.66/0.86        | (m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E) @ 
% 0.66/0.86           (k1_zfmisc_1 @ 
% 0.66/0.86            (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))))),
% 0.66/0.86      inference('clc', [status(thm)], ['223', '224'])).
% 0.66/0.86  thf('226', plain, (~ (v2_struct_0 @ sk_B)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('227', plain,
% 0.66/0.86      ((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E) @ 
% 0.66/0.86        (k1_zfmisc_1 @ 
% 0.66/0.86         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.66/0.86      inference('clc', [status(thm)], ['225', '226'])).
% 0.66/0.86  thf('228', plain,
% 0.66/0.86      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C)
% 0.66/0.86         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E))),
% 0.66/0.86      inference('sup+', [status(thm)], ['202', '209'])).
% 0.66/0.86  thf('229', plain,
% 0.66/0.86      ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 0.66/0.86        (k1_zfmisc_1 @ 
% 0.66/0.86         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.66/0.86      inference('demod', [status(thm)], ['227', '228'])).
% 0.66/0.86  thf('230', plain,
% 0.66/0.86      (((v2_struct_0 @ sk_B)
% 0.66/0.86        | (v2_struct_0 @ sk_D)
% 0.66/0.86        | (v2_struct_0 @ sk_C)
% 0.66/0.86        | (v2_struct_0 @ sk_A)
% 0.66/0.86        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ 
% 0.66/0.86            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))
% 0.66/0.86            = (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C)))),
% 0.66/0.86      inference('demod', [status(thm)], ['188', '211', '220', '229'])).
% 0.66/0.86  thf('231', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('232', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C))),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('233', plain, (((sk_F) = (sk_G))),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('234', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.66/0.86      inference('demod', [status(thm)], ['232', '233'])).
% 0.66/0.86  thf('235', plain,
% 0.66/0.86      ((r1_tmap_1 @ sk_D @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.66/0.86        sk_F)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('236', plain,
% 0.66/0.86      ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.66/0.86        (k1_zfmisc_1 @ 
% 0.66/0.86         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.66/0.86      inference('demod', [status(thm)], ['165', '166'])).
% 0.66/0.86  thf(t81_tmap_1, axiom,
% 0.66/0.86    (![A:$i]:
% 0.66/0.86     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.66/0.86       ( ![B:$i]:
% 0.66/0.86         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.66/0.86             ( l1_pre_topc @ B ) ) =>
% 0.66/0.86           ( ![C:$i]:
% 0.66/0.86             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.66/0.86               ( ![D:$i]:
% 0.66/0.86                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.66/0.86                   ( ![E:$i]:
% 0.66/0.86                     ( ( ( v1_funct_1 @ E ) & 
% 0.66/0.86                         ( v1_funct_2 @
% 0.66/0.86                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.66/0.86                         ( m1_subset_1 @
% 0.66/0.86                           E @ 
% 0.66/0.86                           ( k1_zfmisc_1 @
% 0.66/0.86                             ( k2_zfmisc_1 @
% 0.66/0.86                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.66/0.86                       ( ![F:$i]:
% 0.66/0.86                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ C ) ) =>
% 0.66/0.86                           ( ![G:$i]:
% 0.66/0.86                             ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.66/0.86                               ( ( ( ( F ) = ( G ) ) & 
% 0.66/0.86                                   ( m1_pre_topc @ D @ C ) & 
% 0.66/0.86                                   ( r1_tmap_1 @ C @ B @ E @ F ) ) =>
% 0.66/0.86                                 ( r1_tmap_1 @
% 0.66/0.86                                   D @ B @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ 
% 0.66/0.86                                   G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.66/0.86  thf('237', plain,
% 0.66/0.86      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.66/0.86         ((v2_struct_0 @ X27)
% 0.66/0.86          | ~ (v2_pre_topc @ X27)
% 0.66/0.86          | ~ (l1_pre_topc @ X27)
% 0.66/0.86          | (v2_struct_0 @ X28)
% 0.66/0.86          | ~ (m1_pre_topc @ X28 @ X29)
% 0.66/0.86          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X31))
% 0.66/0.86          | ~ (m1_pre_topc @ X28 @ X31)
% 0.66/0.86          | ~ (r1_tmap_1 @ X31 @ X27 @ X32 @ X30)
% 0.66/0.86          | ((X30) != (X33))
% 0.66/0.86          | (r1_tmap_1 @ X28 @ X27 @ 
% 0.66/0.86             (k3_tmap_1 @ X29 @ X27 @ X31 @ X28 @ X32) @ X33)
% 0.66/0.86          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X28))
% 0.66/0.86          | ~ (m1_subset_1 @ X32 @ 
% 0.66/0.86               (k1_zfmisc_1 @ 
% 0.66/0.86                (k2_zfmisc_1 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X27))))
% 0.66/0.86          | ~ (v1_funct_2 @ X32 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X27))
% 0.66/0.86          | ~ (v1_funct_1 @ X32)
% 0.66/0.86          | ~ (m1_pre_topc @ X31 @ X29)
% 0.66/0.86          | (v2_struct_0 @ X31)
% 0.66/0.86          | ~ (l1_pre_topc @ X29)
% 0.66/0.86          | ~ (v2_pre_topc @ X29)
% 0.66/0.86          | (v2_struct_0 @ X29))),
% 0.66/0.86      inference('cnf', [status(esa)], [t81_tmap_1])).
% 0.66/0.86  thf('238', plain,
% 0.66/0.86      (![X27 : $i, X28 : $i, X29 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.66/0.86         ((v2_struct_0 @ X29)
% 0.66/0.86          | ~ (v2_pre_topc @ X29)
% 0.66/0.86          | ~ (l1_pre_topc @ X29)
% 0.66/0.86          | (v2_struct_0 @ X31)
% 0.66/0.86          | ~ (m1_pre_topc @ X31 @ X29)
% 0.66/0.86          | ~ (v1_funct_1 @ X32)
% 0.66/0.86          | ~ (v1_funct_2 @ X32 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X27))
% 0.66/0.86          | ~ (m1_subset_1 @ X32 @ 
% 0.66/0.86               (k1_zfmisc_1 @ 
% 0.66/0.86                (k2_zfmisc_1 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X27))))
% 0.66/0.86          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X28))
% 0.66/0.86          | (r1_tmap_1 @ X28 @ X27 @ 
% 0.66/0.86             (k3_tmap_1 @ X29 @ X27 @ X31 @ X28 @ X32) @ X33)
% 0.66/0.86          | ~ (r1_tmap_1 @ X31 @ X27 @ X32 @ X33)
% 0.66/0.86          | ~ (m1_pre_topc @ X28 @ X31)
% 0.66/0.86          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X31))
% 0.66/0.86          | ~ (m1_pre_topc @ X28 @ X29)
% 0.66/0.86          | (v2_struct_0 @ X28)
% 0.66/0.86          | ~ (l1_pre_topc @ X27)
% 0.66/0.86          | ~ (v2_pre_topc @ X27)
% 0.66/0.86          | (v2_struct_0 @ X27))),
% 0.66/0.86      inference('simplify', [status(thm)], ['237'])).
% 0.66/0.86  thf('239', plain,
% 0.66/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.86         ((v2_struct_0 @ sk_B)
% 0.66/0.86          | ~ (v2_pre_topc @ sk_B)
% 0.66/0.86          | ~ (l1_pre_topc @ sk_B)
% 0.66/0.86          | (v2_struct_0 @ X0)
% 0.66/0.86          | ~ (m1_pre_topc @ X0 @ X1)
% 0.66/0.86          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 0.66/0.86          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.66/0.86          | ~ (r1_tmap_1 @ sk_D @ sk_B @ 
% 0.66/0.86               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ X2)
% 0.66/0.86          | (r1_tmap_1 @ X0 @ sk_B @ 
% 0.66/0.86             (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ 
% 0.66/0.86              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.66/0.86             X2)
% 0.66/0.86          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.66/0.86          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.66/0.86               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.66/0.86          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))
% 0.66/0.86          | ~ (m1_pre_topc @ sk_D @ X1)
% 0.66/0.86          | (v2_struct_0 @ sk_D)
% 0.66/0.86          | ~ (l1_pre_topc @ X1)
% 0.66/0.86          | ~ (v2_pre_topc @ X1)
% 0.66/0.86          | (v2_struct_0 @ X1))),
% 0.66/0.86      inference('sup-', [status(thm)], ['236', '238'])).
% 0.66/0.86  thf('240', plain, ((v2_pre_topc @ sk_B)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('241', plain, ((l1_pre_topc @ sk_B)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('242', plain,
% 0.66/0.86      ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.66/0.86        (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.66/0.86      inference('clc', [status(thm)], ['124', '125'])).
% 0.66/0.86  thf('243', plain, ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))),
% 0.66/0.86      inference('demod', [status(thm)], ['170', '171'])).
% 0.66/0.86  thf('244', plain,
% 0.66/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.86         ((v2_struct_0 @ sk_B)
% 0.66/0.86          | (v2_struct_0 @ X0)
% 0.66/0.86          | ~ (m1_pre_topc @ X0 @ X1)
% 0.66/0.86          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 0.66/0.86          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.66/0.86          | ~ (r1_tmap_1 @ sk_D @ sk_B @ 
% 0.66/0.86               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ X2)
% 0.66/0.86          | (r1_tmap_1 @ X0 @ sk_B @ 
% 0.66/0.86             (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ 
% 0.66/0.86              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.66/0.86             X2)
% 0.66/0.86          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.66/0.86          | ~ (m1_pre_topc @ sk_D @ X1)
% 0.66/0.86          | (v2_struct_0 @ sk_D)
% 0.66/0.86          | ~ (l1_pre_topc @ X1)
% 0.66/0.86          | ~ (v2_pre_topc @ X1)
% 0.66/0.86          | (v2_struct_0 @ X1))),
% 0.66/0.86      inference('demod', [status(thm)], ['239', '240', '241', '242', '243'])).
% 0.66/0.86  thf('245', plain,
% 0.66/0.86      (![X0 : $i, X1 : $i]:
% 0.66/0.86         ((v2_struct_0 @ X0)
% 0.66/0.86          | ~ (v2_pre_topc @ X0)
% 0.66/0.86          | ~ (l1_pre_topc @ X0)
% 0.66/0.86          | (v2_struct_0 @ sk_D)
% 0.66/0.86          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.66/0.86          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ X1))
% 0.66/0.86          | (r1_tmap_1 @ X1 @ sk_B @ 
% 0.66/0.86             (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ 
% 0.66/0.86              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.66/0.86             sk_F)
% 0.66/0.86          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.66/0.86          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))
% 0.66/0.86          | ~ (m1_pre_topc @ X1 @ X0)
% 0.66/0.86          | (v2_struct_0 @ X1)
% 0.66/0.86          | (v2_struct_0 @ sk_B))),
% 0.66/0.86      inference('sup-', [status(thm)], ['235', '244'])).
% 0.66/0.86  thf('246', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('247', plain,
% 0.66/0.86      (![X0 : $i, X1 : $i]:
% 0.66/0.86         ((v2_struct_0 @ X0)
% 0.66/0.86          | ~ (v2_pre_topc @ X0)
% 0.66/0.86          | ~ (l1_pre_topc @ X0)
% 0.66/0.86          | (v2_struct_0 @ sk_D)
% 0.66/0.86          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.66/0.86          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ X1))
% 0.66/0.86          | (r1_tmap_1 @ X1 @ sk_B @ 
% 0.66/0.86             (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ 
% 0.66/0.86              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.66/0.86             sk_F)
% 0.66/0.86          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.66/0.86          | ~ (m1_pre_topc @ X1 @ X0)
% 0.66/0.86          | (v2_struct_0 @ X1)
% 0.66/0.86          | (v2_struct_0 @ sk_B))),
% 0.66/0.86      inference('demod', [status(thm)], ['245', '246'])).
% 0.66/0.86  thf('248', plain,
% 0.66/0.86      (![X0 : $i]:
% 0.66/0.86         ((v2_struct_0 @ sk_B)
% 0.66/0.86          | (v2_struct_0 @ sk_C)
% 0.66/0.86          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.66/0.86          | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.66/0.86          | (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.66/0.86             (k3_tmap_1 @ X0 @ sk_B @ sk_D @ sk_C @ 
% 0.66/0.86              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.66/0.86             sk_F)
% 0.66/0.86          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.66/0.86          | (v2_struct_0 @ sk_D)
% 0.66/0.86          | ~ (l1_pre_topc @ X0)
% 0.66/0.86          | ~ (v2_pre_topc @ X0)
% 0.66/0.86          | (v2_struct_0 @ X0))),
% 0.66/0.86      inference('sup-', [status(thm)], ['234', '247'])).
% 0.66/0.86  thf('249', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('250', plain,
% 0.66/0.86      (![X0 : $i]:
% 0.66/0.86         ((v2_struct_0 @ sk_B)
% 0.66/0.86          | (v2_struct_0 @ sk_C)
% 0.66/0.86          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.66/0.86          | (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.66/0.86             (k3_tmap_1 @ X0 @ sk_B @ sk_D @ sk_C @ 
% 0.66/0.86              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.66/0.86             sk_F)
% 0.66/0.86          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.66/0.86          | (v2_struct_0 @ sk_D)
% 0.66/0.86          | ~ (l1_pre_topc @ X0)
% 0.66/0.86          | ~ (v2_pre_topc @ X0)
% 0.66/0.86          | (v2_struct_0 @ X0))),
% 0.66/0.86      inference('demod', [status(thm)], ['248', '249'])).
% 0.66/0.86  thf('251', plain,
% 0.66/0.86      (((v2_struct_0 @ sk_A)
% 0.66/0.86        | ~ (v2_pre_topc @ sk_A)
% 0.66/0.86        | ~ (l1_pre_topc @ sk_A)
% 0.66/0.86        | (v2_struct_0 @ sk_D)
% 0.66/0.86        | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.66/0.86        | (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.66/0.86           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ 
% 0.66/0.86            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.66/0.86           sk_F)
% 0.66/0.86        | (v2_struct_0 @ sk_C)
% 0.66/0.86        | (v2_struct_0 @ sk_B))),
% 0.66/0.86      inference('sup-', [status(thm)], ['231', '250'])).
% 0.66/0.86  thf('252', plain, ((v2_pre_topc @ sk_A)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('253', plain, ((l1_pre_topc @ sk_A)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('254', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('255', plain,
% 0.66/0.86      (((v2_struct_0 @ sk_A)
% 0.66/0.86        | (v2_struct_0 @ sk_D)
% 0.66/0.86        | (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.66/0.86           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ 
% 0.66/0.86            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.66/0.86           sk_F)
% 0.66/0.86        | (v2_struct_0 @ sk_C)
% 0.66/0.86        | (v2_struct_0 @ sk_B))),
% 0.66/0.86      inference('demod', [status(thm)], ['251', '252', '253', '254'])).
% 0.66/0.86  thf('256', plain,
% 0.66/0.86      (((r1_tmap_1 @ sk_C @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 0.66/0.86         sk_F)
% 0.66/0.86        | (v2_struct_0 @ sk_A)
% 0.66/0.86        | (v2_struct_0 @ sk_C)
% 0.66/0.86        | (v2_struct_0 @ sk_D)
% 0.66/0.86        | (v2_struct_0 @ sk_B)
% 0.66/0.86        | (v2_struct_0 @ sk_B)
% 0.66/0.86        | (v2_struct_0 @ sk_C)
% 0.66/0.86        | (v2_struct_0 @ sk_D)
% 0.66/0.86        | (v2_struct_0 @ sk_A))),
% 0.66/0.86      inference('sup+', [status(thm)], ['230', '255'])).
% 0.66/0.86  thf('257', plain,
% 0.66/0.86      (((v2_struct_0 @ sk_B)
% 0.66/0.86        | (v2_struct_0 @ sk_D)
% 0.66/0.86        | (v2_struct_0 @ sk_C)
% 0.66/0.86        | (v2_struct_0 @ sk_A)
% 0.66/0.86        | (r1_tmap_1 @ sk_C @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 0.66/0.86           sk_F))),
% 0.66/0.86      inference('simplify', [status(thm)], ['256'])).
% 0.66/0.86  thf('258', plain,
% 0.66/0.86      (~ (r1_tmap_1 @ sk_C @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 0.66/0.86          sk_G)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('259', plain, (((sk_F) = (sk_G))),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('260', plain,
% 0.66/0.86      (~ (r1_tmap_1 @ sk_C @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 0.66/0.86          sk_F)),
% 0.66/0.86      inference('demod', [status(thm)], ['258', '259'])).
% 0.66/0.86  thf('261', plain,
% 0.66/0.86      (((v2_struct_0 @ sk_A)
% 0.66/0.86        | (v2_struct_0 @ sk_C)
% 0.66/0.86        | (v2_struct_0 @ sk_D)
% 0.66/0.86        | (v2_struct_0 @ sk_B))),
% 0.66/0.86      inference('sup-', [status(thm)], ['257', '260'])).
% 0.66/0.86  thf('262', plain, (~ (v2_struct_0 @ sk_B)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('263', plain,
% 0.66/0.86      (((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A))),
% 0.66/0.86      inference('sup-', [status(thm)], ['261', '262'])).
% 0.66/0.86  thf('264', plain, (~ (v2_struct_0 @ sk_D)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('265', plain, (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C))),
% 0.66/0.86      inference('clc', [status(thm)], ['263', '264'])).
% 0.66/0.86  thf('266', plain, (~ (v2_struct_0 @ sk_A)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('267', plain, ((v2_struct_0 @ sk_C)),
% 0.66/0.86      inference('clc', [status(thm)], ['265', '266'])).
% 0.66/0.86  thf('268', plain, ($false), inference('demod', [status(thm)], ['0', '267'])).
% 0.66/0.86  
% 0.66/0.86  % SZS output end Refutation
% 0.66/0.86  
% 0.70/0.87  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
