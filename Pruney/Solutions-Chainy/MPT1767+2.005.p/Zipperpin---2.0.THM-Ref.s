%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SX6XGJ3lJl

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:07 EST 2020

% Result     : Theorem 1.95s
% Output     : Refutation 1.95s
% Verified   : 
% Statistics : Number of formulae       :  150 ( 298 expanded)
%              Number of leaves         :   33 ( 102 expanded)
%              Depth                    :   30
%              Number of atoms          : 2207 (9253 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :   27 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(t78_tmap_1,conjecture,(
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
                         => ( r2_funct_2 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ ( k3_tmap_1 @ A @ B @ D @ C @ ( k2_tmap_1 @ A @ B @ E @ D ) ) @ ( k2_tmap_1 @ A @ B @ E @ C ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t78_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('2',plain,(
    ! [X10: $i] :
      ( ( l1_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('3',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
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

thf('5',plain,(
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

thf('6',plain,(
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
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['6','7','8','9','10','11','12'])).

thf('14',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','13'])).

thf('15',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference(clc,[status(thm)],['14','15'])).

thf('17',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) )
        & ( m1_subset_1 @ ( k2_partfun1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_funct_1 @ ( k2_partfun1 @ X1 @ X2 @ X0 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_partfun1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ X0 ) )
      | ~ ( v1_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ),
    inference('sup+',[status(thm)],['18','23'])).

thf('25',plain,(
    ! [X10: $i] :
      ( ( l1_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('26',plain,(
    ! [X10: $i] :
      ( ( l1_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('27',plain,(
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

thf('28',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X19 ) ) ) )
      | ~ ( v1_funct_2 @ X17 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X19 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( l1_struct_0 @ X19 )
      | ~ ( l1_struct_0 @ X18 )
      | ~ ( l1_struct_0 @ X20 )
      | ( v1_funct_2 @ ( k2_tmap_1 @ X18 @ X19 @ X17 @ X20 ) @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tmap_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['26','32'])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_B )
      | ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','35'])).

thf('37',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf(rc1_funct_2,axiom,(
    ! [A: $i,B: $i] :
    ? [C: $i] :
      ( ( v1_funct_2 @ C @ A @ B )
      & ( v1_funct_1 @ C )
      & ( v5_relat_1 @ C @ B )
      & ( v4_relat_1 @ C @ A )
      & ( v1_relat_1 @ C )
      & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) )).

thf('39',plain,(
    ! [X4: $i,X5: $i] :
      ( m1_subset_1 @ ( sk_C @ X4 @ X5 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[rc1_funct_2])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('41',plain,(
    ! [X10: $i] :
      ( ( l1_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('42',plain,(
    ! [X10: $i] :
      ( ( l1_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('43',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X19 ) ) ) )
      | ~ ( v1_funct_2 @ X17 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X19 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( l1_struct_0 @ X19 )
      | ~ ( l1_struct_0 @ X18 )
      | ~ ( l1_struct_0 @ X20 )
      | ( m1_subset_1 @ ( k2_tmap_1 @ X18 @ X19 @ X17 @ X20 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X19 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tmap_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['42','48'])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_B )
      | ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','51'])).

thf('53',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf(reflexivity_r2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_funct_2 @ A @ B @ C @ C ) ) )).

thf('55',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( r2_funct_2 @ X6 @ X7 @ X8 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) )
      | ~ ( v1_funct_2 @ X8 @ X6 @ X7 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_funct_2 @ X9 @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_funct_2])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( v1_funct_1 @ ( sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v1_funct_2 @ ( sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['39','58'])).

thf('60',plain,(
    ! [X4: $i,X5: $i] :
      ( v1_funct_1 @ ( sk_C @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[rc1_funct_2])).

thf('61',plain,(
    ! [X4: $i,X5: $i] :
      ( v1_funct_2 @ ( sk_C @ X4 @ X5 ) @ X5 @ X4 ) ),
    inference(cnf,[status(esa)],[rc1_funct_2])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) ) ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,(
    ! [X10: $i] :
      ( ( l1_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('64',plain,(
    ! [X10: $i] :
      ( ( l1_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('65',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X19 ) ) ) )
      | ~ ( v1_funct_2 @ X17 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X19 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( l1_struct_0 @ X19 )
      | ~ ( l1_struct_0 @ X18 )
      | ~ ( l1_struct_0 @ X20 )
      | ( v1_funct_1 @ ( k2_tmap_1 @ X18 @ X19 @ X17 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tmap_1])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['64','70'])).

thf('72',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_B )
      | ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','73'])).

thf('75',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(clc,[status(thm)],['62','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf(t77_tmap_1,axiom,(
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
                     => ! [F: $i] :
                          ( ( ( v1_funct_1 @ F )
                            & ( v1_funct_2 @ F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
                            & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) )
                         => ( ( ( r2_funct_2 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ F @ ( k2_tmap_1 @ A @ B @ E @ C ) )
                              & ( m1_pre_topc @ D @ C ) )
                           => ( r2_funct_2 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) @ ( k3_tmap_1 @ A @ B @ C @ D @ F ) @ ( k2_tmap_1 @ A @ B @ E @ D ) ) ) ) ) ) ) ) ) )).

thf('79',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( v2_struct_0 @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ( v2_struct_0 @ X22 )
      | ~ ( m1_pre_topc @ X22 @ X23 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_2 @ X24 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X21 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X21 ) ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X21 ) @ ( k3_tmap_1 @ X23 @ X21 @ X25 @ X22 @ X24 ) @ ( k2_tmap_1 @ X23 @ X21 @ X26 @ X22 ) )
      | ~ ( r2_funct_2 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X21 ) @ X24 @ ( k2_tmap_1 @ X23 @ X21 @ X26 @ X25 ) )
      | ~ ( m1_pre_topc @ X22 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X21 ) ) ) )
      | ~ ( v1_funct_2 @ X26 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X21 ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( m1_pre_topc @ X25 @ X23 )
      | ( v2_struct_0 @ X25 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t77_tmap_1])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( m1_pre_topc @ X3 @ X0 )
      | ~ ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( k2_tmap_1 @ X1 @ sk_B @ X2 @ X0 ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ X1 @ sk_B @ X0 @ X3 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) ) @ ( k2_tmap_1 @ X1 @ sk_B @ X2 @ X3 ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( m1_pre_topc @ X3 @ X1 )
      | ( v2_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( m1_pre_topc @ X3 @ X0 )
      | ~ ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( k2_tmap_1 @ X1 @ sk_B @ X2 @ X0 ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ X1 @ sk_B @ X0 @ X3 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) ) @ ( k2_tmap_1 @ X1 @ sk_B @ X2 @ X3 ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( m1_pre_topc @ X3 @ X1 )
      | ( v2_struct_0 @ X3 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ X0 @ X1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1 ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['77','83'])).

thf('85',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ X0 @ X1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1 ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['84','85','86','87','88','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ X0 @ X1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1 ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ X0 @ X1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1 ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ X0 @ X1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1 ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','93'])).

thf('95',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','96'])).

thf('98',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('99',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ( l1_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('100',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['97','102'])).

thf('104',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C_1 )
    | ~ ( m1_pre_topc @ sk_C_1 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','103'])).

thf('105',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C_1 )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D ) ),
    inference(clc,[status(thm)],['110','111'])).

thf('113',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    v2_struct_0 @ sk_D ),
    inference(clc,[status(thm)],['112','113'])).

thf('115',plain,(
    $false ),
    inference(demod,[status(thm)],['0','114'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SX6XGJ3lJl
% 0.16/0.37  % Computer   : n010.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 19:52:44 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.38  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 1.95/2.11  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.95/2.11  % Solved by: fo/fo7.sh
% 1.95/2.11  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.95/2.11  % done 1264 iterations in 1.662s
% 1.95/2.11  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.95/2.11  % SZS output start Refutation
% 1.95/2.11  thf(sk_A_type, type, sk_A: $i).
% 1.95/2.11  thf(sk_B_type, type, sk_B: $i).
% 1.95/2.11  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 1.95/2.11  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 1.95/2.11  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.95/2.11  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.95/2.11  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.95/2.11  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.95/2.11  thf(sk_E_type, type, sk_E: $i).
% 1.95/2.11  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.95/2.11  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.95/2.11  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.95/2.11  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 1.95/2.11  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.95/2.11  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.95/2.11  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.95/2.11  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.95/2.11  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.95/2.11  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.95/2.11  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 1.95/2.11  thf(sk_D_type, type, sk_D: $i).
% 1.95/2.11  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.95/2.11  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.95/2.11  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 1.95/2.11  thf(t78_tmap_1, conjecture,
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
% 1.95/2.11                         ( r2_funct_2 @
% 1.95/2.11                           ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ 
% 1.95/2.11                           ( k3_tmap_1 @
% 1.95/2.11                             A @ B @ D @ C @ ( k2_tmap_1 @ A @ B @ E @ D ) ) @ 
% 1.95/2.11                           ( k2_tmap_1 @ A @ B @ E @ C ) ) ) ) ) ) ) ) ) ) ) ))).
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
% 1.95/2.11                            ( r2_funct_2 @
% 1.95/2.11                              ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ 
% 1.95/2.11                              ( k3_tmap_1 @
% 1.95/2.11                                A @ B @ D @ C @ ( k2_tmap_1 @ A @ B @ E @ D ) ) @ 
% 1.95/2.11                              ( k2_tmap_1 @ A @ B @ E @ C ) ) ) ) ) ) ) ) ) ) ) ) )),
% 1.95/2.11    inference('cnf.neg', [status(esa)], [t78_tmap_1])).
% 1.95/2.11  thf('0', plain, (~ (v2_struct_0 @ sk_D)),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('1', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf(dt_l1_pre_topc, axiom,
% 1.95/2.11    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 1.95/2.11  thf('2', plain, (![X10 : $i]: ((l1_struct_0 @ X10) | ~ (l1_pre_topc @ X10))),
% 1.95/2.11      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.95/2.11  thf('3', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('4', plain,
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
% 1.95/2.11  thf('5', plain,
% 1.95/2.11      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 1.95/2.11         ((v2_struct_0 @ X13)
% 1.95/2.11          | ~ (v2_pre_topc @ X13)
% 1.95/2.11          | ~ (l1_pre_topc @ X13)
% 1.95/2.11          | ~ (m1_pre_topc @ X14 @ X15)
% 1.95/2.11          | ((k2_tmap_1 @ X15 @ X13 @ X16 @ X14)
% 1.95/2.11              = (k2_partfun1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X13) @ 
% 1.95/2.11                 X16 @ (u1_struct_0 @ X14)))
% 1.95/2.11          | ~ (m1_subset_1 @ X16 @ 
% 1.95/2.11               (k1_zfmisc_1 @ 
% 1.95/2.11                (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X13))))
% 1.95/2.11          | ~ (v1_funct_2 @ X16 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X13))
% 1.95/2.11          | ~ (v1_funct_1 @ X16)
% 1.95/2.11          | ~ (l1_pre_topc @ X15)
% 1.95/2.11          | ~ (v2_pre_topc @ X15)
% 1.95/2.11          | (v2_struct_0 @ X15))),
% 1.95/2.11      inference('cnf', [status(esa)], [d4_tmap_1])).
% 1.95/2.11  thf('6', plain,
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
% 1.95/2.11      inference('sup-', [status(thm)], ['4', '5'])).
% 1.95/2.11  thf('7', plain, ((v2_pre_topc @ sk_A)),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('9', plain, ((v1_funct_1 @ sk_E)),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('10', plain,
% 1.95/2.11      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('11', plain, ((l1_pre_topc @ sk_B)),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('12', plain, ((v2_pre_topc @ sk_B)),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('13', plain,
% 1.95/2.11      (![X0 : $i]:
% 1.95/2.11         ((v2_struct_0 @ sk_A)
% 1.95/2.11          | ((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0)
% 1.95/2.11              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 1.95/2.11                 sk_E @ (u1_struct_0 @ X0)))
% 1.95/2.11          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.95/2.11          | (v2_struct_0 @ sk_B))),
% 1.95/2.11      inference('demod', [status(thm)], ['6', '7', '8', '9', '10', '11', '12'])).
% 1.95/2.11  thf('14', plain,
% 1.95/2.11      (((v2_struct_0 @ sk_B)
% 1.95/2.11        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 1.95/2.11            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 1.95/2.11               sk_E @ (u1_struct_0 @ sk_D)))
% 1.95/2.11        | (v2_struct_0 @ sk_A))),
% 1.95/2.11      inference('sup-', [status(thm)], ['3', '13'])).
% 1.95/2.11  thf('15', plain, (~ (v2_struct_0 @ sk_B)),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('16', plain,
% 1.95/2.11      (((v2_struct_0 @ sk_A)
% 1.95/2.11        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 1.95/2.11            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 1.95/2.11               sk_E @ (u1_struct_0 @ sk_D))))),
% 1.95/2.11      inference('clc', [status(thm)], ['14', '15'])).
% 1.95/2.11  thf('17', plain, (~ (v2_struct_0 @ sk_A)),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('18', plain,
% 1.95/2.11      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 1.95/2.11         = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 1.95/2.11            (u1_struct_0 @ sk_D)))),
% 1.95/2.11      inference('clc', [status(thm)], ['16', '17'])).
% 1.95/2.11  thf('19', plain,
% 1.95/2.11      ((m1_subset_1 @ sk_E @ 
% 1.95/2.11        (k1_zfmisc_1 @ 
% 1.95/2.11         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf(dt_k2_partfun1, axiom,
% 1.95/2.11    (![A:$i,B:$i,C:$i,D:$i]:
% 1.95/2.11     ( ( ( v1_funct_1 @ C ) & 
% 1.95/2.11         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.95/2.11       ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) ) & 
% 1.95/2.11         ( m1_subset_1 @
% 1.95/2.11           ( k2_partfun1 @ A @ B @ C @ D ) @ 
% 1.95/2.11           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 1.95/2.11  thf('20', plain,
% 1.95/2.11      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.95/2.11         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 1.95/2.11          | ~ (v1_funct_1 @ X0)
% 1.95/2.11          | (v1_funct_1 @ (k2_partfun1 @ X1 @ X2 @ X0 @ X3)))),
% 1.95/2.11      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 1.95/2.11  thf('21', plain,
% 1.95/2.11      (![X0 : $i]:
% 1.95/2.11         ((v1_funct_1 @ 
% 1.95/2.11           (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 1.95/2.11            X0))
% 1.95/2.11          | ~ (v1_funct_1 @ sk_E))),
% 1.95/2.11      inference('sup-', [status(thm)], ['19', '20'])).
% 1.95/2.11  thf('22', plain, ((v1_funct_1 @ sk_E)),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('23', plain,
% 1.95/2.11      (![X0 : $i]:
% 1.95/2.11         (v1_funct_1 @ 
% 1.95/2.11          (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 1.95/2.11           X0))),
% 1.95/2.11      inference('demod', [status(thm)], ['21', '22'])).
% 1.95/2.11  thf('24', plain, ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))),
% 1.95/2.11      inference('sup+', [status(thm)], ['18', '23'])).
% 1.95/2.11  thf('25', plain,
% 1.95/2.11      (![X10 : $i]: ((l1_struct_0 @ X10) | ~ (l1_pre_topc @ X10))),
% 1.95/2.11      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.95/2.11  thf('26', plain,
% 1.95/2.11      (![X10 : $i]: ((l1_struct_0 @ X10) | ~ (l1_pre_topc @ X10))),
% 1.95/2.11      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.95/2.11  thf('27', plain,
% 1.95/2.11      ((m1_subset_1 @ sk_E @ 
% 1.95/2.11        (k1_zfmisc_1 @ 
% 1.95/2.11         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf(dt_k2_tmap_1, axiom,
% 1.95/2.11    (![A:$i,B:$i,C:$i,D:$i]:
% 1.95/2.11     ( ( ( l1_struct_0 @ A ) & ( l1_struct_0 @ B ) & ( v1_funct_1 @ C ) & 
% 1.95/2.11         ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.95/2.11         ( m1_subset_1 @
% 1.95/2.11           C @ 
% 1.95/2.11           ( k1_zfmisc_1 @
% 1.95/2.11             ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 1.95/2.11         ( l1_struct_0 @ D ) ) =>
% 1.95/2.11       ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) ) & 
% 1.95/2.11         ( v1_funct_2 @
% 1.95/2.11           ( k2_tmap_1 @ A @ B @ C @ D ) @ ( u1_struct_0 @ D ) @ 
% 1.95/2.11           ( u1_struct_0 @ B ) ) & 
% 1.95/2.11         ( m1_subset_1 @
% 1.95/2.11           ( k2_tmap_1 @ A @ B @ C @ D ) @ 
% 1.95/2.11           ( k1_zfmisc_1 @
% 1.95/2.11             ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 1.95/2.11  thf('28', plain,
% 1.95/2.11      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 1.95/2.11         (~ (m1_subset_1 @ X17 @ 
% 1.95/2.11             (k1_zfmisc_1 @ 
% 1.95/2.11              (k2_zfmisc_1 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X19))))
% 1.95/2.11          | ~ (v1_funct_2 @ X17 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X19))
% 1.95/2.11          | ~ (v1_funct_1 @ X17)
% 1.95/2.11          | ~ (l1_struct_0 @ X19)
% 1.95/2.11          | ~ (l1_struct_0 @ X18)
% 1.95/2.11          | ~ (l1_struct_0 @ X20)
% 1.95/2.11          | (v1_funct_2 @ (k2_tmap_1 @ X18 @ X19 @ X17 @ X20) @ 
% 1.95/2.11             (u1_struct_0 @ X20) @ (u1_struct_0 @ X19)))),
% 1.95/2.11      inference('cnf', [status(esa)], [dt_k2_tmap_1])).
% 1.95/2.11  thf('29', plain,
% 1.95/2.11      (![X0 : $i]:
% 1.95/2.11         ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 1.95/2.11           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 1.95/2.11          | ~ (l1_struct_0 @ X0)
% 1.95/2.11          | ~ (l1_struct_0 @ sk_A)
% 1.95/2.11          | ~ (l1_struct_0 @ sk_B)
% 1.95/2.11          | ~ (v1_funct_1 @ sk_E)
% 1.95/2.11          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 1.95/2.11      inference('sup-', [status(thm)], ['27', '28'])).
% 1.95/2.11  thf('30', plain, ((v1_funct_1 @ sk_E)),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('31', plain,
% 1.95/2.11      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('32', plain,
% 1.95/2.11      (![X0 : $i]:
% 1.95/2.11         ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 1.95/2.11           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 1.95/2.11          | ~ (l1_struct_0 @ X0)
% 1.95/2.11          | ~ (l1_struct_0 @ sk_A)
% 1.95/2.11          | ~ (l1_struct_0 @ sk_B))),
% 1.95/2.11      inference('demod', [status(thm)], ['29', '30', '31'])).
% 1.95/2.11  thf('33', plain,
% 1.95/2.11      (![X0 : $i]:
% 1.95/2.11         (~ (l1_pre_topc @ sk_A)
% 1.95/2.11          | ~ (l1_struct_0 @ sk_B)
% 1.95/2.11          | ~ (l1_struct_0 @ X0)
% 1.95/2.11          | (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 1.95/2.11             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 1.95/2.11      inference('sup-', [status(thm)], ['26', '32'])).
% 1.95/2.11  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('35', plain,
% 1.95/2.11      (![X0 : $i]:
% 1.95/2.11         (~ (l1_struct_0 @ sk_B)
% 1.95/2.11          | ~ (l1_struct_0 @ X0)
% 1.95/2.11          | (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 1.95/2.11             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 1.95/2.11      inference('demod', [status(thm)], ['33', '34'])).
% 1.95/2.11  thf('36', plain,
% 1.95/2.11      (![X0 : $i]:
% 1.95/2.11         (~ (l1_pre_topc @ sk_B)
% 1.95/2.11          | (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 1.95/2.11             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 1.95/2.11          | ~ (l1_struct_0 @ X0))),
% 1.95/2.11      inference('sup-', [status(thm)], ['25', '35'])).
% 1.95/2.11  thf('37', plain, ((l1_pre_topc @ sk_B)),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('38', plain,
% 1.95/2.11      (![X0 : $i]:
% 1.95/2.11         ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 1.95/2.11           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 1.95/2.11          | ~ (l1_struct_0 @ X0))),
% 1.95/2.11      inference('demod', [status(thm)], ['36', '37'])).
% 1.95/2.11  thf(rc1_funct_2, axiom,
% 1.95/2.11    (![A:$i,B:$i]:
% 1.95/2.11     ( ?[C:$i]:
% 1.95/2.11       ( ( v1_funct_2 @ C @ A @ B ) & ( v1_funct_1 @ C ) & 
% 1.95/2.11         ( v5_relat_1 @ C @ B ) & ( v4_relat_1 @ C @ A ) & 
% 1.95/2.11         ( v1_relat_1 @ C ) & 
% 1.95/2.11         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 1.95/2.11  thf('39', plain,
% 1.95/2.11      (![X4 : $i, X5 : $i]:
% 1.95/2.11         (m1_subset_1 @ (sk_C @ X4 @ X5) @ 
% 1.95/2.11          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X4)))),
% 1.95/2.11      inference('cnf', [status(esa)], [rc1_funct_2])).
% 1.95/2.11  thf('40', plain,
% 1.95/2.11      (![X0 : $i]:
% 1.95/2.11         ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 1.95/2.11           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 1.95/2.11          | ~ (l1_struct_0 @ X0))),
% 1.95/2.11      inference('demod', [status(thm)], ['36', '37'])).
% 1.95/2.11  thf('41', plain,
% 1.95/2.11      (![X10 : $i]: ((l1_struct_0 @ X10) | ~ (l1_pre_topc @ X10))),
% 1.95/2.11      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.95/2.11  thf('42', plain,
% 1.95/2.11      (![X10 : $i]: ((l1_struct_0 @ X10) | ~ (l1_pre_topc @ X10))),
% 1.95/2.11      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.95/2.11  thf('43', plain,
% 1.95/2.11      ((m1_subset_1 @ sk_E @ 
% 1.95/2.11        (k1_zfmisc_1 @ 
% 1.95/2.11         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('44', plain,
% 1.95/2.11      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 1.95/2.11         (~ (m1_subset_1 @ X17 @ 
% 1.95/2.11             (k1_zfmisc_1 @ 
% 1.95/2.11              (k2_zfmisc_1 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X19))))
% 1.95/2.11          | ~ (v1_funct_2 @ X17 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X19))
% 1.95/2.11          | ~ (v1_funct_1 @ X17)
% 1.95/2.11          | ~ (l1_struct_0 @ X19)
% 1.95/2.11          | ~ (l1_struct_0 @ X18)
% 1.95/2.11          | ~ (l1_struct_0 @ X20)
% 1.95/2.11          | (m1_subset_1 @ (k2_tmap_1 @ X18 @ X19 @ X17 @ X20) @ 
% 1.95/2.11             (k1_zfmisc_1 @ 
% 1.95/2.11              (k2_zfmisc_1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X19)))))),
% 1.95/2.11      inference('cnf', [status(esa)], [dt_k2_tmap_1])).
% 1.95/2.11  thf('45', plain,
% 1.95/2.11      (![X0 : $i]:
% 1.95/2.11         ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 1.95/2.11           (k1_zfmisc_1 @ 
% 1.95/2.11            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 1.95/2.11          | ~ (l1_struct_0 @ X0)
% 1.95/2.11          | ~ (l1_struct_0 @ sk_A)
% 1.95/2.11          | ~ (l1_struct_0 @ sk_B)
% 1.95/2.11          | ~ (v1_funct_1 @ sk_E)
% 1.95/2.11          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 1.95/2.11      inference('sup-', [status(thm)], ['43', '44'])).
% 1.95/2.11  thf('46', plain, ((v1_funct_1 @ sk_E)),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('47', plain,
% 1.95/2.11      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('48', plain,
% 1.95/2.11      (![X0 : $i]:
% 1.95/2.11         ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 1.95/2.11           (k1_zfmisc_1 @ 
% 1.95/2.11            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 1.95/2.11          | ~ (l1_struct_0 @ X0)
% 1.95/2.11          | ~ (l1_struct_0 @ sk_A)
% 1.95/2.11          | ~ (l1_struct_0 @ sk_B))),
% 1.95/2.11      inference('demod', [status(thm)], ['45', '46', '47'])).
% 1.95/2.11  thf('49', plain,
% 1.95/2.11      (![X0 : $i]:
% 1.95/2.11         (~ (l1_pre_topc @ sk_A)
% 1.95/2.11          | ~ (l1_struct_0 @ sk_B)
% 1.95/2.11          | ~ (l1_struct_0 @ X0)
% 1.95/2.11          | (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 1.95/2.11             (k1_zfmisc_1 @ 
% 1.95/2.11              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))))),
% 1.95/2.11      inference('sup-', [status(thm)], ['42', '48'])).
% 1.95/2.11  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('51', plain,
% 1.95/2.11      (![X0 : $i]:
% 1.95/2.11         (~ (l1_struct_0 @ sk_B)
% 1.95/2.11          | ~ (l1_struct_0 @ X0)
% 1.95/2.11          | (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 1.95/2.11             (k1_zfmisc_1 @ 
% 1.95/2.11              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))))),
% 1.95/2.11      inference('demod', [status(thm)], ['49', '50'])).
% 1.95/2.11  thf('52', plain,
% 1.95/2.11      (![X0 : $i]:
% 1.95/2.11         (~ (l1_pre_topc @ sk_B)
% 1.95/2.11          | (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 1.95/2.11             (k1_zfmisc_1 @ 
% 1.95/2.11              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 1.95/2.11          | ~ (l1_struct_0 @ X0))),
% 1.95/2.11      inference('sup-', [status(thm)], ['41', '51'])).
% 1.95/2.11  thf('53', plain, ((l1_pre_topc @ sk_B)),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('54', plain,
% 1.95/2.11      (![X0 : $i]:
% 1.95/2.11         ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 1.95/2.11           (k1_zfmisc_1 @ 
% 1.95/2.11            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 1.95/2.11          | ~ (l1_struct_0 @ X0))),
% 1.95/2.11      inference('demod', [status(thm)], ['52', '53'])).
% 1.95/2.11  thf(reflexivity_r2_funct_2, axiom,
% 1.95/2.11    (![A:$i,B:$i,C:$i,D:$i]:
% 1.95/2.11     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.95/2.11         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.95/2.11         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.95/2.11         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.95/2.11       ( r2_funct_2 @ A @ B @ C @ C ) ))).
% 1.95/2.11  thf('55', plain,
% 1.95/2.11      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 1.95/2.11         ((r2_funct_2 @ X6 @ X7 @ X8 @ X8)
% 1.95/2.11          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7)))
% 1.95/2.11          | ~ (v1_funct_2 @ X8 @ X6 @ X7)
% 1.95/2.11          | ~ (v1_funct_1 @ X8)
% 1.95/2.11          | ~ (v1_funct_1 @ X9)
% 1.95/2.11          | ~ (v1_funct_2 @ X9 @ X6 @ X7)
% 1.95/2.11          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 1.95/2.11      inference('cnf', [status(esa)], [reflexivity_r2_funct_2])).
% 1.95/2.11  thf('56', plain,
% 1.95/2.11      (![X0 : $i, X1 : $i]:
% 1.95/2.11         (~ (l1_struct_0 @ X0)
% 1.95/2.11          | ~ (m1_subset_1 @ X1 @ 
% 1.95/2.11               (k1_zfmisc_1 @ 
% 1.95/2.11                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 1.95/2.11          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 1.95/2.11          | ~ (v1_funct_1 @ X1)
% 1.95/2.11          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 1.95/2.11          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 1.95/2.11               (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 1.95/2.11          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 1.95/2.11             (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 1.95/2.11             (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0)))),
% 1.95/2.11      inference('sup-', [status(thm)], ['54', '55'])).
% 1.95/2.11  thf('57', plain,
% 1.95/2.11      (![X0 : $i, X1 : $i]:
% 1.95/2.11         (~ (l1_struct_0 @ X0)
% 1.95/2.11          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 1.95/2.11             (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 1.95/2.11             (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 1.95/2.11          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 1.95/2.11          | ~ (v1_funct_1 @ X1)
% 1.95/2.11          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 1.95/2.11          | ~ (m1_subset_1 @ X1 @ 
% 1.95/2.11               (k1_zfmisc_1 @ 
% 1.95/2.11                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 1.95/2.11          | ~ (l1_struct_0 @ X0))),
% 1.95/2.11      inference('sup-', [status(thm)], ['40', '56'])).
% 1.95/2.11  thf('58', plain,
% 1.95/2.11      (![X0 : $i, X1 : $i]:
% 1.95/2.11         (~ (m1_subset_1 @ X1 @ 
% 1.95/2.11             (k1_zfmisc_1 @ 
% 1.95/2.11              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 1.95/2.11          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 1.95/2.11          | ~ (v1_funct_1 @ X1)
% 1.95/2.11          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 1.95/2.11          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 1.95/2.11             (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 1.95/2.11             (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 1.95/2.11          | ~ (l1_struct_0 @ X0))),
% 1.95/2.11      inference('simplify', [status(thm)], ['57'])).
% 1.95/2.11  thf('59', plain,
% 1.95/2.11      (![X0 : $i]:
% 1.95/2.11         (~ (l1_struct_0 @ X0)
% 1.95/2.11          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 1.95/2.11             (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 1.95/2.11             (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 1.95/2.11          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 1.95/2.11          | ~ (v1_funct_1 @ (sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X0)))
% 1.95/2.11          | ~ (v1_funct_2 @ 
% 1.95/2.11               (sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X0)) @ 
% 1.95/2.11               (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 1.95/2.11      inference('sup-', [status(thm)], ['39', '58'])).
% 1.95/2.11  thf('60', plain, (![X4 : $i, X5 : $i]: (v1_funct_1 @ (sk_C @ X4 @ X5))),
% 1.95/2.11      inference('cnf', [status(esa)], [rc1_funct_2])).
% 1.95/2.11  thf('61', plain,
% 1.95/2.11      (![X4 : $i, X5 : $i]: (v1_funct_2 @ (sk_C @ X4 @ X5) @ X5 @ X4)),
% 1.95/2.11      inference('cnf', [status(esa)], [rc1_funct_2])).
% 1.95/2.11  thf('62', plain,
% 1.95/2.11      (![X0 : $i]:
% 1.95/2.11         (~ (l1_struct_0 @ X0)
% 1.95/2.11          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 1.95/2.11             (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 1.95/2.11             (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 1.95/2.11          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0)))),
% 1.95/2.11      inference('demod', [status(thm)], ['59', '60', '61'])).
% 1.95/2.11  thf('63', plain,
% 1.95/2.11      (![X10 : $i]: ((l1_struct_0 @ X10) | ~ (l1_pre_topc @ X10))),
% 1.95/2.11      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.95/2.11  thf('64', plain,
% 1.95/2.11      (![X10 : $i]: ((l1_struct_0 @ X10) | ~ (l1_pre_topc @ X10))),
% 1.95/2.11      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.95/2.11  thf('65', plain,
% 1.95/2.11      ((m1_subset_1 @ sk_E @ 
% 1.95/2.11        (k1_zfmisc_1 @ 
% 1.95/2.11         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('66', plain,
% 1.95/2.11      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 1.95/2.11         (~ (m1_subset_1 @ X17 @ 
% 1.95/2.11             (k1_zfmisc_1 @ 
% 1.95/2.11              (k2_zfmisc_1 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X19))))
% 1.95/2.11          | ~ (v1_funct_2 @ X17 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X19))
% 1.95/2.11          | ~ (v1_funct_1 @ X17)
% 1.95/2.11          | ~ (l1_struct_0 @ X19)
% 1.95/2.11          | ~ (l1_struct_0 @ X18)
% 1.95/2.11          | ~ (l1_struct_0 @ X20)
% 1.95/2.11          | (v1_funct_1 @ (k2_tmap_1 @ X18 @ X19 @ X17 @ X20)))),
% 1.95/2.11      inference('cnf', [status(esa)], [dt_k2_tmap_1])).
% 1.95/2.11  thf('67', plain,
% 1.95/2.11      (![X0 : $i]:
% 1.95/2.11         ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 1.95/2.11          | ~ (l1_struct_0 @ X0)
% 1.95/2.11          | ~ (l1_struct_0 @ sk_A)
% 1.95/2.11          | ~ (l1_struct_0 @ sk_B)
% 1.95/2.11          | ~ (v1_funct_1 @ sk_E)
% 1.95/2.11          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 1.95/2.11      inference('sup-', [status(thm)], ['65', '66'])).
% 1.95/2.11  thf('68', plain, ((v1_funct_1 @ sk_E)),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('69', plain,
% 1.95/2.11      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('70', plain,
% 1.95/2.11      (![X0 : $i]:
% 1.95/2.11         ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 1.95/2.11          | ~ (l1_struct_0 @ X0)
% 1.95/2.11          | ~ (l1_struct_0 @ sk_A)
% 1.95/2.11          | ~ (l1_struct_0 @ sk_B))),
% 1.95/2.11      inference('demod', [status(thm)], ['67', '68', '69'])).
% 1.95/2.11  thf('71', plain,
% 1.95/2.11      (![X0 : $i]:
% 1.95/2.11         (~ (l1_pre_topc @ sk_A)
% 1.95/2.11          | ~ (l1_struct_0 @ sk_B)
% 1.95/2.11          | ~ (l1_struct_0 @ X0)
% 1.95/2.11          | (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0)))),
% 1.95/2.11      inference('sup-', [status(thm)], ['64', '70'])).
% 1.95/2.11  thf('72', plain, ((l1_pre_topc @ sk_A)),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('73', plain,
% 1.95/2.11      (![X0 : $i]:
% 1.95/2.11         (~ (l1_struct_0 @ sk_B)
% 1.95/2.11          | ~ (l1_struct_0 @ X0)
% 1.95/2.11          | (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0)))),
% 1.95/2.11      inference('demod', [status(thm)], ['71', '72'])).
% 1.95/2.11  thf('74', plain,
% 1.95/2.11      (![X0 : $i]:
% 1.95/2.11         (~ (l1_pre_topc @ sk_B)
% 1.95/2.11          | (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 1.95/2.11          | ~ (l1_struct_0 @ X0))),
% 1.95/2.11      inference('sup-', [status(thm)], ['63', '73'])).
% 1.95/2.11  thf('75', plain, ((l1_pre_topc @ sk_B)),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('76', plain,
% 1.95/2.11      (![X0 : $i]:
% 1.95/2.11         ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 1.95/2.11          | ~ (l1_struct_0 @ X0))),
% 1.95/2.11      inference('demod', [status(thm)], ['74', '75'])).
% 1.95/2.11  thf('77', plain,
% 1.95/2.11      (![X0 : $i]:
% 1.95/2.11         ((r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 1.95/2.11           (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 1.95/2.11           (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 1.95/2.11          | ~ (l1_struct_0 @ X0))),
% 1.95/2.11      inference('clc', [status(thm)], ['62', '76'])).
% 1.95/2.11  thf('78', plain,
% 1.95/2.11      (![X0 : $i]:
% 1.95/2.11         ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 1.95/2.11           (k1_zfmisc_1 @ 
% 1.95/2.11            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 1.95/2.11          | ~ (l1_struct_0 @ X0))),
% 1.95/2.11      inference('demod', [status(thm)], ['52', '53'])).
% 1.95/2.11  thf(t77_tmap_1, axiom,
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
% 1.95/2.11                       ( ![F:$i]:
% 1.95/2.11                         ( ( ( v1_funct_1 @ F ) & 
% 1.95/2.11                             ( v1_funct_2 @
% 1.95/2.11                               F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 1.95/2.11                             ( m1_subset_1 @
% 1.95/2.11                               F @ 
% 1.95/2.11                               ( k1_zfmisc_1 @
% 1.95/2.11                                 ( k2_zfmisc_1 @
% 1.95/2.11                                   ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.95/2.11                           ( ( ( r2_funct_2 @
% 1.95/2.11                                 ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ 
% 1.95/2.11                                 F @ ( k2_tmap_1 @ A @ B @ E @ C ) ) & 
% 1.95/2.11                               ( m1_pre_topc @ D @ C ) ) =>
% 1.95/2.11                             ( r2_funct_2 @
% 1.95/2.11                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) @ 
% 1.95/2.11                               ( k3_tmap_1 @ A @ B @ C @ D @ F ) @ 
% 1.95/2.11                               ( k2_tmap_1 @ A @ B @ E @ D ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.95/2.11  thf('79', plain,
% 1.95/2.11      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 1.95/2.11         ((v2_struct_0 @ X21)
% 1.95/2.11          | ~ (v2_pre_topc @ X21)
% 1.95/2.11          | ~ (l1_pre_topc @ X21)
% 1.95/2.11          | (v2_struct_0 @ X22)
% 1.95/2.11          | ~ (m1_pre_topc @ X22 @ X23)
% 1.95/2.11          | ~ (v1_funct_1 @ X24)
% 1.95/2.11          | ~ (v1_funct_2 @ X24 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X21))
% 1.95/2.11          | ~ (m1_subset_1 @ X24 @ 
% 1.95/2.11               (k1_zfmisc_1 @ 
% 1.95/2.11                (k2_zfmisc_1 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X21))))
% 1.95/2.11          | (r2_funct_2 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X21) @ 
% 1.95/2.11             (k3_tmap_1 @ X23 @ X21 @ X25 @ X22 @ X24) @ 
% 1.95/2.11             (k2_tmap_1 @ X23 @ X21 @ X26 @ X22))
% 1.95/2.11          | ~ (r2_funct_2 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X21) @ X24 @ 
% 1.95/2.11               (k2_tmap_1 @ X23 @ X21 @ X26 @ X25))
% 1.95/2.11          | ~ (m1_pre_topc @ X22 @ X25)
% 1.95/2.11          | ~ (m1_subset_1 @ X26 @ 
% 1.95/2.11               (k1_zfmisc_1 @ 
% 1.95/2.11                (k2_zfmisc_1 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X21))))
% 1.95/2.11          | ~ (v1_funct_2 @ X26 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X21))
% 1.95/2.11          | ~ (v1_funct_1 @ X26)
% 1.95/2.11          | ~ (m1_pre_topc @ X25 @ X23)
% 1.95/2.11          | (v2_struct_0 @ X25)
% 1.95/2.11          | ~ (l1_pre_topc @ X23)
% 1.95/2.11          | ~ (v2_pre_topc @ X23)
% 1.95/2.11          | (v2_struct_0 @ X23))),
% 1.95/2.11      inference('cnf', [status(esa)], [t77_tmap_1])).
% 1.95/2.11  thf('80', plain,
% 1.95/2.11      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.95/2.11         (~ (l1_struct_0 @ X0)
% 1.95/2.11          | (v2_struct_0 @ X1)
% 1.95/2.11          | ~ (v2_pre_topc @ X1)
% 1.95/2.11          | ~ (l1_pre_topc @ X1)
% 1.95/2.11          | (v2_struct_0 @ X0)
% 1.95/2.11          | ~ (m1_pre_topc @ X0 @ X1)
% 1.95/2.11          | ~ (v1_funct_1 @ X2)
% 1.95/2.11          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B))
% 1.95/2.11          | ~ (m1_subset_1 @ X2 @ 
% 1.95/2.11               (k1_zfmisc_1 @ 
% 1.95/2.11                (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B))))
% 1.95/2.11          | ~ (m1_pre_topc @ X3 @ X0)
% 1.95/2.11          | ~ (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 1.95/2.11               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 1.95/2.11               (k2_tmap_1 @ X1 @ sk_B @ X2 @ X0))
% 1.95/2.11          | (r2_funct_2 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ sk_B) @ 
% 1.95/2.11             (k3_tmap_1 @ X1 @ sk_B @ X0 @ X3 @ 
% 1.95/2.11              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0)) @ 
% 1.95/2.11             (k2_tmap_1 @ X1 @ sk_B @ X2 @ X3))
% 1.95/2.11          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 1.95/2.11               (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 1.95/2.11          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 1.95/2.11          | ~ (m1_pre_topc @ X3 @ X1)
% 1.95/2.11          | (v2_struct_0 @ X3)
% 1.95/2.11          | ~ (l1_pre_topc @ sk_B)
% 1.95/2.11          | ~ (v2_pre_topc @ sk_B)
% 1.95/2.11          | (v2_struct_0 @ sk_B))),
% 1.95/2.11      inference('sup-', [status(thm)], ['78', '79'])).
% 1.95/2.11  thf('81', plain, ((l1_pre_topc @ sk_B)),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('82', plain, ((v2_pre_topc @ sk_B)),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('83', plain,
% 1.95/2.11      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.95/2.11         (~ (l1_struct_0 @ X0)
% 1.95/2.11          | (v2_struct_0 @ X1)
% 1.95/2.11          | ~ (v2_pre_topc @ X1)
% 1.95/2.11          | ~ (l1_pre_topc @ X1)
% 1.95/2.11          | (v2_struct_0 @ X0)
% 1.95/2.11          | ~ (m1_pre_topc @ X0 @ X1)
% 1.95/2.11          | ~ (v1_funct_1 @ X2)
% 1.95/2.11          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B))
% 1.95/2.11          | ~ (m1_subset_1 @ X2 @ 
% 1.95/2.11               (k1_zfmisc_1 @ 
% 1.95/2.11                (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B))))
% 1.95/2.11          | ~ (m1_pre_topc @ X3 @ X0)
% 1.95/2.11          | ~ (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 1.95/2.11               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 1.95/2.11               (k2_tmap_1 @ X1 @ sk_B @ X2 @ X0))
% 1.95/2.11          | (r2_funct_2 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ sk_B) @ 
% 1.95/2.11             (k3_tmap_1 @ X1 @ sk_B @ X0 @ X3 @ 
% 1.95/2.11              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0)) @ 
% 1.95/2.11             (k2_tmap_1 @ X1 @ sk_B @ X2 @ X3))
% 1.95/2.11          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 1.95/2.11               (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 1.95/2.11          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 1.95/2.11          | ~ (m1_pre_topc @ X3 @ X1)
% 1.95/2.11          | (v2_struct_0 @ X3)
% 1.95/2.11          | (v2_struct_0 @ sk_B))),
% 1.95/2.11      inference('demod', [status(thm)], ['80', '81', '82'])).
% 1.95/2.11  thf('84', plain,
% 1.95/2.11      (![X0 : $i, X1 : $i]:
% 1.95/2.11         (~ (l1_struct_0 @ X0)
% 1.95/2.11          | (v2_struct_0 @ sk_B)
% 1.95/2.11          | (v2_struct_0 @ X1)
% 1.95/2.11          | ~ (m1_pre_topc @ X1 @ sk_A)
% 1.95/2.11          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 1.95/2.11          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 1.95/2.11               (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 1.95/2.11          | (r2_funct_2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B) @ 
% 1.95/2.11             (k3_tmap_1 @ sk_A @ sk_B @ X0 @ X1 @ 
% 1.95/2.11              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0)) @ 
% 1.95/2.11             (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1))
% 1.95/2.11          | ~ (m1_pre_topc @ X1 @ X0)
% 1.95/2.11          | ~ (m1_subset_1 @ sk_E @ 
% 1.95/2.11               (k1_zfmisc_1 @ 
% 1.95/2.11                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 1.95/2.11          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 1.95/2.11          | ~ (v1_funct_1 @ sk_E)
% 1.95/2.11          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.95/2.11          | (v2_struct_0 @ X0)
% 1.95/2.11          | ~ (l1_pre_topc @ sk_A)
% 1.95/2.11          | ~ (v2_pre_topc @ sk_A)
% 1.95/2.11          | (v2_struct_0 @ sk_A)
% 1.95/2.11          | ~ (l1_struct_0 @ X0))),
% 1.95/2.11      inference('sup-', [status(thm)], ['77', '83'])).
% 1.95/2.11  thf('85', plain,
% 1.95/2.11      ((m1_subset_1 @ sk_E @ 
% 1.95/2.11        (k1_zfmisc_1 @ 
% 1.95/2.11         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('86', plain,
% 1.95/2.11      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('87', plain, ((v1_funct_1 @ sk_E)),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('88', plain, ((l1_pre_topc @ sk_A)),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('89', plain, ((v2_pre_topc @ sk_A)),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('90', plain,
% 1.95/2.11      (![X0 : $i, X1 : $i]:
% 1.95/2.11         (~ (l1_struct_0 @ X0)
% 1.95/2.11          | (v2_struct_0 @ sk_B)
% 1.95/2.11          | (v2_struct_0 @ X1)
% 1.95/2.11          | ~ (m1_pre_topc @ X1 @ sk_A)
% 1.95/2.11          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 1.95/2.11          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 1.95/2.11               (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 1.95/2.11          | (r2_funct_2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B) @ 
% 1.95/2.11             (k3_tmap_1 @ sk_A @ sk_B @ X0 @ X1 @ 
% 1.95/2.11              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0)) @ 
% 1.95/2.11             (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1))
% 1.95/2.11          | ~ (m1_pre_topc @ X1 @ X0)
% 1.95/2.11          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.95/2.11          | (v2_struct_0 @ X0)
% 1.95/2.11          | (v2_struct_0 @ sk_A)
% 1.95/2.11          | ~ (l1_struct_0 @ X0))),
% 1.95/2.11      inference('demod', [status(thm)], ['84', '85', '86', '87', '88', '89'])).
% 1.95/2.11  thf('91', plain,
% 1.95/2.11      (![X0 : $i, X1 : $i]:
% 1.95/2.11         ((v2_struct_0 @ sk_A)
% 1.95/2.11          | (v2_struct_0 @ X0)
% 1.95/2.11          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.95/2.11          | ~ (m1_pre_topc @ X1 @ X0)
% 1.95/2.11          | (r2_funct_2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B) @ 
% 1.95/2.11             (k3_tmap_1 @ sk_A @ sk_B @ X0 @ X1 @ 
% 1.95/2.11              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0)) @ 
% 1.95/2.11             (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1))
% 1.95/2.11          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 1.95/2.11               (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 1.95/2.11          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 1.95/2.11          | ~ (m1_pre_topc @ X1 @ sk_A)
% 1.95/2.11          | (v2_struct_0 @ X1)
% 1.95/2.11          | (v2_struct_0 @ sk_B)
% 1.95/2.11          | ~ (l1_struct_0 @ X0))),
% 1.95/2.11      inference('simplify', [status(thm)], ['90'])).
% 1.95/2.11  thf('92', plain,
% 1.95/2.11      (![X0 : $i, X1 : $i]:
% 1.95/2.11         (~ (l1_struct_0 @ X0)
% 1.95/2.11          | ~ (l1_struct_0 @ X0)
% 1.95/2.11          | (v2_struct_0 @ sk_B)
% 1.95/2.11          | (v2_struct_0 @ X1)
% 1.95/2.11          | ~ (m1_pre_topc @ X1 @ sk_A)
% 1.95/2.11          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 1.95/2.11          | (r2_funct_2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B) @ 
% 1.95/2.11             (k3_tmap_1 @ sk_A @ sk_B @ X0 @ X1 @ 
% 1.95/2.11              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0)) @ 
% 1.95/2.11             (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1))
% 1.95/2.11          | ~ (m1_pre_topc @ X1 @ X0)
% 1.95/2.11          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.95/2.11          | (v2_struct_0 @ X0)
% 1.95/2.11          | (v2_struct_0 @ sk_A))),
% 1.95/2.11      inference('sup-', [status(thm)], ['38', '91'])).
% 1.95/2.11  thf('93', plain,
% 1.95/2.11      (![X0 : $i, X1 : $i]:
% 1.95/2.11         ((v2_struct_0 @ sk_A)
% 1.95/2.11          | (v2_struct_0 @ X0)
% 1.95/2.11          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.95/2.11          | ~ (m1_pre_topc @ X1 @ X0)
% 1.95/2.11          | (r2_funct_2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B) @ 
% 1.95/2.11             (k3_tmap_1 @ sk_A @ sk_B @ X0 @ X1 @ 
% 1.95/2.11              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0)) @ 
% 1.95/2.11             (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1))
% 1.95/2.11          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 1.95/2.11          | ~ (m1_pre_topc @ X1 @ sk_A)
% 1.95/2.11          | (v2_struct_0 @ X1)
% 1.95/2.11          | (v2_struct_0 @ sk_B)
% 1.95/2.11          | ~ (l1_struct_0 @ X0))),
% 1.95/2.11      inference('simplify', [status(thm)], ['92'])).
% 1.95/2.11  thf('94', plain,
% 1.95/2.11      (![X0 : $i]:
% 1.95/2.11         (~ (l1_struct_0 @ sk_D)
% 1.95/2.11          | (v2_struct_0 @ sk_B)
% 1.95/2.11          | (v2_struct_0 @ X0)
% 1.95/2.11          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.95/2.11          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 1.95/2.11             (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ 
% 1.95/2.11              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 1.95/2.11             (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 1.95/2.11          | ~ (m1_pre_topc @ X0 @ sk_D)
% 1.95/2.11          | ~ (m1_pre_topc @ sk_D @ sk_A)
% 1.95/2.11          | (v2_struct_0 @ sk_D)
% 1.95/2.11          | (v2_struct_0 @ sk_A))),
% 1.95/2.11      inference('sup-', [status(thm)], ['24', '93'])).
% 1.95/2.11  thf('95', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('96', plain,
% 1.95/2.11      (![X0 : $i]:
% 1.95/2.11         (~ (l1_struct_0 @ sk_D)
% 1.95/2.11          | (v2_struct_0 @ sk_B)
% 1.95/2.11          | (v2_struct_0 @ X0)
% 1.95/2.11          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.95/2.11          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 1.95/2.11             (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ 
% 1.95/2.11              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 1.95/2.11             (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 1.95/2.11          | ~ (m1_pre_topc @ X0 @ sk_D)
% 1.95/2.11          | (v2_struct_0 @ sk_D)
% 1.95/2.11          | (v2_struct_0 @ sk_A))),
% 1.95/2.11      inference('demod', [status(thm)], ['94', '95'])).
% 1.95/2.11  thf('97', plain,
% 1.95/2.11      (![X0 : $i]:
% 1.95/2.11         (~ (l1_pre_topc @ sk_D)
% 1.95/2.11          | (v2_struct_0 @ sk_A)
% 1.95/2.11          | (v2_struct_0 @ sk_D)
% 1.95/2.11          | ~ (m1_pre_topc @ X0 @ sk_D)
% 1.95/2.11          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 1.95/2.11             (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ 
% 1.95/2.11              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 1.95/2.11             (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 1.95/2.11          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.95/2.11          | (v2_struct_0 @ X0)
% 1.95/2.11          | (v2_struct_0 @ sk_B))),
% 1.95/2.11      inference('sup-', [status(thm)], ['2', '96'])).
% 1.95/2.11  thf('98', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf(dt_m1_pre_topc, axiom,
% 1.95/2.11    (![A:$i]:
% 1.95/2.11     ( ( l1_pre_topc @ A ) =>
% 1.95/2.11       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 1.95/2.11  thf('99', plain,
% 1.95/2.11      (![X11 : $i, X12 : $i]:
% 1.95/2.11         (~ (m1_pre_topc @ X11 @ X12)
% 1.95/2.11          | (l1_pre_topc @ X11)
% 1.95/2.11          | ~ (l1_pre_topc @ X12))),
% 1.95/2.11      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 1.95/2.11  thf('100', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 1.95/2.11      inference('sup-', [status(thm)], ['98', '99'])).
% 1.95/2.11  thf('101', plain, ((l1_pre_topc @ sk_A)),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('102', plain, ((l1_pre_topc @ sk_D)),
% 1.95/2.11      inference('demod', [status(thm)], ['100', '101'])).
% 1.95/2.11  thf('103', plain,
% 1.95/2.11      (![X0 : $i]:
% 1.95/2.11         ((v2_struct_0 @ sk_A)
% 1.95/2.11          | (v2_struct_0 @ sk_D)
% 1.95/2.11          | ~ (m1_pre_topc @ X0 @ sk_D)
% 1.95/2.11          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 1.95/2.11             (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ 
% 1.95/2.11              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 1.95/2.11             (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 1.95/2.11          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.95/2.11          | (v2_struct_0 @ X0)
% 1.95/2.11          | (v2_struct_0 @ sk_B))),
% 1.95/2.11      inference('demod', [status(thm)], ['97', '102'])).
% 1.95/2.11  thf('104', plain,
% 1.95/2.11      (((v2_struct_0 @ sk_B)
% 1.95/2.11        | (v2_struct_0 @ sk_C_1)
% 1.95/2.11        | ~ (m1_pre_topc @ sk_C_1 @ sk_A)
% 1.95/2.11        | (r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 1.95/2.11           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ 
% 1.95/2.11            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 1.95/2.11           (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C_1))
% 1.95/2.11        | (v2_struct_0 @ sk_D)
% 1.95/2.11        | (v2_struct_0 @ sk_A))),
% 1.95/2.11      inference('sup-', [status(thm)], ['1', '103'])).
% 1.95/2.11  thf('105', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('106', plain,
% 1.95/2.11      (((v2_struct_0 @ sk_B)
% 1.95/2.11        | (v2_struct_0 @ sk_C_1)
% 1.95/2.11        | (r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 1.95/2.11           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ 
% 1.95/2.11            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 1.95/2.11           (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C_1))
% 1.95/2.11        | (v2_struct_0 @ sk_D)
% 1.95/2.11        | (v2_struct_0 @ sk_A))),
% 1.95/2.11      inference('demod', [status(thm)], ['104', '105'])).
% 1.95/2.11  thf('107', plain,
% 1.95/2.11      (~ (r2_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 1.95/2.11          (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C_1 @ 
% 1.95/2.11           (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 1.95/2.11          (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C_1))),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('108', plain,
% 1.95/2.11      (((v2_struct_0 @ sk_A)
% 1.95/2.11        | (v2_struct_0 @ sk_D)
% 1.95/2.11        | (v2_struct_0 @ sk_C_1)
% 1.95/2.11        | (v2_struct_0 @ sk_B))),
% 1.95/2.11      inference('sup-', [status(thm)], ['106', '107'])).
% 1.95/2.11  thf('109', plain, (~ (v2_struct_0 @ sk_B)),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('110', plain,
% 1.95/2.11      (((v2_struct_0 @ sk_C_1) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_A))),
% 1.95/2.11      inference('sup-', [status(thm)], ['108', '109'])).
% 1.95/2.11  thf('111', plain, (~ (v2_struct_0 @ sk_C_1)),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('112', plain, (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D))),
% 1.95/2.11      inference('clc', [status(thm)], ['110', '111'])).
% 1.95/2.11  thf('113', plain, (~ (v2_struct_0 @ sk_A)),
% 1.95/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.11  thf('114', plain, ((v2_struct_0 @ sk_D)),
% 1.95/2.11      inference('clc', [status(thm)], ['112', '113'])).
% 1.95/2.11  thf('115', plain, ($false), inference('demod', [status(thm)], ['0', '114'])).
% 1.95/2.11  
% 1.95/2.11  % SZS output end Refutation
% 1.95/2.11  
% 1.95/2.12  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
