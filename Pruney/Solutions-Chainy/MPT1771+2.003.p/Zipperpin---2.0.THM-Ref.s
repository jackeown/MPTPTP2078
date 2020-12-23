%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.kPBbjykmWM

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:13 EST 2020

% Result     : Theorem 0.60s
% Output     : Refutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :  391 (7235 expanded)
%              Number of leaves         :   32 (2101 expanded)
%              Depth                    :   35
%              Number of atoms          : 5733 (300806 expanded)
%              Number of equality atoms :   87 (4624 expanded)
%              Maximal formula depth    :   27 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

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
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('3',plain,(
    ! [X22: $i] :
      ( ( m1_pre_topc @ X22 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('4',plain,(
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

thf('5',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_pre_topc @ X17 @ X18 )
      | ~ ( m1_pre_topc @ X19 @ X18 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_funct_2 @ X21 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X20 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X20 ) ) ) )
      | ( m1_subset_1 @ ( k3_tmap_1 @ X18 @ X20 @ X19 @ X17 @ X21 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X20 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_tmap_1])).

thf('6',plain,(
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
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_A @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['6','7','8','9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
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
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['12','13','14','15'])).

thf('17',plain,
    ( ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['2','16'])).

thf('18',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['17','18'])).

thf('20',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['19','20'])).

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

thf('22',plain,(
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

thf('23',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( r2_funct_2 @ X1 @ X2 @ X3 @ X3 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_funct_2 @ X3 @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X22: $i] :
      ( ( m1_pre_topc @ X22 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('27',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_pre_topc @ X17 @ X18 )
      | ~ ( m1_pre_topc @ X19 @ X18 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_funct_2 @ X21 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X20 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X20 ) ) ) )
      | ( v1_funct_1 @ ( k3_tmap_1 @ X18 @ X20 @ X19 @ X17 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_tmap_1])).

thf('29',plain,(
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
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_A @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['29','30','31','32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['26','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['35','36','37','38'])).

thf('40',plain,
    ( ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['25','39'])).

thf('41',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('43',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('45',plain,
    ( ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ) ),
    inference(demod,[status(thm)],['24','44'])).

thf('46',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X22: $i] :
      ( ( m1_pre_topc @ X22 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('48',plain,(
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

thf('49',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( v2_struct_0 @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( m1_pre_topc @ X13 @ X14 )
      | ~ ( m1_pre_topc @ X13 @ X15 )
      | ( ( k3_tmap_1 @ X14 @ X12 @ X15 @ X13 @ X16 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X12 ) @ X16 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X12 ) ) ) )
      | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X12 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( m1_pre_topc @ X15 @ X14 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d5_tmap_1])).

thf('50',plain,(
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
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
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
    inference(demod,[status(thm)],['50','51','52','53','54'])).

thf('56',plain,(
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
    inference('sup-',[status(thm)],['47','55'])).

thf('57',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['56','57','58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['46','61'])).

thf('63',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('65',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['64','65'])).

thf('67',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
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

thf('69',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( v2_struct_0 @ X8 )
      | ~ ( v2_pre_topc @ X8 )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( m1_pre_topc @ X9 @ X10 )
      | ( ( k2_tmap_1 @ X10 @ X8 @ X11 @ X9 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X8 ) @ X11 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X8 ) ) ) )
      | ~ ( v1_funct_2 @ X11 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X8 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('70',plain,(
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
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['70','71','72','73','74','75','76'])).

thf('78',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['67','77'])).

thf('79',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference(clc,[status(thm)],['78','79'])).

thf('81',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['80','81'])).

thf('83',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ),
    inference('sup+',[status(thm)],['66','82'])).

thf('84',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ),
    inference('sup+',[status(thm)],['66','82'])).

thf('85',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ),
    inference('sup+',[status(thm)],['66','82'])).

thf('86',plain,
    ( ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) ),
    inference(demod,[status(thm)],['45','83','84','85'])).

thf('87',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X22: $i] :
      ( ( m1_pre_topc @ X22 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('89',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_pre_topc @ X17 @ X18 )
      | ~ ( m1_pre_topc @ X19 @ X18 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_funct_2 @ X21 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X20 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X20 ) ) ) )
      | ( v1_funct_2 @ ( k3_tmap_1 @ X18 @ X20 @ X19 @ X17 @ X21 ) @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_tmap_1])).

thf('91',plain,(
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
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_A @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['91','92','93','94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['88','96'])).

thf('98',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['97','98','99','100'])).

thf('102',plain,
    ( ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['87','101'])).

thf('103',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ),
    inference('sup+',[status(thm)],['66','82'])).

thf('104',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['104','105'])).

thf('107',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['106','107'])).

thf('109',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ),
    inference(demod,[status(thm)],['86','108'])).

thf('110',plain,(
    m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('111',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ),
    inference('sup+',[status(thm)],['66','82'])).

thf('112',plain,(
    m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['110','111'])).

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

thf('113',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( v2_struct_0 @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ~ ( l1_pre_topc @ X29 )
      | ( v2_struct_0 @ X30 )
      | ~ ( m1_pre_topc @ X30 @ X31 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_funct_2 @ X32 @ ( u1_struct_0 @ X33 ) @ ( u1_struct_0 @ X29 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X33 ) @ ( u1_struct_0 @ X29 ) ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X29 ) @ ( k3_tmap_1 @ X31 @ X29 @ X33 @ X30 @ X32 ) @ ( k2_tmap_1 @ X31 @ X29 @ X34 @ X30 ) )
      | ~ ( r2_funct_2 @ ( u1_struct_0 @ X33 ) @ ( u1_struct_0 @ X29 ) @ X32 @ ( k2_tmap_1 @ X31 @ X29 @ X34 @ X33 ) )
      | ~ ( m1_pre_topc @ X30 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X29 ) ) ) )
      | ~ ( v1_funct_2 @ X34 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X29 ) )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( m1_pre_topc @ X33 @ X31 )
      | ( v2_struct_0 @ X33 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t77_tmap_1])).

thf('114',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( m1_pre_topc @ X2 @ sk_D )
      | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( k2_tmap_1 @ X0 @ sk_B @ X1 @ sk_D ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( k2_tmap_1 @ X0 @ sk_B @ X1 @ X2 ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) )
      | ~ ( m1_pre_topc @ X2 @ X0 )
      | ( v2_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['106','107'])).

thf('116',plain,(
    v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('117',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ),
    inference('sup+',[status(thm)],['66','82'])).

thf('118',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( m1_pre_topc @ X2 @ sk_D )
      | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( k2_tmap_1 @ X0 @ sk_B @ X1 @ sk_D ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( k2_tmap_1 @ X0 @ sk_B @ X1 @ X2 ) )
      | ~ ( m1_pre_topc @ X2 @ X0 )
      | ( v2_struct_0 @ X2 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['114','115','118','119','120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['109','121'])).

thf('123',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['122','123','124','125','126','127','128'])).

thf('130',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ~ ( m1_pre_topc @ sk_C @ sk_D )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','129'])).

thf('131',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('135',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( v2_struct_0 @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( m1_pre_topc @ X13 @ X14 )
      | ~ ( m1_pre_topc @ X13 @ X15 )
      | ( ( k3_tmap_1 @ X14 @ X12 @ X15 @ X13 @ X16 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X12 ) @ X16 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X12 ) ) ) )
      | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X12 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( m1_pre_topc @ X15 @ X14 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d5_tmap_1])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('138',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['136','137','138','139'])).

thf('141',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ),
    inference('sup+',[status(thm)],['66','82'])).

thf('142',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['106','107'])).

thf('143',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ),
    inference('sup+',[status(thm)],['66','82'])).

thf('144',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ),
    inference('sup+',[status(thm)],['66','82'])).

thf('145',plain,(
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
    inference(demod,[status(thm)],['140','141','142','143','144'])).

thf('146',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['133','145'])).

thf('147',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['146','147','148'])).

thf('150',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['132','149'])).

thf('151',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('153',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( v2_struct_0 @ X8 )
      | ~ ( v2_pre_topc @ X8 )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( m1_pre_topc @ X9 @ X10 )
      | ( ( k2_tmap_1 @ X10 @ X8 @ X11 @ X9 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X8 ) @ X11 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X8 ) ) ) )
      | ~ ( v1_funct_2 @ X11 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X8 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('154',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k2_tmap_1 @ sk_D @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('156',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_pre_topc @ X4 @ X5 )
      | ( v2_pre_topc @ X4 )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('157',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['157','158','159'])).

thf('161',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('162',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_pre_topc @ X6 @ X7 )
      | ( l1_pre_topc @ X6 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('163',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['161','162'])).

thf('164',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['163','164'])).

thf('166',plain,(
    v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('167',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k2_tmap_1 @ sk_D @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['154','160','165','166','167','168'])).

thf('170',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ),
    inference('sup+',[status(thm)],['66','82'])).

thf('171',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ),
    inference('sup+',[status(thm)],['66','82'])).

thf('172',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ),
    inference('sup+',[status(thm)],['66','82'])).

thf('173',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['169','170','171','172'])).

thf('174',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['106','107'])).

thf('175',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['173','174'])).

thf('176',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['151','175'])).

thf('177',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['176','177'])).

thf('179',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ sk_C )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['178','179'])).

thf('181',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) )
      = ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['150','180','181'])).

thf('183',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) )
      = ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ sk_C ) ) ),
    inference(clc,[status(thm)],['182','183'])).

thf('185',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) )
    = ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ sk_C ) ),
    inference(clc,[status(thm)],['184','185'])).

thf('187',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ sk_C ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['130','131','186'])).

thf('188',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,(
    ! [X22: $i] :
      ( ( m1_pre_topc @ X22 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('190',plain,(
    m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('191',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_pre_topc @ X17 @ X18 )
      | ~ ( m1_pre_topc @ X19 @ X18 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_funct_2 @ X21 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X20 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X20 ) ) ) )
      | ( m1_subset_1 @ ( k3_tmap_1 @ X18 @ X20 @ X19 @ X17 @ X21 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X20 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_tmap_1])).

thf('192',plain,(
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
    inference('sup-',[status(thm)],['190','191'])).

thf('193',plain,(
    v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('194',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['192','193','194','195'])).

thf('197',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ),
    inference('sup+',[status(thm)],['66','82'])).

thf('198',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ),
    inference('sup+',[status(thm)],['66','82'])).

thf('199',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['106','107'])).

thf('200',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['196','197','198','199'])).

thf('201',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_D )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ( v2_struct_0 @ sk_D )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['189','200'])).

thf('202',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['163','164'])).

thf('203',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['163','164'])).

thf('204',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['157','158','159'])).

thf('205',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['201','202','203','204'])).

thf('206',plain,
    ( ( m1_subset_1 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['188','205'])).

thf('207',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['206','207'])).

thf('209',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('210',plain,(
    m1_subset_1 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['208','209'])).

thf('211',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('212',plain,(
    ! [X22: $i] :
      ( ( m1_pre_topc @ X22 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('213',plain,(
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
    inference(demod,[status(thm)],['140','141','142','143','144'])).

thf('214',plain,(
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
    inference('sup-',[status(thm)],['212','213'])).

thf('215',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['163','164'])).

thf('216',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['163','164'])).

thf('217',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['157','158','159'])).

thf('218',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['214','215','216','217'])).

thf('219',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['218'])).

thf('220',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['211','219'])).

thf('221',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('222',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['220','221'])).

thf('223',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('224',plain,
    ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['222','223'])).

thf('225',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ sk_C )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['178','179'])).

thf('226',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ sk_C )
    = ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) ),
    inference('sup+',[status(thm)],['224','225'])).

thf('227',plain,(
    m1_subset_1 @ ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['210','226'])).

thf('228',plain,(
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

thf('229',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ sk_C ) @ X0 )
      | ( ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ sk_C )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ sk_C ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['227','228'])).

thf('230',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('231',plain,(
    ! [X22: $i] :
      ( ( m1_pre_topc @ X22 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('232',plain,(
    m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('233',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_pre_topc @ X17 @ X18 )
      | ~ ( m1_pre_topc @ X19 @ X18 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_funct_2 @ X21 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X20 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X20 ) ) ) )
      | ( v1_funct_1 @ ( k3_tmap_1 @ X18 @ X20 @ X19 @ X17 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_tmap_1])).

thf('234',plain,(
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
    inference('sup-',[status(thm)],['232','233'])).

thf('235',plain,(
    v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('236',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('237',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('238',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ) )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['234','235','236','237'])).

thf('239',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ),
    inference('sup+',[status(thm)],['66','82'])).

thf('240',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ),
    inference('sup+',[status(thm)],['66','82'])).

thf('241',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['238','239','240'])).

thf('242',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['106','107'])).

thf('243',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['241','242'])).

thf('244',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_D )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ( v2_struct_0 @ sk_D )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) ) ) ),
    inference('sup-',[status(thm)],['231','243'])).

thf('245',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['163','164'])).

thf('246',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['163','164'])).

thf('247',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['157','158','159'])).

thf('248',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) ) ) ),
    inference(demod,[status(thm)],['244','245','246','247'])).

thf('249',plain,
    ( ( v1_funct_1 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['230','248'])).

thf('250',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('251',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v1_funct_1 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) ) ),
    inference(clc,[status(thm)],['249','250'])).

thf('252',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('253',plain,(
    v1_funct_1 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) ),
    inference(clc,[status(thm)],['251','252'])).

thf('254',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ sk_C )
    = ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) ),
    inference('sup+',[status(thm)],['224','225'])).

thf('255',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ sk_C ) ),
    inference(demod,[status(thm)],['253','254'])).

thf('256',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ sk_C ) @ X0 )
      | ( ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ sk_C )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['229','255'])).

thf('257',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('258',plain,(
    ! [X22: $i] :
      ( ( m1_pre_topc @ X22 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('259',plain,(
    m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('260',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_pre_topc @ X17 @ X18 )
      | ~ ( m1_pre_topc @ X19 @ X18 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_funct_2 @ X21 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X20 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X20 ) ) ) )
      | ( v1_funct_2 @ ( k3_tmap_1 @ X18 @ X20 @ X19 @ X17 @ X21 ) @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_tmap_1])).

thf('261',plain,(
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
    inference('sup-',[status(thm)],['259','260'])).

thf('262',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('263',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('264',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('265',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['261','262','263','264'])).

thf('266',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['106','107'])).

thf('267',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['265','266'])).

thf('268',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_D )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ( v2_struct_0 @ sk_D )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['258','267'])).

thf('269',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['163','164'])).

thf('270',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['163','164'])).

thf('271',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['157','158','159'])).

thf('272',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['268','269','270','271'])).

thf('273',plain,
    ( ( v1_funct_2 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['257','272'])).

thf('274',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ sk_C )
    = ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) ),
    inference('sup+',[status(thm)],['224','225'])).

thf('275',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['273','274'])).

thf('276',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('277',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v1_funct_2 @ ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['275','276'])).

thf('278',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('279',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['277','278'])).

thf('280',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ sk_C ) @ X0 )
      | ( ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ sk_C )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['256','279'])).

thf('281',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ sk_C )
      = ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) ) ),
    inference('sup-',[status(thm)],['187','280'])).

thf('282',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('283',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['35','36','37','38'])).

thf('284',plain,
    ( ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['282','283'])).

thf('285',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('286',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E ) ) ),
    inference(clc,[status(thm)],['284','285'])).

thf('287',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('288',plain,(
    v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference(clc,[status(thm)],['286','287'])).

thf('289',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('290',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('291',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['289','290'])).

thf('292',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('293',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['291','292'])).

thf('294',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('295',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['293','294'])).

thf('296',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('297',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['70','71','72','73','74','75','76'])).

thf('298',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['296','297'])).

thf('299',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('300',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['298','299'])).

thf('301',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('302',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['300','301'])).

thf('303',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference('sup+',[status(thm)],['295','302'])).

thf('304',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) ),
    inference(demod,[status(thm)],['288','303'])).

thf('305',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('306',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['97','98','99','100'])).

thf('307',plain,
    ( ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['305','306'])).

thf('308',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference('sup+',[status(thm)],['295','302'])).

thf('309',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['307','308'])).

thf('310',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('311',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['309','310'])).

thf('312',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('313',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['311','312'])).

thf('314',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('315',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['12','13','14','15'])).

thf('316',plain,
    ( ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['314','315'])).

thf('317',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('318',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['316','317'])).

thf('319',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('320',plain,(
    m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['318','319'])).

thf('321',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference('sup+',[status(thm)],['295','302'])).

thf('322',plain,(
    m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['320','321'])).

thf('323',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ sk_C )
      = ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) ) ),
    inference(demod,[status(thm)],['281','304','313','322'])).

thf('324',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('325',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('326',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['324','325'])).

thf('327',plain,(
    r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('328',plain,(
    m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['110','111'])).

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

thf('329',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( v2_struct_0 @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ~ ( l1_pre_topc @ X23 )
      | ( v2_struct_0 @ X24 )
      | ~ ( m1_pre_topc @ X24 @ X23 )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X24 ) )
      | ( r1_tmap_1 @ X24 @ X26 @ ( k2_tmap_1 @ X23 @ X26 @ X27 @ X24 ) @ X25 )
      | ( X28 != X25 )
      | ~ ( r1_tmap_1 @ X23 @ X26 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X23 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X26 ) ) ) )
      | ~ ( v1_funct_2 @ X27 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X26 ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t64_tmap_1])).

thf('330',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( v2_struct_0 @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_funct_2 @ X27 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X26 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X26 ) ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X23 ) )
      | ~ ( r1_tmap_1 @ X23 @ X26 @ X27 @ X25 )
      | ( r1_tmap_1 @ X24 @ X26 @ ( k2_tmap_1 @ X23 @ X26 @ X27 @ X24 ) @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X24 ) )
      | ~ ( m1_pre_topc @ X24 @ X23 )
      | ( v2_struct_0 @ X24 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(simplify,[status(thm)],['329'])).

thf('331',plain,(
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
    inference('sup-',[status(thm)],['328','330'])).

thf('332',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['157','158','159'])).

thf('333',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['163','164'])).

thf('334',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['106','107'])).

thf('335',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('336',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('337',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('338',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ sk_B @ ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ X0 ) @ X1 )
      | ~ ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_D ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['331','332','333','334','335','336','337'])).

thf('339',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) )
      | ( r1_tmap_1 @ X0 @ sk_B @ ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ X0 ) @ sk_F )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['327','338'])).

thf('340',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('341',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r1_tmap_1 @ X0 @ sk_B @ ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ X0 ) @ sk_F )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['339','340'])).

thf('342',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ~ ( m1_pre_topc @ sk_C @ sk_D )
    | ( r1_tmap_1 @ sk_C @ sk_B @ ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ sk_C ) @ sk_F )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['326','341'])).

thf('343',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('344',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_C @ sk_B @ ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ sk_C ) @ sk_F )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['342','343'])).

thf('345',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup+',[status(thm)],['323','344'])).

thf('346',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_C @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F ) ),
    inference(simplify,[status(thm)],['345'])).

thf('347',plain,(
    ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('348',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('349',plain,(
    ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F ) ),
    inference(demod,[status(thm)],['347','348'])).

thf('350',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['346','349'])).

thf('351',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('352',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['350','351'])).

thf('353',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('354',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D ) ),
    inference(clc,[status(thm)],['352','353'])).

thf('355',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('356',plain,(
    v2_struct_0 @ sk_D ),
    inference(clc,[status(thm)],['354','355'])).

thf('357',plain,(
    $false ),
    inference(demod,[status(thm)],['0','356'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.kPBbjykmWM
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:28:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.60/0.85  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.60/0.85  % Solved by: fo/fo7.sh
% 0.60/0.85  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.60/0.85  % done 633 iterations in 0.383s
% 0.60/0.85  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.60/0.85  % SZS output start Refutation
% 0.60/0.85  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.60/0.85  thf(sk_G_type, type, sk_G: $i).
% 0.60/0.85  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.60/0.85  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.60/0.85  thf(sk_E_type, type, sk_E: $i).
% 0.60/0.85  thf(sk_D_type, type, sk_D: $i).
% 0.60/0.85  thf(sk_F_type, type, sk_F: $i).
% 0.60/0.85  thf(sk_A_type, type, sk_A: $i).
% 0.60/0.85  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.60/0.85  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.60/0.85  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.60/0.85  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.60/0.85  thf(sk_B_type, type, sk_B: $i).
% 0.60/0.85  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.60/0.85  thf(sk_C_type, type, sk_C: $i).
% 0.60/0.85  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.60/0.85  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.60/0.85  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.60/0.85  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.60/0.85  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.60/0.85  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.60/0.85  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.60/0.85  thf(t82_tmap_1, conjecture,
% 0.60/0.85    (![A:$i]:
% 0.60/0.85     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.60/0.85       ( ![B:$i]:
% 0.60/0.85         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.60/0.85             ( l1_pre_topc @ B ) ) =>
% 0.60/0.85           ( ![C:$i]:
% 0.60/0.85             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.60/0.85               ( ![D:$i]:
% 0.60/0.85                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.60/0.85                   ( ![E:$i]:
% 0.60/0.85                     ( ( ( v1_funct_1 @ E ) & 
% 0.60/0.85                         ( v1_funct_2 @
% 0.60/0.85                           E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.60/0.85                         ( m1_subset_1 @
% 0.60/0.85                           E @ 
% 0.60/0.85                           ( k1_zfmisc_1 @
% 0.60/0.85                             ( k2_zfmisc_1 @
% 0.60/0.85                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.60/0.85                       ( ( m1_pre_topc @ C @ D ) =>
% 0.60/0.85                         ( ![F:$i]:
% 0.60/0.85                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.60/0.85                             ( ![G:$i]:
% 0.60/0.85                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.60/0.85                                 ( ( ( ( F ) = ( G ) ) & 
% 0.60/0.85                                     ( r1_tmap_1 @
% 0.60/0.85                                       D @ B @ ( k2_tmap_1 @ A @ B @ E @ D ) @ 
% 0.60/0.85                                       F ) ) =>
% 0.60/0.85                                   ( r1_tmap_1 @
% 0.60/0.85                                     C @ B @ ( k2_tmap_1 @ A @ B @ E @ C ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.60/0.85  thf(zf_stmt_0, negated_conjecture,
% 0.60/0.85    (~( ![A:$i]:
% 0.60/0.85        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.60/0.85            ( l1_pre_topc @ A ) ) =>
% 0.60/0.85          ( ![B:$i]:
% 0.60/0.85            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.60/0.85                ( l1_pre_topc @ B ) ) =>
% 0.60/0.85              ( ![C:$i]:
% 0.60/0.85                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.60/0.85                  ( ![D:$i]:
% 0.60/0.85                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.60/0.85                      ( ![E:$i]:
% 0.60/0.85                        ( ( ( v1_funct_1 @ E ) & 
% 0.60/0.85                            ( v1_funct_2 @
% 0.60/0.85                              E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.60/0.85                            ( m1_subset_1 @
% 0.60/0.85                              E @ 
% 0.60/0.85                              ( k1_zfmisc_1 @
% 0.60/0.85                                ( k2_zfmisc_1 @
% 0.60/0.85                                  ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.60/0.85                          ( ( m1_pre_topc @ C @ D ) =>
% 0.60/0.85                            ( ![F:$i]:
% 0.60/0.85                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.60/0.85                                ( ![G:$i]:
% 0.60/0.85                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.60/0.85                                    ( ( ( ( F ) = ( G ) ) & 
% 0.60/0.85                                        ( r1_tmap_1 @
% 0.60/0.85                                          D @ B @ 
% 0.60/0.85                                          ( k2_tmap_1 @ A @ B @ E @ D ) @ F ) ) =>
% 0.60/0.85                                      ( r1_tmap_1 @
% 0.60/0.85                                        C @ B @ 
% 0.60/0.85                                        ( k2_tmap_1 @ A @ B @ E @ C ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.60/0.85    inference('cnf.neg', [status(esa)], [t82_tmap_1])).
% 0.60/0.85  thf('0', plain, (~ (v2_struct_0 @ sk_D)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('1', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('2', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf(t2_tsep_1, axiom,
% 0.60/0.85    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.60/0.85  thf('3', plain,
% 0.60/0.85      (![X22 : $i]: ((m1_pre_topc @ X22 @ X22) | ~ (l1_pre_topc @ X22))),
% 0.60/0.85      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.60/0.85  thf('4', plain,
% 0.60/0.85      ((m1_subset_1 @ sk_E @ 
% 0.60/0.85        (k1_zfmisc_1 @ 
% 0.60/0.85         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf(dt_k3_tmap_1, axiom,
% 0.60/0.85    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.60/0.85     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.60/0.85         ( l1_pre_topc @ A ) & ( ~( v2_struct_0 @ B ) ) & 
% 0.60/0.85         ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) & ( m1_pre_topc @ C @ A ) & 
% 0.60/0.85         ( m1_pre_topc @ D @ A ) & ( v1_funct_1 @ E ) & 
% 0.60/0.85         ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.60/0.85         ( m1_subset_1 @
% 0.60/0.85           E @ 
% 0.60/0.85           ( k1_zfmisc_1 @
% 0.60/0.85             ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.60/0.85       ( ( v1_funct_1 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) ) & 
% 0.60/0.85         ( v1_funct_2 @
% 0.60/0.85           ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ ( u1_struct_0 @ D ) @ 
% 0.60/0.85           ( u1_struct_0 @ B ) ) & 
% 0.60/0.85         ( m1_subset_1 @
% 0.60/0.85           ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ 
% 0.60/0.85           ( k1_zfmisc_1 @
% 0.60/0.85             ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.60/0.85  thf('5', plain,
% 0.60/0.85      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.60/0.85         (~ (m1_pre_topc @ X17 @ X18)
% 0.60/0.85          | ~ (m1_pre_topc @ X19 @ X18)
% 0.60/0.85          | ~ (l1_pre_topc @ X20)
% 0.60/0.85          | ~ (v2_pre_topc @ X20)
% 0.60/0.85          | (v2_struct_0 @ X20)
% 0.60/0.85          | ~ (l1_pre_topc @ X18)
% 0.60/0.85          | ~ (v2_pre_topc @ X18)
% 0.60/0.85          | (v2_struct_0 @ X18)
% 0.60/0.85          | ~ (v1_funct_1 @ X21)
% 0.60/0.85          | ~ (v1_funct_2 @ X21 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X20))
% 0.60/0.85          | ~ (m1_subset_1 @ X21 @ 
% 0.60/0.85               (k1_zfmisc_1 @ 
% 0.60/0.85                (k2_zfmisc_1 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X20))))
% 0.60/0.85          | (m1_subset_1 @ (k3_tmap_1 @ X18 @ X20 @ X19 @ X17 @ X21) @ 
% 0.60/0.85             (k1_zfmisc_1 @ 
% 0.60/0.85              (k2_zfmisc_1 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X20)))))),
% 0.60/0.85      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 0.60/0.85  thf('6', plain,
% 0.60/0.85      (![X0 : $i, X1 : $i]:
% 0.60/0.85         ((m1_subset_1 @ (k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 0.60/0.85           (k1_zfmisc_1 @ 
% 0.60/0.85            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.60/0.85          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.60/0.85          | ~ (v1_funct_1 @ sk_E)
% 0.60/0.85          | (v2_struct_0 @ X1)
% 0.60/0.85          | ~ (v2_pre_topc @ X1)
% 0.60/0.85          | ~ (l1_pre_topc @ X1)
% 0.60/0.85          | (v2_struct_0 @ sk_B)
% 0.60/0.85          | ~ (v2_pre_topc @ sk_B)
% 0.60/0.85          | ~ (l1_pre_topc @ sk_B)
% 0.60/0.85          | ~ (m1_pre_topc @ sk_A @ X1)
% 0.60/0.85          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.60/0.85      inference('sup-', [status(thm)], ['4', '5'])).
% 0.60/0.85  thf('7', plain,
% 0.60/0.85      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('8', plain, ((v1_funct_1 @ sk_E)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('9', plain, ((v2_pre_topc @ sk_B)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('10', plain, ((l1_pre_topc @ sk_B)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('11', plain,
% 0.60/0.85      (![X0 : $i, X1 : $i]:
% 0.60/0.85         ((m1_subset_1 @ (k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 0.60/0.85           (k1_zfmisc_1 @ 
% 0.60/0.85            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.60/0.85          | (v2_struct_0 @ X1)
% 0.60/0.85          | ~ (v2_pre_topc @ X1)
% 0.60/0.85          | ~ (l1_pre_topc @ X1)
% 0.60/0.85          | (v2_struct_0 @ sk_B)
% 0.60/0.85          | ~ (m1_pre_topc @ sk_A @ X1)
% 0.60/0.85          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.60/0.85      inference('demod', [status(thm)], ['6', '7', '8', '9', '10'])).
% 0.60/0.85  thf('12', plain,
% 0.60/0.85      (![X0 : $i]:
% 0.60/0.85         (~ (l1_pre_topc @ sk_A)
% 0.60/0.85          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.60/0.85          | (v2_struct_0 @ sk_B)
% 0.60/0.85          | ~ (l1_pre_topc @ sk_A)
% 0.60/0.85          | ~ (v2_pre_topc @ sk_A)
% 0.60/0.85          | (v2_struct_0 @ sk_A)
% 0.60/0.85          | (m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 0.60/0.85             (k1_zfmisc_1 @ 
% 0.60/0.85              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))))),
% 0.60/0.85      inference('sup-', [status(thm)], ['3', '11'])).
% 0.60/0.85  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('15', plain, ((v2_pre_topc @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('16', plain,
% 0.60/0.85      (![X0 : $i]:
% 0.60/0.85         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.60/0.85          | (v2_struct_0 @ sk_B)
% 0.60/0.85          | (v2_struct_0 @ sk_A)
% 0.60/0.85          | (m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 0.60/0.85             (k1_zfmisc_1 @ 
% 0.60/0.85              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))))),
% 0.60/0.85      inference('demod', [status(thm)], ['12', '13', '14', '15'])).
% 0.60/0.85  thf('17', plain,
% 0.60/0.85      (((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E) @ 
% 0.60/0.85         (k1_zfmisc_1 @ 
% 0.60/0.85          (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 0.60/0.85        | (v2_struct_0 @ sk_A)
% 0.60/0.85        | (v2_struct_0 @ sk_B))),
% 0.60/0.85      inference('sup-', [status(thm)], ['2', '16'])).
% 0.60/0.85  thf('18', plain, (~ (v2_struct_0 @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('19', plain,
% 0.60/0.85      (((v2_struct_0 @ sk_B)
% 0.60/0.85        | (m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E) @ 
% 0.60/0.85           (k1_zfmisc_1 @ 
% 0.60/0.85            (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))))),
% 0.60/0.85      inference('clc', [status(thm)], ['17', '18'])).
% 0.60/0.85  thf('20', plain, (~ (v2_struct_0 @ sk_B)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('21', plain,
% 0.60/0.85      ((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E) @ 
% 0.60/0.85        (k1_zfmisc_1 @ 
% 0.60/0.85         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.60/0.85      inference('clc', [status(thm)], ['19', '20'])).
% 0.60/0.85  thf(redefinition_r2_funct_2, axiom,
% 0.60/0.85    (![A:$i,B:$i,C:$i,D:$i]:
% 0.60/0.85     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.60/0.85         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.60/0.85         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.60/0.85         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.60/0.85       ( ( r2_funct_2 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.60/0.85  thf('22', plain,
% 0.60/0.85      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.60/0.85         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 0.60/0.85          | ~ (v1_funct_2 @ X0 @ X1 @ X2)
% 0.60/0.85          | ~ (v1_funct_1 @ X0)
% 0.60/0.85          | ~ (v1_funct_1 @ X3)
% 0.60/0.85          | ~ (v1_funct_2 @ X3 @ X1 @ X2)
% 0.60/0.85          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 0.60/0.85          | (r2_funct_2 @ X1 @ X2 @ X0 @ X3)
% 0.60/0.85          | ((X0) != (X3)))),
% 0.60/0.85      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 0.60/0.85  thf('23', plain,
% 0.60/0.85      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.60/0.85         ((r2_funct_2 @ X1 @ X2 @ X3 @ X3)
% 0.60/0.85          | ~ (v1_funct_1 @ X3)
% 0.60/0.85          | ~ (v1_funct_2 @ X3 @ X1 @ X2)
% 0.60/0.85          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2))))),
% 0.60/0.85      inference('simplify', [status(thm)], ['22'])).
% 0.60/0.85  thf('24', plain,
% 0.60/0.85      ((~ (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E) @ 
% 0.60/0.85           (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.60/0.85        | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))
% 0.60/0.85        | (r2_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.85           (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E) @ 
% 0.60/0.85           (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E)))),
% 0.60/0.85      inference('sup-', [status(thm)], ['21', '23'])).
% 0.60/0.85  thf('25', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('26', plain,
% 0.60/0.85      (![X22 : $i]: ((m1_pre_topc @ X22 @ X22) | ~ (l1_pre_topc @ X22))),
% 0.60/0.85      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.60/0.85  thf('27', plain,
% 0.60/0.85      ((m1_subset_1 @ sk_E @ 
% 0.60/0.85        (k1_zfmisc_1 @ 
% 0.60/0.85         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('28', plain,
% 0.60/0.85      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.60/0.85         (~ (m1_pre_topc @ X17 @ X18)
% 0.60/0.85          | ~ (m1_pre_topc @ X19 @ X18)
% 0.60/0.85          | ~ (l1_pre_topc @ X20)
% 0.60/0.85          | ~ (v2_pre_topc @ X20)
% 0.60/0.85          | (v2_struct_0 @ X20)
% 0.60/0.85          | ~ (l1_pre_topc @ X18)
% 0.60/0.85          | ~ (v2_pre_topc @ X18)
% 0.60/0.85          | (v2_struct_0 @ X18)
% 0.60/0.85          | ~ (v1_funct_1 @ X21)
% 0.60/0.85          | ~ (v1_funct_2 @ X21 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X20))
% 0.60/0.85          | ~ (m1_subset_1 @ X21 @ 
% 0.60/0.85               (k1_zfmisc_1 @ 
% 0.60/0.85                (k2_zfmisc_1 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X20))))
% 0.60/0.85          | (v1_funct_1 @ (k3_tmap_1 @ X18 @ X20 @ X19 @ X17 @ X21)))),
% 0.60/0.85      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 0.60/0.85  thf('29', plain,
% 0.60/0.85      (![X0 : $i, X1 : $i]:
% 0.60/0.85         ((v1_funct_1 @ (k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E))
% 0.60/0.85          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.60/0.85          | ~ (v1_funct_1 @ sk_E)
% 0.60/0.85          | (v2_struct_0 @ X1)
% 0.60/0.85          | ~ (v2_pre_topc @ X1)
% 0.60/0.85          | ~ (l1_pre_topc @ X1)
% 0.60/0.85          | (v2_struct_0 @ sk_B)
% 0.60/0.85          | ~ (v2_pre_topc @ sk_B)
% 0.60/0.85          | ~ (l1_pre_topc @ sk_B)
% 0.60/0.85          | ~ (m1_pre_topc @ sk_A @ X1)
% 0.60/0.85          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.60/0.85      inference('sup-', [status(thm)], ['27', '28'])).
% 0.60/0.85  thf('30', plain,
% 0.60/0.85      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('31', plain, ((v1_funct_1 @ sk_E)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('32', plain, ((v2_pre_topc @ sk_B)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('33', plain, ((l1_pre_topc @ sk_B)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('34', plain,
% 0.60/0.85      (![X0 : $i, X1 : $i]:
% 0.60/0.85         ((v1_funct_1 @ (k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E))
% 0.60/0.85          | (v2_struct_0 @ X1)
% 0.60/0.85          | ~ (v2_pre_topc @ X1)
% 0.60/0.85          | ~ (l1_pre_topc @ X1)
% 0.60/0.85          | (v2_struct_0 @ sk_B)
% 0.60/0.85          | ~ (m1_pre_topc @ sk_A @ X1)
% 0.60/0.85          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.60/0.85      inference('demod', [status(thm)], ['29', '30', '31', '32', '33'])).
% 0.60/0.85  thf('35', plain,
% 0.60/0.85      (![X0 : $i]:
% 0.60/0.85         (~ (l1_pre_topc @ sk_A)
% 0.60/0.85          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.60/0.85          | (v2_struct_0 @ sk_B)
% 0.60/0.85          | ~ (l1_pre_topc @ sk_A)
% 0.60/0.85          | ~ (v2_pre_topc @ sk_A)
% 0.60/0.85          | (v2_struct_0 @ sk_A)
% 0.60/0.85          | (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E)))),
% 0.60/0.85      inference('sup-', [status(thm)], ['26', '34'])).
% 0.60/0.85  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('38', plain, ((v2_pre_topc @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('39', plain,
% 0.60/0.85      (![X0 : $i]:
% 0.60/0.85         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.60/0.85          | (v2_struct_0 @ sk_B)
% 0.60/0.85          | (v2_struct_0 @ sk_A)
% 0.60/0.85          | (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E)))),
% 0.60/0.85      inference('demod', [status(thm)], ['35', '36', '37', '38'])).
% 0.60/0.85  thf('40', plain,
% 0.60/0.85      (((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))
% 0.60/0.85        | (v2_struct_0 @ sk_A)
% 0.60/0.85        | (v2_struct_0 @ sk_B))),
% 0.60/0.85      inference('sup-', [status(thm)], ['25', '39'])).
% 0.60/0.85  thf('41', plain, (~ (v2_struct_0 @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('42', plain,
% 0.60/0.85      (((v2_struct_0 @ sk_B)
% 0.60/0.85        | (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E)))),
% 0.60/0.85      inference('clc', [status(thm)], ['40', '41'])).
% 0.60/0.85  thf('43', plain, (~ (v2_struct_0 @ sk_B)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('44', plain,
% 0.60/0.85      ((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))),
% 0.60/0.85      inference('clc', [status(thm)], ['42', '43'])).
% 0.60/0.85  thf('45', plain,
% 0.60/0.85      ((~ (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E) @ 
% 0.60/0.85           (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.60/0.85        | (r2_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.85           (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E) @ 
% 0.60/0.85           (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E)))),
% 0.60/0.85      inference('demod', [status(thm)], ['24', '44'])).
% 0.60/0.85  thf('46', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('47', plain,
% 0.60/0.85      (![X22 : $i]: ((m1_pre_topc @ X22 @ X22) | ~ (l1_pre_topc @ X22))),
% 0.60/0.85      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.60/0.85  thf('48', plain,
% 0.60/0.85      ((m1_subset_1 @ sk_E @ 
% 0.60/0.85        (k1_zfmisc_1 @ 
% 0.60/0.85         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf(d5_tmap_1, axiom,
% 0.60/0.85    (![A:$i]:
% 0.60/0.85     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.60/0.85       ( ![B:$i]:
% 0.60/0.85         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.60/0.85             ( l1_pre_topc @ B ) ) =>
% 0.60/0.85           ( ![C:$i]:
% 0.60/0.85             ( ( m1_pre_topc @ C @ A ) =>
% 0.60/0.85               ( ![D:$i]:
% 0.60/0.85                 ( ( m1_pre_topc @ D @ A ) =>
% 0.60/0.85                   ( ![E:$i]:
% 0.60/0.85                     ( ( ( v1_funct_1 @ E ) & 
% 0.60/0.85                         ( v1_funct_2 @
% 0.60/0.85                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.60/0.85                         ( m1_subset_1 @
% 0.60/0.85                           E @ 
% 0.60/0.85                           ( k1_zfmisc_1 @
% 0.60/0.85                             ( k2_zfmisc_1 @
% 0.60/0.85                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.60/0.85                       ( ( m1_pre_topc @ D @ C ) =>
% 0.60/0.85                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 0.60/0.85                           ( k2_partfun1 @
% 0.60/0.85                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 0.60/0.85                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.60/0.85  thf('49', plain,
% 0.60/0.85      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.60/0.85         ((v2_struct_0 @ X12)
% 0.60/0.85          | ~ (v2_pre_topc @ X12)
% 0.60/0.85          | ~ (l1_pre_topc @ X12)
% 0.60/0.85          | ~ (m1_pre_topc @ X13 @ X14)
% 0.60/0.85          | ~ (m1_pre_topc @ X13 @ X15)
% 0.60/0.85          | ((k3_tmap_1 @ X14 @ X12 @ X15 @ X13 @ X16)
% 0.60/0.85              = (k2_partfun1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X12) @ 
% 0.60/0.85                 X16 @ (u1_struct_0 @ X13)))
% 0.60/0.85          | ~ (m1_subset_1 @ X16 @ 
% 0.60/0.85               (k1_zfmisc_1 @ 
% 0.60/0.85                (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X12))))
% 0.60/0.85          | ~ (v1_funct_2 @ X16 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X12))
% 0.60/0.85          | ~ (v1_funct_1 @ X16)
% 0.60/0.85          | ~ (m1_pre_topc @ X15 @ X14)
% 0.60/0.85          | ~ (l1_pre_topc @ X14)
% 0.60/0.85          | ~ (v2_pre_topc @ X14)
% 0.60/0.85          | (v2_struct_0 @ X14))),
% 0.60/0.85      inference('cnf', [status(esa)], [d5_tmap_1])).
% 0.60/0.85  thf('50', plain,
% 0.60/0.85      (![X0 : $i, X1 : $i]:
% 0.60/0.85         ((v2_struct_0 @ X0)
% 0.60/0.85          | ~ (v2_pre_topc @ X0)
% 0.60/0.85          | ~ (l1_pre_topc @ X0)
% 0.60/0.85          | ~ (m1_pre_topc @ sk_A @ X0)
% 0.60/0.85          | ~ (v1_funct_1 @ sk_E)
% 0.60/0.85          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.60/0.85          | ((k3_tmap_1 @ X0 @ sk_B @ sk_A @ X1 @ sk_E)
% 0.60/0.85              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.85                 sk_E @ (u1_struct_0 @ X1)))
% 0.60/0.85          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.60/0.85          | ~ (m1_pre_topc @ X1 @ X0)
% 0.60/0.85          | ~ (l1_pre_topc @ sk_B)
% 0.60/0.85          | ~ (v2_pre_topc @ sk_B)
% 0.60/0.85          | (v2_struct_0 @ sk_B))),
% 0.60/0.85      inference('sup-', [status(thm)], ['48', '49'])).
% 0.60/0.85  thf('51', plain, ((v1_funct_1 @ sk_E)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('52', plain,
% 0.60/0.85      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('53', plain, ((l1_pre_topc @ sk_B)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('54', plain, ((v2_pre_topc @ sk_B)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('55', plain,
% 0.60/0.85      (![X0 : $i, X1 : $i]:
% 0.60/0.85         ((v2_struct_0 @ X0)
% 0.60/0.85          | ~ (v2_pre_topc @ X0)
% 0.60/0.85          | ~ (l1_pre_topc @ X0)
% 0.60/0.85          | ~ (m1_pre_topc @ sk_A @ X0)
% 0.60/0.85          | ((k3_tmap_1 @ X0 @ sk_B @ sk_A @ X1 @ sk_E)
% 0.60/0.85              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.85                 sk_E @ (u1_struct_0 @ X1)))
% 0.60/0.85          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.60/0.85          | ~ (m1_pre_topc @ X1 @ X0)
% 0.60/0.85          | (v2_struct_0 @ sk_B))),
% 0.60/0.85      inference('demod', [status(thm)], ['50', '51', '52', '53', '54'])).
% 0.60/0.85  thf('56', plain,
% 0.60/0.85      (![X0 : $i]:
% 0.60/0.85         (~ (l1_pre_topc @ sk_A)
% 0.60/0.85          | (v2_struct_0 @ sk_B)
% 0.60/0.85          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.60/0.85          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.60/0.85          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E)
% 0.60/0.85              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.85                 sk_E @ (u1_struct_0 @ X0)))
% 0.60/0.85          | ~ (l1_pre_topc @ sk_A)
% 0.60/0.85          | ~ (v2_pre_topc @ sk_A)
% 0.60/0.85          | (v2_struct_0 @ sk_A))),
% 0.60/0.85      inference('sup-', [status(thm)], ['47', '55'])).
% 0.60/0.85  thf('57', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('58', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('59', plain, ((v2_pre_topc @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('60', plain,
% 0.60/0.85      (![X0 : $i]:
% 0.60/0.85         ((v2_struct_0 @ sk_B)
% 0.60/0.85          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.60/0.85          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.60/0.85          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E)
% 0.60/0.85              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.85                 sk_E @ (u1_struct_0 @ X0)))
% 0.60/0.85          | (v2_struct_0 @ sk_A))),
% 0.60/0.85      inference('demod', [status(thm)], ['56', '57', '58', '59'])).
% 0.60/0.85  thf('61', plain,
% 0.60/0.85      (![X0 : $i]:
% 0.60/0.85         ((v2_struct_0 @ sk_A)
% 0.60/0.85          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E)
% 0.60/0.85              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.85                 sk_E @ (u1_struct_0 @ X0)))
% 0.60/0.85          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.60/0.85          | (v2_struct_0 @ sk_B))),
% 0.60/0.85      inference('simplify', [status(thm)], ['60'])).
% 0.60/0.85  thf('62', plain,
% 0.60/0.85      (((v2_struct_0 @ sk_B)
% 0.60/0.85        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E)
% 0.60/0.85            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.85               sk_E @ (u1_struct_0 @ sk_D)))
% 0.60/0.85        | (v2_struct_0 @ sk_A))),
% 0.60/0.85      inference('sup-', [status(thm)], ['46', '61'])).
% 0.60/0.85  thf('63', plain, (~ (v2_struct_0 @ sk_B)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('64', plain,
% 0.60/0.85      (((v2_struct_0 @ sk_A)
% 0.60/0.85        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E)
% 0.60/0.85            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.85               sk_E @ (u1_struct_0 @ sk_D))))),
% 0.60/0.85      inference('clc', [status(thm)], ['62', '63'])).
% 0.60/0.85  thf('65', plain, (~ (v2_struct_0 @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('66', plain,
% 0.60/0.85      (((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E)
% 0.60/0.85         = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.60/0.85            (u1_struct_0 @ sk_D)))),
% 0.60/0.85      inference('clc', [status(thm)], ['64', '65'])).
% 0.60/0.85  thf('67', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('68', plain,
% 0.60/0.85      ((m1_subset_1 @ sk_E @ 
% 0.60/0.85        (k1_zfmisc_1 @ 
% 0.60/0.85         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf(d4_tmap_1, axiom,
% 0.60/0.85    (![A:$i]:
% 0.60/0.85     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.60/0.85       ( ![B:$i]:
% 0.60/0.85         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.60/0.85             ( l1_pre_topc @ B ) ) =>
% 0.60/0.85           ( ![C:$i]:
% 0.60/0.85             ( ( ( v1_funct_1 @ C ) & 
% 0.60/0.85                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.60/0.85                 ( m1_subset_1 @
% 0.60/0.85                   C @ 
% 0.60/0.85                   ( k1_zfmisc_1 @
% 0.60/0.85                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.60/0.85               ( ![D:$i]:
% 0.60/0.85                 ( ( m1_pre_topc @ D @ A ) =>
% 0.60/0.85                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 0.60/0.85                     ( k2_partfun1 @
% 0.60/0.85                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.60/0.85                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 0.60/0.85  thf('69', plain,
% 0.60/0.85      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.60/0.85         ((v2_struct_0 @ X8)
% 0.60/0.85          | ~ (v2_pre_topc @ X8)
% 0.60/0.85          | ~ (l1_pre_topc @ X8)
% 0.60/0.85          | ~ (m1_pre_topc @ X9 @ X10)
% 0.60/0.85          | ((k2_tmap_1 @ X10 @ X8 @ X11 @ X9)
% 0.60/0.85              = (k2_partfun1 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X8) @ 
% 0.60/0.85                 X11 @ (u1_struct_0 @ X9)))
% 0.60/0.85          | ~ (m1_subset_1 @ X11 @ 
% 0.60/0.85               (k1_zfmisc_1 @ 
% 0.60/0.85                (k2_zfmisc_1 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X8))))
% 0.60/0.85          | ~ (v1_funct_2 @ X11 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X8))
% 0.60/0.85          | ~ (v1_funct_1 @ X11)
% 0.60/0.85          | ~ (l1_pre_topc @ X10)
% 0.60/0.85          | ~ (v2_pre_topc @ X10)
% 0.60/0.85          | (v2_struct_0 @ X10))),
% 0.60/0.85      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.60/0.85  thf('70', plain,
% 0.60/0.85      (![X0 : $i]:
% 0.60/0.85         ((v2_struct_0 @ sk_A)
% 0.60/0.85          | ~ (v2_pre_topc @ sk_A)
% 0.60/0.85          | ~ (l1_pre_topc @ sk_A)
% 0.60/0.85          | ~ (v1_funct_1 @ sk_E)
% 0.60/0.85          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.60/0.85          | ((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0)
% 0.60/0.85              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.85                 sk_E @ (u1_struct_0 @ X0)))
% 0.60/0.85          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.60/0.85          | ~ (l1_pre_topc @ sk_B)
% 0.60/0.85          | ~ (v2_pre_topc @ sk_B)
% 0.60/0.85          | (v2_struct_0 @ sk_B))),
% 0.60/0.85      inference('sup-', [status(thm)], ['68', '69'])).
% 0.60/0.85  thf('71', plain, ((v2_pre_topc @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('72', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('73', plain, ((v1_funct_1 @ sk_E)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('74', plain,
% 0.60/0.85      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('75', plain, ((l1_pre_topc @ sk_B)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('76', plain, ((v2_pre_topc @ sk_B)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('77', plain,
% 0.60/0.85      (![X0 : $i]:
% 0.60/0.85         ((v2_struct_0 @ sk_A)
% 0.60/0.85          | ((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0)
% 0.60/0.85              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.85                 sk_E @ (u1_struct_0 @ X0)))
% 0.60/0.85          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.60/0.85          | (v2_struct_0 @ sk_B))),
% 0.60/0.85      inference('demod', [status(thm)],
% 0.60/0.85                ['70', '71', '72', '73', '74', '75', '76'])).
% 0.60/0.85  thf('78', plain,
% 0.60/0.85      (((v2_struct_0 @ sk_B)
% 0.60/0.85        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 0.60/0.85            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.85               sk_E @ (u1_struct_0 @ sk_D)))
% 0.60/0.85        | (v2_struct_0 @ sk_A))),
% 0.60/0.85      inference('sup-', [status(thm)], ['67', '77'])).
% 0.60/0.85  thf('79', plain, (~ (v2_struct_0 @ sk_B)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('80', plain,
% 0.60/0.85      (((v2_struct_0 @ sk_A)
% 0.60/0.85        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 0.60/0.85            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.85               sk_E @ (u1_struct_0 @ sk_D))))),
% 0.60/0.85      inference('clc', [status(thm)], ['78', '79'])).
% 0.60/0.85  thf('81', plain, (~ (v2_struct_0 @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('82', plain,
% 0.60/0.85      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 0.60/0.85         = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.60/0.85            (u1_struct_0 @ sk_D)))),
% 0.60/0.85      inference('clc', [status(thm)], ['80', '81'])).
% 0.60/0.85  thf('83', plain,
% 0.60/0.85      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 0.60/0.85         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))),
% 0.60/0.85      inference('sup+', [status(thm)], ['66', '82'])).
% 0.60/0.85  thf('84', plain,
% 0.60/0.85      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 0.60/0.85         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))),
% 0.60/0.85      inference('sup+', [status(thm)], ['66', '82'])).
% 0.60/0.85  thf('85', plain,
% 0.60/0.85      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 0.60/0.85         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))),
% 0.60/0.85      inference('sup+', [status(thm)], ['66', '82'])).
% 0.60/0.85  thf('86', plain,
% 0.60/0.85      ((~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.60/0.85           (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.60/0.85        | (r2_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.85           (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.60/0.85           (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)))),
% 0.60/0.85      inference('demod', [status(thm)], ['45', '83', '84', '85'])).
% 0.60/0.85  thf('87', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('88', plain,
% 0.60/0.85      (![X22 : $i]: ((m1_pre_topc @ X22 @ X22) | ~ (l1_pre_topc @ X22))),
% 0.60/0.85      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.60/0.85  thf('89', plain,
% 0.60/0.85      ((m1_subset_1 @ sk_E @ 
% 0.60/0.85        (k1_zfmisc_1 @ 
% 0.60/0.85         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('90', plain,
% 0.60/0.85      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.60/0.85         (~ (m1_pre_topc @ X17 @ X18)
% 0.60/0.85          | ~ (m1_pre_topc @ X19 @ X18)
% 0.60/0.85          | ~ (l1_pre_topc @ X20)
% 0.60/0.85          | ~ (v2_pre_topc @ X20)
% 0.60/0.85          | (v2_struct_0 @ X20)
% 0.60/0.85          | ~ (l1_pre_topc @ X18)
% 0.60/0.85          | ~ (v2_pre_topc @ X18)
% 0.60/0.85          | (v2_struct_0 @ X18)
% 0.60/0.85          | ~ (v1_funct_1 @ X21)
% 0.60/0.85          | ~ (v1_funct_2 @ X21 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X20))
% 0.60/0.85          | ~ (m1_subset_1 @ X21 @ 
% 0.60/0.85               (k1_zfmisc_1 @ 
% 0.60/0.85                (k2_zfmisc_1 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X20))))
% 0.60/0.85          | (v1_funct_2 @ (k3_tmap_1 @ X18 @ X20 @ X19 @ X17 @ X21) @ 
% 0.60/0.85             (u1_struct_0 @ X17) @ (u1_struct_0 @ X20)))),
% 0.60/0.85      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 0.60/0.85  thf('91', plain,
% 0.60/0.85      (![X0 : $i, X1 : $i]:
% 0.60/0.85         ((v1_funct_2 @ (k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 0.60/0.85           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.60/0.85          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.60/0.85          | ~ (v1_funct_1 @ sk_E)
% 0.60/0.85          | (v2_struct_0 @ X1)
% 0.60/0.85          | ~ (v2_pre_topc @ X1)
% 0.60/0.85          | ~ (l1_pre_topc @ X1)
% 0.60/0.85          | (v2_struct_0 @ sk_B)
% 0.60/0.85          | ~ (v2_pre_topc @ sk_B)
% 0.60/0.85          | ~ (l1_pre_topc @ sk_B)
% 0.60/0.85          | ~ (m1_pre_topc @ sk_A @ X1)
% 0.60/0.85          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.60/0.85      inference('sup-', [status(thm)], ['89', '90'])).
% 0.60/0.85  thf('92', plain,
% 0.60/0.85      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('93', plain, ((v1_funct_1 @ sk_E)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('94', plain, ((v2_pre_topc @ sk_B)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('95', plain, ((l1_pre_topc @ sk_B)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('96', plain,
% 0.60/0.85      (![X0 : $i, X1 : $i]:
% 0.60/0.85         ((v1_funct_2 @ (k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 0.60/0.85           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.60/0.85          | (v2_struct_0 @ X1)
% 0.60/0.85          | ~ (v2_pre_topc @ X1)
% 0.60/0.85          | ~ (l1_pre_topc @ X1)
% 0.60/0.85          | (v2_struct_0 @ sk_B)
% 0.60/0.85          | ~ (m1_pre_topc @ sk_A @ X1)
% 0.60/0.85          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.60/0.85      inference('demod', [status(thm)], ['91', '92', '93', '94', '95'])).
% 0.60/0.85  thf('97', plain,
% 0.60/0.85      (![X0 : $i]:
% 0.60/0.85         (~ (l1_pre_topc @ sk_A)
% 0.60/0.85          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.60/0.85          | (v2_struct_0 @ sk_B)
% 0.60/0.85          | ~ (l1_pre_topc @ sk_A)
% 0.60/0.85          | ~ (v2_pre_topc @ sk_A)
% 0.60/0.85          | (v2_struct_0 @ sk_A)
% 0.60/0.85          | (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 0.60/0.85             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 0.60/0.85      inference('sup-', [status(thm)], ['88', '96'])).
% 0.60/0.85  thf('98', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('99', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('100', plain, ((v2_pre_topc @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('101', plain,
% 0.60/0.85      (![X0 : $i]:
% 0.60/0.85         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.60/0.85          | (v2_struct_0 @ sk_B)
% 0.60/0.85          | (v2_struct_0 @ sk_A)
% 0.60/0.85          | (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 0.60/0.85             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 0.60/0.85      inference('demod', [status(thm)], ['97', '98', '99', '100'])).
% 0.60/0.85  thf('102', plain,
% 0.60/0.85      (((v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E) @ 
% 0.60/0.85         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.60/0.85        | (v2_struct_0 @ sk_A)
% 0.60/0.85        | (v2_struct_0 @ sk_B))),
% 0.60/0.85      inference('sup-', [status(thm)], ['87', '101'])).
% 0.60/0.85  thf('103', plain,
% 0.60/0.85      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 0.60/0.85         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))),
% 0.60/0.85      inference('sup+', [status(thm)], ['66', '82'])).
% 0.60/0.85  thf('104', plain,
% 0.60/0.85      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.60/0.85         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.60/0.85        | (v2_struct_0 @ sk_A)
% 0.60/0.85        | (v2_struct_0 @ sk_B))),
% 0.60/0.85      inference('demod', [status(thm)], ['102', '103'])).
% 0.60/0.85  thf('105', plain, (~ (v2_struct_0 @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('106', plain,
% 0.60/0.85      (((v2_struct_0 @ sk_B)
% 0.60/0.85        | (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.60/0.85           (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))),
% 0.60/0.85      inference('clc', [status(thm)], ['104', '105'])).
% 0.60/0.85  thf('107', plain, (~ (v2_struct_0 @ sk_B)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('108', plain,
% 0.60/0.85      ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.60/0.85        (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.60/0.85      inference('clc', [status(thm)], ['106', '107'])).
% 0.60/0.85  thf('109', plain,
% 0.60/0.85      ((r2_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.85        (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.60/0.85        (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))),
% 0.60/0.85      inference('demod', [status(thm)], ['86', '108'])).
% 0.60/0.85  thf('110', plain,
% 0.60/0.85      ((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E) @ 
% 0.60/0.85        (k1_zfmisc_1 @ 
% 0.60/0.85         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.60/0.85      inference('clc', [status(thm)], ['19', '20'])).
% 0.60/0.85  thf('111', plain,
% 0.60/0.85      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 0.60/0.85         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))),
% 0.60/0.85      inference('sup+', [status(thm)], ['66', '82'])).
% 0.60/0.85  thf('112', plain,
% 0.60/0.85      ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.60/0.85        (k1_zfmisc_1 @ 
% 0.60/0.85         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.60/0.85      inference('demod', [status(thm)], ['110', '111'])).
% 0.60/0.85  thf(t77_tmap_1, axiom,
% 0.60/0.85    (![A:$i]:
% 0.60/0.85     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.60/0.85       ( ![B:$i]:
% 0.60/0.85         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.60/0.85             ( l1_pre_topc @ B ) ) =>
% 0.60/0.85           ( ![C:$i]:
% 0.60/0.85             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.60/0.85               ( ![D:$i]:
% 0.60/0.85                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.60/0.85                   ( ![E:$i]:
% 0.60/0.85                     ( ( ( v1_funct_1 @ E ) & 
% 0.60/0.85                         ( v1_funct_2 @
% 0.60/0.85                           E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.60/0.85                         ( m1_subset_1 @
% 0.60/0.85                           E @ 
% 0.60/0.85                           ( k1_zfmisc_1 @
% 0.60/0.85                             ( k2_zfmisc_1 @
% 0.60/0.85                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.60/0.85                       ( ![F:$i]:
% 0.60/0.85                         ( ( ( v1_funct_1 @ F ) & 
% 0.60/0.85                             ( v1_funct_2 @
% 0.60/0.85                               F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.60/0.85                             ( m1_subset_1 @
% 0.60/0.85                               F @ 
% 0.60/0.85                               ( k1_zfmisc_1 @
% 0.60/0.85                                 ( k2_zfmisc_1 @
% 0.60/0.85                                   ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.60/0.85                           ( ( ( r2_funct_2 @
% 0.60/0.85                                 ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ 
% 0.60/0.85                                 F @ ( k2_tmap_1 @ A @ B @ E @ C ) ) & 
% 0.60/0.85                               ( m1_pre_topc @ D @ C ) ) =>
% 0.60/0.85                             ( r2_funct_2 @
% 0.60/0.85                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) @ 
% 0.60/0.85                               ( k3_tmap_1 @ A @ B @ C @ D @ F ) @ 
% 0.60/0.85                               ( k2_tmap_1 @ A @ B @ E @ D ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.60/0.85  thf('113', plain,
% 0.60/0.85      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.60/0.85         ((v2_struct_0 @ X29)
% 0.60/0.85          | ~ (v2_pre_topc @ X29)
% 0.60/0.85          | ~ (l1_pre_topc @ X29)
% 0.60/0.85          | (v2_struct_0 @ X30)
% 0.60/0.85          | ~ (m1_pre_topc @ X30 @ X31)
% 0.60/0.85          | ~ (v1_funct_1 @ X32)
% 0.60/0.85          | ~ (v1_funct_2 @ X32 @ (u1_struct_0 @ X33) @ (u1_struct_0 @ X29))
% 0.60/0.85          | ~ (m1_subset_1 @ X32 @ 
% 0.60/0.85               (k1_zfmisc_1 @ 
% 0.60/0.85                (k2_zfmisc_1 @ (u1_struct_0 @ X33) @ (u1_struct_0 @ X29))))
% 0.60/0.85          | (r2_funct_2 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X29) @ 
% 0.60/0.85             (k3_tmap_1 @ X31 @ X29 @ X33 @ X30 @ X32) @ 
% 0.60/0.85             (k2_tmap_1 @ X31 @ X29 @ X34 @ X30))
% 0.60/0.85          | ~ (r2_funct_2 @ (u1_struct_0 @ X33) @ (u1_struct_0 @ X29) @ X32 @ 
% 0.60/0.85               (k2_tmap_1 @ X31 @ X29 @ X34 @ X33))
% 0.60/0.85          | ~ (m1_pre_topc @ X30 @ X33)
% 0.60/0.85          | ~ (m1_subset_1 @ X34 @ 
% 0.60/0.85               (k1_zfmisc_1 @ 
% 0.60/0.85                (k2_zfmisc_1 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X29))))
% 0.60/0.85          | ~ (v1_funct_2 @ X34 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X29))
% 0.60/0.85          | ~ (v1_funct_1 @ X34)
% 0.60/0.85          | ~ (m1_pre_topc @ X33 @ X31)
% 0.60/0.85          | (v2_struct_0 @ X33)
% 0.60/0.85          | ~ (l1_pre_topc @ X31)
% 0.60/0.85          | ~ (v2_pre_topc @ X31)
% 0.60/0.85          | (v2_struct_0 @ X31))),
% 0.60/0.85      inference('cnf', [status(esa)], [t77_tmap_1])).
% 0.60/0.85  thf('114', plain,
% 0.60/0.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.60/0.85         ((v2_struct_0 @ X0)
% 0.60/0.85          | ~ (v2_pre_topc @ X0)
% 0.60/0.85          | ~ (l1_pre_topc @ X0)
% 0.60/0.85          | (v2_struct_0 @ sk_D)
% 0.60/0.85          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.60/0.85          | ~ (v1_funct_1 @ X1)
% 0.60/0.85          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.60/0.85          | ~ (m1_subset_1 @ X1 @ 
% 0.60/0.85               (k1_zfmisc_1 @ 
% 0.60/0.85                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.60/0.85          | ~ (m1_pre_topc @ X2 @ sk_D)
% 0.60/0.85          | ~ (r2_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.85               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.60/0.85               (k2_tmap_1 @ X0 @ sk_B @ X1 @ sk_D))
% 0.60/0.85          | (r2_funct_2 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.85             (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X2 @ 
% 0.60/0.85              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.60/0.85             (k2_tmap_1 @ X0 @ sk_B @ X1 @ X2))
% 0.60/0.85          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.60/0.85               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.60/0.85          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))
% 0.60/0.85          | ~ (m1_pre_topc @ X2 @ X0)
% 0.60/0.85          | (v2_struct_0 @ X2)
% 0.60/0.85          | ~ (l1_pre_topc @ sk_B)
% 0.60/0.85          | ~ (v2_pre_topc @ sk_B)
% 0.60/0.85          | (v2_struct_0 @ sk_B))),
% 0.60/0.85      inference('sup-', [status(thm)], ['112', '113'])).
% 0.60/0.85  thf('115', plain,
% 0.60/0.85      ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.60/0.85        (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.60/0.85      inference('clc', [status(thm)], ['106', '107'])).
% 0.60/0.85  thf('116', plain,
% 0.60/0.85      ((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))),
% 0.60/0.85      inference('clc', [status(thm)], ['42', '43'])).
% 0.60/0.85  thf('117', plain,
% 0.60/0.85      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 0.60/0.85         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))),
% 0.60/0.85      inference('sup+', [status(thm)], ['66', '82'])).
% 0.60/0.85  thf('118', plain, ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))),
% 0.60/0.85      inference('demod', [status(thm)], ['116', '117'])).
% 0.60/0.85  thf('119', plain, ((l1_pre_topc @ sk_B)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('120', plain, ((v2_pre_topc @ sk_B)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('121', plain,
% 0.60/0.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.60/0.85         ((v2_struct_0 @ X0)
% 0.60/0.85          | ~ (v2_pre_topc @ X0)
% 0.60/0.85          | ~ (l1_pre_topc @ X0)
% 0.60/0.85          | (v2_struct_0 @ sk_D)
% 0.60/0.85          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.60/0.85          | ~ (v1_funct_1 @ X1)
% 0.60/0.85          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.60/0.85          | ~ (m1_subset_1 @ X1 @ 
% 0.60/0.85               (k1_zfmisc_1 @ 
% 0.60/0.85                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.60/0.85          | ~ (m1_pre_topc @ X2 @ sk_D)
% 0.60/0.85          | ~ (r2_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.85               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.60/0.85               (k2_tmap_1 @ X0 @ sk_B @ X1 @ sk_D))
% 0.60/0.85          | (r2_funct_2 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.85             (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X2 @ 
% 0.60/0.85              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.60/0.85             (k2_tmap_1 @ X0 @ sk_B @ X1 @ X2))
% 0.60/0.85          | ~ (m1_pre_topc @ X2 @ X0)
% 0.60/0.85          | (v2_struct_0 @ X2)
% 0.60/0.85          | (v2_struct_0 @ sk_B))),
% 0.60/0.85      inference('demod', [status(thm)], ['114', '115', '118', '119', '120'])).
% 0.60/0.85  thf('122', plain,
% 0.60/0.85      (![X0 : $i]:
% 0.60/0.85         ((v2_struct_0 @ sk_B)
% 0.60/0.85          | (v2_struct_0 @ X0)
% 0.60/0.85          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.60/0.85          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.85             (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ 
% 0.60/0.85              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.60/0.85             (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 0.60/0.85          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.60/0.85          | ~ (m1_subset_1 @ sk_E @ 
% 0.60/0.85               (k1_zfmisc_1 @ 
% 0.60/0.85                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.60/0.85          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.60/0.85          | ~ (v1_funct_1 @ sk_E)
% 0.60/0.85          | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.60/0.85          | (v2_struct_0 @ sk_D)
% 0.60/0.85          | ~ (l1_pre_topc @ sk_A)
% 0.60/0.85          | ~ (v2_pre_topc @ sk_A)
% 0.60/0.85          | (v2_struct_0 @ sk_A))),
% 0.60/0.85      inference('sup-', [status(thm)], ['109', '121'])).
% 0.60/0.85  thf('123', plain,
% 0.60/0.85      ((m1_subset_1 @ sk_E @ 
% 0.60/0.85        (k1_zfmisc_1 @ 
% 0.60/0.85         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('124', plain,
% 0.60/0.85      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('125', plain, ((v1_funct_1 @ sk_E)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('126', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('127', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('128', plain, ((v2_pre_topc @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('129', plain,
% 0.60/0.85      (![X0 : $i]:
% 0.60/0.85         ((v2_struct_0 @ sk_B)
% 0.60/0.85          | (v2_struct_0 @ X0)
% 0.60/0.85          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.60/0.85          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.85             (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ 
% 0.60/0.85              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.60/0.85             (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 0.60/0.85          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.60/0.85          | (v2_struct_0 @ sk_D)
% 0.60/0.85          | (v2_struct_0 @ sk_A))),
% 0.60/0.85      inference('demod', [status(thm)],
% 0.60/0.85                ['122', '123', '124', '125', '126', '127', '128'])).
% 0.60/0.85  thf('130', plain,
% 0.60/0.85      (((v2_struct_0 @ sk_A)
% 0.60/0.85        | (v2_struct_0 @ sk_D)
% 0.60/0.85        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.60/0.85        | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.85           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ 
% 0.60/0.85            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.60/0.85           (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C))
% 0.60/0.85        | (v2_struct_0 @ sk_C)
% 0.60/0.85        | (v2_struct_0 @ sk_B))),
% 0.60/0.85      inference('sup-', [status(thm)], ['1', '129'])).
% 0.60/0.85  thf('131', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('132', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('133', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('134', plain,
% 0.60/0.85      ((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E) @ 
% 0.60/0.85        (k1_zfmisc_1 @ 
% 0.60/0.85         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.60/0.85      inference('clc', [status(thm)], ['19', '20'])).
% 0.60/0.85  thf('135', plain,
% 0.60/0.85      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.60/0.85         ((v2_struct_0 @ X12)
% 0.60/0.85          | ~ (v2_pre_topc @ X12)
% 0.60/0.85          | ~ (l1_pre_topc @ X12)
% 0.60/0.85          | ~ (m1_pre_topc @ X13 @ X14)
% 0.60/0.85          | ~ (m1_pre_topc @ X13 @ X15)
% 0.60/0.85          | ((k3_tmap_1 @ X14 @ X12 @ X15 @ X13 @ X16)
% 0.60/0.85              = (k2_partfun1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X12) @ 
% 0.60/0.85                 X16 @ (u1_struct_0 @ X13)))
% 0.60/0.85          | ~ (m1_subset_1 @ X16 @ 
% 0.60/0.85               (k1_zfmisc_1 @ 
% 0.60/0.85                (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X12))))
% 0.60/0.85          | ~ (v1_funct_2 @ X16 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X12))
% 0.60/0.85          | ~ (v1_funct_1 @ X16)
% 0.60/0.85          | ~ (m1_pre_topc @ X15 @ X14)
% 0.60/0.85          | ~ (l1_pre_topc @ X14)
% 0.60/0.85          | ~ (v2_pre_topc @ X14)
% 0.60/0.85          | (v2_struct_0 @ X14))),
% 0.60/0.85      inference('cnf', [status(esa)], [d5_tmap_1])).
% 0.60/0.85  thf('136', plain,
% 0.60/0.85      (![X0 : $i, X1 : $i]:
% 0.60/0.85         ((v2_struct_0 @ X0)
% 0.60/0.85          | ~ (v2_pre_topc @ X0)
% 0.60/0.85          | ~ (l1_pre_topc @ X0)
% 0.60/0.85          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.60/0.85          | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))
% 0.60/0.85          | ~ (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E) @ 
% 0.60/0.85               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.60/0.85          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ 
% 0.60/0.85              (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))
% 0.60/0.85              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.85                 (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E) @ 
% 0.60/0.85                 (u1_struct_0 @ X1)))
% 0.60/0.85          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.60/0.85          | ~ (m1_pre_topc @ X1 @ X0)
% 0.60/0.85          | ~ (l1_pre_topc @ sk_B)
% 0.60/0.85          | ~ (v2_pre_topc @ sk_B)
% 0.60/0.85          | (v2_struct_0 @ sk_B))),
% 0.60/0.85      inference('sup-', [status(thm)], ['134', '135'])).
% 0.60/0.85  thf('137', plain,
% 0.60/0.85      ((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))),
% 0.60/0.85      inference('clc', [status(thm)], ['42', '43'])).
% 0.60/0.85  thf('138', plain, ((l1_pre_topc @ sk_B)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('139', plain, ((v2_pre_topc @ sk_B)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('140', plain,
% 0.60/0.85      (![X0 : $i, X1 : $i]:
% 0.60/0.85         ((v2_struct_0 @ X0)
% 0.60/0.85          | ~ (v2_pre_topc @ X0)
% 0.60/0.85          | ~ (l1_pre_topc @ X0)
% 0.60/0.85          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.60/0.85          | ~ (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E) @ 
% 0.60/0.85               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.60/0.85          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ 
% 0.60/0.85              (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))
% 0.60/0.85              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.85                 (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E) @ 
% 0.60/0.85                 (u1_struct_0 @ X1)))
% 0.60/0.85          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.60/0.85          | ~ (m1_pre_topc @ X1 @ X0)
% 0.60/0.85          | (v2_struct_0 @ sk_B))),
% 0.60/0.85      inference('demod', [status(thm)], ['136', '137', '138', '139'])).
% 0.60/0.85  thf('141', plain,
% 0.60/0.85      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 0.60/0.85         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))),
% 0.60/0.85      inference('sup+', [status(thm)], ['66', '82'])).
% 0.60/0.85  thf('142', plain,
% 0.60/0.85      ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.60/0.85        (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.60/0.85      inference('clc', [status(thm)], ['106', '107'])).
% 0.60/0.85  thf('143', plain,
% 0.60/0.85      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 0.60/0.85         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))),
% 0.60/0.85      inference('sup+', [status(thm)], ['66', '82'])).
% 0.60/0.85  thf('144', plain,
% 0.60/0.85      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 0.60/0.85         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))),
% 0.60/0.85      inference('sup+', [status(thm)], ['66', '82'])).
% 0.60/0.85  thf('145', plain,
% 0.60/0.85      (![X0 : $i, X1 : $i]:
% 0.60/0.85         ((v2_struct_0 @ X0)
% 0.60/0.85          | ~ (v2_pre_topc @ X0)
% 0.60/0.85          | ~ (l1_pre_topc @ X0)
% 0.60/0.85          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.60/0.85          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ 
% 0.60/0.85              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))
% 0.60/0.85              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.85                 (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ (u1_struct_0 @ X1)))
% 0.60/0.85          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.60/0.85          | ~ (m1_pre_topc @ X1 @ X0)
% 0.60/0.85          | (v2_struct_0 @ sk_B))),
% 0.60/0.85      inference('demod', [status(thm)], ['140', '141', '142', '143', '144'])).
% 0.60/0.85  thf('146', plain,
% 0.60/0.85      (![X0 : $i]:
% 0.60/0.85         ((v2_struct_0 @ sk_B)
% 0.60/0.85          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.60/0.85          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.60/0.85          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ 
% 0.60/0.85              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))
% 0.60/0.85              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.85                 (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ (u1_struct_0 @ X0)))
% 0.60/0.85          | ~ (l1_pre_topc @ sk_A)
% 0.60/0.85          | ~ (v2_pre_topc @ sk_A)
% 0.60/0.85          | (v2_struct_0 @ sk_A))),
% 0.60/0.85      inference('sup-', [status(thm)], ['133', '145'])).
% 0.60/0.85  thf('147', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('148', plain, ((v2_pre_topc @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('149', plain,
% 0.60/0.85      (![X0 : $i]:
% 0.60/0.85         ((v2_struct_0 @ sk_B)
% 0.60/0.85          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.60/0.85          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.60/0.85          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ 
% 0.60/0.85              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))
% 0.60/0.85              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.85                 (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ (u1_struct_0 @ X0)))
% 0.60/0.85          | (v2_struct_0 @ sk_A))),
% 0.60/0.85      inference('demod', [status(thm)], ['146', '147', '148'])).
% 0.60/0.85  thf('150', plain,
% 0.60/0.85      (((v2_struct_0 @ sk_A)
% 0.60/0.85        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ 
% 0.60/0.85            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))
% 0.60/0.85            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.85               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ (u1_struct_0 @ sk_C)))
% 0.60/0.85        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.60/0.85        | (v2_struct_0 @ sk_B))),
% 0.60/0.85      inference('sup-', [status(thm)], ['132', '149'])).
% 0.60/0.85  thf('151', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('152', plain,
% 0.60/0.85      ((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E) @ 
% 0.60/0.85        (k1_zfmisc_1 @ 
% 0.60/0.85         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.60/0.85      inference('clc', [status(thm)], ['19', '20'])).
% 0.60/0.85  thf('153', plain,
% 0.60/0.85      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.60/0.85         ((v2_struct_0 @ X8)
% 0.60/0.85          | ~ (v2_pre_topc @ X8)
% 0.60/0.85          | ~ (l1_pre_topc @ X8)
% 0.60/0.85          | ~ (m1_pre_topc @ X9 @ X10)
% 0.60/0.85          | ((k2_tmap_1 @ X10 @ X8 @ X11 @ X9)
% 0.60/0.85              = (k2_partfun1 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X8) @ 
% 0.60/0.85                 X11 @ (u1_struct_0 @ X9)))
% 0.60/0.85          | ~ (m1_subset_1 @ X11 @ 
% 0.60/0.85               (k1_zfmisc_1 @ 
% 0.60/0.85                (k2_zfmisc_1 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X8))))
% 0.60/0.85          | ~ (v1_funct_2 @ X11 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X8))
% 0.60/0.85          | ~ (v1_funct_1 @ X11)
% 0.60/0.85          | ~ (l1_pre_topc @ X10)
% 0.60/0.85          | ~ (v2_pre_topc @ X10)
% 0.60/0.85          | (v2_struct_0 @ X10))),
% 0.60/0.85      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.60/0.85  thf('154', plain,
% 0.60/0.85      (![X0 : $i]:
% 0.60/0.85         ((v2_struct_0 @ sk_D)
% 0.60/0.85          | ~ (v2_pre_topc @ sk_D)
% 0.60/0.85          | ~ (l1_pre_topc @ sk_D)
% 0.60/0.85          | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))
% 0.60/0.85          | ~ (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E) @ 
% 0.60/0.85               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.60/0.85          | ((k2_tmap_1 @ sk_D @ sk_B @ 
% 0.60/0.85              (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E) @ X0)
% 0.60/0.85              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.85                 (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E) @ 
% 0.60/0.85                 (u1_struct_0 @ X0)))
% 0.60/0.85          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.60/0.85          | ~ (l1_pre_topc @ sk_B)
% 0.60/0.85          | ~ (v2_pre_topc @ sk_B)
% 0.60/0.85          | (v2_struct_0 @ sk_B))),
% 0.60/0.85      inference('sup-', [status(thm)], ['152', '153'])).
% 0.60/0.85  thf('155', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf(cc1_pre_topc, axiom,
% 0.60/0.85    (![A:$i]:
% 0.60/0.85     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.60/0.85       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.60/0.85  thf('156', plain,
% 0.60/0.85      (![X4 : $i, X5 : $i]:
% 0.60/0.85         (~ (m1_pre_topc @ X4 @ X5)
% 0.60/0.85          | (v2_pre_topc @ X4)
% 0.60/0.85          | ~ (l1_pre_topc @ X5)
% 0.60/0.85          | ~ (v2_pre_topc @ X5))),
% 0.60/0.85      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.60/0.85  thf('157', plain,
% 0.60/0.85      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_D))),
% 0.60/0.85      inference('sup-', [status(thm)], ['155', '156'])).
% 0.60/0.85  thf('158', plain, ((v2_pre_topc @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('159', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('160', plain, ((v2_pre_topc @ sk_D)),
% 0.60/0.85      inference('demod', [status(thm)], ['157', '158', '159'])).
% 0.60/0.85  thf('161', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf(dt_m1_pre_topc, axiom,
% 0.60/0.85    (![A:$i]:
% 0.60/0.85     ( ( l1_pre_topc @ A ) =>
% 0.60/0.85       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.60/0.85  thf('162', plain,
% 0.60/0.85      (![X6 : $i, X7 : $i]:
% 0.60/0.85         (~ (m1_pre_topc @ X6 @ X7) | (l1_pre_topc @ X6) | ~ (l1_pre_topc @ X7))),
% 0.60/0.85      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.60/0.85  thf('163', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 0.60/0.85      inference('sup-', [status(thm)], ['161', '162'])).
% 0.60/0.85  thf('164', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('165', plain, ((l1_pre_topc @ sk_D)),
% 0.60/0.85      inference('demod', [status(thm)], ['163', '164'])).
% 0.60/0.85  thf('166', plain,
% 0.60/0.85      ((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))),
% 0.60/0.85      inference('clc', [status(thm)], ['42', '43'])).
% 0.60/0.85  thf('167', plain, ((l1_pre_topc @ sk_B)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('168', plain, ((v2_pre_topc @ sk_B)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('169', plain,
% 0.60/0.85      (![X0 : $i]:
% 0.60/0.85         ((v2_struct_0 @ sk_D)
% 0.60/0.85          | ~ (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E) @ 
% 0.60/0.85               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.60/0.85          | ((k2_tmap_1 @ sk_D @ sk_B @ 
% 0.60/0.85              (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E) @ X0)
% 0.60/0.85              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.85                 (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E) @ 
% 0.60/0.85                 (u1_struct_0 @ X0)))
% 0.60/0.85          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.60/0.85          | (v2_struct_0 @ sk_B))),
% 0.60/0.85      inference('demod', [status(thm)],
% 0.60/0.85                ['154', '160', '165', '166', '167', '168'])).
% 0.60/0.85  thf('170', plain,
% 0.60/0.85      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 0.60/0.85         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))),
% 0.60/0.85      inference('sup+', [status(thm)], ['66', '82'])).
% 0.60/0.85  thf('171', plain,
% 0.60/0.85      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 0.60/0.85         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))),
% 0.60/0.85      inference('sup+', [status(thm)], ['66', '82'])).
% 0.60/0.85  thf('172', plain,
% 0.60/0.85      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 0.60/0.85         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))),
% 0.60/0.85      inference('sup+', [status(thm)], ['66', '82'])).
% 0.60/0.85  thf('173', plain,
% 0.60/0.85      (![X0 : $i]:
% 0.60/0.85         ((v2_struct_0 @ sk_D)
% 0.60/0.85          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.60/0.85               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.60/0.85          | ((k2_tmap_1 @ sk_D @ sk_B @ 
% 0.60/0.85              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ X0)
% 0.60/0.85              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.85                 (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ (u1_struct_0 @ X0)))
% 0.60/0.85          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.60/0.85          | (v2_struct_0 @ sk_B))),
% 0.60/0.85      inference('demod', [status(thm)], ['169', '170', '171', '172'])).
% 0.60/0.85  thf('174', plain,
% 0.60/0.85      ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.60/0.85        (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.60/0.85      inference('clc', [status(thm)], ['106', '107'])).
% 0.60/0.85  thf('175', plain,
% 0.60/0.85      (![X0 : $i]:
% 0.60/0.85         ((v2_struct_0 @ sk_D)
% 0.60/0.85          | ((k2_tmap_1 @ sk_D @ sk_B @ 
% 0.60/0.85              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ X0)
% 0.60/0.85              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.85                 (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ (u1_struct_0 @ X0)))
% 0.60/0.85          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.60/0.85          | (v2_struct_0 @ sk_B))),
% 0.60/0.85      inference('demod', [status(thm)], ['173', '174'])).
% 0.60/0.85  thf('176', plain,
% 0.60/0.85      (((v2_struct_0 @ sk_B)
% 0.60/0.85        | ((k2_tmap_1 @ sk_D @ sk_B @ 
% 0.60/0.85            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ sk_C)
% 0.60/0.85            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.85               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ (u1_struct_0 @ sk_C)))
% 0.60/0.85        | (v2_struct_0 @ sk_D))),
% 0.60/0.85      inference('sup-', [status(thm)], ['151', '175'])).
% 0.60/0.85  thf('177', plain, (~ (v2_struct_0 @ sk_B)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('178', plain,
% 0.60/0.85      (((v2_struct_0 @ sk_D)
% 0.60/0.85        | ((k2_tmap_1 @ sk_D @ sk_B @ 
% 0.60/0.85            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ sk_C)
% 0.60/0.85            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.85               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ (u1_struct_0 @ sk_C))))),
% 0.60/0.85      inference('clc', [status(thm)], ['176', '177'])).
% 0.60/0.85  thf('179', plain, (~ (v2_struct_0 @ sk_D)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('180', plain,
% 0.60/0.85      (((k2_tmap_1 @ sk_D @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.60/0.85         sk_C)
% 0.60/0.85         = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.85            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ (u1_struct_0 @ sk_C)))),
% 0.60/0.85      inference('clc', [status(thm)], ['178', '179'])).
% 0.60/0.85  thf('181', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('182', plain,
% 0.60/0.85      (((v2_struct_0 @ sk_A)
% 0.60/0.85        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ 
% 0.60/0.85            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))
% 0.60/0.85            = (k2_tmap_1 @ sk_D @ sk_B @ 
% 0.60/0.85               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ sk_C))
% 0.60/0.85        | (v2_struct_0 @ sk_B))),
% 0.60/0.85      inference('demod', [status(thm)], ['150', '180', '181'])).
% 0.60/0.85  thf('183', plain, (~ (v2_struct_0 @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('184', plain,
% 0.60/0.85      (((v2_struct_0 @ sk_B)
% 0.60/0.85        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ 
% 0.60/0.85            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))
% 0.60/0.85            = (k2_tmap_1 @ sk_D @ sk_B @ 
% 0.60/0.85               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ sk_C)))),
% 0.60/0.85      inference('clc', [status(thm)], ['182', '183'])).
% 0.60/0.85  thf('185', plain, (~ (v2_struct_0 @ sk_B)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('186', plain,
% 0.60/0.85      (((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ 
% 0.60/0.85         (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))
% 0.60/0.85         = (k2_tmap_1 @ sk_D @ sk_B @ 
% 0.60/0.85            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ sk_C))),
% 0.60/0.85      inference('clc', [status(thm)], ['184', '185'])).
% 0.60/0.85  thf('187', plain,
% 0.60/0.85      (((v2_struct_0 @ sk_A)
% 0.60/0.85        | (v2_struct_0 @ sk_D)
% 0.60/0.85        | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.85           (k2_tmap_1 @ sk_D @ sk_B @ 
% 0.60/0.85            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ sk_C) @ 
% 0.60/0.85           (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C))
% 0.60/0.85        | (v2_struct_0 @ sk_C)
% 0.60/0.85        | (v2_struct_0 @ sk_B))),
% 0.60/0.85      inference('demod', [status(thm)], ['130', '131', '186'])).
% 0.60/0.85  thf('188', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('189', plain,
% 0.60/0.85      (![X22 : $i]: ((m1_pre_topc @ X22 @ X22) | ~ (l1_pre_topc @ X22))),
% 0.60/0.85      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.60/0.85  thf('190', plain,
% 0.60/0.85      ((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E) @ 
% 0.60/0.85        (k1_zfmisc_1 @ 
% 0.60/0.85         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.60/0.85      inference('clc', [status(thm)], ['19', '20'])).
% 0.60/0.85  thf('191', plain,
% 0.60/0.85      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.60/0.85         (~ (m1_pre_topc @ X17 @ X18)
% 0.60/0.85          | ~ (m1_pre_topc @ X19 @ X18)
% 0.60/0.85          | ~ (l1_pre_topc @ X20)
% 0.60/0.85          | ~ (v2_pre_topc @ X20)
% 0.60/0.85          | (v2_struct_0 @ X20)
% 0.60/0.85          | ~ (l1_pre_topc @ X18)
% 0.60/0.85          | ~ (v2_pre_topc @ X18)
% 0.60/0.85          | (v2_struct_0 @ X18)
% 0.60/0.85          | ~ (v1_funct_1 @ X21)
% 0.60/0.85          | ~ (v1_funct_2 @ X21 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X20))
% 0.60/0.85          | ~ (m1_subset_1 @ X21 @ 
% 0.60/0.85               (k1_zfmisc_1 @ 
% 0.60/0.85                (k2_zfmisc_1 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X20))))
% 0.60/0.85          | (m1_subset_1 @ (k3_tmap_1 @ X18 @ X20 @ X19 @ X17 @ X21) @ 
% 0.60/0.85             (k1_zfmisc_1 @ 
% 0.60/0.85              (k2_zfmisc_1 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X20)))))),
% 0.60/0.85      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 0.60/0.85  thf('192', plain,
% 0.60/0.85      (![X0 : $i, X1 : $i]:
% 0.60/0.85         ((m1_subset_1 @ 
% 0.60/0.85           (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ 
% 0.60/0.85            (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E)) @ 
% 0.60/0.85           (k1_zfmisc_1 @ 
% 0.60/0.85            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.60/0.85          | ~ (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E) @ 
% 0.60/0.85               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.60/0.85          | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))
% 0.60/0.85          | (v2_struct_0 @ X1)
% 0.60/0.85          | ~ (v2_pre_topc @ X1)
% 0.60/0.85          | ~ (l1_pre_topc @ X1)
% 0.60/0.85          | (v2_struct_0 @ sk_B)
% 0.60/0.85          | ~ (v2_pre_topc @ sk_B)
% 0.60/0.85          | ~ (l1_pre_topc @ sk_B)
% 0.60/0.85          | ~ (m1_pre_topc @ sk_D @ X1)
% 0.60/0.85          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.60/0.85      inference('sup-', [status(thm)], ['190', '191'])).
% 0.60/0.85  thf('193', plain,
% 0.60/0.85      ((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))),
% 0.60/0.85      inference('clc', [status(thm)], ['42', '43'])).
% 0.60/0.85  thf('194', plain, ((v2_pre_topc @ sk_B)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('195', plain, ((l1_pre_topc @ sk_B)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('196', plain,
% 0.60/0.85      (![X0 : $i, X1 : $i]:
% 0.60/0.85         ((m1_subset_1 @ 
% 0.60/0.85           (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ 
% 0.60/0.85            (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E)) @ 
% 0.60/0.85           (k1_zfmisc_1 @ 
% 0.60/0.85            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.60/0.85          | ~ (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E) @ 
% 0.60/0.85               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.60/0.85          | (v2_struct_0 @ X1)
% 0.60/0.85          | ~ (v2_pre_topc @ X1)
% 0.60/0.85          | ~ (l1_pre_topc @ X1)
% 0.60/0.85          | (v2_struct_0 @ sk_B)
% 0.60/0.85          | ~ (m1_pre_topc @ sk_D @ X1)
% 0.60/0.85          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.60/0.85      inference('demod', [status(thm)], ['192', '193', '194', '195'])).
% 0.60/0.85  thf('197', plain,
% 0.60/0.85      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 0.60/0.85         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))),
% 0.60/0.85      inference('sup+', [status(thm)], ['66', '82'])).
% 0.60/0.85  thf('198', plain,
% 0.60/0.85      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 0.60/0.85         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))),
% 0.60/0.85      inference('sup+', [status(thm)], ['66', '82'])).
% 0.60/0.85  thf('199', plain,
% 0.60/0.85      ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.60/0.85        (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.60/0.85      inference('clc', [status(thm)], ['106', '107'])).
% 0.60/0.85  thf('200', plain,
% 0.60/0.85      (![X0 : $i, X1 : $i]:
% 0.60/0.85         ((m1_subset_1 @ 
% 0.60/0.85           (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ 
% 0.60/0.85            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.60/0.85           (k1_zfmisc_1 @ 
% 0.60/0.85            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.60/0.85          | (v2_struct_0 @ X1)
% 0.60/0.85          | ~ (v2_pre_topc @ X1)
% 0.60/0.85          | ~ (l1_pre_topc @ X1)
% 0.60/0.85          | (v2_struct_0 @ sk_B)
% 0.60/0.85          | ~ (m1_pre_topc @ sk_D @ X1)
% 0.60/0.85          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.60/0.85      inference('demod', [status(thm)], ['196', '197', '198', '199'])).
% 0.60/0.85  thf('201', plain,
% 0.60/0.85      (![X0 : $i]:
% 0.60/0.85         (~ (l1_pre_topc @ sk_D)
% 0.60/0.85          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.60/0.85          | (v2_struct_0 @ sk_B)
% 0.60/0.85          | ~ (l1_pre_topc @ sk_D)
% 0.60/0.85          | ~ (v2_pre_topc @ sk_D)
% 0.60/0.85          | (v2_struct_0 @ sk_D)
% 0.60/0.85          | (m1_subset_1 @ 
% 0.60/0.85             (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ 
% 0.60/0.85              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.60/0.85             (k1_zfmisc_1 @ 
% 0.60/0.85              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))))),
% 0.60/0.85      inference('sup-', [status(thm)], ['189', '200'])).
% 0.60/0.85  thf('202', plain, ((l1_pre_topc @ sk_D)),
% 0.60/0.85      inference('demod', [status(thm)], ['163', '164'])).
% 0.60/0.85  thf('203', plain, ((l1_pre_topc @ sk_D)),
% 0.60/0.85      inference('demod', [status(thm)], ['163', '164'])).
% 0.60/0.85  thf('204', plain, ((v2_pre_topc @ sk_D)),
% 0.60/0.85      inference('demod', [status(thm)], ['157', '158', '159'])).
% 0.60/0.85  thf('205', plain,
% 0.60/0.85      (![X0 : $i]:
% 0.60/0.85         (~ (m1_pre_topc @ X0 @ sk_D)
% 0.60/0.85          | (v2_struct_0 @ sk_B)
% 0.60/0.85          | (v2_struct_0 @ sk_D)
% 0.60/0.85          | (m1_subset_1 @ 
% 0.60/0.85             (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ 
% 0.60/0.85              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.60/0.85             (k1_zfmisc_1 @ 
% 0.60/0.85              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))))),
% 0.60/0.85      inference('demod', [status(thm)], ['201', '202', '203', '204'])).
% 0.60/0.85  thf('206', plain,
% 0.60/0.85      (((m1_subset_1 @ 
% 0.60/0.85         (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ 
% 0.60/0.85          (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.60/0.85         (k1_zfmisc_1 @ 
% 0.60/0.85          (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 0.60/0.85        | (v2_struct_0 @ sk_D)
% 0.60/0.85        | (v2_struct_0 @ sk_B))),
% 0.60/0.85      inference('sup-', [status(thm)], ['188', '205'])).
% 0.60/0.85  thf('207', plain, (~ (v2_struct_0 @ sk_D)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('208', plain,
% 0.60/0.85      (((v2_struct_0 @ sk_B)
% 0.60/0.85        | (m1_subset_1 @ 
% 0.60/0.85           (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ 
% 0.60/0.85            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.60/0.85           (k1_zfmisc_1 @ 
% 0.60/0.85            (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))))),
% 0.60/0.85      inference('clc', [status(thm)], ['206', '207'])).
% 0.60/0.85  thf('209', plain, (~ (v2_struct_0 @ sk_B)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('210', plain,
% 0.60/0.85      ((m1_subset_1 @ 
% 0.60/0.85        (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ 
% 0.60/0.85         (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.60/0.85        (k1_zfmisc_1 @ 
% 0.60/0.85         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.60/0.85      inference('clc', [status(thm)], ['208', '209'])).
% 0.60/0.85  thf('211', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('212', plain,
% 0.60/0.85      (![X22 : $i]: ((m1_pre_topc @ X22 @ X22) | ~ (l1_pre_topc @ X22))),
% 0.60/0.85      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.60/0.85  thf('213', plain,
% 0.60/0.85      (![X0 : $i, X1 : $i]:
% 0.60/0.85         ((v2_struct_0 @ X0)
% 0.60/0.85          | ~ (v2_pre_topc @ X0)
% 0.60/0.85          | ~ (l1_pre_topc @ X0)
% 0.60/0.85          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.60/0.85          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ 
% 0.60/0.85              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))
% 0.60/0.85              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.85                 (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ (u1_struct_0 @ X1)))
% 0.60/0.85          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.60/0.85          | ~ (m1_pre_topc @ X1 @ X0)
% 0.60/0.85          | (v2_struct_0 @ sk_B))),
% 0.60/0.85      inference('demod', [status(thm)], ['140', '141', '142', '143', '144'])).
% 0.60/0.85  thf('214', plain,
% 0.60/0.85      (![X0 : $i]:
% 0.60/0.85         (~ (l1_pre_topc @ sk_D)
% 0.60/0.85          | (v2_struct_0 @ sk_B)
% 0.60/0.85          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.60/0.85          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.60/0.85          | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ 
% 0.60/0.85              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))
% 0.60/0.85              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.85                 (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ (u1_struct_0 @ X0)))
% 0.60/0.85          | ~ (l1_pre_topc @ sk_D)
% 0.60/0.85          | ~ (v2_pre_topc @ sk_D)
% 0.60/0.85          | (v2_struct_0 @ sk_D))),
% 0.60/0.85      inference('sup-', [status(thm)], ['212', '213'])).
% 0.60/0.85  thf('215', plain, ((l1_pre_topc @ sk_D)),
% 0.60/0.85      inference('demod', [status(thm)], ['163', '164'])).
% 0.60/0.85  thf('216', plain, ((l1_pre_topc @ sk_D)),
% 0.60/0.85      inference('demod', [status(thm)], ['163', '164'])).
% 0.60/0.85  thf('217', plain, ((v2_pre_topc @ sk_D)),
% 0.60/0.85      inference('demod', [status(thm)], ['157', '158', '159'])).
% 0.60/0.85  thf('218', plain,
% 0.60/0.85      (![X0 : $i]:
% 0.60/0.85         ((v2_struct_0 @ sk_B)
% 0.60/0.85          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.60/0.85          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.60/0.85          | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ 
% 0.60/0.85              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))
% 0.60/0.85              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.85                 (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ (u1_struct_0 @ X0)))
% 0.60/0.85          | (v2_struct_0 @ sk_D))),
% 0.60/0.85      inference('demod', [status(thm)], ['214', '215', '216', '217'])).
% 0.60/0.85  thf('219', plain,
% 0.60/0.85      (![X0 : $i]:
% 0.60/0.85         ((v2_struct_0 @ sk_D)
% 0.60/0.85          | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ 
% 0.60/0.85              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))
% 0.60/0.85              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.85                 (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ (u1_struct_0 @ X0)))
% 0.60/0.85          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.60/0.85          | (v2_struct_0 @ sk_B))),
% 0.60/0.85      inference('simplify', [status(thm)], ['218'])).
% 0.60/0.85  thf('220', plain,
% 0.60/0.85      (((v2_struct_0 @ sk_B)
% 0.60/0.85        | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ 
% 0.60/0.85            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))
% 0.60/0.85            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.85               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ (u1_struct_0 @ sk_C)))
% 0.60/0.85        | (v2_struct_0 @ sk_D))),
% 0.60/0.85      inference('sup-', [status(thm)], ['211', '219'])).
% 0.60/0.85  thf('221', plain, (~ (v2_struct_0 @ sk_B)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('222', plain,
% 0.60/0.85      (((v2_struct_0 @ sk_D)
% 0.60/0.85        | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ 
% 0.60/0.85            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))
% 0.60/0.85            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.85               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ (u1_struct_0 @ sk_C))))),
% 0.60/0.85      inference('clc', [status(thm)], ['220', '221'])).
% 0.60/0.85  thf('223', plain, (~ (v2_struct_0 @ sk_D)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('224', plain,
% 0.60/0.85      (((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ 
% 0.60/0.85         (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))
% 0.60/0.85         = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.85            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ (u1_struct_0 @ sk_C)))),
% 0.60/0.85      inference('clc', [status(thm)], ['222', '223'])).
% 0.60/0.85  thf('225', plain,
% 0.60/0.85      (((k2_tmap_1 @ sk_D @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.60/0.85         sk_C)
% 0.60/0.85         = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.85            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ (u1_struct_0 @ sk_C)))),
% 0.60/0.85      inference('clc', [status(thm)], ['178', '179'])).
% 0.60/0.85  thf('226', plain,
% 0.60/0.85      (((k2_tmap_1 @ sk_D @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.60/0.85         sk_C)
% 0.60/0.85         = (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ 
% 0.60/0.85            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)))),
% 0.60/0.85      inference('sup+', [status(thm)], ['224', '225'])).
% 0.60/0.85  thf('227', plain,
% 0.60/0.85      ((m1_subset_1 @ 
% 0.60/0.85        (k2_tmap_1 @ sk_D @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.60/0.85         sk_C) @ 
% 0.60/0.85        (k1_zfmisc_1 @ 
% 0.60/0.85         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.60/0.85      inference('demod', [status(thm)], ['210', '226'])).
% 0.60/0.85  thf('228', plain,
% 0.60/0.85      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.60/0.85         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 0.60/0.85          | ~ (v1_funct_2 @ X0 @ X1 @ X2)
% 0.60/0.85          | ~ (v1_funct_1 @ X0)
% 0.60/0.85          | ~ (v1_funct_1 @ X3)
% 0.60/0.85          | ~ (v1_funct_2 @ X3 @ X1 @ X2)
% 0.60/0.85          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 0.60/0.85          | ((X0) = (X3))
% 0.60/0.85          | ~ (r2_funct_2 @ X1 @ X2 @ X0 @ X3))),
% 0.60/0.85      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 0.60/0.85  thf('229', plain,
% 0.60/0.85      (![X0 : $i]:
% 0.60/0.85         (~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.85             (k2_tmap_1 @ sk_D @ sk_B @ 
% 0.60/0.85              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ sk_C) @ 
% 0.60/0.85             X0)
% 0.60/0.85          | ((k2_tmap_1 @ sk_D @ sk_B @ 
% 0.60/0.85              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ sk_C) = (X0))
% 0.60/0.85          | ~ (m1_subset_1 @ X0 @ 
% 0.60/0.85               (k1_zfmisc_1 @ 
% 0.60/0.85                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 0.60/0.85          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.60/0.85          | ~ (v1_funct_1 @ X0)
% 0.60/0.85          | ~ (v1_funct_1 @ 
% 0.60/0.85               (k2_tmap_1 @ sk_D @ sk_B @ 
% 0.60/0.85                (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ sk_C))
% 0.60/0.85          | ~ (v1_funct_2 @ 
% 0.60/0.85               (k2_tmap_1 @ sk_D @ sk_B @ 
% 0.60/0.85                (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ sk_C) @ 
% 0.60/0.85               (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 0.60/0.85      inference('sup-', [status(thm)], ['227', '228'])).
% 0.60/0.85  thf('230', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('231', plain,
% 0.60/0.85      (![X22 : $i]: ((m1_pre_topc @ X22 @ X22) | ~ (l1_pre_topc @ X22))),
% 0.60/0.85      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.60/0.85  thf('232', plain,
% 0.60/0.85      ((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E) @ 
% 0.60/0.85        (k1_zfmisc_1 @ 
% 0.60/0.85         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.60/0.85      inference('clc', [status(thm)], ['19', '20'])).
% 0.60/0.85  thf('233', plain,
% 0.60/0.85      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.60/0.85         (~ (m1_pre_topc @ X17 @ X18)
% 0.60/0.85          | ~ (m1_pre_topc @ X19 @ X18)
% 0.60/0.85          | ~ (l1_pre_topc @ X20)
% 0.60/0.85          | ~ (v2_pre_topc @ X20)
% 0.60/0.85          | (v2_struct_0 @ X20)
% 0.60/0.85          | ~ (l1_pre_topc @ X18)
% 0.60/0.85          | ~ (v2_pre_topc @ X18)
% 0.60/0.85          | (v2_struct_0 @ X18)
% 0.60/0.85          | ~ (v1_funct_1 @ X21)
% 0.60/0.85          | ~ (v1_funct_2 @ X21 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X20))
% 0.60/0.85          | ~ (m1_subset_1 @ X21 @ 
% 0.60/0.85               (k1_zfmisc_1 @ 
% 0.60/0.85                (k2_zfmisc_1 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X20))))
% 0.60/0.85          | (v1_funct_1 @ (k3_tmap_1 @ X18 @ X20 @ X19 @ X17 @ X21)))),
% 0.60/0.85      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 0.60/0.85  thf('234', plain,
% 0.60/0.85      (![X0 : $i, X1 : $i]:
% 0.60/0.85         ((v1_funct_1 @ 
% 0.60/0.85           (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ 
% 0.60/0.85            (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E)))
% 0.60/0.85          | ~ (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E) @ 
% 0.60/0.85               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.60/0.85          | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))
% 0.60/0.85          | (v2_struct_0 @ X1)
% 0.60/0.85          | ~ (v2_pre_topc @ X1)
% 0.60/0.85          | ~ (l1_pre_topc @ X1)
% 0.60/0.85          | (v2_struct_0 @ sk_B)
% 0.60/0.85          | ~ (v2_pre_topc @ sk_B)
% 0.60/0.85          | ~ (l1_pre_topc @ sk_B)
% 0.60/0.85          | ~ (m1_pre_topc @ sk_D @ X1)
% 0.60/0.85          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.60/0.85      inference('sup-', [status(thm)], ['232', '233'])).
% 0.60/0.85  thf('235', plain,
% 0.60/0.85      ((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))),
% 0.60/0.85      inference('clc', [status(thm)], ['42', '43'])).
% 0.60/0.85  thf('236', plain, ((v2_pre_topc @ sk_B)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('237', plain, ((l1_pre_topc @ sk_B)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('238', plain,
% 0.60/0.85      (![X0 : $i, X1 : $i]:
% 0.60/0.85         ((v1_funct_1 @ 
% 0.60/0.85           (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ 
% 0.60/0.85            (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E)))
% 0.60/0.85          | ~ (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E) @ 
% 0.60/0.85               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.60/0.85          | (v2_struct_0 @ X1)
% 0.60/0.85          | ~ (v2_pre_topc @ X1)
% 0.60/0.85          | ~ (l1_pre_topc @ X1)
% 0.60/0.85          | (v2_struct_0 @ sk_B)
% 0.60/0.85          | ~ (m1_pre_topc @ sk_D @ X1)
% 0.60/0.85          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.60/0.85      inference('demod', [status(thm)], ['234', '235', '236', '237'])).
% 0.60/0.85  thf('239', plain,
% 0.60/0.85      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 0.60/0.85         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))),
% 0.60/0.85      inference('sup+', [status(thm)], ['66', '82'])).
% 0.60/0.85  thf('240', plain,
% 0.60/0.85      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 0.60/0.85         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))),
% 0.60/0.85      inference('sup+', [status(thm)], ['66', '82'])).
% 0.60/0.85  thf('241', plain,
% 0.60/0.85      (![X0 : $i, X1 : $i]:
% 0.60/0.85         ((v1_funct_1 @ 
% 0.60/0.85           (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ 
% 0.60/0.85            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)))
% 0.60/0.85          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.60/0.85               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.60/0.85          | (v2_struct_0 @ X1)
% 0.60/0.85          | ~ (v2_pre_topc @ X1)
% 0.60/0.85          | ~ (l1_pre_topc @ X1)
% 0.60/0.85          | (v2_struct_0 @ sk_B)
% 0.60/0.85          | ~ (m1_pre_topc @ sk_D @ X1)
% 0.60/0.85          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.60/0.85      inference('demod', [status(thm)], ['238', '239', '240'])).
% 0.60/0.85  thf('242', plain,
% 0.60/0.85      ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.60/0.85        (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.60/0.85      inference('clc', [status(thm)], ['106', '107'])).
% 0.60/0.85  thf('243', plain,
% 0.60/0.85      (![X0 : $i, X1 : $i]:
% 0.60/0.85         ((v1_funct_1 @ 
% 0.60/0.85           (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ 
% 0.60/0.85            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)))
% 0.60/0.85          | (v2_struct_0 @ X1)
% 0.60/0.85          | ~ (v2_pre_topc @ X1)
% 0.60/0.85          | ~ (l1_pre_topc @ X1)
% 0.60/0.85          | (v2_struct_0 @ sk_B)
% 0.60/0.85          | ~ (m1_pre_topc @ sk_D @ X1)
% 0.60/0.85          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.60/0.85      inference('demod', [status(thm)], ['241', '242'])).
% 0.60/0.85  thf('244', plain,
% 0.60/0.85      (![X0 : $i]:
% 0.60/0.85         (~ (l1_pre_topc @ sk_D)
% 0.60/0.85          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.60/0.85          | (v2_struct_0 @ sk_B)
% 0.60/0.85          | ~ (l1_pre_topc @ sk_D)
% 0.60/0.85          | ~ (v2_pre_topc @ sk_D)
% 0.60/0.85          | (v2_struct_0 @ sk_D)
% 0.60/0.85          | (v1_funct_1 @ 
% 0.60/0.85             (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ 
% 0.60/0.85              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))))),
% 0.60/0.85      inference('sup-', [status(thm)], ['231', '243'])).
% 0.60/0.85  thf('245', plain, ((l1_pre_topc @ sk_D)),
% 0.60/0.85      inference('demod', [status(thm)], ['163', '164'])).
% 0.60/0.85  thf('246', plain, ((l1_pre_topc @ sk_D)),
% 0.60/0.85      inference('demod', [status(thm)], ['163', '164'])).
% 0.60/0.85  thf('247', plain, ((v2_pre_topc @ sk_D)),
% 0.60/0.85      inference('demod', [status(thm)], ['157', '158', '159'])).
% 0.60/0.85  thf('248', plain,
% 0.60/0.85      (![X0 : $i]:
% 0.60/0.85         (~ (m1_pre_topc @ X0 @ sk_D)
% 0.60/0.85          | (v2_struct_0 @ sk_B)
% 0.60/0.85          | (v2_struct_0 @ sk_D)
% 0.60/0.85          | (v1_funct_1 @ 
% 0.60/0.85             (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ 
% 0.60/0.85              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))))),
% 0.60/0.85      inference('demod', [status(thm)], ['244', '245', '246', '247'])).
% 0.60/0.85  thf('249', plain,
% 0.60/0.85      (((v1_funct_1 @ 
% 0.60/0.85         (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ 
% 0.60/0.85          (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)))
% 0.60/0.85        | (v2_struct_0 @ sk_D)
% 0.60/0.85        | (v2_struct_0 @ sk_B))),
% 0.60/0.85      inference('sup-', [status(thm)], ['230', '248'])).
% 0.60/0.85  thf('250', plain, (~ (v2_struct_0 @ sk_D)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('251', plain,
% 0.60/0.85      (((v2_struct_0 @ sk_B)
% 0.60/0.85        | (v1_funct_1 @ 
% 0.60/0.85           (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ 
% 0.60/0.85            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))))),
% 0.60/0.85      inference('clc', [status(thm)], ['249', '250'])).
% 0.60/0.85  thf('252', plain, (~ (v2_struct_0 @ sk_B)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('253', plain,
% 0.60/0.85      ((v1_funct_1 @ 
% 0.60/0.85        (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ 
% 0.60/0.85         (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)))),
% 0.60/0.85      inference('clc', [status(thm)], ['251', '252'])).
% 0.60/0.85  thf('254', plain,
% 0.60/0.85      (((k2_tmap_1 @ sk_D @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.60/0.85         sk_C)
% 0.60/0.85         = (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ 
% 0.60/0.85            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)))),
% 0.60/0.85      inference('sup+', [status(thm)], ['224', '225'])).
% 0.60/0.85  thf('255', plain,
% 0.60/0.85      ((v1_funct_1 @ 
% 0.60/0.85        (k2_tmap_1 @ sk_D @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.60/0.85         sk_C))),
% 0.60/0.85      inference('demod', [status(thm)], ['253', '254'])).
% 0.60/0.85  thf('256', plain,
% 0.60/0.85      (![X0 : $i]:
% 0.60/0.85         (~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.85             (k2_tmap_1 @ sk_D @ sk_B @ 
% 0.60/0.85              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ sk_C) @ 
% 0.60/0.85             X0)
% 0.60/0.85          | ((k2_tmap_1 @ sk_D @ sk_B @ 
% 0.60/0.85              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ sk_C) = (X0))
% 0.60/0.85          | ~ (m1_subset_1 @ X0 @ 
% 0.60/0.85               (k1_zfmisc_1 @ 
% 0.60/0.85                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 0.60/0.85          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.60/0.85          | ~ (v1_funct_1 @ X0)
% 0.60/0.85          | ~ (v1_funct_2 @ 
% 0.60/0.85               (k2_tmap_1 @ sk_D @ sk_B @ 
% 0.60/0.85                (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ sk_C) @ 
% 0.60/0.85               (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 0.60/0.85      inference('demod', [status(thm)], ['229', '255'])).
% 0.60/0.85  thf('257', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('258', plain,
% 0.60/0.85      (![X22 : $i]: ((m1_pre_topc @ X22 @ X22) | ~ (l1_pre_topc @ X22))),
% 0.60/0.85      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.60/0.85  thf('259', plain,
% 0.60/0.85      ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.60/0.85        (k1_zfmisc_1 @ 
% 0.60/0.85         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.60/0.85      inference('demod', [status(thm)], ['110', '111'])).
% 0.60/0.85  thf('260', plain,
% 0.60/0.85      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.60/0.85         (~ (m1_pre_topc @ X17 @ X18)
% 0.60/0.85          | ~ (m1_pre_topc @ X19 @ X18)
% 0.60/0.85          | ~ (l1_pre_topc @ X20)
% 0.60/0.85          | ~ (v2_pre_topc @ X20)
% 0.60/0.85          | (v2_struct_0 @ X20)
% 0.60/0.85          | ~ (l1_pre_topc @ X18)
% 0.60/0.85          | ~ (v2_pre_topc @ X18)
% 0.60/0.85          | (v2_struct_0 @ X18)
% 0.60/0.85          | ~ (v1_funct_1 @ X21)
% 0.60/0.85          | ~ (v1_funct_2 @ X21 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X20))
% 0.60/0.85          | ~ (m1_subset_1 @ X21 @ 
% 0.60/0.85               (k1_zfmisc_1 @ 
% 0.60/0.85                (k2_zfmisc_1 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X20))))
% 0.60/0.85          | (v1_funct_2 @ (k3_tmap_1 @ X18 @ X20 @ X19 @ X17 @ X21) @ 
% 0.60/0.85             (u1_struct_0 @ X17) @ (u1_struct_0 @ X20)))),
% 0.60/0.85      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 0.60/0.85  thf('261', plain,
% 0.60/0.85      (![X0 : $i, X1 : $i]:
% 0.60/0.85         ((v1_funct_2 @ 
% 0.60/0.85           (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ 
% 0.60/0.85            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.60/0.85           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.60/0.85          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.60/0.85               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.60/0.85          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))
% 0.60/0.85          | (v2_struct_0 @ X1)
% 0.60/0.85          | ~ (v2_pre_topc @ X1)
% 0.60/0.85          | ~ (l1_pre_topc @ X1)
% 0.60/0.85          | (v2_struct_0 @ sk_B)
% 0.60/0.85          | ~ (v2_pre_topc @ sk_B)
% 0.60/0.85          | ~ (l1_pre_topc @ sk_B)
% 0.60/0.85          | ~ (m1_pre_topc @ sk_D @ X1)
% 0.60/0.85          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.60/0.85      inference('sup-', [status(thm)], ['259', '260'])).
% 0.60/0.85  thf('262', plain, ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))),
% 0.60/0.85      inference('demod', [status(thm)], ['116', '117'])).
% 0.60/0.85  thf('263', plain, ((v2_pre_topc @ sk_B)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('264', plain, ((l1_pre_topc @ sk_B)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('265', plain,
% 0.60/0.85      (![X0 : $i, X1 : $i]:
% 0.60/0.85         ((v1_funct_2 @ 
% 0.60/0.85           (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ 
% 0.60/0.85            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.60/0.85           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.60/0.85          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.60/0.85               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.60/0.85          | (v2_struct_0 @ X1)
% 0.60/0.85          | ~ (v2_pre_topc @ X1)
% 0.60/0.85          | ~ (l1_pre_topc @ X1)
% 0.60/0.85          | (v2_struct_0 @ sk_B)
% 0.60/0.85          | ~ (m1_pre_topc @ sk_D @ X1)
% 0.60/0.85          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.60/0.85      inference('demod', [status(thm)], ['261', '262', '263', '264'])).
% 0.60/0.85  thf('266', plain,
% 0.60/0.85      ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.60/0.85        (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.60/0.85      inference('clc', [status(thm)], ['106', '107'])).
% 0.60/0.85  thf('267', plain,
% 0.60/0.85      (![X0 : $i, X1 : $i]:
% 0.60/0.85         ((v1_funct_2 @ 
% 0.60/0.85           (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ 
% 0.60/0.85            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.60/0.85           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.60/0.85          | (v2_struct_0 @ X1)
% 0.60/0.85          | ~ (v2_pre_topc @ X1)
% 0.60/0.85          | ~ (l1_pre_topc @ X1)
% 0.60/0.85          | (v2_struct_0 @ sk_B)
% 0.60/0.85          | ~ (m1_pre_topc @ sk_D @ X1)
% 0.60/0.85          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.60/0.85      inference('demod', [status(thm)], ['265', '266'])).
% 0.60/0.85  thf('268', plain,
% 0.60/0.85      (![X0 : $i]:
% 0.60/0.85         (~ (l1_pre_topc @ sk_D)
% 0.60/0.85          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.60/0.85          | (v2_struct_0 @ sk_B)
% 0.60/0.85          | ~ (l1_pre_topc @ sk_D)
% 0.60/0.85          | ~ (v2_pre_topc @ sk_D)
% 0.60/0.85          | (v2_struct_0 @ sk_D)
% 0.60/0.85          | (v1_funct_2 @ 
% 0.60/0.85             (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ 
% 0.60/0.85              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.60/0.85             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 0.60/0.85      inference('sup-', [status(thm)], ['258', '267'])).
% 0.60/0.85  thf('269', plain, ((l1_pre_topc @ sk_D)),
% 0.60/0.85      inference('demod', [status(thm)], ['163', '164'])).
% 0.60/0.85  thf('270', plain, ((l1_pre_topc @ sk_D)),
% 0.60/0.85      inference('demod', [status(thm)], ['163', '164'])).
% 0.60/0.85  thf('271', plain, ((v2_pre_topc @ sk_D)),
% 0.60/0.85      inference('demod', [status(thm)], ['157', '158', '159'])).
% 0.60/0.85  thf('272', plain,
% 0.60/0.85      (![X0 : $i]:
% 0.60/0.85         (~ (m1_pre_topc @ X0 @ sk_D)
% 0.60/0.85          | (v2_struct_0 @ sk_B)
% 0.60/0.85          | (v2_struct_0 @ sk_D)
% 0.60/0.85          | (v1_funct_2 @ 
% 0.60/0.85             (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ 
% 0.60/0.85              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.60/0.85             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 0.60/0.85      inference('demod', [status(thm)], ['268', '269', '270', '271'])).
% 0.60/0.85  thf('273', plain,
% 0.60/0.85      (((v1_funct_2 @ 
% 0.60/0.85         (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ 
% 0.60/0.85          (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.60/0.85         (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.60/0.85        | (v2_struct_0 @ sk_D)
% 0.60/0.85        | (v2_struct_0 @ sk_B))),
% 0.60/0.85      inference('sup-', [status(thm)], ['257', '272'])).
% 0.60/0.85  thf('274', plain,
% 0.60/0.85      (((k2_tmap_1 @ sk_D @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.60/0.85         sk_C)
% 0.60/0.85         = (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ 
% 0.60/0.85            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)))),
% 0.60/0.85      inference('sup+', [status(thm)], ['224', '225'])).
% 0.60/0.85  thf('275', plain,
% 0.60/0.85      (((v1_funct_2 @ 
% 0.60/0.85         (k2_tmap_1 @ sk_D @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.60/0.85          sk_C) @ 
% 0.60/0.85         (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.60/0.85        | (v2_struct_0 @ sk_D)
% 0.60/0.85        | (v2_struct_0 @ sk_B))),
% 0.60/0.85      inference('demod', [status(thm)], ['273', '274'])).
% 0.60/0.85  thf('276', plain, (~ (v2_struct_0 @ sk_D)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('277', plain,
% 0.60/0.85      (((v2_struct_0 @ sk_B)
% 0.60/0.85        | (v1_funct_2 @ 
% 0.60/0.85           (k2_tmap_1 @ sk_D @ sk_B @ 
% 0.60/0.85            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ sk_C) @ 
% 0.60/0.85           (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 0.60/0.85      inference('clc', [status(thm)], ['275', '276'])).
% 0.60/0.85  thf('278', plain, (~ (v2_struct_0 @ sk_B)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('279', plain,
% 0.60/0.85      ((v1_funct_2 @ 
% 0.60/0.85        (k2_tmap_1 @ sk_D @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.60/0.85         sk_C) @ 
% 0.60/0.85        (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.60/0.85      inference('clc', [status(thm)], ['277', '278'])).
% 0.60/0.85  thf('280', plain,
% 0.60/0.85      (![X0 : $i]:
% 0.60/0.85         (~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.85             (k2_tmap_1 @ sk_D @ sk_B @ 
% 0.60/0.85              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ sk_C) @ 
% 0.60/0.85             X0)
% 0.60/0.85          | ((k2_tmap_1 @ sk_D @ sk_B @ 
% 0.60/0.85              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ sk_C) = (X0))
% 0.60/0.85          | ~ (m1_subset_1 @ X0 @ 
% 0.60/0.85               (k1_zfmisc_1 @ 
% 0.60/0.85                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 0.60/0.85          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.60/0.85          | ~ (v1_funct_1 @ X0))),
% 0.60/0.85      inference('demod', [status(thm)], ['256', '279'])).
% 0.60/0.85  thf('281', plain,
% 0.60/0.85      (((v2_struct_0 @ sk_B)
% 0.60/0.85        | (v2_struct_0 @ sk_C)
% 0.60/0.85        | (v2_struct_0 @ sk_D)
% 0.60/0.85        | (v2_struct_0 @ sk_A)
% 0.60/0.85        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C))
% 0.60/0.85        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 0.60/0.85             (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.60/0.85        | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 0.60/0.85             (k1_zfmisc_1 @ 
% 0.60/0.85              (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 0.60/0.85        | ((k2_tmap_1 @ sk_D @ sk_B @ 
% 0.60/0.85            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ sk_C)
% 0.60/0.85            = (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C)))),
% 0.60/0.85      inference('sup-', [status(thm)], ['187', '280'])).
% 0.60/0.85  thf('282', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('283', plain,
% 0.60/0.85      (![X0 : $i]:
% 0.60/0.85         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.60/0.85          | (v2_struct_0 @ sk_B)
% 0.60/0.85          | (v2_struct_0 @ sk_A)
% 0.60/0.85          | (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E)))),
% 0.60/0.85      inference('demod', [status(thm)], ['35', '36', '37', '38'])).
% 0.60/0.85  thf('284', plain,
% 0.60/0.85      (((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E))
% 0.60/0.85        | (v2_struct_0 @ sk_A)
% 0.60/0.85        | (v2_struct_0 @ sk_B))),
% 0.60/0.85      inference('sup-', [status(thm)], ['282', '283'])).
% 0.60/0.85  thf('285', plain, (~ (v2_struct_0 @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('286', plain,
% 0.60/0.85      (((v2_struct_0 @ sk_B)
% 0.60/0.85        | (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E)))),
% 0.60/0.85      inference('clc', [status(thm)], ['284', '285'])).
% 0.60/0.85  thf('287', plain, (~ (v2_struct_0 @ sk_B)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('288', plain,
% 0.60/0.85      ((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E))),
% 0.60/0.85      inference('clc', [status(thm)], ['286', '287'])).
% 0.60/0.85  thf('289', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('290', plain,
% 0.60/0.85      (![X0 : $i]:
% 0.60/0.85         ((v2_struct_0 @ sk_A)
% 0.60/0.85          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E)
% 0.60/0.85              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.85                 sk_E @ (u1_struct_0 @ X0)))
% 0.60/0.85          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.60/0.85          | (v2_struct_0 @ sk_B))),
% 0.60/0.85      inference('simplify', [status(thm)], ['60'])).
% 0.60/0.85  thf('291', plain,
% 0.60/0.85      (((v2_struct_0 @ sk_B)
% 0.60/0.85        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E)
% 0.60/0.85            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.85               sk_E @ (u1_struct_0 @ sk_C)))
% 0.60/0.85        | (v2_struct_0 @ sk_A))),
% 0.60/0.85      inference('sup-', [status(thm)], ['289', '290'])).
% 0.60/0.85  thf('292', plain, (~ (v2_struct_0 @ sk_B)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('293', plain,
% 0.60/0.85      (((v2_struct_0 @ sk_A)
% 0.60/0.85        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E)
% 0.60/0.85            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.85               sk_E @ (u1_struct_0 @ sk_C))))),
% 0.60/0.85      inference('clc', [status(thm)], ['291', '292'])).
% 0.60/0.85  thf('294', plain, (~ (v2_struct_0 @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('295', plain,
% 0.60/0.85      (((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E)
% 0.60/0.85         = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.60/0.85            (u1_struct_0 @ sk_C)))),
% 0.60/0.85      inference('clc', [status(thm)], ['293', '294'])).
% 0.60/0.85  thf('296', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('297', plain,
% 0.60/0.85      (![X0 : $i]:
% 0.60/0.85         ((v2_struct_0 @ sk_A)
% 0.60/0.85          | ((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0)
% 0.60/0.85              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.85                 sk_E @ (u1_struct_0 @ X0)))
% 0.60/0.85          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.60/0.85          | (v2_struct_0 @ sk_B))),
% 0.60/0.85      inference('demod', [status(thm)],
% 0.60/0.85                ['70', '71', '72', '73', '74', '75', '76'])).
% 0.60/0.85  thf('298', plain,
% 0.60/0.85      (((v2_struct_0 @ sk_B)
% 0.60/0.85        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C)
% 0.60/0.85            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.85               sk_E @ (u1_struct_0 @ sk_C)))
% 0.60/0.85        | (v2_struct_0 @ sk_A))),
% 0.60/0.85      inference('sup-', [status(thm)], ['296', '297'])).
% 0.60/0.85  thf('299', plain, (~ (v2_struct_0 @ sk_B)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('300', plain,
% 0.60/0.85      (((v2_struct_0 @ sk_A)
% 0.60/0.85        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C)
% 0.60/0.85            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.60/0.85               sk_E @ (u1_struct_0 @ sk_C))))),
% 0.60/0.85      inference('clc', [status(thm)], ['298', '299'])).
% 0.60/0.85  thf('301', plain, (~ (v2_struct_0 @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('302', plain,
% 0.60/0.85      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C)
% 0.60/0.85         = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.60/0.85            (u1_struct_0 @ sk_C)))),
% 0.60/0.85      inference('clc', [status(thm)], ['300', '301'])).
% 0.60/0.85  thf('303', plain,
% 0.60/0.85      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C)
% 0.60/0.85         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E))),
% 0.60/0.85      inference('sup+', [status(thm)], ['295', '302'])).
% 0.60/0.85  thf('304', plain, ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C))),
% 0.60/0.85      inference('demod', [status(thm)], ['288', '303'])).
% 0.60/0.85  thf('305', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('306', plain,
% 0.60/0.85      (![X0 : $i]:
% 0.60/0.85         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.60/0.85          | (v2_struct_0 @ sk_B)
% 0.60/0.85          | (v2_struct_0 @ sk_A)
% 0.60/0.85          | (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 0.60/0.85             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 0.60/0.85      inference('demod', [status(thm)], ['97', '98', '99', '100'])).
% 0.60/0.85  thf('307', plain,
% 0.60/0.85      (((v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E) @ 
% 0.60/0.85         (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.60/0.85        | (v2_struct_0 @ sk_A)
% 0.60/0.85        | (v2_struct_0 @ sk_B))),
% 0.60/0.85      inference('sup-', [status(thm)], ['305', '306'])).
% 0.60/0.85  thf('308', plain,
% 0.60/0.85      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C)
% 0.60/0.85         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E))),
% 0.60/0.85      inference('sup+', [status(thm)], ['295', '302'])).
% 0.60/0.85  thf('309', plain,
% 0.60/0.85      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 0.60/0.85         (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.60/0.85        | (v2_struct_0 @ sk_A)
% 0.60/0.85        | (v2_struct_0 @ sk_B))),
% 0.60/0.85      inference('demod', [status(thm)], ['307', '308'])).
% 0.60/0.85  thf('310', plain, (~ (v2_struct_0 @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('311', plain,
% 0.60/0.85      (((v2_struct_0 @ sk_B)
% 0.60/0.85        | (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 0.60/0.85           (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 0.60/0.85      inference('clc', [status(thm)], ['309', '310'])).
% 0.60/0.85  thf('312', plain, (~ (v2_struct_0 @ sk_B)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('313', plain,
% 0.60/0.85      ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 0.60/0.85        (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.60/0.85      inference('clc', [status(thm)], ['311', '312'])).
% 0.60/0.85  thf('314', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('315', plain,
% 0.60/0.85      (![X0 : $i]:
% 0.60/0.85         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.60/0.85          | (v2_struct_0 @ sk_B)
% 0.60/0.85          | (v2_struct_0 @ sk_A)
% 0.60/0.85          | (m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 0.60/0.85             (k1_zfmisc_1 @ 
% 0.60/0.85              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))))),
% 0.60/0.85      inference('demod', [status(thm)], ['12', '13', '14', '15'])).
% 0.60/0.85  thf('316', plain,
% 0.60/0.85      (((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E) @ 
% 0.60/0.86         (k1_zfmisc_1 @ 
% 0.60/0.86          (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 0.60/0.86        | (v2_struct_0 @ sk_A)
% 0.60/0.86        | (v2_struct_0 @ sk_B))),
% 0.60/0.86      inference('sup-', [status(thm)], ['314', '315'])).
% 0.60/0.86  thf('317', plain, (~ (v2_struct_0 @ sk_A)),
% 0.60/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.86  thf('318', plain,
% 0.60/0.86      (((v2_struct_0 @ sk_B)
% 0.60/0.86        | (m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E) @ 
% 0.60/0.86           (k1_zfmisc_1 @ 
% 0.60/0.86            (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))))),
% 0.60/0.86      inference('clc', [status(thm)], ['316', '317'])).
% 0.60/0.86  thf('319', plain, (~ (v2_struct_0 @ sk_B)),
% 0.60/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.86  thf('320', plain,
% 0.60/0.86      ((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E) @ 
% 0.60/0.86        (k1_zfmisc_1 @ 
% 0.60/0.86         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.60/0.86      inference('clc', [status(thm)], ['318', '319'])).
% 0.60/0.86  thf('321', plain,
% 0.60/0.86      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C)
% 0.60/0.86         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E))),
% 0.60/0.86      inference('sup+', [status(thm)], ['295', '302'])).
% 0.60/0.86  thf('322', plain,
% 0.60/0.86      ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 0.60/0.86        (k1_zfmisc_1 @ 
% 0.60/0.86         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.60/0.86      inference('demod', [status(thm)], ['320', '321'])).
% 0.60/0.86  thf('323', plain,
% 0.60/0.86      (((v2_struct_0 @ sk_B)
% 0.60/0.86        | (v2_struct_0 @ sk_C)
% 0.60/0.86        | (v2_struct_0 @ sk_D)
% 0.60/0.86        | (v2_struct_0 @ sk_A)
% 0.60/0.86        | ((k2_tmap_1 @ sk_D @ sk_B @ 
% 0.60/0.86            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ sk_C)
% 0.60/0.86            = (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C)))),
% 0.60/0.86      inference('demod', [status(thm)], ['281', '304', '313', '322'])).
% 0.60/0.86  thf('324', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C))),
% 0.60/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.86  thf('325', plain, (((sk_F) = (sk_G))),
% 0.60/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.86  thf('326', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.60/0.86      inference('demod', [status(thm)], ['324', '325'])).
% 0.60/0.86  thf('327', plain,
% 0.60/0.86      ((r1_tmap_1 @ sk_D @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.60/0.86        sk_F)),
% 0.60/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.86  thf('328', plain,
% 0.60/0.86      ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.60/0.86        (k1_zfmisc_1 @ 
% 0.60/0.86         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.60/0.86      inference('demod', [status(thm)], ['110', '111'])).
% 0.60/0.86  thf(t64_tmap_1, axiom,
% 0.60/0.86    (![A:$i]:
% 0.60/0.86     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.60/0.86       ( ![B:$i]:
% 0.60/0.86         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.60/0.86             ( l1_pre_topc @ B ) ) =>
% 0.60/0.86           ( ![C:$i]:
% 0.60/0.86             ( ( ( v1_funct_1 @ C ) & 
% 0.60/0.86                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.60/0.86                 ( m1_subset_1 @
% 0.60/0.86                   C @ 
% 0.60/0.86                   ( k1_zfmisc_1 @
% 0.60/0.86                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.60/0.86               ( ![D:$i]:
% 0.60/0.86                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.60/0.86                   ( ![E:$i]:
% 0.60/0.86                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.60/0.86                       ( ![F:$i]:
% 0.60/0.86                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.60/0.86                           ( ( ( ( E ) = ( F ) ) & 
% 0.60/0.86                               ( r1_tmap_1 @ B @ A @ C @ E ) ) =>
% 0.60/0.86                             ( r1_tmap_1 @
% 0.60/0.86                               D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.60/0.86  thf('329', plain,
% 0.60/0.86      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.60/0.86         ((v2_struct_0 @ X23)
% 0.60/0.86          | ~ (v2_pre_topc @ X23)
% 0.60/0.86          | ~ (l1_pre_topc @ X23)
% 0.60/0.86          | (v2_struct_0 @ X24)
% 0.60/0.86          | ~ (m1_pre_topc @ X24 @ X23)
% 0.60/0.86          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X24))
% 0.60/0.86          | (r1_tmap_1 @ X24 @ X26 @ (k2_tmap_1 @ X23 @ X26 @ X27 @ X24) @ X25)
% 0.60/0.86          | ((X28) != (X25))
% 0.60/0.86          | ~ (r1_tmap_1 @ X23 @ X26 @ X27 @ X28)
% 0.60/0.86          | ~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X23))
% 0.60/0.86          | ~ (m1_subset_1 @ X27 @ 
% 0.60/0.86               (k1_zfmisc_1 @ 
% 0.60/0.86                (k2_zfmisc_1 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X26))))
% 0.60/0.86          | ~ (v1_funct_2 @ X27 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X26))
% 0.60/0.86          | ~ (v1_funct_1 @ X27)
% 0.60/0.86          | ~ (l1_pre_topc @ X26)
% 0.60/0.86          | ~ (v2_pre_topc @ X26)
% 0.60/0.86          | (v2_struct_0 @ X26))),
% 0.60/0.86      inference('cnf', [status(esa)], [t64_tmap_1])).
% 0.60/0.86  thf('330', plain,
% 0.60/0.86      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.60/0.86         ((v2_struct_0 @ X26)
% 0.60/0.86          | ~ (v2_pre_topc @ X26)
% 0.60/0.86          | ~ (l1_pre_topc @ X26)
% 0.60/0.86          | ~ (v1_funct_1 @ X27)
% 0.60/0.86          | ~ (v1_funct_2 @ X27 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X26))
% 0.60/0.86          | ~ (m1_subset_1 @ X27 @ 
% 0.60/0.86               (k1_zfmisc_1 @ 
% 0.60/0.86                (k2_zfmisc_1 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X26))))
% 0.60/0.86          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X23))
% 0.60/0.86          | ~ (r1_tmap_1 @ X23 @ X26 @ X27 @ X25)
% 0.60/0.86          | (r1_tmap_1 @ X24 @ X26 @ (k2_tmap_1 @ X23 @ X26 @ X27 @ X24) @ X25)
% 0.60/0.86          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X24))
% 0.60/0.86          | ~ (m1_pre_topc @ X24 @ X23)
% 0.60/0.86          | (v2_struct_0 @ X24)
% 0.60/0.86          | ~ (l1_pre_topc @ X23)
% 0.60/0.86          | ~ (v2_pre_topc @ X23)
% 0.60/0.86          | (v2_struct_0 @ X23))),
% 0.60/0.86      inference('simplify', [status(thm)], ['329'])).
% 0.60/0.86  thf('331', plain,
% 0.60/0.86      (![X0 : $i, X1 : $i]:
% 0.60/0.86         ((v2_struct_0 @ sk_D)
% 0.60/0.86          | ~ (v2_pre_topc @ sk_D)
% 0.60/0.86          | ~ (l1_pre_topc @ sk_D)
% 0.60/0.86          | (v2_struct_0 @ X0)
% 0.60/0.86          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.60/0.86          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.60/0.86          | (r1_tmap_1 @ X0 @ sk_B @ 
% 0.60/0.86             (k2_tmap_1 @ sk_D @ sk_B @ 
% 0.60/0.86              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ X0) @ 
% 0.60/0.86             X1)
% 0.60/0.86          | ~ (r1_tmap_1 @ sk_D @ sk_B @ 
% 0.60/0.86               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ X1)
% 0.60/0.86          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D))
% 0.60/0.86          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.60/0.86               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.60/0.86          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))
% 0.60/0.86          | ~ (l1_pre_topc @ sk_B)
% 0.60/0.86          | ~ (v2_pre_topc @ sk_B)
% 0.60/0.86          | (v2_struct_0 @ sk_B))),
% 0.60/0.86      inference('sup-', [status(thm)], ['328', '330'])).
% 0.60/0.86  thf('332', plain, ((v2_pre_topc @ sk_D)),
% 0.60/0.86      inference('demod', [status(thm)], ['157', '158', '159'])).
% 0.60/0.86  thf('333', plain, ((l1_pre_topc @ sk_D)),
% 0.60/0.86      inference('demod', [status(thm)], ['163', '164'])).
% 0.60/0.86  thf('334', plain,
% 0.60/0.86      ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.60/0.86        (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.60/0.86      inference('clc', [status(thm)], ['106', '107'])).
% 0.60/0.86  thf('335', plain, ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))),
% 0.60/0.86      inference('demod', [status(thm)], ['116', '117'])).
% 0.60/0.86  thf('336', plain, ((l1_pre_topc @ sk_B)),
% 0.60/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.86  thf('337', plain, ((v2_pre_topc @ sk_B)),
% 0.60/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.86  thf('338', plain,
% 0.60/0.86      (![X0 : $i, X1 : $i]:
% 0.60/0.86         ((v2_struct_0 @ sk_D)
% 0.60/0.86          | (v2_struct_0 @ X0)
% 0.60/0.86          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.60/0.86          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.60/0.86          | (r1_tmap_1 @ X0 @ sk_B @ 
% 0.60/0.86             (k2_tmap_1 @ sk_D @ sk_B @ 
% 0.60/0.86              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ X0) @ 
% 0.60/0.86             X1)
% 0.60/0.86          | ~ (r1_tmap_1 @ sk_D @ sk_B @ 
% 0.60/0.86               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ X1)
% 0.60/0.86          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D))
% 0.60/0.86          | (v2_struct_0 @ sk_B))),
% 0.60/0.86      inference('demod', [status(thm)],
% 0.60/0.86                ['331', '332', '333', '334', '335', '336', '337'])).
% 0.60/0.86  thf('339', plain,
% 0.60/0.86      (![X0 : $i]:
% 0.60/0.86         ((v2_struct_0 @ sk_B)
% 0.60/0.86          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))
% 0.60/0.86          | (r1_tmap_1 @ X0 @ sk_B @ 
% 0.60/0.86             (k2_tmap_1 @ sk_D @ sk_B @ 
% 0.60/0.86              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ X0) @ 
% 0.60/0.86             sk_F)
% 0.60/0.86          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ X0))
% 0.60/0.86          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.60/0.86          | (v2_struct_0 @ X0)
% 0.60/0.86          | (v2_struct_0 @ sk_D))),
% 0.60/0.86      inference('sup-', [status(thm)], ['327', '338'])).
% 0.60/0.86  thf('340', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.60/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.86  thf('341', plain,
% 0.60/0.86      (![X0 : $i]:
% 0.60/0.86         ((v2_struct_0 @ sk_B)
% 0.60/0.86          | (r1_tmap_1 @ X0 @ sk_B @ 
% 0.60/0.86             (k2_tmap_1 @ sk_D @ sk_B @ 
% 0.60/0.86              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ X0) @ 
% 0.60/0.86             sk_F)
% 0.60/0.86          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ X0))
% 0.60/0.86          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.60/0.86          | (v2_struct_0 @ X0)
% 0.60/0.86          | (v2_struct_0 @ sk_D))),
% 0.60/0.86      inference('demod', [status(thm)], ['339', '340'])).
% 0.60/0.86  thf('342', plain,
% 0.60/0.86      (((v2_struct_0 @ sk_D)
% 0.60/0.86        | (v2_struct_0 @ sk_C)
% 0.60/0.86        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.60/0.86        | (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.60/0.86           (k2_tmap_1 @ sk_D @ sk_B @ 
% 0.60/0.86            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ sk_C) @ 
% 0.60/0.86           sk_F)
% 0.60/0.86        | (v2_struct_0 @ sk_B))),
% 0.60/0.86      inference('sup-', [status(thm)], ['326', '341'])).
% 0.60/0.86  thf('343', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.60/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.86  thf('344', plain,
% 0.60/0.86      (((v2_struct_0 @ sk_D)
% 0.60/0.86        | (v2_struct_0 @ sk_C)
% 0.60/0.86        | (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.60/0.86           (k2_tmap_1 @ sk_D @ sk_B @ 
% 0.60/0.86            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ sk_C) @ 
% 0.60/0.86           sk_F)
% 0.60/0.86        | (v2_struct_0 @ sk_B))),
% 0.60/0.86      inference('demod', [status(thm)], ['342', '343'])).
% 0.60/0.86  thf('345', plain,
% 0.60/0.86      (((r1_tmap_1 @ sk_C @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 0.60/0.86         sk_F)
% 0.60/0.86        | (v2_struct_0 @ sk_A)
% 0.60/0.86        | (v2_struct_0 @ sk_D)
% 0.60/0.86        | (v2_struct_0 @ sk_C)
% 0.60/0.86        | (v2_struct_0 @ sk_B)
% 0.60/0.86        | (v2_struct_0 @ sk_B)
% 0.60/0.86        | (v2_struct_0 @ sk_C)
% 0.60/0.86        | (v2_struct_0 @ sk_D))),
% 0.60/0.86      inference('sup+', [status(thm)], ['323', '344'])).
% 0.60/0.86  thf('346', plain,
% 0.60/0.86      (((v2_struct_0 @ sk_B)
% 0.60/0.86        | (v2_struct_0 @ sk_C)
% 0.60/0.86        | (v2_struct_0 @ sk_D)
% 0.60/0.86        | (v2_struct_0 @ sk_A)
% 0.60/0.86        | (r1_tmap_1 @ sk_C @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 0.60/0.86           sk_F))),
% 0.60/0.86      inference('simplify', [status(thm)], ['345'])).
% 0.60/0.86  thf('347', plain,
% 0.60/0.86      (~ (r1_tmap_1 @ sk_C @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 0.60/0.86          sk_G)),
% 0.60/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.86  thf('348', plain, (((sk_F) = (sk_G))),
% 0.60/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.86  thf('349', plain,
% 0.60/0.86      (~ (r1_tmap_1 @ sk_C @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 0.60/0.86          sk_F)),
% 0.60/0.86      inference('demod', [status(thm)], ['347', '348'])).
% 0.60/0.86  thf('350', plain,
% 0.60/0.86      (((v2_struct_0 @ sk_A)
% 0.60/0.86        | (v2_struct_0 @ sk_D)
% 0.60/0.86        | (v2_struct_0 @ sk_C)
% 0.60/0.86        | (v2_struct_0 @ sk_B))),
% 0.60/0.86      inference('sup-', [status(thm)], ['346', '349'])).
% 0.60/0.86  thf('351', plain, (~ (v2_struct_0 @ sk_B)),
% 0.60/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.86  thf('352', plain,
% 0.60/0.86      (((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_A))),
% 0.60/0.86      inference('sup-', [status(thm)], ['350', '351'])).
% 0.60/0.86  thf('353', plain, (~ (v2_struct_0 @ sk_C)),
% 0.60/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.86  thf('354', plain, (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D))),
% 0.60/0.86      inference('clc', [status(thm)], ['352', '353'])).
% 0.60/0.86  thf('355', plain, (~ (v2_struct_0 @ sk_A)),
% 0.60/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.86  thf('356', plain, ((v2_struct_0 @ sk_D)),
% 0.60/0.86      inference('clc', [status(thm)], ['354', '355'])).
% 0.60/0.86  thf('357', plain, ($false), inference('demod', [status(thm)], ['0', '356'])).
% 0.60/0.86  
% 0.60/0.86  % SZS output end Refutation
% 0.60/0.86  
% 0.60/0.86  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
