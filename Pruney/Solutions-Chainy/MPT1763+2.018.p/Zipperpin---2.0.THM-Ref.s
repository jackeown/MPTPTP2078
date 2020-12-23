%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xskq6r9awD

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:04 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 125 expanded)
%              Number of leaves         :   31 (  51 expanded)
%              Depth                    :   14
%              Number of atoms          :  767 (2567 expanded)
%              Number of equality atoms :   22 (  22 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(t74_tmap_1,conjecture,(
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
                    ( ( ( v1_funct_1 @ D )
                      & ( v1_funct_2 @ D @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
                      & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) )
                   => ( r2_funct_2 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ D @ ( k3_tmap_1 @ A @ B @ C @ C @ D ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t74_tmap_1])).

thf('0',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_D @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_C @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('1',plain,(
    ! [X24: $i] :
      ( ( m1_pre_topc @ X24 @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('2',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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

thf('5',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( v2_struct_0 @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( m1_pre_topc @ X20 @ X21 )
      | ~ ( m1_pre_topc @ X20 @ X22 )
      | ( ( k3_tmap_1 @ X21 @ X19 @ X22 @ X20 @ X23 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X19 ) @ X23 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X19 ) ) ) )
      | ~ ( v1_funct_2 @ X23 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X19 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( m1_pre_topc @ X22 @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d5_tmap_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_C @ X1 @ sk_D )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_D @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_C )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('10',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ( ( k2_partfun1 @ X10 @ X11 @ X9 @ X12 )
        = ( k7_relat_1 @ X9 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_D @ X0 )
        = ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_C @ X1 @ sk_D )
        = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_C )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['6','7','8','13','14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ sk_D )
        = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ sk_D )
        = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_C @ sk_D )
      = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['2','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('23',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v4_relat_1 @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('24',plain,(
    v4_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('25',plain,(
    ! [X4: $i,X5: $i] :
      ( ( X4
        = ( k7_relat_1 @ X4 @ X5 ) )
      | ~ ( v4_relat_1 @ X4 @ X5 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('26',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( sk_D
      = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('29',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('30',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('31',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['26','31'])).

thf('33',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_C @ sk_D )
      = sk_D )
    | ~ ( m1_pre_topc @ sk_C @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['21','32'])).

thf('34',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_C @ sk_D )
      = sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','33'])).

thf('35',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('36',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_pre_topc @ X17 @ X18 )
      | ( l1_pre_topc @ X17 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('37',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_C @ sk_D )
      = sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['34','39'])).

thf('41',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_C @ sk_D )
      = sk_D ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('43',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_C @ sk_D )
    = sk_D ),
    inference(clc,[status(thm)],['42','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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

thf('46',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ~ ( v1_funct_2 @ X13 @ X14 @ X15 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_funct_2 @ X16 @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ( r2_funct_2 @ X14 @ X15 @ X13 @ X16 )
      | ( X13 != X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('47',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r2_funct_2 @ X14 @ X15 @ X16 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_funct_2 @ X16 @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ~ ( v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_D @ sk_D ) ),
    inference('sup-',[status(thm)],['45','47'])).

thf('49',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_D @ sk_D ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,(
    $false ),
    inference(demod,[status(thm)],['0','44','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xskq6r9awD
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:40:12 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.33  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.18/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.18/0.46  % Solved by: fo/fo7.sh
% 0.18/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.18/0.46  % done 35 iterations in 0.020s
% 0.18/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.18/0.46  % SZS output start Refutation
% 0.18/0.46  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.18/0.46  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.18/0.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.18/0.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.18/0.46  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.18/0.46  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.18/0.46  thf(sk_D_type, type, sk_D: $i).
% 0.18/0.46  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.18/0.46  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.18/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.18/0.46  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.18/0.46  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.18/0.46  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.18/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.18/0.46  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.18/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.18/0.46  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.18/0.46  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.18/0.46  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.18/0.46  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.18/0.46  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.18/0.46  thf(t74_tmap_1, conjecture,
% 0.18/0.46    (![A:$i]:
% 0.18/0.46     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.18/0.46       ( ![B:$i]:
% 0.18/0.46         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.18/0.46             ( l1_pre_topc @ B ) ) =>
% 0.18/0.46           ( ![C:$i]:
% 0.18/0.46             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.18/0.46               ( ![D:$i]:
% 0.18/0.46                 ( ( ( v1_funct_1 @ D ) & 
% 0.18/0.46                     ( v1_funct_2 @
% 0.18/0.46                       D @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.18/0.46                     ( m1_subset_1 @
% 0.18/0.46                       D @ 
% 0.18/0.46                       ( k1_zfmisc_1 @
% 0.18/0.46                         ( k2_zfmisc_1 @
% 0.18/0.46                           ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.18/0.46                   ( r2_funct_2 @
% 0.18/0.46                     ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ D @ 
% 0.18/0.46                     ( k3_tmap_1 @ A @ B @ C @ C @ D ) ) ) ) ) ) ) ) ))).
% 0.18/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.18/0.46    (~( ![A:$i]:
% 0.18/0.46        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.18/0.46            ( l1_pre_topc @ A ) ) =>
% 0.18/0.46          ( ![B:$i]:
% 0.18/0.46            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.18/0.46                ( l1_pre_topc @ B ) ) =>
% 0.18/0.46              ( ![C:$i]:
% 0.18/0.46                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.18/0.46                  ( ![D:$i]:
% 0.18/0.46                    ( ( ( v1_funct_1 @ D ) & 
% 0.18/0.46                        ( v1_funct_2 @
% 0.18/0.46                          D @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.18/0.46                        ( m1_subset_1 @
% 0.18/0.46                          D @ 
% 0.18/0.46                          ( k1_zfmisc_1 @
% 0.18/0.46                            ( k2_zfmisc_1 @
% 0.18/0.46                              ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.18/0.46                      ( r2_funct_2 @
% 0.18/0.46                        ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ D @ 
% 0.18/0.46                        ( k3_tmap_1 @ A @ B @ C @ C @ D ) ) ) ) ) ) ) ) ) )),
% 0.18/0.46    inference('cnf.neg', [status(esa)], [t74_tmap_1])).
% 0.18/0.46  thf('0', plain,
% 0.18/0.46      (~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_D @ 
% 0.18/0.46          (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_C @ sk_D))),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf(t2_tsep_1, axiom,
% 0.18/0.46    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.18/0.46  thf('1', plain,
% 0.18/0.46      (![X24 : $i]: ((m1_pre_topc @ X24 @ X24) | ~ (l1_pre_topc @ X24))),
% 0.18/0.46      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.18/0.46  thf('2', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('3', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('4', plain,
% 0.18/0.46      ((m1_subset_1 @ sk_D @ 
% 0.18/0.46        (k1_zfmisc_1 @ 
% 0.18/0.46         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf(d5_tmap_1, axiom,
% 0.18/0.46    (![A:$i]:
% 0.18/0.46     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.18/0.46       ( ![B:$i]:
% 0.18/0.46         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.18/0.46             ( l1_pre_topc @ B ) ) =>
% 0.18/0.46           ( ![C:$i]:
% 0.18/0.46             ( ( m1_pre_topc @ C @ A ) =>
% 0.18/0.46               ( ![D:$i]:
% 0.18/0.46                 ( ( m1_pre_topc @ D @ A ) =>
% 0.18/0.46                   ( ![E:$i]:
% 0.18/0.46                     ( ( ( v1_funct_1 @ E ) & 
% 0.18/0.46                         ( v1_funct_2 @
% 0.18/0.46                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.18/0.46                         ( m1_subset_1 @
% 0.18/0.46                           E @ 
% 0.18/0.46                           ( k1_zfmisc_1 @
% 0.18/0.46                             ( k2_zfmisc_1 @
% 0.18/0.46                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.18/0.46                       ( ( m1_pre_topc @ D @ C ) =>
% 0.18/0.46                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 0.18/0.46                           ( k2_partfun1 @
% 0.18/0.46                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 0.18/0.46                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.18/0.46  thf('5', plain,
% 0.18/0.46      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.18/0.46         ((v2_struct_0 @ X19)
% 0.18/0.46          | ~ (v2_pre_topc @ X19)
% 0.18/0.46          | ~ (l1_pre_topc @ X19)
% 0.18/0.46          | ~ (m1_pre_topc @ X20 @ X21)
% 0.18/0.46          | ~ (m1_pre_topc @ X20 @ X22)
% 0.18/0.46          | ((k3_tmap_1 @ X21 @ X19 @ X22 @ X20 @ X23)
% 0.18/0.46              = (k2_partfun1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X19) @ 
% 0.18/0.46                 X23 @ (u1_struct_0 @ X20)))
% 0.18/0.46          | ~ (m1_subset_1 @ X23 @ 
% 0.18/0.46               (k1_zfmisc_1 @ 
% 0.18/0.46                (k2_zfmisc_1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X19))))
% 0.18/0.46          | ~ (v1_funct_2 @ X23 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X19))
% 0.18/0.46          | ~ (v1_funct_1 @ X23)
% 0.18/0.46          | ~ (m1_pre_topc @ X22 @ X21)
% 0.18/0.46          | ~ (l1_pre_topc @ X21)
% 0.18/0.46          | ~ (v2_pre_topc @ X21)
% 0.18/0.46          | (v2_struct_0 @ X21))),
% 0.18/0.46      inference('cnf', [status(esa)], [d5_tmap_1])).
% 0.18/0.46  thf('6', plain,
% 0.18/0.46      (![X0 : $i, X1 : $i]:
% 0.18/0.46         ((v2_struct_0 @ X0)
% 0.18/0.46          | ~ (v2_pre_topc @ X0)
% 0.18/0.46          | ~ (l1_pre_topc @ X0)
% 0.18/0.46          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.18/0.46          | ~ (v1_funct_1 @ sk_D)
% 0.18/0.46          | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.18/0.46          | ((k3_tmap_1 @ X0 @ sk_B @ sk_C @ X1 @ sk_D)
% 0.18/0.46              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.18/0.46                 sk_D @ (u1_struct_0 @ X1)))
% 0.18/0.46          | ~ (m1_pre_topc @ X1 @ sk_C)
% 0.18/0.46          | ~ (m1_pre_topc @ X1 @ X0)
% 0.18/0.46          | ~ (l1_pre_topc @ sk_B)
% 0.18/0.46          | ~ (v2_pre_topc @ sk_B)
% 0.18/0.46          | (v2_struct_0 @ sk_B))),
% 0.18/0.46      inference('sup-', [status(thm)], ['4', '5'])).
% 0.18/0.46  thf('7', plain, ((v1_funct_1 @ sk_D)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('8', plain,
% 0.18/0.46      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('9', plain,
% 0.18/0.46      ((m1_subset_1 @ sk_D @ 
% 0.18/0.46        (k1_zfmisc_1 @ 
% 0.18/0.46         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf(redefinition_k2_partfun1, axiom,
% 0.18/0.46    (![A:$i,B:$i,C:$i,D:$i]:
% 0.18/0.46     ( ( ( v1_funct_1 @ C ) & 
% 0.18/0.46         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.18/0.46       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.18/0.46  thf('10', plain,
% 0.18/0.46      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.18/0.46         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11)))
% 0.18/0.46          | ~ (v1_funct_1 @ X9)
% 0.18/0.46          | ((k2_partfun1 @ X10 @ X11 @ X9 @ X12) = (k7_relat_1 @ X9 @ X12)))),
% 0.18/0.46      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.18/0.46  thf('11', plain,
% 0.18/0.46      (![X0 : $i]:
% 0.18/0.46         (((k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_D @ 
% 0.18/0.46            X0) = (k7_relat_1 @ sk_D @ X0))
% 0.18/0.46          | ~ (v1_funct_1 @ sk_D))),
% 0.18/0.46      inference('sup-', [status(thm)], ['9', '10'])).
% 0.18/0.46  thf('12', plain, ((v1_funct_1 @ sk_D)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('13', plain,
% 0.18/0.46      (![X0 : $i]:
% 0.18/0.46         ((k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_D @ 
% 0.18/0.46           X0) = (k7_relat_1 @ sk_D @ X0))),
% 0.18/0.46      inference('demod', [status(thm)], ['11', '12'])).
% 0.18/0.46  thf('14', plain, ((l1_pre_topc @ sk_B)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('15', plain, ((v2_pre_topc @ sk_B)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('16', plain,
% 0.18/0.46      (![X0 : $i, X1 : $i]:
% 0.18/0.46         ((v2_struct_0 @ X0)
% 0.18/0.46          | ~ (v2_pre_topc @ X0)
% 0.18/0.46          | ~ (l1_pre_topc @ X0)
% 0.18/0.46          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.18/0.46          | ((k3_tmap_1 @ X0 @ sk_B @ sk_C @ X1 @ sk_D)
% 0.18/0.46              = (k7_relat_1 @ sk_D @ (u1_struct_0 @ X1)))
% 0.18/0.46          | ~ (m1_pre_topc @ X1 @ sk_C)
% 0.18/0.46          | ~ (m1_pre_topc @ X1 @ X0)
% 0.18/0.46          | (v2_struct_0 @ sk_B))),
% 0.18/0.46      inference('demod', [status(thm)], ['6', '7', '8', '13', '14', '15'])).
% 0.18/0.46  thf('17', plain,
% 0.18/0.46      (![X0 : $i]:
% 0.18/0.46         ((v2_struct_0 @ sk_B)
% 0.18/0.46          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.18/0.46          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.18/0.46          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ sk_D)
% 0.18/0.46              = (k7_relat_1 @ sk_D @ (u1_struct_0 @ X0)))
% 0.18/0.46          | ~ (l1_pre_topc @ sk_A)
% 0.18/0.46          | ~ (v2_pre_topc @ sk_A)
% 0.18/0.46          | (v2_struct_0 @ sk_A))),
% 0.18/0.46      inference('sup-', [status(thm)], ['3', '16'])).
% 0.18/0.46  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('19', plain, ((v2_pre_topc @ sk_A)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('20', plain,
% 0.18/0.46      (![X0 : $i]:
% 0.18/0.46         ((v2_struct_0 @ sk_B)
% 0.18/0.46          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.18/0.46          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.18/0.46          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ sk_D)
% 0.18/0.46              = (k7_relat_1 @ sk_D @ (u1_struct_0 @ X0)))
% 0.18/0.46          | (v2_struct_0 @ sk_A))),
% 0.18/0.46      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.18/0.46  thf('21', plain,
% 0.18/0.46      (((v2_struct_0 @ sk_A)
% 0.18/0.46        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_C @ sk_D)
% 0.18/0.46            = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)))
% 0.18/0.46        | ~ (m1_pre_topc @ sk_C @ sk_C)
% 0.18/0.46        | (v2_struct_0 @ sk_B))),
% 0.18/0.46      inference('sup-', [status(thm)], ['2', '20'])).
% 0.18/0.46  thf('22', plain,
% 0.18/0.46      ((m1_subset_1 @ sk_D @ 
% 0.18/0.46        (k1_zfmisc_1 @ 
% 0.18/0.46         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf(cc2_relset_1, axiom,
% 0.18/0.46    (![A:$i,B:$i,C:$i]:
% 0.18/0.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.18/0.46       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.18/0.46  thf('23', plain,
% 0.18/0.46      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.18/0.46         ((v4_relat_1 @ X6 @ X7)
% 0.18/0.46          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.18/0.46      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.18/0.46  thf('24', plain, ((v4_relat_1 @ sk_D @ (u1_struct_0 @ sk_C))),
% 0.18/0.46      inference('sup-', [status(thm)], ['22', '23'])).
% 0.18/0.46  thf(t209_relat_1, axiom,
% 0.18/0.46    (![A:$i,B:$i]:
% 0.18/0.46     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.18/0.46       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.18/0.46  thf('25', plain,
% 0.18/0.46      (![X4 : $i, X5 : $i]:
% 0.18/0.46         (((X4) = (k7_relat_1 @ X4 @ X5))
% 0.18/0.46          | ~ (v4_relat_1 @ X4 @ X5)
% 0.18/0.46          | ~ (v1_relat_1 @ X4))),
% 0.18/0.46      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.18/0.46  thf('26', plain,
% 0.18/0.46      ((~ (v1_relat_1 @ sk_D)
% 0.18/0.46        | ((sk_D) = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C))))),
% 0.18/0.46      inference('sup-', [status(thm)], ['24', '25'])).
% 0.18/0.46  thf('27', plain,
% 0.18/0.46      ((m1_subset_1 @ sk_D @ 
% 0.18/0.46        (k1_zfmisc_1 @ 
% 0.18/0.46         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf(cc2_relat_1, axiom,
% 0.18/0.46    (![A:$i]:
% 0.18/0.46     ( ( v1_relat_1 @ A ) =>
% 0.18/0.46       ( ![B:$i]:
% 0.18/0.46         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.18/0.46  thf('28', plain,
% 0.18/0.46      (![X0 : $i, X1 : $i]:
% 0.18/0.46         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.18/0.46          | (v1_relat_1 @ X0)
% 0.18/0.46          | ~ (v1_relat_1 @ X1))),
% 0.18/0.46      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.18/0.46  thf('29', plain,
% 0.18/0.46      ((~ (v1_relat_1 @ 
% 0.18/0.46           (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))
% 0.18/0.46        | (v1_relat_1 @ sk_D))),
% 0.18/0.46      inference('sup-', [status(thm)], ['27', '28'])).
% 0.18/0.46  thf(fc6_relat_1, axiom,
% 0.18/0.46    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.18/0.46  thf('30', plain,
% 0.18/0.46      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.18/0.46      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.18/0.46  thf('31', plain, ((v1_relat_1 @ sk_D)),
% 0.18/0.46      inference('demod', [status(thm)], ['29', '30'])).
% 0.18/0.46  thf('32', plain, (((sk_D) = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)))),
% 0.18/0.46      inference('demod', [status(thm)], ['26', '31'])).
% 0.18/0.46  thf('33', plain,
% 0.18/0.46      (((v2_struct_0 @ sk_A)
% 0.18/0.46        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_C @ sk_D) = (sk_D))
% 0.18/0.46        | ~ (m1_pre_topc @ sk_C @ sk_C)
% 0.18/0.46        | (v2_struct_0 @ sk_B))),
% 0.18/0.46      inference('demod', [status(thm)], ['21', '32'])).
% 0.18/0.46  thf('34', plain,
% 0.18/0.46      ((~ (l1_pre_topc @ sk_C)
% 0.18/0.46        | (v2_struct_0 @ sk_B)
% 0.18/0.46        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_C @ sk_D) = (sk_D))
% 0.18/0.46        | (v2_struct_0 @ sk_A))),
% 0.18/0.46      inference('sup-', [status(thm)], ['1', '33'])).
% 0.18/0.46  thf('35', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf(dt_m1_pre_topc, axiom,
% 0.18/0.46    (![A:$i]:
% 0.18/0.46     ( ( l1_pre_topc @ A ) =>
% 0.18/0.46       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.18/0.46  thf('36', plain,
% 0.18/0.46      (![X17 : $i, X18 : $i]:
% 0.18/0.46         (~ (m1_pre_topc @ X17 @ X18)
% 0.18/0.46          | (l1_pre_topc @ X17)
% 0.18/0.46          | ~ (l1_pre_topc @ X18))),
% 0.18/0.46      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.18/0.46  thf('37', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 0.18/0.46      inference('sup-', [status(thm)], ['35', '36'])).
% 0.18/0.46  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('39', plain, ((l1_pre_topc @ sk_C)),
% 0.18/0.46      inference('demod', [status(thm)], ['37', '38'])).
% 0.18/0.46  thf('40', plain,
% 0.18/0.46      (((v2_struct_0 @ sk_B)
% 0.18/0.46        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_C @ sk_D) = (sk_D))
% 0.18/0.46        | (v2_struct_0 @ sk_A))),
% 0.18/0.46      inference('demod', [status(thm)], ['34', '39'])).
% 0.18/0.46  thf('41', plain, (~ (v2_struct_0 @ sk_B)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('42', plain,
% 0.18/0.46      (((v2_struct_0 @ sk_A)
% 0.18/0.46        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_C @ sk_D) = (sk_D)))),
% 0.18/0.46      inference('clc', [status(thm)], ['40', '41'])).
% 0.18/0.46  thf('43', plain, (~ (v2_struct_0 @ sk_A)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('44', plain, (((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_C @ sk_D) = (sk_D))),
% 0.18/0.46      inference('clc', [status(thm)], ['42', '43'])).
% 0.18/0.46  thf('45', plain,
% 0.18/0.46      ((m1_subset_1 @ sk_D @ 
% 0.18/0.46        (k1_zfmisc_1 @ 
% 0.18/0.46         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf(redefinition_r2_funct_2, axiom,
% 0.18/0.46    (![A:$i,B:$i,C:$i,D:$i]:
% 0.18/0.46     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.18/0.46         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.18/0.46         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.18/0.46         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.18/0.46       ( ( r2_funct_2 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.18/0.46  thf('46', plain,
% 0.18/0.46      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.18/0.46         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 0.18/0.46          | ~ (v1_funct_2 @ X13 @ X14 @ X15)
% 0.18/0.46          | ~ (v1_funct_1 @ X13)
% 0.18/0.46          | ~ (v1_funct_1 @ X16)
% 0.18/0.46          | ~ (v1_funct_2 @ X16 @ X14 @ X15)
% 0.18/0.46          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 0.18/0.46          | (r2_funct_2 @ X14 @ X15 @ X13 @ X16)
% 0.18/0.46          | ((X13) != (X16)))),
% 0.18/0.46      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 0.18/0.46  thf('47', plain,
% 0.18/0.46      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.18/0.46         ((r2_funct_2 @ X14 @ X15 @ X16 @ X16)
% 0.18/0.46          | ~ (v1_funct_1 @ X16)
% 0.18/0.46          | ~ (v1_funct_2 @ X16 @ X14 @ X15)
% 0.18/0.46          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.18/0.46      inference('simplify', [status(thm)], ['46'])).
% 0.18/0.46  thf('48', plain,
% 0.18/0.46      ((~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.18/0.46        | ~ (v1_funct_1 @ sk_D)
% 0.18/0.46        | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_D @ 
% 0.18/0.46           sk_D))),
% 0.18/0.46      inference('sup-', [status(thm)], ['45', '47'])).
% 0.18/0.46  thf('49', plain,
% 0.18/0.46      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('50', plain, ((v1_funct_1 @ sk_D)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('51', plain,
% 0.18/0.46      ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_D @ sk_D)),
% 0.18/0.46      inference('demod', [status(thm)], ['48', '49', '50'])).
% 0.18/0.46  thf('52', plain, ($false),
% 0.18/0.46      inference('demod', [status(thm)], ['0', '44', '51'])).
% 0.18/0.46  
% 0.18/0.46  % SZS output end Refutation
% 0.18/0.46  
% 0.18/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
