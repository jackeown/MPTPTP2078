%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yV1Od8TBw4

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:47 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 189 expanded)
%              Number of leaves         :   32 (  71 expanded)
%              Depth                    :   16
%              Number of atoms          :  927 (5367 expanded)
%              Number of equality atoms :   28 ( 107 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t61_tmap_1,conjecture,(
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
                      ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                     => ( ( r1_tarski @ E @ ( u1_struct_0 @ C ) )
                       => ( ( k7_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ D @ E )
                          = ( k7_relset_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ ( k2_tmap_1 @ B @ A @ D @ C ) @ E ) ) ) ) ) ) ) ) )).

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
                        ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                       => ( ( r1_tarski @ E @ ( u1_struct_0 @ C ) )
                         => ( ( k7_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ D @ E )
                            = ( k7_relset_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ ( k2_tmap_1 @ B @ A @ D @ C ) @ E ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t61_tmap_1])).

thf('0',plain,(
    r1_tarski @ sk_E @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t162_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( r1_tarski @ B @ C )
         => ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B )
            = ( k9_relat_1 @ A @ B ) ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 )
        = ( k9_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t162_relat_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X0 @ ( u1_struct_0 @ sk_C ) ) @ sk_E )
        = ( k9_relat_1 @ X0 @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ( k7_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_E )
 != ( k7_relset_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C ) @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('5',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) )
      | ( ( k7_relset_1 @ X7 @ X8 @ X6 @ X9 )
        = ( k9_relat_1 @ X6 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ( k9_relat_1 @ sk_D @ sk_E )
 != ( k7_relset_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C ) @ sk_E ) ),
    inference(demod,[status(thm)],['3','6'])).

thf('8',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
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

thf('10',plain,(
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

thf('11',plain,(
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
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('17',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ( ( k2_partfun1 @ X11 @ X12 @ X10 @ X13 )
        = ( k7_relat_1 @ X10 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 )
        = ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 )
        = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['11','12','13','14','15','20','21','22'])).

thf('24',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
      = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['8','23'])).

thf('25',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
      = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
    = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('29',plain,(
    ( k9_relat_1 @ sk_D @ sk_E )
 != ( k7_relset_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ sk_E ) ),
    inference(demod,[status(thm)],['7','28'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('30',plain,(
    ! [X14: $i] :
      ( ( l1_struct_0 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('31',plain,
    ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
    = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('32',plain,(
    ! [X14: $i] :
      ( ( l1_struct_0 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('33',plain,(
    ! [X14: $i] :
      ( ( l1_struct_0 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('34',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
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

thf('35',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X23 ) ) ) )
      | ~ ( v1_funct_2 @ X21 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X23 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( l1_struct_0 @ X23 )
      | ~ ( l1_struct_0 @ X22 )
      | ~ ( l1_struct_0 @ X24 )
      | ( m1_subset_1 @ ( k2_tmap_1 @ X22 @ X23 @ X21 @ X24 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X23 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tmap_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_B )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['33','39'])).

thf('41',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( m1_subset_1 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','42'])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['31','45'])).

thf('47',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['30','46'])).

thf('48',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('49',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_pre_topc @ X15 @ X16 )
      | ( l1_pre_topc @ X15 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('50',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['47','52'])).

thf('54',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) )
      | ( ( k7_relset_1 @ X7 @ X8 @ X6 @ X9 )
        = ( k9_relat_1 @ X6 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ X0 )
      = ( k9_relat_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ( k9_relat_1 @ sk_D @ sk_E )
 != ( k9_relat_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ sk_E ) ),
    inference(demod,[status(thm)],['29','55'])).

thf('57',plain,
    ( ( ( k9_relat_1 @ sk_D @ sk_E )
     != ( k9_relat_1 @ sk_D @ sk_E ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['2','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('59',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( v1_relat_1 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('60',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ( k9_relat_1 @ sk_D @ sk_E )
 != ( k9_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['57','60'])).

thf('62',plain,(
    $false ),
    inference(simplify,[status(thm)],['61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yV1Od8TBw4
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:01:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.48  % Solved by: fo/fo7.sh
% 0.19/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.48  % done 41 iterations in 0.025s
% 0.19/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.48  % SZS output start Refutation
% 0.19/0.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.19/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.48  thf(sk_D_type, type, sk_D: $i).
% 0.19/0.48  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.19/0.48  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.19/0.48  thf(sk_E_type, type, sk_E: $i).
% 0.19/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.48  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.48  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.19/0.48  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.19/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.48  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.19/0.48  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.19/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.48  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.19/0.48  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.19/0.48  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.19/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.48  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.19/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.48  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.19/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.48  thf(t61_tmap_1, conjecture,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.48       ( ![B:$i]:
% 0.19/0.48         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.19/0.48             ( l1_pre_topc @ B ) ) =>
% 0.19/0.48           ( ![C:$i]:
% 0.19/0.48             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.19/0.48               ( ![D:$i]:
% 0.19/0.48                 ( ( ( v1_funct_1 @ D ) & 
% 0.19/0.48                     ( v1_funct_2 @
% 0.19/0.48                       D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.19/0.48                     ( m1_subset_1 @
% 0.19/0.48                       D @ 
% 0.19/0.48                       ( k1_zfmisc_1 @
% 0.19/0.48                         ( k2_zfmisc_1 @
% 0.19/0.48                           ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.19/0.48                   ( ![E:$i]:
% 0.19/0.48                     ( ( m1_subset_1 @
% 0.19/0.48                         E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.19/0.48                       ( ( r1_tarski @ E @ ( u1_struct_0 @ C ) ) =>
% 0.19/0.48                         ( ( k7_relset_1 @
% 0.19/0.48                             ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ D @ E ) =
% 0.19/0.48                           ( k7_relset_1 @
% 0.19/0.48                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ 
% 0.19/0.48                             ( k2_tmap_1 @ B @ A @ D @ C ) @ E ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.48    (~( ![A:$i]:
% 0.19/0.48        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.19/0.48            ( l1_pre_topc @ A ) ) =>
% 0.19/0.48          ( ![B:$i]:
% 0.19/0.48            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.19/0.48                ( l1_pre_topc @ B ) ) =>
% 0.19/0.48              ( ![C:$i]:
% 0.19/0.48                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.19/0.48                  ( ![D:$i]:
% 0.19/0.48                    ( ( ( v1_funct_1 @ D ) & 
% 0.19/0.48                        ( v1_funct_2 @
% 0.19/0.48                          D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.19/0.48                        ( m1_subset_1 @
% 0.19/0.48                          D @ 
% 0.19/0.48                          ( k1_zfmisc_1 @
% 0.19/0.48                            ( k2_zfmisc_1 @
% 0.19/0.48                              ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.19/0.48                      ( ![E:$i]:
% 0.19/0.48                        ( ( m1_subset_1 @
% 0.19/0.48                            E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.19/0.48                          ( ( r1_tarski @ E @ ( u1_struct_0 @ C ) ) =>
% 0.19/0.48                            ( ( k7_relset_1 @
% 0.19/0.48                                ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.19/0.48                                D @ E ) =
% 0.19/0.48                              ( k7_relset_1 @
% 0.19/0.48                                ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ 
% 0.19/0.48                                ( k2_tmap_1 @ B @ A @ D @ C ) @ E ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.19/0.48    inference('cnf.neg', [status(esa)], [t61_tmap_1])).
% 0.19/0.48  thf('0', plain, ((r1_tarski @ sk_E @ (u1_struct_0 @ sk_C))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(t162_relat_1, axiom,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( v1_relat_1 @ A ) =>
% 0.19/0.48       ( ![B:$i,C:$i]:
% 0.19/0.48         ( ( r1_tarski @ B @ C ) =>
% 0.19/0.48           ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B ) =
% 0.19/0.48             ( k9_relat_1 @ A @ B ) ) ) ) ))).
% 0.19/0.48  thf('1', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.48         (~ (r1_tarski @ X0 @ X1)
% 0.19/0.48          | ((k9_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0)
% 0.19/0.48              = (k9_relat_1 @ X2 @ X0))
% 0.19/0.48          | ~ (v1_relat_1 @ X2))),
% 0.19/0.48      inference('cnf', [status(esa)], [t162_relat_1])).
% 0.19/0.48  thf('2', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (~ (v1_relat_1 @ X0)
% 0.19/0.48          | ((k9_relat_1 @ (k7_relat_1 @ X0 @ (u1_struct_0 @ sk_C)) @ sk_E)
% 0.19/0.48              = (k9_relat_1 @ X0 @ sk_E)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['0', '1'])).
% 0.19/0.48  thf('3', plain,
% 0.19/0.48      (((k7_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.19/0.48         sk_E)
% 0.19/0.48         != (k7_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.48             (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C) @ sk_E))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('4', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_D @ 
% 0.19/0.48        (k1_zfmisc_1 @ 
% 0.19/0.48         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(redefinition_k7_relset_1, axiom,
% 0.19/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.48       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.19/0.48  thf('5', plain,
% 0.19/0.48      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.19/0.48         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8)))
% 0.19/0.48          | ((k7_relset_1 @ X7 @ X8 @ X6 @ X9) = (k9_relat_1 @ X6 @ X9)))),
% 0.19/0.48      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.19/0.48  thf('6', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         ((k7_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.19/0.48           X0) = (k9_relat_1 @ sk_D @ X0))),
% 0.19/0.48      inference('sup-', [status(thm)], ['4', '5'])).
% 0.19/0.48  thf('7', plain,
% 0.19/0.48      (((k9_relat_1 @ sk_D @ sk_E)
% 0.19/0.48         != (k7_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.48             (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C) @ sk_E))),
% 0.19/0.48      inference('demod', [status(thm)], ['3', '6'])).
% 0.19/0.48  thf('8', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('9', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_D @ 
% 0.19/0.48        (k1_zfmisc_1 @ 
% 0.19/0.48         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(d4_tmap_1, axiom,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.48       ( ![B:$i]:
% 0.19/0.48         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.19/0.48             ( l1_pre_topc @ B ) ) =>
% 0.19/0.48           ( ![C:$i]:
% 0.19/0.48             ( ( ( v1_funct_1 @ C ) & 
% 0.19/0.48                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.19/0.48                 ( m1_subset_1 @
% 0.19/0.48                   C @ 
% 0.19/0.48                   ( k1_zfmisc_1 @
% 0.19/0.48                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.19/0.48               ( ![D:$i]:
% 0.19/0.48                 ( ( m1_pre_topc @ D @ A ) =>
% 0.19/0.48                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 0.19/0.48                     ( k2_partfun1 @
% 0.19/0.48                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.19/0.48                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.48  thf('10', plain,
% 0.19/0.48      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.19/0.48         ((v2_struct_0 @ X17)
% 0.19/0.48          | ~ (v2_pre_topc @ X17)
% 0.19/0.48          | ~ (l1_pre_topc @ X17)
% 0.19/0.48          | ~ (m1_pre_topc @ X18 @ X19)
% 0.19/0.48          | ((k2_tmap_1 @ X19 @ X17 @ X20 @ X18)
% 0.19/0.48              = (k2_partfun1 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X17) @ 
% 0.19/0.48                 X20 @ (u1_struct_0 @ X18)))
% 0.19/0.48          | ~ (m1_subset_1 @ X20 @ 
% 0.19/0.48               (k1_zfmisc_1 @ 
% 0.19/0.48                (k2_zfmisc_1 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X17))))
% 0.19/0.48          | ~ (v1_funct_2 @ X20 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X17))
% 0.19/0.48          | ~ (v1_funct_1 @ X20)
% 0.19/0.48          | ~ (l1_pre_topc @ X19)
% 0.19/0.48          | ~ (v2_pre_topc @ X19)
% 0.19/0.48          | (v2_struct_0 @ X19))),
% 0.19/0.48      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.19/0.48  thf('11', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         ((v2_struct_0 @ sk_B)
% 0.19/0.48          | ~ (v2_pre_topc @ sk_B)
% 0.19/0.48          | ~ (l1_pre_topc @ sk_B)
% 0.19/0.48          | ~ (v1_funct_1 @ sk_D)
% 0.19/0.48          | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.19/0.48          | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0)
% 0.19/0.48              = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.48                 sk_D @ (u1_struct_0 @ X0)))
% 0.19/0.48          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.19/0.48          | ~ (l1_pre_topc @ sk_A)
% 0.19/0.48          | ~ (v2_pre_topc @ sk_A)
% 0.19/0.48          | (v2_struct_0 @ sk_A))),
% 0.19/0.48      inference('sup-', [status(thm)], ['9', '10'])).
% 0.19/0.48  thf('12', plain, ((v2_pre_topc @ sk_B)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('13', plain, ((l1_pre_topc @ sk_B)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('14', plain, ((v1_funct_1 @ sk_D)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('15', plain,
% 0.19/0.48      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('16', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_D @ 
% 0.19/0.48        (k1_zfmisc_1 @ 
% 0.19/0.48         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(redefinition_k2_partfun1, axiom,
% 0.19/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.48     ( ( ( v1_funct_1 @ C ) & 
% 0.19/0.48         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.19/0.48       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.19/0.48  thf('17', plain,
% 0.19/0.48      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.19/0.48         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12)))
% 0.19/0.48          | ~ (v1_funct_1 @ X10)
% 0.19/0.48          | ((k2_partfun1 @ X11 @ X12 @ X10 @ X13) = (k7_relat_1 @ X10 @ X13)))),
% 0.19/0.48      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.19/0.48  thf('18', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (((k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.19/0.48            X0) = (k7_relat_1 @ sk_D @ X0))
% 0.19/0.48          | ~ (v1_funct_1 @ sk_D))),
% 0.19/0.48      inference('sup-', [status(thm)], ['16', '17'])).
% 0.19/0.48  thf('19', plain, ((v1_funct_1 @ sk_D)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('20', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         ((k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.19/0.48           X0) = (k7_relat_1 @ sk_D @ X0))),
% 0.19/0.48      inference('demod', [status(thm)], ['18', '19'])).
% 0.19/0.48  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('22', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('23', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         ((v2_struct_0 @ sk_B)
% 0.19/0.48          | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0)
% 0.19/0.48              = (k7_relat_1 @ sk_D @ (u1_struct_0 @ X0)))
% 0.19/0.48          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.19/0.48          | (v2_struct_0 @ sk_A))),
% 0.19/0.48      inference('demod', [status(thm)],
% 0.19/0.48                ['11', '12', '13', '14', '15', '20', '21', '22'])).
% 0.19/0.48  thf('24', plain,
% 0.19/0.48      (((v2_struct_0 @ sk_A)
% 0.19/0.48        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.19/0.48            = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)))
% 0.19/0.48        | (v2_struct_0 @ sk_B))),
% 0.19/0.48      inference('sup-', [status(thm)], ['8', '23'])).
% 0.19/0.48  thf('25', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('26', plain,
% 0.19/0.48      (((v2_struct_0 @ sk_B)
% 0.19/0.48        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.19/0.48            = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C))))),
% 0.19/0.48      inference('clc', [status(thm)], ['24', '25'])).
% 0.19/0.48  thf('27', plain, (~ (v2_struct_0 @ sk_B)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('28', plain,
% 0.19/0.48      (((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.19/0.48         = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)))),
% 0.19/0.48      inference('clc', [status(thm)], ['26', '27'])).
% 0.19/0.48  thf('29', plain,
% 0.19/0.48      (((k9_relat_1 @ sk_D @ sk_E)
% 0.19/0.48         != (k7_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.48             (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ sk_E))),
% 0.19/0.48      inference('demod', [status(thm)], ['7', '28'])).
% 0.19/0.48  thf(dt_l1_pre_topc, axiom,
% 0.19/0.48    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.19/0.48  thf('30', plain,
% 0.19/0.48      (![X14 : $i]: ((l1_struct_0 @ X14) | ~ (l1_pre_topc @ X14))),
% 0.19/0.48      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.19/0.48  thf('31', plain,
% 0.19/0.48      (((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.19/0.48         = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)))),
% 0.19/0.48      inference('clc', [status(thm)], ['26', '27'])).
% 0.19/0.48  thf('32', plain,
% 0.19/0.48      (![X14 : $i]: ((l1_struct_0 @ X14) | ~ (l1_pre_topc @ X14))),
% 0.19/0.48      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.19/0.48  thf('33', plain,
% 0.19/0.48      (![X14 : $i]: ((l1_struct_0 @ X14) | ~ (l1_pre_topc @ X14))),
% 0.19/0.48      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.19/0.48  thf('34', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_D @ 
% 0.19/0.48        (k1_zfmisc_1 @ 
% 0.19/0.48         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(dt_k2_tmap_1, axiom,
% 0.19/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.48     ( ( ( l1_struct_0 @ A ) & ( l1_struct_0 @ B ) & ( v1_funct_1 @ C ) & 
% 0.19/0.48         ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.19/0.48         ( m1_subset_1 @
% 0.19/0.48           C @ 
% 0.19/0.48           ( k1_zfmisc_1 @
% 0.19/0.48             ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 0.19/0.48         ( l1_struct_0 @ D ) ) =>
% 0.19/0.48       ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) ) & 
% 0.19/0.48         ( v1_funct_2 @
% 0.19/0.48           ( k2_tmap_1 @ A @ B @ C @ D ) @ ( u1_struct_0 @ D ) @ 
% 0.19/0.48           ( u1_struct_0 @ B ) ) & 
% 0.19/0.48         ( m1_subset_1 @
% 0.19/0.48           ( k2_tmap_1 @ A @ B @ C @ D ) @ 
% 0.19/0.48           ( k1_zfmisc_1 @
% 0.19/0.48             ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.19/0.48  thf('35', plain,
% 0.19/0.48      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.19/0.48         (~ (m1_subset_1 @ X21 @ 
% 0.19/0.48             (k1_zfmisc_1 @ 
% 0.19/0.48              (k2_zfmisc_1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X23))))
% 0.19/0.48          | ~ (v1_funct_2 @ X21 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X23))
% 0.19/0.48          | ~ (v1_funct_1 @ X21)
% 0.19/0.48          | ~ (l1_struct_0 @ X23)
% 0.19/0.48          | ~ (l1_struct_0 @ X22)
% 0.19/0.48          | ~ (l1_struct_0 @ X24)
% 0.19/0.48          | (m1_subset_1 @ (k2_tmap_1 @ X22 @ X23 @ X21 @ X24) @ 
% 0.19/0.48             (k1_zfmisc_1 @ 
% 0.19/0.48              (k2_zfmisc_1 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X23)))))),
% 0.19/0.48      inference('cnf', [status(esa)], [dt_k2_tmap_1])).
% 0.19/0.48  thf('36', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         ((m1_subset_1 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0) @ 
% 0.19/0.48           (k1_zfmisc_1 @ 
% 0.19/0.48            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 0.19/0.48          | ~ (l1_struct_0 @ X0)
% 0.19/0.48          | ~ (l1_struct_0 @ sk_B)
% 0.19/0.48          | ~ (l1_struct_0 @ sk_A)
% 0.19/0.48          | ~ (v1_funct_1 @ sk_D)
% 0.19/0.48          | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['34', '35'])).
% 0.19/0.48  thf('37', plain, ((v1_funct_1 @ sk_D)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('38', plain,
% 0.19/0.48      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('39', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         ((m1_subset_1 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0) @ 
% 0.19/0.48           (k1_zfmisc_1 @ 
% 0.19/0.48            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 0.19/0.48          | ~ (l1_struct_0 @ X0)
% 0.19/0.48          | ~ (l1_struct_0 @ sk_B)
% 0.19/0.48          | ~ (l1_struct_0 @ sk_A))),
% 0.19/0.48      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.19/0.48  thf('40', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (~ (l1_pre_topc @ sk_B)
% 0.19/0.48          | ~ (l1_struct_0 @ sk_A)
% 0.19/0.48          | ~ (l1_struct_0 @ X0)
% 0.19/0.48          | (m1_subset_1 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0) @ 
% 0.19/0.48             (k1_zfmisc_1 @ 
% 0.19/0.48              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A)))))),
% 0.19/0.48      inference('sup-', [status(thm)], ['33', '39'])).
% 0.19/0.48  thf('41', plain, ((l1_pre_topc @ sk_B)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('42', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (~ (l1_struct_0 @ sk_A)
% 0.19/0.48          | ~ (l1_struct_0 @ X0)
% 0.19/0.48          | (m1_subset_1 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0) @ 
% 0.19/0.48             (k1_zfmisc_1 @ 
% 0.19/0.48              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A)))))),
% 0.19/0.48      inference('demod', [status(thm)], ['40', '41'])).
% 0.19/0.48  thf('43', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (~ (l1_pre_topc @ sk_A)
% 0.19/0.48          | (m1_subset_1 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0) @ 
% 0.19/0.48             (k1_zfmisc_1 @ 
% 0.19/0.48              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 0.19/0.48          | ~ (l1_struct_0 @ X0))),
% 0.19/0.48      inference('sup-', [status(thm)], ['32', '42'])).
% 0.19/0.48  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('45', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         ((m1_subset_1 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0) @ 
% 0.19/0.48           (k1_zfmisc_1 @ 
% 0.19/0.48            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 0.19/0.48          | ~ (l1_struct_0 @ X0))),
% 0.19/0.48      inference('demod', [status(thm)], ['43', '44'])).
% 0.19/0.48  thf('46', plain,
% 0.19/0.48      (((m1_subset_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.19/0.48         (k1_zfmisc_1 @ 
% 0.19/0.48          (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))
% 0.19/0.48        | ~ (l1_struct_0 @ sk_C))),
% 0.19/0.48      inference('sup+', [status(thm)], ['31', '45'])).
% 0.19/0.48  thf('47', plain,
% 0.19/0.48      ((~ (l1_pre_topc @ sk_C)
% 0.19/0.48        | (m1_subset_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.19/0.48           (k1_zfmisc_1 @ 
% 0.19/0.48            (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A)))))),
% 0.19/0.48      inference('sup-', [status(thm)], ['30', '46'])).
% 0.19/0.48  thf('48', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(dt_m1_pre_topc, axiom,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( l1_pre_topc @ A ) =>
% 0.19/0.48       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.19/0.48  thf('49', plain,
% 0.19/0.48      (![X15 : $i, X16 : $i]:
% 0.19/0.48         (~ (m1_pre_topc @ X15 @ X16)
% 0.19/0.48          | (l1_pre_topc @ X15)
% 0.19/0.48          | ~ (l1_pre_topc @ X16))),
% 0.19/0.48      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.19/0.48  thf('50', plain, ((~ (l1_pre_topc @ sk_B) | (l1_pre_topc @ sk_C))),
% 0.19/0.48      inference('sup-', [status(thm)], ['48', '49'])).
% 0.19/0.48  thf('51', plain, ((l1_pre_topc @ sk_B)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('52', plain, ((l1_pre_topc @ sk_C)),
% 0.19/0.48      inference('demod', [status(thm)], ['50', '51'])).
% 0.19/0.48  thf('53', plain,
% 0.19/0.48      ((m1_subset_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.19/0.48        (k1_zfmisc_1 @ 
% 0.19/0.48         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.19/0.48      inference('demod', [status(thm)], ['47', '52'])).
% 0.19/0.48  thf('54', plain,
% 0.19/0.48      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.19/0.48         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8)))
% 0.19/0.48          | ((k7_relset_1 @ X7 @ X8 @ X6 @ X9) = (k9_relat_1 @ X6 @ X9)))),
% 0.19/0.48      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.19/0.48  thf('55', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         ((k7_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.48           (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ X0)
% 0.19/0.48           = (k9_relat_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ X0))),
% 0.19/0.48      inference('sup-', [status(thm)], ['53', '54'])).
% 0.19/0.48  thf('56', plain,
% 0.19/0.48      (((k9_relat_1 @ sk_D @ sk_E)
% 0.19/0.48         != (k9_relat_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ sk_E))),
% 0.19/0.48      inference('demod', [status(thm)], ['29', '55'])).
% 0.19/0.48  thf('57', plain,
% 0.19/0.48      ((((k9_relat_1 @ sk_D @ sk_E) != (k9_relat_1 @ sk_D @ sk_E))
% 0.19/0.48        | ~ (v1_relat_1 @ sk_D))),
% 0.19/0.48      inference('sup-', [status(thm)], ['2', '56'])).
% 0.19/0.48  thf('58', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_D @ 
% 0.19/0.48        (k1_zfmisc_1 @ 
% 0.19/0.48         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(cc1_relset_1, axiom,
% 0.19/0.48    (![A:$i,B:$i,C:$i]:
% 0.19/0.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.48       ( v1_relat_1 @ C ) ))).
% 0.19/0.48  thf('59', plain,
% 0.19/0.48      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.19/0.48         ((v1_relat_1 @ X3)
% 0.19/0.48          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5))))),
% 0.19/0.48      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.19/0.48  thf('60', plain, ((v1_relat_1 @ sk_D)),
% 0.19/0.48      inference('sup-', [status(thm)], ['58', '59'])).
% 0.19/0.48  thf('61', plain,
% 0.19/0.48      (((k9_relat_1 @ sk_D @ sk_E) != (k9_relat_1 @ sk_D @ sk_E))),
% 0.19/0.48      inference('demod', [status(thm)], ['57', '60'])).
% 0.19/0.48  thf('62', plain, ($false), inference('simplify', [status(thm)], ['61'])).
% 0.19/0.48  
% 0.19/0.48  % SZS output end Refutation
% 0.19/0.48  
% 0.19/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
