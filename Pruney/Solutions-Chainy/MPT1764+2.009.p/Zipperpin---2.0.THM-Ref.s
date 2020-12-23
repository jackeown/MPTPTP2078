%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DTtGqGEknH

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:05 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 214 expanded)
%              Number of leaves         :   31 (  77 expanded)
%              Depth                    :   19
%              Number of atoms          : 1101 (7509 expanded)
%              Number of equality atoms :   31 ( 131 expanded)
%              Maximal formula depth    :   24 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t75_tmap_1,conjecture,(
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
                            ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ D ) ) )
                           => ( ( r1_tarski @ F @ ( u1_struct_0 @ C ) )
                             => ( ( k7_relset_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) @ E @ F )
                                = ( k7_relset_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ F ) ) ) ) ) ) ) ) ) ) )).

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
                              ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ D ) ) )
                             => ( ( r1_tarski @ F @ ( u1_struct_0 @ C ) )
                               => ( ( k7_relset_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) @ E @ F )
                                  = ( k7_relset_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ F ) ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t75_tmap_1])).

thf('0',plain,(
    r1_tarski @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t174_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( r1_tarski @ C @ B )
         => ( ( k9_relat_1 @ A @ C )
            = ( k9_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) )).

thf('1',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X12 @ X13 )
      | ( ( k9_relat_1 @ X14 @ X12 )
        = ( k9_relat_1 @ ( k7_relat_1 @ X14 @ X13 ) @ X12 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t174_funct_2])).

thf('2',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ sk_F )
        = ( k9_relat_1 @ ( k7_relat_1 @ X0 @ ( u1_struct_0 @ sk_C ) ) @ sk_F ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ( k7_relset_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ sk_F )
 != ( k7_relset_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('5',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) )
      | ( ( k7_relset_1 @ X5 @ X6 @ X4 @ X7 )
        = ( k9_relat_1 @ X4 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ X0 )
      = ( k9_relat_1 @ sk_E @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ( k9_relat_1 @ sk_E @ sk_F )
 != ( k7_relset_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_F ) ),
    inference(demod,[status(thm)],['3','6'])).

thf('8',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
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

thf('11',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( v2_struct_0 @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( m1_pre_topc @ X16 @ X17 )
      | ~ ( m1_pre_topc @ X16 @ X18 )
      | ( ( k3_tmap_1 @ X17 @ X15 @ X18 @ X16 @ X19 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X15 ) @ X19 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X15 ) ) ) )
      | ~ ( v1_funct_2 @ X19 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X15 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( m1_pre_topc @ X18 @ X17 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d5_tmap_1])).

thf('12',plain,(
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
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('16',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ( ( k2_partfun1 @ X9 @ X10 @ X8 @ X11 )
        = ( k7_relat_1 @ X8 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ X0 )
        = ( k7_relat_1 @ sk_E @ X0 ) )
      | ~ ( v1_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E )
        = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['12','13','14','19','20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_E )
        = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_E )
        = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
      = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['8','26'])).

thf('28',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
      = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
      = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('32',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,(
    ( k9_relat_1 @ sk_E @ sk_F )
 != ( k7_relset_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) @ sk_F ) ),
    inference(demod,[status(thm)],['7','33'])).

thf('35',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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

thf('38',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_pre_topc @ X20 @ X21 )
      | ~ ( m1_pre_topc @ X22 @ X21 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_2 @ X24 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X23 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X23 ) ) ) )
      | ( m1_subset_1 @ ( k3_tmap_1 @ X21 @ X23 @ X22 @ X20 @ X24 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X23 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_tmap_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['39','40','41','42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['36','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,
    ( ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['35','48'])).

thf('50',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('51',plain,
    ( ( m1_subset_1 @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) )
      | ( ( k7_relset_1 @ X5 @ X6 @ X4 @ X7 )
        = ( k9_relat_1 @ X4 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) @ X0 )
      = ( k9_relat_1 @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ( k9_relat_1 @ sk_E @ sk_F )
 != ( k9_relat_1 @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) @ sk_F ) ),
    inference(demod,[status(thm)],['34','57'])).

thf('59',plain,
    ( ( ( k9_relat_1 @ sk_E @ sk_F )
     != ( k9_relat_1 @ sk_E @ sk_F ) )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['2','58'])).

thf('60',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('63',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('64',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('65',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ( k9_relat_1 @ sk_E @ sk_F )
 != ( k9_relat_1 @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['59','60','65'])).

thf('67',plain,(
    $false ),
    inference(simplify,[status(thm)],['66'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DTtGqGEknH
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:50:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 43 iterations in 0.017s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.21/0.47  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.21/0.47  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.47  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.47  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.47  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.47  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.21/0.47  thf(sk_E_type, type, sk_E: $i).
% 0.21/0.47  thf(sk_F_type, type, sk_F: $i).
% 0.21/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.47  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.21/0.47  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.47  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.47  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.21/0.47  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.47  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.21/0.47  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(t75_tmap_1, conjecture,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.47             ( l1_pre_topc @ B ) ) =>
% 0.21/0.47           ( ![C:$i]:
% 0.21/0.47             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.21/0.47               ( ![D:$i]:
% 0.21/0.47                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.21/0.47                   ( ![E:$i]:
% 0.21/0.47                     ( ( ( v1_funct_1 @ E ) & 
% 0.21/0.47                         ( v1_funct_2 @
% 0.21/0.47                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.47                         ( m1_subset_1 @
% 0.21/0.47                           E @ 
% 0.21/0.47                           ( k1_zfmisc_1 @
% 0.21/0.47                             ( k2_zfmisc_1 @
% 0.21/0.47                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.47                       ( ( m1_pre_topc @ C @ D ) =>
% 0.21/0.47                         ( ![F:$i]:
% 0.21/0.47                           ( ( m1_subset_1 @
% 0.21/0.47                               F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ D ) ) ) =>
% 0.21/0.47                             ( ( r1_tarski @ F @ ( u1_struct_0 @ C ) ) =>
% 0.21/0.47                               ( ( k7_relset_1 @
% 0.21/0.47                                   ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) @ 
% 0.21/0.47                                   E @ F ) =
% 0.21/0.47                                 ( k7_relset_1 @
% 0.21/0.47                                   ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ 
% 0.21/0.47                                   ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i]:
% 0.21/0.47        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.47            ( l1_pre_topc @ A ) ) =>
% 0.21/0.47          ( ![B:$i]:
% 0.21/0.47            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.47                ( l1_pre_topc @ B ) ) =>
% 0.21/0.47              ( ![C:$i]:
% 0.21/0.47                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.21/0.47                  ( ![D:$i]:
% 0.21/0.47                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.21/0.47                      ( ![E:$i]:
% 0.21/0.47                        ( ( ( v1_funct_1 @ E ) & 
% 0.21/0.47                            ( v1_funct_2 @
% 0.21/0.47                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.47                            ( m1_subset_1 @
% 0.21/0.47                              E @ 
% 0.21/0.47                              ( k1_zfmisc_1 @
% 0.21/0.47                                ( k2_zfmisc_1 @
% 0.21/0.47                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.47                          ( ( m1_pre_topc @ C @ D ) =>
% 0.21/0.47                            ( ![F:$i]:
% 0.21/0.47                              ( ( m1_subset_1 @
% 0.21/0.47                                  F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ D ) ) ) =>
% 0.21/0.47                                ( ( r1_tarski @ F @ ( u1_struct_0 @ C ) ) =>
% 0.21/0.47                                  ( ( k7_relset_1 @
% 0.21/0.47                                      ( u1_struct_0 @ D ) @ 
% 0.21/0.47                                      ( u1_struct_0 @ B ) @ E @ F ) =
% 0.21/0.47                                    ( k7_relset_1 @
% 0.21/0.47                                      ( u1_struct_0 @ C ) @ 
% 0.21/0.47                                      ( u1_struct_0 @ B ) @ 
% 0.21/0.47                                      ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t75_tmap_1])).
% 0.21/0.47  thf('0', plain, ((r1_tarski @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(t174_funct_2, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.47       ( ![B:$i,C:$i]:
% 0.21/0.47         ( ( r1_tarski @ C @ B ) =>
% 0.21/0.47           ( ( k9_relat_1 @ A @ C ) =
% 0.21/0.47             ( k9_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ))).
% 0.21/0.47  thf('1', plain,
% 0.21/0.47      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.47         (~ (r1_tarski @ X12 @ X13)
% 0.21/0.47          | ((k9_relat_1 @ X14 @ X12)
% 0.21/0.47              = (k9_relat_1 @ (k7_relat_1 @ X14 @ X13) @ X12))
% 0.21/0.47          | ~ (v1_funct_1 @ X14)
% 0.21/0.47          | ~ (v1_relat_1 @ X14))),
% 0.21/0.47      inference('cnf', [status(esa)], [t174_funct_2])).
% 0.21/0.47  thf('2', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (v1_relat_1 @ X0)
% 0.21/0.47          | ~ (v1_funct_1 @ X0)
% 0.21/0.47          | ((k9_relat_1 @ X0 @ sk_F)
% 0.21/0.47              = (k9_relat_1 @ (k7_relat_1 @ X0 @ (u1_struct_0 @ sk_C)) @ sk_F)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.47  thf('3', plain,
% 0.21/0.47      (((k7_relset_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.21/0.47         sk_F)
% 0.21/0.47         != (k7_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.47             (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('4', plain,
% 0.21/0.47      ((m1_subset_1 @ sk_E @ 
% 0.21/0.47        (k1_zfmisc_1 @ 
% 0.21/0.47         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(redefinition_k7_relset_1, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.47       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.21/0.47  thf('5', plain,
% 0.21/0.47      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.47         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6)))
% 0.21/0.47          | ((k7_relset_1 @ X5 @ X6 @ X4 @ X7) = (k9_relat_1 @ X4 @ X7)))),
% 0.21/0.47      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.21/0.47  thf('6', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((k7_relset_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.21/0.47           X0) = (k9_relat_1 @ sk_E @ X0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.47  thf('7', plain,
% 0.21/0.47      (((k9_relat_1 @ sk_E @ sk_F)
% 0.21/0.47         != (k7_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.47             (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F))),
% 0.21/0.47      inference('demod', [status(thm)], ['3', '6'])).
% 0.21/0.47  thf('8', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('9', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('10', plain,
% 0.21/0.47      ((m1_subset_1 @ sk_E @ 
% 0.21/0.47        (k1_zfmisc_1 @ 
% 0.21/0.47         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(d5_tmap_1, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.47             ( l1_pre_topc @ B ) ) =>
% 0.21/0.47           ( ![C:$i]:
% 0.21/0.47             ( ( m1_pre_topc @ C @ A ) =>
% 0.21/0.47               ( ![D:$i]:
% 0.21/0.47                 ( ( m1_pre_topc @ D @ A ) =>
% 0.21/0.47                   ( ![E:$i]:
% 0.21/0.47                     ( ( ( v1_funct_1 @ E ) & 
% 0.21/0.47                         ( v1_funct_2 @
% 0.21/0.47                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.47                         ( m1_subset_1 @
% 0.21/0.47                           E @ 
% 0.21/0.47                           ( k1_zfmisc_1 @
% 0.21/0.47                             ( k2_zfmisc_1 @
% 0.21/0.47                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.47                       ( ( m1_pre_topc @ D @ C ) =>
% 0.21/0.47                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 0.21/0.47                           ( k2_partfun1 @
% 0.21/0.47                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 0.21/0.47                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.47  thf('11', plain,
% 0.21/0.47      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.47         ((v2_struct_0 @ X15)
% 0.21/0.47          | ~ (v2_pre_topc @ X15)
% 0.21/0.47          | ~ (l1_pre_topc @ X15)
% 0.21/0.47          | ~ (m1_pre_topc @ X16 @ X17)
% 0.21/0.47          | ~ (m1_pre_topc @ X16 @ X18)
% 0.21/0.47          | ((k3_tmap_1 @ X17 @ X15 @ X18 @ X16 @ X19)
% 0.21/0.47              = (k2_partfun1 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X15) @ 
% 0.21/0.47                 X19 @ (u1_struct_0 @ X16)))
% 0.21/0.47          | ~ (m1_subset_1 @ X19 @ 
% 0.21/0.47               (k1_zfmisc_1 @ 
% 0.21/0.47                (k2_zfmisc_1 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X15))))
% 0.21/0.47          | ~ (v1_funct_2 @ X19 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X15))
% 0.21/0.47          | ~ (v1_funct_1 @ X19)
% 0.21/0.47          | ~ (m1_pre_topc @ X18 @ X17)
% 0.21/0.47          | ~ (l1_pre_topc @ X17)
% 0.21/0.47          | ~ (v2_pre_topc @ X17)
% 0.21/0.47          | (v2_struct_0 @ X17))),
% 0.21/0.47      inference('cnf', [status(esa)], [d5_tmap_1])).
% 0.21/0.47  thf('12', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         ((v2_struct_0 @ X0)
% 0.21/0.47          | ~ (v2_pre_topc @ X0)
% 0.21/0.47          | ~ (l1_pre_topc @ X0)
% 0.21/0.47          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.21/0.47          | ~ (v1_funct_1 @ sk_E)
% 0.21/0.47          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.21/0.47          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E)
% 0.21/0.47              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.47                 sk_E @ (u1_struct_0 @ X1)))
% 0.21/0.47          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.21/0.47          | ~ (m1_pre_topc @ X1 @ X0)
% 0.21/0.47          | ~ (l1_pre_topc @ sk_B)
% 0.21/0.47          | ~ (v2_pre_topc @ sk_B)
% 0.21/0.47          | (v2_struct_0 @ sk_B))),
% 0.21/0.47      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.47  thf('13', plain, ((v1_funct_1 @ sk_E)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('14', plain,
% 0.21/0.47      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('15', plain,
% 0.21/0.47      ((m1_subset_1 @ sk_E @ 
% 0.21/0.47        (k1_zfmisc_1 @ 
% 0.21/0.47         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(redefinition_k2_partfun1, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.47     ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.47         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.47       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.21/0.47  thf('16', plain,
% 0.21/0.47      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.47         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10)))
% 0.21/0.47          | ~ (v1_funct_1 @ X8)
% 0.21/0.47          | ((k2_partfun1 @ X9 @ X10 @ X8 @ X11) = (k7_relat_1 @ X8 @ X11)))),
% 0.21/0.47      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.21/0.47  thf('17', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (((k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.21/0.47            X0) = (k7_relat_1 @ sk_E @ X0))
% 0.21/0.47          | ~ (v1_funct_1 @ sk_E))),
% 0.21/0.47      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.47  thf('18', plain, ((v1_funct_1 @ sk_E)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('19', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.21/0.47           X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.21/0.47      inference('demod', [status(thm)], ['17', '18'])).
% 0.21/0.47  thf('20', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('21', plain, ((v2_pre_topc @ sk_B)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('22', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         ((v2_struct_0 @ X0)
% 0.21/0.47          | ~ (v2_pre_topc @ X0)
% 0.21/0.47          | ~ (l1_pre_topc @ X0)
% 0.21/0.47          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.21/0.47          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E)
% 0.21/0.47              = (k7_relat_1 @ sk_E @ (u1_struct_0 @ X1)))
% 0.21/0.47          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.21/0.47          | ~ (m1_pre_topc @ X1 @ X0)
% 0.21/0.47          | (v2_struct_0 @ sk_B))),
% 0.21/0.47      inference('demod', [status(thm)], ['12', '13', '14', '19', '20', '21'])).
% 0.21/0.47  thf('23', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((v2_struct_0 @ sk_B)
% 0.21/0.47          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.21/0.47          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.21/0.47          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_E)
% 0.21/0.47              = (k7_relat_1 @ sk_E @ (u1_struct_0 @ X0)))
% 0.21/0.47          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.47          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.47          | (v2_struct_0 @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['9', '22'])).
% 0.21/0.47  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('25', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('26', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((v2_struct_0 @ sk_B)
% 0.21/0.47          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.21/0.47          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.21/0.47          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_E)
% 0.21/0.47              = (k7_relat_1 @ sk_E @ (u1_struct_0 @ X0)))
% 0.21/0.47          | (v2_struct_0 @ sk_A))),
% 0.21/0.47      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.21/0.47  thf('27', plain,
% 0.21/0.47      (((v2_struct_0 @ sk_A)
% 0.21/0.47        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.21/0.47            = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))
% 0.21/0.47        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.21/0.47        | (v2_struct_0 @ sk_B))),
% 0.21/0.47      inference('sup-', [status(thm)], ['8', '26'])).
% 0.21/0.47  thf('28', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('29', plain,
% 0.21/0.47      (((v2_struct_0 @ sk_A)
% 0.21/0.47        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.21/0.47            = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))
% 0.21/0.47        | (v2_struct_0 @ sk_B))),
% 0.21/0.47      inference('demod', [status(thm)], ['27', '28'])).
% 0.21/0.47  thf('30', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('31', plain,
% 0.21/0.47      (((v2_struct_0 @ sk_B)
% 0.21/0.47        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.21/0.47            = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C))))),
% 0.21/0.47      inference('clc', [status(thm)], ['29', '30'])).
% 0.21/0.47  thf('32', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('33', plain,
% 0.21/0.47      (((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.21/0.47         = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))),
% 0.21/0.47      inference('clc', [status(thm)], ['31', '32'])).
% 0.21/0.47  thf('34', plain,
% 0.21/0.47      (((k9_relat_1 @ sk_E @ sk_F)
% 0.21/0.47         != (k7_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.47             (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)) @ sk_F))),
% 0.21/0.47      inference('demod', [status(thm)], ['7', '33'])).
% 0.21/0.47  thf('35', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('36', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('37', plain,
% 0.21/0.47      ((m1_subset_1 @ sk_E @ 
% 0.21/0.47        (k1_zfmisc_1 @ 
% 0.21/0.47         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(dt_k3_tmap_1, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.21/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.47         ( l1_pre_topc @ A ) & ( ~( v2_struct_0 @ B ) ) & 
% 0.21/0.47         ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) & ( m1_pre_topc @ C @ A ) & 
% 0.21/0.47         ( m1_pre_topc @ D @ A ) & ( v1_funct_1 @ E ) & 
% 0.21/0.47         ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.47         ( m1_subset_1 @
% 0.21/0.47           E @ 
% 0.21/0.47           ( k1_zfmisc_1 @
% 0.21/0.47             ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.47       ( ( v1_funct_1 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) ) & 
% 0.21/0.47         ( v1_funct_2 @
% 0.21/0.47           ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ ( u1_struct_0 @ D ) @ 
% 0.21/0.47           ( u1_struct_0 @ B ) ) & 
% 0.21/0.47         ( m1_subset_1 @
% 0.21/0.47           ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ 
% 0.21/0.47           ( k1_zfmisc_1 @
% 0.21/0.47             ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.21/0.47  thf('38', plain,
% 0.21/0.47      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.21/0.47         (~ (m1_pre_topc @ X20 @ X21)
% 0.21/0.47          | ~ (m1_pre_topc @ X22 @ X21)
% 0.21/0.47          | ~ (l1_pre_topc @ X23)
% 0.21/0.47          | ~ (v2_pre_topc @ X23)
% 0.21/0.47          | (v2_struct_0 @ X23)
% 0.21/0.47          | ~ (l1_pre_topc @ X21)
% 0.21/0.47          | ~ (v2_pre_topc @ X21)
% 0.21/0.47          | (v2_struct_0 @ X21)
% 0.21/0.47          | ~ (v1_funct_1 @ X24)
% 0.21/0.47          | ~ (v1_funct_2 @ X24 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X23))
% 0.21/0.47          | ~ (m1_subset_1 @ X24 @ 
% 0.21/0.47               (k1_zfmisc_1 @ 
% 0.21/0.47                (k2_zfmisc_1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X23))))
% 0.21/0.47          | (m1_subset_1 @ (k3_tmap_1 @ X21 @ X23 @ X22 @ X20 @ X24) @ 
% 0.21/0.47             (k1_zfmisc_1 @ 
% 0.21/0.47              (k2_zfmisc_1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X23)))))),
% 0.21/0.47      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 0.21/0.47  thf('39', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         ((m1_subset_1 @ (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_E) @ 
% 0.21/0.47           (k1_zfmisc_1 @ 
% 0.21/0.47            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.21/0.47          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.21/0.47          | ~ (v1_funct_1 @ sk_E)
% 0.21/0.47          | (v2_struct_0 @ X1)
% 0.21/0.47          | ~ (v2_pre_topc @ X1)
% 0.21/0.47          | ~ (l1_pre_topc @ X1)
% 0.21/0.47          | (v2_struct_0 @ sk_B)
% 0.21/0.47          | ~ (v2_pre_topc @ sk_B)
% 0.21/0.47          | ~ (l1_pre_topc @ sk_B)
% 0.21/0.47          | ~ (m1_pre_topc @ sk_D @ X1)
% 0.21/0.47          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.21/0.47      inference('sup-', [status(thm)], ['37', '38'])).
% 0.21/0.47  thf('40', plain,
% 0.21/0.47      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('41', plain, ((v1_funct_1 @ sk_E)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('42', plain, ((v2_pre_topc @ sk_B)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('43', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('44', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         ((m1_subset_1 @ (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_E) @ 
% 0.21/0.47           (k1_zfmisc_1 @ 
% 0.21/0.47            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.21/0.47          | (v2_struct_0 @ X1)
% 0.21/0.47          | ~ (v2_pre_topc @ X1)
% 0.21/0.47          | ~ (l1_pre_topc @ X1)
% 0.21/0.47          | (v2_struct_0 @ sk_B)
% 0.21/0.47          | ~ (m1_pre_topc @ sk_D @ X1)
% 0.21/0.47          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.21/0.47      inference('demod', [status(thm)], ['39', '40', '41', '42', '43'])).
% 0.21/0.47  thf('45', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.21/0.47          | (v2_struct_0 @ sk_B)
% 0.21/0.47          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.47          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.47          | (v2_struct_0 @ sk_A)
% 0.21/0.47          | (m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_E) @ 
% 0.21/0.47             (k1_zfmisc_1 @ 
% 0.21/0.47              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['36', '44'])).
% 0.21/0.47  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('47', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('48', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.21/0.47          | (v2_struct_0 @ sk_B)
% 0.21/0.47          | (v2_struct_0 @ sk_A)
% 0.21/0.47          | (m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_E) @ 
% 0.21/0.47             (k1_zfmisc_1 @ 
% 0.21/0.47              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))))),
% 0.21/0.47      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.21/0.47  thf('49', plain,
% 0.21/0.47      (((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ 
% 0.21/0.47         (k1_zfmisc_1 @ 
% 0.21/0.47          (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 0.21/0.47        | (v2_struct_0 @ sk_A)
% 0.21/0.47        | (v2_struct_0 @ sk_B))),
% 0.21/0.47      inference('sup-', [status(thm)], ['35', '48'])).
% 0.21/0.47  thf('50', plain,
% 0.21/0.47      (((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.21/0.47         = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))),
% 0.21/0.47      inference('clc', [status(thm)], ['31', '32'])).
% 0.21/0.47  thf('51', plain,
% 0.21/0.47      (((m1_subset_1 @ (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)) @ 
% 0.21/0.47         (k1_zfmisc_1 @ 
% 0.21/0.47          (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 0.21/0.47        | (v2_struct_0 @ sk_A)
% 0.21/0.47        | (v2_struct_0 @ sk_B))),
% 0.21/0.47      inference('demod', [status(thm)], ['49', '50'])).
% 0.21/0.47  thf('52', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('53', plain,
% 0.21/0.47      (((v2_struct_0 @ sk_B)
% 0.21/0.47        | (m1_subset_1 @ (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)) @ 
% 0.21/0.47           (k1_zfmisc_1 @ 
% 0.21/0.47            (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))))),
% 0.21/0.47      inference('clc', [status(thm)], ['51', '52'])).
% 0.21/0.47  thf('54', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('55', plain,
% 0.21/0.47      ((m1_subset_1 @ (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)) @ 
% 0.21/0.47        (k1_zfmisc_1 @ 
% 0.21/0.47         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.47      inference('clc', [status(thm)], ['53', '54'])).
% 0.21/0.47  thf('56', plain,
% 0.21/0.47      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.47         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6)))
% 0.21/0.47          | ((k7_relset_1 @ X5 @ X6 @ X4 @ X7) = (k9_relat_1 @ X4 @ X7)))),
% 0.21/0.47      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.21/0.47  thf('57', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((k7_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.47           (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)) @ X0)
% 0.21/0.47           = (k9_relat_1 @ (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)) @ X0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['55', '56'])).
% 0.21/0.47  thf('58', plain,
% 0.21/0.47      (((k9_relat_1 @ sk_E @ sk_F)
% 0.21/0.47         != (k9_relat_1 @ (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)) @ sk_F))),
% 0.21/0.47      inference('demod', [status(thm)], ['34', '57'])).
% 0.21/0.47  thf('59', plain,
% 0.21/0.47      ((((k9_relat_1 @ sk_E @ sk_F) != (k9_relat_1 @ sk_E @ sk_F))
% 0.21/0.47        | ~ (v1_funct_1 @ sk_E)
% 0.21/0.47        | ~ (v1_relat_1 @ sk_E))),
% 0.21/0.47      inference('sup-', [status(thm)], ['2', '58'])).
% 0.21/0.47  thf('60', plain, ((v1_funct_1 @ sk_E)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('61', plain,
% 0.21/0.47      ((m1_subset_1 @ sk_E @ 
% 0.21/0.47        (k1_zfmisc_1 @ 
% 0.21/0.47         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(cc2_relat_1, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( v1_relat_1 @ A ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.21/0.47  thf('62', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.21/0.47          | (v1_relat_1 @ X0)
% 0.21/0.47          | ~ (v1_relat_1 @ X1))),
% 0.21/0.47      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.21/0.47  thf('63', plain,
% 0.21/0.47      ((~ (v1_relat_1 @ 
% 0.21/0.47           (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))
% 0.21/0.47        | (v1_relat_1 @ sk_E))),
% 0.21/0.47      inference('sup-', [status(thm)], ['61', '62'])).
% 0.21/0.47  thf(fc6_relat_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.21/0.47  thf('64', plain,
% 0.21/0.47      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.21/0.47      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.21/0.47  thf('65', plain, ((v1_relat_1 @ sk_E)),
% 0.21/0.47      inference('demod', [status(thm)], ['63', '64'])).
% 0.21/0.47  thf('66', plain,
% 0.21/0.47      (((k9_relat_1 @ sk_E @ sk_F) != (k9_relat_1 @ sk_E @ sk_F))),
% 0.21/0.47      inference('demod', [status(thm)], ['59', '60', '65'])).
% 0.21/0.47  thf('67', plain, ($false), inference('simplify', [status(thm)], ['66'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
