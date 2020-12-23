%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.R4zDEe2REa

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:49 EST 2020

% Result     : Theorem 0.17s
% Output     : Refutation 0.17s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 202 expanded)
%              Number of leaves         :   38 (  79 expanded)
%              Depth                    :   14
%              Number of atoms          :  983 (4584 expanded)
%              Number of equality atoms :   29 (  80 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(t62_tmap_1,conjecture,(
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
                    & ( v1_funct_2 @ D @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
                 => ! [E: $i] :
                      ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                     => ( ( r1_tarski @ ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ D @ E ) @ ( u1_struct_0 @ C ) )
                       => ( ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ D @ E )
                          = ( k8_relset_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ ( k2_tmap_1 @ A @ B @ D @ C ) @ E ) ) ) ) ) ) ) ) )).

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
                      & ( v1_funct_2 @ D @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                      & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
                   => ! [E: $i] :
                        ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                       => ( ( r1_tarski @ ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ D @ E ) @ ( u1_struct_0 @ C ) )
                         => ( ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ D @ E )
                            = ( k8_relset_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ ( k2_tmap_1 @ A @ B @ D @ C ) @ E ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t62_tmap_1])).

thf('0',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_D @ sk_E )
 != ( k8_relset_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ( ( k8_relset_1 @ X20 @ X21 @ X19 @ X22 )
        = ( k10_relat_1 @ X19 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_D @ X0 )
      = ( k10_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ( k10_relat_1 @ sk_D @ sk_E )
 != ( k8_relset_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_E ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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

thf('7',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( v2_struct_0 @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( m1_pre_topc @ X34 @ X35 )
      | ( ( k2_tmap_1 @ X35 @ X33 @ X36 @ X34 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X35 ) @ ( u1_struct_0 @ X33 ) @ X36 @ ( u1_struct_0 @ X34 ) ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X35 ) @ ( u1_struct_0 @ X33 ) ) ) )
      | ~ ( v1_funct_2 @ X36 @ ( u1_struct_0 @ X35 ) @ ( u1_struct_0 @ X33 ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_D @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('14',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( v1_funct_1 @ X26 )
      | ( ( k2_partfun1 @ X27 @ X28 @ X26 @ X29 )
        = ( k7_relat_1 @ X26 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_D @ X0 )
        = ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 )
        = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['8','9','10','11','12','17','18','19'])).

thf('21',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C )
      = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','20'])).

thf('22',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C )
      = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('24',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C )
    = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('27',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('28',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(t88_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ) )).

thf('29',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X8 @ X9 ) @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k7_relat_1 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('34',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v1_relat_1 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('35',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('38',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('39',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X13 @ X14 @ X15 ) @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k7_relat_1 @ sk_D @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('42',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k2_relset_1 @ X17 @ X18 @ X16 )
        = ( k2_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k7_relat_1 @ sk_D @ X0 ) )
      = ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('46',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('47',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X6 @ X7 ) ) @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('48',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X23 ) @ X24 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X23 ) @ X25 )
      | ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( m1_subset_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X2 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('52',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v1_relat_1 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['33','34'])).

thf('55',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['50','53','54'])).

thf('56',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ( ( k8_relset_1 @ X20 @ X21 @ X19 @ X22 )
        = ( k10_relat_1 @ X19 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relset_1 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( k7_relat_1 @ sk_D @ X0 ) @ X1 )
      = ( k10_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    r1_tarski @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_D @ X0 )
      = ( k10_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('60',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['58','59'])).

thf(t175_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B )
         => ( ( k10_relat_1 @ A @ C )
            = ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) )).

thf('61',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( r1_tarski @ ( k10_relat_1 @ X30 @ X31 ) @ X32 )
      | ( ( k10_relat_1 @ X30 @ X31 )
        = ( k10_relat_1 @ ( k7_relat_1 @ X30 @ X32 ) @ X31 ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t175_funct_2])).

thf('62',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( ( k10_relat_1 @ sk_D @ sk_E )
      = ( k10_relat_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ sk_E ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['33','34'])).

thf('64',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( k10_relat_1 @ sk_D @ sk_E )
    = ( k10_relat_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ sk_E ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,(
    ( k10_relat_1 @ sk_D @ sk_E )
 != ( k10_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['4','25','57','65'])).

thf('67',plain,(
    $false ),
    inference(simplify,[status(thm)],['66'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.11  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.R4zDEe2REa
% 0.11/0.32  % Computer   : n025.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 19:45:51 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  % Running portfolio for 600 s
% 0.11/0.32  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.11/0.32  % Number of cores: 8
% 0.11/0.32  % Python version: Python 3.6.8
% 0.11/0.32  % Running in FO mode
% 0.17/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.17/0.56  % Solved by: fo/fo7.sh
% 0.17/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.17/0.56  % done 155 iterations in 0.124s
% 0.17/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.17/0.56  % SZS output start Refutation
% 0.17/0.56  thf(sk_C_type, type, sk_C: $i).
% 0.17/0.56  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.17/0.56  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.17/0.56  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.17/0.56  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.17/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.17/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.17/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.17/0.56  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.17/0.56  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.17/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.17/0.56  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.17/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.17/0.56  thf(sk_D_type, type, sk_D: $i).
% 0.17/0.56  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.17/0.56  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.17/0.56  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.17/0.56  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.17/0.56  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.17/0.56  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.17/0.56  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.17/0.56  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.17/0.56  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.17/0.56  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.17/0.56  thf(sk_E_type, type, sk_E: $i).
% 0.17/0.56  thf(t62_tmap_1, conjecture,
% 0.17/0.56    (![A:$i]:
% 0.17/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.17/0.56       ( ![B:$i]:
% 0.17/0.56         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.17/0.56             ( l1_pre_topc @ B ) ) =>
% 0.17/0.56           ( ![C:$i]:
% 0.17/0.56             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.17/0.56               ( ![D:$i]:
% 0.17/0.56                 ( ( ( v1_funct_1 @ D ) & 
% 0.17/0.56                     ( v1_funct_2 @
% 0.17/0.56                       D @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.17/0.56                     ( m1_subset_1 @
% 0.17/0.56                       D @ 
% 0.17/0.56                       ( k1_zfmisc_1 @
% 0.17/0.56                         ( k2_zfmisc_1 @
% 0.17/0.56                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.17/0.56                   ( ![E:$i]:
% 0.17/0.56                     ( ( m1_subset_1 @
% 0.17/0.56                         E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.17/0.56                       ( ( r1_tarski @
% 0.17/0.56                           ( k8_relset_1 @
% 0.17/0.56                             ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ D @ E ) @ 
% 0.17/0.56                           ( u1_struct_0 @ C ) ) =>
% 0.17/0.56                         ( ( k8_relset_1 @
% 0.17/0.56                             ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ D @ E ) =
% 0.17/0.56                           ( k8_relset_1 @
% 0.17/0.56                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ 
% 0.17/0.56                             ( k2_tmap_1 @ A @ B @ D @ C ) @ E ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.17/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.17/0.56    (~( ![A:$i]:
% 0.17/0.56        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.17/0.56            ( l1_pre_topc @ A ) ) =>
% 0.17/0.56          ( ![B:$i]:
% 0.17/0.56            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.17/0.56                ( l1_pre_topc @ B ) ) =>
% 0.17/0.56              ( ![C:$i]:
% 0.17/0.56                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.17/0.56                  ( ![D:$i]:
% 0.17/0.56                    ( ( ( v1_funct_1 @ D ) & 
% 0.17/0.56                        ( v1_funct_2 @
% 0.17/0.56                          D @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.17/0.56                        ( m1_subset_1 @
% 0.17/0.56                          D @ 
% 0.17/0.56                          ( k1_zfmisc_1 @
% 0.17/0.56                            ( k2_zfmisc_1 @
% 0.17/0.56                              ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.17/0.56                      ( ![E:$i]:
% 0.17/0.56                        ( ( m1_subset_1 @
% 0.17/0.56                            E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.17/0.56                          ( ( r1_tarski @
% 0.17/0.56                              ( k8_relset_1 @
% 0.17/0.56                                ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.17/0.56                                D @ E ) @ 
% 0.17/0.56                              ( u1_struct_0 @ C ) ) =>
% 0.17/0.56                            ( ( k8_relset_1 @
% 0.17/0.56                                ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.17/0.56                                D @ E ) =
% 0.17/0.56                              ( k8_relset_1 @
% 0.17/0.56                                ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ 
% 0.17/0.56                                ( k2_tmap_1 @ A @ B @ D @ C ) @ E ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.17/0.56    inference('cnf.neg', [status(esa)], [t62_tmap_1])).
% 0.17/0.56  thf('0', plain,
% 0.17/0.56      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_D @ 
% 0.17/0.56         sk_E)
% 0.17/0.56         != (k8_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.17/0.56             (k2_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_E))),
% 0.17/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.56  thf('1', plain,
% 0.17/0.56      ((m1_subset_1 @ sk_D @ 
% 0.17/0.56        (k1_zfmisc_1 @ 
% 0.17/0.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.17/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.56  thf(redefinition_k8_relset_1, axiom,
% 0.17/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.17/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.17/0.56       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.17/0.56  thf('2', plain,
% 0.17/0.56      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.17/0.56         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.17/0.56          | ((k8_relset_1 @ X20 @ X21 @ X19 @ X22) = (k10_relat_1 @ X19 @ X22)))),
% 0.17/0.56      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.17/0.56  thf('3', plain,
% 0.17/0.56      (![X0 : $i]:
% 0.17/0.56         ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_D @ 
% 0.17/0.56           X0) = (k10_relat_1 @ sk_D @ X0))),
% 0.17/0.56      inference('sup-', [status(thm)], ['1', '2'])).
% 0.17/0.56  thf('4', plain,
% 0.17/0.56      (((k10_relat_1 @ sk_D @ sk_E)
% 0.17/0.56         != (k8_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.17/0.56             (k2_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_E))),
% 0.17/0.56      inference('demod', [status(thm)], ['0', '3'])).
% 0.17/0.56  thf('5', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.17/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.56  thf('6', plain,
% 0.17/0.56      ((m1_subset_1 @ sk_D @ 
% 0.17/0.56        (k1_zfmisc_1 @ 
% 0.17/0.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.17/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.56  thf(d4_tmap_1, axiom,
% 0.17/0.56    (![A:$i]:
% 0.17/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.17/0.56       ( ![B:$i]:
% 0.17/0.56         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.17/0.56             ( l1_pre_topc @ B ) ) =>
% 0.17/0.56           ( ![C:$i]:
% 0.17/0.56             ( ( ( v1_funct_1 @ C ) & 
% 0.17/0.56                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.17/0.56                 ( m1_subset_1 @
% 0.17/0.56                   C @ 
% 0.17/0.56                   ( k1_zfmisc_1 @
% 0.17/0.56                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.17/0.56               ( ![D:$i]:
% 0.17/0.56                 ( ( m1_pre_topc @ D @ A ) =>
% 0.17/0.56                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 0.17/0.56                     ( k2_partfun1 @
% 0.17/0.56                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.17/0.56                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 0.17/0.56  thf('7', plain,
% 0.17/0.56      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.17/0.56         ((v2_struct_0 @ X33)
% 0.17/0.56          | ~ (v2_pre_topc @ X33)
% 0.17/0.56          | ~ (l1_pre_topc @ X33)
% 0.17/0.56          | ~ (m1_pre_topc @ X34 @ X35)
% 0.17/0.56          | ((k2_tmap_1 @ X35 @ X33 @ X36 @ X34)
% 0.17/0.56              = (k2_partfun1 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X33) @ 
% 0.17/0.56                 X36 @ (u1_struct_0 @ X34)))
% 0.17/0.56          | ~ (m1_subset_1 @ X36 @ 
% 0.17/0.56               (k1_zfmisc_1 @ 
% 0.17/0.56                (k2_zfmisc_1 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X33))))
% 0.17/0.56          | ~ (v1_funct_2 @ X36 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X33))
% 0.17/0.56          | ~ (v1_funct_1 @ X36)
% 0.17/0.56          | ~ (l1_pre_topc @ X35)
% 0.17/0.56          | ~ (v2_pre_topc @ X35)
% 0.17/0.56          | (v2_struct_0 @ X35))),
% 0.17/0.56      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.17/0.56  thf('8', plain,
% 0.17/0.56      (![X0 : $i]:
% 0.17/0.56         ((v2_struct_0 @ sk_A)
% 0.17/0.56          | ~ (v2_pre_topc @ sk_A)
% 0.17/0.56          | ~ (l1_pre_topc @ sk_A)
% 0.17/0.56          | ~ (v1_funct_1 @ sk_D)
% 0.17/0.56          | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.17/0.56          | ((k2_tmap_1 @ sk_A @ sk_B @ sk_D @ X0)
% 0.17/0.56              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.17/0.56                 sk_D @ (u1_struct_0 @ X0)))
% 0.17/0.56          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.17/0.56          | ~ (l1_pre_topc @ sk_B)
% 0.17/0.56          | ~ (v2_pre_topc @ sk_B)
% 0.17/0.56          | (v2_struct_0 @ sk_B))),
% 0.17/0.56      inference('sup-', [status(thm)], ['6', '7'])).
% 0.17/0.56  thf('9', plain, ((v2_pre_topc @ sk_A)),
% 0.17/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.56  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.17/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.56  thf('11', plain, ((v1_funct_1 @ sk_D)),
% 0.17/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.56  thf('12', plain,
% 0.17/0.56      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.17/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.56  thf('13', plain,
% 0.17/0.56      ((m1_subset_1 @ sk_D @ 
% 0.17/0.56        (k1_zfmisc_1 @ 
% 0.17/0.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.17/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.56  thf(redefinition_k2_partfun1, axiom,
% 0.17/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.17/0.56     ( ( ( v1_funct_1 @ C ) & 
% 0.17/0.56         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.17/0.56       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.17/0.56  thf('14', plain,
% 0.17/0.56      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.17/0.56         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.17/0.56          | ~ (v1_funct_1 @ X26)
% 0.17/0.56          | ((k2_partfun1 @ X27 @ X28 @ X26 @ X29) = (k7_relat_1 @ X26 @ X29)))),
% 0.17/0.56      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.17/0.56  thf('15', plain,
% 0.17/0.56      (![X0 : $i]:
% 0.17/0.56         (((k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_D @ 
% 0.17/0.56            X0) = (k7_relat_1 @ sk_D @ X0))
% 0.17/0.56          | ~ (v1_funct_1 @ sk_D))),
% 0.17/0.56      inference('sup-', [status(thm)], ['13', '14'])).
% 0.17/0.56  thf('16', plain, ((v1_funct_1 @ sk_D)),
% 0.17/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.56  thf('17', plain,
% 0.17/0.56      (![X0 : $i]:
% 0.17/0.56         ((k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_D @ 
% 0.17/0.56           X0) = (k7_relat_1 @ sk_D @ X0))),
% 0.17/0.56      inference('demod', [status(thm)], ['15', '16'])).
% 0.17/0.56  thf('18', plain, ((l1_pre_topc @ sk_B)),
% 0.17/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.56  thf('19', plain, ((v2_pre_topc @ sk_B)),
% 0.17/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.56  thf('20', plain,
% 0.17/0.56      (![X0 : $i]:
% 0.17/0.56         ((v2_struct_0 @ sk_A)
% 0.17/0.56          | ((k2_tmap_1 @ sk_A @ sk_B @ sk_D @ X0)
% 0.17/0.56              = (k7_relat_1 @ sk_D @ (u1_struct_0 @ X0)))
% 0.17/0.56          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.17/0.56          | (v2_struct_0 @ sk_B))),
% 0.17/0.56      inference('demod', [status(thm)],
% 0.17/0.56                ['8', '9', '10', '11', '12', '17', '18', '19'])).
% 0.17/0.56  thf('21', plain,
% 0.17/0.56      (((v2_struct_0 @ sk_B)
% 0.17/0.56        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C)
% 0.17/0.56            = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)))
% 0.17/0.56        | (v2_struct_0 @ sk_A))),
% 0.17/0.56      inference('sup-', [status(thm)], ['5', '20'])).
% 0.17/0.56  thf('22', plain, (~ (v2_struct_0 @ sk_B)),
% 0.17/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.56  thf('23', plain,
% 0.17/0.56      (((v2_struct_0 @ sk_A)
% 0.17/0.56        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C)
% 0.17/0.56            = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C))))),
% 0.17/0.56      inference('clc', [status(thm)], ['21', '22'])).
% 0.17/0.56  thf('24', plain, (~ (v2_struct_0 @ sk_A)),
% 0.17/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.56  thf('25', plain,
% 0.17/0.56      (((k2_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C)
% 0.17/0.56         = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)))),
% 0.17/0.56      inference('clc', [status(thm)], ['23', '24'])).
% 0.17/0.56  thf('26', plain,
% 0.17/0.56      ((m1_subset_1 @ sk_D @ 
% 0.17/0.56        (k1_zfmisc_1 @ 
% 0.17/0.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.17/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.56  thf(t3_subset, axiom,
% 0.17/0.56    (![A:$i,B:$i]:
% 0.17/0.56     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.17/0.56  thf('27', plain,
% 0.17/0.56      (![X3 : $i, X4 : $i]:
% 0.17/0.56         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.17/0.56      inference('cnf', [status(esa)], [t3_subset])).
% 0.17/0.56  thf('28', plain,
% 0.17/0.56      ((r1_tarski @ sk_D @ 
% 0.17/0.56        (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.17/0.56      inference('sup-', [status(thm)], ['26', '27'])).
% 0.17/0.56  thf(t88_relat_1, axiom,
% 0.17/0.56    (![A:$i,B:$i]:
% 0.17/0.56     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ))).
% 0.17/0.56  thf('29', plain,
% 0.17/0.56      (![X8 : $i, X9 : $i]:
% 0.17/0.56         ((r1_tarski @ (k7_relat_1 @ X8 @ X9) @ X8) | ~ (v1_relat_1 @ X8))),
% 0.17/0.56      inference('cnf', [status(esa)], [t88_relat_1])).
% 0.17/0.56  thf(t1_xboole_1, axiom,
% 0.17/0.56    (![A:$i,B:$i,C:$i]:
% 0.17/0.56     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.17/0.56       ( r1_tarski @ A @ C ) ))).
% 0.17/0.56  thf('30', plain,
% 0.17/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.17/0.56         (~ (r1_tarski @ X0 @ X1)
% 0.17/0.56          | ~ (r1_tarski @ X1 @ X2)
% 0.17/0.56          | (r1_tarski @ X0 @ X2))),
% 0.17/0.56      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.17/0.56  thf('31', plain,
% 0.17/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.17/0.56         (~ (v1_relat_1 @ X0)
% 0.17/0.56          | (r1_tarski @ (k7_relat_1 @ X0 @ X1) @ X2)
% 0.17/0.56          | ~ (r1_tarski @ X0 @ X2))),
% 0.17/0.56      inference('sup-', [status(thm)], ['29', '30'])).
% 0.17/0.56  thf('32', plain,
% 0.17/0.56      (![X0 : $i]:
% 0.17/0.56         ((r1_tarski @ (k7_relat_1 @ sk_D @ X0) @ 
% 0.17/0.56           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 0.17/0.56          | ~ (v1_relat_1 @ sk_D))),
% 0.17/0.56      inference('sup-', [status(thm)], ['28', '31'])).
% 0.17/0.56  thf('33', plain,
% 0.17/0.56      ((m1_subset_1 @ sk_D @ 
% 0.17/0.56        (k1_zfmisc_1 @ 
% 0.17/0.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.17/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.56  thf(cc1_relset_1, axiom,
% 0.17/0.56    (![A:$i,B:$i,C:$i]:
% 0.17/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.17/0.56       ( v1_relat_1 @ C ) ))).
% 0.17/0.56  thf('34', plain,
% 0.17/0.56      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.17/0.56         ((v1_relat_1 @ X10)
% 0.17/0.56          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.17/0.56      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.17/0.56  thf('35', plain, ((v1_relat_1 @ sk_D)),
% 0.17/0.56      inference('sup-', [status(thm)], ['33', '34'])).
% 0.17/0.56  thf('36', plain,
% 0.17/0.56      (![X0 : $i]:
% 0.17/0.56         (r1_tarski @ (k7_relat_1 @ sk_D @ X0) @ 
% 0.17/0.56          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.17/0.56      inference('demod', [status(thm)], ['32', '35'])).
% 0.17/0.56  thf('37', plain,
% 0.17/0.56      (![X3 : $i, X5 : $i]:
% 0.17/0.56         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 0.17/0.56      inference('cnf', [status(esa)], [t3_subset])).
% 0.17/0.56  thf('38', plain,
% 0.17/0.56      (![X0 : $i]:
% 0.17/0.56         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 0.17/0.56          (k1_zfmisc_1 @ 
% 0.17/0.56           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.17/0.56      inference('sup-', [status(thm)], ['36', '37'])).
% 0.17/0.56  thf(dt_k2_relset_1, axiom,
% 0.17/0.56    (![A:$i,B:$i,C:$i]:
% 0.17/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.17/0.56       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.17/0.56  thf('39', plain,
% 0.17/0.56      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.17/0.56         ((m1_subset_1 @ (k2_relset_1 @ X13 @ X14 @ X15) @ (k1_zfmisc_1 @ X14))
% 0.17/0.56          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.17/0.56      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 0.17/0.56  thf('40', plain,
% 0.17/0.56      (![X0 : $i]:
% 0.17/0.56         (m1_subset_1 @ 
% 0.17/0.56          (k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.17/0.56           (k7_relat_1 @ sk_D @ X0)) @ 
% 0.17/0.56          (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.17/0.56      inference('sup-', [status(thm)], ['38', '39'])).
% 0.17/0.56  thf('41', plain,
% 0.17/0.56      (![X0 : $i]:
% 0.17/0.56         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 0.17/0.56          (k1_zfmisc_1 @ 
% 0.17/0.56           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.17/0.56      inference('sup-', [status(thm)], ['36', '37'])).
% 0.17/0.56  thf(redefinition_k2_relset_1, axiom,
% 0.17/0.56    (![A:$i,B:$i,C:$i]:
% 0.17/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.17/0.56       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.17/0.56  thf('42', plain,
% 0.17/0.56      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.17/0.56         (((k2_relset_1 @ X17 @ X18 @ X16) = (k2_relat_1 @ X16))
% 0.17/0.56          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.17/0.56      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.17/0.56  thf('43', plain,
% 0.17/0.56      (![X0 : $i]:
% 0.17/0.56         ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.17/0.56           (k7_relat_1 @ sk_D @ X0)) = (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)))),
% 0.17/0.56      inference('sup-', [status(thm)], ['41', '42'])).
% 0.17/0.56  thf('44', plain,
% 0.17/0.56      (![X0 : $i]:
% 0.17/0.56         (m1_subset_1 @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ 
% 0.17/0.56          (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.17/0.56      inference('demod', [status(thm)], ['40', '43'])).
% 0.17/0.56  thf('45', plain,
% 0.17/0.56      (![X3 : $i, X4 : $i]:
% 0.17/0.56         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.17/0.56      inference('cnf', [status(esa)], [t3_subset])).
% 0.17/0.56  thf('46', plain,
% 0.17/0.56      (![X0 : $i]:
% 0.17/0.56         (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ 
% 0.17/0.56          (u1_struct_0 @ sk_B))),
% 0.17/0.56      inference('sup-', [status(thm)], ['44', '45'])).
% 0.17/0.56  thf(t87_relat_1, axiom,
% 0.17/0.56    (![A:$i,B:$i]:
% 0.17/0.56     ( ( v1_relat_1 @ B ) =>
% 0.17/0.56       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 0.17/0.56  thf('47', plain,
% 0.17/0.56      (![X6 : $i, X7 : $i]:
% 0.17/0.56         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X6 @ X7)) @ X7)
% 0.17/0.56          | ~ (v1_relat_1 @ X6))),
% 0.17/0.56      inference('cnf', [status(esa)], [t87_relat_1])).
% 0.17/0.56  thf(t11_relset_1, axiom,
% 0.17/0.56    (![A:$i,B:$i,C:$i]:
% 0.17/0.56     ( ( v1_relat_1 @ C ) =>
% 0.17/0.56       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.17/0.56           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.17/0.56         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.17/0.56  thf('48', plain,
% 0.17/0.56      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.17/0.56         (~ (r1_tarski @ (k1_relat_1 @ X23) @ X24)
% 0.17/0.56          | ~ (r1_tarski @ (k2_relat_1 @ X23) @ X25)
% 0.17/0.56          | (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.17/0.56          | ~ (v1_relat_1 @ X23))),
% 0.17/0.56      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.17/0.56  thf('49', plain,
% 0.17/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.17/0.56         (~ (v1_relat_1 @ X1)
% 0.17/0.56          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.17/0.56          | (m1_subset_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 0.17/0.56             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X2)))
% 0.17/0.56          | ~ (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X2))),
% 0.17/0.56      inference('sup-', [status(thm)], ['47', '48'])).
% 0.17/0.56  thf('50', plain,
% 0.17/0.56      (![X0 : $i]:
% 0.17/0.56         ((m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 0.17/0.56           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ (u1_struct_0 @ sk_B))))
% 0.17/0.56          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 0.17/0.56          | ~ (v1_relat_1 @ sk_D))),
% 0.17/0.56      inference('sup-', [status(thm)], ['46', '49'])).
% 0.17/0.56  thf('51', plain,
% 0.17/0.56      (![X0 : $i]:
% 0.17/0.56         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 0.17/0.56          (k1_zfmisc_1 @ 
% 0.17/0.56           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.17/0.56      inference('sup-', [status(thm)], ['36', '37'])).
% 0.17/0.56  thf('52', plain,
% 0.17/0.56      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.17/0.56         ((v1_relat_1 @ X10)
% 0.17/0.56          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.17/0.56      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.17/0.56  thf('53', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 0.17/0.56      inference('sup-', [status(thm)], ['51', '52'])).
% 0.17/0.56  thf('54', plain, ((v1_relat_1 @ sk_D)),
% 0.17/0.56      inference('sup-', [status(thm)], ['33', '34'])).
% 0.17/0.56  thf('55', plain,
% 0.17/0.56      (![X0 : $i]:
% 0.17/0.56         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 0.17/0.56          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ (u1_struct_0 @ sk_B))))),
% 0.17/0.56      inference('demod', [status(thm)], ['50', '53', '54'])).
% 0.17/0.56  thf('56', plain,
% 0.17/0.56      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.17/0.56         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.17/0.56          | ((k8_relset_1 @ X20 @ X21 @ X19 @ X22) = (k10_relat_1 @ X19 @ X22)))),
% 0.17/0.56      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.17/0.56  thf('57', plain,
% 0.17/0.56      (![X0 : $i, X1 : $i]:
% 0.17/0.56         ((k8_relset_1 @ X0 @ (u1_struct_0 @ sk_B) @ 
% 0.17/0.56           (k7_relat_1 @ sk_D @ X0) @ X1)
% 0.17/0.56           = (k10_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ X1))),
% 0.17/0.56      inference('sup-', [status(thm)], ['55', '56'])).
% 0.17/0.56  thf('58', plain,
% 0.17/0.56      ((r1_tarski @ 
% 0.17/0.56        (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_D @ 
% 0.17/0.56         sk_E) @ 
% 0.17/0.56        (u1_struct_0 @ sk_C))),
% 0.17/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.56  thf('59', plain,
% 0.17/0.56      (![X0 : $i]:
% 0.17/0.56         ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_D @ 
% 0.17/0.56           X0) = (k10_relat_1 @ sk_D @ X0))),
% 0.17/0.56      inference('sup-', [status(thm)], ['1', '2'])).
% 0.17/0.56  thf('60', plain,
% 0.17/0.56      ((r1_tarski @ (k10_relat_1 @ sk_D @ sk_E) @ (u1_struct_0 @ sk_C))),
% 0.17/0.56      inference('demod', [status(thm)], ['58', '59'])).
% 0.17/0.56  thf(t175_funct_2, axiom,
% 0.17/0.56    (![A:$i]:
% 0.17/0.56     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.17/0.56       ( ![B:$i,C:$i]:
% 0.17/0.56         ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.17/0.56           ( ( k10_relat_1 @ A @ C ) =
% 0.17/0.56             ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ))).
% 0.17/0.56  thf('61', plain,
% 0.17/0.56      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.17/0.56         (~ (r1_tarski @ (k10_relat_1 @ X30 @ X31) @ X32)
% 0.17/0.56          | ((k10_relat_1 @ X30 @ X31)
% 0.17/0.56              = (k10_relat_1 @ (k7_relat_1 @ X30 @ X32) @ X31))
% 0.17/0.56          | ~ (v1_funct_1 @ X30)
% 0.17/0.56          | ~ (v1_relat_1 @ X30))),
% 0.17/0.56      inference('cnf', [status(esa)], [t175_funct_2])).
% 0.17/0.56  thf('62', plain,
% 0.17/0.56      ((~ (v1_relat_1 @ sk_D)
% 0.17/0.56        | ~ (v1_funct_1 @ sk_D)
% 0.17/0.56        | ((k10_relat_1 @ sk_D @ sk_E)
% 0.17/0.56            = (k10_relat_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ sk_E)))),
% 0.17/0.56      inference('sup-', [status(thm)], ['60', '61'])).
% 0.17/0.56  thf('63', plain, ((v1_relat_1 @ sk_D)),
% 0.17/0.56      inference('sup-', [status(thm)], ['33', '34'])).
% 0.17/0.56  thf('64', plain, ((v1_funct_1 @ sk_D)),
% 0.17/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.56  thf('65', plain,
% 0.17/0.56      (((k10_relat_1 @ sk_D @ sk_E)
% 0.17/0.56         = (k10_relat_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ sk_E))),
% 0.17/0.56      inference('demod', [status(thm)], ['62', '63', '64'])).
% 0.17/0.56  thf('66', plain,
% 0.17/0.56      (((k10_relat_1 @ sk_D @ sk_E) != (k10_relat_1 @ sk_D @ sk_E))),
% 0.17/0.56      inference('demod', [status(thm)], ['4', '25', '57', '65'])).
% 0.17/0.56  thf('67', plain, ($false), inference('simplify', [status(thm)], ['66'])).
% 0.17/0.56  
% 0.17/0.56  % SZS output end Refutation
% 0.17/0.56  
% 0.17/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
