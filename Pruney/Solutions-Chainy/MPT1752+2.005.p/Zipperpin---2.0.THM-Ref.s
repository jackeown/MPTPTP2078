%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jdU12o76qj

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:49 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 148 expanded)
%              Number of leaves         :   39 (  62 expanded)
%              Depth                    :   11
%              Number of atoms          :  968 (3725 expanded)
%              Number of equality atoms :   31 (  74 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( ( k8_relset_1 @ X21 @ X22 @ X20 @ X23 )
        = ( k10_relat_1 @ X20 @ X23 ) ) ) ),
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
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( v2_struct_0 @ X34 )
      | ~ ( v2_pre_topc @ X34 )
      | ~ ( l1_pre_topc @ X34 )
      | ~ ( m1_pre_topc @ X35 @ X36 )
      | ( ( k2_tmap_1 @ X36 @ X34 @ X37 @ X35 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X36 ) @ ( u1_struct_0 @ X34 ) @ X37 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X36 ) @ ( u1_struct_0 @ X34 ) ) ) )
      | ~ ( v1_funct_2 @ X37 @ ( u1_struct_0 @ X36 ) @ ( u1_struct_0 @ X34 ) )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( l1_pre_topc @ X36 )
      | ~ ( v2_pre_topc @ X36 )
      | ( v2_struct_0 @ X36 ) ) ),
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
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ~ ( v1_funct_1 @ X27 )
      | ( ( k2_partfun1 @ X28 @ X29 @ X27 @ X30 )
        = ( k7_relat_1 @ X27 @ X30 ) ) ) ),
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

thf(dt_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('27',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ( m1_subset_1 @ ( k7_relset_1 @ X13 @ X14 @ X12 @ X15 ) @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relset_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('30',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_D @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('32',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ( ( k7_relset_1 @ X17 @ X18 @ X16 @ X19 )
        = ( k9_relat_1 @ X16 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_D @ X0 )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_relat_1 @ sk_D @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['30','33'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('35',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('36',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X5 @ X6 ) )
        = ( k9_relat_1 @ X5 @ X6 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('37',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X7 @ X8 ) ) @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('38',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X24 ) @ X25 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X24 ) @ X26 )
      | ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( m1_subset_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X2 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( m1_subset_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( m1_subset_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( m1_subset_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X2 ) ) ) ) ),
    inference('sup-',[status(thm)],['35','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X2 ) ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['34','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('46',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v1_relat_1 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('47',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['44','47'])).

thf('49',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( ( k8_relset_1 @ X21 @ X22 @ X20 @ X23 )
        = ( k10_relat_1 @ X20 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relset_1 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( k7_relat_1 @ sk_D @ X0 ) @ X1 )
      = ( k10_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    r1_tarski @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_D @ X0 )
      = ( k10_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('53',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['51','52'])).

thf(t175_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B )
         => ( ( k10_relat_1 @ A @ C )
            = ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) )).

thf('54',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( r1_tarski @ ( k10_relat_1 @ X31 @ X32 ) @ X33 )
      | ( ( k10_relat_1 @ X31 @ X32 )
        = ( k10_relat_1 @ ( k7_relat_1 @ X31 @ X33 ) @ X32 ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t175_funct_2])).

thf('55',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( ( k10_relat_1 @ sk_D @ sk_E )
      = ( k10_relat_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ sk_E ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['45','46'])).

thf('57',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( k10_relat_1 @ sk_D @ sk_E )
    = ( k10_relat_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ sk_E ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,(
    ( k10_relat_1 @ sk_D @ sk_E )
 != ( k10_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['4','25','50','58'])).

thf('60',plain,(
    $false ),
    inference(simplify,[status(thm)],['59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jdU12o76qj
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 19:05:52 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.33  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.19/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.56  % Solved by: fo/fo7.sh
% 0.19/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.56  % done 96 iterations in 0.080s
% 0.19/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.56  % SZS output start Refutation
% 0.19/0.56  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.19/0.56  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.19/0.56  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.19/0.56  thf(sk_D_type, type, sk_D: $i).
% 0.19/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.56  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.56  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.56  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.19/0.56  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.56  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.56  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.56  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.19/0.56  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.19/0.56  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.19/0.56  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.19/0.56  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.19/0.56  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.19/0.56  thf(sk_E_type, type, sk_E: $i).
% 0.19/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.56  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.19/0.56  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.19/0.56  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.19/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.56  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.19/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.56  thf(t62_tmap_1, conjecture,
% 0.19/0.56    (![A:$i]:
% 0.19/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.56       ( ![B:$i]:
% 0.19/0.56         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.19/0.56             ( l1_pre_topc @ B ) ) =>
% 0.19/0.56           ( ![C:$i]:
% 0.19/0.56             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.19/0.56               ( ![D:$i]:
% 0.19/0.56                 ( ( ( v1_funct_1 @ D ) & 
% 0.19/0.56                     ( v1_funct_2 @
% 0.19/0.56                       D @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.19/0.56                     ( m1_subset_1 @
% 0.19/0.56                       D @ 
% 0.19/0.56                       ( k1_zfmisc_1 @
% 0.19/0.56                         ( k2_zfmisc_1 @
% 0.19/0.56                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.19/0.56                   ( ![E:$i]:
% 0.19/0.56                     ( ( m1_subset_1 @
% 0.19/0.56                         E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.19/0.56                       ( ( r1_tarski @
% 0.19/0.56                           ( k8_relset_1 @
% 0.19/0.56                             ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ D @ E ) @ 
% 0.19/0.56                           ( u1_struct_0 @ C ) ) =>
% 0.19/0.56                         ( ( k8_relset_1 @
% 0.19/0.56                             ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ D @ E ) =
% 0.19/0.56                           ( k8_relset_1 @
% 0.19/0.56                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ 
% 0.19/0.56                             ( k2_tmap_1 @ A @ B @ D @ C ) @ E ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.56    (~( ![A:$i]:
% 0.19/0.56        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.19/0.56            ( l1_pre_topc @ A ) ) =>
% 0.19/0.56          ( ![B:$i]:
% 0.19/0.56            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.19/0.56                ( l1_pre_topc @ B ) ) =>
% 0.19/0.56              ( ![C:$i]:
% 0.19/0.56                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.19/0.56                  ( ![D:$i]:
% 0.19/0.56                    ( ( ( v1_funct_1 @ D ) & 
% 0.19/0.56                        ( v1_funct_2 @
% 0.19/0.56                          D @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.19/0.56                        ( m1_subset_1 @
% 0.19/0.56                          D @ 
% 0.19/0.56                          ( k1_zfmisc_1 @
% 0.19/0.56                            ( k2_zfmisc_1 @
% 0.19/0.56                              ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.19/0.56                      ( ![E:$i]:
% 0.19/0.56                        ( ( m1_subset_1 @
% 0.19/0.56                            E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.19/0.56                          ( ( r1_tarski @
% 0.19/0.56                              ( k8_relset_1 @
% 0.19/0.56                                ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.19/0.56                                D @ E ) @ 
% 0.19/0.56                              ( u1_struct_0 @ C ) ) =>
% 0.19/0.56                            ( ( k8_relset_1 @
% 0.19/0.56                                ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.19/0.56                                D @ E ) =
% 0.19/0.56                              ( k8_relset_1 @
% 0.19/0.56                                ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ 
% 0.19/0.56                                ( k2_tmap_1 @ A @ B @ D @ C ) @ E ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.19/0.56    inference('cnf.neg', [status(esa)], [t62_tmap_1])).
% 0.19/0.56  thf('0', plain,
% 0.19/0.56      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_D @ 
% 0.19/0.56         sk_E)
% 0.19/0.56         != (k8_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.56             (k2_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_E))),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf('1', plain,
% 0.19/0.56      ((m1_subset_1 @ sk_D @ 
% 0.19/0.56        (k1_zfmisc_1 @ 
% 0.19/0.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf(redefinition_k8_relset_1, axiom,
% 0.19/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.56       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.19/0.56  thf('2', plain,
% 0.19/0.56      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.19/0.56         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.19/0.56          | ((k8_relset_1 @ X21 @ X22 @ X20 @ X23) = (k10_relat_1 @ X20 @ X23)))),
% 0.19/0.56      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.19/0.56  thf('3', plain,
% 0.19/0.56      (![X0 : $i]:
% 0.19/0.56         ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_D @ 
% 0.19/0.56           X0) = (k10_relat_1 @ sk_D @ X0))),
% 0.19/0.56      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.56  thf('4', plain,
% 0.19/0.56      (((k10_relat_1 @ sk_D @ sk_E)
% 0.19/0.56         != (k8_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.56             (k2_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_E))),
% 0.19/0.56      inference('demod', [status(thm)], ['0', '3'])).
% 0.19/0.56  thf('5', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf('6', plain,
% 0.19/0.56      ((m1_subset_1 @ sk_D @ 
% 0.19/0.56        (k1_zfmisc_1 @ 
% 0.19/0.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf(d4_tmap_1, axiom,
% 0.19/0.56    (![A:$i]:
% 0.19/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.56       ( ![B:$i]:
% 0.19/0.56         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.19/0.56             ( l1_pre_topc @ B ) ) =>
% 0.19/0.56           ( ![C:$i]:
% 0.19/0.56             ( ( ( v1_funct_1 @ C ) & 
% 0.19/0.56                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.19/0.56                 ( m1_subset_1 @
% 0.19/0.56                   C @ 
% 0.19/0.56                   ( k1_zfmisc_1 @
% 0.19/0.56                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.19/0.56               ( ![D:$i]:
% 0.19/0.56                 ( ( m1_pre_topc @ D @ A ) =>
% 0.19/0.56                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 0.19/0.56                     ( k2_partfun1 @
% 0.19/0.56                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.19/0.56                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.56  thf('7', plain,
% 0.19/0.56      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.19/0.56         ((v2_struct_0 @ X34)
% 0.19/0.56          | ~ (v2_pre_topc @ X34)
% 0.19/0.56          | ~ (l1_pre_topc @ X34)
% 0.19/0.56          | ~ (m1_pre_topc @ X35 @ X36)
% 0.19/0.56          | ((k2_tmap_1 @ X36 @ X34 @ X37 @ X35)
% 0.19/0.56              = (k2_partfun1 @ (u1_struct_0 @ X36) @ (u1_struct_0 @ X34) @ 
% 0.19/0.56                 X37 @ (u1_struct_0 @ X35)))
% 0.19/0.56          | ~ (m1_subset_1 @ X37 @ 
% 0.19/0.56               (k1_zfmisc_1 @ 
% 0.19/0.56                (k2_zfmisc_1 @ (u1_struct_0 @ X36) @ (u1_struct_0 @ X34))))
% 0.19/0.56          | ~ (v1_funct_2 @ X37 @ (u1_struct_0 @ X36) @ (u1_struct_0 @ X34))
% 0.19/0.56          | ~ (v1_funct_1 @ X37)
% 0.19/0.56          | ~ (l1_pre_topc @ X36)
% 0.19/0.56          | ~ (v2_pre_topc @ X36)
% 0.19/0.56          | (v2_struct_0 @ X36))),
% 0.19/0.56      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.19/0.56  thf('8', plain,
% 0.19/0.56      (![X0 : $i]:
% 0.19/0.56         ((v2_struct_0 @ sk_A)
% 0.19/0.56          | ~ (v2_pre_topc @ sk_A)
% 0.19/0.56          | ~ (l1_pre_topc @ sk_A)
% 0.19/0.56          | ~ (v1_funct_1 @ sk_D)
% 0.19/0.56          | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.19/0.56          | ((k2_tmap_1 @ sk_A @ sk_B @ sk_D @ X0)
% 0.19/0.56              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.56                 sk_D @ (u1_struct_0 @ X0)))
% 0.19/0.56          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.19/0.56          | ~ (l1_pre_topc @ sk_B)
% 0.19/0.56          | ~ (v2_pre_topc @ sk_B)
% 0.19/0.56          | (v2_struct_0 @ sk_B))),
% 0.19/0.56      inference('sup-', [status(thm)], ['6', '7'])).
% 0.19/0.56  thf('9', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf('11', plain, ((v1_funct_1 @ sk_D)),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf('12', plain,
% 0.19/0.56      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf('13', plain,
% 0.19/0.56      ((m1_subset_1 @ sk_D @ 
% 0.19/0.56        (k1_zfmisc_1 @ 
% 0.19/0.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf(redefinition_k2_partfun1, axiom,
% 0.19/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.56     ( ( ( v1_funct_1 @ C ) & 
% 0.19/0.56         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.19/0.56       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.19/0.56  thf('14', plain,
% 0.19/0.56      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.19/0.56         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.19/0.56          | ~ (v1_funct_1 @ X27)
% 0.19/0.56          | ((k2_partfun1 @ X28 @ X29 @ X27 @ X30) = (k7_relat_1 @ X27 @ X30)))),
% 0.19/0.56      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.19/0.56  thf('15', plain,
% 0.19/0.56      (![X0 : $i]:
% 0.19/0.56         (((k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_D @ 
% 0.19/0.56            X0) = (k7_relat_1 @ sk_D @ X0))
% 0.19/0.56          | ~ (v1_funct_1 @ sk_D))),
% 0.19/0.56      inference('sup-', [status(thm)], ['13', '14'])).
% 0.19/0.56  thf('16', plain, ((v1_funct_1 @ sk_D)),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf('17', plain,
% 0.19/0.56      (![X0 : $i]:
% 0.19/0.56         ((k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_D @ 
% 0.19/0.56           X0) = (k7_relat_1 @ sk_D @ X0))),
% 0.19/0.56      inference('demod', [status(thm)], ['15', '16'])).
% 0.19/0.56  thf('18', plain, ((l1_pre_topc @ sk_B)),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf('19', plain, ((v2_pre_topc @ sk_B)),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf('20', plain,
% 0.19/0.56      (![X0 : $i]:
% 0.19/0.56         ((v2_struct_0 @ sk_A)
% 0.19/0.56          | ((k2_tmap_1 @ sk_A @ sk_B @ sk_D @ X0)
% 0.19/0.56              = (k7_relat_1 @ sk_D @ (u1_struct_0 @ X0)))
% 0.19/0.56          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.19/0.56          | (v2_struct_0 @ sk_B))),
% 0.19/0.56      inference('demod', [status(thm)],
% 0.19/0.56                ['8', '9', '10', '11', '12', '17', '18', '19'])).
% 0.19/0.56  thf('21', plain,
% 0.19/0.56      (((v2_struct_0 @ sk_B)
% 0.19/0.56        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C)
% 0.19/0.56            = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)))
% 0.19/0.56        | (v2_struct_0 @ sk_A))),
% 0.19/0.56      inference('sup-', [status(thm)], ['5', '20'])).
% 0.19/0.56  thf('22', plain, (~ (v2_struct_0 @ sk_B)),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf('23', plain,
% 0.19/0.56      (((v2_struct_0 @ sk_A)
% 0.19/0.56        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C)
% 0.19/0.56            = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C))))),
% 0.19/0.56      inference('clc', [status(thm)], ['21', '22'])).
% 0.19/0.56  thf('24', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf('25', plain,
% 0.19/0.56      (((k2_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C)
% 0.19/0.56         = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)))),
% 0.19/0.56      inference('clc', [status(thm)], ['23', '24'])).
% 0.19/0.56  thf('26', plain,
% 0.19/0.56      ((m1_subset_1 @ sk_D @ 
% 0.19/0.56        (k1_zfmisc_1 @ 
% 0.19/0.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf(dt_k7_relset_1, axiom,
% 0.19/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.56       ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.19/0.56  thf('27', plain,
% 0.19/0.56      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.19/0.56         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.19/0.56          | (m1_subset_1 @ (k7_relset_1 @ X13 @ X14 @ X12 @ X15) @ 
% 0.19/0.56             (k1_zfmisc_1 @ X14)))),
% 0.19/0.56      inference('cnf', [status(esa)], [dt_k7_relset_1])).
% 0.19/0.56  thf('28', plain,
% 0.19/0.56      (![X0 : $i]:
% 0.19/0.56         (m1_subset_1 @ 
% 0.19/0.56          (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_D @ 
% 0.19/0.56           X0) @ 
% 0.19/0.56          (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.19/0.56      inference('sup-', [status(thm)], ['26', '27'])).
% 0.19/0.56  thf(t3_subset, axiom,
% 0.19/0.56    (![A:$i,B:$i]:
% 0.19/0.56     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.19/0.56  thf('29', plain,
% 0.19/0.56      (![X0 : $i, X1 : $i]:
% 0.19/0.56         ((r1_tarski @ X0 @ X1) | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.19/0.56      inference('cnf', [status(esa)], [t3_subset])).
% 0.19/0.56  thf('30', plain,
% 0.19/0.56      (![X0 : $i]:
% 0.19/0.56         (r1_tarski @ 
% 0.19/0.56          (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_D @ 
% 0.19/0.56           X0) @ 
% 0.19/0.56          (u1_struct_0 @ sk_B))),
% 0.19/0.56      inference('sup-', [status(thm)], ['28', '29'])).
% 0.19/0.56  thf('31', plain,
% 0.19/0.56      ((m1_subset_1 @ sk_D @ 
% 0.19/0.56        (k1_zfmisc_1 @ 
% 0.19/0.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf(redefinition_k7_relset_1, axiom,
% 0.19/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.56       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.19/0.56  thf('32', plain,
% 0.19/0.56      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.19/0.56         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.19/0.56          | ((k7_relset_1 @ X17 @ X18 @ X16 @ X19) = (k9_relat_1 @ X16 @ X19)))),
% 0.19/0.56      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.19/0.56  thf('33', plain,
% 0.19/0.56      (![X0 : $i]:
% 0.19/0.56         ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_D @ 
% 0.19/0.56           X0) = (k9_relat_1 @ sk_D @ X0))),
% 0.19/0.56      inference('sup-', [status(thm)], ['31', '32'])).
% 0.19/0.56  thf('34', plain,
% 0.19/0.56      (![X0 : $i]:
% 0.19/0.56         (r1_tarski @ (k9_relat_1 @ sk_D @ X0) @ (u1_struct_0 @ sk_B))),
% 0.19/0.56      inference('demod', [status(thm)], ['30', '33'])).
% 0.19/0.56  thf(dt_k7_relat_1, axiom,
% 0.19/0.56    (![A:$i,B:$i]:
% 0.19/0.56     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.19/0.56  thf('35', plain,
% 0.19/0.56      (![X3 : $i, X4 : $i]:
% 0.19/0.56         (~ (v1_relat_1 @ X3) | (v1_relat_1 @ (k7_relat_1 @ X3 @ X4)))),
% 0.19/0.56      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.19/0.56  thf(t148_relat_1, axiom,
% 0.19/0.56    (![A:$i,B:$i]:
% 0.19/0.56     ( ( v1_relat_1 @ B ) =>
% 0.19/0.56       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.19/0.56  thf('36', plain,
% 0.19/0.56      (![X5 : $i, X6 : $i]:
% 0.19/0.56         (((k2_relat_1 @ (k7_relat_1 @ X5 @ X6)) = (k9_relat_1 @ X5 @ X6))
% 0.19/0.56          | ~ (v1_relat_1 @ X5))),
% 0.19/0.56      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.19/0.56  thf(t87_relat_1, axiom,
% 0.19/0.56    (![A:$i,B:$i]:
% 0.19/0.56     ( ( v1_relat_1 @ B ) =>
% 0.19/0.56       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 0.19/0.56  thf('37', plain,
% 0.19/0.56      (![X7 : $i, X8 : $i]:
% 0.19/0.56         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X7 @ X8)) @ X8)
% 0.19/0.56          | ~ (v1_relat_1 @ X7))),
% 0.19/0.56      inference('cnf', [status(esa)], [t87_relat_1])).
% 0.19/0.56  thf(t11_relset_1, axiom,
% 0.19/0.56    (![A:$i,B:$i,C:$i]:
% 0.19/0.56     ( ( v1_relat_1 @ C ) =>
% 0.19/0.56       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.19/0.56           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.19/0.56         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.19/0.56  thf('38', plain,
% 0.19/0.56      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.19/0.56         (~ (r1_tarski @ (k1_relat_1 @ X24) @ X25)
% 0.19/0.56          | ~ (r1_tarski @ (k2_relat_1 @ X24) @ X26)
% 0.19/0.56          | (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.19/0.56          | ~ (v1_relat_1 @ X24))),
% 0.19/0.56      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.19/0.56  thf('39', plain,
% 0.19/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.56         (~ (v1_relat_1 @ X1)
% 0.19/0.56          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.19/0.56          | (m1_subset_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 0.19/0.56             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X2)))
% 0.19/0.56          | ~ (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X2))),
% 0.19/0.56      inference('sup-', [status(thm)], ['37', '38'])).
% 0.19/0.56  thf('40', plain,
% 0.19/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.56         (~ (r1_tarski @ (k9_relat_1 @ X1 @ X0) @ X2)
% 0.19/0.56          | ~ (v1_relat_1 @ X1)
% 0.19/0.56          | (m1_subset_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 0.19/0.56             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X2)))
% 0.19/0.56          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.19/0.56          | ~ (v1_relat_1 @ X1))),
% 0.19/0.56      inference('sup-', [status(thm)], ['36', '39'])).
% 0.19/0.56  thf('41', plain,
% 0.19/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.56         (~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.19/0.56          | (m1_subset_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 0.19/0.56             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X2)))
% 0.19/0.56          | ~ (v1_relat_1 @ X1)
% 0.19/0.56          | ~ (r1_tarski @ (k9_relat_1 @ X1 @ X0) @ X2))),
% 0.19/0.56      inference('simplify', [status(thm)], ['40'])).
% 0.19/0.56  thf('42', plain,
% 0.19/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.56         (~ (v1_relat_1 @ X1)
% 0.19/0.56          | ~ (r1_tarski @ (k9_relat_1 @ X1 @ X0) @ X2)
% 0.19/0.56          | ~ (v1_relat_1 @ X1)
% 0.19/0.56          | (m1_subset_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 0.19/0.56             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X2))))),
% 0.19/0.56      inference('sup-', [status(thm)], ['35', '41'])).
% 0.19/0.56  thf('43', plain,
% 0.19/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.56         ((m1_subset_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 0.19/0.56           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X2)))
% 0.19/0.56          | ~ (r1_tarski @ (k9_relat_1 @ X1 @ X0) @ X2)
% 0.19/0.56          | ~ (v1_relat_1 @ X1))),
% 0.19/0.56      inference('simplify', [status(thm)], ['42'])).
% 0.19/0.56  thf('44', plain,
% 0.19/0.56      (![X0 : $i]:
% 0.19/0.56         (~ (v1_relat_1 @ sk_D)
% 0.19/0.56          | (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 0.19/0.56             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ (u1_struct_0 @ sk_B)))))),
% 0.19/0.56      inference('sup-', [status(thm)], ['34', '43'])).
% 0.19/0.56  thf('45', plain,
% 0.19/0.56      ((m1_subset_1 @ sk_D @ 
% 0.19/0.56        (k1_zfmisc_1 @ 
% 0.19/0.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf(cc1_relset_1, axiom,
% 0.19/0.56    (![A:$i,B:$i,C:$i]:
% 0.19/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.56       ( v1_relat_1 @ C ) ))).
% 0.19/0.56  thf('46', plain,
% 0.19/0.56      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.19/0.56         ((v1_relat_1 @ X9)
% 0.19/0.56          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.19/0.56      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.19/0.56  thf('47', plain, ((v1_relat_1 @ sk_D)),
% 0.19/0.56      inference('sup-', [status(thm)], ['45', '46'])).
% 0.19/0.56  thf('48', plain,
% 0.19/0.56      (![X0 : $i]:
% 0.19/0.56         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 0.19/0.56          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ (u1_struct_0 @ sk_B))))),
% 0.19/0.56      inference('demod', [status(thm)], ['44', '47'])).
% 0.19/0.56  thf('49', plain,
% 0.19/0.56      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.19/0.56         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.19/0.56          | ((k8_relset_1 @ X21 @ X22 @ X20 @ X23) = (k10_relat_1 @ X20 @ X23)))),
% 0.19/0.56      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.19/0.56  thf('50', plain,
% 0.19/0.56      (![X0 : $i, X1 : $i]:
% 0.19/0.56         ((k8_relset_1 @ X0 @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.56           (k7_relat_1 @ sk_D @ X0) @ X1)
% 0.19/0.56           = (k10_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ X1))),
% 0.19/0.56      inference('sup-', [status(thm)], ['48', '49'])).
% 0.19/0.56  thf('51', plain,
% 0.19/0.56      ((r1_tarski @ 
% 0.19/0.56        (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_D @ 
% 0.19/0.56         sk_E) @ 
% 0.19/0.56        (u1_struct_0 @ sk_C))),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf('52', plain,
% 0.19/0.56      (![X0 : $i]:
% 0.19/0.56         ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_D @ 
% 0.19/0.56           X0) = (k10_relat_1 @ sk_D @ X0))),
% 0.19/0.56      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.56  thf('53', plain,
% 0.19/0.56      ((r1_tarski @ (k10_relat_1 @ sk_D @ sk_E) @ (u1_struct_0 @ sk_C))),
% 0.19/0.56      inference('demod', [status(thm)], ['51', '52'])).
% 0.19/0.56  thf(t175_funct_2, axiom,
% 0.19/0.56    (![A:$i]:
% 0.19/0.56     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.19/0.56       ( ![B:$i,C:$i]:
% 0.19/0.56         ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.19/0.56           ( ( k10_relat_1 @ A @ C ) =
% 0.19/0.56             ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ))).
% 0.19/0.56  thf('54', plain,
% 0.19/0.56      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.19/0.56         (~ (r1_tarski @ (k10_relat_1 @ X31 @ X32) @ X33)
% 0.19/0.56          | ((k10_relat_1 @ X31 @ X32)
% 0.19/0.56              = (k10_relat_1 @ (k7_relat_1 @ X31 @ X33) @ X32))
% 0.19/0.56          | ~ (v1_funct_1 @ X31)
% 0.19/0.56          | ~ (v1_relat_1 @ X31))),
% 0.19/0.56      inference('cnf', [status(esa)], [t175_funct_2])).
% 0.19/0.56  thf('55', plain,
% 0.19/0.56      ((~ (v1_relat_1 @ sk_D)
% 0.19/0.56        | ~ (v1_funct_1 @ sk_D)
% 0.19/0.56        | ((k10_relat_1 @ sk_D @ sk_E)
% 0.19/0.56            = (k10_relat_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ sk_E)))),
% 0.19/0.56      inference('sup-', [status(thm)], ['53', '54'])).
% 0.19/0.56  thf('56', plain, ((v1_relat_1 @ sk_D)),
% 0.19/0.56      inference('sup-', [status(thm)], ['45', '46'])).
% 0.19/0.56  thf('57', plain, ((v1_funct_1 @ sk_D)),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf('58', plain,
% 0.19/0.56      (((k10_relat_1 @ sk_D @ sk_E)
% 0.19/0.56         = (k10_relat_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ sk_E))),
% 0.19/0.56      inference('demod', [status(thm)], ['55', '56', '57'])).
% 0.19/0.56  thf('59', plain,
% 0.19/0.56      (((k10_relat_1 @ sk_D @ sk_E) != (k10_relat_1 @ sk_D @ sk_E))),
% 0.19/0.56      inference('demod', [status(thm)], ['4', '25', '50', '58'])).
% 0.19/0.56  thf('60', plain, ($false), inference('simplify', [status(thm)], ['59'])).
% 0.19/0.56  
% 0.19/0.56  % SZS output end Refutation
% 0.19/0.56  
% 0.19/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
