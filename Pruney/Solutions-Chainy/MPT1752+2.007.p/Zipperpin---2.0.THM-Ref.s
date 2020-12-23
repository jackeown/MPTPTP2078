%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9Rco6f3z20

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:50 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 185 expanded)
%              Number of leaves         :   41 (  74 expanded)
%              Depth                    :   14
%              Number of atoms          :  995 (4162 expanded)
%              Number of equality atoms :   26 (  73 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('26',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('27',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('28',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v5_relat_1 @ X17 @ X19 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('29',plain,(
    v5_relat_1 @ sk_D @ ( u1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('30',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v5_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k2_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('31',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('33',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('34',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('35',plain,(
    ! [X9: $i,X10: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('36',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['31','36'])).

thf(t88_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ) )).

thf('38',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X15 @ X16 ) @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('39',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( r1_tarski @ ( k2_relat_1 @ X12 ) @ ( k2_relat_1 @ X11 ) )
      | ~ ( r1_tarski @ X12 @ X11 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) @ X2 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['37','45'])).

thf('47',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['34','35'])).

thf('48',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('49',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X13 @ X14 ) ) @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('50',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X24 ) @ X25 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X24 ) @ X26 )
      | ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( m1_subset_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X2 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['34','35'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['26','54'])).

thf('56',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['34','35'])).

thf('57',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( ( k8_relset_1 @ X21 @ X22 @ X20 @ X23 )
        = ( k10_relat_1 @ X20 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relset_1 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( k7_relat_1 @ sk_D @ X0 ) @ X1 )
      = ( k10_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    r1_tarski @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_D @ X0 )
      = ( k10_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('62',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['60','61'])).

thf(t175_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B )
         => ( ( k10_relat_1 @ A @ C )
            = ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) )).

thf('63',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( r1_tarski @ ( k10_relat_1 @ X31 @ X32 ) @ X33 )
      | ( ( k10_relat_1 @ X31 @ X32 )
        = ( k10_relat_1 @ ( k7_relat_1 @ X31 @ X33 ) @ X32 ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t175_funct_2])).

thf('64',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( ( k10_relat_1 @ sk_D @ sk_E )
      = ( k10_relat_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ sk_E ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['34','35'])).

thf('66',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( k10_relat_1 @ sk_D @ sk_E )
    = ( k10_relat_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ sk_E ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,(
    ( k10_relat_1 @ sk_D @ sk_E )
 != ( k10_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['4','25','59','67'])).

thf('69',plain,(
    $false ),
    inference(simplify,[status(thm)],['68'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9Rco6f3z20
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:23:14 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.53  % Solved by: fo/fo7.sh
% 0.21/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.53  % done 133 iterations in 0.119s
% 0.21/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.53  % SZS output start Refutation
% 0.21/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.53  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.21/0.53  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.53  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.21/0.53  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.53  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.53  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.53  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.53  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.53  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.21/0.53  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.53  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.21/0.53  thf(sk_E_type, type, sk_E: $i).
% 0.21/0.53  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.21/0.53  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.21/0.53  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.21/0.53  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.21/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.53  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.53  thf(t62_tmap_1, conjecture,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.53             ( l1_pre_topc @ B ) ) =>
% 0.21/0.53           ( ![C:$i]:
% 0.21/0.53             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.21/0.53               ( ![D:$i]:
% 0.21/0.53                 ( ( ( v1_funct_1 @ D ) & 
% 0.21/0.53                     ( v1_funct_2 @
% 0.21/0.53                       D @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.53                     ( m1_subset_1 @
% 0.21/0.53                       D @ 
% 0.21/0.53                       ( k1_zfmisc_1 @
% 0.21/0.53                         ( k2_zfmisc_1 @
% 0.21/0.53                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.53                   ( ![E:$i]:
% 0.21/0.53                     ( ( m1_subset_1 @
% 0.21/0.53                         E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.21/0.53                       ( ( r1_tarski @
% 0.21/0.53                           ( k8_relset_1 @
% 0.21/0.53                             ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ D @ E ) @ 
% 0.21/0.53                           ( u1_struct_0 @ C ) ) =>
% 0.21/0.53                         ( ( k8_relset_1 @
% 0.21/0.53                             ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ D @ E ) =
% 0.21/0.53                           ( k8_relset_1 @
% 0.21/0.53                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ 
% 0.21/0.53                             ( k2_tmap_1 @ A @ B @ D @ C ) @ E ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.53    (~( ![A:$i]:
% 0.21/0.53        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.53            ( l1_pre_topc @ A ) ) =>
% 0.21/0.53          ( ![B:$i]:
% 0.21/0.53            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.53                ( l1_pre_topc @ B ) ) =>
% 0.21/0.53              ( ![C:$i]:
% 0.21/0.53                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.21/0.53                  ( ![D:$i]:
% 0.21/0.53                    ( ( ( v1_funct_1 @ D ) & 
% 0.21/0.53                        ( v1_funct_2 @
% 0.21/0.53                          D @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.53                        ( m1_subset_1 @
% 0.21/0.53                          D @ 
% 0.21/0.53                          ( k1_zfmisc_1 @
% 0.21/0.53                            ( k2_zfmisc_1 @
% 0.21/0.53                              ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.53                      ( ![E:$i]:
% 0.21/0.53                        ( ( m1_subset_1 @
% 0.21/0.53                            E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.21/0.53                          ( ( r1_tarski @
% 0.21/0.53                              ( k8_relset_1 @
% 0.21/0.53                                ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.21/0.53                                D @ E ) @ 
% 0.21/0.53                              ( u1_struct_0 @ C ) ) =>
% 0.21/0.53                            ( ( k8_relset_1 @
% 0.21/0.53                                ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.21/0.53                                D @ E ) =
% 0.21/0.53                              ( k8_relset_1 @
% 0.21/0.53                                ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ 
% 0.21/0.53                                ( k2_tmap_1 @ A @ B @ D @ C ) @ E ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.53    inference('cnf.neg', [status(esa)], [t62_tmap_1])).
% 0.21/0.53  thf('0', plain,
% 0.21/0.53      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_D @ 
% 0.21/0.53         sk_E)
% 0.21/0.53         != (k8_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.53             (k2_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_E))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('1', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_D @ 
% 0.21/0.53        (k1_zfmisc_1 @ 
% 0.21/0.53         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(redefinition_k8_relset_1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.53       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.21/0.53  thf('2', plain,
% 0.21/0.53      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.21/0.53          | ((k8_relset_1 @ X21 @ X22 @ X20 @ X23) = (k10_relat_1 @ X20 @ X23)))),
% 0.21/0.53      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.21/0.53  thf('3', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_D @ 
% 0.21/0.53           X0) = (k10_relat_1 @ sk_D @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.53  thf('4', plain,
% 0.21/0.53      (((k10_relat_1 @ sk_D @ sk_E)
% 0.21/0.53         != (k8_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.53             (k2_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_E))),
% 0.21/0.53      inference('demod', [status(thm)], ['0', '3'])).
% 0.21/0.53  thf('5', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('6', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_D @ 
% 0.21/0.53        (k1_zfmisc_1 @ 
% 0.21/0.53         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(d4_tmap_1, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.53             ( l1_pre_topc @ B ) ) =>
% 0.21/0.53           ( ![C:$i]:
% 0.21/0.53             ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.53                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.53                 ( m1_subset_1 @
% 0.21/0.53                   C @ 
% 0.21/0.53                   ( k1_zfmisc_1 @
% 0.21/0.53                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.53               ( ![D:$i]:
% 0.21/0.53                 ( ( m1_pre_topc @ D @ A ) =>
% 0.21/0.53                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 0.21/0.53                     ( k2_partfun1 @
% 0.21/0.53                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.21/0.53                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.53  thf('7', plain,
% 0.21/0.53      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.21/0.53         ((v2_struct_0 @ X34)
% 0.21/0.53          | ~ (v2_pre_topc @ X34)
% 0.21/0.53          | ~ (l1_pre_topc @ X34)
% 0.21/0.53          | ~ (m1_pre_topc @ X35 @ X36)
% 0.21/0.53          | ((k2_tmap_1 @ X36 @ X34 @ X37 @ X35)
% 0.21/0.53              = (k2_partfun1 @ (u1_struct_0 @ X36) @ (u1_struct_0 @ X34) @ 
% 0.21/0.53                 X37 @ (u1_struct_0 @ X35)))
% 0.21/0.53          | ~ (m1_subset_1 @ X37 @ 
% 0.21/0.53               (k1_zfmisc_1 @ 
% 0.21/0.53                (k2_zfmisc_1 @ (u1_struct_0 @ X36) @ (u1_struct_0 @ X34))))
% 0.21/0.53          | ~ (v1_funct_2 @ X37 @ (u1_struct_0 @ X36) @ (u1_struct_0 @ X34))
% 0.21/0.53          | ~ (v1_funct_1 @ X37)
% 0.21/0.53          | ~ (l1_pre_topc @ X36)
% 0.21/0.53          | ~ (v2_pre_topc @ X36)
% 0.21/0.53          | (v2_struct_0 @ X36))),
% 0.21/0.53      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.21/0.53  thf('8', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v2_struct_0 @ sk_A)
% 0.21/0.53          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.53          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.53          | ~ (v1_funct_1 @ sk_D)
% 0.21/0.53          | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.21/0.53          | ((k2_tmap_1 @ sk_A @ sk_B @ sk_D @ X0)
% 0.21/0.53              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.53                 sk_D @ (u1_struct_0 @ X0)))
% 0.21/0.53          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.21/0.53          | ~ (l1_pre_topc @ sk_B)
% 0.21/0.53          | ~ (v2_pre_topc @ sk_B)
% 0.21/0.53          | (v2_struct_0 @ sk_B))),
% 0.21/0.53      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.53  thf('9', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('11', plain, ((v1_funct_1 @ sk_D)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('12', plain,
% 0.21/0.53      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('13', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_D @ 
% 0.21/0.53        (k1_zfmisc_1 @ 
% 0.21/0.53         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(redefinition_k2_partfun1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.53     ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.53         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.53       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.21/0.53  thf('14', plain,
% 0.21/0.53      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.21/0.53          | ~ (v1_funct_1 @ X27)
% 0.21/0.53          | ((k2_partfun1 @ X28 @ X29 @ X27 @ X30) = (k7_relat_1 @ X27 @ X30)))),
% 0.21/0.53      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.21/0.53  thf('15', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (((k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_D @ 
% 0.21/0.53            X0) = (k7_relat_1 @ sk_D @ X0))
% 0.21/0.53          | ~ (v1_funct_1 @ sk_D))),
% 0.21/0.53      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.53  thf('16', plain, ((v1_funct_1 @ sk_D)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('17', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_D @ 
% 0.21/0.53           X0) = (k7_relat_1 @ sk_D @ X0))),
% 0.21/0.53      inference('demod', [status(thm)], ['15', '16'])).
% 0.21/0.53  thf('18', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('19', plain, ((v2_pre_topc @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('20', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v2_struct_0 @ sk_A)
% 0.21/0.53          | ((k2_tmap_1 @ sk_A @ sk_B @ sk_D @ X0)
% 0.21/0.53              = (k7_relat_1 @ sk_D @ (u1_struct_0 @ X0)))
% 0.21/0.53          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.21/0.53          | (v2_struct_0 @ sk_B))),
% 0.21/0.53      inference('demod', [status(thm)],
% 0.21/0.53                ['8', '9', '10', '11', '12', '17', '18', '19'])).
% 0.21/0.53  thf('21', plain,
% 0.21/0.53      (((v2_struct_0 @ sk_B)
% 0.21/0.53        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C)
% 0.21/0.53            = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)))
% 0.21/0.53        | (v2_struct_0 @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['5', '20'])).
% 0.21/0.53  thf('22', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('23', plain,
% 0.21/0.53      (((v2_struct_0 @ sk_A)
% 0.21/0.53        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C)
% 0.21/0.53            = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C))))),
% 0.21/0.53      inference('clc', [status(thm)], ['21', '22'])).
% 0.21/0.53  thf('24', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('25', plain,
% 0.21/0.53      (((k2_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C)
% 0.21/0.53         = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)))),
% 0.21/0.53      inference('clc', [status(thm)], ['23', '24'])).
% 0.21/0.53  thf(dt_k7_relat_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.21/0.53  thf('26', plain,
% 0.21/0.53      (![X7 : $i, X8 : $i]:
% 0.21/0.53         (~ (v1_relat_1 @ X7) | (v1_relat_1 @ (k7_relat_1 @ X7 @ X8)))),
% 0.21/0.53      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.21/0.53  thf('27', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_D @ 
% 0.21/0.53        (k1_zfmisc_1 @ 
% 0.21/0.53         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(cc2_relset_1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.53       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.21/0.53  thf('28', plain,
% 0.21/0.53      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.53         ((v5_relat_1 @ X17 @ X19)
% 0.21/0.53          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.21/0.53      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.21/0.53  thf('29', plain, ((v5_relat_1 @ sk_D @ (u1_struct_0 @ sk_B))),
% 0.21/0.53      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.53  thf(d19_relat_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( v1_relat_1 @ B ) =>
% 0.21/0.53       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.21/0.53  thf('30', plain,
% 0.21/0.53      (![X5 : $i, X6 : $i]:
% 0.21/0.53         (~ (v5_relat_1 @ X5 @ X6)
% 0.21/0.53          | (r1_tarski @ (k2_relat_1 @ X5) @ X6)
% 0.21/0.53          | ~ (v1_relat_1 @ X5))),
% 0.21/0.53      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.21/0.53  thf('31', plain,
% 0.21/0.53      ((~ (v1_relat_1 @ sk_D)
% 0.21/0.53        | (r1_tarski @ (k2_relat_1 @ sk_D) @ (u1_struct_0 @ sk_B)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['29', '30'])).
% 0.21/0.53  thf('32', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_D @ 
% 0.21/0.53        (k1_zfmisc_1 @ 
% 0.21/0.53         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(cc2_relat_1, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( v1_relat_1 @ A ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.21/0.53  thf('33', plain,
% 0.21/0.53      (![X3 : $i, X4 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.21/0.53          | (v1_relat_1 @ X3)
% 0.21/0.53          | ~ (v1_relat_1 @ X4))),
% 0.21/0.53      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.21/0.53  thf('34', plain,
% 0.21/0.53      ((~ (v1_relat_1 @ 
% 0.21/0.53           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 0.21/0.53        | (v1_relat_1 @ sk_D))),
% 0.21/0.53      inference('sup-', [status(thm)], ['32', '33'])).
% 0.21/0.53  thf(fc6_relat_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.21/0.53  thf('35', plain,
% 0.21/0.53      (![X9 : $i, X10 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X9 @ X10))),
% 0.21/0.53      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.21/0.53  thf('36', plain, ((v1_relat_1 @ sk_D)),
% 0.21/0.53      inference('demod', [status(thm)], ['34', '35'])).
% 0.21/0.53  thf('37', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.21/0.53      inference('demod', [status(thm)], ['31', '36'])).
% 0.21/0.53  thf(t88_relat_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ))).
% 0.21/0.53  thf('38', plain,
% 0.21/0.53      (![X15 : $i, X16 : $i]:
% 0.21/0.53         ((r1_tarski @ (k7_relat_1 @ X15 @ X16) @ X15) | ~ (v1_relat_1 @ X15))),
% 0.21/0.53      inference('cnf', [status(esa)], [t88_relat_1])).
% 0.21/0.53  thf(t25_relat_1, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( v1_relat_1 @ A ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( v1_relat_1 @ B ) =>
% 0.21/0.53           ( ( r1_tarski @ A @ B ) =>
% 0.21/0.53             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 0.21/0.53               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 0.21/0.53  thf('39', plain,
% 0.21/0.53      (![X11 : $i, X12 : $i]:
% 0.21/0.53         (~ (v1_relat_1 @ X11)
% 0.21/0.53          | (r1_tarski @ (k2_relat_1 @ X12) @ (k2_relat_1 @ X11))
% 0.21/0.53          | ~ (r1_tarski @ X12 @ X11)
% 0.21/0.53          | ~ (v1_relat_1 @ X12))),
% 0.21/0.53      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.21/0.53  thf('40', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (~ (v1_relat_1 @ X0)
% 0.21/0.53          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 0.21/0.53          | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X0 @ X1)) @ 
% 0.21/0.53             (k2_relat_1 @ X0))
% 0.21/0.53          | ~ (v1_relat_1 @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['38', '39'])).
% 0.21/0.53  thf('41', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         ((r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X0 @ X1)) @ 
% 0.21/0.53           (k2_relat_1 @ X0))
% 0.21/0.53          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 0.21/0.53          | ~ (v1_relat_1 @ X0))),
% 0.21/0.53      inference('simplify', [status(thm)], ['40'])).
% 0.21/0.53  thf('42', plain,
% 0.21/0.53      (![X7 : $i, X8 : $i]:
% 0.21/0.53         (~ (v1_relat_1 @ X7) | (v1_relat_1 @ (k7_relat_1 @ X7 @ X8)))),
% 0.21/0.53      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.21/0.53  thf('43', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (~ (v1_relat_1 @ X0)
% 0.21/0.53          | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X0 @ X1)) @ 
% 0.21/0.53             (k2_relat_1 @ X0)))),
% 0.21/0.53      inference('clc', [status(thm)], ['41', '42'])).
% 0.21/0.53  thf(t1_xboole_1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.21/0.53       ( r1_tarski @ A @ C ) ))).
% 0.21/0.53  thf('44', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         (~ (r1_tarski @ X0 @ X1)
% 0.21/0.53          | ~ (r1_tarski @ X1 @ X2)
% 0.21/0.53          | (r1_tarski @ X0 @ X2))),
% 0.21/0.53      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.21/0.53  thf('45', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         (~ (v1_relat_1 @ X0)
% 0.21/0.53          | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X0 @ X1)) @ X2)
% 0.21/0.53          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X2))),
% 0.21/0.53      inference('sup-', [status(thm)], ['43', '44'])).
% 0.21/0.53  thf('46', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ 
% 0.21/0.53           (u1_struct_0 @ sk_B))
% 0.21/0.53          | ~ (v1_relat_1 @ sk_D))),
% 0.21/0.53      inference('sup-', [status(thm)], ['37', '45'])).
% 0.21/0.53  thf('47', plain, ((v1_relat_1 @ sk_D)),
% 0.21/0.53      inference('demod', [status(thm)], ['34', '35'])).
% 0.21/0.53  thf('48', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ 
% 0.21/0.53          (u1_struct_0 @ sk_B))),
% 0.21/0.53      inference('demod', [status(thm)], ['46', '47'])).
% 0.21/0.53  thf(t87_relat_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( v1_relat_1 @ B ) =>
% 0.21/0.53       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 0.21/0.53  thf('49', plain,
% 0.21/0.53      (![X13 : $i, X14 : $i]:
% 0.21/0.53         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X13 @ X14)) @ X14)
% 0.21/0.53          | ~ (v1_relat_1 @ X13))),
% 0.21/0.53      inference('cnf', [status(esa)], [t87_relat_1])).
% 0.21/0.54  thf(t11_relset_1, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ( v1_relat_1 @ C ) =>
% 0.21/0.54       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.21/0.54           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.21/0.54         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.21/0.54  thf('50', plain,
% 0.21/0.54      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.21/0.54         (~ (r1_tarski @ (k1_relat_1 @ X24) @ X25)
% 0.21/0.54          | ~ (r1_tarski @ (k2_relat_1 @ X24) @ X26)
% 0.21/0.54          | (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.21/0.54          | ~ (v1_relat_1 @ X24))),
% 0.21/0.54      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.21/0.54  thf('51', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.54         (~ (v1_relat_1 @ X1)
% 0.21/0.54          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.21/0.54          | (m1_subset_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 0.21/0.54             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X2)))
% 0.21/0.54          | ~ (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X2))),
% 0.21/0.54      inference('sup-', [status(thm)], ['49', '50'])).
% 0.21/0.54  thf('52', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 0.21/0.54           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ (u1_struct_0 @ sk_B))))
% 0.21/0.54          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 0.21/0.54          | ~ (v1_relat_1 @ sk_D))),
% 0.21/0.54      inference('sup-', [status(thm)], ['48', '51'])).
% 0.21/0.54  thf('53', plain, ((v1_relat_1 @ sk_D)),
% 0.21/0.54      inference('demod', [status(thm)], ['34', '35'])).
% 0.21/0.54  thf('54', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 0.21/0.54           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ (u1_struct_0 @ sk_B))))
% 0.21/0.54          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0)))),
% 0.21/0.54      inference('demod', [status(thm)], ['52', '53'])).
% 0.21/0.54  thf('55', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (v1_relat_1 @ sk_D)
% 0.21/0.54          | (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 0.21/0.54             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ (u1_struct_0 @ sk_B)))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['26', '54'])).
% 0.21/0.54  thf('56', plain, ((v1_relat_1 @ sk_D)),
% 0.21/0.54      inference('demod', [status(thm)], ['34', '35'])).
% 0.21/0.54  thf('57', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 0.21/0.54          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ (u1_struct_0 @ sk_B))))),
% 0.21/0.54      inference('demod', [status(thm)], ['55', '56'])).
% 0.21/0.54  thf('58', plain,
% 0.21/0.54      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.21/0.54          | ((k8_relset_1 @ X21 @ X22 @ X20 @ X23) = (k10_relat_1 @ X20 @ X23)))),
% 0.21/0.54      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.21/0.54  thf('59', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         ((k8_relset_1 @ X0 @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.54           (k7_relat_1 @ sk_D @ X0) @ X1)
% 0.21/0.54           = (k10_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ X1))),
% 0.21/0.54      inference('sup-', [status(thm)], ['57', '58'])).
% 0.21/0.54  thf('60', plain,
% 0.21/0.54      ((r1_tarski @ 
% 0.21/0.54        (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_D @ 
% 0.21/0.54         sk_E) @ 
% 0.21/0.54        (u1_struct_0 @ sk_C))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('61', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_D @ 
% 0.21/0.54           X0) = (k10_relat_1 @ sk_D @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.54  thf('62', plain,
% 0.21/0.54      ((r1_tarski @ (k10_relat_1 @ sk_D @ sk_E) @ (u1_struct_0 @ sk_C))),
% 0.21/0.54      inference('demod', [status(thm)], ['60', '61'])).
% 0.21/0.54  thf(t175_funct_2, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.54       ( ![B:$i,C:$i]:
% 0.21/0.54         ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.21/0.54           ( ( k10_relat_1 @ A @ C ) =
% 0.21/0.54             ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ))).
% 0.21/0.54  thf('63', plain,
% 0.21/0.54      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.21/0.54         (~ (r1_tarski @ (k10_relat_1 @ X31 @ X32) @ X33)
% 0.21/0.54          | ((k10_relat_1 @ X31 @ X32)
% 0.21/0.54              = (k10_relat_1 @ (k7_relat_1 @ X31 @ X33) @ X32))
% 0.21/0.54          | ~ (v1_funct_1 @ X31)
% 0.21/0.54          | ~ (v1_relat_1 @ X31))),
% 0.21/0.54      inference('cnf', [status(esa)], [t175_funct_2])).
% 0.21/0.54  thf('64', plain,
% 0.21/0.54      ((~ (v1_relat_1 @ sk_D)
% 0.21/0.54        | ~ (v1_funct_1 @ sk_D)
% 0.21/0.54        | ((k10_relat_1 @ sk_D @ sk_E)
% 0.21/0.54            = (k10_relat_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ sk_E)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['62', '63'])).
% 0.21/0.54  thf('65', plain, ((v1_relat_1 @ sk_D)),
% 0.21/0.54      inference('demod', [status(thm)], ['34', '35'])).
% 0.21/0.54  thf('66', plain, ((v1_funct_1 @ sk_D)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('67', plain,
% 0.21/0.54      (((k10_relat_1 @ sk_D @ sk_E)
% 0.21/0.54         = (k10_relat_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ sk_E))),
% 0.21/0.54      inference('demod', [status(thm)], ['64', '65', '66'])).
% 0.21/0.54  thf('68', plain,
% 0.21/0.54      (((k10_relat_1 @ sk_D @ sk_E) != (k10_relat_1 @ sk_D @ sk_E))),
% 0.21/0.54      inference('demod', [status(thm)], ['4', '25', '59', '67'])).
% 0.21/0.54  thf('69', plain, ($false), inference('simplify', [status(thm)], ['68'])).
% 0.21/0.54  
% 0.21/0.54  % SZS output end Refutation
% 0.21/0.54  
% 0.21/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
