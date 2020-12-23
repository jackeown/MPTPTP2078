%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pHOSKv1u7x

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:46 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 144 expanded)
%              Number of leaves         :   37 (  59 expanded)
%              Depth                    :   13
%              Number of atoms          :  939 (3219 expanded)
%              Number of equality atoms :   29 (  68 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X9 @ X8 ) @ X7 )
        = ( k9_relat_1 @ X9 @ X7 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
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
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ( ( k7_relset_1 @ X22 @ X23 @ X21 @ X24 )
        = ( k9_relat_1 @ X21 @ X24 ) ) ) ),
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
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( v2_struct_0 @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( m1_pre_topc @ X33 @ X34 )
      | ( ( k2_tmap_1 @ X34 @ X32 @ X35 @ X33 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X32 ) @ X35 @ ( u1_struct_0 @ X33 ) ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X32 ) ) ) )
      | ~ ( v1_funct_2 @ X35 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X32 ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( l1_pre_topc @ X34 )
      | ~ ( v2_pre_topc @ X34 )
      | ( v2_struct_0 @ X34 ) ) ),
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
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ( ( k2_partfun1 @ X29 @ X30 @ X28 @ X31 )
        = ( k7_relat_1 @ X28 @ X31 ) ) ) ),
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
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('30',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( m1_subset_1 @ ( k7_relset_1 @ X18 @ X19 @ X17 @ X20 ) @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relset_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('33',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k7_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('35',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_relat_1 @ sk_D @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf(t88_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ) )).

thf('36',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X12 @ X13 ) @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf('37',plain,(
    ! [X0: $i,X2: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X2 ) )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k7_relat_1 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('39',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('42',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X5 @ X6 ) )
        = ( k9_relat_1 @ X5 @ X6 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('43',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X10 @ X11 ) ) @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('44',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X25 ) @ X26 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X25 ) @ X27 )
      | ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( m1_subset_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X2 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( m1_subset_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( m1_subset_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( m1_subset_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X2 ) ) ) ) ),
    inference('sup-',[status(thm)],['41','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X2 ) ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['35','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('52',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v1_relat_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('53',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['50','53'])).

thf('55',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ( ( k7_relset_1 @ X22 @ X23 @ X21 @ X24 )
        = ( k9_relat_1 @ X21 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relset_1 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( k7_relat_1 @ sk_D @ X0 ) @ X1 )
      = ( k9_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ( k9_relat_1 @ sk_D @ sk_E )
 != ( k9_relat_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ sk_E ) ),
    inference(demod,[status(thm)],['7','28','56'])).

thf('58',plain,
    ( ( ( k9_relat_1 @ sk_D @ sk_E )
     != ( k9_relat_1 @ sk_D @ sk_E ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['2','57'])).

thf('59',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['51','52'])).

thf('60',plain,(
    ( k9_relat_1 @ sk_D @ sk_E )
 != ( k9_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    $false ),
    inference(simplify,[status(thm)],['60'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pHOSKv1u7x
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:44:38 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.21/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.54  % Solved by: fo/fo7.sh
% 0.21/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.54  % done 107 iterations in 0.066s
% 0.21/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.54  % SZS output start Refutation
% 0.21/0.54  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.54  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.54  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.54  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.54  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.54  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.21/0.54  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.54  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.21/0.54  thf(sk_E_type, type, sk_E: $i).
% 0.21/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.54  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.21/0.54  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.21/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.54  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.54  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.54  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.54  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.21/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.54  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.21/0.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.54  thf(t61_tmap_1, conjecture,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.54             ( l1_pre_topc @ B ) ) =>
% 0.21/0.54           ( ![C:$i]:
% 0.21/0.54             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.21/0.54               ( ![D:$i]:
% 0.21/0.54                 ( ( ( v1_funct_1 @ D ) & 
% 0.21/0.54                     ( v1_funct_2 @
% 0.21/0.54                       D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.54                     ( m1_subset_1 @
% 0.21/0.54                       D @ 
% 0.21/0.54                       ( k1_zfmisc_1 @
% 0.21/0.54                         ( k2_zfmisc_1 @
% 0.21/0.54                           ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.21/0.54                   ( ![E:$i]:
% 0.21/0.54                     ( ( m1_subset_1 @
% 0.21/0.54                         E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.21/0.54                       ( ( r1_tarski @ E @ ( u1_struct_0 @ C ) ) =>
% 0.21/0.54                         ( ( k7_relset_1 @
% 0.21/0.54                             ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ D @ E ) =
% 0.21/0.54                           ( k7_relset_1 @
% 0.21/0.54                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ 
% 0.21/0.54                             ( k2_tmap_1 @ B @ A @ D @ C ) @ E ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.54    (~( ![A:$i]:
% 0.21/0.54        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.54            ( l1_pre_topc @ A ) ) =>
% 0.21/0.54          ( ![B:$i]:
% 0.21/0.54            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.54                ( l1_pre_topc @ B ) ) =>
% 0.21/0.54              ( ![C:$i]:
% 0.21/0.54                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.21/0.54                  ( ![D:$i]:
% 0.21/0.54                    ( ( ( v1_funct_1 @ D ) & 
% 0.21/0.54                        ( v1_funct_2 @
% 0.21/0.54                          D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.54                        ( m1_subset_1 @
% 0.21/0.54                          D @ 
% 0.21/0.54                          ( k1_zfmisc_1 @
% 0.21/0.54                            ( k2_zfmisc_1 @
% 0.21/0.54                              ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.21/0.54                      ( ![E:$i]:
% 0.21/0.54                        ( ( m1_subset_1 @
% 0.21/0.54                            E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.21/0.54                          ( ( r1_tarski @ E @ ( u1_struct_0 @ C ) ) =>
% 0.21/0.54                            ( ( k7_relset_1 @
% 0.21/0.54                                ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.21/0.54                                D @ E ) =
% 0.21/0.54                              ( k7_relset_1 @
% 0.21/0.54                                ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ 
% 0.21/0.54                                ( k2_tmap_1 @ B @ A @ D @ C ) @ E ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.54    inference('cnf.neg', [status(esa)], [t61_tmap_1])).
% 0.21/0.54  thf('0', plain, ((r1_tarski @ sk_E @ (u1_struct_0 @ sk_C))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(t162_relat_1, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( v1_relat_1 @ A ) =>
% 0.21/0.54       ( ![B:$i,C:$i]:
% 0.21/0.54         ( ( r1_tarski @ B @ C ) =>
% 0.21/0.54           ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B ) =
% 0.21/0.54             ( k9_relat_1 @ A @ B ) ) ) ) ))).
% 0.21/0.54  thf('1', plain,
% 0.21/0.54      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.54         (~ (r1_tarski @ X7 @ X8)
% 0.21/0.54          | ((k9_relat_1 @ (k7_relat_1 @ X9 @ X8) @ X7)
% 0.21/0.54              = (k9_relat_1 @ X9 @ X7))
% 0.21/0.54          | ~ (v1_relat_1 @ X9))),
% 0.21/0.54      inference('cnf', [status(esa)], [t162_relat_1])).
% 0.21/0.54  thf('2', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (v1_relat_1 @ X0)
% 0.21/0.54          | ((k9_relat_1 @ (k7_relat_1 @ X0 @ (u1_struct_0 @ sk_C)) @ sk_E)
% 0.21/0.54              = (k9_relat_1 @ X0 @ sk_E)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.54  thf('3', plain,
% 0.21/0.54      (((k7_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.21/0.54         sk_E)
% 0.21/0.54         != (k7_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.54             (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C) @ sk_E))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('4', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_D @ 
% 0.21/0.54        (k1_zfmisc_1 @ 
% 0.21/0.54         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(redefinition_k7_relset_1, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.54       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.21/0.54  thf('5', plain,
% 0.21/0.54      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.21/0.54          | ((k7_relset_1 @ X22 @ X23 @ X21 @ X24) = (k9_relat_1 @ X21 @ X24)))),
% 0.21/0.54      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.21/0.54  thf('6', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((k7_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.21/0.54           X0) = (k9_relat_1 @ sk_D @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.54  thf('7', plain,
% 0.21/0.54      (((k9_relat_1 @ sk_D @ sk_E)
% 0.21/0.54         != (k7_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.54             (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C) @ sk_E))),
% 0.21/0.54      inference('demod', [status(thm)], ['3', '6'])).
% 0.21/0.54  thf('8', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('9', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_D @ 
% 0.21/0.54        (k1_zfmisc_1 @ 
% 0.21/0.54         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(d4_tmap_1, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.54             ( l1_pre_topc @ B ) ) =>
% 0.21/0.54           ( ![C:$i]:
% 0.21/0.54             ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.54                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.54                 ( m1_subset_1 @
% 0.21/0.54                   C @ 
% 0.21/0.54                   ( k1_zfmisc_1 @
% 0.21/0.54                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.54               ( ![D:$i]:
% 0.21/0.54                 ( ( m1_pre_topc @ D @ A ) =>
% 0.21/0.54                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 0.21/0.54                     ( k2_partfun1 @
% 0.21/0.54                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.21/0.54                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.54  thf('10', plain,
% 0.21/0.54      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.21/0.54         ((v2_struct_0 @ X32)
% 0.21/0.54          | ~ (v2_pre_topc @ X32)
% 0.21/0.54          | ~ (l1_pre_topc @ X32)
% 0.21/0.54          | ~ (m1_pre_topc @ X33 @ X34)
% 0.21/0.54          | ((k2_tmap_1 @ X34 @ X32 @ X35 @ X33)
% 0.21/0.54              = (k2_partfun1 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X32) @ 
% 0.21/0.54                 X35 @ (u1_struct_0 @ X33)))
% 0.21/0.54          | ~ (m1_subset_1 @ X35 @ 
% 0.21/0.54               (k1_zfmisc_1 @ 
% 0.21/0.54                (k2_zfmisc_1 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X32))))
% 0.21/0.54          | ~ (v1_funct_2 @ X35 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X32))
% 0.21/0.54          | ~ (v1_funct_1 @ X35)
% 0.21/0.54          | ~ (l1_pre_topc @ X34)
% 0.21/0.54          | ~ (v2_pre_topc @ X34)
% 0.21/0.54          | (v2_struct_0 @ X34))),
% 0.21/0.54      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.21/0.54  thf('11', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((v2_struct_0 @ sk_B)
% 0.21/0.54          | ~ (v2_pre_topc @ sk_B)
% 0.21/0.54          | ~ (l1_pre_topc @ sk_B)
% 0.21/0.54          | ~ (v1_funct_1 @ sk_D)
% 0.21/0.54          | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.21/0.54          | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0)
% 0.21/0.54              = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.54                 sk_D @ (u1_struct_0 @ X0)))
% 0.21/0.54          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.21/0.54          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.54          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.54          | (v2_struct_0 @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.54  thf('12', plain, ((v2_pre_topc @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('13', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('14', plain, ((v1_funct_1 @ sk_D)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('15', plain,
% 0.21/0.54      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('16', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_D @ 
% 0.21/0.54        (k1_zfmisc_1 @ 
% 0.21/0.54         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(redefinition_k2_partfun1, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.54     ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.54         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.54       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.21/0.54  thf('17', plain,
% 0.21/0.54      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.21/0.54          | ~ (v1_funct_1 @ X28)
% 0.21/0.54          | ((k2_partfun1 @ X29 @ X30 @ X28 @ X31) = (k7_relat_1 @ X28 @ X31)))),
% 0.21/0.54      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.21/0.54  thf('18', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (((k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.21/0.54            X0) = (k7_relat_1 @ sk_D @ X0))
% 0.21/0.54          | ~ (v1_funct_1 @ sk_D))),
% 0.21/0.54      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.54  thf('19', plain, ((v1_funct_1 @ sk_D)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('20', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.21/0.54           X0) = (k7_relat_1 @ sk_D @ X0))),
% 0.21/0.54      inference('demod', [status(thm)], ['18', '19'])).
% 0.21/0.54  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('22', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('23', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((v2_struct_0 @ sk_B)
% 0.21/0.54          | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0)
% 0.21/0.54              = (k7_relat_1 @ sk_D @ (u1_struct_0 @ X0)))
% 0.21/0.54          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.21/0.54          | (v2_struct_0 @ sk_A))),
% 0.21/0.54      inference('demod', [status(thm)],
% 0.21/0.54                ['11', '12', '13', '14', '15', '20', '21', '22'])).
% 0.21/0.54  thf('24', plain,
% 0.21/0.54      (((v2_struct_0 @ sk_A)
% 0.21/0.54        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.21/0.54            = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)))
% 0.21/0.54        | (v2_struct_0 @ sk_B))),
% 0.21/0.54      inference('sup-', [status(thm)], ['8', '23'])).
% 0.21/0.54  thf('25', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('26', plain,
% 0.21/0.54      (((v2_struct_0 @ sk_B)
% 0.21/0.54        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.21/0.54            = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C))))),
% 0.21/0.54      inference('clc', [status(thm)], ['24', '25'])).
% 0.21/0.54  thf('27', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('28', plain,
% 0.21/0.54      (((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.21/0.54         = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)))),
% 0.21/0.54      inference('clc', [status(thm)], ['26', '27'])).
% 0.21/0.54  thf('29', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_D @ 
% 0.21/0.54        (k1_zfmisc_1 @ 
% 0.21/0.54         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(dt_k7_relset_1, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.54       ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.21/0.54  thf('30', plain,
% 0.21/0.54      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.21/0.54          | (m1_subset_1 @ (k7_relset_1 @ X18 @ X19 @ X17 @ X20) @ 
% 0.21/0.54             (k1_zfmisc_1 @ X19)))),
% 0.21/0.54      inference('cnf', [status(esa)], [dt_k7_relset_1])).
% 0.21/0.54  thf('31', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (m1_subset_1 @ 
% 0.21/0.54          (k7_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.21/0.54           X0) @ 
% 0.21/0.54          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['29', '30'])).
% 0.21/0.54  thf(t3_subset, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.54  thf('32', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         ((r1_tarski @ X0 @ X1) | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.21/0.54      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.54  thf('33', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (r1_tarski @ 
% 0.21/0.54          (k7_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.21/0.54           X0) @ 
% 0.21/0.54          (u1_struct_0 @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.54  thf('34', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((k7_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.21/0.54           X0) = (k9_relat_1 @ sk_D @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.54  thf('35', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (r1_tarski @ (k9_relat_1 @ sk_D @ X0) @ (u1_struct_0 @ sk_A))),
% 0.21/0.54      inference('demod', [status(thm)], ['33', '34'])).
% 0.21/0.54  thf(t88_relat_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ))).
% 0.21/0.54  thf('36', plain,
% 0.21/0.54      (![X12 : $i, X13 : $i]:
% 0.21/0.54         ((r1_tarski @ (k7_relat_1 @ X12 @ X13) @ X12) | ~ (v1_relat_1 @ X12))),
% 0.21/0.54      inference('cnf', [status(esa)], [t88_relat_1])).
% 0.21/0.54  thf('37', plain,
% 0.21/0.54      (![X0 : $i, X2 : $i]:
% 0.21/0.54         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X2)) | ~ (r1_tarski @ X0 @ X2))),
% 0.21/0.54      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.54  thf('38', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         (~ (v1_relat_1 @ X0)
% 0.21/0.54          | (m1_subset_1 @ (k7_relat_1 @ X0 @ X1) @ (k1_zfmisc_1 @ X0)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['36', '37'])).
% 0.21/0.54  thf(cc2_relat_1, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( v1_relat_1 @ A ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.21/0.54  thf('39', plain,
% 0.21/0.54      (![X3 : $i, X4 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.21/0.54          | (v1_relat_1 @ X3)
% 0.21/0.54          | ~ (v1_relat_1 @ X4))),
% 0.21/0.54      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.21/0.54  thf('40', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         (~ (v1_relat_1 @ X0)
% 0.21/0.54          | ~ (v1_relat_1 @ X0)
% 0.21/0.54          | (v1_relat_1 @ (k7_relat_1 @ X0 @ X1)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['38', '39'])).
% 0.21/0.54  thf('41', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         ((v1_relat_1 @ (k7_relat_1 @ X0 @ X1)) | ~ (v1_relat_1 @ X0))),
% 0.21/0.54      inference('simplify', [status(thm)], ['40'])).
% 0.21/0.54  thf(t148_relat_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( v1_relat_1 @ B ) =>
% 0.21/0.54       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.21/0.54  thf('42', plain,
% 0.21/0.54      (![X5 : $i, X6 : $i]:
% 0.21/0.54         (((k2_relat_1 @ (k7_relat_1 @ X5 @ X6)) = (k9_relat_1 @ X5 @ X6))
% 0.21/0.54          | ~ (v1_relat_1 @ X5))),
% 0.21/0.54      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.21/0.54  thf(t87_relat_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( v1_relat_1 @ B ) =>
% 0.21/0.54       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 0.21/0.54  thf('43', plain,
% 0.21/0.54      (![X10 : $i, X11 : $i]:
% 0.21/0.54         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X10 @ X11)) @ X11)
% 0.21/0.54          | ~ (v1_relat_1 @ X10))),
% 0.21/0.54      inference('cnf', [status(esa)], [t87_relat_1])).
% 0.21/0.54  thf(t11_relset_1, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ( v1_relat_1 @ C ) =>
% 0.21/0.54       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.21/0.54           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.21/0.54         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.21/0.54  thf('44', plain,
% 0.21/0.54      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.21/0.54         (~ (r1_tarski @ (k1_relat_1 @ X25) @ X26)
% 0.21/0.54          | ~ (r1_tarski @ (k2_relat_1 @ X25) @ X27)
% 0.21/0.54          | (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.21/0.54          | ~ (v1_relat_1 @ X25))),
% 0.21/0.54      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.21/0.54  thf('45', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.54         (~ (v1_relat_1 @ X1)
% 0.21/0.54          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.21/0.54          | (m1_subset_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 0.21/0.54             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X2)))
% 0.21/0.54          | ~ (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X2))),
% 0.21/0.54      inference('sup-', [status(thm)], ['43', '44'])).
% 0.21/0.54  thf('46', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.54         (~ (r1_tarski @ (k9_relat_1 @ X1 @ X0) @ X2)
% 0.21/0.54          | ~ (v1_relat_1 @ X1)
% 0.21/0.54          | (m1_subset_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 0.21/0.54             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X2)))
% 0.21/0.54          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.21/0.54          | ~ (v1_relat_1 @ X1))),
% 0.21/0.54      inference('sup-', [status(thm)], ['42', '45'])).
% 0.21/0.54  thf('47', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.54         (~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.21/0.54          | (m1_subset_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 0.21/0.54             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X2)))
% 0.21/0.54          | ~ (v1_relat_1 @ X1)
% 0.21/0.54          | ~ (r1_tarski @ (k9_relat_1 @ X1 @ X0) @ X2))),
% 0.21/0.54      inference('simplify', [status(thm)], ['46'])).
% 0.21/0.54  thf('48', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.54         (~ (v1_relat_1 @ X1)
% 0.21/0.54          | ~ (r1_tarski @ (k9_relat_1 @ X1 @ X0) @ X2)
% 0.21/0.54          | ~ (v1_relat_1 @ X1)
% 0.21/0.54          | (m1_subset_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 0.21/0.54             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X2))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['41', '47'])).
% 0.21/0.54  thf('49', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.54         ((m1_subset_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 0.21/0.54           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X2)))
% 0.21/0.54          | ~ (r1_tarski @ (k9_relat_1 @ X1 @ X0) @ X2)
% 0.21/0.54          | ~ (v1_relat_1 @ X1))),
% 0.21/0.54      inference('simplify', [status(thm)], ['48'])).
% 0.21/0.54  thf('50', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (v1_relat_1 @ sk_D)
% 0.21/0.54          | (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 0.21/0.54             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['35', '49'])).
% 0.21/0.54  thf('51', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_D @ 
% 0.21/0.54        (k1_zfmisc_1 @ 
% 0.21/0.54         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(cc1_relset_1, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.54       ( v1_relat_1 @ C ) ))).
% 0.21/0.54  thf('52', plain,
% 0.21/0.54      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.54         ((v1_relat_1 @ X14)
% 0.21/0.54          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.21/0.54      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.21/0.54  thf('53', plain, ((v1_relat_1 @ sk_D)),
% 0.21/0.54      inference('sup-', [status(thm)], ['51', '52'])).
% 0.21/0.54  thf('54', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 0.21/0.54          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.54      inference('demod', [status(thm)], ['50', '53'])).
% 0.21/0.54  thf('55', plain,
% 0.21/0.54      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.21/0.54          | ((k7_relset_1 @ X22 @ X23 @ X21 @ X24) = (k9_relat_1 @ X21 @ X24)))),
% 0.21/0.54      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.21/0.54  thf('56', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         ((k7_relset_1 @ X0 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.54           (k7_relat_1 @ sk_D @ X0) @ X1)
% 0.21/0.54           = (k9_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ X1))),
% 0.21/0.54      inference('sup-', [status(thm)], ['54', '55'])).
% 0.21/0.54  thf('57', plain,
% 0.21/0.54      (((k9_relat_1 @ sk_D @ sk_E)
% 0.21/0.54         != (k9_relat_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ sk_E))),
% 0.21/0.54      inference('demod', [status(thm)], ['7', '28', '56'])).
% 0.21/0.54  thf('58', plain,
% 0.21/0.54      ((((k9_relat_1 @ sk_D @ sk_E) != (k9_relat_1 @ sk_D @ sk_E))
% 0.21/0.54        | ~ (v1_relat_1 @ sk_D))),
% 0.21/0.54      inference('sup-', [status(thm)], ['2', '57'])).
% 0.21/0.54  thf('59', plain, ((v1_relat_1 @ sk_D)),
% 0.21/0.54      inference('sup-', [status(thm)], ['51', '52'])).
% 0.21/0.54  thf('60', plain,
% 0.21/0.54      (((k9_relat_1 @ sk_D @ sk_E) != (k9_relat_1 @ sk_D @ sk_E))),
% 0.21/0.54      inference('demod', [status(thm)], ['58', '59'])).
% 0.21/0.54  thf('61', plain, ($false), inference('simplify', [status(thm)], ['60'])).
% 0.21/0.54  
% 0.21/0.54  % SZS output end Refutation
% 0.21/0.54  
% 0.21/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
