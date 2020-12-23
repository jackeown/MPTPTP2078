%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1337+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YDmyURZ2hs

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:31 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 318 expanded)
%              Number of leaves         :   38 ( 113 expanded)
%              Depth                    :   13
%              Number of atoms          : 1002 (6732 expanded)
%              Number of equality atoms :   17 ( 125 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(sk_E_2_type,type,(
    sk_E_2: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(k3_funct_3_type,type,(
    k3_funct_3: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_tops_2_type,type,(
    v2_tops_2: $i > $i > $o )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(t60_tops_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) )
                 => ( ( ( v5_pre_topc @ C @ A @ B )
                      & ( v2_tops_2 @ D @ B ) )
                   => ! [E: $i] :
                        ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
                       => ( ( E
                            = ( k9_relat_1 @ ( k3_funct_3 @ C ) @ D ) )
                         => ( v2_tops_2 @ E @ A ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( l1_pre_topc @ B )
           => ! [C: $i] :
                ( ( ( v1_funct_1 @ C )
                  & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) )
                   => ( ( ( v5_pre_topc @ C @ A @ B )
                        & ( v2_tops_2 @ D @ B ) )
                     => ! [E: $i] :
                          ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
                         => ( ( E
                              = ( k9_relat_1 @ ( k3_funct_3 @ C ) @ D ) )
                           => ( v2_tops_2 @ E @ A ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t60_tops_2])).

thf('0',plain,(
    m1_subset_1 @ sk_E_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v2_tops_2 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( r2_hidden @ C @ B )
                 => ( v4_pre_topc @ C @ A ) ) ) ) ) ) )).

thf('1',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) ) )
      | ~ ( v4_pre_topc @ ( sk_C @ X20 @ X21 ) @ X21 )
      | ( v2_tops_2 @ X20 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_2])).

thf('2',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_2 @ sk_E_2 @ sk_A )
    | ~ ( v4_pre_topc @ ( sk_C @ sk_E_2 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( v2_tops_2 @ sk_E_2 @ sk_A )
    | ~ ( v4_pre_topc @ ( sk_C @ sk_E_2 @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ~ ( v2_tops_2 @ sk_E_2 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ~ ( v4_pre_topc @ ( sk_C @ sk_E_2 @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_E_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) ) )
      | ( r2_hidden @ ( sk_C @ X20 @ X21 ) @ X20 )
      | ( v2_tops_2 @ X20 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_2])).

thf('9',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_2 @ sk_E_2 @ sk_A )
    | ( r2_hidden @ ( sk_C @ sk_E_2 @ sk_A ) @ sk_E_2 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( v2_tops_2 @ sk_E_2 @ sk_A )
    | ( r2_hidden @ ( sk_C @ sk_E_2 @ sk_A ) @ sk_E_2 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ~ ( v2_tops_2 @ sk_E_2 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    r2_hidden @ ( sk_C @ sk_E_2 @ sk_A ) @ sk_E_2 ),
    inference(clc,[status(thm)],['11','12'])).

thf(dt_k3_funct_3,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k3_funct_3 @ A ) )
        & ( v1_funct_1 @ ( k3_funct_3 @ A ) ) ) ) )).

thf('14',plain,(
    ! [X23: $i] :
      ( ( v1_relat_1 @ ( k3_funct_3 @ X23 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_funct_3])).

thf('15',plain,(
    ! [X23: $i] :
      ( ( v1_funct_1 @ ( k3_funct_3 @ X23 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_funct_3])).

thf('16',plain,
    ( sk_E_2
    = ( k9_relat_1 @ ( k3_funct_3 @ sk_C_1 ) @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d12_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_funct_1 @ A )
        & ( v1_relat_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k9_relat_1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ? [E: $i] :
                  ( ( r2_hidden @ E @ ( k1_relat_1 @ A ) )
                  & ( r2_hidden @ E @ B )
                  & ( D
                    = ( k1_funct_1 @ A @ E ) ) ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ D @ B @ A )
    <=> ( ( D
          = ( k1_funct_1 @ A @ E ) )
        & ( r2_hidden @ E @ B )
        & ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k9_relat_1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ? [E: $i] :
                  ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) ) )).

thf('17',plain,(
    ! [X9: $i,X10: $i,X12: $i,X13: $i] :
      ( ( X12
       != ( k9_relat_1 @ X10 @ X9 ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X13 @ X9 @ X10 ) @ X13 @ X9 @ X10 )
      | ~ ( r2_hidden @ X13 @ X12 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('18',plain,(
    ! [X9: $i,X10: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( r2_hidden @ X13 @ ( k9_relat_1 @ X10 @ X9 ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X13 @ X9 @ X10 ) @ X13 @ X9 @ X10 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_E_2 )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X0 @ sk_D_2 @ ( k3_funct_3 @ sk_C_1 ) ) @ X0 @ sk_D_2 @ ( k3_funct_3 @ sk_C_1 ) )
      | ~ ( v1_funct_1 @ ( k3_funct_3 @ sk_C_1 ) )
      | ~ ( v1_relat_1 @ ( k3_funct_3 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v1_relat_1 @ ( k3_funct_3 @ sk_C_1 ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X0 @ sk_D_2 @ ( k3_funct_3 @ sk_C_1 ) ) @ X0 @ sk_D_2 @ ( k3_funct_3 @ sk_C_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_E_2 ) ) ),
    inference('sup-',[status(thm)],['15','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_relat_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('23',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k3_funct_3 @ sk_C_1 ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X0 @ sk_D_2 @ ( k3_funct_3 @ sk_C_1 ) ) @ X0 @ sk_D_2 @ ( k3_funct_3 @ sk_C_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_E_2 ) ) ),
    inference(demod,[status(thm)],['20','23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ sk_E_2 )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X0 @ sk_D_2 @ ( k3_funct_3 @ sk_C_1 ) ) @ X0 @ sk_D_2 @ ( k3_funct_3 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['14','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['21','22'])).

thf('28',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_E_2 )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X0 @ sk_D_2 @ ( k3_funct_3 @ sk_C_1 ) ) @ X0 @ sk_D_2 @ ( k3_funct_3 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ ( sk_C @ sk_E_2 @ sk_A ) @ sk_D_2 @ ( k3_funct_3 @ sk_C_1 ) ) @ ( sk_C @ sk_E_2 @ sk_A ) @ sk_D_2 @ ( k3_funct_3 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['13','29'])).

thf('31',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X4 @ X6 )
      | ~ ( zip_tseitin_0 @ X4 @ X5 @ X6 @ X3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('32',plain,(
    r2_hidden @ ( sk_E_1 @ ( sk_C @ sk_E_2 @ sk_A ) @ sk_D_2 @ ( k3_funct_3 @ sk_C_1 ) ) @ sk_D_2 ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('34',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( r2_hidden @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X32 ) )
      | ( m1_subset_1 @ X30 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( r2_hidden @ X0 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ ( sk_E_1 @ ( sk_C @ sk_E_2 @ sk_A ) @ sk_D_2 @ ( k3_funct_3 @ sk_C_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d12_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ( ( v5_pre_topc @ C @ A @ B )
              <=> ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                   => ( ( v4_pre_topc @ D @ B )
                     => ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ A ) ) ) ) ) ) ) )).

thf('38',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( v5_pre_topc @ X17 @ X18 @ X16 )
      | ~ ( v4_pre_topc @ X19 @ X16 )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X16 ) @ X17 @ X19 ) @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X16 ) ) ) )
      | ~ ( v1_funct_2 @ X17 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X16 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_B )
      | ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B )
      | ~ ( l1_pre_topc @ sk_B ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('44',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( ( k8_relset_1 @ X25 @ X26 @ X24 @ X27 )
        = ( k10_relat_1 @ X24 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 @ X0 )
      = ( k10_relat_1 @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v5_pre_topc @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( v4_pre_topc @ ( k10_relat_1 @ sk_C_1 @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['39','40','41','42','45','46','47'])).

thf('49',plain,
    ( ~ ( v4_pre_topc @ ( sk_E_1 @ ( sk_C @ sk_E_2 @ sk_A ) @ sk_D_2 @ ( k3_funct_3 @ sk_C_1 ) ) @ sk_B )
    | ( v4_pre_topc @ ( k10_relat_1 @ sk_C_1 @ ( sk_E_1 @ ( sk_C @ sk_E_2 @ sk_A ) @ sk_D_2 @ ( k3_funct_3 @ sk_C_1 ) ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['36','48'])).

thf('50',plain,(
    r2_hidden @ ( sk_E_1 @ ( sk_C @ sk_E_2 @ sk_A ) @ sk_D_2 @ ( k3_funct_3 @ sk_C_1 ) ) @ sk_D_2 ),
    inference('sup-',[status(thm)],['30','31'])).

thf('51',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) ) )
      | ~ ( v2_tops_2 @ X20 @ X21 )
      | ~ ( r2_hidden @ X22 @ X20 )
      | ( v4_pre_topc @ X22 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_2])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( v4_pre_topc @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_D_2 )
      | ~ ( v2_tops_2 @ sk_D_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v2_tops_2 @ sk_D_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( v4_pre_topc @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( r2_hidden @ X0 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_D_2 )
      | ( v4_pre_topc @ X0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['56','57'])).

thf('59',plain,(
    v4_pre_topc @ ( sk_E_1 @ ( sk_C @ sk_E_2 @ sk_A ) @ sk_D_2 @ ( k3_funct_3 @ sk_C_1 ) ) @ sk_B ),
    inference('sup-',[status(thm)],['50','58'])).

thf('60',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ ( sk_C @ sk_E_2 @ sk_A ) @ sk_D_2 @ ( k3_funct_3 @ sk_C_1 ) ) @ ( sk_C @ sk_E_2 @ sk_A ) @ sk_D_2 @ ( k3_funct_3 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['13','29'])).

thf('61',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X4 @ ( k1_relat_1 @ X3 ) )
      | ~ ( zip_tseitin_0 @ X4 @ X5 @ X6 @ X3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('62',plain,(
    r2_hidden @ ( sk_E_1 @ ( sk_C @ sk_E_2 @ sk_A ) @ sk_D_2 @ ( k3_funct_3 @ sk_C_1 ) ) @ ( k1_relat_1 @ ( k3_funct_3 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf(t24_funct_3,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k3_funct_3 @ B ) ) )
       => ( ( k1_funct_1 @ ( k3_funct_3 @ B ) @ A )
          = ( k10_relat_1 @ B @ A ) ) ) ) )).

thf('63',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ X28 @ ( k1_relat_1 @ ( k3_funct_3 @ X29 ) ) )
      | ( ( k1_funct_1 @ ( k3_funct_3 @ X29 ) @ X28 )
        = ( k10_relat_1 @ X29 @ X28 ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_3])).

thf('64',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( ( k1_funct_1 @ ( k3_funct_3 @ sk_C_1 ) @ ( sk_E_1 @ ( sk_C @ sk_E_2 @ sk_A ) @ sk_D_2 @ ( k3_funct_3 @ sk_C_1 ) ) )
      = ( k10_relat_1 @ sk_C_1 @ ( sk_E_1 @ ( sk_C @ sk_E_2 @ sk_A ) @ sk_D_2 @ ( k3_funct_3 @ sk_C_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['21','22'])).

thf('66',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ ( sk_C @ sk_E_2 @ sk_A ) @ sk_D_2 @ ( k3_funct_3 @ sk_C_1 ) ) @ ( sk_C @ sk_E_2 @ sk_A ) @ sk_D_2 @ ( k3_funct_3 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['13','29'])).

thf('68',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( X5
        = ( k1_funct_1 @ X3 @ X4 ) )
      | ~ ( zip_tseitin_0 @ X4 @ X5 @ X6 @ X3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('69',plain,
    ( ( sk_C @ sk_E_2 @ sk_A )
    = ( k1_funct_1 @ ( k3_funct_3 @ sk_C_1 ) @ ( sk_E_1 @ ( sk_C @ sk_E_2 @ sk_A ) @ sk_D_2 @ ( k3_funct_3 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( sk_C @ sk_E_2 @ sk_A )
    = ( k10_relat_1 @ sk_C_1 @ ( sk_E_1 @ ( sk_C @ sk_E_2 @ sk_A ) @ sk_D_2 @ ( k3_funct_3 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['64','65','66','69'])).

thf('71',plain,(
    v4_pre_topc @ ( sk_C @ sk_E_2 @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['49','59','70'])).

thf('72',plain,(
    $false ),
    inference(demod,[status(thm)],['6','71'])).


%------------------------------------------------------------------------------
